import System.IO
import Text.Printf
import Data.List

----------------
-- Fin и список, с которыми будем работать.
-- Все возможные сравнения.
----------------

restrFin :: Int
restrFin = 5

checklist = [(i,j) | i <- [0..(restrFin-1)], j <- [0..(restrFin-1)], i<j]

lis = [[a-1,s-1,d-1,f-1,g-1] | a <- [1..5], s <- [1..5], d <- [1..5], f <- [1..5], g <- [1..5],
	(a-s)*(a-d)*(a-f)*(a-g)*(s-d)*(s-f)*(s-g)*(d-f)*(d-g)*(f-g) /= 0]

----------------
-- Печать чисел и отступов.
-- Конкатенация в списке.
-- Предстваление списков в Agda.
----------------

finToString 0 = "zerof"
finToString s = "sucf (" ++ (finToString (s-1)) ++ ")"

lessThanProof 0 = "s≤s z≤n"
lessThanProof n = "s≤s (" ++ (lessThanProof (n-1)) ++ ")"

vstav d = foldl (++) "" ["        " | q <- [1..d]]
concatInList s1 s2 = s1 ++ " ∷ " ++ s2

listOfName [] = ""
listOfName (q:[]) = show q
listOfName (q:ls) = (show q) ++ "," ++ (listOfName ls)

presentation :: [[Int]] -> String
presentation lss = foldr concatInList "[]" (map (\ x -> "p_" ++ listOfName x) lss)

----------------
-- Алгоритм сортировки и его осмысленность.
-- Вывод алгоритма на данной глубине.
-- Указатель, где живёт noexist.
----------------

data NoexPointer = First | Second

data AlgSearch = Leaf [Int] | Node Int Int AlgSearch AlgSearch | Noexist String | Wtf

sense Wtf = 0
sense (Noexist s) = 0
sense q = 1

algOutputDepth :: AlgSearch -> Int -> String
algOutputDepth (Leaf l) d = printf "%s(leaf p_%s)" (vstav d) (listOfName l)
algOutputDepth (Node i j a b) d = printf "%s(node (%s) (%s) prfNoteq%d--%d,%d \n%s\n%s)"
	(vstav d) (finToString i) (finToString j)
	(restrFin :: Int) (i :: Int) (j :: Int)
	(algOutputDepth a (d+1)) (algOutputDepth b (d+1))

----------------
-- Заголовок функции в noexist-е.
-- Случай очень больших или
-- равных аргументов.
----------------

impos 0 = "h"
impos n = "(sucf " ++ (impos (n-1)) ++ ")"

impossibru = impos restrFin

fHeader nam lss dep = printf
	"F%s : (i j : Fin %d) → (i ≢ j) → (noexist (cmpFilter i j (%s)) %d ⊎ noexist (cmpFilter j i (%s)) %d) \n\n"
	nam restrFin
	(presentation lss) (dep-1)
	(presentation lss) (dep-1)

fStringEquiv nam m = printf "F%s (%s) (%s) p = ⊥-elim (p refl)\n"
	nam
	(finToString m)
	(finToString m)

fStringImpos nam = printf "F%s %s _ = ⊥-elim (nolify h) \nF%s _ %s = ⊥-elim (nolify h) \n\n"
	nam impossibru nam impossibru

----------------
-- Сбор сведений о noexist-ах: где они живут
-- и что из себя представляют.
----------------

addFString nam i j First = printf "F%s (%s) (%s) _ = inj₁ (noex%s<%d,%d>) \nF%s (%s) (%s) _ = inj₂ (noex%s<%d,%d>) \n\n"
	nam (finToString i) (finToString j)
	nam (i :: Int) (j :: Int)
	nam (finToString j) (finToString i)
	nam (i :: Int) (j :: Int)
addFString nam i j Second = printf "F%s (%s) (%s) _ = inj₂ (noex%s<%d,%d>) \nF%s (%s) (%s) _ = inj₁ (noex%s<%d,%d>) \n\n"
	nam (finToString i) (finToString j)
	nam (j :: Int) (i :: Int)
	nam (finToString j) (finToString i)
	nam (j :: Int) (i :: Int)

prepared :: String -> (Int, Int, AlgSearch, AlgSearch) -> (String, String)
prepared nam (i,j,a,b) = case (a,b) of
	(Noexist s, q) -> (s, addFString nam i j First)
	(q, Noexist s) -> (s, addFString nam i j Second)

----------------
-- Поиск алгоритма с данной глубиной
-- или соответствующего noexist-а.
----------------

algFind :: [[Int]] -> Int -> String -> AlgSearch
algFind ls dep nam = if (2 ^ dep < length ls)
    then Noexist (printf "noex%s : noexist (%s) %d \nnoex%s = basa\n        (%s)\n        %d (%s)\n\n"
	nam (presentation ls) (dep :: Int)
	nam (presentation ls) (dep :: Int)
	(lessThanProof (2 ^ dep)))
    else case (length ls) of
	0 -> Wtf
	1 -> Leaf (head ls)
	q -> let checkSense (i,j,a,b) = (sense a) * (sense b) > 0 in
	     let createFilter x y = filter (\l -> l!!x < l!!y) ls in
	     let createAlg x y = algFind (createFilter x y) (dep-1) (nam ++ printf "<%s,%s>" (show x) (show y)) in
	     let smashedChecklist = map (\ (x,y) -> (x, y, createAlg x y, createAlg y x)) checklist in
	     let largeList = filter checkSense smashedChecklist in
		case largeList of
		    (i,j,a,b):somelist -> Node i j a b
		    [] -> let strings = map (\x -> prepared nam x) smashedChecklist in
			Noexist (foldl (++) ""
			    ((map fst strings) ++ [fHeader nam ls dep] ++
			     [fStringEquiv nam t | t <- [0..(restrFin-1)]] ++
			     [fStringImpos nam] ++ (map snd strings) ++
			     [printf "noex%s : noexist (%s) %d\nnoex%s = pereh (%s) %d F%s\n\n"
				nam (presentation ls) (dep :: Int)
				nam (presentation ls) (dep-1 :: Int) nam]))

----------------
-- Дана глубина. Выведем либо алгоритм,
-- либо док-во его отсутствия.
----------------

algOutput :: Int -> String
algOutput dep = case (algFind lis dep "") of
    Wtf -> "Oops, an error occured"
    Noexist s -> s ++ (printf "noalgprf : (a : Alg lis) → (depth a ℕ≤ %d) → ⊥ \nnoalgprf = noexistNoAlg (s≤s (s≤s z≤n)) UNI noex" dep)
    Leaf l -> printf "autoalg : Alg lis\nautoalg = leaf p_%s" (listOfName l)
    Node i j a b -> printf "autoalg : Alg lis\nautoalg = node (%s) (%s) prfNoteq%d--%d,%d \n%s\n%s"
	(finToString i :: String) (finToString j :: String)
	(restrFin :: Int) (i :: Int) (j :: Int)
	(algOutputDepth a 1 :: String) (algOutputDepth b 1 :: String)

----------------
-- Main.
----------------

main = do
	hSetEncoding stdout utf8
--	putStr (show (length lis) ++ "\n\n\n\n")
	putStr (algOutput 7)