import System.IO
import Text.Printf
import Data.List

----------------
-- Fin и список, с которыми будем работать.
----------------

restrFin :: Int
restrFin = 5

lis = [[a-1,s-1,d-1,f-1,g-1] | a <- [1..5], s <- [1..5], d <- [1..5], f <- [1..5], g <- [1..5],
	(a-s)*(a-d)*(a-f)*(a-g)*(s-d)*(s-f)*(s-g)*(d-f)*(d-g)*(f-g) /= 0]

----------------
-- Печать конечных чисел — с указанием и без указания
-- типа нуля. Печать сравнений.
-- Специальные конкатенации строк.
----------------

finToStringRestr 0 x = "zerof" 
finToStringRestr s x = "sucf (" ++ (finToStringRestr (s-1) (x-1)) ++ ")"

finToStringRestrSpec 0 x = "zerof {" ++ (show (x-1)) ++ "}" 
finToStringRestrSpec s x = "sucf (" ++ (finToStringRestrSpec (s-1) (x-1)) ++ ")"

finToString a = finToStringRestr a restrFin
finToStringSpec a = finToStringRestrSpec a restrFin

printCmp 0 x = "z≤n"
printCmp 1 x = "s≤s " ++ printCmp 0 (x-1)
printCmp s x = "s≤s (" ++ printCmp (s-1) (x-1) ++ ")"

spacConcat s1 s2 = s1 ++ "\n\n" ++ s2
concatInList s1 s2 = s1 ++ " ∷ " ++ s2

----------------
-- Доказательства неравенств конечных чисел.
-- Название одного, печать одного,
-- печать сразу всех.
----------------

prfNoteqName :: Int -> Int -> String
prfNoteqName a b = printf "prfNoteq%d--%d,%d"
	(restrFin :: Int)
	(a :: Int)
	(b :: Int)

prfNoteq a b = printf
	"%s : %s ≢ %s\n%s = λ P → noteq\n  (toℕ (%s))\n  (toℕ (%s))\n  (%s)\n  (eq_cong toℕ P)"
	(prfNoteqName a b)
	(finToStringSpec a)
	(finToStringSpec b)
	(prfNoteqName a b)
	(finToStringSpec a)
	(finToStringSpec b)
	(printCmp (a+1) b)

allNoteq = foldr spacConcat "" [prfNoteq a b | a <- [0..(restrFin-1)], b <- [0..(restrFin-1)], a<b]

----------------
-- Имя объекта по соответствующему ему
-- списку. Перечисление перестановок
-- и сформированного из них lis.
----------------

listOfName [] = ""
listOfName (q:[]) = show q
listOfName (q:ls) = (show q) ++ "," ++ (listOfName ls)

permOfName :: [Int] -> String
permOfName [] = "«»"
permOfName (0:[]) = printf "%s — %s" (finToStringSpec 0) (permOfName [])
permOfName (0:ls) = printf "%s — (%s)" (finToStringSpec 0) (permOfName ls)
permOfName (q:[]) = printf "(%s) — %s" (finToStringSpec q) (permOfName [])
permOfName (q:ls) = printf "(%s) — (%s)" (finToStringSpec q) (permOfName ls)

localIntroduction :: [Int] -> String
localIntroduction l = printf "p_%s = %s\n\n"
	(listOfName l) (permOfName l)

listOfNames = printf "lis = %s" (foldr concatInList "[]" (map (\ x -> "p_" ++ listOfName x) lis))

globalIntroduction = (foldl (++) "" [localIntroduction x | x <- lis]) ++ listOfNames ++ "\n\n"

----------------
-- Заголовок доказательства того,
-- что данный элемент — перестановка.
-- Случай равных аргументов.
----------------

header x = printf "u_%s : (i j : Fin %d) → (i ≢ j) → nth p_%s i ≢ nth p_%s j \n"
	(listOfName x) restrFin (listOfName x) (listOfName x)

stringEquiv x m = printf "u_%s (%s) (%s) p = ⊥-elim (p refl)\n"
	(listOfName x)
	(finToString m)
	(finToString m)

----------------
-- Случай недостижимых аргументов.
----------------

impos 0 = "h"
impos n = "(sucf " ++ (impos (n-1)) ++ ")"

impossibru = impos restrFin

stringImpos x = printf "u_%s %s _ = ⊥-elim (nolify h) \nu_%s _ %s = ⊥-elim (nolify h) \n\n"
	(listOfName x) impossibru (listOfName x) impossibru

----------------
-- Случай общих аргументов.
----------------

stringUnic x m n =
	let nom = x!!m in
	let non = x!!n in
		if nom<non then
			printf "u_%s (%s) (%s) p = %s \nu_%s (%s) (%s) p = ncom %s \n\n"
				(listOfName x) (finToString m)
				(finToString n) (prfNoteqName nom non)
				(listOfName x) (finToString n)
				(finToString m) (prfNoteqName nom non)
		else
			printf "u_%s (%s) (%s) p = ncom %s \nu_%s (%s) (%s) p = %s \n\n"
				(listOfName x) (finToString m)
				(finToString n) (prfNoteqName non nom)
				(listOfName x) (finToString n)
				(finToString m) (prfNoteqName non nom)

----------------
-- Сводим доказательство Unicalized.
----------------

localUnic x = foldl (++) []
       ([header x] ++
	[stringEquiv x m | m <- [0..(restrFin-1)]] ++
	[stringImpos x] ++
	[stringUnic x m n | m <- [0..(restrFin-1)], n <- [0..(restrFin-1)], m<n])

globalUnic = foldl (++) "" [localUnic x | x <- lis]

unicalizedWrite [] = "u-nil"
unicalizedWrite (q:[]) = printf "u_%s u-cons %s" (listOfName q) (unicalizedWrite [])
unicalizedWrite (q:ls) = printf "u_%s u-cons (%s)" (listOfName q) (unicalizedWrite ls)

unicalizedFinal = printf "UNI : Unicalized lis \nUNI = %s" (unicalizedWrite lis)

----------------
-- Выводим всё, что породили,
-- в правильном порядке.
----------------

main = do
	hSetEncoding stdout utf8
	putStr (allNoteq)
	putStr (globalIntroduction)
	putStr (globalUnic)
	putStr (unicalizedFinal)