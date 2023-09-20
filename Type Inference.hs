
--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------

------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m

------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs x (At a)       = x == a
occurs x (At a :-> b) = occurs x (At a) || occurs x b
occurs x ((At a :-> At b) :-> At c) = occurs x (At a :-> At b) || occurs x (At c)

findAtoms :: Type -> [Atom]
findAtoms (At a) = [a]
findAtoms (a :-> b) = (findAtoms a) `merge` (findAtoms b)

------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub (a, At b) (At c)
   | a == c = (At b)
   | otherwise = (At c)
sub (a, At b :-> At c) (At d)
   | a == d = (At b :-> At c)
   | otherwise = (At d)
sub (a,b) (x :-> y) = (sub (a,b) x :-> sub (a,b) y)


subs :: [Sub] -> Type -> Type
subs [] a = a
subs [x] a = sub x a
subs (x:xs) a = sub x (subs xs a)

------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u s [] = []
sub_u  s ((x,y):xs) = [(sub s x, sub s y)] ++ sub_u s xs

step :: State -> State
step (subList,((a :-> b, c :-> d):xs)) = (subList, xs ++[(a,c),(b,d)]) -- CASE C no errors
step (subList,((At a,t):xs))
   | At a == t = (subList,xs) -- CASE A
   | any (== a) (findAtoms(t)) == True = error "ufail" -- B FAIL
   | otherwise = ([(a, t)] ++ subList, sub_u (a, t) xs) -- B
step (subList,((a,At t):xs))
   | a == At t = (subList,xs) -- CASE A
   | any (== t) (findAtoms(a)) == True = error "fail" -- B FAIL
   | otherwise = ([(t,a)] ++ subList, sub_u (t,a) xs) -- B


unify :: [Upair] -> [Sub]
unify u = fst(unif([],u)) -- base case
  where
    unif :: State -> State
    unif(s,[]) = (s,[])
    unif(s,u) = unif(step(s,u))

------------------------- Assignment 4
type Context   = [(Var,Type)]
type Judgement = (Context, Term, Type)

data Derivation =
    Axiom Judgement
  | Abstraction Judgement Derivation
  | Application Judgement Derivation Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")


d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


conclusion :: Derivation -> Judgement
conclusion (Axiom x) = x
conclusion (Abstraction x y) = x
conclusion (Application x y z) = x

subs_ctx :: [Sub] -> Context -> Context
subs_ctx _ [] = []
subs_ctx s (x:xs) = [(fst x, subs s (snd x))] ++ subs_ctx s xs

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg [] a = a
subs_jdg s (con, ter, typ) = (subs_ctx s con, ter, subs s typ)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der [] a = a
subs_der s (Axiom x) = (Axiom (subs_jdg s x))
subs_der s (Abstraction x y) = (Abstraction (subs_jdg s x) (subs_der s y))
subs_der s (Application x y z) = (Application (subs_jdg s x) (subs_der s y) (subs_der s z))

------------------------- Typesetting derivations

instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])

------------------------- Assignment 5
inflist :: [Type] -> [Type]
inflist x = x ++ inflist x

addCon :: Context -> (Var,Type) -> Context
addCon [] y = [y]
addCon (x:xs) y
  | x==y = (y:xs)
  | otherwise = (x:addCon xs y)

conMerge :: Context -> Context -> Context
conMerge x [] = x
conMerge x (y:ys) = conMerge (addCon x y) ys


derive0 :: Term -> Derivation
derive0 m = aux ([(x,At "") | x <- free m],m,At "")
  where
    aux :: Judgement -> Derivation
    aux (ctx,Variable x,At "") = Axiom (ctx,Variable x,At "")
    aux (ctx,Lambda x m,At "") = Abstraction (ctx,Lambda x m,At "") (aux ( (x,At "") : filter ((/= x).fst) ctx,m,At ""))
    aux (ctx,Apply  m n,At "") = Application (ctx,Apply  m n,At "") (aux (ctx,m,At "")) (aux (ctx,n,At ""))

---------------------------------------------------------
n = Lambda "x" (Lambda "y" (Lambda "z" (Apply(Apply(Variable "x")(Variable "z"))(Apply(Variable "y")(Variable "z")))))

n2 = Lambda "x" (Lambda "x" (Variable "x"))

n3 = Lambda "x" (Variable "x")
---------------------------------------------------------
derive1 :: Term -> Derivation
derive1 m = aux remAtoms (ctx, m, At (head atoms))
  where
    xs = free m
    ctx = [(x,At a) | (x,a) <- zip xs (tail atoms)]
    remAtoms = drop (length xs + 1) atoms
    aux :: [Atom] -> Judgement -> Derivation
    aux ats (ctx,Variable x,typ) = Axiom (ctx,Variable x,typ)
    aux ats (ctx,Lambda x m,typ) = Abstraction (ctx,Lambda x m, typ) (aux (drop 1 ats) (conMerge [(x,At (head ats))] ctx,m,At (head (drop 1 ats))))
    aux ats (ctx,Apply m n,typ) = Application (ctx,Apply m n,typ) (aux (splitStream 1 (drop 2 ats)) (ctx,m,At (head(ats)))) (aux(splitStream 2 (drop 2 ats))(ctx,n,At (head(drop 1 ats))))
    splitStream :: Int -> [Atom] -> [Atom]
    splitStream  _ [] = []
    splitStream 1 (x:xs) = x:(splitStream 1 (drop 1 xs))
    splitStream 2 xs = xs `minus` (splitStream 1 xs)


upairs :: Derivation -> [Upair]
upairs (Axiom (ctx,Variable x,t)) = [(t,find x ctx)]
upairs (Abstraction (ctx,Lambda x n,t) d) = (t,  find x dx :-> s ) : upairs d
  where
    (dx,_,s) = conclusion d
upairs (Application (ctx,Apply  n m,t) d e) = (r, s :-> t) : upairs d ++ upairs e
  where
   (dx,_,r) = conclusion d
   (ex,_,s) = conclusion e
    
    
derive :: Term -> Derivation
derive n = subs_der (unify (upairs d)) d
  where
    d = derive1 n