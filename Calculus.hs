module Calculus where

import Data.Maybe

data UnOp = Neg | Sin | Cos | Log
          deriving (Eq, Ord, Show)

data BinOp = Add | Mul | Div
           deriving (Eq, Ord, Show)

data Exp = Val Double | Id String | UnApp UnOp Exp | BinApp BinOp Exp Exp
         deriving (Eq, Ord, Show)

type Env = [(String, Double)]

--Op to operator list
binop = [(Add,(+)), (Mul,(*)), (Div,(/))]
unop = [(Neg,(*(-1))), (Sin,sin), (Cos,cos), (Log,log)]

-- look for matching pair
lookUp :: Eq a => a -> [(a, b)] -> b
lookUp x env = fromJust (lookup x env)

-- evaluate an expression for given x
eval :: Exp -> Env -> Double
eval (Val x) env = x
eval (Id s) env  = lookUp s env
eval (UnApp uop exp) env = (lookUp uop unop) (eval exp env)
eval (BinApp bop exp1 exp2) env 
      = (lookUp bop binop) (eval exp1 env) (eval exp2 env)

-- differentiate a given expression
diff :: Exp -> String -> Exp
diff (BinApp bop exp1 exp2) x 
   | bop == Mul = BinApp Add (BinApp Mul (exp1) (diff exp2 x)) 
                  (BinApp Mul (diff exp1 x) (exp2))
   | bop == Div = BinApp Div (BinApp Add (BinApp Mul (diff exp1 x) (exp2)) 
                  (UnApp Neg (BinApp Mul (exp1) (diff exp2 x)))) 
                  (BinApp Mul exp2 exp2)
   | otherwise  = BinApp bop (diff exp1 x) (diff exp2 x)
diff (UnApp uop exp) x
   | uop == Neg = UnApp uop (diff exp x)
   | uop == Sin = BinApp Mul (UnApp Cos exp) (diff exp x)
   | uop == Cos = UnApp Neg (BinApp Mul (UnApp Sin exp) (diff exp x))
   | otherwise  = BinApp Div (diff exp x) (exp)
diff (Val x') x = Val 0.0
diff (Id s) x
   | s == x     = Val 1.0
   | otherwise  = Val 0.0

-- find apporximation of f(x) for given x, n
-- using maclaurin series
maclaurin :: Exp -> Double -> Int -> Double
maclaurin _ _ 0 = 0
maclaurin exp x n = maclaurin' exp 0 1 0
   where
   (env,m) = ([("x",0)],n-1)
   maclaurin' :: Exp -> Int -> Int -> Double -> Double
   maclaurin' exp' i d last'
     | i == m    = last'+x^i*(eval exp' env)/d'
     | otherwise = seq (i',d'',last'') $ maclaurin' nexp i' d'' last''
	where
        (i',d'',last'') = (i+1,d*(i+1),last'+x^i*(eval exp' env)/d')
        nexp = diff exp' "x"
        d'   = fromIntegral d
        
-- Op to Math function list
sbop = [(Add,'+'), (Mul,'*'), (Div,'/')]	 
suop = [(Neg,"-"), (Sin,"sin"), (Cos,"cos"), (Log,"log")]  

-- take an expression, show string of expression	   
showExp :: Exp -> String
showExp (Val x) = show x
showExp (Id s)  = s
showExp (UnApp uop exp) = (lookUp uop suop)++'(':(showExp exp)++")"
showExp (BinApp bop exp1 exp2) 
  = '(':(showExp exp1)++(lookUp bop sbop):(showExp exp2)++")"


-- list of operator precedence
so = [(Add,1),(Mul,2),(Div,2)]

-- show an expression in simplest form
-- assuming unop > binop
-- unop is right assocciative
showSply :: Exp -> String
showSply exp = simply s
  where
  s = showExp' exp
  showExp' :: Exp -> String
  showExp' (Val x)
    | fromIntegral (floor x) - x == 0 = show (floor x)
    | otherwise = show x 
  showExp' (Id s)  = s
  showExp' (UnApp uop exp'@(BinApp bop exp1 exp2)) 
    = (lookUp uop suop)++'(':(showExp' exp')++")"
  showExp' (UnApp uop exp') = (lookUp uop suop)++(showExp exp')
  showExp' (BinApp bop exp1 exp2) 
    = (inst True exp1 (showExp' exp1) bop)++(lookUp bop sbop)
      :(inst False exp2 (showExp' exp2) bop)
  inst :: Bool -> Exp -> String -> BinOp -> String
  inst b (BinApp bop' exp1 exp2) s' bop
    | b && (lookUp bop' so) >= (lookUp bop so) = s'
    | b = '(':s'++")"
    | (lookUp bop' so) > (lookUp bop so) = s'
    | otherwise = '(':s'++")"
  inst _ _ s' _ = s'
  simply :: String -> String
  simply [x] = [x]
  simply (x:x':xs)
    | (x == '+') && (x' == '-') = x': simply xs
    | otherwise = x : simply (x':xs)
  
-- instance declaration for overloaded definition
instance Num Exp where
 (+) = BinApp Add
 (*) = BinApp Mul
 negate = UnApp Neg
 fromInteger = (.) Val fromInteger

instance Fractional Exp where
 (/) = BinApp Div

instance Floating Exp where
 sin = UnApp Sin
 cos = UnApp Cos
 log = UnApp Log


-- differentiation with overloaded definition
-- simplification via definitions in Maybe monad
diff2 :: Exp -> String -> Maybe Exp
diff2 (BinApp bop exp1 exp2) x 
   | bop == Mul 
       = (Just exp1) * (diff2 exp2 x) + (diff2 exp1 x) * (Just exp2)
   | bop == Div 
       = ((diff2 exp1 x) * (Just exp2) + (-((Just exp1) 
         * (diff2 exp2 x)))) / (Just exp2 * Just exp2)
   | otherwise = (diff2 exp1 x) + (diff2 exp2 x)
diff2 (UnApp uop exp) x
   | uop == Neg = -(diff2 exp x)
   | uop == Sin = Just (UnApp Cos exp) * (diff2 exp x)
   | uop == Cos = -(Just (UnApp Sin exp)) * (diff2 exp x)
   | otherwise  = (diff2 exp x) / Just exp
diff2 (Val x') x = Nothing
diff2 (Id s) x
   | s == x    = Just 1
   | otherwise = Nothing

minus :: (Num a) => a -> a
minus x = -x

-- instance declaration for Maybe monad
-- simplification rule for Just encoded 
instance (Eq a, Num a) => Num (Maybe a) where
 Nothing + x = x
 Just t + Just s = Just (t+s)
 x + y  = y + x
 Just 1 * x = x
 Nothing * x = Nothing
 Just t * Just s = Just (t*s)
 x * y = y * x
 fromInteger = (.) Just fromInteger
-- negate :: Maybe a -> Maybe a
 negate Nothing = Nothing
 negate (Just x) = Just (-x)
 
data OpExp
  = OpExp Exp
  deriving (Show)

instance Num OpExp where
  OpExp e1 + OpExp (Val 0)
    = OpExp e1

  OpExp e1 + OpExp e2
    = OpExp (e1 + e2)

  fromInteger
    = OpExp . fromInteger
 
getExp :: OpExp -> Exp
getExp (OpExp e) = e

instance (Eq a, Fractional a) => Fractional (Maybe a) where
 Nothing / x = x
 x / Just 1 = x
 Just x / Just y 
   | x == y = Just 1
   | otherwise = Just (x/y)


---------------------------------------------------------------------------
-- Test cases from the spec.

e1, e2, e3, e4, e5, e6 :: Exp

-- > 5*x
e1 = BinApp Mul (Val 5.0) (Id "x")

-- > x*x + y - 7
e2 = BinApp Add (BinApp Add (BinApp Mul (Id "x") (Id "x")) (Id "y"))
                (UnApp Neg (Val 7.0))

-- > x-y^2/(4*x*y-y^2)::Exp
e3 = BinApp Add (Id "x")
            (UnApp Neg (BinApp Div (BinApp Mul (Id "y") (Id "y"))
            (BinApp Add (BinApp Mul (BinApp Mul (Val 4.0) (Id "x")) (Id "y"))
                        (UnApp Neg (BinApp Mul (Id "y") (Id "y"))))))

-- > -cos x::Exp
e4 = UnApp Neg (UnApp Cos (Id "x"))

-- > sin (1+log(2*x))::Exp
e5 = UnApp Sin (BinApp Add (Val 1.0)
                           (UnApp Log (BinApp Mul (Val 2.0) (Id "x"))))

-- > log(3*x^2+2)::Exp
e6 = UnApp Log (BinApp Add (BinApp Mul (Val 3.0) (BinApp Mul (Id "x") (Id "x")))
                           (Val 2.0))

----------------------------------------------------------------------

-- The following makes it much easier to input expressions, e.g. sin x, log(x*x) etc.

x, y :: Exp
x = Id "x"
y = Id "y"
