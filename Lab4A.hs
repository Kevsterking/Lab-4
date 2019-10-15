-- Authors:
-- Date:

import Poly
import Test.QuickCheck


-- Use the following simple data type for binary operators
data BinOp = AddOp | MulOp
  -- deriving Show
--------------------------------------------------------------------------------
-- * A1
-- Define a data type Expr which represents three kinds of expression:
-- binary operators (use BinOp as a helper type) applied to two expressions,
-- numbers (use Int), and exponentiation x^n.
-- Note that since we consider expressions containing just a single variable,
-- x, your data type should not use String or Char anywhere, since this is
-- not needed.

data Expr = Val Int | Op Expr BinOp Expr | Pow Int


--------------------------------------------------------------------------------
-- * A2
-- Define the data type invariant that checks that exponents are never negative
prop_Expr :: Expr -> Bool
prop_Expr (Val n)            = True 
prop_Expr (Pow n)            = n >= 0
prop_Expr (Op expr1 _ expr2) = prop_Expr expr1 && prop_Expr expr2


--------------------------------------------------------------------------------
-- * A3
-- Make Expr an instance of Show (along the lines of the example in the lecture)
-- You can use Haskell notation for powers: x^2
-- You should show x^1 as just x.

instance Show Expr where
  show (Val n) = show n
  show (Pow 0) = "1"
  show (Pow 1) = "x"
  show (Pow n) = "x^" ++ show n
  show (Op expr1 AddOp expr2) = show expr1 ++ "+" ++ show expr2
  show (Op expr1 MulOp expr2) = show_mul expr1 expr2

show_mul :: Expr -> Expr -> String
show_mul (Op exp1 AddOp exp2) (Op exp3 AddOp exp4) = "(" ++ show (Op exp1 AddOp exp2) ++ ")(" ++ show (Op exp3 AddOp exp4) ++ ")"
show_mul (Op exp1 AddOp exp2) exp3 = "(" ++ show (Op exp1 AddOp exp2) ++ ")*" ++ show exp3
show_mul exp1 (Op exp2 AddOp exp3) = show exp1 ++ "(" ++ show (Op exp2 AddOp exp3) ++ ")"
show_mul exp1 exp2 = show exp1 ++ "*" ++ show exp2

--------------------------------------------------------------------------------
-- * A4
-- Make Expr an instance of Arbitrary.
-- Now you can check the data type invariant that you defined in A3 using
-- quickCheck

-- (Optional)
-- Add a definition of function shrink :: Expr -> [Expr] to Arbitrary
-- which gives hints to quickCheck on possible smaller expressions that it
-- could use to find a smaller counterexample for failing tests

-- instance Arbitrary Expr
--   where arbitrary = do
--     Val x <- choose [0..]
--     Pow y <- choose [1..]


--------------------------------------------------------------------------------
-- * A5
-- Define the eval function which takes a value for x and an expression and
-- evaluates it

eval :: Int -> Expr -> Int
eval = undefined


--------------------------------------------------------------------------------
-- * A6
-- Define
exprToPoly :: Expr -> Poly
-- Which converts an expression into a polynomial.
-- Here it is important to think recursively to just solve the bigger problem
-- by solving the smaller problems and combining them in the right way.

exprToPoly = undefined

-- Define (and check) prop_exprToPoly, which checks that evaluating the
-- polynomial you get from exprToPoly gives the same answer as evaluating
-- the expression

prop_exprToPoly = undefined

--------------------------------------------------------------------------------
-- * A7
-- Now define the function going in the other direction,
polyToExpr :: Poly -> Expr

polyToExpr = undefined


-- Write (and check) a quickCheck property for this function similar to
-- question 6. 
prop_polyToExpr = undefined

--------------------------------------------------------------------------------
-- * A8
-- Write a function
simplify :: Expr -> Expr
-- which simplifies an expression by converting it to a polynomial
-- and back again
simplify = undefined

--------------------------------------------------------------------------------
-- * A9
-- Write a quickCheck property
prop_noJunk :: Expr -> Bool

--that checks that a simplified expression does not contain any "junk":
--where junk is defined to be multiplication by one or zero,
--addition of zero, addition or multiplication of numbers, or x to the
--power zero. (You may need to fix A7)

prop_noJunk = undefined

--------------------------------------------------------------------------------
