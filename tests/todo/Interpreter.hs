module Interpreter where 
{-@ LIQUID "--totality" @-}

data BinOp = Plus | Times
data Exp   = EConst Int | EBinOp BinOp Exp Exp

data Instr = IConst Int | IBinOp BinOp

type Prog  = [Instr]
type Stack = [Int]

{-@ measure binOpDenote @-}
binOpDenote :: Int -> Int -> BinOp -> Int -- (Int -> Int -> Int)
binOpDenote x y Plus  = (x+y)
binOpDenote x y Times = (x*y)

{-@ measure expDenote :: Exp -> Int @-}
expDenote :: Exp -> Int 
expDenote (EConst n)       = n
expDenote (EBinOp b e1 e2) = (\x y -> binOpDenote x y b) (expDenote e1) (expDenote e2)

instrDenote :: Stack -> Instr -> Maybe Stack
instrDenote s       (IConst n) = Just (n:s)
instrDenote (x:y:s) (IBinOp b) = Just ((\x y -> binOpDenote x y b) x y:s)
instrDenote _        _         = Nothing

{- measure progDenote :: Stack -> Prog -> Maybe Stack @-}
progDenote :: Stack -> Prog -> Maybe Stack
progDenote s [] = Just s
progDenote s (x:xs) | Just s' <- instrDenote s x = progDenote s' xs
                    | otherwise                  = Nothing

{- compile :: e:Exp -> {v:Prog | (progDenote [] v) == Just ([(expDenote e)])} @-}
compile :: Exp -> Prog
compile (EConst n)       = [IConst n]
compile (EBinOp b e1 e2) = compile e2 ++ compile e1 ++ [IBinOp b] 


-- Termination Annotations
{-@ data Exp [expSize] @-}
{-@ invariant {v:Exp | expSize v >= 0} @-}

{-@ measure expSize @-}
expSize :: Exp -> Int
expSize (EConst _) = 0
expSize (EBinOp _ e1 e2) = 1 + (expSize e1) + (expSize e2)

{-@ Decrease progDenote 2 @-}
