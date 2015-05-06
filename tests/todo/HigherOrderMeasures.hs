module Fixme where

data BinOp = Plus | Times

{-@ measure binOpDenote @-}
binOpDenote :: Int  ->  BinOp -> Int
binOpDenote x Plus  = (x + x)
binOpDenote x Times = (x * x)