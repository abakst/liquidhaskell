module Blank (foo) where


-- This is unsoundly safe without the native flag. 
{-@ LIQUID "--native" @-}

-- This is a blank file.

data G = A | B

{-@ foo :: Int -> {v:G | v = A} @-}
foo  :: Int -> G
foo _ = B


