{-# LANGUAGE BangPatterns, CPP, MagicHash, NondecreasingIndentation #-}

module Language.Haskell.Liquid.Desugar710.HscMain (hscDesugarWithLoc) where

import Language.Haskell.Liquid.Desugar710.Desugar (deSugarWithLoc)
import Module
import Lexer
import TcRnMonad
import ErrUtils
import HscTypes
import Bag
import Exception

#include "HsVersions.h"

getWarnings :: Hsc WarningMessages
getWarnings = Hsc $ \_ w -> return (w, w)

clearWarnings :: Hsc ()
clearWarnings = Hsc $ \_ _ -> return ((), emptyBag)

logWarnings :: WarningMessages -> Hsc ()
logWarnings w = Hsc $ \_ w0 -> return ((), w0 `unionBags` w)

getHscEnv :: Hsc HscEnv
getHscEnv = Hsc $ \e w -> return (e, w)

handleWarnings :: Hsc ()
handleWarnings = do
    dflags <- getDynFlags
    w <- getWarnings
    liftIO $ printOrThrowWarnings dflags w
    clearWarnings

-- | Throw some errors.
throwErrors :: ErrorMessages -> Hsc a
throwErrors = liftIO . throwIO . mkSrcErr

ioMsgMaybe :: IO (Messages, Maybe a) -> Hsc a
ioMsgMaybe ioA = do
    ((warns,errs), mb_r) <- liftIO ioA
    logWarnings warns
    case mb_r of
        Nothing -> throwErrors errs
        Just r  -> ASSERT( isEmptyBag errs ) return r

hscDesugar :: HscEnv -> ModSummary -> TcGblEnv -> IO ModGuts
hscDesugar hsc_env mod_summary tc_result =
    runHsc hsc_env $ hscDesugar' (ms_location mod_summary) tc_result

hscDesugar' :: ModLocation -> TcGblEnv -> Hsc ModGuts
hscDesugar' mod_location tc_result = do
    hsc_env <- getHscEnv
    r <- ioMsgMaybe $
      {-# SCC "deSugar" #-}
      deSugarWithLoc hsc_env mod_location tc_result

    -- always check -Werror after desugaring, this is the last opportunity for
    -- warnings to arise before the backend.
    handleWarnings
    return r
