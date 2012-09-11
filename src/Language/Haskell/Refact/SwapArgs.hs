{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Refact.SwapArgs (swapArgs) where

import qualified Data.Generics.Schemes as SYB
import qualified Data.Generics.Aliases as SYB
import qualified GHC.SYB.Utils         as SYB

import qualified GHC
import qualified DynFlags              as GHC
import qualified Outputable            as GHC
import qualified MonadUtils            as GHC
import qualified RdrName               as GHC
import qualified OccName               as GHC
 
import GHC.Paths ( libdir )
import Control.Monad
import Control.Monad.State
import Data.Data
-----------------

import Language.Haskell.Refact.Utils 
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.LocUtils

import Debug.Trace

swapArgs :: [String] -> IO () -- For now
swapArgs args
  = do let fileName = args!!0              
           row = (read (args!!1)::Int)
           col = (read (args!!2)::Int)	
       modInfo@((_, _, mod), toks) <- parseSourceFile fileName 
       -- putStrLn $ showParsedModule mod
       let pnt = locToPNT fileName (row, col) mod  

       --if isFunPNT pnt mod    -- Add this back in ++ CMB +++
       -- then do 
       refactoredMod@(_, (t, s)) <- applyRefac (doSwap pnt) (Just modInfo) fileName
       --        rs <-if isExported pnt exps 
       --               then  applyRefacToClientMods (doSwap pnt) fileName
       --               else  return []
       -- writeRefactoredFiles False (r:rs)      
       -- else error "\nInvalid cursor position!"
       
       -- putStrLn (showToks t)
       writeRefactoredFiles False [refactoredMod]  
       -- putStrLn ("here" ++ (SYB.showData SYB.Parser 0 mod))  -- $ show [fileName, beginPos, endPos]
       putStrLn "Completd"


doSwap ::
  GHC.GenLocated GHC.SrcSpan GHC.RdrName  
  -> (t, [GHC.LIE GHC.RdrName], GHC.ParsedSource) -> Refact GHC.ParsedSource -- m GHC.ParsedSource
doSwap pnt@(GHC.L s _) (_ , _, mod) 
    = {-error (SYB.showData SYB.Parser 0 pnt) -- -} everywhereMStaged SYB.Parser (SYB.mkM inMatch `SYB.extM` inExp) mod -- this needs to be bottom up +++ CMB +++
    where
        inMatch i@(GHC.L x m@(GHC.Match (p1:p2:ps) nothing rhs)::GHC.Located (GHC.Match GHC.RdrName) )
		  -- = error (SYB.showData SYB.Parser 0 pnt) 
            | GHC.srcSpanStart s == GHC.srcSpanStart x
              = do liftIO $ putStrLn ("inMatch>" ++ SYB.showData SYB.Parser 0 (p1:p2:ps) ++ "<")
                   p1' <- update p1 p2 p1 --pats
                   p2' <- update p2 p1 p2
                   return (GHC.L x (GHC.Match (p1':p2':ps) nothing rhs))
        inMatch i = return i 
        
        inExp exp@((GHC.L x (GHC.HsApp (GHC.L y (GHC.HsApp e e1)) e2))::GHC.Located HsExpP)
          | expToPNT e == pnt = update e2 e1 =<< update e1 e2 exp
        inExp e = return e
        -- In the call-site.
   {- inExp exp@((Exp (HsApp (Exp (HsApp e e1)) e2))::HsExpP)
      | expToPNT e == pnt     
      = update e2 e1 =<< update e1 e2 exp     
    inExp e = return e -}
-- pats nothing rhss ds)

-- expToPNT x = undefined

prettyprint :: (GHC.Outputable a) => a -> String
prettyprint x = GHC.showSDoc $ GHC.ppr x