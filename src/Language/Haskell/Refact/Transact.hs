{-# LANGUAGE ScopedTypeVariables, RankNTypes, BangPatterns #-}
-----------------------------------------------------------------------------
--
-- Module      :  Language.Haskell.Refact.Transact
-- Copyright   :
-- License     :  BSD3
--
-- Maintainer  :  Chris Brown
-- Stability   :  Provisional
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Language.Haskell.Refact.Transact (
  transact
) where

import qualified Data.Generics.Schemes as SYB
import qualified Data.Generics.Aliases as SYB
import qualified GHC.SYB.Utils         as SYB

import qualified FastString            as GHC
import qualified Name                  as GHC
import qualified GHC
import qualified DynFlags              as GHC
import qualified Outputable            as GHC
import qualified MonadUtils            as GHC
import qualified RdrName               as GHC
import qualified OccName               as GHC
import qualified SrcLoc                as GHC
import qualified Module                as GHC
import NameSet

import GHC.Paths ( libdir )
import Control.Monad
import Control.Monad.State
import Data.Data
import Data.Maybe
import Data.List (isPrefixOf)
-----------------

import Language.Haskell.Refact.Utils
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils


{-import Language.Haskell.Refact.Utils
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils
import Language.Haskell.Refact.Utils.TokenUtils-}

import Debug.Trace

transact :: [String] -> IO ()
transact args = do
    runRefacSession Nothing (comp Nothing fileName (row,col))
    return () where
        fileName = ghead "filename" args
        row = read (args!!1)::Int
        col = read (args!!2)::Int

comp :: Maybe FilePath -> String -> SimpPos
     -> RefactGhc [ApplyRefacResult]	
comp maybeMainFile fileName (row, col) = do
       loadModuleGraphGhc maybeMainFile
       modInfo@(t, _tokList) <- getModuleGhc fileName
       renamed <- getRefactRenamed
       parsed  <- getRefactParsed
       -- modInfo@((_, renamed, mod), toks) <- parseSourceFileGhc fileName
       -- putStrLn $ showParsedModule mod
       -- let pnt = locToPNT fileName (row, col) mod

       -- 1) get variable name
       let pnt = locToPNT (GHC.mkFastString fileName) (row, col) renamed
       let name = locToName (GHC.mkFastString fileName) (row, col) renamed
       -- error (SYB.showData SYB.Parser 0 name)

       case name of
            (Just pn) -> do refactoredMod@(_, (t, s)) <- applyRefac (doTransact pnt pn) (Just modInfo) fileName
                            return [refactoredMod]
            Nothing   -> error "Incorrect identifier selected!"
       --if isFunPNT pnt mod    -- Add this back in ++ CMB +++
       -- then do
              --        rs <-if isExported pnt exps
       --               then  applyRefacToClientMods (doSwap pnt) fileName
       --               else  return []
       -- writeRefactoredFiles False (r:rs)
       -- else error "\nInvalid cursor position!"

       -- putStrLn (showToks t)
       -- writeRefactoredFiles False [refactoredMod]
       -- putStrLn ("here" ++ (SYB.showData SYB.Parser 0 mod))  -- $ show [fileName, beginPos, endPos]
       -- putStrLn "Completd"


doTransact ::
 PNT -> (GHC.Located GHC.Name) -> RefactGhc () -- m GHC.ParsedSource
doTransact pnt@(PNT (GHC.L _ _)) name@(GHC.L s n) = do
    inscopes <- getRefactInscopes
    renamed  <- getRefactRenamed
    parsed   <- getRefactParsed
    reallyDoTransact pnt name renamed


reallyDoTransact :: PNT -> (GHC.Located GHC.Name) -> GHC.RenamedSource -> RefactGhc ()
reallyDoTransact pnt@(PNT (GHC.L _ _)) name@(GHC.L s n1) renamed = do

    --newImports <- addImportDecl stmModuleName (renamedImports renamed)
    --renamed' <- return $ changeImportsRenamed renamed newImports

    -- Commenting out the type signature changes, for now.
    -- Once I'm confident on the main workings of the refactoring,
    -- then I'll focus on refactoring the type signature.

    -- 2) get its binding(s)
    let binding      = listifyStaged SYB.Renamer (isDesiredBinding n1) renamed
    -- 3) get its applications
    let applications = listifyStaged SYB.Renamer (isDesiredApplication n1) renamed

    -- 4.1) separate applications different from the concurrency functions
    let uncommonApps = filter (not . appMatchesDefaultConc) applications

    let commonApps   = filter appMatchesDefaultConc applications

    let commonApps2  = filterLExpr commonApps []    

    let appStarts    = map startEndLineCol commonApps2

    renamed' <- everywhereMStaged SYB.Renamer (SYB.mkM inMod `SYB.extM` (inExp appStarts) {-`SYB.extM` inType -}) renamed -- this needs to be bottom up +++ CMB +++
--    liftIO $ putStrLn ("inMatch>" ++ SYB.showData SYB.Parser 0 renamed'{-(GHC.L x (GHC.VarPat n2))-} ++ "<")
    putRefactRenamed renamed'

    return ()
    liftIO $ putStrLn $ "Found name? "++(show (isJust (getName "Control.Concurrent.STM.TMVar.newEmptyTMVarIO" renamed)))
    liftIO $ putStrLn $"Number of applications "++ (show $ length applications) ++ " " ++ (GHC.showPpr applications)
    liftIO $ putStrLn $"Number of uncommon functions "++ (show $ length uncommonApps) ++ " " ++ (SYB.showData SYB.Renamer 0 uncommonApps)
    liftIO $ putStrLn $"Number of common functions "++ (show $ length commonApps2) ++ " " ++ (GHC.showPpr commonApps2)--(SYB.showData SYB.Renamer 0 commonApps2)
    liftIO $ putStrLn $"Number of bindings "++ (show $ length binding) ++ " " ++ (SYB.showData SYB.Renamer 0 binding)
--(GHC.showPpr binding)

--    liftIO $ putStrLn $"test> "++ (SYB.showData SYB.Renamer 0 renamed)

    where
         atomicallyName :: RefactGhc GHC.Name
         atomicallyName = do
                 let maybeAtomName = getName "atomically" renamed
                 if isJust maybeAtomName then return $ fromJust maybeAtomName
                 else mkNewGhcName "atomically"

         startLineCol :: GHC.Located a -> (Int,Int)
         startLineCol (GHC.L l _) = 
                 let 
                     rsspan    = realSrcSpan l 
                     startLine = GHC.srcSpanStartLine rsspan
                     startCol  = GHC.srcSpanStartCol rsspan
                 in (startLine, startCol)

         startEndLineCol :: GHC.Located a -> ((Int,Int),(Int,Int))
         startEndLineCol (GHC.L l _) =
                 let
                     rsspan    = realSrcSpan l
                     startLine = GHC.srcSpanStartLine rsspan
                     startCol  = GHC.srcSpanStartCol rsspan
                     endLine   = GHC.srcSpanEndLine rsspan
                     endCol    = GHC.srcSpanEndCol rsspan
                 in ((startLine, startCol),(endLine,endCol))


         filterLExpr :: [GHC.LHsExpr GHC.Name] -> [(Int, Int)] -> [GHC.LHsExpr GHC.Name]
         filterLExpr (lexpr:lexprs) initialPositions = 
                 let 
                     new = not $ elem (startLineCol lexpr) initialPositions
                 in
                     if new then lexpr : (filterLExpr lexprs $ (startLineCol lexpr):initialPositions)
                     else filterLExpr lexprs initialPositions
         filterLExpr [] _ = []

         stmModuleName = GHC.mkModuleName "Control.Concurrent.STM"

         renamedImports :: GHC.RenamedSource -> [GHC.Located (GHC.ImportDecl GHC.Name)]
         renamedImports (a,b,c,d) = b

         changeImportsRenamed ::
             GHC.RenamedSource -> [GHC.Located (GHC.ImportDecl GHC.Name)] -> GHC.RenamedSource
         changeImportsRenamed (a, oldImports, c, d) newImports = (a, newImports, c, d)

         -- modifying the bindstatement
         -- apparently runs on SYB monad
         inMod (bindSt@(GHC.BindStmt
            (GHC.L x (GHC.VarPat n2))
            oldf@(GHC.L y (GHC.HsVar nv)) z w )::(GHC.StmtLR GHC.Name GHC.Name))
              | GHC.nameUnique n1 == GHC.nameUnique n2
                = do
                    liftIO $ putStrLn ("inMatch>" ++ SYB.showData SYB.Parser 0 bindSt{-(GHC.L x (GHC.VarPat n2))-} ++ "<")
                    newName <- (\x -> if isJust x then mkNewGhcName (fromJust x)
                                      else return nv) $ case nameToString nv of 
                                    "GHC.MVar.newEmptyMVar" -> Just "newEmptyTMVarIO"
                                    "GHC.MVar.newMVar"      -> Just "Control.Concurrent.STM.TMVar.newTMVarIO"
                                    _                       -> Nothing --(nameToString nv)
                    liftIO $ putStrLn $ nameToString nv
                    liftIO $ putStrLn $ nameToString newName
                    --liftIO $ putStrLn $ show $ GHC.nameUnique oldName
                    -- liftIO $ putStrLn $ show $ (GHC.nameUnique oldName) == (GHC.nameUnique nv)
                    --replacedFunction <- changeFunctionName nv
                    --oldf <- return (GHC.L y (GHC.HsVar nv))
                    newf <- newFuncName oldf newName
                    newBindSt <- return (GHC.BindStmt (GHC.L x (GHC.VarPat n2)) newf z w)
                    liftIO $ putStrLn ("inChanged>" ++ SYB.showData SYB.Parser 0 newBindSt{-(GHC.L x (GHC.VarPat n2))-} ++ "<")
                    liftIO $ putStrLn ("Location changed>" ++ (show y)++"<<")
                    updateToks oldf newf GHC.showPpr False
                    return newBindSt
                    --return bindSt
         inMod (bindSt@(GHC.BindStmt
            (GHC.L x (GHC.VarPat n2))
            (GHC.L _ (GHC.HsApp oldf@(GHC.L y (GHC.HsVar nv)) _ )) z w )::(GHC.StmtLR GHC.Name GHC.Name))
              | GHC.nameUnique n1 == GHC.nameUnique n2
                = do
                    liftIO $ putStrLn ("inMatch>" ++ SYB.showData SYB.Parser 0 bindSt{-(GHC.L x (GHC.VarPat n2))-} ++ "<")
                    newName <- (\x -> if isJust x then mkNewGhcName (fromJust x)
                                      else return nv) $ case nameToString nv of 
                                    "GHC.MVar.newEmptyMVar" -> Just "newEmptyTMVarIO"
                                    "GHC.MVar.newMVar"      -> Just "Control.Concurrent.STM.TMVar.newTMVarIO"
                                    _                       -> Nothing --(nameToString nv)
                    liftIO $ putStrLn $ nameToString nv
                    liftIO $ putStrLn $ nameToString newName
                    --liftIO $ putStrLn $ show $ GHC.nameUnique oldName
                    -- liftIO $ putStrLn $ show $ (GHC.nameUnique oldName) == (GHC.nameUnique nv)
                    --replacedFunction <- changeFunctionName nv
                    --oldf <- return (GHC.L y (GHC.HsVar nv))
                    newf <- newFuncName oldf newName
                    newBindSt <- return (GHC.BindStmt (GHC.L x (GHC.VarPat n2)) newf z w)
                    liftIO $ putStrLn ("inChanged>" ++ SYB.showData SYB.Parser 0 newBindSt{-(GHC.L x (GHC.VarPat n2))-} ++ "<")
                    liftIO $ putStrLn ("Location changed>" ++ (show y)++"<<")
                    updateToks oldf newf GHC.showPpr False
                    return newBindSt
                    --return bindSt

         inMod func = return func

         -- /modifying the bindstatement

         -- 1. The definition is at top level...
         -- não queremos que seja top level!
         -- e o FunBind deve ser apenas de variável, ou de função?
         {-inMod (func@(GHC.FunBind (GHC.L x n2) infixity (GHC.MatchGroup matches p) a locals tick)::(GHC.HsBindLR GHC.Name GHC.Name ))
            | GHC.nameUnique n1 == GHC.nameUnique n2
                    = do liftIO $ putStrLn ("inMatch>" ++ SYB.showData SYB.Parser 0 (GHC.L x n2) ++ "<")
                         newMatches <- updateMatches matches
                         return (GHC.FunBind (GHC.L x n2) infixity (GHC.MatchGroup newMatches p) a locals tick)
         inMod func = return func-}

         -- Change call sites
         inExp selectedApps exp@((GHC.L l app@(GHC.HsApp _ _))::GHC.Located (GHC.HsExpr GHC.Name))
            | (startEndLineCol exp) `elem` selectedApps
                   = do
                    atomName <- atomicallyName
                    newAtomName <- return $ atomName --{
                                               -- Name.n_sort :: Name.NameSort,
                                               -- Name.n_occ :: !GHC.OccName,
                                               -- Name.n_uniq :: FastTypes.FastInt,
                                      --         GHC.n_loc = l-- !GHC.SrcSpan
                                           -- }
                    translatedTree <- translateHsApp True {-atomName-} app
                    updateToks exp (GHC.L l translatedTree) (GHC.showPpr) False
                    return (GHC.L l translatedTree) -- update e2 e1 =<< update e1 e2 exp
         inExp _ e = return e

         -- 3. Type signature...
         -- <turned off for now>
         inType ty@(GHC.L x (GHC.TypeSig [GHC.L x2 name] types)::GHC.LSig GHC.Name)
           | GHC.nameUnique name == GHC.nameUnique n1
                = do let (t1:t2:ts) = tyFunToList types
                     t1' <- update t1 t2 t1
                     t2' <- update t2 t1 t2
                     return (GHC.L x (GHC.TypeSig [GHC.L x2 name] (tyListToFun (t1':t2':ts))))
                     --return ty

         inType ty@(GHC.L x (GHC.TypeSig (n:ns) types)::GHC.LSig GHC.Name)
           | GHC.nameUnique n1 `elem` (map (\(GHC.L _ n) -> GHC.nameUnique n) (n:ns))
            = error "Error in swapping arguments in type signature: signature bound to muliple entities!"

         inType ty = return ty

         tyFunToList (GHC.L _ (GHC.HsForAllTy _ _ _ (GHC.L _ (GHC.HsFunTy t1 t2)))) = t1 : (tyFunToList t2)
         tyFunToList (GHC.L _ (GHC.HsFunTy t1 t2)) = t1 : (tyFunToList t2)
         tyFunToList t = [t]

         tyListToFun [t1] = t1
         tyListToFun (t1:ts) = GHC.noLoc (GHC.HsFunTy t1 (tyListToFun ts))
         -- </turned off for now>

         updateMatches [] = return []
         updateMatches (i@(GHC.L x m@(GHC.Match pats nothing rhs)::GHC.Located (GHC.Match GHC.Name)):matches)
           = case pats of
               (p1:p2:ps) -> do p1' <- update p1 p2 p1
                                p2' <- update p2 p1 p2
                                matches' <- updateMatches matches
                                return ((GHC.L x (GHC.Match (p1':p2':ps) nothing rhs)):matches')

instance Eq id => Eq (GHC.HsExpr id)

newFuncName (GHC.L y (GHC.HsVar nv)) newf = return (GHC.L y' (GHC.HsVar newf)) where
    realSpan = realSrcSpan y
    srcFile = GHC.srcSpanFile realSpan
    startLine = 1--GHC.srcSpanStartLine realSpan
    endLine = 1--GHC.srcSpanEndLine realSpan
    startCol = 1--GHC.srcSpanStartCol realSpan
    endCol = 1--GHC.srcSpanEndCol realSpan
    nameEndDelta = (length (nameToString newf)) - (length (nameToString nv))
    y' = GHC.mkSrcSpan (GHC.mkSrcLoc srcFile startLine startCol) (GHC.mkSrcLoc srcFile endLine (endCol {-+ nameEndDelta-}))


getLocationTesting (GHC.L y (GHC.HsVar nv)) = y


-- | Remove ImportDecl from the imports list, commonly returned from a RenamedSource type, so it can
-- be further processed.  
rmPreludeImports :: [GHC.Located (GHC.ImportDecl GHC.Name)] -> [GHC.Located (GHC.ImportDecl GHC.Name)]
rmPreludeImports = filter isPrelude where
            isPrelude = (/="Prelude") . GHC.moduleNameString . GHC.unLoc . GHC.ideclName . GHC.unLoc


prettyprint :: (GHC.Outputable a) => a -> String
--prettyprint x = GHC.showSDoc $ GHC.ppr x
prettyprint  = GHC.showPpr 

-- filter for 2) get its binding(s)
isDesiredBinding :: GHC.Name -> GHC.StmtLR GHC.Name GHC.Name -> Bool
isDesiredBinding n1 ((GHC.BindStmt
            (GHC.L x (GHC.VarPat n2))
            (GHC.L y (GHC.HsVar nv)) z w )::(GHC.StmtLR GHC.Name GHC.Name))
            = GHC.nameUnique n1 == GHC.nameUnique n2
isDesiredBinding n1 ((GHC.BindStmt
            (GHC.L x (GHC.VarPat n2))
            (GHC.L y (GHC.HsApp (GHC.L _ (GHC.HsVar nv)) _)) z w )::(GHC.StmtLR GHC.Name GHC.Name))
            = GHC.nameUnique n1 == GHC.nameUnique n2
isDesiredBinding _ _ = False

-- filter for 3) get its applications
isDesiredApplication :: GHC.Name -> GHC.LHsExpr GHC.Name -> Bool 
isDesiredApplication n1 (GHC.L _ (GHC.HsApp inApp@(GHC.L _ (GHC.HsApp _ _)) _ {-(GHC.L _ (GHC.HsVar nv))-})) 
             = isDesiredApplication n1 inApp --GHC.nameUnique n1 == GHC.nameUnique nv
isDesiredApplication n1 (GHC.L _ (GHC.HsApp _ (GHC.L _ (GHC.HsVar nv))))  
             = GHC.nameUnique n1 == GHC.nameUnique nv              
--isDesiredApplication _ (GHC.L _ (GHC.HsApp _ _ )) = True
isDesiredApplication _ _ = False

-- | Looks for the function being applied by a GHC.HsApp, and matches it
-- with known concurrency modules' names.
appMatchesDefaultConc :: GHC.LHsExpr GHC.Name -> Bool
appMatchesDefaultConc (GHC.L _ (GHC.HsApp (GHC.L _ (GHC.HsWrap _ (GHC.HsVar n))) _ )) = -- HsWrap for TypecheckedSource 
        nameMatchesDefaultConc n
appMatchesDefaultConc (GHC.L _ (GHC.HsApp (GHC.L _  (GHC.HsVar n)) _ )) = -- HsVar directly for RenamedSource 
        nameMatchesDefaultConc n
appMatchesDefaultConc (GHC.L _ (GHC.HsApp insideApp@(GHC.L _ (GHC.HsApp _ _)) _)) = 
        appMatchesDefaultConc insideApp
appMatchesDefaultConc _ = False


mkNewL :: a -> GHC.Located a
mkNewL a = (GHC.L l a) where
    filename = (GHC.mkFastString "f")
    l = GHC.mkSrcSpan (GHC.mkSrcLoc filename 1 1) (GHC.mkSrcLoc filename 1 1)

-- | Matches a GHC.Name reference with known concurrency modules' names.
nameMatchesDefaultConc :: GHC.Name -> Bool
nameMatchesDefaultConc n = matchesDefaultConc $ nameToString n


-- | Matches a String beginning with one of known concurrency modules' names.
matchesDefaultConc :: String -> Bool
matchesDefaultConc text = matchesAnyPrefix ["GHC.MVar.", "Control.Concurrent.", "GHC.Conc.Sync"] text


-- | Tries to match a list of prefixes to a String. True if any matches.
matchesAnyPrefix :: [String] -- ^ Prefixes
                 -> String -- ^ String to be matched
                 -> Bool
matchesAnyPrefix prefixes text = or [ x `isPrefixOf` text | x <- prefixes ]


translateFunction :: GHC.Name -> RefactGhc GHC.Name 
translateFunction n =
    mkNewGhcName $ case nameToString n of 
        "GHC.MVar.takeMVar" -> {-"Control.Concurrent.STM.TMVar.-}"takeTMVar"
        "GHC.MVar.putMVar"  -> {-"Control.Concurrent.STM.TMVar.-}"putTMVar"
        _                   -> nameToString n

testeTranslateNull :: GHC.Name -> RefactGhc GHC.Name
testeTranslateNull n =
    mkNewGhcName $ case nameToString n of 
        "GHC.MVar.takeMVar" -> {-"Control.Concurrent.STM.TMVar.-}"atomically"
        "GHC.MVar.putMVar"  -> {-"Control.Concurrent.STM.TMVar.-}"atomically"
        _                   -> nameToString n

-- | Translates the calling function from this HsApp.
--
-- Author's note: I wrote this function top pattern match in one go, reloaded GHCi, 
-- and it showed no errors. I gotta say I felt pretty proud about myself right then.
--        
translateHsApp :: Bool -- ^ Is this function the topmost application? Deals with  
                       -- recursive HsApp's, as in functions with multiple arguments.
--               -> GHC.Name -- ^Name for atomically call.
               -> GHC.HsExpr GHC.Name -- ^ The application to be refactored.
               -> RefactGhc ( GHC.HsExpr GHC.Name )
translateHsApp isTopNode {-atomicallyName-} (GHC.HsApp (GHC.L l insideApp@(GHC.HsApp _ _)) exp2 ) = do
    translatedLeaf <- translateHsApp False {-atomicallyName-} insideApp
    translatedNode <- if isTopNode then do
                     atomicallyName <- mkNewGhcName "atomically"
                     return $ GHC.HsApp 
                                  ({-GHC.L l-}mkNewL (GHC.HsVar atomicallyName)) 
                                  ({-GHC.L l-}mkNewL (GHC.HsPar ({-GHC.L l-}mkNewL (GHC.HsApp 
                                                                   ({-GHC.L l-}mkNewL translatedLeaf) 
                                                                    exp2
                                                            ))))
                   else 
                       return $ GHC.HsApp 
                                    ({-GHC.L l-}mkNewL translatedLeaf) 
                                     exp2
                                
    return translatedNode
translateHsApp isTopNode {-atomicallyName-} (GHC.HsApp (GHC.L l (GHC.HsVar functionName)) (GHC.L l2 exp2)) = do
    tmfunction <- translateFunction functionName
    let translatedNode = GHC.HsApp ({-GHC.L l-}mkNewL (GHC.HsVar tmfunction)) ({-GHC.L l-}mkNewL exp2)
    if isTopNode then do
        atomicallyName <- testeTranslateNull functionName --mkNewGhcName "atomically"
        return $ GHC.HsApp 
                ({-GHC.L l-}mkNewL (GHC.HsVar atomicallyName)) 
                ({-GHC.L l-}mkNewL (GHC.HsPar (GHC.L l translatedNode )))
    else 
        return translatedNode 
--    return translatedNode
translateHsApp _ {-_-} x = return x


realSrcSpan :: GHC.SrcSpan -> GHC.RealSrcSpan
realSrcSpan (GHC.RealSrcSpan rssp) = rssp
realSrcSpan _ = error "SrcSpan is not real"

-- ===========================
-- SYB temp
-- ===========================

-- | Checks whether the current item is undesirable for analysis in the current
-- AST Stage.
checkItemStage stage x = (const False `SYB.extQ` postTcType `SYB.extQ` fixity `SYB.extQ` nameSet) x
  where nameSet    = const (stage `elem` [SYB.Parser,SYB.TypeChecker]) :: NameSet    -> Bool
        postTcType = const (stage<SYB.TypeChecker)                     :: GHC.PostTcType -> Bool
        fixity     = const (stage<SYB.Renamer)                         :: GHC.Fixity -> Bool

-- | Staged variation of SYB.everything
-- The stage must be provided to avoid trying to modify elements which
-- may not be present at all stages of AST processing.
everythingStaged :: SYB.Stage -> (r -> r -> r) -> r -> SYB.GenericQ r -> SYB.GenericQ r
everythingStaged stage k z f x
  | checkItemStage stage x = z
  | otherwise = foldl k (f x) (gmapQ (everythingStaged stage k z f) x)


-- listify :: Typeable r => (r -> Bool) -> GenericQ [r]
-- listify p = everything (++) ([] `mkQ` (\x -> if p x then [x] else []))

-- | Staged variation of SYB.listify
-- The stage must be provided to avoid trying to modify elements which
-- may not be present at all stages of AST processing.
listifyStaged stage p = everythingStaged stage (++) [] ([] `SYB.mkQ` (\x -> [ x | p x ]))





{-newSrcSpan :: GHC.SrcSpan -> GHC.Name -> GHC.Name -> RefactGhc GHC.SrcSpan
newSrcSpan srcSpan@(GHC.RealSrcSpan realSrcSpan) oldName newName
        | GHC.isOneLineSpan srcSpan = do
            newNameDiffersBy <- return $ (length (nameToString newName)) - (length (nameToString oldName))
            oldSrcSpanEndCol <- return $ GHC.srcSpanEndCol realSrcSpan
            newSrcSpanEndCol <- return $ oldSrcSpanEndCol - newNameDiffersBy
            return srcSpan
        | otherwise = return srcSpan


--newSrcSpan otherspan _ _ = return otherspan-}


{-        inMatch i@(GHC.L x m@(GHC.Match (p1:p2:ps) nothing rhs)::GHC.Located (GHC.Match GHC.RdrName) )
		  -- = error (SYB.showData SYB.Parser 0 pnt)
            | GHC.srcSpanStart s == GHC.srcSpanStart x
              = do liftIO $ putStrLn ("inMatch>" ++ SYB.showData SYB.Parser 0 (p1:p2:ps) ++ "<")
                   p1' <- update p1 p2 p1 --pats
                   p2' <- update p2 p1 p2
                   return (GHC.L x (GHC.Match (p1':p2':ps) nothing rhs))
        inMatch i = return i

        inExp exp@((GHC.L x (GHC.HsApp (GHC.L y (GHC.HsApp e e1)) e2))::GHC.Located (GHC.HsExpr GHC.RdrName))
          {- | (fromJust $ expToName e) == (GHC.L s (GHC.nameRdrName n))-} -- = error (SYB.showData SYB.Parser 0 (GHC.L s (GHC.nameRdrName n)))  -- update e2 e1 =<< update e1 e2 exp
       -- inExp e = return e -}
        -- In the call-site.
   {- inExp exp@((Exp (HsApp (Exp (HsApp e e1)) e2))::HsExpP)
      | expToPNT e == pnt
      = update e2 e1 =<< update e1 e2 exp
    inExp e = return e -}
-- pats nothing rhss ds)

-- expToPNT x = undefined


