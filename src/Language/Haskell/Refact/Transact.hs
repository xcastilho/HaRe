{-# LANGUAGE ScopedTypeVariables, RankNTypes, DoAndIfThenElse #-}
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
import qualified TypeRep               as GHC
import TyCon
import Var
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

import Debug.Trace

transact :: [String] -> IO ()
transact args = do
    runRefacSession Nothing Nothing (comp Nothing fileName (row,col))
    return () where
        fileName = ghead "filename" args
        row = read (args!!1)::Int
        col = read (args!!2)::Int

comp :: Maybe FilePath -> String -> SimpPos
     -> RefactGhc [ApplyRefacResult]	
comp maybeMainFile fileName (row, col) = do
       loadModuleGraphGhc maybeMainFile
       --modInfo@(t, _tokList) <- getModuleGhc fileName
       getModuleGhc fileName
--     /== type checking ==\
--       checkedModule <- getTypecheckedModule
--       let typeChecked = GHC.tm_typechecked_source checkedModule
--     \== type checking ==/
       renamed <- getRefactRenamed
       parsed  <- getRefactParsed

       -- 1) get variable name
       let pnt  = locToPNT (GHC.mkFastString fileName) (row, col) renamed
       let name = locToName (GHC.mkFastString fileName) (row, col) renamed
       -- error (SYB.showData SYB.Parser 0 name)

       case name of
            (Just pn) -> do (refactoredMod@(_, (t, s)), _) <- applyRefac (doTransact pnt pn) (RSFile fileName)
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


doTransact :: PNT -> GHC.Located GHC.Name -> RefactGhc () 
doTransact pnt@(PNT (GHC.L _ _)) name@(GHC.L s n) = do
    inscopes <- getRefactInscopes
    renamed  <- getRefactRenamed
    parsed   <- getRefactParsed
    typechecked <- liftM GHC.tm_typechecked_source getTypecheckedModule -- >>= (return.GHC.tm_typechecked_source)
    reallyDoTransact pnt name renamed typechecked
--    reallyDoTransact pnt name renamed


reallyDoTransact :: PNT -> GHC.Located GHC.Name -> GHC.RenamedSource -> GHC.TypecheckedSource-> RefactGhc ()
reallyDoTransact pnt@(PNT (GHC.L _ _)) name@(GHC.L s n1) renamed typechecked = do
--reallyDoTransact pnt@(PNT (GHC.L _ _)) name@(GHC.L s n1) renamed = do

    -- TODO: Add import declaration for STM module, if it doesn't exists.
    --newImports <- addImportDecl stmModuleName (renamedImports renamed)
    --renamed' <- return $ changeImportsRenamed renamed newImports

    -- Commenting out the type signature changes, for now.
    -- Once I'm confident on the main workings of the refactoring,
    -- then I'll focus on refactoring the type signature.

    -- 2) get its binding(s)
    let binding      = listifyStaged SYB.Renamer (isDesiredBinding n1) renamed

    let mainbind     = ghead "bindings" binding


--- === typechecking ===
    let typecheckedVars = listifyStaged SYB.TypeChecker (isOkVar n1) typechecked 
    let lVars = length typecheckedVars
    let typecheckedTypes = map varType typecheckedVars
    let rightTypes = filter isOkType typecheckedTypes
    let typenames = map getTypeName rightTypes
    liftIO $ putStrLn ("checkedVarsfound ("++(show lVars)++"):: "++ show (map (SYB.showData SYB.TypeChecker 0) typecheckedTypes)) --SYB.showData SYB.TypeChecker 0 typecheckedVars )
    liftIO $ putStrLn ("varsTypes: "++show typenames)
    let successful = (length typenames) == 1 && (head typenames) == "GHC.MVar.MVar"
    if not successful then
        error "Error: did not select an MVar variable."
    else do
--- === /typechecking ===

        -- 3) get its applications
        let applications = listifyStaged SYB.Renamer (isDesiredApplication n1) renamed

        -- 4.1) separate applications different from the concurrency functions
        let uncommonApps = filter (not . appMatchesDefaultConc) applications

        let commonApps   = filter appMatchesDefaultConc applications

        let commonApps2  = filterLExpr commonApps []    

        let appStarts    = map startEndLineCol commonApps2

        renamed' <- everywhereMStaged SYB.Renamer (SYB.mkM inMod `SYB.extM` inExp appStarts {-`SYB.extM` inType -}) renamed -- this needs to be bottom up +++ CMB +++
--        liftIO $ putStrLn ("inMatch>" ++ SYB.showData SYB.Parser 0 renamed'{-(GHC.L x (GHC.VarPat n2))-} ++ "<")
        putRefactRenamed renamed'

        liftIO $ putStrLn $ "Found name? "++show (isJust (getName "Control.Concurrent.STM.TMVar.newEmptyTMVarIO" renamed))
        liftIO $ putStrLn $"Number of applications "++ show (length applications) ++ " " ++ GHC.showPpr applications
        liftIO $ putStrLn $"Number of uncommon functions "++ show (length uncommonApps) ++ " " ++ SYB.showData SYB.Renamer 0 uncommonApps
        liftIO $ putStrLn $"Number of common functions "++ show (length commonApps2) ++ " " ++ GHC.showPpr commonApps2
        liftIO $ putStrLn $"Number of bindings "++ show (length binding) ++ " " ++ SYB.showData SYB.Renamer 0 binding
--(GHC.showPpr binding)

--        liftIO $ putStrLn $"test> "++ (SYB.showData SYB.Renamer 0 renamed)

      where

         startLineCol :: GHC.Located a -> (Int,Int)
         startLineCol  = fst . startEndLineCol

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
                     new = notElem (startLineCol lexpr) initialPositions
                 in
                     if new then lexpr : filterLExpr lexprs ( startLineCol lexpr : initialPositions)
                     else filterLExpr lexprs initialPositions
         filterLExpr [] _ = []

         stmModuleName = GHC.mkModuleName "Control.Concurrent.STM"

         renamedImports :: GHC.RenamedSource -> [GHC.Located (GHC.ImportDecl GHC.Name)]
         renamedImports (a,b,c,d) = b

         changeImportsRenamed ::
             GHC.RenamedSource -> [GHC.Located (GHC.ImportDecl GHC.Name)] -> GHC.RenamedSource
         changeImportsRenamed (a, oldImports, c, d) newImports = (a, newImports, c, d)

         -- modifying the bindstatement
         -- TODO: try to condense this two pattern-matches into one.
         inMod (bindSt@(GHC.BindStmt
            (GHC.L x (GHC.VarPat n2))
            oldf@(GHC.L y (GHC.HsVar nv)) z w )::(GHC.StmtLR GHC.Name GHC.Name))
              | GHC.nameUnique n1 == GHC.nameUnique n2
                = do
--                    liftIO $ putStrLn ("inMatch>" ++ SYB.showData SYB.Renamer 0 bindSt ++ "<")

-- ====  testing. it breaks the build!
--                    let typeOfPattern = typeOf (GHC.VarPat n2)
--                    liftIO $ putStrLn $ SYB.showData SYB.Parser 0 typeOfPattern
-- ==== /testing

                    newName <- translateFunction nv
                    newf <- newFuncName oldf newName
                    updateToks oldf newf GHC.showPpr False
                    return $ GHC.BindStmt (GHC.L x (GHC.VarPat n2)) newf z w
         inMod (bindSt@(GHC.BindStmt
            (GHC.L x (GHC.VarPat n2))
            oldf@(GHC.L l (GHC.HsApp (GHC.L y (GHC.HsVar nv)) exp2 )) z w )::(GHC.StmtLR GHC.Name GHC.Name))
              | GHC.nameUnique n1 == GHC.nameUnique n2
                = do
--                    liftIO $ putStrLn ("inMatch>" ++ SYB.showData SYB.Renamer 0 bindSt ++ "<")
--                    let typeOfPattern = typeOf (GHC.VarPat n2)
                    newName <- translateFunction nv
                    let newf = GHC.L l $ GHC.HsApp (GHC.L y (GHC.HsVar newName)) exp2
                    updateToks oldf newf GHC.showPpr False
                    return $ GHC.BindStmt (GHC.L x (GHC.VarPat n2)) newf z w
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
            | startEndLineCol exp `elem` selectedApps
                   = do
                    translatedTree <- translateHsApp True app
                    updateToks exp (GHC.L l translatedTree) GHC.showPpr False
                    return (GHC.L l translatedTree) 
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
           | GHC.nameUnique n1 `elem` map (\(GHC.L _ n) -> GHC.nameUnique n) (n:ns)
            = error "Error in swapping arguments in type signature: signature bound to muliple entities!"

         inType ty = return ty

         tyFunToList (GHC.L _ (GHC.HsForAllTy _ _ _ (GHC.L _ (GHC.HsFunTy t1 t2)))) = t1 : tyFunToList t2
         tyFunToList (GHC.L _ (GHC.HsFunTy t1 t2)) = t1 : tyFunToList t2
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
                                return (GHC.L x (GHC.Match (p1':p2':ps) nothing rhs):matches')

-- This was a simpler form to match HsExprs, but I think it was responsible 
-- for crashing the application. 
--instance Eq id => Eq (GHC.HsExpr id)

newFuncName (GHC.L y (GHC.HsVar nv)) newf = return (GHC.L y (GHC.HsVar newf)) 


-- | Remove ImportDecl from the imports list, commonly returned from a RenamedSource type, so it can
-- be further processed.  
rmPreludeImports :: [GHC.Located (GHC.ImportDecl GHC.Name)] -> [GHC.Located (GHC.ImportDecl GHC.Name)]
rmPreludeImports = filter isPrelude where
            isPrelude = (/="Prelude") . GHC.moduleNameString . GHC.unLoc . GHC.ideclName . GHC.unLoc


prettyprint :: (GHC.Outputable a) => a -> String
prettyprint  = GHC.showPpr 


-- | Gets the Located VarPat from a BindStmt, or errors if not a VarPat BindStmt.
getLVarPat :: GHC.StmtLR a a -> GHC.LPat a
getLVarPat (GHC.BindStmt loc@(GHC.L _ (GHC.VarPat _)) _ _ _) = loc
getLVarPat _ = error "Not a Var binding."

getNameLPat :: GHC.LPat GHC.Name -> GHC.Name
getNameLPat (GHC.L _ (GHC.VarPat name)) = name
getNameLPat _ = error "Not a Var pattern."

isTyVarTy :: GHC.Type -> Bool
isTyVarTy = undefined --(TypeRep.TyVarTy _) = True
--isTyVarTy _ = False

isOkVar :: GHC.Name -> Var -> Bool
isOkVar name variable = GHC.nameUnique name == GHC.nameUnique ( varName variable ) 

isOkType :: GHC.Type -> Bool
isOkType (GHC.TyConApp _ _) = True
isOkType _ = False

getTypeName :: GHC.Type -> String
getTypeName (GHC.TyConApp tycon _) = (nameToString . TyCon.tyConName) tycon
getTypeName _ = []

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
isDesiredApplication n1 (GHC.L _ (GHC.HsApp inApp@(GHC.L _ (GHC.HsApp _ _)) _ )) 
             = isDesiredApplication n1 inApp 
isDesiredApplication n1 (GHC.L _ (GHC.HsApp _ (GHC.L _ (GHC.HsVar nv))))  
             = GHC.nameUnique n1 == GHC.nameUnique nv              
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
mkNewL = GHC.L l where
    filename = GHC.mkFastString "f"
    l = GHC.mkSrcSpan (GHC.mkSrcLoc filename 1 1) (GHC.mkSrcLoc filename 1 1)

-- | Matches a GHC.Name reference with known concurrency modules' names.
nameMatchesDefaultConc :: GHC.Name -> Bool
nameMatchesDefaultConc n = matchesDefaultConc $ nameToString n


-- | Matches a String beginning with one of known concurrency modules' names.
matchesDefaultConc :: String -> Bool
matchesDefaultConc = matchesAnyPrefix ["GHC.MVar.", "Control.Concurrent.", "GHC.Conc.Sync"] 


-- | Tries to match a list of prefixes to a String. True if any matches.
matchesAnyPrefix :: [String] -- ^ Prefixes
                 -> String -- ^ String to be matched
                 -> Bool
matchesAnyPrefix prefixes text = or [ x `isPrefixOf` text | x <- prefixes ]


translateFunction :: GHC.Name -> RefactGhc GHC.Name 
translateFunction n =
    mkNewGhcName $ case nameToString n of 
        "GHC.MVar.takeMVar"     -> "takeTMVar"
        "GHC.MVar.putMVar"      -> "putTMVar"
        "GHC.MVar.newEmptyMVar" -> "newEmptyTMVarIO"
        "GHC.MVar.newMVar"      -> "newTMVarIO"
        "GHC.MVar.tryTakeMVar"  -> "tryTakeTMVar"
        "GHC.MVar.tryPutMVar"   -> "tryPutTMVar"
        "GHC.MVar.isEmptyMVar"  -> "isEmptyTMVar"
        "Control.Concurrent.MVar.readMVar" -> "readTMVar"
        "Control.Concurrent.MVar.swapMVar" -> "swapTMVar"

        _                       -> nameToString n

-- | Translates the calling function from this HsApp.
--
-- Author's note: I wrote this function top pattern match in one go, reloaded GHCi, 
-- and it showed no errors. I gotta say I felt pretty proud about myself right then.
-- It ended up having a bug, but no compile-time errors!
--        
translateHsApp :: Bool -- ^ Is this function the topmost application? Deals with  
                       -- recursive HsApp's, as in functions with multiple arguments.
               -> GHC.HsExpr GHC.Name -- ^ The application to be refactored.
               -> RefactGhc ( GHC.HsExpr GHC.Name )
translateHsApp isTopNode (GHC.HsApp (GHC.L l insideApp@(GHC.HsApp _ _)) exp2 ) = do
    translatedLeaf <- translateHsApp False insideApp
    if isTopNode then do
             atomicallyName <- mkNewGhcName "atomically"
             return $ GHC.HsApp 
                          (GHC.L l (GHC.HsVar atomicallyName)) 
                          (GHC.L l (GHC.HsPar (GHC.L l (GHC.HsApp 
                                                           (GHC.L l translatedLeaf) 
                                                            exp2
                                                    ))))
    else 
             return $ GHC.HsApp 
                         (GHC.L l translatedLeaf) 
                          exp2
                                
translateHsApp isTopNode (GHC.HsApp (GHC.L l (GHC.HsVar functionName)) (GHC.L l2 exp2)) = do
    tmfunction <- translateFunction functionName
    let translatedNode = GHC.HsApp (GHC.L l (GHC.HsVar tmfunction)) (GHC.L l exp2)
    if isTopNode then do
        atomicallyName <- mkNewGhcName "atomically"
        return $ GHC.HsApp 
                (GHC.L l (GHC.HsVar atomicallyName)) 
                (GHC.L l (GHC.HsPar (GHC.L l translatedNode )))
    else 
        return translatedNode 
translateHsApp _ x = return x


realSrcSpan :: GHC.SrcSpan -> GHC.RealSrcSpan
realSrcSpan (GHC.RealSrcSpan rssp) = rssp
realSrcSpan _ = error "SrcSpan is not real"


