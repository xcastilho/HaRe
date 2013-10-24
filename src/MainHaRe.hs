{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- Based on
-- https://github.com/kazu-yamamoto/ghc-mod/blob/master/src/GHCMod.hs

import Control.Exception
import Data.List
import Data.Maybe
import Data.Typeable
import Data.Version
import Language.Haskell.GhcMod
import Language.Haskell.Refact.Case
import Language.Haskell.Refact.DupDef
import Language.Haskell.Refact.MoveDef
import Language.Haskell.Refact.Renaming
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.TypeSyn
import Paths_HaRe
import Prelude
import System.Console.GetOpt
import System.Environment (getArgs)
import System.IO (hPutStr, hPutStrLn, stdout, stderr, hSetEncoding, utf8)

import Text.Parsec.Combinator
import Text.Parsec.Prim
import Text.Parsec.Char

----------------------------------------------------------------

ghcOptHelp :: String
ghcOptHelp = " [-g GHC_opt1 -g GHC_opt2 ...] "

usage :: String
usage =    "ghc-hare version " ++ showVersion version ++ "\n"
        ++ "Usage:\n"
        ++ "\t ghc-hare demote" ++ ghcOptHelp ++ "filename line col\n"
        ++ "\t ghc-hare dupdef" ++ ghcOptHelp ++ "filename newname line col\n"
        ++ "\t ghc-hare iftocase" ++ ghcOptHelp ++ "filename startline startcol endline endcol\n"
        ++ "\t ghc-hare liftOneLevel" ++ ghcOptHelp ++ "filename line col\n"
        ++ "\t ghc-hare liftToTopLevel" ++ ghcOptHelp ++ "filename line col\n"
        ++ "\t ghc-hare rename" ++ ghcOptHelp ++ "filename newname line col\n"
        ++ "\t ghc-hare help\n"

{-
        ++ "\t ghc-hare list" ++ ghcOptHelp ++ "[-l]\n"
        ++ "\t ghc-hare lang [-l]\n"
        ++ "\t ghc-hare flag [-l]\n"
        ++ "\t ghc-hare browse" ++ ghcOptHelp ++ "[-l] [-o] [-d] <module> [<module> ...]\n"
        ++ "\t ghc-hare check" ++ ghcOptHelp ++ "<HaskellFile>\n"
        ++ "\t ghc-hare expand" ++ ghcOptHelp ++ "<HaskellFile>\n"
        ++ "\t ghc-hare debug" ++ ghcOptHelp ++ "<HaskellFile>\n"
        ++ "\t ghc-hare info" ++ ghcOptHelp ++ "<HaskellFile> <module> <expression>\n"
        ++ "\t ghc-hare type" ++ ghcOptHelp ++ "<HaskellFile> <module> <line-no> <column-no>\n"
        ++ "\t ghc-hare lint [-h opt] <HaskellFile>\n"
        ++ "\t ghc-hare boot\n"
        ++ "\t ghc-hare help\n"
-}
----------------------------------------------------------------

argspec :: [OptDescr (RefactSettings -> RefactSettings)]
argspec = [ Option "m" ["mainfile"]
              (ReqArg (\mf opts -> opts { rsetMainFile = Just mf }) "FILE")
              "Main file name if not specified in cabal file"

          -- , Option "l" ["tolisp"]
          --     (NoArg (\opts -> opts { outputStyle = LispStyle }))
          --     "print as a list of Lisp"
          -- , Option "h" ["hlintOpt"]
          --     (ReqArg (\h opts -> opts { hlintOpts = h : hlintOpts opts }) "hlintOpt")
          --     "hlint options"
          , Option "g" ["ghcOpt"]
              (ReqArg (\g opts -> opts { rsetGhcOpts = g : rsetGhcOpts opts }) "ghcOpt")
              "GHC options"
          -- , Option "o" ["operators"]
          --     (NoArg (\opts -> opts { operators = True }))
          --     "print operators, too"
          -- , Option "d" ["detailed"]
          --     (NoArg (\opts -> opts { detailed = True }))
          --     "print detailed info"
          , Option "v" ["verbose"]
              (NoArg (\opts -> opts { rsetVerboseLevel = Debug }))
              "debug logging on"
          , Option "b" ["boundary"]
            (ReqArg (\s opts -> opts { rsetLineSeparator = LineSeparator s }) "sep")
            "specify line separator (default is Nul string)"
          ]

parseArgs :: [OptDescr (RefactSettings -> RefactSettings)] -> [String] -> (RefactSettings, [String])
parseArgs spec argv
    = case getOpt Permute spec argv of
        (o,n,[]  ) -> (foldr id defaultSettings o, n)
        (_,_,errs) -> throw (CmdArg errs)

----------------------------------------------------------------

data HareError = SafeList
                 | NoSuchCommand String
                 | CmdArg [String]
                 | FileNotExist String deriving (Show, Typeable)

instance Exception HareError

----------------------------------------------------------------

main :: IO ()
main = flip catches handlers $ do
-- #if __GLASGOW_HASKELL__ >= 611
    hSetEncoding stdout utf8
-- #endif
    args <- getArgs
    let (opt,cmdArg) = parseArgs argspec args
    cradle <- findCradle
    let cmdArg0 = cmdArg !. 0
        cmdArg1 = cmdArg !. 1
        cmdArg2 = cmdArg !. 2
        cmdArg3 = cmdArg !. 3
        cmdArg4 = cmdArg !. 4
        cmdArg5 = cmdArg !. 5
    res <- case cmdArg0 of

      -- demote wants FilePath -> SimpPos
      "demote" -> runFunc $ demote opt cradle cmdArg1 (parseSimpPos cmdArg2 cmdArg3)

      -- dupdef wants FilePath -> String -> SimpPos
      "dupdef" -> runFunc $ duplicateDef opt cradle cmdArg1 cmdArg2 (parseSimpPos cmdArg3 cmdArg4)

      -- iftocase wants FilePath -> SimpPos -> SimpPos
      "iftocase" -> runFunc $ ifToCase opt cradle cmdArg1 (parseSimpPos cmdArg2 cmdArg3) (parseSimpPos cmdArg4 cmdArg5)

      -- liftOneLevel wants FilePath -> SimpPos
      "liftOneLevel" -> runFunc $ liftOneLevel opt cradle cmdArg1 (parseSimpPos cmdArg2 cmdArg3)

      -- liftToTopLevel wants FilePath -> SimpPos
      "liftToTopLevel" -> runFunc $ liftToTopLevel opt cradle cmdArg1 (parseSimpPos cmdArg2 cmdArg3)

      -- rename wants FilePath -> String -> SimpPos
      "rename" -> runFunc $ rename opt cradle cmdArg1 cmdArg2 (parseSimpPos cmdArg3 cmdArg4)

      "show" -> putStrLn  (show (opt,cradle))

      cmd      -> throw (NoSuchCommand cmd)
    putStr (show res)
    -- putStr $ "(ok " ++ showLisp mfs ++ ")"
  where
    handlers = [Handler handler1, Handler handler2]

    handler1 :: ErrorCall -> IO ()
    handler1 = print -- for debug

    handler2 :: HareError -> IO ()
    handler2 SafeList = printUsage
    handler2 (NoSuchCommand cmd) = do
        hPutStrLn stderr $ "\"" ++ cmd ++ "\" not supported"
        printUsage
    handler2 (CmdArg errs) = do
        mapM_ (hPutStr stderr) errs
        printUsage
    handler2 (FileNotExist file) = do
        hPutStrLn stderr $ "\"" ++ file ++ "\" not found"
        printUsage

    printUsage = hPutStrLn stderr $ '\n' : usageInfo usage argspec
{-
    withFile cmd file = do
        exist <- doesFileExist file
        if exist
            then cmd file
            else throw (FileNotExist file)
-}
    xs !. idx
      | length xs <= idx = throw SafeList
      | otherwise = xs !! idx


----------------------------------------------------------------

runFunc :: IO [String] -> IO ()
runFunc f = do
  r <- catchException f
  let ret = case r of
       Left s    -> "(error " ++ (show s) ++ ")"
       Right mfs -> "(ok " ++ showLisp mfs ++ ")"
  putStrLn ret

showLisp :: [String] -> String
showLisp xs = "(" ++ (intercalate " " $ map show xs) ++ ")"

catchException :: (IO t) -> IO (Either String t)
catchException f = do
  res <- handle handler (f >>= \r -> return $ Right r)
  return res
  where
    handler:: SomeException -> IO (Either String t)
    handler e = return (Left (show e))

----------------------------------------------------------------

parseSimpPos :: String -> String -> SimpPos
-- parseSimpPos str1 str2 = case (parse rowCol "" (T.pack (str1 ++ " " ++ str2))) of
parseSimpPos str1 str2 = case (parse rowCol "" ((str1 ++ " " ++ str2))) of
                          Left err -> throw (CmdArg [(show err)])
                          Right val -> val

rowCol :: P (Int,Int)
rowCol = do
  row <- number "line number"
  _ <- spaces
  col <- number "column number"
  return (fromIntegral row, fromIntegral col)

type P = Parsec String ()

instance (Monad m) => Stream String m Char where
    -- uncons = return . T.uncons
    uncons [] = return Nothing
    uncons s  = return $ Just (head s,tail s)

number :: String -> P Integer
number expectedStr = do { ds <- many1 digit; return (read ds) } <?> expectedStr

----------------------------------------------------------------

