module TransactSpec (main, spec) where

import           Test.Hspec
import           Test.QuickCheck

import qualified GHC      as GHC
import qualified GhcMonad as GHC
import qualified RdrName  as GHC
import qualified SrcLoc   as GHC

import Exception
import Control.Monad.State
import Language.Haskell.Refact.Transact
import Language.Haskell.Refact.Utils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.LocUtils

import TestUtils

-- ---------------------------------------------------------------------

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "transact" $ do
    it "Tries to select something that's not an identifier" $ do
     res <- catchException (transact ["./test/testdata/Transact/B.hs","5","1"])
     -- let res = "foo"
     (show res) `shouldBe` "Just \"Incorrect identifier selected!\""


    it "Selects an identifier, for the case of a simple MVar created but never used." $ do
     transact ["./test/testdata/Transact/B.hs","24","3"]
     diff <- compareFiles "./test/testdata/Transact/B.hs.refactored"
                          "./test/testdata/Transact/B.hs.expected"
     diff `shouldBe` []

    it "Selects an identifier, for the case of a simple MVar which is not used as an MVar." $ do
     transact ["./test/testdata/Transact/SimpleConfusion.hs","12","17"]
     diff <- compareFiles "./test/testdata/Transact/SimpleConfusion.hs.refactored"
                          "./test/testdata/Transact/SimpleConfusion.hs.expected"
     diff `shouldBe` []



-- ---------------------------------------------------------------------
-- Helper functions

