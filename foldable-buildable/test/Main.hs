module Main (main) where

import Data.Buildable (fromListL, fromListR)
import qualified Data.Vector as Vector
import Test.Hspec (describe, hspec, it, shouldBe)

main :: IO ()
main =
  hspec $ do
    describe "Data.Buildable" $ do
      describe "Buildable Vector" $ do
        it "fromListR" $ do
          fromListR [1 :: Int, 2, 3, 4] `shouldBe` Vector.fromList [1, 2, 3, 4]
        it "fromListL" $ do
          fromListL [1 :: Int, 2, 3, 4] `shouldBe` Vector.fromList [1, 2, 3, 4]