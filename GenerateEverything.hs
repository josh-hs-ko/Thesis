import Data.List hiding (find)
import Data.Char
import Data.Ord
import Data.Maybe
import Control.Arrow
import Control.Monad
import Control.Applicative
import System.IO
import System.FilePath
import System.FilePath.Find

prefix :: String
prefix = "Thesis."

ordering :: [String]
ordering =
  [ "Prelude", "Refinement", "Description", "Ornament", "Relation",
    "Examples" ]

exclusion :: [FindClause Bool]
exclusion =
  [ liftOp (flip isPrefixOf) directory "./Old",
    liftOp (flip isPrefixOf) directory "./Notes",
    fileName ==? "Everything.agda",
    fileName ==? "Playground.agda",
    fileName ==? "Scribble.agda" ]

process :: [FilePath] -> String
process =
  unlines .
  ("module Thesis.Everything where":) . ("":) .
  map (("import " ++) . (prefix ++). concat . intersperse ".") .
  sortBy
    (comparing
      ((maybe (-1) id . flip findIndex ordering . (==) . head) &&& tail)) .
  map (map (takeWhile isAlpha) . tail . splitPath)

main :: IO ()
main = do
  files <- find always
             (extension ==? ".agda" &&? (not . or <$> sequence exclusion))
             "."
  writeFile "Everything.agda" (process files)

