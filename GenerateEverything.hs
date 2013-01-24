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


output_file :: FilePath
output_file = "Everything.agda"

header :: [String]
header = ["module Thesis.Everything where", ""]

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

main :: IO ()
main = do
  files <- find always
             (extension ==? ".agda" &&? (not . or <$> sequence exclusion))
             "."
  writeFile output_file (process files)

process :: [FilePath] -> String
process =
  unlines .
  (header ++) .
  map (("import " ++) . (prefix ++). concat . intersperse ".") .
  sortBy (comparing
    ((maybe maxBound id . flip findIndex ordering . (==) . head)
     &&& tail)) .
  map (map (takeWhile isAlpha) . tail . splitPath)

