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


everything_header :: [String]
everything_header =
  [ "module Thesis.Everything where",
    "" ]

readme_header :: [String]
readme_header =
  [ "# Composable structures for dependently typed programming (TBD)",
    "",
    "This implements, in Agda, a framework of " ++
    "composable datatype refinements based on " ++
    "McBride's ornamentation.",
    "",
    "See [the author's homepage]" ++
    "(http://www.cs.ox.ac.uk/people/hsiang-shang.ko/) " ++
    "for more information, including published papers.",
    "",
    "## Module descriptions",
    "" ]

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
  (ps, fs) <- preprocess <$>
                find always
                  (extension ==? ".agda" &&?
                     (not . or <$> sequence exclusion))
                  "."
  hs <- mapM readHeader ps
  let fis = zip (map (concat . (prefix :) . intersperse ".") fs) hs
  writeFile "Everything.agda" (generateEverything fis)
  writeFile "README.md"       (generateReadme     fis)

preprocess :: [FilePath] -> ([FilePath], [[String]])
preprocess =
  unzip .
  sortBy (comparing (((toIndex . head) &&& tail) . snd)) .
  map (id &&& (map (takeWhile isAlpha) . tail . splitPath))
  where
    toIndex :: String -> Int
    toIndex = maybe maxBound id . flip findIndex ordering . (==)    

readHeader :: FilePath -> IO [String]
readHeader path =
  map (dropWhile isSpace . dropWhile (== '-')) .
  takeWhile (("--" ==) . take 2) . lines <$> readFile path

generateEverything :: [(String, [String])] -> String
generateEverything =
  unlines . (everything_header ++) . map (("import " ++) . fst)

generateReadme :: [(String, [String])] -> String
generateReadme =
  unlines . (readme_header ++) . concat . intersperse [""] .
  map (\(h, hs) -> ("#### " ++ h) : hs)

