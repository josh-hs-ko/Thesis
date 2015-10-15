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
  [ "module Everything where",
    "" ]

readme_header :: [String]
readme_header =
  [ "# Analysis and synthesis of inductive families",
    "",
    "This implements, in Agda, a framework of " ++
    "composable datatype refinements and " ++
    "relational algebraic ornamentation " ++
    "based on [McBride's work on ornaments]" ++
    "(http://personal.cis.strath.ac.uk/~conor/pub/OAAO/LitOrn.pdf), " ++
    "and forms the basis of [the author's DPhil dissertation]" ++
    "(https://github.com/josh-hs-ko/dissertation/blob/master/dissertation.pdf).",
    "",
    "All files typecheck with Agda 2.4.2.4 and Standard Library 0.10.",
    "",
    "See [the author's (old) homepage]" ++
    "(http://www.cs.ox.ac.uk/people/hsiang-shang.ko/) " ++
    "for more information, including published papers.",
    "",
    "## Module descriptions",
    "" ]

prefix :: String
prefix = ""

ordering :: [String]
ordering =
  [ "Prelude", "Refinement", "Description", "Ornament", "Relation",
    "Examples" ]

exclusion :: [FindClause Bool]
exclusion =
  [ liftOp (flip isPrefixOf) directory "./Notes",
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
  let ms = map (concat . (prefix :) . intersperse ".") fs
  writeFile "Everything.agda" (generateEverything ms)
  writeFile "README.md"       (generateReadme (zip ms hs))

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
  takeWhile ((== "--") . take 2) . lines <$> readFile path

generateEverything :: [String] -> String
generateEverything =
  unlines . (everything_header ++) . map ("import " ++)

generateReadme :: [(String, [String])] -> String
generateReadme =
  unlines . (readme_header ++) . concat . intersperse [""] .
  map (\(m, hs) -> ("#### " ++ m) : hs)

