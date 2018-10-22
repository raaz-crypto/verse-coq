import System.Environment
import System.FilePath
import Data.Char           (toUpper)

capitalize (x:xs) = toUpper x : xs
capitalize xs     = xs

pathCapitalize = joinPath . map capitalize . splitPath

main :: IO ()
main = do args <- getArgs
          mapM_ (putStrLn . pathCapitalize) args
