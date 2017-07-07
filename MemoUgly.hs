module MemoUgly where
import Control.Concurrent.MVar
import qualified Data.Map as M
import System.IO.Unsafe(unsafePerformIO)
import qualified Data.MemoUgly

memo f = Data.MemoUgly.memo f
memoIO f = Data.MemoUgly.memoIO f

memoFix ff = f where f = memo (ff f)
