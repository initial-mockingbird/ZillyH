import Classic.Parser.QuickCheck as PCQC
import Test.Framework.QuickCheckWrapper
import Data.Foldable (traverse_)

main :: IO ()
main = traverse_ quickCheck PCQC.props
