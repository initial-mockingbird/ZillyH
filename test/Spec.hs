-- import Classic.Parser.QuickCheck as PCQC
{-# LANGUAGE ImportQualifiedPost #-}
import Test.Framework.QuickCheckWrapper
import Data.Foldable (traverse_)
import TC.HM qualified as HM

props :: [Property]
props = HM.props

main :: IO ()
main = traverse_ quickCheck props
