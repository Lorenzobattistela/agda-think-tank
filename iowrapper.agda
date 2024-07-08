module iowrapper where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

-- postulate putStrLn : String → IO ⊤
-- ffi to ghc

-- main : IO ⊤
-- main = putStrLn "Hello world!"

postulate
  return : ∀ {A : Set} → A → IO A
  _>>=_ : ∀ {A B : Set} → IO A → (A → IO B) → IO B
  putStrLn : String → IO ⊤ 
  getLine : IO String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC return = \_ -> return #-}
{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}
{-# COMPILE GHC getLine = fmap T.pack getLine #-}


data IOWrapper (A : Set) : Set where
  Wrap : IO A → IOWrapper A

unwrap : ∀ {A : Set} → IOWrapper A → IO A
unwrap (Wrap io) = io

wrapReturn : ∀ {A : Set} → A → IOWrapper A
wrapReturn x = Wrap (return x)

wrapBind : ∀ {A B : Set} → IOWrapper A → (A → IOWrapper B) → IOWrapper B
wrapBind (Wrap ioa) f = Wrap (ioa >>= λ x → unwrap (f x))

wrapPutStrLn : String → IOWrapper ⊤
wrapPutStrLn s = Wrap (putStrLn s)

wrapGetLine : IOWrapper String
wrapGetLine = Wrap getLine

-- write an example that runs putStrLn "test"
example : IOWrapper ⊤
example = wrapPutStrLn "test"

exampleGetAndPrint : IOWrapper ⊤
exampleGetAndPrint = wrapBind wrapGetLine λ input →
                     wrapPutStrLn (input)

runIOWrapper : ∀ {A : Set} → IOWrapper A → IO A
runIOWrapper = unwrap

main : IO ⊤
main = runIOWrapper exampleGetAndPrint





