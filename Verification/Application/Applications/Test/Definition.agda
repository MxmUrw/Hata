
module Verification.Application.Applications.Test.Definition where

open import Verification.Conventions
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Application.Definition
open import Verification.Application.Configuration.Static
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.AllOf.Product
open import Verification.Experimental.Data.AllOf.Universe
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Expr.Variant.Base.Definition

open import Verification.Application.Persistent

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation

open import Verification.Experimental.Theory.Std.Inference.Definition
open import Verification.Experimental.Theory.Std.Inference.Task

open import Verification.Experimental.Data.SourceCode.Variant.Tokenized.HaskellLike.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductClosedTheory.Inference.Boundary


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  instance
    IShow:+-𝒰 : {{_ : IShow A}} {{_ : IShow B}} -> IShow (A + B)
    IShow:+-𝒰 = record { show = either show show }

record TestState : 𝒰₀ where
  constructor printExe

-- instance
--   IShow:Bool : IShow Bool
--   IShow.show IShow:Bool false = "false"
--   IShow.show IShow:Bool true = "true"

data TestError : 𝒰₀ where
  persistencyError : PersistencyError -> TestError

instance
  IShow:TestError : IShow TestError
  IShow.show IShow:TestError (persistencyError x) = show x


doTest : Text -> TestError + Text
doTest input = do
  contentfile <- mapLeft (persistencyError ∘ parseError) (parseContentFile input)
  contentfile' <- mapLeft persistencyError (unbaseContentFile contentfile)
  return (inferCF contentfile')

  where
    inferCF : ContentFile -> String
    inferCF (contentFile language content) =
      let res = parseHaskellLikeTokenizedSourceCode {P = 𝕋ΛTypeData} content
      in show res
      -- let _ , task = getInferenceTask language
      -- in executeInferenceFlat task content

testExecutable : Executable TestState
testExecutable = executable (printExe) loop
  where
    loop : Event → TestState → List (Reaction TestState) ×~ TestState
    loop (Event-ReadFile f) s = (Reaction-PrintDebug (show (doTest f)) ∷ []) , s
    loop _ s = Reaction-PrintDebug "not implemented" ∷ [] , s



-- testApplication : Application
-- testApplication = execute "infer" testExecutable







