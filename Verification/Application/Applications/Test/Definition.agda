
module Verification.Application.Applications.Test.Definition where

open import Verification.Conventions
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Application.Definition
open import Verification.Application.Configuration.Static
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.Product
-- open import Verification.Core.Data.AllOf.Universe
-- open import Verification.Core.Data.Int.Definition
-- open import Verification.Core.Data.Expr.Variant.Base.Definition

open import Verification.Application.Persistent

-- open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Monad.Definition
-- open import Verification.Core.Category.Std.Monad.TypeMonadNotation

-- open import Verification.Core.Theory.Std.Inference.Definition
-- open import Verification.Core.Theory.Std.Inference.Task

-- open import Verification.Core.Data.SourceCode.Variant.HaskellLike.Definition
-- open import Verification.Core.Data.Expr.Variant.List.Definition
-- open import Verification.Core.Theory.Std.Specific.ProductClosedTheory.Inference.Boundary


-- module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
--   instance
--     IShow:+-𝒰 : {{_ : IShow A}} {{_ : IShow B}} -> IShow (A + B)
--     IShow:+-𝒰 = record { show = either show show }

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


open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Example.Simple
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Statement
open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.Show

doTest : Text -> TestError + Text
doTest _ =
  let x = result-t-0
  in case x of
      (λ _ -> right "error")
      λ res → let _ / _ ⊩ _ , τ , _ , _ = res .fst in right {!show {{Show:𝒯⊔Term}} τ!}

-- doTest input = do
--   contentfile <- mapLeft (persistencyError ∘ parseError) (parseContentFile input)
--   contentfile' <- mapLeft persistencyError (unbaseContentFile contentfile)
--   return (inferCF contentfile')

--   where
--     inferCF : ContentFile -> String
--     inferCF (contentFile language content) =
--       let res = parseHaskellLikeSourceCode content
--           res2 = (map makeListExprᵘ res)
--       in show res <> "\n-----------------------\n" <> show res2
--       -- let _ , task = getInferenceTask language
--       -- in executeInferenceFlat task content

testExecutable : Executable TestState
testExecutable = executable (printExe) loop
  where
    loop : Event → TestState → List (Reaction TestState) ×~ TestState
    loop (Event-ReadFile f) s = (Reaction-PrintDebug (show (doTest f)) ∷ []) , s
    loop _ s = Reaction-PrintDebug "not implemented" ∷ [] , s



-- testApplication : Application
-- testApplication = execute "infer" testExecutable







