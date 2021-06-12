
module Hata.Runtime.Service.Parse.GeneralizedLambdaTerm where
import Hata.Runtime.Application

data TermBase_GL = Te String [TermBase_GL] | Var String | Lam String TermBase_GL | App TermBase_GL TermBase_GL

parseTerm_GL :: [String] -> String -> Either HataError TermBase_GL
parseTerm_GL keywords input = undefined



