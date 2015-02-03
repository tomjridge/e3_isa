(* common definitions *)

theory E3_prelude
imports Main  
begin

definition rev_apply :: "'a => ('a => 'b) => 'b" (infixl "|>" 60) where
  "x |> f == f x"

definition arbitrary :: "'a" where
"arbitrary == THE x. (x=x)"

definition failwith :: "string => 'a" where
"failwith s = arbitrary"

end
