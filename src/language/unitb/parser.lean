import meta.declaration
import meta.tactic

import unitb.models.pointers.basic
import language.unitb.obligations
import language.unitb.semantics
import language.unitb.syntax
import language.unitb.scope

import util.control.applicative
import util.control.monad
import util.data.generic

universes u v w k

namespace unitb.parser

open lean lean.parser
open interactive.types
open interactive

open list tactic applicative

open tactic.interactive

meta def expr.local_consts (e : expr) : list expr :=
e.fold [ ] (λ e i xs, if e.is_local_constant then e :: xs else xs)

open lean (parser)  monad (mmap₂) predicate

@[user_command]
meta def unitb_machine (meta_info : decl_meta_info) (_ : parse $ tk "machine") : parser unit :=
do n ← ident,
   updateex_env $ λ e₀, return $ e₀.add_namespace n,
   s ← variable_decl n,
   invs ← invariant_section s,
   init ← init_section s,
   sch ← event_section s,
   pos ← mk_proof_obligations s init invs,
   proof_section s pos,
   mk_machine_spec n sch,
   mk_machine_correctness n,
   tk "end"

end unitb.parser

precedence `initialization` : 0
precedence `invariants` : 0
precedence `events` : 0
precedence `when`   : 0
precedence `proofs` : 0
notation when := _root_.when
