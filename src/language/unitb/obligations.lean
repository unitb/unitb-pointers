
import language.unitb.scope

open tactic lean lean.parser interactive.types
open tactic.interactive (exact)
open applicative (mmapp) list (map)

meta def po_table := (name_map (list expr × expr))

meta def proof_section (s : scope) (pos : po_table) : parser unit :=
do tk "proofs",
   id ← ident <* tk ":=",
   (hyp,g) ← pos.find id <|> fail format!"invalid proof obligation: {id};\n{pos.keys}",
   pr ← s.texpr,
   let g' := expr.pis hyp g,
   ((do t ← mk_meta_var g',
        set_goals [t],
        intron hyp.length,
        exact pr) : tactic _),
   tk ",",
   return ()

meta def mk_proof_obligations (s : scope) (init invs : list expr)
: tactic po_table :=
do rb_map.of_list <$> mmap (λ p : expr, do t ← infer_type p, return (p.local_pp_name, s.vars.values ++ init, t)) invs
