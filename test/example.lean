
import language.unitb.parser

open list -- unitb.parser

machine foo
variables x, y
invariants
  bar: x ∪ y ⊆ x
initialization
  x := ∅, y := ∅
events
  move
    when grd1 : ∅ ∈ x
    then end
  add_x begin x := y end
  swap begin x,y := y,x end
proofs
  bar :=
  begin
    simp [x_1,y_1], admit,
  end,

end

#print foo.correctness
-- #print prefix foo.event.swap
-- #print prefix foo.event.move
#print foo.event.swap.step'
#print foo.event.add_x.step'
#print foo.event.move.step'
#print foo.event.spec
#print foo.init'
#print foo.spec

example (s : foo.state) (J : foo.inv s) : true :=
begin
  induction s,
  dunfold foo.inv at J,
  induction J,
  admit
end

example (k : foo.state) : true :=
begin
  induction k,
  admit
end
