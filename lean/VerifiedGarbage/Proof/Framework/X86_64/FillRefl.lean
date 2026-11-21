module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall

/-!
# `Fill` of code that both sides share (x86-64)

`Fill k n a a` holds of any code `a`: each of its calls `.call f (.block [])`
is its own `Fill.call` (an empty body needs nothing of `calleeSide`). A
function's proof of `Fill` from its code with a stub to its code with an
implementation states it of the parts of the code that do not call the
implementation, rather than walk them with `fill_calls`.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64

/-- Any code is `Fill` of itself. -/
theorem Fill.refl {k : Nat} {n : String → Nat} : ∀ a : Prog isa, Fill k n a a
  | .block is => .block is
  | .seq a b => .seq (Fill.refl a) (Fill.refl b)
  | .ite c t e => .ite c (Fill.refl t) (Fill.refl e)
  | .loop b c => .loop c (Fill.refl b)
  | .call f b => .call f f (Fill.refl b)
  | .frame i b j => .frame i j (Fill.refl b)
  | .icall i f b x => .icall i f (Fill.refl b) (Fill.refl x)

end VG.X86_64.Scrub
