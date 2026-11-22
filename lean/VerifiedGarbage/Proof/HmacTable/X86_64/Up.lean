module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.TableFill
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Variants.MdHash.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.TableFill
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Tables of the interface `Hmac` on x86-64: what a caller's cleanup needs

A function that calls HMAC's functions through a table of `Hmac` clears the
stack they use and the registers they write: what its cleanup needs of each
variant's functions (`HmacUp`, `X86_64.Scrub.upCallee`, with 24 bytes of
stack), which the kernel evaluates once for every variant (`variants_up`),
for every function that takes the tables.
-/

@[expose] public section

namespace VG.Proof.HmacTable.X86_64

open VG.X86_64 VG.X86_64.Scrub

/-- What the cleanup of a caller through a table needs of the HMAC functions
of `w` (`X86_64.Scrub.upCallee`), with 24 bytes of stack. -/
def HmacUp (w : Proof.Pbkdf2.Md.X86_64.MdHash) : Prop :=
  upCallee w.H.hmacInitAny 24 = true ∧ upCallee w.H.updC 24 = true ∧ upCallee w.H.hmacFin 24 = true

/-- `HmacUp` of every variant, evaluated once for every curve. -/
theorem variants_hmacUp : (VG.Proof.Variants.MdHash.X86_64.variants.all fun w =>
    upCallee w.H.hmacInitAny 24 && upCallee w.H.updC 24 && upCallee w.H.hmacFin 24) = true := by
  lit_decide

theorem variants_up : ∀ w ∈ VG.Proof.Variants.MdHash.X86_64.variants, HmacUp w := fun w hw => by
  have h := List.all_eq_true.mp variants_hmacUp w hw
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end VG.Proof.HmacTable.X86_64
