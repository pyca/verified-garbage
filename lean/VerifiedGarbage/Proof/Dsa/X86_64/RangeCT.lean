module
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Checks
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time DSA range checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def RangeAddresses (L : Lay) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 L.w ∧
  s.gpr .rbx = off L.B (slot L.w aX) ∧ s.gpr .r10 = off L.B (slot L.w aN)

/-- Both scans have a public word count; neither branches on the scalar or
on the final range mask. The modulus need not be public for this check. -/
theorem rangeMask_ct (aboveOne : Bool) :
    RelCT isa (Two GoodL) (Checks.rangeMask aboveOne) (fun _ _ => True) := by
  unfold Checks.rangeMask seqs
  refine RelCT.seq (two_piece (Ψ := RangeAddresses) [.rdi] pins_good (by taint_decide) ?_) ?_
  · intro L s hg
    exact WP.mono (rangeHead_ok hg.1 hg.2) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  have hp : Pins RangeAddresses [.r12, .rbx, .r10] := pins_of (fun (L : Lay) r =>
    if r = .r12 then BitVec.ofNat 64 L.w else if r = .rbx then off L.B (slot L.w aX)
    else off L.B (slot L.w aN)) (by
    intro L s h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2)
  cases aboveOne <;> exact two_taint [.r12, .rbx, .r10] hp (by taint_decide)

end VG.Proof.Dsa.X86_64
