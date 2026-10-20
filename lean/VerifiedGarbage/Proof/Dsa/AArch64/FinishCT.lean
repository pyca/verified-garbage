module

public import VerifiedGarbage.Proof.Dsa.AArch64.StoreCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Core
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of arithmetic result storage and return -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def FinishPre (p : BPub) (s : State) : Prop := StorePre p s ∧
  1 ≤ p.len ∧ p.len < 2 ^ 31 ∧ p.x.wx = (p.len + 7) / 8 ∧
  (∀ j < p.len, InRegions s.wr (p.ptr + BitVec.ofNat 64 j) 1) ∧
  (∀ j < p.len, p.x.Z ≤ ofs p.x.B (p.ptr + BitVec.ofNat 64 j))

theorem finish_ct : RelCT isa (Two FinishPre) (seqs Core.finish) (fun _ _ => True) := by
  unfold Core.finish seqs
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .x0 = off p.x.B p.x.o)
    (two_map (fun p : BPub => p) (fun _ _ h => h.1) store_ct) ?_) ?_
  · intro p s ⟨⟨minv, hc, hp, hl⟩, h1, h31, hw, hout, hpre⟩
    exact WP.mono (storeSuffix_ok hc (by decide) (by decide) (by decide) hp hl h1 h31 hw hout hpre)
      fun t ⟨hct, _⟩ => hct.x0
  exact two_taint [.x0]
    (pins_of (fun p _ => off p.x.B p.x.o) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h)) (by taint_decide)

end VG.Proof.Dsa.AArch64
