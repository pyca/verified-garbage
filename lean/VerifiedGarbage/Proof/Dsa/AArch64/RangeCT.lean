module
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Checks
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeLow

/-! # Fixed-trace scalar range scans -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ScanAddresses (L : Ws) (s : State) : Prop :=
  s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x16 = off L.B (slot L.w aX)

theorem pins_scanAddresses : Pins ScanAddresses [.x12, .x16] :=
  pins_of (fun L r => if r = .x12 then BitVec.ofNat 64 L.w else off L.B (slot L.w aX)) (by
    intro L s h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2)

theorem pins_goodW : Pins GoodW [.x0] :=
  pins_of (fun L _ => L.B) (by
    intro L s ⟨_, hg, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hg.x0)

theorem scanHead_ct : RelCT isa (Two GoodW)
    (.block [ldh .x12 sW, ldh .x16 (sArr aX)]) (Two ScanAddresses) := by
  refine two_piece [.x0] pins_goodW (by taint_decide) ?_
  intro L s ⟨minv, hg, hz⟩
  brun [ScanAddresses, hg.x0, hdr_enc (show sW < 32 by decide),
    hdr_enc (show sArr aX < 32 by decide), hg.hdr.hw, hg.hdr.harr aX (by decide),
    hg.ld hz (show sW < 32 by decide), hg.ld hz (show sArr aX < 32 by decide)]

theorem lowerScan_ct (aboveOne : Bool) :
    RelCT isa (Two GoodW) (Checks.lowerScan aboveOne) (fun _ _ => True) := by
  unfold Checks.lowerScan seqs
  refine RelCT.seq scanHead_ct ?_
  cases aboveOne <;> exact two_taint [.x12, .x16] pins_scanAddresses (by taint_decide)

def RangePre (L : Ws) (s : State) : Prop := GoodW L s ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31

theorem rangeMask_ct (aboveOne : Bool) :
    RelCT isa (Two RangePre) (Checks.rangeMask aboveOne) (fun _ _ => True) := by
  unfold Checks.rangeMask seqs
  refine RelCT.seq (two_post (Ψ := GoodW)
    (two_map (fun L : Ws => L) (fun _ _ h => h.1) (lowerScan_ct aboveOne)) ?_) ?_
  · intro L s ⟨⟨minv, hg, hz⟩, hw, hw'⟩
    exact WP.mono (lowerScan_ok hg hz hw hw' aboveOne) fun t ⟨_, hm, hk⟩ =>
      ⟨minv, ⟨hg.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩, hz⟩
  refine RelCT.seq (two_piece (Ψ := fun L s =>
    s.gpr .x16 = off L.B (slot L.w aX) ∧ s.gpr .x17 = off L.B (slot L.w aN) ∧
    s.gpr .x14 = BitVec.ofNat 64 L.w) [.x0] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨minv, hg, hz⟩
    brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aX < 32 by decide),
      hdr_enc (show sArr aN < 32 by decide), hg.hdr.hw, hg.hdr.harr aX (by decide), hg.hdr.harr aN (by decide),
      hg.ld hz (show sW < 32 by decide), hg.ld hz (show sArr aX < 32 by decide), hg.ld hz (show sArr aN < 32 by decide)]
  exact two_taint [.x16, .x17, .x14]
    (pins_of (fun L r => if r = .x16 then off L.B (slot L.w aX)
      else if r = .x17 then off L.B (slot L.w aN) else BitVec.ofNat 64 L.w) (by
        intro L s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64
