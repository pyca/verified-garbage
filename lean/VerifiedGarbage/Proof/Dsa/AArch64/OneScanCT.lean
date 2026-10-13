module

public import VerifiedGarbage.Proof.Dsa.AArch64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.LoadCheckCT
public import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant time of comparing a subgroup result with one -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- After `oneScanHead`'s loads from the header. -/
def OneRegs (L : Ws) (s : State) : Prop :=
  s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x16 = off L.B (slot L.w aX)

theorem pins_oneRegs : Pins OneRegs [.x12, .x16] :=
  pins_of (fun L r => if r = .x12 then BitVec.ofNat 64 L.w else off L.B (slot L.w aX)) (by
    intro L s h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2)

/-- Before the scan of the high limbs. -/
def OneLoopRegs (L : Ws) (s : State) : Prop :=
  s.gpr .x14 = BitVec.ofNat 64 (L.w - 1) ∧ s.gpr .x16 = off L.B (slot L.w aX + 8)

theorem pins_oneLoopRegs : Pins OneLoopRegs [.x14, .x16] :=
  pins_of (fun L r => if r = .x14 then BitVec.ofNat 64 (L.w - 1) else off L.B (slot L.w aX + 8)) (by
    intro L s h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2)

theorem oneScanHead_ct : RelCT isa (Two GoodW) (.block oneScanHead) (fun _ _ => True) := by
  change RelCT isa _ (.block (([ldh .x12 sW, ldh .x16 (sArr aX)] : List Instr) ++
    [ld .x9 .x16, movi .x4 1, .logic .eor .x .x9 .x9 .x4, next .x16, .subImm .x .x14 .x12 1])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := OneRegs) [.x0] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨minv, hg, hz⟩
    brun [OneRegs, hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aX < 8 by decide)),
      hg.ld hz (show sW < 32 by decide), hg.ld hz (sArr_lt (show aX < 8 by decide)), hg.hdr.hw,
      hg.hdr.harr aX (by decide)]
  exact two_taint [.x12, .x16] pins_oneRegs (by taint_decide)

theorem oneScan_ct : RelCT isa (Two CheckW) (.seq (.block oneScanHead) oneScanLoop) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := OneLoopRegs) (two_map (fun L => L) (fun _ _ h => h.1) oneScanHead_ct) ?_)
    (two_taint [.x14, .x16] pins_oneLoopRegs (by taint_decide))
  intro L s ⟨⟨minv, hg, hz⟩, hw, _⟩
  exact WP.mono (oneScanHead_ok hg hz (by omega)) fun _ h => ⟨h.2.2.1, h.2.1⟩

theorem oneReturn_ct : RelCT isa (Two LoadedCheck)
    (.seq (.block oneScanHead) (.seq oneScanLoop
      (.block (([mov .x3 .x9] : List Instr) ++ Checks.zeroMask ++ ([Crt.leave] : List Instr) ++
        Checks.accumulate))))
    (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq (two_post (Ψ := fun p s => LinkedPre p.x s)
    (two_map (fun p : BPub => p.x.ws) (fun _ _ ⟨minv, hc, hw, hw'⟩ => ⟨⟨minv, hc.good, Nat.le_refl _⟩, hw, hw'⟩)
      oneScan_ct) ?_) ?_
  · intro p s ⟨minv, hc, hw, hw'⟩
    exact WP.mono (oneScan_ok hc.good (Nat.le_refl _) hw hw')
      fun t ⟨_, hm, hk⟩ => ⟨minv, hc.of_keep hm hk (by decide)⟩
  change RelCT isa _ (.block ((([mov .x3 .x9] : List Instr) ++ Checks.zeroMask) ++
    (([Crt.leave] : List Instr) ++ Checks.accumulate))) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p s => LinkedPre p.x s) []
    (by intro p s t hs ht r hr; cases hr) (by taint_decide) ?_) ?_
  · intro p s ⟨minv, hc⟩
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x3] (Q := fun g => g.mem = s.mem) (by brun) (by decide) (by decide)
      (by decide +kernel)) fun g ⟨hgm, hkg⟩ => ?_
    exact WP.mono (zeroMask_ok g) fun t ⟨⟨_, _, _, hm⟩, hk⟩ =>
      ⟨minv, (hc.of_keep hgm hkg (by decide)).of_keep hm hk (by decide)⟩
  exact two_map (fun p : BPub => p.x) (fun _ _ h => h) leaveAccumulate_ct

end VG.Proof.Dsa.AArch64
