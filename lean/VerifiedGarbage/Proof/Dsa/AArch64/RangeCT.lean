module

public import VerifiedGarbage.Proof.Dsa.AArch64.RangeHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeHead
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant-time DSA range checks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- A child workspace with a word count the scans support. -/
def CheckW (L : Ws) (s : State) : Prop := GoodW L s ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31

/-- After `rangeMask`'s head: the comparison's bounds and count. -/
def RangeAddresses (L : Ws) (s : State) : Prop :=
  CheckW L s ∧ s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x16 = off L.B (slot L.w aX) ∧
    s.gpr .x17 = off L.B (slot L.w aN) ∧ s.gpr .x14 = BitVec.ofNat 64 L.w ∧ s.gpr .x7 = 0 ∧ s.c = true

/-- After the comparison. -/
def RangeCompared (L : Ws) (s : State) : Prop :=
  GoodW L s ∧ s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x7 = 0

/-- After the low limb's address is loaded again. -/
def RangeLowAddr (L : Ws) (s : State) : Prop :=
  GoodW L s ∧ s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x16 = off L.B (slot L.w aX)

/-- Before the scan of the high limbs. -/
def RangeOr (L : Ws) (s : State) : Prop :=
  s.gpr .x14 = BitVec.ofNat 64 L.w - BitVec.ofNat 64 1 ∧ s.gpr .x16 = off L.B (slot L.w aX + 8)

/-- Both scans have a public word count; neither branches on the scalar or
on the final range mask. The modulus need not be public for this check. -/
theorem rangeMask_ct (aboveOne : Bool) :
    RelCT isa (Two CheckW) (Checks.rangeMask aboveOne) (fun _ _ => True) := by
  unfold Checks.rangeMask seqs
  refine RelCT.seq (two_piece (Ψ := RangeAddresses) [.x0]
    (pins_of (fun L _ => L.B) fun L s ⟨⟨_, hg, _⟩, _⟩ r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hg.x0) (by taint_decide) ?_) ?_
  · intro L s ⟨⟨minv, hg, hz⟩, hw⟩
    exact WP.mono (rangeHead_ok hg hz) fun t ⟨h12, h16, h17, h14, h7, hc, hm, hk⟩ =>
      ⟨⟨⟨minv, ⟨hg.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩, hz⟩, hw⟩,
        h12, h16, h17, h14, h7, hc⟩
  refine RelCT.seq (two_post (Ψ := RangeCompared) (two_taint [.x14, .x16, .x17]
    (pins_of (fun L r => if r = .x14 then BitVec.ofNat 64 L.w else if r = .x16 then off L.B (slot L.w aX)
      else off L.B (slot L.w aN)) fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.2.2.2.2.1
        · exact h.2.2.1
        · exact h.2.2.2.1) (by taint_decide)) ?_) ?_
  · intro L s ⟨⟨⟨minv, hg, hz⟩, hw, hw'⟩, h12, h16, h17, h14, h7, hc⟩
    have hx := Nat.le_trans (slot_le (w := L.w) (show aX < 8 by decide)) hz
    have hn := Nat.le_trans (slot_le (w := L.w) (show aN < 8 by decide)) hz
    exact WP.mono (cmpLoop_ok hg.scr h16 h17 h14 hc (by omega) hw' (by omega) (by omega))
      fun t ⟨_, hm, hk⟩ => ⟨⟨minv, ⟨hg.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩, hz⟩,
        (hk.gpr .x12 (by decide)).trans h12, (hk.gpr .x7 (by decide)).trans h7⟩
  have hmid : Impl.Rsa.AArch64.Crt.borrowMask ++ ([mov .x11 .x15, ldh .x16 (sArr aX), ld .x9 .x16] : List Instr) ++
      (if aboveOne then [.lsr .x .x9 .x9 1] else []) ++ ([next .x16, .subImm .x .x14 .x12 1] : List Instr) =
      (Impl.Rsa.AArch64.Crt.borrowMask ++ ([mov .x11 .x15, ldh .x16 (sArr aX)] : List Instr)) ++
        (ld .x9 .x16 :: ((if aboveOne then [.lsr .x .x9 .x9 1] else []) ++
          ([next .x16, .subImm .x .x14 .x12 1] : List Instr))) := by
    cases aboveOne <;> rfl
  rw [hmid]
  have hor : Pins RangeOr [.x14, .x16] :=
    pins_of (fun L r => if r = .x14 then BitVec.ofNat 64 L.w - BitVec.ofNat 64 1
      else off L.B (slot L.w aX + 8)) fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_piece (Ψ := RangeLowAddr) [.x0]
    (pins_of (fun L _ => L.B) fun L s ⟨⟨_, hg, _⟩, _⟩ r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hg.x0) (by taint_decide) ?_) (two_post (Ψ := RangeOr) ?_ ?_))) ?_
  · intro L s ⟨⟨minv, hg, hz⟩, h12, h7⟩
    exact WP.mono (WP.keep [.x4, .x11, .x15, .x16] (Q := fun t => t.gpr .x16 = off L.B (slot L.w aX) ∧
        t.mem = s.mem)
      (by brun [Impl.Rsa.AArch64.Crt.borrowMask, h7, hg.x0, hdr_enc (sArr_lt (show aX < 8 by decide)),
        hg.ld hz (sArr_lt (show aX < 8 by decide)), hg.hdr.harr aX (by decide)])
      (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h16, hm⟩, hk⟩ => ⟨⟨minv, ⟨hg.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩, hz⟩,
        (hk.gpr .x12 (by decide)).trans h12, h16⟩
  · have hp : Pins RangeLowAddr [.x12, .x16] :=
      pins_of (fun L r => if r = .x12 then BitVec.ofNat 64 L.w else off L.B (slot L.w aX)) fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.2.1
        · exact h.2.2
    cases aboveOne <;> exact two_taint [.x12, .x16] hp (by taint_decide)
  · intro L s ⟨⟨minv, hg, hz⟩, h12, h16⟩
    have hx := Nat.le_trans (slot_le (w := L.w) (show aX < 8 by decide)) hz
    refine WP.mono (WP.keep [.x9, .x14, .x16] (Q := RangeOr L) ?_
      (by cases aboveOne <;> decide) (by cases aboveOne <;> decide) (by cases aboveOne <;> decide +kernel))
      fun t h => h.1
    cases aboveOne <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, List.nil_append, List.cons_append] <;>
      brun [RangeOr, h12, h16, hg.scr.ld (show slot L.w aX + 8 ≤ L.Z by omega)]
  · cases aboveOne <;> exact two_taint [.x14, .x16] hor (by taint_decide)

end VG.Proof.Dsa.AArch64
