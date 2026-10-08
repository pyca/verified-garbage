import VerifiedGarbage.Proof.P256.EcdhInverse.Round

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

def rounds : Nat → List Instr
  | 0 => []
  | n+1 => roundStep++rounds n

theorem rounds_ok {t : MSt} {s : State} (hs : RowState t s) (hb : rowBounds t)
    (n : Nat) (hd : |t.d|+2*n<2^62) :
    WP isa (.block (rounds n)) s fun a => RowState (msteps n t) a ∧
      Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s a := by
  induction n generalizing t s with
  | zero =>
    exact WP.block_nil ⟨hs,⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩⟩
  | succ n ih =>
    rw [rounds,WP.block_append_iff]
    have hdr : -(2^63)≤t.d ∧ t.d<2^63 := by
      have := le_abs_self t.d
      have := neg_abs_le t.d
      omega
    refine WP.mono (roundStep_ok hs hdr hb) fun a ⟨ha,ka⟩ => ?_
    have hdn : |(mstep t).d|+2*n<2^62 := by
      have h := mstep_d t
      norm_num only [Nat.cast_add,Nat.cast_one] at hd
      omega
    refine WP.mono (ih ha (rowBounds_step hb) hdn) fun b ⟨hb,kb⟩ => ?_
    exact ⟨hb,ka.trans kb⟩

/-- The last half does not need to prepare parity for another step. -/
theorem lastStep_ok {t : MSt} {s : State} (hs : RowState t s)
    (hd : -(2^63)≤t.d ∧ t.d<2^63) (hb : rowBounds t) :
    WP isa (.block (updateStep++halfStep)) s fun a =>
      a.gpr .x1=BitVec.ofInt 64 (mstep t).d ∧
      a.gpr .x4=BitVec.ofInt 64 (mstep t).f ∧
      a.gpr .x5=BitVec.ofInt 64 (mstep t).g ∧
      a.gpr .x27=0 ∧ Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s a := by
  rw [WP.block_append_iff]
  refine WP.mono (updateStep_int hs hd) fun a ⟨ad,af,ag,ka⟩ => ?_
  have a27 : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact hs.zero
  refine WP.mono (halfStep_run a a27) fun b ⟨bg,_,kb⟩ => ?_
  refine ⟨?_,?_,?_,?_,(ka.mono (by decide)).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide)]; exact ad
  · rw [kb.gpr _ (by decide)]; exact af
  · have hnum : -(2^63)≤numerator t ∧ numerator t<2^63 := row_numerator_bound hb
    rw [bg,ag,signed_shift_ofInt hnum]
    change BitVec.ofInt 64 (numerator t/2)=_
    rw [numerator_half]
  · rw [kb.gpr _ (by decide)]; exact a27

end VG.Proof.P256.EcdhInverse
