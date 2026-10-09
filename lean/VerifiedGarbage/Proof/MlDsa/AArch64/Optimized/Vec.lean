import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Arithmetic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word
import VerifiedGarbage.Proof.MlKem.AArch64.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)

/-- Exact execution of the selected three-instruction normalizer. All input
bit patterns are allowed; output words are positive representatives below 3q. -/
theorem positive_ok {d tmp qreg : VReg} (hdt : d ≠ tmp) (hdq : d ≠ qreg)
    (htq : tmp ≠ qreg) {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀ e < 4, vword (s.v qreg) e = 8380417#32)
    (k : ∀ s', VChg [tmp,d] s s' →
      (∀ e < 4, vword (s'.v d) e = positiveWord (vword (s.v d) e)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.positive d tmp qreg ++ rest)) s Q := by
  refine wp_vop (d := tmp) rfl fun s₁ h₁ =>
    wp_vop (d := d) rfl fun s₂ h₂ => wp_vop (d := d) rfl fun s₃ h₃ => ?_
  refine k s₃ (VChg.mono ((h₁.chg.trans h₂.chg).trans h₃.chg) ?_) ?_
  · intro r hr
    simp only [List.mem_append, List.mem_cons] at *
    grind only
  · intro e he
    rw [h₃.v, VG.AArch64.vword_map2 _ _ _ he, h₂.v, vword_mapWords3 _ _ _ _ he,
      h₁.get d hdt, h₁.v, VG.AArch64.vword_map2 _ _ _ he,
      h₁.get qreg (Ne.symm htq), h₂.get qreg (Ne.symm hdq),
      h₁.get qreg (Ne.symm htq), hq e he]
    rfl

/-- Lane-level evaluation fact also used by the NTT's scheduled batches,
where all high products precede all low products. -/
theorem reciprocal_eval {s : State} {d a b : VReg} {z : Nat → Int}
    (hz : ∀ e < 4, 0 ≤ z e ∧ z e < 8380417)
    (hb : ∀ e < 4, vword (s.v b) e = BitVec.ofInt 32 (reciprocal (z e))) :
    (VOp.sqdmulh d a b).eval s = some (d, ofVWords
      (BitVec.ofInt 32 ((vword (s.v a) 0).toInt * reciprocal (z 0) / 2147483648))
      (BitVec.ofInt 32 ((vword (s.v a) 1).toInt * reciprocal (z 1) / 2147483648))
      (BitVec.ofInt 32 ((vword (s.v a) 2).toInt * reciprocal (z 2) / 2147483648))
      (BitVec.ofInt 32 ((vword (s.v a) 3).toInt * reciprocal (z 3) / 2147483648))) := by
  have h e (he : e < 4) : sqdmulhLane (vword (s.v a) e) (vword (s.v b) e) =
      some (BitVec.ofInt 32 ((vword (s.v a) e).toInt * reciprocal (z e) / 2147483648)) := by
    rw [hb e he]
    exact sqdmulh_reciprocal _ (hz e he).1 (hz e he).2
  simp only [VOp.eval, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- The exact three-instruction reciprocal butterfly multiplier, permitting
signed input words and preserving all registers outside its two destinations. -/
theorem fastMul_ok {d tmp zr br qr : VReg}
    (hdt : d ≠ tmp) (htz : tmp ≠ zr) (htq : tmp ≠ qr) (hdq : d ≠ qr)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀ e < 4, 0 ≤ z e ∧ z e < 8380417)
    (hzw : ∀ e < 4, vword (s.v zr) e = BitVec.ofInt 32 (z e))
    (hbw : ∀ e < 4, vword (s.v br) e = BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e < 4, vword (s.v qr) e = 8380417#32)
    (k : ∀ s', VChg [tmp,d] s s' →
      (∀ e < 4, vword (s'.v d) e = fastMulWord (vword (s.v d) e) (z e)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.fastMul d tmp zr br qr ++ rest)) s Q := by
  let w := fun e => BitVec.ofInt 32 ((vword (s.v d) e).toInt * reciprocal (z e) / 2147483648)
  have he : (VOp.sqdmulh tmp d br).eval s = some (tmp, ofVWords (w 0) (w 1) (w 2) (w 3)) :=
    reciprocal_eval hz hbw
  refine wp_vop he fun s₁ h₁ => wp_vop (d := d) rfl fun s₂ h₂ =>
    wp_vop (d := d) rfl fun s₃ h₃ => ?_
  refine k s₃ (VChg.mono ((h₁.chg.trans h₂.chg).trans h₃.chg) ?_) ?_
  · intro r hr
    simp only [List.mem_append, List.mem_cons] at *
    grind only
  · intro e he4
    rw [h₃.v, vword_mapWords3 _ _ _ _ he4, h₂.v, VG.AArch64.vword_map2 _ _ _ he4,
      h₁.get d hdt, h₁.get zr (Ne.symm htz), hzw e he4,
      h₂.get tmp (Ne.symm hdt), h₁.v, VG.AArch64.vword_ofVWords _ _ _ _ he4,
      h₂.get qr (Ne.symm hdq), h₁.get qr (Ne.symm htq), hqw e he4]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- The chosen renaming schedule writes the difference into a free register
and leaves the sum in the first input register. -/
theorem renamed_pair_ok {a b free : VReg} (haf : a ≠ free) (hbf : b ≠ free)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [free,a] s t →
      (∀ e < 4, vword (t.v a) e = vword (s.v a) e + vword (s.v b) e) →
      (∀ e < 4, vword (t.v free) e = vword (s.v a) e - vword (s.v b) e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.vop (.sub .s4 free a b) :: .vop (.add .s4 a a b) :: rest)) s Q := by
  refine wp_vop (d := free) rfl fun s₁ h₁ => wp_vop (d := a) rfl fun s₂ h₂ => ?_
  refine k s₂ (h₁.chg.trans h₂.chg) ?_ ?_
  · intro e he
    rw [h₂.v, VG.AArch64.vword_map2 _ _ _ he, h₁.get a haf, h₁.get b hbf]
  · intro e he
    rw [h₂.get free (Ne.symm haf), h₁.v, VG.AArch64.vword_map2 _ _ _ he]

end VG.Proof.MlDsa.AArch64.Optimized
