module

public import VerifiedGarbage.Proof.Rsa.Arm.CvDivD
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_crt_values` on ARMv7: the results written out -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- What the outputs and the result are, from the mask `c` and the values computed. -/
structure Outs (s0 : State) (t : State) (c : Bool) (R₂ R₃ X : Nat) : Prop where
  done : Done s0 t
  ret : t.gpr .r0 = if c then 1 else 0
  dp : outDp t.mem s0 = if c then Spec.Rsa.i2osp (R₂ % 2 ^ (8 * cvPl s0)) (cvPl s0) else List.replicate (cvPl s0) 0
  dq : outDq t.mem s0 = if c then Spec.Rsa.i2osp (R₃ % 2 ^ (8 * cvQl s0)) (cvQl s0) else List.replicate (cvQl s0) 0
  qi : outQi t.mem s0 = if c then Spec.Rsa.i2osp (X % 2 ^ (8 * cvPl s0)) (cvPl s0) else List.replicate (cvPl s0) 0

theorem num_frame {s0 : State} (pre : CvPre s0) {m m' : Mem} {R : Region} (hf : Frame [R] m m')
    (hd : R.Disjoint (rS s0)) {j : Nat} (hj : j < nArr) :
    num m' (cvB s0) (cvW s0) j = num m (cvB s0) (cvW s0) j := by
  have fa := Nat.le_trans (arr_end (w := cvW s0) hj) pre.fits
  have fS := pre.fS
  have eZ : cvZ s0 = (stackArg s0 11).toNat * 8 := rfl
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  refine val32_congr fun i hi => congrArg BitVec.toNat (hf.readW (r := rS s0)
    (Offset.contains_base _ (by omega) (by omega)) (by simpa using hd.symm) (by decide))

theorem slot_frame' {s0 : State} (pre : CvPre s0) {m m' : Mem} {R : Region} (hf : Frame [R] m m')
    (hd : R.Disjoint (rS s0)) {e : Nat} (he : e + 4 ≤ hdr) :
    slot m' (cvB s0) e = slot m (cvB s0) e := by
  have := pre.fits
  have fS := pre.fS
  have eZ : cvZ s0 = (stackArg s0 11).toNat * 8 := rfl
  have hz : hdr ≤ cvZ s0 := Nat.le_trans (Nat.le_add_right _ _) this
  exact congrArg BitVec.toNat (hf.readW (r := rS s0) (Offset.contains_base _ (by omega) (by simp only [hdr] at he; omega))
    (by simpa using hd.symm) (by decide))

theorem ite_mask (c : Bool) {α : Type} (a b : α) : (if (if c then 1 else 0 : Nat) = 1 then a else b) = if c then a else b := by
  cases c <;> rfl

/-- The glue: the working space, and `dp` and `dq` from the header. -/
def glue : List Instr := ctx ++ [.ldr .r10 .r8 sDp, .ldr .r12 .r8 sDq]

theorem glue_ok {s0 s : State} {X₁ X₂ : Nat} (h : StG s0 X₁ X₂ s) :
    WP isa (.block glue) s fun u => Base s0 u ∧ Ws u (cvB s0) (cvZ s0) (cvW s0) nArr ∧
    u.gpr .r10 = s0.gpr .r0 ∧ u.gpr .r12 = s0.gpr .r2 ∧
    WP isa stores u fun t => ∃ V,
      (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
        (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧ num s.mem (cvB s0) (cvW s0) 3 < cvM s0) ∧
      Outs s0 t (maskOf (cvP s0) (cvQ s0) X₁ X₂ V) (num s.mem (cvB s0) (cvW s0) aDR2)
        (num s.mem (cvB s0) (cvW s0) aDR3) (num s.mem (cvB s0) (cvW s0) 3) := by
  have pre := h.base.pre
  obtain ⟨V, mV, iV⟩ := h.mask
  unfold glue
  refine ctx_ok h.base fun t1 b1 h1 r1 m1 => ?_
  refine wp_ldrSlot h1 (d := sDp) (by decide) fun t2 u2 => ?_
  refine wp_ldrSlot (h1.of_upd u2 (by decide) (by decide) (by decide)) (d := sDq) (by decide) fun t3 u3 => WP.block_nil ?_
  have h3 := (h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)
  have b3 := b1.of_rest ((u2.rest (ws := [.r10, .r12]) (by simp)).trans (u3.rest (by simp))) (u3.mem.trans u2.mem)
  have p10 : t3.gpr .r10 = s0.gpr .r0 := by
    rw [u3.other _ (by decide), u2.gpr, m1]
    exact BitVec.eq_of_toNat_eq (h.base.saved 9 (by decide))
  have p12 : t3.gpr .r12 = s0.gpr .r2 := by
    rw [u3.gpr, u2.mem, m1]
    exact BitVec.eq_of_toNat_eq (h.base.saved 10 (by decide))
  refine ⟨b3, h3, p10, p12, ?_⟩
  have d3 := b3.done
  have w16 := pre.w16
  have kb := pre.kb
  have hkw : ∀ k, k < cvK s0 → k ≤ 4 * cvW s0 := fun k hk => by simp only [cvW] at *; omega
  have mb : slot t3.mem (cvB s0) sMask ≤ 1 := by
    rw [u3.mem, u2.mem, m1, mV]; split <;> omega
  unfold stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_ldrSp d3.rA_mem (by rw [d3.sp]; exact pre.sp48) (i := 5) (by decide) fun t4 u4 => WP.block_nil ?_
  have d4 := d3.of_rest (u4.rest (ws := [.r11]) (by simp)) u4.mem
  have h4 := h3.of_upd u4 (by decide) (by decide) (by decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok d4 h4 (j := aDR2) (by decide) (R := rDp s0) (.inl rfl) (dst := s0.gpr .r0)
    (k := cvPl s0) (by simp [rDp, reg, pre.dpLen]) pre.pl1 (hkw _ pre.pl2) (by rw [← pre.dpLen]; exact pre.fDp)
    (by rw [u4.other _ (by decide), p10]) (by rw [u4.gpr, d3.arg (by decide)]; simp)
    (by rw [u4.mem]; exact mb)) fun t5 ⟨d5, h5, o5, f5, r5⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_mov (op2_reg _ _) fun t6 u6 => ?_
  have d6 := d5.of_rest (u6.rest (ws := [.r10]) (by simp)) u6.mem
  refine wp_ldrSp d6.rA_mem (by rw [d6.sp]; exact pre.sp48) (i := 7) (by decide) fun t7 u7 => WP.block_nil ?_
  have d7 := d6.of_rest (u7.rest (ws := [.r11]) (by simp)) u7.mem
  have h7 := (h5.of_upd u6 (by decide) (by decide) (by decide)).of_upd u7 (by decide) (by decide) (by decide)
  have mb5 : slot t5.mem (cvB s0) sMask = slot t3.mem (cvB s0) sMask := by
    rw [slot_frame' pre f5 pre.dpS (by decide), u4.mem]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok d7 h7 (j := aDR3) (by decide) (R := rDq s0) (.inr (.inl rfl)) (dst := s0.gpr .r2)
    (k := cvQl s0) (by simp [rDq, reg, pre.dqLen]) pre.ql1 (hkw _ pre.ql2) (by rw [← pre.dqLen]; exact pre.fDq)
    (by rw [u7.other _ (by decide), u6.gpr, r5.gpr _ (by decide), u4.other _ (by decide), p12])
    (by rw [u7.gpr, d6.arg (by decide)]; simp)
    (by rw [u7.mem, u6.mem, mb5]; exact mb)) fun t8 ⟨d8, h8, o8, f8, r8⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_ldrSp d8.rA_mem (by rw [d8.sp]; exact pre.sp48) (i := 0) (by decide) fun t9 u9 => ?_
  have d9 := d8.of_rest (u9.rest (ws := [.r10]) (by simp)) u9.mem
  refine wp_ldrSp d9.rA_mem (by rw [d9.sp]; exact pre.sp48) (i := 5) (by decide) fun t10 u10 => WP.block_nil ?_
  have d10 := d9.of_rest (u10.rest (ws := [.r11]) (by simp)) u10.mem
  have h10 := (h8.of_upd u9 (by decide) (by decide) (by decide)).of_upd u10 (by decide) (by decide) (by decide)
  have mb8 : slot t8.mem (cvB s0) sMask = slot t3.mem (cvB s0) sMask := by
    rw [slot_frame' pre f8 pre.dqS (by decide), u7.mem, u6.mem, mb5]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok d10 h10 (j := 3) (by decide) (R := rQi s0) (.inr (.inr rfl)) (dst := stackArg s0 0)
    (k := cvPl s0) (by simp [rQi, reg, pre.qiLen]) pre.pl1 (hkw _ pre.pl2) (by rw [← pre.qiLen]; exact pre.fQi)
    (by rw [u10.other _ (by decide), u9.gpr, d8.arg (by decide)])
    (by rw [u10.gpr, d9.arg (by decide)]; simp)
    (by rw [u10.mem, u9.mem, mb8]; exact mb)) fun t11 ⟨d11, h11, o11, f11, r11⟩ => ?_
  refine wp_ldrSlot h11 (d := sMask) (by decide) fun t u12 => WP.block_nil ?_
  have mb11 : slot t11.mem (cvB s0) sMask = slot t3.mem (cvB s0) sMask := by
    rw [slot_frame' pre f11 pre.qiS (by decide), u10.mem, u9.mem, mb8]
  have ms : slot t3.mem (cvB s0) sMask = if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then 1 else 0 := by
    rw [u3.mem, u2.mem, m1, mV]
  have n3 : ∀ j, j < nArr → num t3.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := fun j _ => by
    rw [u3.mem, u2.mem, m1]
  refine ⟨V, iV, ⟨d11.of_rest (u12.rest (ws := [.r0]) (by simp)) u12.mem, ?_, ?_, ?_, ?_⟩⟩
  · rw [u12.gpr]
    apply BitVec.eq_of_toNat_eq
    change slot t11.mem (cvB s0) sMask = _
    rw [mb11, ms]; split <;> rfl
  · have lp := pre.pl2; have lq := pre.ql2
    have eDp : (⟨State.addr (s0.gpr .r0), cvPl s0⟩ : Region) = rDp s0 := by simp [rDp, reg, pre.dpLen]
    simp only [outDp]
    rw [u12.mem, bytes_frame f11 (by rw [eDp]; simpa using pre.dpQi) (by omega), u10.mem, u9.mem,
      bytes_frame f8 (by rw [eDp]; simpa using pre.dpDq) (by omega), u7.mem, u6.mem, o5, u4.mem, ms, ite_mask,
      n3 _ (by decide)]
  · have lq := pre.ql2
    have eDq : (⟨State.addr (s0.gpr .r2), cvQl s0⟩ : Region) = rDq s0 := by simp [rDq, reg, pre.dqLen]
    simp only [outDq]
    rw [u12.mem, bytes_frame f11 (by rw [eDq]; simpa using pre.dqQi) (by omega), u10.mem, u9.mem, o8,
      u7.mem, u6.mem, mb5, ms, ite_mask, num_frame pre f5 pre.dpS (by decide), u4.mem, n3 _ (by decide)]
  · simp only [outQi]
    rw [u12.mem, o11, u10.mem, u9.mem, mb8, ms, ite_mask, num_frame pre f8 pre.dqS (by decide), u7.mem, u6.mem,
      num_frame pre f5 pre.dpS (by decide), u4.mem, n3 _ (by decide)]

theorem finish_ok {s0 s : State} {X₁ X₂ : Nat} (h : StG s0 X₁ X₂ s) :
    WP isa (.seq (.block glue) stores) s fun t => ∃ V,
      (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
        (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧ num s.mem (cvB s0) (cvW s0) 3 < cvM s0) ∧
      Outs s0 t (maskOf (cvP s0) (cvQ s0) X₁ X₂ V) (num s.mem (cvB s0) (cvW s0) aDR2)
        (num s.mem (cvB s0) (cvW s0) aDR3) (num s.mem (cvB s0) (cvW s0) 3) :=
  WP.seq_iff.mpr (WP.mono (glue_ok h) fun _ h => h.2.2.2.2)

end VG.Proof.Rsa.Arm.CrtValues
