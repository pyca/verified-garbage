module

public import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_crt_values` on ARMv7: an invalid modulus, and the return -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The outputs. -/
abbrev outDp (m : Mem) (s0 : State) : List Byte := Spec.Rsa.bytesAt m (State.addr (s0.gpr .r0)) (cvPl s0)
abbrev outDq (m : Mem) (s0 : State) : List Byte := Spec.Rsa.bytesAt m (State.addr (s0.gpr .r2)) (cvQl s0)
abbrev outQi (m : Mem) (s0 : State) : List Byte := Spec.Rsa.bytesAt m (State.addr (stackArg s0 0)) (cvPl s0)

theorem ofNat_len {x y : BitVec 32} (h : x.toNat = y.toNat) : BitVec.ofNat 32 x.toNat = y := by
  rw [h]; simp

theorem fail_ok {s0 s : State} (h : Base s0 s) (p0 : s.gpr .r0 = s0.gpr .r0) (p3 : s.gpr .r3 = s0.gpr .r2) :
    WP isa fail s fun t => Done s0 t ∧ t.gpr .r0 = 0 ∧
      outDp t.mem s0 = List.replicate (cvPl s0) 0 ∧ outDq t.mem s0 = List.replicate (cvQl s0) 0 ∧
      outQi t.mem s0 = List.replicate (cvPl s0) 0 := by
  have pre := h.pre
  have sp48 := pre.sp48
  unfold fail
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have b1 := h.of_rest (u1.rest (ws := [.r2]) (by simp)) u1.mem
  refine wp_ldrSp b1.rA_mem (by rw [b1.sp]; exact sp48) (i := 5) (by decide) fun s2 u2 => WP.block_nil ?_
  have b2 := b1.of_rest (u2.rest (ws := [.lr]) (by simp)) u2.mem
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroOut_ok b2.done (R := rDp s0) (dst := s0.gpr .r0) (.inl rfl) rfl
    (by show 0 < (s0.gpr .r1).toNat; rw [pre.dpLen]; exact pre.pl1) (s0.gpr .r1).isLt pre.fDp
    (by rw [u2.other _ (by decide), u1.other _ (by decide), p0])
    (by rw [u2.gpr, b1.arg (by decide)]; exact (ofNat_len pre.dpLen).symm)
    (by rw [u2.other _ (by decide), u1.gpr])) fun t3 ⟨d3, o3, f3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  have d4 := d3.of_rest (u4.rest (ws := [.r0]) (by simp)) u4.mem
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  have d5 := d4.of_rest (u5.rest (ws := [.r2]) (by simp)) u5.mem
  refine wp_ldrSp d5.rA_mem (by rw [d5.sp]; exact sp48) (i := 7) (by decide) fun s6 u6 => WP.block_nil ?_
  have d6 := d5.of_rest (u6.rest (ws := [.lr]) (by simp)) u6.mem
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroOut_ok d6 (R := rDq s0) (dst := s0.gpr .r2) (.inr (.inl rfl)) rfl
    (by show 0 < (s0.gpr .r3).toNat; rw [pre.dqLen]; exact pre.ql1) (s0.gpr .r3).isLt pre.fDq
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, r3.gpr _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), p3])
    (by rw [u6.gpr, d5.arg (by decide)]; exact (ofNat_len pre.dqLen).symm)
    (by rw [u6.other _ (by decide), u5.gpr])) fun t7 ⟨d7, o7, f7, r7⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_ldrSp d7.rA_mem (by rw [d7.sp]; exact sp48) (i := 0) (by decide) fun s8 u8 => ?_
  have d8 := d7.of_rest (u8.rest (ws := [.r0]) (by simp)) u8.mem
  refine wp_mov (op2_imm (by decide)) fun s9 u9 => ?_
  have d9 := d8.of_rest (u9.rest (ws := [.r2]) (by simp)) u9.mem
  refine wp_ldrSp d9.rA_mem (by rw [d9.sp]; exact sp48) (i := 5) (by decide) fun s10 u10 => WP.block_nil ?_
  have d10 := d9.of_rest (u10.rest (ws := [.lr]) (by simp)) u10.mem
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroOut_ok d10 (R := rQi s0) (dst := stackArg s0 0) (.inr (.inr rfl)) rfl
    (by show 0 < (stackArg s0 1).toNat; rw [pre.qiLen]; exact pre.pl1) (stackArg s0 1).isLt pre.fQi
    (by rw [u10.other _ (by decide), u9.other _ (by decide), u8.gpr, d7.arg (by decide)])
    (by rw [u10.gpr, d9.arg (by decide)]; exact (ofNat_len pre.qiLen).symm)
    (by rw [u10.other _ (by decide), u9.gpr])) fun t11 ⟨d11, o11, f11, r11⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun t u12 => WP.block_nil ?_
  have dt := d11.of_rest (u12.rest (ws := [.r0]) (by simp)) u12.mem
  have eDp : (⟨State.addr (s0.gpr .r0), cvPl s0⟩ : Region) = rDp s0 := by simp [rDp, reg, pre.dpLen]
  have eDq : (⟨State.addr (s0.gpr .r2), cvQl s0⟩ : Region) = rDq s0 := by simp [rDq, reg, pre.dqLen]
  have lp := pre.pl2
  have lq := pre.ql2
  have kb := pre.kb
  refine ⟨dt, u12.gpr, ?_, ?_, ?_⟩
  · simp only [outDp]
    rw [u12.mem, bytes_frame f11 (by rw [eDp]; simpa using pre.dpQi) (by omega), u10.mem, u9.mem, u8.mem,
      bytes_frame f7 (by rw [eDp]; simpa using pre.dpDq) (by omega), u6.mem, u5.mem, u4.mem]
    simpa only [rDp, reg, pre.dpLen] using o3
  · simp only [outDq]
    rw [u12.mem, bytes_frame f11 (by rw [eDq]; simpa using pre.dqQi) (by omega), u10.mem, u9.mem, u8.mem]
    simpa only [rDq, reg, pre.dqLen] using o7
  · simp only [outQi]
    rw [u12.mem]
    simpa only [rQi, reg, pre.qiLen] using o11

end VG.Proof.Rsa.Arm.CrtValues

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

theorem ldrSaved {s0 s : State} (h : Done s0 s) (p12 : s.gpr .r12 = cvB s0) {i : Nat} (hi : i < 11)
    {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (s0.gpr (savedReg i)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldr t .r12 (20 + 4 * i) :: rest)) s Q := by
  have pre := h.pre
  have fS := pre.fS
  have hz : 64 ≤ cvZ s0 := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega) pre.fits
  simp only [cvZ] at hz
  have eB : (cvB s0).toNat = (stackArg s0 10).toNat := rfl
  refine wp_ldr (by omega) (by rw [p12]; exact addr_add (by omega))
    ⟨rS s0, List.mem_append_right _ (by rw [h.wr, pre.wr]; simp),
      Offset.contains_base _ (by omega) (by omega)⟩ fun s' u => k s' ?_
  have e : s.mem.readW (off (State.addr (cvB s0)) (20 + 4 * i)) 32 = s0.gpr (savedReg i) :=
    BitVec.eq_of_toNat_eq (h.saved i hi)
  exact ⟨by rw [u.gpr]; exact e, u.other, u.mem, u.rd, u.wr, u.sp⟩

theorem restore_ok {s0 s : State} (h : Done s0 s) :
    WP isa (.block restore) s fun t => (∀ r ∈ preserved, t.gpr r = s0.gpr r) ∧ t.sp = s0.sp ∧
      t.mem = s.mem ∧ t.gpr .r0 = s.gpr .r0 := by
  have pre := h.pre
  refine wp_ldrSp h.rA_mem (by rw [h.sp]; exact pre.sp48) (i := 10) (by decide) fun s1 u1 => ?_
  have d1 := h.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have p12 : s1.gpr .r12 = cvB s0 := by rw [u1.gpr, h.arg (by decide)]
  refine ldrSaved d1 p12 (i := 0) (by decide) fun s2 u2 => ?_
  have d2 := d1.of_rest (u2.rest (ws := [.r4]) (by simp)) u2.mem
  refine ldrSaved d2 (by rw [u2.other _ (by decide), p12]) (i := 1) (by decide) fun s3 u3 => ?_
  have d3 := d2.of_rest (u3.rest (ws := [.r5]) (by simp)) u3.mem
  refine ldrSaved d3 (by rw [u3.other _ (by decide), u2.other _ (by decide), p12]) (i := 2) (by decide)
    fun s4 u4 => ?_
  have d4 := d3.of_rest (u4.rest (ws := [.r6]) (by simp)) u4.mem
  have q4 : s4.gpr .r12 = cvB s0 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p12]
  refine ldrSaved d4 q4 (i := 3) (by decide) fun s5 u5 => ?_
  have d5 := d4.of_rest (u5.rest (ws := [.r7]) (by simp)) u5.mem
  refine ldrSaved d5 (by rw [u5.other _ (by decide), q4]) (i := 4) (by decide) fun s6 u6 => ?_
  have d6 := d5.of_rest (u6.rest (ws := [.r8]) (by simp)) u6.mem
  have q6 : s6.gpr .r12 = cvB s0 := by rw [u6.other _ (by decide), u5.other _ (by decide), q4]
  refine ldrSaved d6 q6 (i := 5) (by decide) fun s7 u7 => ?_
  have d7 := d6.of_rest (u7.rest (ws := [.r9]) (by simp)) u7.mem
  refine ldrSaved d7 (by rw [u7.other _ (by decide), q6]) (i := 6) (by decide) fun s8 u8 => ?_
  have d8 := d7.of_rest (u8.rest (ws := [.r10]) (by simp)) u8.mem
  have q8 : s8.gpr .r12 = cvB s0 := by rw [u8.other _ (by decide), u7.other _ (by decide), q6]
  refine ldrSaved d8 q8 (i := 7) (by decide) fun s9 u9 => ?_
  have d9 := d8.of_rest (u9.rest (ws := [.r11]) (by simp)) u9.mem
  refine ldrSaved d9 (by rw [u9.other _ (by decide), q8]) (i := 8) (by decide) fun t u10 => WP.block_nil ?_
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.gpr]; rfl
    · rw [u10.other _ (by decide), u9.gpr]; rfl
    · rw [u10.gpr]; rfl
  · rw [u10.sp, d9.sp]
  · rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide)]

end VG.Proof.Rsa.Arm.CrtValues
