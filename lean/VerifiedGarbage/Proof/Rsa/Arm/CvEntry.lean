module

public import VerifiedGarbage.Proof.Rsa.Arm.CvState
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Framework.Offset

/-! # `vg_rsa_crt_values` on ARMv7: the entry

The registers are saved in the header, and `n` checked (`entry_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Arm.Spill VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The registers saved, and where. -/
def saveL : List (Reg × Nat) :=
  [(.r4, 20), (.r5, 24), (.r6, 28), (.r7, 32), (.r8, 36), (.r9, 40), (.r10, 44), (.r11, 48), (.lr, 52),
   (.r0, 56), (.r2, 60)]

theorem entry_eq : entry = .ldrSp .r12 (4 * 10) :: (saveL.map (fun p => Instr.str p.1 .r12 p.2) ++
    (([.mov .r8 (.reg .r12), .mov .r3 (.reg .r2)] : List Instr) ++ (.ldrSp .r4 (4 * 2) :: .ldrSp .r6 (4 * 3) :: modulusCheck))) := rfl

theorem saveL_mem {i : Nat} (hi : i < 11) : (savedReg i, 20 + 4 * i) ∈ saveL := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The bytes of `n`. -/
abbrev nBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (cvK s)

theorem entry_ok {s0 : State} (h : CvPre s0) :
    WP isa (.block entry) s0 fun t => Base s0 t ∧ t.gpr .r8 = cvB s0 ∧ t.gpr .r0 = s0.gpr .r0 ∧
      t.gpr .r3 = s0.gpr .r2 ∧ t.gpr .r6 = stackArg s0 3 ∧
      t.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0) := by
  have fS := h.fS
  have fits := h.fits
  have kb := h.kb
  rw [entry_eq]
  have hrd : rA s0 ∈ s0.rd := by rw [h.rd]; simp
  refine wp_ldrSp hrd h.sp48 (by decide) fun s1 u1 => ?_
  have hz : 64 ≤ cvZ s0 := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega) fits
  refine save_slots_ok (lo := 20) (hi := 64) (by decide) (by rw [u1.gpr]; simp only [cvZ] at hz; omega)
    (fun d h1 h2 => ⟨rS s0, by rw [u1.wr, h.wr]; simp, by
      rw [u1.gpr]; exact Offset.contains_base _ (by simp only [cvZ] at hz; omega) (by omega)⟩) ?_
  -- The state after the stores.
  have b2 : Base s0 { s1 with mem := saveMem s1.mem (State.addr (s1.gpr .r12)) s1.gpr saveL } := by
    refine ⟨h, u1.sp, u1.rd, u1.wr, ?_, fun i hi => ?_⟩
    · rw [u1.gpr]
      refine Frame.sub (rs := [⟨State.addr (stackArg s0 10), 64⟩]) ?_ fun r hr => ⟨rS s0, by simp, ?_⟩
      · rw [← u1.mem]
        exact saveMem_frame _ _ _ (by decide) _ (by decide)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by simp only [cvZ] at hz; omega)
    · have sv := saveMem_saved (lo := 20) (hi := 64) (State.addr (s1.gpr .r12)) s1.gpr s1.mem saveL (by decide)
        _ (saveL_mem hi)
      simp only [u1.gpr] at sv
      show ((saveMem s1.mem (State.addr (s1.gpr .r12)) s1.gpr saveL).readW
        (off (State.addr (cvB s0)) (20 + 4 * i)) 32).toNat = _
      rw [u1.gpr]
      erw [sv]
      have : savedReg i ≠ .r12 := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u1.other _ this]
  refine wp_mov (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  have b4 := (b2.of_rest (u3.rest (ws := [.r8, .r3]) (by simp)) u3.mem).of_rest (u4.rest (ws := [.r3]) (by simp)) u4.mem
  have sp4 : s4.sp.toNat + 48 ≤ 2 ^ 32 := by rw [b4.sp]; exact h.sp48
  refine wp_ldrSp b4.rA_mem sp4 (by decide) fun s5 u5 => ?_
  have b5 := b4.of_rest (u5.rest (ws := [.r4]) (by simp)) u5.mem
  refine wp_ldrSp b5.rA_mem (by rw [b5.sp]; exact h.sp48) (by decide) fun s6 u6 => ?_
  have b6 := b5.of_rest (u6.rest (ws := [.r6]) (by simp)) u6.mem
  have nfit := h.fN
  refine WP.mono (modulusCheck_ok s6 (src := stackArg s0 2) (k := cvK s0) kb.1 kb.2 (by simp only [cvK]; omega)
    ?_ (by rw [u6.other _ (by decide), u5.gpr, b4.arg (by decide)])
    (by rw [u6.gpr, b5.arg (by decide)]; simp only [cvK, BitVec.ofNat_toNat, BitVec.setWidth_eq])) ?_
  · refine ⟨rN s0, List.mem_append_left _ (by rw [b6.rd, h.rd]; simp), Region.contains_self _ _⟩
  · rintro t ⟨z, m, r⟩
    have bt := b6.of_rest r m
    refine ⟨bt, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r.gpr _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr,
        u1.gpr]
    · rw [r.gpr _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
        u3.other _ (by decide)]
      exact u1.other _ (by decide)
    · rw [r.gpr _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide)]
      exact u1.other _ (by decide)
    · rw [r.gpr _ (by decide), u6.gpr, b5.arg (by decide)]
    · have e : Spec.Rsa.bytesAt s6.mem (State.addr (stackArg s0 2)) (cvK s0) = nBytes s0 := by
        unfold Spec.Rsa.bytesAt
        refine List.map_congr_left fun i hi => ?_
        simp only [List.mem_range] at hi
        exact b6.frame.bytes (R := rN s0)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.nS) (by simp; omega) hi
      rw [z, e]

end VG.Proof.Rsa.Arm.CrtValues
