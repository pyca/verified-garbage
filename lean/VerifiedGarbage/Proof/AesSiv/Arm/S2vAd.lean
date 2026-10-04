import VerifiedGarbage.Proof.AesSiv.Arm.CmacOf

/-!
# AES-SIV on ARMv7: a step of S2V over the associated data

Untrusted: everything here is checked by Lean. After the CMAC of a
component into the state at `W + 176` (`cmacOf_ok`), the code doubles `D`
(at `W + 2560`) in place and XORs the CMAC into it, so `D` is then
`dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`); then it moves to the next
descriptor and counts one fewer left (`adStep_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Proof.AesGcm.Arm (ofNat_sub32 z_cmp gpr_subFlags z_subFlags bytesAt_frame covers_left mem_subFlags rd_subFlags wr_subFlags sp_subFlags)
open VG.Proof.CmacAes.Arm (xorBlk xorBlk_ok dbl_wp dblMem dblMem_bytes dblMem_frame)
open VG.Proof.MdStream.Arm (wp_mov op2_reg)

theorem xor4_eq (pb qb cb : Reg) (pd qd cd : Nat) : xor4 pb qb cb pd qd cd = xorBlk .r12 .lr pb qb cb pd qd cd :=
  rfl

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- `adStep`: `dbl(D)` in place with the CMAC state XORed into it, then the
descriptor pointer advanced by 8 and the count decremented, `Z` set when
none are left. -/
theorem adStep_ok {s : State} (he : Env c w sp R s) {a : BitVec 32} {k : Nat} (hk : 0 < k) (hk32 : k < 2 ^ 32)
    (h8 : s.gpr .r8 = a) (h7 : s.gpr .r7 = BitVec.ofNat 32 k) :
    WP isa (.block adStep) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 →
        r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r8 = a + BitVec.ofNat 32 8 ∧ s'.gpr .r7 = BitVec.ofNat 32 (k - 1) ∧ s'.z = decide (k - 1 = 0) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
        Spec.Siv.xor (Spec.Siv.dbl (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16))
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 stOff) 16) := by
  have ww := L.ww
  rw [adStep, List.cons_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have h6₁ : s₁.gpr .r6 = w := by rw [u₁.gpr, he.r11]
  simp only [List.append_eq, List.append_assoc]
  refine dbl_wp (K := w) h6₁ (src := dOff) (dst := dOff) (by decide) (by decide) (by omega) (by omega)
    (by rw [u₁.rd, u₁.wr]; exact covers_left (he.perm.wC (by decide)))
    (by rw [u₁.wr]; exact he.perm.wC (by decide)) fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have h11₂ : s₂.gpr .r11 = w := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u₁.other _ (by decide),
      he.r11]
  rw [xor4_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h11₂]; simp only [dOff]; omega)
    (by rw [h11₂]; simp only [stOff]; omega) (by rw [h11₂]; simp only [dOff]; omega)
    (by rw [h11₂, rd₂, wr₂, u₁.rd, u₁.wr]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₂, rd₂, wr₂, u₁.rd, u₁.wr]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₂, wr₂, u₁.wr]; exact he.perm.wC (by decide)) fun s₃ g₃ => ?_
  have h7₃ : s₃.gpr .r7 = BitVec.ofNat 32 k := by
    rw [g₃.gpr _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), u₁.other _ (by decide), h7]
  have h8₃ : s₃.gpr .r8 = a := by
    rw [g₃.gpr _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), u₁.other _ (by decide), h8]
  have e1 : BitVec.ofNat 32 k - BitVec.ofNat 32 1 = BitVec.ofNat 32 (k - 1) := ofNat_sub32 (by omega) hk32
  refine WP.of_runBlock ⟨_, by arun [h7₃, h8₃], ?_⟩
  have dD : (⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 stOff, 16⟩ := L.w_w (.inr (by decide)) (by decide) (by decide)
  refine ⟨he.keep (fun r hr => ?_) (by simp [sp_setReg, g₃.sp, sp₂, u₁.sp])
      (by simp [rd_setReg, g₃.rd, rd₂, u₁.rd]) (by simp [wr_setReg, g₃.wr, wr₂, u₁.wr]),
    by simp [rd_setReg, g₃.rd, rd₂, u₁.rd], by simp [wr_setReg, g₃.wr, wr₂, u₁.wr], fun r a0 a1 a2 a3 a4 a6 a7 a8 a12 alr => ?_,
    by simp [gpr_setReg, h8₃], by simp [gpr_setReg, h7₃, e1], ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp [gpr_setReg, g₃.gpr _ (by decide : Reg.r9 ≠ .r12) (by decide), g₃.gpr _ (by decide : Reg.r10 ≠ .r12) (by decide),
        g₃.gpr _ (by decide : Reg.r11 ≠ .r12) (by decide), g₂, u₁.other]
  · simp only [gpr_setReg, gpr_subFlags, a7, a8, ite_false, reduceCtorEq]
    rw [g₃.gpr r a12 alr, g₂ r a0 a1 a2 a3 a4 a12, u₁.other r a6]
  · simp only [z_setReg, z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h7₃]
    rw [z_cmp hk32 (by decide)]
    simp only [decide_eq_decide]; omega
  · simp only [mem_setReg, mem_subFlags, g₃.mem, m₂, u₁.mem, h11₂]
    exact (dblMem_frame _ _ _ _).trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
  · simp only [mem_setReg, mem_subFlags, g₃.mem, m₂, u₁.mem, h11₂]
    rw [Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint dD), dblMem_bytes,
      bytesAt_frame (dblMem_frame _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD.symm) (by decide)]
    rfl

end

end VG.Proof.AesSiv.Arm
