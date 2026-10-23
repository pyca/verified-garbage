module

public import VerifiedGarbage.Proof.Rsa.Arm.KcFnBase
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.KeyWorkspace

/-! # The checks of an RSA key on ARMv7: the entry's first block, and every array zeroed

`EntSt σ s A`: during the entry, the working space's registers are set, `w`
is in the division's header, every array holds `A` (all its `w + 2` words),
and `n` and `n_len` are kept in `r10` and `r11`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Arm.Spill VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (reg)

section
variable {nA iS : Nat} {ins : List (Nat × Nat)}

structure EntSt (nA iS : Nat) (ins : List (Nat × Nat)) (σ s : State) (A : Nat → Nat) : Prop where
  base : FnBase nA iS ins σ s
  ws : Ws s (geo iS σ).B (geo iS σ).Z (geo iS σ).w nArr
  cnt : s.mem.readW (off (State.addr (geo iS σ).B) 16) 32 = BitVec.ofNat 32 (geo iS σ).w
  full : ∀ j < nArr, val32 s.mem (State.addr (geo iS σ).B) (arr (geo iS σ).w j) ((geo iS σ).w + 2) = A j
  r10 : s.gpr .r10 = σ.gpr .r0
  r11 : s.gpr .r11 = σ.gpr .r1

/-- The registers saved, and where. -/
def saveK : List (Reg × Nat) :=
  [(.r4, 20), (.r5, 24), (.r6, 28), (.r7, 32), (.r8, 36), (.r9, 40), (.r10, 44), (.r11, 48), (.lr, 52),
   (.r2, 56), (.r3, 60)]

theorem entrySave_eq : entrySave = saveK.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([.mov .r8 (.reg .r12), .mov .r10 (.reg .r0), .mov .r11 (.reg .r1), .mov .r4 (.reg .r2),
      .mov .r6 (.reg .r3)] : List Instr) := rfl

theorem saveK_mem {i : Nat} (hi : i < 11) : (savedReg i, 20 + 4 * i) ∈ saveK := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem savedReg_ne {i : Nat} (hi : i < 11) : savedReg i ≠ .r12 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `ldr r12, [sp, #oS]` and the registers saved. -/
theorem save_ok {σ : State} (h : FnPre nA iS ins σ) (h4 : 4 * iS < 4096) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, FnBase nA iS ins σ t → t.gpr .r12 = (geo iS σ).B → (∀ r, r ≠ .r12 → t.gpr r = σ.gpr r) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.ldrSp .r12 (4 * iS) :: (saveK.map (fun p => Instr.str p.1 .r12 p.2) ++ rest))) σ Q := by
  have fS := h.fS
  have fits := h.fits
  have hz : 64 ≤ (stackArg σ (iS + 1)).toNat * 8 := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega) fits
  refine wp_ldrSpA h.rdA h.sp (by have := h.hS; omega) h4 fun s1 u1 => ?_
  refine save_slots_ok (lo := 20) (hi := 64) (by decide) (by rw [u1.gpr]; omega)
    (fun d h1 h2 => ⟨rS iS σ, by rw [u1.wr, h.wr]; simp, by
      rw [u1.gpr]; exact Offset.contains_base _ (by omega) (by omega)⟩) ?_
  refine k _ ⟨h, u1.sp, u1.rd, u1.wr, ?_, fun i hi => ?_⟩ u1.gpr
    (fun r hr => u1.other r hr)
  · rw [u1.gpr]
    refine Frame.sub (rs := [⟨State.addr (stackArg σ iS), 64⟩]) ?_ fun r hr => ⟨rS iS σ, by simp, ?_⟩
    · rw [← u1.mem]
      exact saveMem_frame _ _ _ (by decide) _ (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega)
  · have sv := saveMem_saved (lo := 20) (hi := 64) (State.addr (s1.gpr .r12)) s1.gpr s1.mem saveK (by decide)
      _ (saveK_mem hi)
    simp only [u1.gpr] at sv
    show ((saveMem s1.mem (State.addr (s1.gpr .r12)) s1.gpr saveK).readW
      (off (State.addr (stackArg σ iS)) (20 + 4 * i)) 32).toNat = _
    rw [u1.gpr]
    erw [sv]
    rw [u1.other _ (savedReg_ne hi)]

/-- The entry's first block and `zero`: every array zero. -/
theorem entryFirst_ok {σ : State} (h : FnPre nA iS ins σ) (h4 : 4 * iS < 4096) :
    WP isa (seqs [.block (([.ldrSp .r12 (4 * iS)] : List Instr) ++ entrySave ++ setup), zero]) σ fun t =>
      EntSt nA iS ins σ t (fun _ => 0) ∧ t.gpr .r4 = σ.gpr .r2 ∧ t.gpr .r6 = σ.gpr .r3 := by
  have w16 := h.w16
  have kb := h.kb
  have fits := h.fits
  have fS := h.fS
  rw [wp_seqs_cons (List.cons_ne_nil _ _), entrySave_eq]
  simp only [List.cons_append, List.append_assoc]
  refine save_ok h h4 fun s1 b1 p12 o1 => ?_
  simp only [List.nil_append]
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_mov (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => ?_
  refine wp_mov (op2_reg _ _) fun s6 u6 => ?_
  have r6' : Rest [.r8, .r10, .r11, .r4, .r6] s1 s6 := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp)))))
  have m6 : s6.mem = s1.mem := u6.mem.trans (u5.mem.trans (u4.mem.trans (u3.mem.trans u2.mem)))
  have b6 := b1.of_rest r6' m6
  have e8 : s6.gpr .r8 = (geo iS σ).B := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      p12]
  have e10 : s6.gpr .r10 = σ.gpr .r0 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
      o1 _ (by decide)]
  have e11 : s6.gpr .r11 = σ.gpr .r1 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide), u2.other _ (by decide),
      o1 _ (by decide)]
  have e4 : s6.gpr .r4 = σ.gpr .r2 := by
    rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      o1 _ (by decide)]
  have e6 : s6.gpr .r6 = σ.gpr .r3 := by
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      o1 _ (by decide)]
  -- `setup`.
  unfold setup ctxK
  simp only [List.append_assoc, List.cons_append]
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s8 u8 => ?_
  have h9 : s8.gpr .r9 = BitVec.ofNat 32 (geo iS σ).w := by
    rw [u8.gpr, u7.gpr, dpVal, e11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (3 : BitVec 32).toNat = 3 from rfl]
    simp only [Geo.w, fK] at *
    omega_arith
  refine stride_ok (by omega_arith) h9 fun s9 h7 r9 m9 => ?_
  have r79 : Rest [.r9, .r7] s6 s9 := (u7.rest (by simp)).trans ((u8.rest (by simp)).trans (r9.mono (by simp)))
  have m79 : s9.mem = s6.mem := m9.trans (u8.mem.trans u7.mem)
  have ws9 : Ws s9 (geo iS σ).B (geo iS σ).Z (geo iS σ).w nArr :=
    ⟨fS, by rw [r79.wr, r6'.wr, b1.wr, h.wr]; simp, fits, by omega_arith, by omega_arith, h7,
      by rw [r79.gpr _ (by decide), e8], by rw [r9.gpr _ (by decide), h9]⟩
  have b9 := b6.of_rest r79 m79
  refine wp_strSlot ws9 (d := 16) (by decide) fun s10 u10 => ?_
  have ws10 := ws9.of_mupd u10
  have hz : 64 ≤ (geo iS σ).Z := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_arith) fits
  have o10 := writeW32_outside s9.mem (State.addr (geo iS σ).B) (d := 16) (s9.gpr .r9) (by decide)
  rw [← u10.mem] at o10
  have b10 := b9.outside o10 (by omega_arith) (by omega_arith) u10.sp u10.rd u10.wr
  have c10 : s10.mem.readW (off (State.addr (geo iS σ).B) 16) 32 = BitVec.ofNat 32 (geo iS σ).w := by
    rw [u10.mem, Mem.readW_writeW_self32, ws9.r9]
  refine wp_dp (op2_imm (by decide)) fun s11 u11 => ?_
  refine wp_mov (op2_imm (by decide)) fun s12 u12 => ?_
  refine wp_mul fun s13 u13 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s14 u14 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u15 => WP.block_nil ?_
  have rest : Rest [.r0, .lr, .r3] s10 u := (u11.rest (by simp)).trans ((u12.rest (by simp)).trans
    ((u13.rest (by simp)).trans ((u14.rest (by simp)).trans (u15.rest (by simp)))))
  have mu : u.mem = s10.mem := by rw [u15.mem, u14.mem, u13.mem, u12.mem, u11.mem]
  have bu := b10.of_rest rest mu
  have hu := ws10.rest rest
  have p0 : u.gpr .r0 = (geo iS σ).B + BitVec.ofNat 32 hdr := by
    rw [u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide), u11.gpr,
      dpVal, ws10.r8]
  have plr : u.gpr .lr = BitVec.ofNat 32 (nArr * ((geo iS σ).w + 2)) := by
    rw [u15.other _ (by decide), u14.gpr, u13.gpr, u12.gpr, u12.other _ (by decide), u11.other _ (by decide),
      ws10.r7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nArr, S]
    rw [Nat.mod_eq_of_lt (a := 24) (by decide), Nat.mod_eq_of_lt (a := 4 * ((geo iS σ).w + 2)) (by omega_arith),
      Nat.mod_eq_of_lt (a := 24 * (4 * ((geo iS σ).w + 2))) (by omega_arith),
      Nat.mod_eq_of_lt (a := 24 * ((geo iS σ).w + 2)) (by omega_arith)]
    omega_arith
  have nfit : hdr + 4 * (nArr * ((geo iS σ).w + 2)) ≤ (geo iS σ).Z := by
    simp only [arr, S, nArr] at fits ⊢; omega_arith
  refine WP.mono (zero_ok u (base := (geo iS σ).B) (size := (geo iS σ).Z) (o := hdr) (n := nArr * ((geo iS σ).w + 2))
    ⟨fS, nfit, ⟨rS iS σ, by rw [bu.wr, h.wr]; simp, Region.contains_self _ _⟩⟩
    (by simp only [nArr]; omega_arith) p0 plr (by rw [u15.gpr])) fun t inv => ?_
  have bt := bu.outside inv.outside (by simp only [hdr]; omega_arith) nfit inv.rest.sp inv.rest.rd inv.rest.wr
  have rT : Rest [.r0, .lr, .r3, .r7, .r9] s6 t :=
    (r79.mono (by simp)).trans ((u10.rest _).trans ((rest.trans (inv.rest.mono (by simp))).mono (by simp)))
  refine ⟨⟨bt, hu.rest inv.rest, ?_, fun j hj => ?_, by rw [rT.gpr _ (by decide), e10],
    by rw [rT.gpr _ (by decide), e11]⟩, by rw [rT.gpr _ (by decide), e4], by rw [rT.gpr _ (by decide), e6]⟩
  · have e := inv.outside.w32 (d := 16) (by simp only [hdr]; omega_arith) (by omega_arith)
    apply BitVec.eq_of_toNat_eq
    rw [show (t.mem.readW (off (State.addr (geo iS σ).B) 16) 32).toNat = w32 t.mem (State.addr (geo iS σ).B) 16
      from rfl, e, show w32 u.mem (State.addr (geo iS σ).B) 16 = (u.mem.readW (off (State.addr (geo iS σ).B) 16) 32).toNat
      from rfl, mu, c10]
  · have := VG.Proof.Rsa.Arm.CrtValues.val32_zero_part inv.value (a := j * ((geo iS σ).w + 2))
      (c := (geo iS σ).w + 2) (by
      have := Nat.mul_le_mul_right ((geo iS σ).w + 2) (show j + 1 ≤ nArr by omega_arith)
      rw [Nat.succ_mul] at this; omega_arith)
    simpa only [arr, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

end

end VG.Proof.Rsa.Arm.KeyCheck
