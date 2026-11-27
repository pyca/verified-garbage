module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Loop
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Interleaved counter mode and GHASH on AArch64: `enc` and `dec`

Untrusted: everything here is checked by Lean. `enc_ok`, `dec_ok`: from a
state of `KPre`, `Impl.Gcm.AArch64.Stitch.enc` and `dec` meet `EPost` and
`DPost`, for any `ghPart` that is GHASH (`Gh8Ok`, proven in
`Proof/AesGcm/AArch64/GhashImpls.lean`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv DataInvM dataInvM_self dataInvM_frame dataInvM_store1 ctr32_of_dataInvM keyStream)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq eval_zero eval_nonzero sw32)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly rev64b_read)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch

/-! ## Registers but `kRegs` -/

/-- The invariant does not depend on `x13` and `x14`. -/
theorem LInv.of_x1314 {s₀ : State} {to : Bool} {hb : Nat → Block} {c h : Nat} {s s' : State}
    (hI : LInv s₀ to hb c h s)
    (hg : ∀ r, r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) (hv : s'.v = s.v) (hm : s'.mem = s.mem)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : LInv s₀ to hb c h s' where
  le := hI.le
  x9 := by rw [hg _ (by decide) (by decide), hI.x9]
  x10 := by simp only [State.read]; rw [hg _ (by decide) (by decide)]; exact hI.x10
  x11 := by rw [hg _ (by decide) (by decide), hI.x11]
  xo ht := by rw [hg _ (by decide) (by decide), hI.xo ht]
  gpr r hr := by
    have hk := (kRegsT_not hr).1
    rw [hg r (fun h => hk (by simp [h])) (fun h => hk (by simp [h])), hI.gpr r hr]
  y := by rw [hv, hI.y]
  cr := by rw [hv, hI.cr]
  data := by rw [hm]; exact hI.data
  frame := by rw [hm]; exact hI.frame
  sp := by rw [hsp, hI.sp]
  rd := by rw [hrd, hI.rd]
  wr := by rw [hwr, hI.wr]

/-! ## The setup -/

theorem ushr7 {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 7 = BitVec.ofNat 64 (n / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith)]

theorem setup_ok {s₀ : State} {to : Bool} (hp : KPreM s₀ to) (hb : Nat → Block) :
    WP isa (.block setup) s₀ (LInv s₀ to hb 0 0) := by
  have hn := hp.n16
  have hc12 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x20 + BitVec.ofNat 64 60) 4 := by
    rw [show s₀.gpr .x20 + BitVec.ofNat 64 60 = stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 12 by
      rw [Offset.add_add]]
    exact CallLay.inRegions_sub (inRegions_wr hp.c_in) (by omega_arith) (by omega_arith)
  have hy : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x20 + BitVec.ofNat 64 16) 16 := inRegions_wr hp.y_in
  rw [setup, WP.block_cons_iff]
  refine ⟨_, exec_ldr_w (off := 60) (by decide) hc12, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Pmull.exec_movz_x (imm := 0xc200) (hw := 3) (by decide) _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Pmull.exec_dup_d2 C .x12 _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Pmull.exec_ldrq (t := Y) (off := 16) (by decide) (by decide)
    (by simpa only [gpr_setV, rd_setV, wr_setV, gpr_write_of_ne _ _ _ (show Reg.x20 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x20 ≠ Reg.x10 by decide), rd_write, wr_write] using hy), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Pmull.exec_rev64b Y Y _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 7) (by decide), WP.block_nil ?_⟩
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, fun _ => ?_, fun r hr => ?_, ?_, ?_, ?_, Frame.refl _ _, rfl, rfl, rfl⟩
  · simp only [gpr_write, gpr_setV, reduceCtorEq, ite_false, ite_true, State.read, BitVec.setWidth_eq,
      Nat.mul_zero]
  · simp only [State.read, gpr_write_self, gpr_write_of_ne _ _ _ (show Reg.x10 ≠ Reg.x11 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x10 ≠ Reg.x9 by decide), gpr_setV,
      gpr_write_of_ne _ _ _ (show Reg.x10 ≠ Reg.x12 by decide), sw32]
    rw [show s₀.gpr .x20 + BitVec.ofNat 64 60 = stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 12 by
      rw [Offset.add_add], Proof.Aes.AArch64.icb_lo, Nat.mul_zero, BitVec.add_zero]
  · simp only [gpr_write_self, gpr_write_of_ne _ _ _ (show Reg.x26 ≠ Reg.x9 by decide), gpr_setV,
      gpr_write_of_ne _ _ _ (show Reg.x26 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x26 ≠ Reg.x10 by decide), State.read, BitVec.setWidth_eq]
    rw [show s₀.gpr .x26 = BitVec.ofNat 64 (s₀.gpr .x26).toNat by simp, ushr7 (BitVec.isLt _), Nat.sub_zero]
  · simp only [gpr_write_of_ne _ _ _ (show Reg.x15 ≠ Reg.x11 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x15 ≠ Reg.x9 by decide), gpr_setV,
      gpr_write_of_ne _ _ _ (show Reg.x15 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x15 ≠ Reg.x10 by decide), Nat.mul_zero, BitVec.add_zero]
  · have hr := (kRegsT_not hr).1
    simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write_of_ne _ _ _ hr.2.2.1, gpr_write_of_ne _ _ _ hr.1, gpr_setV,
      gpr_write_of_ne _ _ _ hr.2.2.2.1, gpr_write_of_ne _ _ _ hr.2.1]
  · simp only [v_write, v_setV_self, mem_setV, mem_write, gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x20 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x20 ≠ Reg.x10 by decide)]
    rw [rev64b_read, yh, Nat.mul_zero, List.range_zero, List.map_nil]
    rfl
  · simp only [v_write, v_setV_of_ne _ _ (show C ≠ Y by decide), v_setV_self, gpr_write_self]
    rfl
  · intro i hi
    rw [ite_eq_right (by omega_arith)]
    rfl

/-! ## The loops -/

/-- `open`'s loop: each batch decrypted while it is hashed, the plaintext
stored over it or, out of place, to the destination. -/
theorem decLoop_ok {s₀ : State} {to : Bool} (hp : KPreM s₀ to) (gh : Gh8Ok) {s : State}
    (hI : LInv s₀ to (blockO s₀) 0 0 s) :
    WP isa (decLoop (rounds s₀) to) s (LInv s₀ to (blockO s₀) (nb s₀) (nb s₀)) := by
  have hn := hp.n16
  have h1 := hp.nb1
  let I : Nat → State → Prop := fun m s => ∃ h, m = nb s₀ - h ∧ h < nb s₀ ∧ LInv s₀ to (blockO s₀) h h s
  have hstep : ∀ m s, I m s → WP isa (.block (decBody (rounds s₀) to)) s (fun s' =>
      (AArch64.eval (.nonzero .x .x11) s' = some false ∧ LInv s₀ to (blockO s₀) (nb s₀) (nb s₀) s') ∨
      (AArch64.eval (.nonzero .x .x11) s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨h, rfl, hh, hI⟩
    refine WP.mono (body_ok hp gh (c := h) (h := h) (o := 0) hh hh (by omega_arith) (.inl rfl) (fun _ => rfl) hI
      fun j hj => Proof.Gcm.blockAt_congr fun k hk => by
        rw [Offset.add_add, hI.src hp (by omega_arith) (by omega_arith)]) fun s' hI' => ?_
    rw [eval_nonzero hI'.x11 (by omega_arith)]
    by_cases hl : nb s₀ - (h + 1) = 0
    · have e : h + 1 = nb s₀ := by omega_arith
      exact .inl ⟨by simp [hl], by rw [← e]; exact hI'⟩
    · exact .inr ⟨by simp [hl], nb s₀ - (h + 1), by omega_arith, h + 1, rfl, by omega_arith, hI'⟩
  exact WP.loop (M := isa) I hstep _ _ ⟨0, rfl, by omega_arith, hI⟩

/-- The loop for the number of rounds. -/
theorem byRounds_ok {s₀ : State} {to : Bool} (hp : KPreM s₀ to) {f : Nat → Prog isa} {Q : State → Prop}
    {hb : Nat → Block} {s : State} (hI : LInv s₀ to hb 0 0 s)
    (hf : ∀ s, LInv s₀ to hb 0 0 s → WP isa (f (rounds s₀)) s Q) :
    WP isa (byRounds f) s Q := by
  have hR := hp.rounds
  have hx22 : s.gpr .x22 = BitVec.ofNat 64 (rounds s₀) := by
    rw [hI.gpr _ (notMem_kRegsT _ (by decide))]; simp [rounds]
  rw [byRounds, WP.seq_iff, WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 12) (by decide), WP.block_nil ?_⟩
  have hI' := hI.of_x1314 (s' := ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
      ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12)))
    (fun r h13 h14 => by rw [gpr_write_of_ne _ _ _ h14, gpr_write_of_ne _ _ _ h13]) rfl rfl rfl rfl rfl
  have e13 : ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
      ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12)).gpr .x13 =
      BitVec.ofNat 64 (rounds s₀ - 10) := by
    simp only [gpr_write_of_ne _ _ _ (show Reg.x13 ≠ Reg.x14 by decide), gpr_write_self, State.read,
      BitVec.setWidth_eq, hx22, Size.bits]
    rw [Offset.ofNat_sub_ofNat (by omega_arith)]
  refine WP.ite _ (eval_zero e13 (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h10 : rounds s₀ = 10 := by simp only [decide_eq_true_eq] at h; omega_arith
    have e := hf _ hI'
    rw [h10] at e; exact e
  · have hge : 12 ≤ rounds s₀ := by simp only [decide_eq_false_iff_not] at h; omega_arith
    have e14 : ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
        ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12)).gpr .x14 =
        BitVec.ofNat 64 (rounds s₀ - 12) := by
      simp only [gpr_write_self, State.read, BitVec.setWidth_eq,
        gpr_write_of_ne _ _ _ (show Reg.x22 ≠ Reg.x13 by decide), hx22, Size.bits]
      rw [Offset.ofNat_sub_ofNat (by omega_arith)]
    refine WP.ite _ (eval_zero e14 (by omega_arith)) (fun h' => ?_) (fun h' => ?_)
    · have h12 : rounds s₀ = 12 := by simp only [decide_eq_true_eq] at h'; omega_arith
      have e := hf _ hI'
      rw [h12] at e; exact e
    · have h14 : rounds s₀ = 14 := by simp only [decide_eq_false_iff_not] at h'; omega_arith
      have e := hf _ hI'
      rw [h14] at e; exact e

end VG.Proof.Gcm.AArch64.Stitch
