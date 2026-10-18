module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# Interleaved counter mode and GHASH on AArch64: `enc` and `dec`

Untrusted: everything here is checked by Lean. `finish_ok`: `Y` and the
counter stored back; `enc_ok`, `dec_ok`: `Impl.Gcm.AArch64.Stitch.enc` and
`dec` meet `EPost` and `DPost` from a state of `KPre`, for any `ghPart`
that is GHASH (`Gh8Ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv keyStream)
open VG.Proof.Aes.AArch64.Aese (sw32)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly blockAt_store ext8_ext8)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch

/-- What `finish` leaves. -/
structure FPost (s₀ : State) (hb : Nat → Block) (s : State) : Prop where
  y : blockAt s.mem (stp s₀ + BitVec.ofNat 64 16) = yh s₀ hb (8 * nb s₀)
  ctr : blockAt s.mem (stp s₀ + BitVec.ofNat 64 48) = Nat.repeat inc32 (8 * nb s₀) (icb s₀)
  data : DataInv s₀.mem s.mem (dp s₀) (8 * nb s₀) (8 * nb s₀) (kst s₀)
  frame : Frame [yR s₀, cR s₀, dR s₀] s₀.mem s.mem
  gpr : ∀ r, r ∉ kRegs → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finish_ok {s₀ : State} (hp : KPre s₀) {hb : Nat → Block} {s : State}
    (hI : LInv s₀ hb (nb s₀) (nb s₀) s) : WP isa (.block finish) s (FPost s₀ hb) := by
  have hn := hp.n16
  have hs := hp.wrap_s
  have g20 : s.gpr .x20 = stp s₀ := hI.gpr _ (by decide)
  have e60 : stp s₀ + BitVec.ofNat 64 60 = stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 12 := by
    rw [Offset.add_add]
  have hy : InRegions s.wr (s.gpr .x20 + BitVec.ofNat 64 16) 16 := by rw [hI.wr, g20]; exact hp.y_in
  have hc : InRegions s.wr (s.gpr .x20 + BitVec.ofNat 64 60) 4 := by
    rw [hI.wr, g20, e60]
    exact CallLay.inRegions_sub hp.c_in (by omega) (by omega)
  rw [finish, WP.block_cons_iff]
  refine ⟨_, Pmull.exec_rev64b Y Y _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Pmull.exec_strq (t := Y) (off := 16) (by decide) (by decide)
    (by simpa only [wr_setV, gpr_setV] using hy), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_str_w (off := 60) (by decide) (by
    simpa only [wr_write, gpr_write_of_ne _ _ _ (show Reg.x20 ≠ Reg.x12 by decide), wr_setV, gpr_setV] using hc),
    WP.block_nil ?_⟩
  simp only [gpr_write_of_ne _ _ _ (show Reg.x20 ≠ Reg.x12 by decide), gpr_setV, gpr_write_self, g20,
    v_setV_self, mem_setV, mem_write, State.read, sw32, e60]
  have hx10 : BitVec.setWidth Size.w.bits (s.gpr .x10) = ctr0 s₀ + BitVec.ofNat 32 (8 * nb s₀) := by
    have := hI.x10; simp only [State.read] at this; exact this
  rw [hx10]
  generalize hm₁ : s.mem.write (stp s₀ + BitVec.ofNat 64 16) 16 (VRevOp.eval .rev64b (s.v Y)) = m₁
  -- `Y`.
  have fy : Frame [yR s₀] s.mem m₁ := by
    rw [← hm₁]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hy₁ : blockAt m₁ (stp s₀ + BitVec.ofNat 64 16) = yh s₀ hb (8 * nb s₀) := by
    rw [← hm₁, blockAt_store, hI.y, ext8_ext8]
  -- The counter block, apart from `Y` and the data.
  have hcb : ∀ k < 16, m₁ (stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 k) =
      s₀.mem (stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 k) := fun k hk => by
    rw [fy.bytes (R := cR s₀) (by simp only [List.mem_singleton, forall_eq]; exact hp.y_c.symm)
      (by show (16 : Nat) ≤ 2 ^ 64; decide) hk]
    exact hI.frame.bytes (R := cR s₀) (by simp only [List.mem_singleton, forall_eq]; exact hp.d_c.symm)
      (by show (16 : Nat) ≤ 2 ^ 64; decide) hk
  have hcb₁ : blockAt m₁ (stp s₀ + BitVec.ofNat 64 48) = icb s₀ :=
    Proof.Gcm.blockAt_congr fun k hk => hcb k hk
  have hlo : rev32 (m₁.readW (stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 12) 32) = ctr0 s₀ := by
    rw [Proof.Aes.AArch64.icb_lo, hcb₁]
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, hI.sp, hI.rd, hI.wr⟩
  · -- `Y`, apart from the counter word.
    dsimp only
    rw [← hy₁]
    refine Proof.Gcm.blockAt_congr fun k hk => ?_
    exact ((Frame.refl [⟨stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 12, 4⟩] m₁).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)).bytes (R := yR s₀)
      (by simp only [List.mem_singleton, forall_eq]
          exact hp.y_c.sub_right (Offset.sub_base _ (by omega)))
      (by show (16 : Nat) ≤ 2 ^ 64; decide) hk
  · -- The counter.
    dsimp only
    rw [← hcb₁]
    refine Proof.Aes.AArch64.ctr_after fun k hk => ?_
    rw [Proof.Aes.AArch64.writeW_apply, Proof.Aes.AArch64.off_toNat _ (by omega) (by omega), hlo]
    by_cases h : 12 ≤ k
    · rw [ite_eq_left h, ite_eq_left (show k - 12 < 32 / 8 by omega), ite_eq_right (show ¬ k < 12 by omega),
        BitVec.setWidth_eq]
      congr 3
      apply BitVec.eq_of_toNat_eq; simp
    · rw [ite_eq_right h, ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega),
        ite_eq_left (show k < 12 by omega)]
  · -- The data.
    dsimp only
    refine Proof.Aes.AArch64.dataInv_frame (rs := [yR s₀, cR s₀]) ?_ ?_ (by omega)
      (by have := hI.data; rw [show 8 * nb s₀ = 8 * nb s₀ from rfl] at this; exact this)
    · rw [← hm₁]
      exact (((Frame.refl _ _).write (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (Offset.contains_base _ (by omega) (by omega)))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (show (⟨dp s₀, 16 * (8 * nb s₀)⟩ : Region) = dR s₀ by simp [dR]; omega) ▸ hp.d_y
      · exact (show (⟨dp s₀, 16 * (8 * nb s₀)⟩ : Region) = dR s₀ by simp [dR]; omega) ▸ hp.d_c
  · -- The frame.
    dsimp only
    rw [← hm₁]
    exact ((hI.frame.mono fun r hr => by simp at hr ⊢; exact .inr (.inr hr)).write (List.mem_cons_self ..) _
      (Region.contains_self _ _)).writeW (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
      (Offset.contains_base _ (by omega) (by omega))
  · simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    dsimp only
    rw [gpr_write_of_ne _ _ _ hr.2.2.2.1, hI.gpr r (by simp [kRegs, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]

/-! ## The loops -/

theorem enc_ok {s₀ : State} (hp : KPre s₀) (gh : Gh8Ok) : WP isa enc s₀ (EPost s₀) := by
  unfold enc
  refine WP.seq (WP.mono (setup_ok hp (blockC s₀)) fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (byRounds_ok hp (f := encLoop) hI₁ fun s hI => encLoop_ok hp gh hI) fun s₂ hI₂ => ?_)
  refine WP.mono (finish_ok hp hI₂) fun s' h => ⟨Proof.Aes.AArch64.ctr32_of_dataInv h.data, h.ctr, ?_, h.frame,
    h.gpr, h.sp, h.rd, h.wr⟩
  rw [h.y, Proof.Aes.AArch64.ctr32_of_dataInv h.data, ctr32_eq_map]

theorem dec_ok {s₀ : State} (hp : KPre s₀) (gh : Gh8Ok) : WP isa dec s₀ (DPost s₀) := by
  unfold dec
  refine WP.seq (WP.mono (setup_ok hp (blockO s₀)) fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (byRounds_ok hp (f := decLoop) hI₁ fun s hI => decLoop_ok hp gh hI) fun s₂ hI₂ => ?_)
  refine WP.mono (finish_ok hp hI₂) fun s' h => ⟨Proof.Aes.AArch64.ctr32_of_dataInv h.data, h.ctr, ?_, h.frame,
    h.gpr, h.sp, h.rd, h.wr⟩
  rw [h.y]
  rfl

end VG.Proof.Gcm.AArch64.Stitch
