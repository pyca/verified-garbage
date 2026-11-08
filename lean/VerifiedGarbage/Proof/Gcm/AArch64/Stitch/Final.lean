module
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Base

import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Interleaved counter mode and GHASH on AArch64: `enc` and `dec`

Untrusted: everything here is checked by Lean. `finish_ok`: `Y` and the
counter stored back; `enc_ok`, `dec_ok`: `Impl.Gcm.AArch64.Stitch.enc` and
`dec` meet `EPost` and `DPost` from a state of `KPre`, for any `ghPart`
that is GHASH (`Gh8Ok`); `decM_ok`: `dec to` meets `DPostT` from a state of
`KPreM`, the plaintext over the text or, out of place, at the destination.
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
structure FPost (s₀ : State) (to : Bool) (hb : Nat → Block) (s : State) : Prop where
  y : blockAt s.mem (stp s₀ + BitVec.ofNat 64 16) = yh s₀ hb (8 * nb s₀)
  ctr : blockAt s.mem (stp s₀ + BitVec.ofNat 64 48) = Nat.repeat inc32 (8 * nb s₀) (icb s₀)
  data : DataInvM s₀.mem s.mem (dp s₀) (op s₀ to) (8 * nb s₀) (8 * nb s₀) (kst s₀)
  frame : Frame [yR s₀, cR s₀, oR s₀ to] s₀.mem s.mem
  gpr : ∀ r, r ∉ kRegsT to → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finish_ok {s₀ : State} {to : Bool} (hp : KPreM s₀ to) {hb : Nat → Block} {s : State}
    (hI : LInv s₀ to hb (nb s₀) (nb s₀) s) : WP isa (.block finish) s (FPost s₀ to hb) := by
  have hn := hp.n16
  have hs := hp.wrap_s
  have g20 : s.gpr .x20 = stp s₀ := hI.gpr _ (notMem_kRegsT _ (by decide))
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
    exact hI.frame.bytes (R := cR s₀) (by simp only [List.mem_singleton, forall_eq]; exact hp.o_c.symm)
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
    refine dataInvM_frame (rs := [yR s₀, cR s₀]) ?_ ?_ (by omega)
      (by have := hI.data; rw [show 8 * nb s₀ = 8 * nb s₀ from rfl] at this; exact this)
    · rw [← hm₁]
      exact (((Frame.refl _ _).write (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (Offset.contains_base _ (by omega) (by omega)))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (show (⟨op s₀ to, 16 * (8 * nb s₀)⟩ : Region) = oR s₀ to by simp [oR]; omega) ▸ hp.o_y
      · exact (show (⟨op s₀ to, 16 * (8 * nb s₀)⟩ : Region) = oR s₀ to by simp [oR]; omega) ▸ hp.o_c
  · -- The frame.
    dsimp only
    rw [← hm₁]
    exact ((hI.frame.mono fun r hr => by simp at hr ⊢; exact .inr (.inr hr)).write (List.mem_cons_self ..) _
      (Region.contains_self _ _)).writeW (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
      (Offset.contains_base _ (by omega) (by omega))
  · have hk := (kRegsT_not hr).1
    simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    dsimp only
    rw [gpr_write_of_ne _ _ _ hk.2.2.2.1, hI.gpr r hr]

/-- The blocks of the output, once all are written. -/
theorem ctr32_of_dataInvM {m₀ m : Mem} {D O : Addr} {n R : Nat} {w : List Byte}
    {icb : Block} (h : DataInvM m₀ m D O n n (keyStream R w icb)) :
    blocksAt m O n = ctr32 (aesWith R w) icb (blocksAt m₀ D n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine Proof.Aes.block_ext fun k hk => ?_
  rw [Proof.Aes.toBytes_xor _ _ hk, Proof.Aes.toBytes_blockAt _ _ hk, Proof.Aes.toBytes_blockAt _ _ hk,
    BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add, h _ (by omega_arith),
    ite_eq_left (by omega_arith)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [Proof.Aes.toBytes_ofBytes (by simp) hk, keyStream, show (16 * i + k) / 16 = i by omega_arith,
    show (16 * i + k) % 16 = k by omega_arith, Proof.Aes.getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## The loops -/

theorem enc_ok {s₀ : State} (hp : KPre s₀) (gh : Gh8Ok) : WP isa enc s₀ (EPost s₀) := by
  have hm := hp.toM
  unfold enc
  refine WP.seq (WP.mono (setup_ok hm (blockC s₀)) fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (byRounds_ok hm (f := encLoop) hI₁ fun s hI => encLoop_ok hm gh hI) fun s₂ hI₂ => ?_)
  refine WP.mono (finish_ok hm hI₂) fun s' h =>
    ⟨Proof.Aes.AArch64.ctr32_of_dataInv (dataInvM_self.mp h.data), h.ctr, ?_, h.frame, h.gpr, h.sp, h.rd, h.wr⟩
  rw [h.y, Proof.Aes.AArch64.ctr32_of_dataInv (dataInvM_self.mp h.data), ctr32_eq_map]

/-- The decryption to `op s₀ to`: over the text, or out of place. -/
theorem decM_ok {s₀ : State} {to : Bool} (hp : KPreM s₀ to) (gh : Gh8Ok) :
    WP isa (dec to) s₀ (DPostT s₀ to) := by
  unfold dec
  refine WP.seq (WP.mono (setup_ok hp (blockO s₀)) fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (byRounds_ok hp (f := fun nr => decLoop nr to) hI₁ fun s hI => decLoop_ok hp gh hI)
    fun s₂ hI₂ => ?_)
  refine WP.mono (finish_ok hp hI₂) fun s' h => ⟨ctr32_of_dataInvM h.data, h.ctr, ?_, h.frame,
    h.gpr, h.sp, h.rd, h.wr⟩
  rw [h.y]
  rfl

theorem dec_ok {s₀ : State} (hp : KPre s₀) (gh : Gh8Ok) : WP isa dec s₀ (DPost s₀) :=
  WP.mono (decM_ok hp.toM gh) fun _ h => ⟨h.data, h.ctr, h.y, h.frame, h.gpr, h.sp, h.rd, h.wr⟩

end VG.Proof.Gcm.AArch64.Stitch
