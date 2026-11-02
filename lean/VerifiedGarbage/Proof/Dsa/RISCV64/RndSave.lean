module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Random
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Mont.Words
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on RISC-V: the randomized functions' frame

As on PPC64LE (`Proof/Dsa/PPC64LE/Random/Save.lean`). `saveRegs_ok`:
`s0`–`s11` and `ra` to the frame's words at `oSave`; `restoreRegs_ok`: back
from them; `clearNonce_ok`: the nonce's 32 octets := 0.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Rnd

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont

theorem cs_inj : ∀ i < 12, ∀ j < 12, cs i = cs j → i = j := by decide

theorem cs_ne : ∀ i < 12, cs i ≠ .t0 ∧ cs i ≠ .ra := by decide

theorem save_sep {F : Addr} {i j : Nat} (hi : i < 13) (hj : j < 13) (h : i ≠ j) :
    Mem.Sep (off F (oSave + 8 * i)) 8 (off F (oSave + 8 * j)) 8 :=
  VG.Offset.sep F (by simp only [oSave]; omega) (by simp only [oSave]; omega) (by simp only [oSave]; omega)

/-- The frame's words at `oSave`, aligned and writable. -/
def SaveW (s : State) (F : Addr) : Prop :=
  ∀ i < 13, InRegions s.wr (off F (oSave + 8 * i)) 8 ∧ (off F (oSave + 8 * i)).toNat % 8 = 0

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (F : Addr) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  out : Outside F oSave (8 * 12) s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off F (oSave + 8 * i)) 64 = s₀.gpr (cs i)

theorem save_step (s₀ : State) {F : Addr} (_hF : F.toNat + frameBytes ≤ 2 ^ 64) (h0 : s₀.gpr .t0 = F)
    (hw : SaveW s₀ F) {n : Nat} (hn : n < 12) {s : State}
    (h : SI s₀ F n s) : WP isa (.block [.store .d (cs n) .t0 (oSave + 8 * n)]) s (SI s₀ F (n + 1)) := by
  have h0' : s.gpr .t0 = F := by rw [h.gpr, h0]
  have hout : InRegions s.wr (s.gpr .t0 + BitVec.ofNat 64 (oSave + 8 * n)) 8 := by
    rw [h.wr, h0']; exact (hw n (by omega)).1
  have ha : (s.gpr .t0 + BitVec.ofNat 64 (oSave + 8 * n)).toNat % 8 = 0 := by
    rw [h0']; exact (hw n (by omega)).2
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show oSave + 8 * n < 2048 by simp only [oSave]; omega) ha hout, Option.some.injEq,
    exists_eq_left', h0']
  refine ⟨h.gpr, h.rd, h.wr, h.sp, ?_, fun i hi => ?_⟩
  · exact h.out.trans ((writeW_outside s.mem F (d := oSave + 8 * n) _ (by simp only [oSave]; omega)).mono
      (by omega) (by omega))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (save_sep (by omega) (by omega) (by omega)) (by decide)]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-- What `saveRegs` leaves, from `s₀`. -/
structure Saved (s₀ : State) (F : Addr) (s : State) : Prop where
  t0 : s.gpr .t0 = F
  others : ∀ r, r ≠ .t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  out : Outside F oSave (8 * 13) s₀.mem s.mem
  saved : ∀ i < 12, s.mem.readW (off F (oSave + 8 * i)) 64 = s₀.gpr (cs i)
  savedRa : s.mem.readW (off F (oSave + 96)) 64 = s₀.gpr .ra

theorem saveRegs_ok (s₀ : State) {F : Addr} (hF : F.toNat + frameBytes ≤ 2 ^ 64) (hsp : s₀.sp = F)
    (hw : SaveW s₀ F) :
    WP isa (.block saveRegs) s₀ (Saved s₀ F) := by
  have hF' := hF
  simp only [frameBytes] at hF'
  rw [saveRegs, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t0] (Q := fun s => s.gpr .t0 = F ∧ s.mem = s₀.mem ∧ s.sp = s₀.sp)
    (by brun [exec_addSp (show 0 < 2048 by decide), hsp, BitVec.add_zero]) (by decide) (by rfl))
    fun s₁ ⟨⟨a0, m1, sp1⟩, k1⟩ => ?_
  have hw1 : SaveW s₁ F := fun i hi => by rw [k1.2.2]; exact hw i hi
  refine WP.mono (wp_range_flatMap (M := isa) (SI s₁ F) (fun k s hk h => save_step s₁ hF a0 hw1 hk h) 12
    (Nat.le_refl _) s₁ ⟨rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s h => ?_
  have h0 : s.gpr .t0 = F := by rw [h.gpr, a0]
  have hst : InRegions s.wr (s.gpr .t0 + BitVec.ofNat 64 (oSave + 96)) 8 := by
    rw [h.wr, h0]; exact (hw1 12 (by decide)).1
  have hal : (s.gpr .t0 + BitVec.ofNat 64 (oSave + 96)).toNat % 8 = 0 := by
    rw [h0]; exact (hw1 12 (by decide)).2
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show oSave + 96 < 2048 by decide) hal hst, Option.some.injEq, exists_eq_left']
  refine ⟨h0, fun r h0' => ?_, by rw [h.rd, k1.2.1], by rw [h.wr, k1.2.2], by rw [h.sp, sp1], ?_,
    fun i hi => ?_, ?_⟩
  · show s.gpr r = _
    rw [h.gpr]; exact k1.gpr (by simp [h0'])
  · show Outside F oSave (8 * 13) s₀.mem (s.mem.writeW (s.gpr .t0 + BitVec.ofNat 64 (oSave + 96)) (s.gpr .ra))
    rw [h0, ← m1]
    exact (h.out.mono (by omega) (by omega)).trans
      ((writeW_outside s.mem F (d := oSave + 96) _ (by simp only [oSave]; omega)).mono
        (by simp only [oSave]; omega) (by simp only [oSave]; omega))
  · show (s.mem.writeW (s.gpr .t0 + BitVec.ofNat 64 (oSave + 96)) (s.gpr .ra)).readW _ 64 = _
    rw [h0, show F + BitVec.ofNat 64 (oSave + 96) = off F (oSave + 8 * 12) from rfl,
      Mem.readW_writeW_sep (save_sep (by omega) (by decide) (by omega)) (by decide), h.saved i hi,
      k1.gpr (by have := cs_ne i hi; simp [this.1])]
  · show (s.mem.writeW (s.gpr .t0 + BitVec.ofNat 64 (oSave + 96)) (s.gpr .ra)).readW _ 64 = _
    rw [h0, show off F (oSave + 96) = F + BitVec.ofNat 64 (oSave + 96) from rfl, Mem.readW_writeW_self64, h.gpr,
      k1.gpr (by decide)]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (F : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  t0 : s.gpr .t0 = F
  restored : ∀ i < n, s.gpr (cs i) = v i
  others : ∀ r, r ≠ .t0 → r ≠ .ra → (∀ i < 12, r ≠ cs i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  ra : s.gpr .ra = v 12

theorem restore_step (sB : State) {F : Addr} {v : Nat → BitVec 64}
    (hw : SaveW sB F) (hsav : ∀ i < 12, sB.mem.readW (off F (oSave + 8 * i)) 64 = v i)
    {n : Nat} (hn : n < 12) {s : State} (h : RI sB F v n s) :
    WP isa (.block [.load .d (cs n) .t0 (oSave + 8 * n)]) s (RI sB F v (n + 1)) := by
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .t0 + BitVec.ofNat 64 (oSave + 8 * n)) 8 := by
    rw [h.rd, h.wr, h.t0]
    obtain ⟨r, hr, hc⟩ := (hw n (by omega)).1
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .t0 + BitVec.ofNat 64 (oSave + 8 * n)).toNat % 8 = 0 := by
    rw [h.t0]; exact (hw n (by omega)).2
  have hv : s.mem.readW (F + BitVec.ofNat 64 (oSave + 8 * n)) 64 = v n := by rw [h.mem]; exact hsav n hn
  have hne := cs_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show oSave + 8 * n < 2048 by simp only [oSave]; omega) ha hin', Option.some.injEq,
    exists_eq_left', h.t0, hv]
  refine ⟨?_, fun i hi => ?_, fun r h0 hra hr => ?_, h.mem, h.rd, h.wr, h.sp, ?_⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e.symm hne.1]; exact h.t0
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : cs i ≠ cs n := fun e => absurd (cs_inj i (by omega) n hn e) (by omega)
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n hn)]
    exact h.others r h0 hra hr
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e.symm hne.2]; exact h.ra

/-- `restoreRegs`, from a state whose saved words hold `v` (`v 12` the return
address). -/
theorem restoreRegs_ok (sB : State) {F : Addr} {v : Nat → BitVec 64} (hsp : sB.sp = F) (hw : SaveW sB F)
    (hsav : ∀ i < 12, sB.mem.readW (off F (oSave + 8 * i)) 64 = v i)
    (hra : sB.mem.readW (off F (oSave + 96)) 64 = v 12) :
    WP isa (.block restoreRegs) sB fun s =>
      (∀ i < 12, s.gpr (cs i) = v i) ∧ s.gpr .ra = v 12 ∧
      (∀ r, r ≠ .t0 → r ≠ .ra → (∀ i < 12, r ≠ cs i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp := by
  rw [restoreRegs, WP.block_append_iff]
  have hl : InRegions ((sB.write .t0 sB.sp).rd ++ (sB.write .t0 sB.sp).wr)
      ((sB.write .t0 sB.sp).gpr .t0 + BitVec.ofNat 64 (oSave + 96)) 8 := by
    rw [rd_write, wr_write, gpr_write, ite_eq_left rfl, hsp]
    obtain ⟨r, hr, hc⟩ := (hw 12 (by decide)).1
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hal : ((sB.write .t0 sB.sp).gpr .t0 + BitVec.ofNat 64 (oSave + 96)).toNat % 8 = 0 := by
    rw [gpr_write, ite_eq_left rfl, hsp]; exact (hw 12 (by decide)).2
  have hlv : (sB.write .t0 sB.sp).mem.readW ((sB.write .t0 sB.sp).gpr .t0 + BitVec.ofNat 64 (oSave + 96)) 64 =
      v 12 := by
    rw [mem_write, gpr_write, ite_eq_left rfl, hsp]; exact hra
  refine WP.mono (Q := RI sB F v 0) ?_ fun s₁ h₁ => WP.mono (wp_range_flatMap (M := isa) (RI sB F v)
    (fun k s hk h => restore_step sB hw hsav hk h) 12 (Nat.le_refl _) s₁ h₁)
    fun s h => ⟨h.restored, h.ra, h.others, h.mem, h.rd, h.wr, h.sp⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero,
    exec_load_d (show oSave + 96 < 2048 by decide) hal hl, hlv, Option.some.injEq, exists_eq_left']
  refine ⟨by gsimp; exact hsp, fun _ h => absurd h (Nat.not_lt_zero _), fun r h0 hra _ => ?_, by gsimp,
    by gsimp, by gsimp, by gsimp, by gsimp⟩
  gsimp
  rw [ite_eq_right_iff.mpr fun e => absurd e hra, ite_eq_right_iff.mpr fun e => absurd e h0]

/-- A byte after a zero doubleword is written at an offset of the same base. -/
theorem writeW_zero_byte (m : Mem) (p : Addr) {a d : Nat} (ha : a < 2 ^ 32) (hd : d < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 a) (0 : BitVec 64)) (off p d) = if a ≤ d ∧ d < a + 8 then 0 else m (off p d) := by
  simp only [Mem.writeW, Mem.write, off]
  rw [VG.Offset.sub_toNat' p (by omega) (by omega)]
  split
  · split
    · rename_i h1 h2
      rw [ite_eq_left ⟨h1, by omega⟩]
      apply BitVec.eq_of_toNat_eq
      simp
    · rename_i h1 h2
      rw [ite_eq_right (by omega)]
  · split
    · omega
    · rename_i h1 h2
      rw [ite_eq_right (by omega)]

/-- `clearNonce`: the nonce's 32 octets := 0. -/
theorem clearNonce_ok (s : State) {F : Addr} (hF : F.toNat + frameBytes ≤ 2 ^ 64) (hsp : s.sp = F)
    (hw : Scr s (off F oNonce) 32) :
    WP isa (.block clearNonce) s fun t =>
      (t.gpr .t0 = F ∧ (∀ j < 32, t.mem (off F (oNonce + j)) = 0) ∧ Outside F oNonce 32 s.mem t.mem) ∧
        Keep [.t0, .t1] s t := by
  have hF' := hF
  simp only [frameBytes] at hF'
  have st : ∀ k < 4, InRegions s.wr (off F (oNonce + 8 * k)) 8 := fun k hk => by
    have := hw.st (d := 8 * k) (n := 8) (by omega)
    rwa [off_off] at this
  have al : ∀ k < 4, (off F (oNonce + 8 * k)).toNat % 8 = 0 := fun k hk => by
    have := hw.al8 (d := 8 * k) (by omega) (by omega)
    rwa [off_off] at this
  refine WP.keep _ ?_ (by decide) (by rfl)
  have s0 : InRegions s.wr (F + BitVec.ofNat 64 32) 8 := st 0 (by decide)
  have s1 : InRegions s.wr (F + BitVec.ofNat 64 40) 8 := st 1 (by decide)
  have s2 : InRegions s.wr (F + BitVec.ofNat 64 48) 8 := st 2 (by decide)
  have s3 : InRegions s.wr (F + BitVec.ofNat 64 56) 8 := st 3 (by decide)
  have a0 : (F + BitVec.ofNat 64 32).toNat % 8 = 0 := al 0 (by decide)
  have a1 : (F + BitVec.ofNat 64 40).toNat % 8 = 0 := al 1 (by decide)
  have a2 : (F + BitVec.ofNat 64 48).toNat % 8 = 0 := al 2 (by decide)
  have a3 : (F + BitVec.ofNat 64 56).toNat % 8 = 0 := al 3 (by decide)
  simp only [clearNonce, oNonce]
  brun [exec_addSp (show 0 < 2048 by decide), hsp, BitVec.add_zero, exec_li_zero, s0, s1, s2, s3, a0, a1, a2, a3]
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [writeW_zero_byte _ _ (a := 56) (d := 32 + j) (by omega) (by omega)]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 48) (d := 32 + j) (by omega) (by omega)]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 40) (d := 32 + j) (by omega) (by omega)]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 32) (d := 32 + j) (by omega) (by omega)]
    split
    · rfl
    · omega
  · have w := fun (m : Mem) (d : Nat) (h : d + 8 ≤ 2 ^ 64) => writeW_outside m F (d := d) (0 : BitVec 64) h
    exact ((((w _ 32 (by omega)).mono (by omega) (by omega)).trans ((w _ 40 (by omega)).mono (by omega) (by omega))).trans
      ((w _ 48 (by omega)).mono (by omega) (by omega))).trans ((w _ 56 (by omega)).mono (by omega) (by omega))

end VG.Proof.Dsa.RISCV64.Rnd
