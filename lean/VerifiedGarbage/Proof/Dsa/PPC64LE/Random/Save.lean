module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Random
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Env

/-!
# DSA on PPC64LE, randomized functions: saving and restoring the registers

In the frame at `F` (`r1`): `saveRegs_ok`, `saveRegs` stores `r14`–`r31` at
`F + oSave + 8 i` and the return address at `F + oLr`, changing memory only
there; `restoreRegs_ok`, `restoreRegs` loads them back.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

theorem nv_inj : ∀ i < 18, ∀ j < 18, nv i = nv j → i = j := by decide

theorem nv_ne0 : ∀ i < 18, nv i ≠ .r0 ∧ nv i ≠ .r12 := by decide

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (F : Addr) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  out : Outside F oSave (8 * 18) s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off F (oSave + 8 * i)) 64 = s₀.gpr (nv i)

theorem save_sep {F : Addr} (_hF : F.toNat + frameBytes ≤ 2 ^ 64) {i j : Nat} (hi : i < 18) (hj : j < 18)
    (h : i ≠ j) : Mem.Sep (off F (oSave + 8 * i)) 8 (off F (oSave + 8 * j)) 8 :=
  VG.Offset.sep F (by simp only [oSave]; omega) (by simp only [oSave]; omega) (by simp only [oSave]; omega)

theorem save_step (s₀ : State) {F : Addr} (hF : F.toNat + frameBytes ≤ 2 ^ 64) (h12 : s₀.gpr .r12 = F)
    (hin : ∀ i < 18, InRegions s₀.wr (off F (oSave + 8 * i)) 8) {n : Nat} (hn : n < 18) {s : State}
    (h : SI s₀ F n s) : WP isa (.block [.store .d (nv n) .r12 (oSave + 8 * n)]) s (SI s₀ F (n + 1)) := by
  have hw : s.gpr .r12 = F := by rw [h.gpr, h12]
  have hout : InRegions s.wr (s.gpr .r12 + BitVec.ofNat 64 (oSave + 8 * n)) 8 := by
    rw [h.wr, hw]; exact hin n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r12 ≠ .r0 by decide) (show oSave + 8 * n < 2 ^ 15 ∧ (oSave + 8 * n) % 4 = 0 by
      simp only [oSave]; omega) hout, Option.some.injEq, exists_eq_left', hw]
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr, ?_, fun i hi => ?_⟩
  · simp only [frameBytes] at hF
    exact h.out.trans ((writeW_outside s.mem F (d := oSave + 8 * n) _ (by simp only [oSave]; omega)).mono
      (by omega) (by omega))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (save_sep hF (by omega) hn (by omega)) (by decide)]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-- What `saveRegs` leaves, from `s₀`. -/
structure Saved (s₀ : State) (F : Addr) (s : State) : Prop where
  r12 : s.gpr .r12 = F
  others : ∀ r, r ≠ .r0 → r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  out : Outside F oSave (8 * 18 + 8) s₀.mem s.mem
  saved : ∀ i < 18, s.mem.readW (off F (oSave + 8 * i)) 64 = s₀.gpr (nv i)
  savedLr : s.mem.readW (off F oLr) 64 = s₀.lr

theorem saveRegs_ok (s₀ : State) {F : Addr} (hF : F.toNat + frameBytes ≤ 2 ^ 64) (hsp : s₀.sp = F)
    (hin : ∀ i < 19, InRegions s₀.wr (off F (oSave + 8 * i)) 8) :
    WP isa (.block saveRegs) s₀ (Saved s₀ F) := by
  have hF' := hF
  simp only [frameBytes] at hF'
  rw [saveRegs, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun s => s.gpr .r12 = F ∧ s.mem = s₀.mem)
    (by prun [exec_addSp (show 0 < 2 ^ 15 by decide), hsp, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a12, m1⟩, k1⟩ => ?_
  have hin1 : ∀ i < 18, InRegions s₁.wr (off F (oSave + 8 * i)) 8 := fun i hi => by
    rw [k1.wr]; exact hin i (by omega)
  refine WP.mono (wp_range_flatMap (M := isa) (SI s₁ F) (fun k s hk h => save_step s₁ hF a12 hin1 hk h) 18
    (Nat.le_refl _) s₁ ⟨rfl, rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s h => ?_
  have hw : s.gpr .r12 = F := by rw [h.gpr, a12]
  have hst : InRegions (s.write .r0 s.lr).wr ((s.write .r0 s.lr).gpr .r12 + BitVec.ofNat 64 oLr) 8 := by
    rw [wr_write, gpr_write, ite_eq_right_iff.mpr (fun e => by cases e), h.wr, k1.wr, hw]
    exact hin 18 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mflr,
    exec_store_d (show Reg.r12 ≠ .r0 by decide) (show oLr < 2 ^ 15 ∧ oLr % 4 = 0 by decide) hst,
    Option.some.injEq, exists_eq_left']
  have h12' : (s.write .r0 s.lr).gpr .r12 = F := by rw [gpr_write, ite_eq_right_iff.mpr (fun e => by cases e), hw]
  refine ⟨by gsimp; exact hw, fun r h0 h12 => ?_, by gsimp; rw [h.rd, k1.rd], by gsimp; rw [h.wr, k1.wr],
    by gsimp; rw [h.sp, k1.sp], by gsimp; rw [h.lr, k1.lr], ?_, fun i hi => ?_, ?_⟩
  · gsimp
    rw [ite_eq_right_iff.mpr (fun e => absurd e h0), h.gpr]
    exact k1.gpr r (by simp [h12])
  · simp only [mem_write, h12']
    rw [← m1]
    exact (h.out.mono (by omega) (by omega)).trans ((writeW_outside s.mem F (d := oLr) _ (by simp only [oLr]; omega)).mono
      (by simp only [oLr, oSave]; omega) (by simp only [oLr, oSave]; omega))
  · simp only [mem_write, h12']
    rw [Mem.readW_writeW_sep (VG.Offset.sep F (by simp only [oLr, oSave]; omega) (by simp only [oSave]; omega)
      (by simp only [oLr]; omega)) (by decide), h.saved i hi, k1.gpr _ (by have := nv_ne0 i hi; simp [this.2])]
  · simp only [mem_write, h12']
    rw [Mem.readW_writeW_self64]
    gsimp
    rw [h.lr, k1.lr]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (F : Addr) (v : Nat → BitVec 64) (lr : BitVec 64) (n : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = F
  restored : ∀ i < n, s.gpr (nv i) = v i
  others : ∀ r, r ≠ .r0 → r ≠ .r12 → (∀ i < 18, r ≠ nv i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = lr

theorem restore_step (sB : State) {F : Addr} {v : Nat → BitVec 64} {lr : BitVec 64}
    (hin : ∀ i < 18, InRegions (sB.rd ++ sB.wr) (off F (oSave + 8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off F (oSave + 8 * i)) 64 = v i)
    {n : Nat} (hn : n < 18) {s : State} (h : RI sB F v lr n s) :
    WP isa (.block [.load .d (nv n) .r12 (oSave + 8 * n)]) s (RI sB F v lr (n + 1)) := by
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 (oSave + 8 * n)) 8 := by
    rw [h.rd, h.wr, h.r12]; exact hin n hn
  have hv : s.mem.readW (F + BitVec.ofNat 64 (oSave + 8 * n)) 64 = v n := by rw [h.mem]; exact hsav n hn
  have hne := nv_ne0 n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r12 ≠ .r0 by decide) (show oSave + 8 * n < 2 ^ 15 ∧ (oSave + 8 * n) % 4 = 0 by
      simp only [oSave]; omega) hin', Option.some.injEq, exists_eq_left', h.r12, hv]
  refine ⟨?_, fun i hi => ?_, fun r h0 h12 hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e.symm hne.2]; exact h.r12
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : nv i ≠ nv n := fun e => absurd (nv_inj i (by omega) n hn e) (by omega)
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n hn)]
    exact h.others r h0 h12 hr

/-- `restoreRegs`, from a state whose saved words hold `v` and `lr`. -/
theorem restoreRegs_ok (sB : State) {F : Addr} {v : Nat → BitVec 64} {lr : BitVec 64} (hsp : sB.sp = F)
    (hin : ∀ i < 19, InRegions (sB.rd ++ sB.wr) (off F (oSave + 8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off F (oSave + 8 * i)) 64 = v i)
    (hlr : sB.mem.readW (off F oLr) 64 = lr) :
    WP isa (.block restoreRegs) sB fun s =>
      (∀ i < 18, s.gpr (nv i) = v i) ∧ s.lr = lr ∧
      (∀ r, r ≠ .r0 → r ≠ .r12 → (∀ i < 18, r ≠ nv i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp := by
  rw [restoreRegs, WP.block_append_iff]
  have hl : InRegions ((sB.write .r12 sB.sp).rd ++ (sB.write .r12 sB.sp).wr)
      ((sB.write .r12 sB.sp).gpr .r12 + BitVec.ofNat 64 oLr) 8 := by
    rw [rd_write, wr_write, gpr_write, ite_eq_left rfl, hsp]; exact hin 18 (by decide)
  have hlv : (sB.write .r12 sB.sp).mem.readW ((sB.write .r12 sB.sp).gpr .r12 + BitVec.ofNat 64 oLr) 64 = lr := by
    rw [mem_write, gpr_write, ite_eq_left rfl, hsp]; exact hlr
  refine WP.mono (Q := RI sB F v lr 0) ?_ fun s₁ h₁ => WP.mono (wp_range_flatMap (M := isa) (RI sB F v lr)
    (fun k s hk h => restore_step sB (fun i hi => hin i (by omega)) hsav hk h) 18 (Nat.le_refl _) s₁ h₁)
    fun s h => ⟨h.restored, h.lr, h.others, h.mem, h.rd, h.wr, h.sp⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addSp (show 0 < 2 ^ 15 by decide), BitVec.add_zero,
    exec_load_d (show Reg.r12 ≠ .r0 by decide) (show oLr < 2 ^ 15 ∧ oLr % 4 = 0 by decide) hl, hlv,
    exec_mtlr, Option.some.injEq, exists_eq_left']
  refine ⟨by gsimp; exact hsp, fun _ h => absurd h (Nat.not_lt_zero _), fun r h0 h12 _ => ?_, by gsimp,
    by gsimp, by gsimp, by gsimp, by gsimp⟩
  gsimp
  rw [ite_eq_right_iff.mpr fun e => absurd e h0, ite_eq_right_iff.mpr fun e => absurd e h12]

/-- A byte after a zero doubleword is written at an offset of the same base. -/
theorem writeW_zero_byte (m : Mem) (p : Addr) {a d : Nat} (ha : a < 2 ^ 32) (hd : d < 2 ^ 32) :
    (m.writeW (off p a) (BitVec.ofNat 64 0)) (off p d) = if a ≤ d ∧ d < a + 8 then 0 else m (off p d) := by
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
      (t.gpr .r12 = F ∧ (∀ j < 32, t.mem (off F (oNonce + j)) = 0) ∧ Outside F oNonce 32 s.mem t.mem) ∧
        Keep [.r0, .r12] s t := by
  have hF' := hF
  simp only [frameBytes] at hF'
  have st : ∀ k < 4, InRegions s.wr (off F (oNonce + 8 * k)) 8 := fun k hk => by
    have := hw.st (d := 8 * k) (n := 8) (by omega) (by decide)
    rwa [off_off] at this
  refine WP.keep _ ?_ (by decide)
  have s0 : InRegions s.wr (F + BitVec.ofNat 64 120) 8 := st 0 (by decide)
  have s1 : InRegions s.wr (F + BitVec.ofNat 64 128) 8 := st 1 (by decide)
  have s2 : InRegions s.wr (F + BitVec.ofNat 64 136) 8 := st 2 (by decide)
  have s3 : InRegions s.wr (F + BitVec.ofNat 64 144) 8 := st 3 (by decide)
  simp only [clearNonce, oNonce]
  prun [exec_addSp (show 0 < 2 ^ 15 by decide), hsp, BitVec.add_zero, s0, s1, s2, s3]
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [writeW_zero_byte _ _ (a := 144) (d := 120 + j) (by omega) (by omega)]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 136) (d := 120 + j) (by omega) (by omega)]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 128) (d := 120 + j) (by omega) (by omega)]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 120) (d := 120 + j) (by omega) (by omega)]
    split
    · rfl
    · omega
  · have w := fun (m : Mem) (d : Nat) (h : d + 8 ≤ 2 ^ 64) => writeW_outside m F (d := d) (BitVec.ofNat 64 0) h
    exact ((((w _ 120 (by omega)).mono (by omega) (by omega)).trans ((w _ 128 (by omega)).mono (by omega) (by omega))).trans
      ((w _ 136 (by omega)).mono (by omega) (by omega))).trans ((w _ 144 (by omega)).mono (by omega) (by omega))

end VG.Proof.Dsa.PPC64LE.Rnd
