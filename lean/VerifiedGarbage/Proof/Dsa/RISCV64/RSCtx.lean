module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RndEnv
public import VerifiedGarbage.Impl.Dsa.RISCV64.RandomSign
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Dsa.RISCV64.Random
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Mont.Words
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes

/-! ### `Dsa.RISCV64.RndSave`, which only this module used -/

section

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
  VG.Offset.sep F (by simp only [oSave]; omega_using [h]) (by simp only [oSave]; omega_using [hi]) (by simp only [oSave]; omega_using [hj])

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
    rw [h.wr, h0']; exact (hw n (by omega_using [hn])).1
  have ha : (s.gpr .t0 + BitVec.ofNat 64 (oSave + 8 * n)).toNat % 8 = 0 := by
    rw [h0']; exact (hw n (by omega_using [hn])).2
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show oSave + 8 * n < 2048 by simp only [oSave]; omega_using [hn]) ha hout, Option.some.injEq,
    exists_eq_left', h0']
  refine ⟨h.gpr, h.rd, h.wr, h.sp, ?_, fun i hi => ?_⟩
  · exact h.out.trans ((writeW_outside s.mem F (d := oSave + 8 * n) _ (by simp only [oSave]; omega_using [hn])).mono
      (by omega_using []) (by omega_using [hn]))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (save_sep (by omega_arith) (by omega_using [hn]) (by omega_using [hi])) (by decide)]
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
    exact (h.out.mono (by omega_using []) (by omega_using [])).trans
      ((writeW_outside s.mem F (d := oSave + 96) _ (by simp only [oSave]; omega_using [])).mono
        (by simp only [oSave]; omega_using []) (by simp only [oSave]; omega_using []))
  · show (s.mem.writeW (s.gpr .t0 + BitVec.ofNat 64 (oSave + 96)) (s.gpr .ra)).readW _ 64 = _
    rw [h0, show F + BitVec.ofNat 64 (oSave + 96) = off F (oSave + 8 * 12) from rfl,
      Mem.readW_writeW_sep (save_sep (by omega_using [hi]) (by decide) (by omega_using [hi])) (by decide), h.saved i hi,
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
    obtain ⟨r, hr, hc⟩ := (hw n (by omega_using [hn])).1
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .t0 + BitVec.ofNat 64 (oSave + 8 * n)).toNat % 8 = 0 := by
    rw [h.t0]; exact (hw n (by omega_using [hn])).2
  have hv : s.mem.readW (F + BitVec.ofNat 64 (oSave + 8 * n)) 64 = v n := by rw [h.mem]; exact hsav n hn
  have hne := cs_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show oSave + 8 * n < 2048 by simp only [oSave]; omega_using [hn]) ha hin', Option.some.injEq,
    exists_eq_left', h.t0, hv]
  refine ⟨?_, fun i hi => ?_, fun r h0 hra hr => ?_, h.mem, h.rd, h.wr, h.sp, ?_⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e.symm hne.1]; exact h.t0
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : cs i ≠ cs n := fun e => absurd (cs_inj i (by omega_arith) n hn e) (by omega_using [hi])
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
  rw [VG.Offset.sub_toNat' p (by omega_using [ha]) (by omega_using [hd])]
  split
  · split
    · rename_i h1 h2
      rw [ite_eq_left ⟨h1, by omega_using [h2]⟩]
      apply BitVec.eq_of_toNat_eq
      simp
    · rename_i h1 h2
      rw [ite_eq_right (by omega_using [h2])]
  · split
    · omega
    · rename_i h1 h2
      rw [ite_eq_right (by omega_using [h1])]

/-- `clearNonce`: the nonce's 32 octets := 0. -/
theorem clearNonce_ok (s : State) {F : Addr} (hF : F.toNat + frameBytes ≤ 2 ^ 64) (hsp : s.sp = F)
    (hw : Scr s (off F oNonce) 32) :
    WP isa (.block clearNonce) s fun t =>
      (t.gpr .t0 = F ∧ (∀ j < 32, t.mem (off F (oNonce + j)) = 0) ∧ Outside F oNonce 32 s.mem t.mem) ∧
        Keep [.t0, .t1] s t := by
  have hF' := hF
  simp only [frameBytes] at hF'
  have st : ∀ k < 4, InRegions s.wr (off F (oNonce + 8 * k)) 8 := fun k hk => by
    have := hw.st (d := 8 * k) (n := 8) (by omega_using [hk])
    rwa [off_off] at this
  have al : ∀ k < 4, (off F (oNonce + 8 * k)).toNat % 8 = 0 := fun k hk => by
    have := hw.al8 (d := 8 * k) (by omega_using [hk]) (by omega_using [])
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
  · rw [writeW_zero_byte _ _ (a := 56) (d := 32 + j) (by omega_using []) (by omega_using [hj])]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 48) (d := 32 + j) (by omega_using []) (by omega_using [hj])]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 40) (d := 32 + j) (by omega_using []) (by omega_using [hj])]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 32) (d := 32 + j) (by omega_using []) (by omega_using [hj])]
    split
    · rfl
    · omega
  · have w := fun (m : Mem) (d : Nat) (h : d + 8 ≤ 2 ^ 64) => writeW_outside m F (d := d) (0 : BitVec 64) h
    exact ((((w _ 32 (by omega_using [])).mono (by omega_using []) (by omega_using [])).trans ((w _ 40 (by omega_using [])).mono (by omega_using []) (by omega_using []))).trans
      ((w _ 48 (by omega_using [])).mono (by omega_using []) (by omega_using []))).trans ((w _ 56 (by omega_using [])).mono (by omega_using []) (by omega_using []))

end VG.Proof.Dsa.RISCV64.Rnd

end

end

/-!
# Randomized DSA signing on RISC-V: the contract on the registers, and the frame's state

As on PPC64LE (`Proof/Dsa/PPC64LE/Random/Save.lean` and `Ctx.lean`).
`rsContract`: `vg_dsa_sign_random(out = a0, out_len = a1, used = a2,
key = a3, key_len = a4, p_len = a5, q_len = a6, digest = a7, digest_len,
rand, rand_len, scratch, scratch_len)`, the last five on the stack. `RL`: a
call's public data (`rlOf`), `Ctx`: what holds in the frame's body: the
registers `entry` sets, the saved registers and the callee's arguments in
the frame, and the key, the digest and the tape unchanged. A change of
memory in `out`, `scratch` or the nonce keeps it (`Ctx.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev rsStack : Nat := 192

/-- The arguments on the stack. -/
abbrev rsStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

/-- The result `randomSignBytes` gives, on entry. -/
def rsRes (s : State) : Spec.Dsa.RandomSignResult :=
  Spec.Dsa.randomSignBytes (s.gpr .a5).toNat (s.gpr .a6).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)

/-- `vg_dsa_sign_random`, on the registers and the stack. -/
def rsContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let used : Region := ⟨s.gpr .a2, 8⟩
    let key : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let dg : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
    let rnd : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 rsStack, rsStack⟩
    rsStack ≤ s.sp.toNat ∧ s.sp.toNat + 8 * 5 ≤ 2 ^ 64 ∧
      s.rd = [key, dg, rnd, rsStackArgs s] ∧ s.wr = [out, used, scr] ∧
      out.Disjoint used ∧ out.Disjoint key ∧ out.Disjoint dg ∧ out.Disjoint rnd ∧ out.Disjoint scr ∧
      out.Disjoint (rsStackArgs s) ∧ used.Disjoint key ∧ used.Disjoint dg ∧ used.Disjoint rnd ∧
      used.Disjoint scr ∧ used.Disjoint (rsStackArgs s) ∧ key.Disjoint scr ∧ dg.Disjoint scr ∧
      rnd.Disjoint scr ∧ scr.Disjoint (rsStackArgs s) ∧
      stk.Disjoint out ∧ stk.Disjoint used ∧ stk.Disjoint key ∧ stk.Disjoint dg ∧ stk.Disjoint rnd ∧
      stk.Disjoint scr ∧ stk.Disjoint (rsStackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a5).toNat (s.gpr .a6).toNat ∧
      (s.gpr .a1).toNat = 2 * (s.gpr .a6).toNat ∧
      (s.gpr .a4).toNat = 3 * (s.gpr .a5).toNat + 2 * (s.gpr .a6).toNat ∧
      Spec.Dsa.randomSignScratchWords (s.gpr .a5).toNat ≤ (stackArg s 4).toNat ∧
      (s.gpr .a2).toNat % 8 = 0 ∧ (stackArg s 3).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = (rsRes s).status ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat =
        (rsRes s).signature.getD (List.replicate (s.gpr .a1).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a2) 1 = [BitVec.ofNat 64 (rsRes s).used]
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
      stackArg s₁ 4 = stackArg s₂ 4 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .a5).toNat (s₁.gpr .a6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (s₁.gpr .a4).toNat) ++ [(rsRes s₁).status, (rsRes s₁).used] ++
          (rsRes s₁).trace =
      Spec.Dsa.publicBytesLeak (s₂.gpr .a5).toNat (s₂.gpr .a6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (s₂.gpr .a4).toNat) ++ [(rsRes s₂).status, (rsRes s₂).used] ++
          (rsRes s₂).trace

/-- A call's public data. -/
structure RL where
  sp : Addr
  out : Addr
  used : Addr
  key : Addr
  dig : Addr
  rand : Addr
  scr : Addr
  pl : Nat
  ql : Nat
  dl : Nat
  rl : Nat
  sl : Nat

def rlOf (s : State) : RL :=
  ⟨s.sp, s.gpr .a0, s.gpr .a2, s.gpr .a3, s.gpr .a7, stackArg s 1, stackArg s 3, (s.gpr .a5).toNat,
    (s.gpr .a6).toNat, (stackArg s 0).toNat, (stackArg s 2).toNat, (stackArg s 4).toNat⟩

namespace RL

variable (L : RL)

abbrev F : Addr := L.sp - BitVec.ofNat 64 frameBytes
abbrev kl : Nat := 3 * L.pl + 2 * L.ql
abbrev outR : Region := ⟨L.out, 2 * L.ql⟩
abbrev usedR : Region := ⟨L.used, 8⟩
abbrev keyR : Region := ⟨L.key, L.kl⟩
abbrev digR : Region := ⟨L.dig, L.dl⟩
abbrev randR : Region := ⟨L.rand, L.rl⟩
abbrev scrR : Region := ⟨L.scr, L.sl * 8⟩
abbrev frR : Region := ⟨L.F, frameBytes⟩
/-- The nonce. -/
abbrev nR : Region := ⟨off L.F oNonce, 32⟩

end RL

/-- What the precondition says of a call's data. -/
structure RL.Ok (L : RL) : Prop where
  lv : Spec.Dsa.lengthsValid L.pl L.ql
  sw : 16 * L.pl + 64 ≤ L.sl
  spF : frameBytes ≤ L.sp.toNat
  spTop : L.sp.toNat + 40 ≤ 2 ^ 64
  sp16 : L.sp.toNat % 16 = 0
  alU : L.used.toNat % 8 = 0
  alS : L.scr.toNat % 8 = 0
  nwOut : L.out.toNat + 2 * L.ql ≤ 2 ^ 64
  nwUsed : L.used.toNat + 8 ≤ 2 ^ 64
  nwKey : L.key.toNat + L.kl ≤ 2 ^ 64
  nwDig : L.dig.toNat + L.dl ≤ 2 ^ 64
  nwRand : L.rand.toNat + L.rl ≤ 2 ^ 64
  nwScr : L.scr.toNat + L.sl * 8 ≤ 2 ^ 64
  dl : L.dl < 2 ^ 64
  rl : L.rl < 2 ^ 64
  sl : L.sl < 2 ^ 64
  dOU : L.outR.Disjoint L.usedR
  dOK : L.outR.Disjoint L.keyR
  dOD : L.outR.Disjoint L.digR
  dOR : L.outR.Disjoint L.randR
  dOS : L.outR.Disjoint L.scrR
  dUK : L.usedR.Disjoint L.keyR
  dUD : L.usedR.Disjoint L.digR
  dUR : L.usedR.Disjoint L.randR
  dUS : L.usedR.Disjoint L.scrR
  dKS : L.keyR.Disjoint L.scrR
  dDS : L.digR.Disjoint L.scrR
  dRS : L.randR.Disjoint L.scrR
  dFO : L.frR.Disjoint L.outR
  dFU : L.frR.Disjoint L.usedR
  dFK : L.frR.Disjoint L.keyR
  dFD : L.frR.Disjoint L.digR
  dFR : L.frR.Disjoint L.randR
  dFS : L.frR.Disjoint L.scrR

theorem rlOf_ok {s : State} (h : rsContract.pre s) : (rlOf s).Ok := by
  obtain ⟨hF, hT, -, -, dOU, dOK, dOD, dOR, dOS, -, dUK, dUD, dUR, dUS, -, dKS, dDS, dRS, -,
    dFO, dFU, dFK, dFD, dFR, dFS, -, nO, nU, nK, nD, nR, nS, lv, hol, hkl, hsw, alU, alS, sp16⟩ := h
  simp only [Spec.Dsa.randomSignScratchWords, Spec.Dsa.scratchWords] at hsw
  have e4 : 2 * (s.gpr .a6).toNat = (s.gpr .a1).toNat := hol.symm
  have e7 : 3 * (s.gpr .a5).toNat + (s.gpr .a1).toNat = (s.gpr .a4).toNat := by omega_using [hol, hkl]
  refine ⟨lv, hsw, hF, hT, sp16, alU, alS, ?_, nU, ?_, nD, nR, nS, (stackArg s 0).isLt, (stackArg s 2).isLt,
    (stackArg s 4).isLt, ?_, ?_, ?_, ?_, ?_, ?_, dUD, dUR, dUS, ?_, dDS, dRS, ?_, dFU, ?_, dFD, dFR, dFS⟩ <;>
  simp only [RL.outR, RL.keyR, RL.kl, RL.frR, RL.F, rlOf, e4, e7]
  · exact nO
  · exact nK
  · exact dOU
  · exact dOK
  · exact dOD
  · exact dOR
  · exact dOS
  · exact dUK
  · exact dKS
  · exact dFO
  · exact dFK

namespace RL.Ok

variable {L : RL} (hL : L.Ok)
include hL

theorem ql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem pl : L.pl = 128 ∨ L.pl = 256 ∨ L.pl = 384 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem F_toNat : L.F.toNat = L.sp.toNat - frameBytes := by
  have h1 := hL.spF
  have h2 := L.sp.isLt
  simp only [RL.F, frameBytes] at h1 ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [h1]

theorem fnw : L.F.toNat + frameBytes ≤ 2 ^ 64 := by
  have := hL.F_toNat; have := hL.spF; have := hL.spTop; omega_arith

theorem fal : L.F.toNat % 8 = 0 := by
  have := hL.F_toNat; have := hL.spF; have := hL.sp16; simp only [frameBytes] at *; omega_arith

omit hL in
/-- A range of the frame is apart from a region apart from the frame. -/
theorem frame_disj {r : Region} (hd : L.frR.Disjoint r) {d n : Nat} (h : d + n ≤ frameBytes) :
    (⟨off L.F d, n⟩ : Region).Disjoint r :=
  hd.sub_left (VG.Offset.sub_base _ h)

end RL.Ok

/-- The frame's region. -/
abbrev frameR (s₀ : State) : Region := ⟨s₀.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩

/-- In the frame's body. -/
structure Ctx (L : RL) (s₀ : State) (t : State) : Prop where
  sp : t.sp = L.F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR s₀ :: s₀.wr
  s1 : t.gpr .s1 = L.key
  s2 : t.gpr .s2 = lens L.pl L.ql
  s3 : t.gpr .s3 = L.rand
  s4 : t.gpr .s4 = BitVec.ofNat 64 L.rl
  sav : ∀ i < 12, t.mem.readW (off L.F (oSave + 8 * i)) 64 = s₀.gpr (cs i)
  ra : t.mem.readW (off L.F (oSave + 96)) 64 = s₀.gpr .ra
  a0 : t.mem.readW (off L.F 0) 64 = BitVec.ofNat 64 L.dl
  a1 : t.mem.readW (off L.F 8) 64 = L.scr
  a2 : t.mem.readW (off L.F 16) 64 = BitVec.ofNat 64 L.sl
  out : t.mem.readW (off L.F oOut) 64 = L.out
  used : t.mem.readW (off L.F oUsed) 64 = L.used
  dig : t.mem.readW (off L.F oDig) 64 = L.dig
  key : Spec.Rsa.bytesAt t.mem L.key L.kl = Spec.Rsa.bytesAt s₀.mem L.key L.kl
  digB : Spec.Rsa.bytesAt t.mem L.dig L.dl = Spec.Rsa.bytesAt s₀.mem L.dig L.dl
  rand : Spec.Rsa.bytesAt t.mem L.rand L.rl = Spec.Rsa.bytesAt s₀.mem L.rand L.rl

/-- The registers `Ctx` fixes. -/
def ctxRegs : List Reg := [.s1, .s2, .s3, .s4]

/-- The octets of a region apart from the regions a change is within are kept. -/
theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {A : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨A, k⟩ : Region).Disjoint r) (hk : k ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  exact hf.bytes (R := ⟨A, k⟩) hd hk hi

/-- A change of memory in `out`, `scratch` or the nonce, with the registers
of `Ctx` kept, keeps `Ctx`. -/
theorem Ctx.step {L : RL} {s₀ t t' : State} (hL : L.Ok) (h : Ctx L s₀ t) (hsp : t'.sp = t.sp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ ctxRegs, t'.gpr r = t.gpr r)
    (hf : Frame [L.outR, L.scrR, L.nR] t.mem t'.mem) : Ctx L s₀ t' := by
  have hF := hL.fnw
  simp only [frameBytes] at hF
  have fw : ∀ d, d + 8 ≤ frameBytes → (d + 8 ≤ oNonce ∨ oNonce + 32 ≤ d) →
      t'.mem.readW (off L.F d) 64 = t.mem.readW (off L.F d) 64 := fun d hd hn =>
    hf.readW (r := ⟨off L.F d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact RL.Ok.frame_disj hL.dFO hd
      · exact RL.Ok.frame_disj hL.dFS hd
      · exact VG.Offset.disjoint L.F (by simp only [oNonce] at hn ⊢; omega_using [hn]) (by simp only [frameBytes] at hd; omega_using [hd])
          (by simp only [oNonce]; omega_using [])) (by decide)
  have nr : ∀ {A : Addr} {k : Nat}, L.frR.Disjoint ⟨A, k⟩ → (⟨A, k⟩ : Region).Disjoint L.nR := fun hd =>
    (RL.Ok.frame_disj hd (d := oNonce) (n := 32) (by decide)).symm
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.s1,
    (hg _ (by decide)).trans h.s2, (hg _ (by decide)).trans h.s3, (hg _ (by decide)).trans h.s4,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega_using [hi]) (by simp only [oSave, oNonce]; omega_using [])).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.ra, (fw _ (by decide) (by decide)).trans h.a0,
    (fw _ (by decide) (by decide)).trans h.a1, (fw _ (by decide) (by decide)).trans h.a2,
    (fw _ (by decide) (by decide)).trans h.out, (fw _ (by decide) (by decide)).trans h.used,
    (fw _ (by decide) (by decide)).trans h.dig, ?_, ?_, ?_⟩
  · refine (bytes_frame hf (fun r hr => ?_) (by have := hL.nwKey; omega_using [this])).trans h.key
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOK.symm
    · exact hL.dKS
    · exact nr hL.dFK
  · refine (bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.dl)).trans h.digB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOD.symm
    · exact hL.dDS
    · exact nr hL.dFD
  · refine (bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.rl)).trans h.rand
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOR.symm
    · exact hL.dRS
    · exact nr hL.dFR

end VG.Proof.Dsa.RISCV64.RS
