module

public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.RISCV64.RndEnv
public import VerifiedGarbage.Impl.Dsa.RISCV64.RandomSign
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Dsa.RISCV64.Random
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes

/-! ### `Dsa.RISCV64.RSCtx`, which this module and modules that import it used -/

section

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

end

end

/-!
# Randomized DSA signing on RISC-V: the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Entry.lean`). `entry_ok`: in
the frame, `entry` saves `s0`–`s11` and `ra`, keeps `out`, `used` and the
digest's address in the frame, the key, the lengths, the tape and its
length in `s1`–`s4`, `vg_dsa_sign`'s arguments on the stack in the frame,
`s5 := 0`, `s6 := 8`, and zeroes the nonce (`Entered`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd

/-- The frame contains its offsets. -/
theorem frameR_contains {L : RL} {s₀ : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) {d n : Nat}
    (h : d + n ≤ frameBytes) : (frameR s₀).Contains (off L.F d) n := by
  have hF := hL.fnw
  simp only [frameR, hsp]
  exact VG.Offset.contains_base _ h (by simp only [frameBytes] at h; omega_using [h])

/-- The frame's offsets past it are the stack pointer's. -/
theorem F_add (L : RL) (d : Nat) : off L.F (frameBytes + d) = L.sp + BitVec.ofNat 64 d := by
  simp only [off, RL.F]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The octets of a region apart from the frame are kept by a change within it. -/
theorem bytes_outside {L : RL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : k ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  refine ho _ (.inr ?_)
  obtain hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega_using [hi]) (by omega_using [hk, hi])
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

/-- A word of a region apart from the frame is kept by a change within it. -/
theorem readW_outside {L : RL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : 8 ≤ k) (hk' : k ≤ 2 ^ 64) : m'.readW A 64 = m.readW A 64 := by
  refine Mem.readW_congr fun i hi => ho _ (.inr ?_)
  obtain hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega) (by omega_using [hi])
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

/-- The nonce is a working space of the frame. -/
theorem scr_nonce {L : RL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR s₀ :: s₀.wr) : Scr t (off L.F oNonce) 32 := by
  have hF := hL.fnw
  have ha := hL.fal
  simp only [frameBytes] at hF
  refine ⟨⟨(frameR s₀).base, oNonce, frameBytes, by rw [hw]; exact List.mem_cons_self .., ?_, by decide,
    by decide⟩, ?_, ?_⟩
  · simp only [hsp]
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega_using [hF]
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega_using [ha]

/-- A word of the frame is writable and aligned. -/
theorem frame_word {L : RL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR s₀ :: s₀.wr) {d : Nat} (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) :
    InRegions t.wr (off L.F d) 8 ∧ (off L.F d).toNat % 8 = 0 := by
  have hF := hL.fnw
  have ha := hL.fal
  refine ⟨⟨_, by rw [hw]; exact List.mem_cons_self .., frameR_contains hL hsp hd⟩, ?_⟩
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by simp only [frameBytes] at hd; omega_using [hd])]
  simp only [frameBytes] at hF hd
  omega_using [h8, ha]

/-- The lengths in `s2`. -/
theorem lens_entry (pl ql : BitVec 64) (hq : ql.toNat < 65536) :
    ql <<< 16 + pl = lens pl.toNat ql.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show ql.toNat * 2 ^ 16 < 2 ^ 64 by omega_using [hq])]
  omega_using []

/-- A word of the frame past a write elsewhere in it. -/
theorem word_wW (m : Mem) (F : Addr) {d d' : Nat} (v : BitVec 64) (hd : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (h : d' + 8 ≤ 2 ^ 64) (h' : d + 8 ≤ 2 ^ 64) :
    (m.writeW (off F d') v).readW (off F d) 64 = m.readW (off F d) 64 :=
  (writeW_outside m F v h).word hd h'

/-- What `entry` leaves. -/
structure Entered (L : RL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 0
  s6 : t.gpr .s6 = BitVec.ofNat 64 8
  nonce : ∀ j < 32, t.mem (off L.F (oNonce + j)) = 0

theorem entry_ok {s₀ : State} (h : rsContract.pre s₀) :
    WP isa (.block entry) (allocd frameBytes s₀) (Entered (rlOf s₀) s₀) := by
  obtain hL := rlOf_ok h
  generalize hLd : rlOf s₀ = L at hL
  obtain hsp : s₀.sp = L.sp := by rw [← hLd]; rfl
  have hF := hL.fnw
  have hF' := hF
  simp only [frameBytes] at hF'
  have hspT := hL.spTop
  have hsp16 := hL.sp16
  obtain hE : (allocd frameBytes s₀).sp = L.F := by simp only [allocd, hsp]
  have hwA : (allocd frameBytes s₀).wr = frameR s₀ :: s₀.wr := rfl
  obtain hsw : SaveW (allocd frameBytes s₀) L.F := fun i hi =>
    frame_word hL hsp hwA (by simp only [oSave, frameBytes]; omega_using [hi]) (by simp only [oSave]; omega_using [])
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveRegs_ok _ hF hE hsw) fun t₁ h₁ => ?_
  -- The call's data.
  obtain eo : s₀.gpr .a0 = L.out := by rw [← hLd]; rfl
  obtain eu : s₀.gpr .a2 = L.used := by rw [← hLd]; rfl
  obtain ek : s₀.gpr .a3 = L.key := by rw [← hLd]; rfl
  obtain ed : s₀.gpr .a7 = L.dig := by rw [← hLd]; rfl
  obtain el : s₀.gpr .a6 <<< 16 + s₀.gpr .a5 = lens L.pl L.ql := by
    rw [lens_entry _ _ (by have := hL.ql; rw [← hLd] at this; simp only [rlOf] at this; omega_using [this])]
    rw [← hLd]; rfl
  obtain a0 : stackArg s₀ 0 = BitVec.ofNat 64 L.dl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain a1 : stackArg s₀ 1 = L.rand := by rw [← hLd]; rfl
  obtain a2 : stackArg s₀ 2 = BitVec.ofNat 64 L.rl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain a3 : stackArg s₀ 3 = L.scr := by rw [← hLd]; rfl
  obtain a4 : stackArg s₀ 4 = BitVec.ofNat 64 L.sl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain hr : ∀ r, r ≠ .t0 → t₁.gpr r = s₀.gpr r := fun r h0 => h₁.others r h0
  obtain o₁ : Outside L.F 0 frameBytes s₀.mem t₁.mem :=
    h₁.out.mono (by omega_using []) (by simp only [oSave, frameBytes]; omega_using [])
  -- The frame's words of `out`, `used` and the digest.
  obtain fw := fun (d : Nat) (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) => frame_word hL hsp (t := t₁)
    (by rw [h₁.wr]; rfl) hd h8
  obtain ⟨w64, l64⟩ := fw 64 (by decide) (by decide)
  obtain ⟨w72, l72⟩ := fw 72 (by decide) (by decide)
  obtain ⟨w80, l80⟩ := fw 80 (by decide) (by decide)
  obtain ⟨w0, l0⟩ := fw 0 (by decide) (by decide)
  obtain ⟨w8, l8⟩ := fw 8 (by decide) (by decide)
  obtain ⟨w16, l16⟩ := fw 16 (by decide) (by decide)
  rw [show ([.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .store .d .a7 .t0 oDig, .addi .s1 .a3 0,
      .shift .sll .d .s2 .a6 16, .add .s2 .s2 .a5, .addSp .t6 frameBytes, .load .d .s3 .t6 8,
      .load .d .s4 .t6 16, .load .d .t1 .t6 0, .load .d .t2 .t6 24, .load .d .t3 .t6 32, .store .d .t1 .t0 0,
      .store .d .t2 .t0 8, .store .d .t3 .t0 16, .li .s5 0, .li .s6 8] : List Instr) =
    [.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .store .d .a7 .t0 oDig, .addi .s1 .a3 0,
      .shift .sll .d .s2 .a6 16, .add .s2 .s2 .a5] ++ [.addSp .t6 frameBytes, .load .d .s3 .t6 8,
      .load .d .s4 .t6 16, .load .d .t1 .t6 0, .load .d .t2 .t6 24, .load .d .t3 .t6 32, .store .d .t1 .t0 0,
      .store .d .t2 .t0 8, .store .d .t3 .t0 16, .li .s5 0, .li .s6 8] from rfl, WP.block_append_iff]
  refine WP.mono (wp_sp (WP.keep [.s1, .s2] (Q := fun t =>
    t.gpr .s1 = L.key ∧ t.gpr .s2 = lens L.pl L.ql ∧
      t.mem = ((t₁.mem.writeW (off L.F oOut) L.out).writeW (off L.F oUsed) L.used).writeW (off L.F oDig) L.dig)
    (by
      brun [h₁.t0, hr .a0 (by decide), hr .a2 (by decide), hr .a3 (by decide), hr .a5 (by decide),
        hr .a6 (by decide), hr .a7 (by decide), eo, eu, ek, ed, el, oOut, oUsed, oDig, w64, l64, w72, l72, w80, l80,
        exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]) (by decide) (by rfl))) fun t₂ ⟨⟨⟨b1, b2, bm⟩, k₂⟩, sp₂⟩ => ?_
  obtain ⟨_, _, hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstk, _⟩ := h
  obtain hrd' : rsStackArgs s₀ ∈ s₀.rd := by rw [hrd]; simp
  obtain o₂ : Outside L.F 0 frameBytes s₀.mem t₂.mem := by
    rw [bm]
    refine o₁.trans (((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_).trans
      (((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_).trans
        ((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_))) <;> decide
  obtain hstk' : L.frR.Disjoint (rsStackArgs s₀) := by
    simpa only [RL.frR, RL.F, hsp, show frameBytes = rsStack from rfl] using hstk
  obtain hsa0 : stackArgAddr s₀ 0 = L.sp := by simp only [stackArgAddr, hsp]; exact BitVec.add_zero _
  obtain sw : ∀ i < 5, t₂.mem.readW (off L.F (192 + 8 * i)) 64 = stackArg s₀ i ∧
      InRegions (t₂.rd ++ t₂.wr) (off L.F (192 + 8 * i)) 8 ∧
      (off L.F (192 + 8 * i)).toNat % 8 = 0 := by
    intro i hi
    rw [show 192 + 8 * i = frameBytes + 8 * i from rfl, F_add]
    obtain hsub : Region.Sub ⟨L.sp + BitVec.ofNat 64 (8 * i), 8⟩ (rsStackArgs s₀) := by
      simp only [rsStackArgs, hsa0]; exact VG.Offset.sub_base _ (by omega_using [hi])
    refine ⟨?_, ⟨_, List.mem_append_left _ (by rw [k₂.2.1, h₁.rd]; exact hrd'), ?_⟩, ?_⟩
    · rw [readW_outside o₂ (hstk'.sub_right hsub) (by omega_using []) (by omega_using [])]
      simp only [stackArg, stackArgAddr, hsp]
    · simp only [rsStackArgs, hsa0]; exact VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega_using [hi])]; omega_using [hsp16]
  obtain ⟨r0, i0, al0⟩ := sw 0 (by decide)
  obtain ⟨r1, i1, al1⟩ := sw 1 (by decide)
  obtain ⟨r2, i2, al2⟩ := sw 2 (by decide)
  obtain ⟨r3, i3, al3⟩ := sw 3 (by decide)
  obtain ⟨r4, i4, al4⟩ := sw 4 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at r0 i0 al0 r1 i1 al1 r2 i2 al2 r3 i3 al3 r4 i4 al4
  have hF192 : L.F + BitVec.ofNat 64 192 = off L.F 192 := rfl
  obtain sp₂' : t₂.sp = L.F := by rw [sp₂, h₁.sp, hE]
  obtain t0₂ : t₂.gpr .t0 = L.F := by rw [k₂.1 .t0 (by decide), h₁.t0]
  have wr₂ : t₂.wr = t₁.wr := k₂.2.2
  rw [← wr₂] at w0 w8 w16
  refine WP.mono (wp_sp (WP.keep [.t6, .s3, .s4, .t1, .t2, .t3, .s5, .s6] (Q := fun t =>
    t.gpr .s3 = L.rand ∧ t.gpr .s4 = BitVec.ofNat 64 L.rl ∧ t.gpr .s5 = BitVec.ofNat 64 0 ∧
      t.gpr .s6 = BitVec.ofNat 64 8 ∧
      t.mem = ((t₂.mem.writeW (off L.F 0) (BitVec.ofNat 64 L.dl)).writeW (off L.F 8) L.scr).writeW
        (off L.F 16) (BitVec.ofNat 64 L.sl))
    (by
      brun [exec_addSp (show 192 < 2048 by decide), exec_li_zero, exec_li_lit (show 8 < 2048 by decide), sp₂', t0₂, hF192, frameBytes, r0, i0, al0, r1, i1, al1, r2, i2, al2, r3, i3, al3, r4, i4, al4,
        a0, a1, a2, a3, a4, w0, l0, w8, l8, w16, l16]
      rfl) (by decide) (by rfl))) fun t₃ ⟨⟨⟨c3, c4, c5, c6, cm⟩, k₃⟩, sp₃⟩ => ?_
  obtain sp₃' : t₃.sp = L.F := by rw [sp₃, sp₂']
  obtain wr₃ : t₃.wr = frameR s₀ :: s₀.wr := by rw [k₃.2.2, wr₂, h₁.wr]; rfl
  refine WP.mono (wp_sp (clearNonce_ok t₃ hF sp₃' (scr_nonce hL hsp wr₃)))
    fun t₄ ⟨⟨⟨_, nz, o₄⟩, k₄⟩, sp₄⟩ => ?_
  -- Memory.
  obtain o₃ : Outside L.F 0 24 t₂.mem t₃.mem := by
    rw [cm]
    exact ((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) (by decide)).trans
      (((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) (by decide)).trans
        ((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) (by decide)))
  obtain o₂' : Outside L.F 64 24 t₁.mem t₂.mem := by
    rw [bm]
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      (((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
        ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)))
  obtain o₁₄ : Outside L.F 0 88 t₁.mem t₄.mem :=
    (o₂'.mono (Nat.zero_le _) (by decide)).trans ((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce]; omega_using [])))
  obtain o₀₄ : Outside L.F 0 frameBytes s₀.mem t₄.mem :=
    o₂.trans (((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce, frameBytes]; omega_using []))))
  obtain w₃ : ∀ d, d + 8 ≤ 32 → t₄.mem.readW (off L.F d) 64 = t₃.mem.readW (off L.F d) 64 := fun d hd =>
    o₄.word (by simp only [oNonce]; omega_using [hd]) (by omega_using [hd])
  obtain w₄ : ∀ d, 64 ≤ d → d + 8 ≤ 88 → t₄.mem.readW (off L.F d) 64 = t₂.mem.readW (off L.F d) 64 :=
    fun d hd hd' => (o₄.word (by simp only [oNonce]; omega_using [hd]) (by omega_using [hd'])).trans
      (o₃.word (by omega_using [hd]) (by omega_using [hd']))
  obtain gk : ∀ r, r ∉ [Reg.t6, .s3, .s4, .t1, .t2, .t3, .s5, .s6] → r ∉ [Reg.t0, .t1] →
      t₄.gpr r = t₃.gpr r := fun r _ h => k₄.1 r h
  obtain g2 : ∀ r, r ∉ [Reg.t6, .s3, .s4, .t1, .t2, .t3, .s5, .s6] → r ∉ [Reg.t0, .t1] →
      t₄.gpr r = t₂.gpr r := fun r h h' => (k₄.1 r h').trans (k₃.1 r h)
  refine ⟨⟨by rw [sp₄, sp₃'], by rw [k₄.2.1, k₃.2.1, k₂.2.1, h₁.rd]; rfl,
    by rw [k₄.2.2, wr₃], by rw [g2 _ (by decide) (by decide), b1], by rw [g2 _ (by decide) (by decide), b2],
    by rw [k₄.1 _ (by decide), c3], by rw [k₄.1 _ (by decide), c4], fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, by rw [k₄.1 _ (by decide), c5], by rw [k₄.1 _ (by decide), c6], nz⟩
  · exact (o₁₄.word (by simp only [oSave]; omega_using []) (by simp only [oSave]; omega_using [hi])).trans (h₁.saved i hi)
  · exact (o₁₄.word (by simp only [oSave]; omega_using []) (by simp only [oSave]; omega_using [])).trans h₁.savedRa
  · rw [w₃ 0 (by decide), cm, word_wW _ _ _ (by decide) (by decide) (by decide),
      word_wW _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [w₃ 8 (by decide), cm, word_wW _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [w₃ 16 (by decide), cm, Mem.readW_writeW_self64]
  · rw [w₄ oOut (by decide) (by decide), bm, word_wW _ _ _ (by decide) (by decide) (by decide),
      word_wW _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [w₄ oUsed (by decide) (by decide), bm, word_wW _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [w₄ oDig (by decide) (by decide), bm, Mem.readW_writeW_self64]
  · exact bytes_outside o₀₄ hL.dFK (by have := hL.nwKey; omega_using [this])
  · exact bytes_outside o₀₄ hL.dFD (by have := hL.nwDig; omega_using [this])
  · exact bytes_outside o₀₄ hL.dFR (by have := hL.nwRand; omega_using [this])

end VG.Proof.Dsa.RISCV64.RS
