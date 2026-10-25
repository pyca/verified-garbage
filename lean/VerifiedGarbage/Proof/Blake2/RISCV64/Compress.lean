module

import VerifiedGarbage.Proof.Blake2.RISCV64.Words
public import VerifiedGarbage.Proof.Blake2.RISCV64.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Blake2.RISCV64.Round

/-!
# BLAKE2 compression function on RISC-V

The structure of the PPC64LE proof (`VG.Proof.Blake2.PPC64LE`), with the hash
value and each block copied to the scratch space, rounded up to a multiple of
8 (`sb`), and the hash value copied back at the end: every word the rounds
read and write is an aligned word of the scratch space, at an offset of `sb`.
The copies a byte at a time are `cp_ok` (into the scratch space) and
`cpOut_ok` (back to the state), proven once for any words.
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64

open VG VG.RISCV64 VG.RISCV64.Align
open VG.Impl.Blake2.RISCV64 (sz wd ws lbb wreg T RT SB loOff hiOff fOff hOff mOff saved ldLE stLE)
open VG.Spec.Blake2 (Params Work Block HashValue)

/-! ## Words of the scratch space -/

theorem zB_dvd (z : Size) : 8 % zB z = 0 := by cases z <;> decide

/-- A word at an offset of an address that is a multiple of 8 is aligned. -/
theorem wal (z : Size) {p : Addr} (hp : p.toNat % 8 = 0) {d : Nat} (hd : d % zB z = 0) :
    (p + BitVec.ofNat 64 d).toNat % zB z = 0 :=
  al_add hp (zB_dvd z) hd

theorem dal {p : Addr} (hp : p.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) :
    (p + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  al_add hp (by decide) hd

/-- A word of the scratch space is unchanged by a write to another. -/
theorem cell_sep (p : Addr) (m : Mem) {w w' : Nat} (v : BitVec w') {d e : Nat}
    (h : d + w / 8 ≤ e ∨ e + w' / 8 ≤ d) (hd : d + w / 8 ≤ 4096) (he : e + w' / 8 ≤ 4096) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) w =
      m.readW (p + BitVec.ofNat 64 d) w :=
  Mem.readW_writeW_sep (Offset.sep p h (by omega) (by omega)) (by omega)

/-- A word of the scratch space outside a range of it that a frame names. -/
theorem cell_frame (p : Addr) {m m' : Mem} {e k : Nat} (hf : Frame [⟨p + BitVec.ofNat 64 e, k⟩] m m')
    {d w : Nat} (h : d + w / 8 ≤ e ∨ e + k ≤ d) (hd : d + w / 8 ≤ 4096) (he : e + k ≤ 4096) :
    m'.readW (p + BitVec.ofNat 64 d) w = m.readW (p + BitVec.ofNat 64 d) w :=
  hf.readW (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint p h (by omega) (by omega)) (by omega)

/-! ## The work vector's initialization -/

section Init
variable {z : Size} (P : Params z.bits)

/-- Words `0 … n-1` of the work vector `v` are in their registers. -/
def PVars (s : State) (v : Work z.bits) (n : Nat) : Prop :=
  ∀ k (hk : k < 16), k < n → (s.gpr (wreg k)).setWidth z.bits = (v[k]'(by omega))

theorem PVars.step {s s' : State} {v : Work z.bits} {n : Nat} (hn : n < 16) (h : PVars s v n)
    (hw : (s'.gpr (wreg n)).setWidth z.bits = (v[n]'(by omega)))
    (ho : ∀ k < 16, k ≠ n → s'.gpr (wreg k) = s.gpr (wreg k)) : PVars s' v (n + 1) := by
  intro k hk hkn
  by_cases e : k = n
  · subst e; exact hw
  · rw [ho k hk e]; exact h k hk (by omega)

/-- The scratch words the body reads, at `p`: the counter `N` (its low 64 bits,
and the bits above) and the flag word `fl`. -/
structure Scr (p : Addr) (N : Nat) (fl : BitVec 64) (s : State) : Prop where
  sb : s.gpr SB = p
  al : p.toNat % 8 = 0
  inLo : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 loOff) 8
  inHi : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 hiOff) 8
  inF : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 fOff) 8
  lo : s.mem.readW (p + BitVec.ofNat 64 loOff) 64 = BitVec.ofNat 64 N
  hi : s.mem.readW (p + BitVec.ofNat 64 hiOff) 64 = BitVec.ofNat 64 (N / 2 ^ 64)
  f : s.mem.readW (p + BitVec.ofNat 64 fOff) 64 = fl

/-- `Scr` after a block that kept `SB`, the memory and the regions. -/
theorem Scr.keep {p : Addr} {N : Nat} {fl : BitVec 64} {s s' : State} (h : Scr p N fl s)
    (hsb : s'.gpr SB = s.gpr SB) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Scr p N fl s' :=
  ⟨hsb.trans h.sb, h.al, by rw [hrd, hwr]; exact h.inLo, by rw [hrd, hwr]; exact h.inHi,
    by rw [hrd, hwr]; exact h.inF, by rw [hm]; exact h.lo, by rw [hm]; exact h.hi,
    by rw [hm]; exact h.f⟩

theorem lds_ok (s : State) (p : Addr) (hp : s.gpr SB = p) (hal : p.toNat % 8 = 0)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (hOff + zB z * k)) (zB z))
    (v : Work z.bits)
    (hv : ∀ k (hk : k < 8), s.mem.readW (p + BitVec.ofNat 64 (hOff + zB z * k)) z.bits = (v[k]'(by omega))) :
    ∀ n ≤ 8, WP isa (Impl.Blake2.RISCV64.lds (w := z.bits) n) s fun s' =>
      PVars s' v n ∧ (∀ q, q ∉ wregs → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil (M := isa) ⟨fun _ _ h => absurd h (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hp₁, ho, hm, hrd, hwr⟩ => ?_)
    have h₁ : s₁.gpr SB = p := by rw [ho _ SB_not_mem, hp]
    have hb : zB z * n ≤ 56 := by have := zB_le z; have := Nat.mul_le_mul this (show n ≤ 7 by omega); omega
    refine WP.mono (ld_ok (z := z) (t := wreg n) (by rw [ws_bits]; simp only [hOff]; omega)
      (by rw [h₁, ws_bits]; exact wal z hal (by cases z <;> simp only [hOff, zB, Width.bytes] <;> omega))
      (by rw [h₁, ws_bits, hrd, hwr]; exact hin n (by omega))) fun s₂ ⟨hw, ho₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨hp₁.step (by omega) (by rw [hw, hm, h₁, ws_bits, hv n (by omega)])
      fun k hk e => ho₂ _ (wreg_ne hk (by omega) e),
      fun q hq => ?_, hm₂.trans hm, hrd₂.trans hrd, hwr₂.trans hwr⟩
    rw [ho₂ _ (ne_wreg hq (by omega)), ho q hq]

theorem iv_getD {n : Nat} (hn : n < 8) : P.IV.toList.getD n 0 = P.IV[n] := by
  simp [List.getD_eq_getElem?_getD, hn]

theorem ivs_ok (s : State) (v : Work z.bits) (hv : ∀ k (hk : k < 8), (v[k + 8]'(by omega)) = P.IV[k])
    (hp : PVars s v 8) :
    ∀ n ≤ 8, WP isa (Impl.Blake2.RISCV64.ivs P n) s fun s' =>
      PVars s' v (n + 8) ∧ (∀ q, q ∉ wregs → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil (M := isa) ⟨hp, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hp, ho, hm, hrd, hwr⟩ => ?_)
    refine WP.mono (movImm_ok (wreg_ne_of T_not_mem (k := n + 8) (by omega)) _)
      fun s₂ ⟨hw, ho₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨?_, fun q hq hT => ?_, hm₂.trans hm, hrd₂.trans hrd, hwr₂.trans hwr⟩
    · rw [show n + 1 + 8 = n + 8 + 1 by omega]
      exact hp.step (by omega) (by rw [hw, iv_getD P (by omega), hv n (by omega)])
        fun k hk e => ho₂ _ (wreg_ne hk (by omega) e) (wreg_ne_of T_not_mem hk)
    · rw [ho₂ _ (ne_wreg hq (by omega)) hT, ho q hq hT]

theorem wreg12 : wreg 12 = .s2 := rfl
theorem wreg13 : wreg 13 = .s3 := rfl
theorem wreg14 : wreg 14 = .s4 := rfl

theorem ctrLo_ok {p : Addr} {N : Nat} {fl : BitVec 64} (s : State) (hs : Scr p N fl s)
    (a : BitVec z.bits) (ha : (s.gpr (wreg 12)).setWidth z.bits = a) :
    WP isa (.block Impl.Blake2.RISCV64.ctrLo) s fun s' =>
      (s'.gpr (wreg 12)).setWidth z.bits = a ^^^ BitVec.ofNat z.bits N ∧
      (∀ q, q ≠ wreg 12 → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  simp only [wreg12] at ha ⊢
  apply WP.of_runBlock
  simp only [Impl.Blake2.RISCV64.ctrLo, wreg12, T, runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show loOff < 2048 by decide) (by rw [hs.sb]; exact dal hs.al (by decide))
      (by rw [hs.sb]; exact hs.inLo), exec_logic, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, hs.sb, hs.lo,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q h1 h2 => by simp only [h1, h2, ite_false], trivial, trivial, trivial⟩
  rw [lo_xor, ha, trunc_ofNat]

theorem hiW_ok {p : Addr} {N : Nat} {fl : BitVec 64} (s : State) (hs : Scr p N fl s) :
    WP isa (.block (Impl.Blake2.RISCV64.hiW (w := z.bits))) s fun s' =>
      (s'.gpr T).setWidth z.bits = BitVec.ofNat z.bits (N / 2 ^ z.bits) ∧
      (∀ q, q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  cases z
  · simp only [Impl.Blake2.RISCV64.hiW, T, Size.bits, show (32 : Nat) ≠ 64 by decide, ite_false,
      runBlock_cons, runStep_some, runBlock_nil,
      exec_load_d (show loOff < 2048 by decide) (by rw [hs.sb]; exact dal hs.al (by decide))
        (by rw [hs.sb]; exact hs.inLo), exec_shift_d (show 32 < 64 by decide), RegUpd.gpr_write,
      RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, ite_true, hs.sb, hs.lo,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun q h1 => by simp only [h1, ite_false], trivial, trivial, trivial⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    rw [show 2 ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mod_mul_right_div_self, Nat.mod_mod]
  · simp only [Impl.Blake2.RISCV64.hiW, T, Size.bits, ite_true, runBlock_cons, runStep_some,
      runBlock_nil, exec_load_d (show hiOff < 2048 by decide)
        (by rw [hs.sb]; exact dal hs.al (by decide)) (by rw [hs.sb]; exact hs.inHi),
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, ite_true, hs.sb,
      hs.hi, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun q h1 => by simp only [h1, ite_false], trivial, trivial, trivial⟩

theorem ctrHi_ok {p : Addr} {N : Nat} {fl : BitVec 64} (s : State) (hs : Scr p N fl s)
    (a b c : BitVec z.bits) (ha : (s.gpr (wreg 13)).setWidth z.bits = a)
    (hc : (s.gpr (wreg 14)).setWidth z.bits = c) (hb : (s.gpr T).setWidth z.bits = b) :
    WP isa (.block Impl.Blake2.RISCV64.ctrHi) s fun s' =>
      (s'.gpr (wreg 13)).setWidth z.bits = a ^^^ b ∧
      (s'.gpr (wreg 14)).setWidth z.bits = c ^^^ fl.setWidth z.bits ∧
      (∀ q, q ≠ wreg 13 → q ≠ wreg 14 → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [wreg13, wreg14, T] at ha hc hb ⊢
  apply WP.of_runBlock
  have h3 : SB ≠ .s3 := by decide
  simp only [Impl.Blake2.RISCV64.ctrHi, wreg13, wreg14, T, runBlock_cons, runStep_some, exec_logic]
  rw [exec_load_d (show fOff < 2048 by decide)
    (by rw [RegUpd.gpr_write_of_ne _ _ h3, hs.sb]; exact dal hs.al (by decide))
    (by rw [RegUpd.gpr_write_of_ne _ _ h3, RegUpd.rd_write, RegUpd.wr_write, hs.sb]; exact hs.inF)]
  simp only [runStep_some, runBlock_cons, runBlock_nil, exec_logic, RegUpd.gpr_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, h3,
    hs.sb, hs.f, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun q h1 h2 h3 => by simp only [h1, h2, h3, ite_false], trivial, trivial,
    trivial⟩
  · rw [lo_xor, ha, hb]
  · rw [lo_xor, hc]

end Init

/-! ## The work vector of `F` -/

section InitV
variable {w : Nat} (P : Params w)

/-- The work vector at the start of the rounds of `F` (RFC 7693 §3.2). -/
def initV (h : HashValue w) (t : Nat) (f : Bool) : Work w :=
  let v : Work w := h ++ P.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat w t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat w (t / 2 ^ w))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes w) else v

theorem F_eq (h : HashValue w) (m : Block w) (t : Nat) (f : Bool) :
    Spec.Blake2.F P h m t f =
      Vector.ofFn fun i => (h[i]'(by omega)) ^^^ ((List.range P.r).foldl (Spec.Blake2.round P m) (initV P h t f))[i] ^^^
        ((List.range P.r).foldl (Spec.Blake2.round P m) (initV P h t f))[i.val + 8] := rfl

/-- The flag word. -/
def flagW (w : Nat) (f : Bool) : BitVec w := if f then BitVec.allOnes w else 0

theorem initV_get (h : HashValue w) (t : Nat) (f : Bool) (k : Nat) (hk : k < 16) :
    (initV P h t f)[k] =
      if k = 12 then (h ++ P.IV)[12] ^^^ BitVec.ofNat w t
      else if k = 13 then (h ++ P.IV)[13] ^^^ BitVec.ofNat w (t / 2 ^ w)
      else if k = 14 then (h ++ P.IV)[14] ^^^ flagW w f
      else (h ++ P.IV)[k] := by
  unfold initV flagW
  by_cases e12 : k = 12
  · subst e12; cases f <;> simp
  by_cases e13 : k = 13
  · subst e13; cases f <;> simp
  by_cases e14 : k = 14
  · subst e14; cases f <;> simp
  cases f <;> simp [e12, e13, e14, Ne.symm e12, Ne.symm e13, Ne.symm e14]

end InitV

theorem flagW_trunc (z : Size) (f : Bool) : (flagW 64 f).setWidth z.bits = flagW z.bits f := by
  cases f <;> cases z <;> simp [flagW] <;> rfl

section Init2
variable {z : Size} (P : Params z.bits)

theorem init_ok {p : Addr} {N : Nat} {f : Bool} (s : State) (hs : Scr p N (flagW 64 f) s)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (hOff + zB z * k)) (zB z))
    (h : HashValue z.bits)
    (hh : ∀ k (hk : k < 8), s.mem.readW (p + BitVec.ofNat 64 (hOff + zB z * k)) z.bits = (h[k]'(by omega))) :
    WP isa (Impl.Blake2.RISCV64.init P) s fun s' =>
      Vars s' (initV P h N f) ∧ (∀ q, q ∉ wregs → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hv : ∀ k (hk : k < 8), s.mem.readW (p + BitVec.ofNat 64 (hOff + zB z * k)) z.bits = (h ++ P.IV)[k] :=
    fun k hk => by rw [hh k hk, Vector.getElem_append_left hk]
  refine WP.seq (WP.mono (lds_ok s p hs.sb hs.al hin _ hv 8 (Nat.le_refl _))
    fun s₁ ⟨hp₁, ho₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  refine WP.seq (WP.mono (ivs_ok P s₁ (h ++ P.IV) (fun k hk => by
      rw [Vector.getElem_append_right (by omega) (by omega)]; simp) hp₁ 8 (Nat.le_refl _))
    fun s₂ ⟨hp₂, ho₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  have o₂ : ∀ q, q ∉ wregs → q ≠ T → s₂.gpr q = s.gpr q := fun q hq hT => (ho₂ q hq hT).trans (ho₁ q hq)
  have hs₂ : Scr p N (flagW 64 f) s₂ :=
    hs.keep (o₂ _ SB_not_mem (by decide)) (by rw [hm₂, hm₁]) (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁])
  refine WP.seq (WP.mono (ctrLo_ok s₂ hs₂ _ (hp₂ 12 (by decide) (by decide)))
    fun s₃ ⟨h12, ho₃, hm₃, hrd₃, hwr₃⟩ => ?_)
  have hs₃ : Scr p N (flagW 64 f) s₃ := hs₂.keep (ho₃ _ (by decide) (by decide)) hm₃ hrd₃ hwr₃
  refine WP.seq (WP.mono (hiW_ok s₃ hs₃) fun s₄ ⟨hT, ho₄, hm₄, hrd₄, hwr₄⟩ => ?_)
  have hs₄ : Scr p N (flagW 64 f) s₄ := hs₃.keep (ho₄ _ (by decide)) hm₄ hrd₄ hwr₄
  refine WP.mono (ctrHi_ok s₄ hs₄ (h ++ P.IV)[13] _ (h ++ P.IV)[14]
    (by rw [ho₄ _ (by decide), ho₃ _ (by decide) (by decide)]; exact hp₂ 13 (by decide) (by decide))
    (by rw [ho₄ _ (by decide), ho₃ _ (by decide) (by decide)]; exact hp₂ 14 (by decide) (by decide)) hT)
    fun s₅ ⟨h13, h14, ho₅, hm₅, hrd₅, hwr₅⟩ => ?_
  refine ⟨fun k hk => ?_, fun q hq hT => ?_, by rw [hm₅, hm₄, hm₃, hm₂, hm₁],
    by rw [hrd₅, hrd₄, hrd₃, hrd₂, hrd₁], by rw [hwr₅, hwr₄, hwr₃, hwr₂, hwr₁]⟩
  · rw [initV_get P h N f k hk]
    by_cases e12 : k = 12
    · subst e12; simp only [↓reduceIte]
      rw [ho₅ _ (by decide) (by decide) (by decide), ho₄ _ (by decide)]; exact h12
    by_cases e13 : k = 13
    · subst e13; simp only [↓reduceIte]; exact h13
    by_cases e14 : k = 14
    · subst e14; simp only [↓reduceIte]; rw [← flagW_trunc]; exact h14
    simp only [e12, e13, e14, ite_false]
    rw [ho₅ _ (wreg_ne hk (by decide) e13) (wreg_ne hk (by decide) e14)
      (wreg_ne_of T_not_mem hk), ho₄ _ (wreg_ne_of T_not_mem hk),
      ho₃ _ (wreg_ne hk (by decide) e12) (wreg_ne_of T_not_mem hk)]
    exact hp₂ k hk (by omega)
  · rw [ho₅ _ (ne_wreg hq (by decide)) (ne_wreg hq (by decide)) hT, ho₄ _ hT,
      ho₃ _ (ne_wreg hq (by decide)) hT, o₂ q hq hT]

/-! ## Adding the work vector into the hash value -/

theorem hw_bound (z : Size) {k : Nat} (hk : k < 8) : hOff + zB z * k + zB z ≤ hOff + 8 * zB z := by
  have := Nat.mul_le_mul_left (zB z) (show k + 1 ≤ 8 by omega)
  rw [Nat.mul_succ] at this; rw [Nat.mul_comm 8]; omega

theorem fin_step (n : Nat) (hn : n < 8) (s : State) (p : Addr) (hp : s.gpr SB = p)
    (hal : p.toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (hOff + zB z * n)) (zB z))
    (hout : InRegions s.wr (p + BitVec.ofNat 64 (hOff + zB z * n)) (zB z))
    (a b : BitVec z.bits) (ha : (s.gpr (wreg n)).setWidth z.bits = a)
    (hb : (s.gpr (wreg (n + 8))).setWidth z.bits = b) :
    WP isa (.block [.load (wd z.bits) T SB (hOff + ws z.bits * n),
      .logic .xor T T (wreg n), .logic .xor T T (wreg (n + 8)),
      .store (wd z.bits) T SB (hOff + ws z.bits * n)]) s fun s' =>
      s'.mem = s.mem.writeW (p + BitVec.ofNat 64 (hOff + zB z * n))
        (s.mem.readW (p + BitVec.ofNat 64 (hOff + zB z * n)) z.bits ^^^ a ^^^ b) ∧
      (∀ q, q ≠ T → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hb' := hw_bound z hn
  have ho : hOff + zB z * n < 2048 := by simp only [hOff] at hb' ⊢; have := zB_le z; omega
  have hal' : (p + BitVec.ofNat 64 (hOff + zB z * n)).toNat % zB z = 0 :=
    wal z hal (by cases z <;> simp only [hOff, zB, Width.bytes] <;> omega)
  have n1 : wreg n ≠ T := wreg_ne_of T_not_mem (by omega)
  have n2 : wreg (n + 8) ≠ T := wreg_ne_of T_not_mem (by omega)
  have hTS : T ≠ SB := by decide
  rw [ws_bits]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec_ld ho (by rw [hp]; exact hal') (by rw [hp]; exact hin),
    exec_logic]
  rw [exec_st ho (by rw [RegUpd.gpr_write_of_ne _ _ (Ne.symm hTS), RegUpd.gpr_write_of_ne _ _ (Ne.symm hTS),
      RegUpd.gpr_write_of_ne _ _ (Ne.symm hTS), hp]; exact hal')
    (by rw [RegUpd.gpr_write_of_ne _ _ (Ne.symm hTS), RegUpd.gpr_write_of_ne _ _ (Ne.symm hTS),
      RegUpd.gpr_write_of_ne _ _ (Ne.symm hTS), RegUpd.wr_write, RegUpd.wr_write, RegUpd.wr_write, hp]
        exact hout)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    ite_true, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Ne.symm hTS, n1, n2, ite_false,
    hp, lo_xor, ext_trunc, ha, hb]
  exact ⟨trivial, fun q hq => by simp only [hq, ite_false], trivial, trivial⟩

theorem fin_ok (s : State) (p : Addr) (hp : s.gpr SB = p) (hal : p.toNat % 8 = 0)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (hOff + zB z * k)) (zB z))
    (hout : ∀ k < 8, InRegions s.wr (p + BitVec.ofNat 64 (hOff + zB z * k)) (zB z))
    (v : Work z.bits) (hv : Vars s v) (h : HashValue z.bits)
    (hh : ∀ k (hk : k < 8), s.mem.readW (p + BitVec.ofNat 64 (hOff + zB z * k)) z.bits = (h[k]'(by omega))) :
    ∀ n ≤ 8, WP isa (Impl.Blake2.RISCV64.fin (w := z.bits) n) s fun s' =>
      (∀ k (hk : k < 8), s'.mem.readW (p + BitVec.ofNat 64 (hOff + zB z * k)) z.bits =
        if k < n then (h[k]'(by omega)) ^^^ (v[k]'(by omega)) ^^^ (v[k + 8]'(by omega)) else (h[k]'(by omega))) ∧
      Frame [⟨p + BitVec.ofNat 64 hOff, 8 * zB z⟩] s.mem s'.mem ∧ (∀ q, q ≠ T → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun k hk => by simpa using hh k hk, Frame.refl _ _,
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hm₁, hf₁, ho₁, hrd₁, hwr₁⟩ => ?_)
    refine WP.mono (fin_step n (by omega) s₁ p (by rw [ho₁ _ (by decide), hp]) hal
      (by rw [hrd₁, hwr₁]; exact hin n (by omega)) (by rw [hwr₁]; exact hout n (by omega))
      (v[n]'(by omega)) (v[n + 8]'(by omega))
      (by rw [ho₁ _ (wreg_ne_of T_not_mem (by omega))]; exact hv n (by omega))
      (by rw [ho₁ _ (wreg_ne_of T_not_mem (by omega))]; exact hv (n + 8) (by omega)))
      fun s₂ ⟨hm₂, ho₂, hrd₂, hwr₂⟩ => ?_
    have e : s₁.mem.readW (p + BitVec.ofNat 64 (hOff + zB z * n)) z.bits = (h[n]'(by omega)) := by
      rw [hm₁ n (by omega)]; simp
    refine ⟨fun k hk => ?_, ?_, fun q hq => (ho₂ q hq).trans (ho₁ q hq), hrd₂.trans hrd₁,
      hwr₂.trans hwr₁⟩
    · rw [hm₂, e]
      by_cases hkn : k = n
      · subst hkn; rw [readW_writeW_self]; simp
      · have b1 := hw_bound z hk
        have b2 := hw_bound z (show n < 8 by omega)
        rw [cell_sep p _ _ (by
            rw [bits_div]
            rcases Nat.lt_or_gt_of_ne hkn with h' | h'
            · left; have := Nat.mul_le_mul_left (zB z) h'; rw [Nat.mul_succ] at this; omega
            · right; have := Nat.mul_le_mul_left (zB z) h'; rw [Nat.mul_succ] at this; omega)
            (by rw [bits_div]; simp only [hOff] at b1 ⊢; have := zB_le z; omega)
            (by rw [bits_div]; simp only [hOff] at b2 ⊢; have := zB_le z; omega), hm₁ k hk]
        by_cases hlt : k < n
        · simp [hlt, show k < n + 1 by omega]
        · simp [hlt, show ¬k < n + 1 by omega]
    · rw [hm₂]
      refine hf₁.writeW (List.mem_singleton_self _) _ ?_
      rw [bits_div]
      exact Offset.contains p (Nat.le_add_right _ _) (hw_bound z (by omega)) (by simp only [hOff]; have := zB_le z; omega)

end Init2

/-! ## Advancing to the next block -/

/-- The carry out of the low word when the counter `N` advances by `2 ^ k`: the new low
word is below `2 ^ k` exactly when the addition wrapped. -/
theorem carry (N k : Nat) (hk : k = 6 ∨ k = 7) :
    BitVec.ofNat 64 (N / 2 ^ 64) + (((BitVec.ofNat 64 N + BitVec.ofNat 64 (2 ^ k)) >>> k - BitVec.ofNat 64 1) >>> 63) =
      BitVec.ofNat 64 ((N + 2 ^ k) / 2 ^ 64) := by
  have hN := Nat.div_add_mod N (2 ^ 64)
  have hL := Nat.mod_lt N (show 2 ^ 64 > 0 by decide)
  have hb : 2 ≤ 2 ^ k ∧ 2 ^ k ≤ 128 := by rcases hk with rfl | rfl <;> decide
  rw [BitVec.ofNat_add_ofNat]
  generalize N / 2 ^ 64 = A at hN ⊢
  generalize N % 2 ^ 64 = L at hN hL ⊢
  subst hN
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (BitVec.ofNat 64 1).toNat = 1 from rfl]
  have e1 : (2 ^ 64 * A + L + 2 ^ k) % 2 ^ 64 = (L + 2 ^ k) % 2 ^ 64 := by
    rw [Nat.add_assoc, Nat.mul_add_mod]
  have e2 : (2 ^ 64 * A + L + 2 ^ k) / 2 ^ 64 = A + (L + 2 ^ k) / 2 ^ 64 := by
    rw [Nat.add_assoc, Nat.mul_add_div (by decide)]
  rw [e1, e2]
  generalize 2 ^ k = B at *
  by_cases hc : L + B < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc]
    have h1 : 1 ≤ (L + B) / B := by
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    have h2 : (L + B) / B ≤ (L + B) / 2 := Nat.div_le_div_left hb.1 (by decide)
    have : (2 ^ 64 - 1 + (L + B) / B) % 2 ^ 64 / 2 ^ 63 = 0 := by omega
    rw [this]; omega
  · have q1 : (L + B) / 2 ^ 64 = 1 := by omega
    have q2 : (L + B) % 2 ^ 64 = L + B - 2 ^ 64 := by omega
    rw [q2, q1, Nat.div_eq_of_lt (show L + B - 2 ^ 64 < B by omega)]
    omega

theorem lbb_cases (z : Size) : lbb z.bits = 6 ∨ lbb z.bits = 7 := by cases z <;> decide

theorem bb_imm (z : Size) : BitVec.ofInt 64 (16 * (ws z.bits : Int)) = BitVec.ofNat 64 (2 ^ lbb z.bits) := by
  cases z <;> rfl

theorem bb_imm12 (z : Size) : imm12 (16 * (ws z.bits : Int)) := by cases z <;> decide

theorem add_neg_one (x : BitVec 64) : x + BitVec.ofInt 64 (-1) = x - BitVec.ofNat 64 1 := by
  rw [BitVec.sub_eq_add_neg]; rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}
open VG.RISCV64.Wp

theorem wp_addiI {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi h) (k _ (Upd.write _ _ _))

theorem wp_srl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .srl .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_sll {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sll .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_andi {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n &&& BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

theorem wp_liI {d : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _))

end

open VG.RISCV64.Wp in
theorem advance_ok {z : Size} {p : Addr} {N : Nat} {fl : BitVec 64} (s : State)
    (hs : Scr p N fl s) (hoLo : InRegions s.wr (p + BitVec.ofNat 64 loOff) 8)
    (hoHi : InRegions s.wr (p + BitVec.ofNat 64 hiOff) 8) :
    WP isa (.block (Impl.Blake2.RISCV64.advance (w := z.bits))) s fun s' =>
      s'.gpr .a1 = s.gpr .a1 + BitVec.ofNat 64 (2 ^ lbb z.bits) ∧
      s'.gpr .a2 = s.gpr .a2 - BitVec.ofNat 64 1 ∧
      s'.mem = (s.mem.writeW (p + BitVec.ofNat 64 loOff) (BitVec.ofNat 64 (N + 2 ^ lbb z.bits))).writeW
        (p + BitVec.ofNat 64 hiOff) (BitVec.ofNat 64 ((N + 2 ^ lbb z.bits) / 2 ^ 64)) ∧
      (∀ q, q ≠ .a1 → q ≠ .a2 → q ≠ wreg 0 → q ≠ wreg 1 → q ≠ wreg 2 → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hk := lbb_cases z
  have hk' : lbb z.bits < 64 := by omega
  have hsb : s.gpr .a5 = p := hs.sb
  have aLo := dal hs.al (show loOff % 8 = 0 by decide)
  have aHi := dal hs.al (show hiOff % 8 = 0 by decide)
  have i1 : imm12 (-1) := by decide
  have hsep : ∀ X : BitVec 64, (s.mem.writeW (p + BitVec.ofNat 64 loOff) X).readW
      (p + BitVec.ofNat 64 hiOff) 64 = BitVec.ofNat 64 (N / 2 ^ 64) := fun X => by
    rw [cell_sep p _ _ (by decide) (by decide) (by decide)]; exact hs.hi
  simp only [Impl.Blake2.RISCV64.advance, show wreg 0 = .a3 from rfl, show wreg 1 = .a4 from rfl,
    show wreg 2 = .a6 from rfl, SB]
  refine wp_addiI (bb_imm12 z) fun s₁ u₁ => ?_
  refine wp_ld (by decide) (a := p + BitVec.ofNat 64 loOff) (by rw [u₁.other _ (by decide), hsb])
    aLo (by rw [u₁.rd, u₁.wr]; exact hs.inLo) fun s₂ u₂ => ?_
  refine wp_addiI (bb_imm12 z) fun s₃ u₃ => ?_
  refine wp_sd (by decide) (a := p + BitVec.ofNat 64 loOff)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hsb]) aLo
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hoLo) fun s₄ u₄ => ?_
  refine wp_srl hk' fun s₅ u₅ => ?_
  refine wp_addiI i1 fun s₆ u₆ => ?_
  refine wp_srl (show 63 < 64 by decide) fun s₇ u₇ => ?_
  have g₇ : ∀ r, r ≠ .a1 → r ≠ .a3 → r ≠ .a4 → s₇.gpr r = s.gpr r := fun r h1 h3 h4 => by
    rw [u₇.other _ h4, u₆.other _ h4, u₅.other _ h4, u₄.gpr, u₃.other _ h3, u₂.other _ h3,
      u₁.other _ h1]
  have m₇ : s₇.mem = s.mem.writeW (p + BitVec.ofNat 64 loOff) (BitVec.ofNat 64 (N + 2 ^ lbb z.bits)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₂.gpr, u₃.mem, u₂.mem, u₁.mem, hs.lo, bb_imm,
      BitVec.ofNat_add_ofNat]
  refine wp_ld (by decide) (a := p + BitVec.ofNat 64 hiOff) (by rw [g₇ _ (by decide) (by decide) (by decide), hsb])
    aHi (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr,
      u₁.rd, u₁.wr]; exact hs.inHi) fun s₈ u₈ => ?_
  refine wp_add fun s₉ u₉ => ?_
  refine wp_sd (by decide) (a := p + BitVec.ofNat 64 hiOff)
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), g₇ _ (by decide) (by decide) (by decide), hsb]) aHi
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hoHi) fun s₁₀ u₁₀ => ?_
  refine wp_addiI i1 fun s₁₁ u₁₁ => WP.block_nil (M := isa) ⟨?_, ?_, ?_, fun q h1 h2 h3 h4 h6 => ?_, ?_, ?_⟩
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, bb_imm]
  · rw [u₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      g₇ _ (by decide) (by decide) (by decide), add_neg_one]
  · rw [u₁₁.mem, u₁₀.mem, u₉.gpr, u₉.mem, u₈.gpr, u₈.other _ (by decide), u₈.mem, u₇.gpr, u₆.gpr,
      u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, hs.lo, m₇, hsep, bb_imm, add_neg_one, carry N _ hk]
  · rw [u₁₁.other q h2, u₁₀.gpr, u₉.other q h6, u₈.other q h6, g₇ q h1 h3 h4]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## Saving registers, the counter and the flag word -/

/-- The flag word, computed without a branch from the zero-extended low word
of `last`. -/
theorem flag_eq (x : BitVec 64) :
    BitVec.ofNat 64 0 - ((x <<< 32 >>> 32 ||| (BitVec.ofNat 64 0 - x <<< 32 >>> 32)) >>> 63) =
      flagW 64 (x.setWidth 32 != 0) := by
  have hz : x <<< 32 >>> 32 = (x.setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h : i < 32
    · simp (disch := omega) [h, hi, show ¬ 32 + i < 32 by omega, show 32 + i < 64 by omega]
    · simp (disch := omega) [h, show ¬ 32 + i < 64 by omega]
  rw [hz]
  generalize x.setWidth 32 = l
  rw [BitVec.ushiftRight_or_distrib]
  have hl := l.isLt
  by_cases h : l = 0
  · subst h; decide
  · have h0 : l.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have e1 : l.setWidth 64 >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
        show (0 : BitVec 64).toNat = 0 from rfl]
      omega
    have e2 : (BitVec.ofNat 64 0 - l.setWidth 64) >>> 63 = 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth,
        Nat.shiftRight_eq_div_pow, show (BitVec.ofNat 64 0).toNat = 0 from rfl,
        show (1 : BitVec 64).toNat = 1 from rfl]
      omega
    rw [e1, e2, show ((0 : BitVec 64) ||| 1) = 1 from rfl]
    have ht : (l != 0) = true := by simpa using h
    simp only [flagW, ht, ite_true]
    decide

/-- The scratch after `setup`'s saves, counter and flag word. -/
def setupMem (m : Mem) (p : Addr) (g : Reg → BitVec 64) (t : BitVec 64) (f : Bool) : Mem :=
  (((Spill.saveMem m p g saved).writeW (p + BitVec.ofNat 64 loOff) t).writeW
    (p + BitVec.ofNat 64 hiOff) (BitVec.ofNat 64 0)).writeW (p + BitVec.ofNat 64 fOff) (flagW 64 f)

theorem save_eq : Impl.Blake2.RISCV64.save = Spill.saveCode SB saved := rfl
theorem restore_eq : Impl.Blake2.RISCV64.restore = Spill.restoreCode SB saved := rfl

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide
theorem saved_off : ∀ p ∈ saved, p.2 + 8 ≤ loOff := by decide

/-- The counter and the flag word. -/
def ctrF : List Instr :=
  [.store .d .a3 SB loOff, .li T 0, .store .d T SB hiOff,
   .shift .sll .d .a4 .a4 32, .shift .srl .d .a4 .a4 32, .sub .a3 T .a4, .logic .or .a4 .a4 .a3,
   .shift .srl .d .a4 .a4 63, .sub .a4 T .a4, .store .d .a4 SB fOff]

theorem setup_eq (w : Nat) : Impl.Blake2.RISCV64.setup (w := w) =
    (([.addi SB SB 7, .logicImm .and SB SB (-8)] ++ Spill.saveCode SB saved) ++ ctrF) ++
      (List.range 8).flatMap (Impl.Blake2.RISCV64.cpIn (w := w)) := rfl

open VG.RISCV64.Wp in
theorem ctrF_ok (s : State) (p : Addr) (hp : s.gpr SB = p) (hal : p.toNat % 8 = 0)
    (ho : ∀ d, d ∈ [loOff, hiOff, fOff] → InRegions s.wr (p + BitVec.ofNat 64 d) 8) :
    WP isa (.block ctrF) s fun s' =>
      s'.mem = ((s.mem.writeW (p + BitVec.ofNat 64 loOff) (s.gpr .a3)).writeW
        (p + BitVec.ofNat 64 hiOff) (BitVec.ofNat 64 0)).writeW (p + BitVec.ofNat 64 fOff)
          (flagW 64 ((s.gpr .a4).setWidth 32 != 0)) ∧
      (∀ q, q ≠ .a3 → q ≠ .a4 → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsb : s.gpr .a5 = p := hp
  have i0 : imm12 0 := by decide
  simp only [ctrF, SB, T]
  refine wp_sd (by decide) (a := p + BitVec.ofNat 64 loOff) (by rw [hsb]) (dal hal (by decide))
    (ho _ (by decide)) fun s₁ u₁ => ?_
  refine wp_liI i0 fun s₂ u₂ => ?_
  refine wp_sd (by decide) (a := p + BitVec.ofNat 64 hiOff)
    (by rw [u₂.other _ (by decide), u₁.gpr, hsb]) (dal hal (by decide))
    (by rw [u₂.wr, u₁.wr]; exact ho _ (by decide)) fun s₃ u₃ => ?_
  refine wp_sll (show 32 < 64 by decide) fun s₄ u₄ => ?_
  refine wp_srl (show 32 < 64 by decide) fun s₅ u₅ => ?_
  refine wp_sub fun s₆ u₆ => ?_
  refine wp_or fun s₇ u₇ => ?_
  refine wp_srl (show 63 < 64 by decide) fun s₈ u₈ => ?_
  refine wp_sub fun s₉ u₉ => ?_
  have g₉ : ∀ r, r ≠ .a3 → r ≠ .a4 → r ≠ .t6 → s₉.gpr r = s.gpr r := fun r h3 h4 hT => by
    rw [u₉.other _ h4, u₈.other _ h4, u₇.other _ h4, u₆.other _ h3, u₅.other _ h4, u₄.other _ h4,
      u₃.gpr, u₂.other _ hT, u₁.gpr]
  refine wp_sd (by decide) (a := p + BitVec.ofNat 64 fOff)
    (by rw [g₉ _ (by decide) (by decide) (by decide), hsb]) (dal hal (by decide))
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact ho _ (by decide))
    fun s₁₀ u₁₀ => WP.block_nil (M := isa) ⟨?_, fun q h3 h4 hT => ?_, ?_, ?_⟩
  · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem]
    simp only [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr,
      u₈.other Reg.t6 (by decide), u₇.other Reg.t6 (by decide), u₆.other Reg.t6 (by decide),
      u₆.other Reg.a4 (by decide), u₅.other Reg.t6 (by decide), u₄.other Reg.t6 (by decide),
      u₂.other Reg.a4 (by decide), show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, flag_eq]
  · rw [u₁₀.gpr, g₉ q h3 h4 hT]
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## Copying words a byte at a time -/

/-- Word `j` from `src` to offset `o` of the scratch space: the shape of
`cpIn` and `cpBlk`. -/
def cpGen (w : Nat) (src : Reg) (o j : Nat) : List Instr :=
  ldLE w T (wreg 0) (wreg 1) src (ws w * j) ++ ([.store (wd w) T SB (o + ws w * j)] : List Instr)

theorem cpIn_eq (w : Nat) : Impl.Blake2.RISCV64.cpIn (w := w) = cpGen w .a0 hOff := rfl
theorem cpBlk_eq (w : Nat) : Impl.Blake2.RISCV64.cpBlk (w := w) = cpGen w .a1 mOff := rfl

/-- After copying words `0 … k-1` from `src` to offset `o` of the scratch space. -/
structure CpI (z : Size) (src : Reg) (o : Nat) (s₁ : State) (k : Nat) (s : State) : Prop where
  other : ∀ q, q ≠ T → q ≠ wreg 0 → q ≠ wreg 1 → s.gpr q = s₁.gpr q
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨s₁.gpr SB + BitVec.ofNat 64 o, 16 * zB z⟩] s₁.mem s.mem
  words : ∀ j < k, s.mem.readW (s₁.gpr SB + BitVec.ofNat 64 (o + zB z * j)) z.bits =
    s₁.mem.readW (s₁.gpr src + BitVec.ofNat 64 (zB z * j)) z.bits

theorem cp_ok {z : Size} {src : Reg} (hsT : src ≠ T) (hs0 : src ≠ wreg 0) (hs1 : src ≠ wreg 1)
    {o N : Nat} (hN : N ≤ 16) (ho : o % 8 = 0) (hob : o + 16 * zB z ≤ 2040) (s₁ : State)
    (hal : (s₁.gpr SB).toNat % 8 = 0)
    (hin : ∀ j < N, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr src + BitVec.ofNat 64 (zB z * j)) (zB z))
    (hout : ∀ j < N, InRegions s₁.wr (s₁.gpr SB + BitVec.ofNat 64 (o + zB z * j)) (zB z))
    (hdis : ∀ j < N, Region.Disjoint ⟨s₁.gpr src + BitVec.ofNat 64 (zB z * j), zB z⟩
      ⟨s₁.gpr SB + BitVec.ofNat 64 o, 16 * zB z⟩) :
    WP isa (.block ((List.range N).flatMap (cpGen z.bits src o))) s₁ (CpI z src o s₁ N) := by
  refine wp_range_flatMap (M := isa) (CpI z src o s₁) (fun k s hk h => ?_) N (Nat.le_refl _) s₁
    ⟨fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hsrc : s.gpr src = s₁.gpr src := h.other _ hsT hs0 hs1
  have hsb : s.gpr SB = s₁.gpr SB := h.other _ (by decide) (by decide) (by decide)
  have hb := zB_mul_le z (show k < 16 by omega)
  have h8 := zB_le z
  unfold cpGen
  rw [ws_bits, WP.block_append_iff]
  refine WP.mono (ldLE_ok (z := z) (d := T) (tmp := wreg 0) (tmp2 := wreg 1) (Ne.symm hsT)
    (Ne.symm hs0) (by decide) (Ne.symm hs1) (by decide) (by decide) (by omega)
    (by rw [h.rd, h.wr, hsrc]; exact hin k hk)) fun s₂ ⟨hv₂, ho₂, hm₂, hrd₂, hwr₂⟩ => ?_
  have hsb₂ : s₂.gpr SB = s₁.gpr SB := (ho₂ _ (by decide) (by decide) (by decide)).trans hsb
  have hoff : (o + zB z * k) % zB z = 0 := by
    rw [Nat.add_mul_mod_self_left]; cases z <;> simp only [zB, Width.bytes] at * <;> omega
  refine WP.mono (st_ok (z := z) (t := T) (n := SB) (off := o + zB z * k) (by omega)
    (by rw [hsb₂]; exact wal z hal hoff) (by rw [hsb₂, hwr₂, h.wr]; exact hout k hk))
    fun s₃ ⟨hg₃, hm₃, hrd₃, hwr₃⟩ => ?_
  have hval : s.mem.readW (s₁.gpr src + BitVec.ofNat 64 (zB z * k)) z.bits =
      s₁.mem.readW (s₁.gpr src + BitVec.ofNat 64 (zB z * k)) z.bits :=
    h.frame.readW (by rw [bits_div]; exact Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdis k hk)
      (by rw [bits_div]; omega)
  refine ⟨fun q h1 h2 h3 => by rw [hg₃, ho₂ q h1 h2 h3]; exact h.other q h1 h2 h3,
    by rw [hrd₃, hrd₂, h.rd], by rw [hwr₃, hwr₂, h.wr], ?_, fun j hj => ?_⟩
  · rw [hm₃, hm₂, hsb₂]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    rw [bits_div]
    exact Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega)
  · rw [hm₃, hm₂, hsb₂]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hb' := zB_mul_le z hj
      rw [cell_sep _ _ _ (by rw [bits_div]; left; omega) (by rw [bits_div]; omega)
        (by rw [bits_div]; omega)]
      exact h.words j hj
    · rw [readW_writeW_self, hv₂, hsrc, hval]

/-- After copying words `0 … k-1` of the hash value from offset `hOff` of the
scratch space to `a0`. -/
structure CpO (z : Size) (s₁ : State) (k : Nat) (s : State) : Prop where
  other : ∀ q, q ≠ T → q ≠ wreg 0 → q ≠ wreg 1 → s.gpr q = s₁.gpr q
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨s₁.gpr .a0, 8 * zB z⟩] s₁.mem s.mem
  words : ∀ j < k, s.mem.readW (s₁.gpr .a0 + BitVec.ofNat 64 (zB z * j)) z.bits =
    s₁.mem.readW (s₁.gpr SB + BitVec.ofNat 64 (hOff + zB z * j)) z.bits

theorem cpOut_ok {z : Size} (s₁ : State) (hal : (s₁.gpr SB).toNat % 8 = 0)
    (hin : ∀ j < 8, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr SB + BitVec.ofNat 64 (hOff + zB z * j)) (zB z))
    (hout : ∀ j < 8, InRegions s₁.wr (s₁.gpr .a0 + BitVec.ofNat 64 (zB z * j)) (zB z))
    (hdis : ∀ j < 8, Region.Disjoint ⟨s₁.gpr SB + BitVec.ofNat 64 (hOff + zB z * j), zB z⟩
      ⟨s₁.gpr .a0, 8 * zB z⟩) :
    WP isa (.block ((List.range 8).flatMap (Impl.Blake2.RISCV64.cpOut (w := z.bits)))) s₁
      (CpO z s₁ 8) := by
  refine wp_range_flatMap (M := isa) (CpO z s₁) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₁
    ⟨fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have ha0 : s.gpr .a0 = s₁.gpr .a0 := h.other _ (by decide) (by decide) (by decide)
  have hsb : s.gpr SB = s₁.gpr SB := h.other _ (by decide) (by decide) (by decide)
  have hb := zB_mul_le z hk
  have h8 := zB_le z
  have hoff : (hOff + zB z * k) % zB z = 0 := by
    rw [Nat.add_mul_mod_self_left]; cases z <;> simp only [hOff, zB, Width.bytes]
  simp only [Impl.Blake2.RISCV64.cpOut, ws_bits]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok (z := z) (t := T) (n := SB) (off := hOff + zB z * k)
    (by simp only [hOff]; omega) (by rw [hsb]; exact wal z hal hoff)
    (by rw [h.rd, h.wr, hsb]; exact hin k hk)) fun s₂ ⟨hv₂, ho₂, hm₂, hrd₂, hwr₂⟩ => ?_
  have ha0₂ : s₂.gpr .a0 = s₁.gpr .a0 := (ho₂ _ (by decide)).trans ha0
  refine WP.mono (stLE_ok (z := z) (v := T) (tmp := wreg 0) (tmp2 := wreg 1) (n := .a0) (by decide)
    (by decide) (by decide) (by decide) (by omega) (by rw [ha0₂, hwr₂, h.wr]; exact hout k hk))
    fun s₃ ⟨ho₃, hm₃, hrd₃, hwr₃⟩ => ?_
  have hval : s.mem.readW (s₁.gpr SB + BitVec.ofNat 64 (hOff + zB z * k)) z.bits =
      s₁.mem.readW (s₁.gpr SB + BitVec.ofNat 64 (hOff + zB z * k)) z.bits :=
    h.frame.readW (by rw [bits_div]; exact Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdis k hk)
      (by rw [bits_div]; omega)
  refine ⟨fun q h1 h2 h3 => by rw [ho₃ q h2 h3, ho₂ q h1]; exact h.other q h1 h2 h3,
    by rw [hrd₃, hrd₂, h.rd], by rw [hwr₃, hwr₂, h.wr], ?_, fun j hj => ?_⟩
  · rw [hm₃, hm₂, ha0₂]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    rw [bits_div]
    have := zB_mul_le z (show k < 8 by omega)
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [hm₃, hm₂, ha0₂]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hb' := zB_mul_le z hj
      rw [cell_sep _ _ _ (by rw [bits_div]; left; omega) (by rw [bits_div]; omega)
        (by rw [bits_div]; omega)]
      exact h.words j hj
    · rw [readW_writeW_self, hv₂, hsb, hval]

/-! ## The regions -/

section Regions
variable (z : Size) (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev bp : Addr := s₀.gpr .a1
abbrev nb : Nat := (s₀.gpr .a2).toNat
abbrev scr₀ : Addr := s₀.gpr .a5
/-- The scratch space, rounded up to a multiple of 8. -/
abbrev sb : Addr := scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀))
abbrev t₀ : Nat := (s₀.gpr .a3).toNat
abbrev fl : Bool := (s₀.gpr .a4).setWidth 32 != 0
abbrev stR : Region := ⟨st s₀, 8 * zB z⟩
abbrev blR : Region := ⟨bp s₀, Spec.Blake2.blockBytes z.bits * nb s₀⟩
abbrev scrR : Region := ⟨scr₀ s₀, 512⟩
abbrev H₀ : HashValue z.bits := Spec.Blake2.stateAt z.bits s₀.mem (st s₀)
/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (Spec.Blake2.blockBytes z.bits * i)

end Regions

theorem bbz (z : Size) : Spec.Blake2.blockBytes z.bits = 16 * zB z := by cases z <;> rfl

theorem bb_pow (z : Size) : Spec.Blake2.blockBytes z.bits = 2 ^ lbb z.bits := by cases z <;> rfl

theorem stateAt_get' (z : Size) (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (Spec.Blake2.stateAt z.bits m p)[k] = m.readW (p + BitVec.ofNat 64 (zB z * k)) z.bits := by
  simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, bits_div]

theorem stateAt_eq' {z : Size} {m : Mem} {p : Addr} {v : HashValue z.bits}
    (h : ∀ k (hk : k < 8), m.readW (p + BitVec.ofNat 64 (zB z * k)) z.bits = (v[k]'(by omega))) :
    Spec.Blake2.stateAt z.bits m p = v := by
  apply Vector.ext
  intro k hk
  rw [stateAt_get' z m p hk]
  exact h k hk

theorem sb_add (s₀ : State) (d : Nat) :
    sb s₀ + BitVec.ofNat 64 d = scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀) + d) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem sb_al (s₀ : State) : (sb s₀).toNat % 8 = 0 := align_al _

theorem cell_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 504) :
    (scrR s₀).Contains (sb s₀ + BitVec.ofNat 64 d) n := by
  rw [sb_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.contains_base _ (by omega) (by omega)

theorem cell_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 504) :
    Region.Sub ⟨sb s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) := by
  rw [sb_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.sub_base _ (by omega)

theorem word_contains (z : Size) (p : Addr) {k : Nat} (hk : k < 8) :
    (⟨p, 8 * zB z⟩ : Region).Contains (p + BitVec.ofNat 64 (zB z * k)) (zB z) := by
  have := zB_mul_le z hk
  have := zB_le z
  exact Offset.contains_base p (by rw [Nat.mul_comm 8]; omega) (by omega)

theorem word_sub (z : Size) (p : Addr) {k : Nat} (hk : k < 8) :
    Region.Sub ⟨p + BitVec.ofNat 64 (zB z * k), zB z⟩ ⟨p, 8 * zB z⟩ := by
  have := zB_mul_le z hk
  exact Offset.sub_base p (by rw [Nat.mul_comm 8]; omega)

theorem blk_bound (z : Size) {i j n : Nat} (hi : i < n) (hj : j < 16)
    (hn : Spec.Blake2.blockBytes z.bits * n < 2 ^ 64) :
    Spec.Blake2.blockBytes z.bits * i + zB z * j + zB z ≤ Spec.Blake2.blockBytes z.bits * n ∧
      Spec.Blake2.blockBytes z.bits * i + zB z * j < 2 ^ 64 := by
  rw [bbz] at *
  cases z <;> simp only [zB, Width.bytes] at * <;> omega

structure Pre (z : Size) (s₀ : State) : Prop where
  rd : s₀.rd = [blR z s₀]
  wr : s₀.wr = [stR z s₀, scrR s₀]
  st_scr : (stR z s₀).Disjoint (scrR s₀)
  blk_st : (blR z s₀).Disjoint (stR z s₀)
  blk_scr : (blR z s₀).Disjoint (scrR s₀)

theorem pre_of {z : Size} (P : Params z.bits) (s₀ : State) (h : (compressRISCV64 P).pre s₀) :
    Pre z s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [bits_div] at h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {z : Size} {s₀ : State} (h : Pre z s₀)
include h

theorem nb_lt : Spec.Blake2.blockBytes z.bits * nb s₀ < 2 ^ 64 := by
  by_contra hn
  have hb := zB_pos z
  refine h.blk_st (st s₀) ?_ (Offset.contains_base (st s₀) (d := 0) (n := 1) (k := 8 * zB z) (by omega) (by decide) |>
    fun c => by simpa using c)
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (zB z * k)) (zB z) :=
  ⟨stR z s₀, by simp [h.wr], word_contains z _ hk⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (zB z * k)) (zB z) :=
  ⟨stR z s₀, by simp [h.wr], word_contains z _ hk⟩

theorem in_cell {d n : Nat} (hd : d + n ≤ 504) :
    InRegions (s₀.rd ++ s₀.wr) (sb s₀ + BitVec.ofNat 64 d) n :=
  ⟨scrR s₀, by simp [h.wr], cell_contains s₀ hd⟩

theorem out_cell {d n : Nat} (hd : d + n ≤ 504) : InRegions s₀.wr (sb s₀ + BitVec.ofNat 64 d) n :=
  ⟨scrR s₀, by simp [h.wr], cell_contains s₀ hd⟩

theorem blk_contains {i j : Nat} (hi : i < nb s₀) (hj : j < 16) :
    (blR z s₀).Contains (blkAddr z s₀ i + BitVec.ofNat 64 (zB z * j)) (zB z) := by
  have hb := blk_bound z hi hj h.nb_lt
  rw [Offset.add_ofNat_add_ofNat]
  exact Offset.contains_base _ hb.1 hb.2

theorem blk_sub {i j : Nat} (hi : i < nb s₀) (hj : j < 16) :
    Region.Sub ⟨blkAddr z s₀ i + BitVec.ofNat 64 (zB z * j), zB z⟩ (blR z s₀) := by
  have hb := blk_bound z hi hj h.nb_lt
  rw [Offset.add_ofNat_add_ofNat]
  exact Offset.sub_base _ hb.1

theorem in_blk {i j : Nat} (hi : i < nb s₀) (hj : j < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr z s₀ i + BitVec.ofNat 64 (zB z * j)) (zB z) :=
  ⟨blR z s₀, by simp [h.rd], h.blk_contains hi hj⟩

/-- A word of the state and a range of the scratch space are disjoint. -/
theorem state_cell {k d n : Nat} (hk : k < 8) (hd : d + n ≤ 504) :
    Region.Disjoint ⟨st s₀ + BitVec.ofNat 64 (zB z * k), zB z⟩ ⟨sb s₀ + BitVec.ofNat 64 d, n⟩ :=
  (h.st_scr.sub_left (word_sub z _ hk)).sub_right (cell_sub s₀ hd)

/-- A word of a block and a range of the scratch space are disjoint. -/
theorem blk_cell {i j d n : Nat} (hi : i < nb s₀) (hj : j < 16) (hd : d + n ≤ 504) :
    Region.Disjoint ⟨blkAddr z s₀ i + BitVec.ofNat 64 (zB z * j), zB z⟩ ⟨sb s₀ + BitVec.ofNat 64 d, n⟩ :=
  (h.blk_scr.sub_left (h.blk_sub hi hj)).sub_right (cell_sub s₀ hd)

/-- A word of the state is unchanged by writes to the scratch space. -/
theorem state_frame {m : Mem} (hf : Frame [scrR s₀] s₀.mem m) {k : Nat} (hk : k < 8) :
    m.readW (st s₀ + BitVec.ofNat 64 (zB z * k)) z.bits =
      s₀.mem.readW (st s₀ + BitVec.ofNat 64 (zB z * k)) z.bits :=
  hf.readW (r := ⟨st s₀ + BitVec.ofNat 64 (zB z * k), zB z⟩) (by rw [bits_div]; exact Region.contains_self _ _)
    (by simpa using h.st_scr.sub_left (word_sub z _ hk)) (by rw [bits_div]; have := zB_le z; omega)

/-- A block word is where it was at the start, when only the scratch space changed. -/
theorem blk_frame {m : Mem} (hf : Frame [scrR s₀] s₀.mem m) {i j : Nat} (hi : i < nb s₀)
    (hj : j < 16) :
    m.readW (blkAddr z s₀ i + BitVec.ofNat 64 (zB z * j)) z.bits =
      Spec.Blake2.blockAt z.bits s₀.mem (blkAddr z s₀ i) ⟨j, hj⟩ := by
  rw [hf.readW (r := ⟨blkAddr z s₀ i + BitVec.ofNat 64 (zB z * j), zB z⟩)
    (by rw [bits_div]; exact Region.contains_self _ _)
    (by simpa using h.blk_scr.sub_left (h.blk_sub hi hj)) (by rw [bits_div]; have := zB_le z; omega),
    blockAt_word, bits_div]

end Pre

/-- The registers the code never writes. -/
def keptRegs : List Reg := [.a0, .ra, .s7, .s8, .s9, .s10, .s11]

theorem kept_ok : ∀ r ∈ keptRegs, r ∉ wregs ∧ r ≠ T ∧ r ≠ RT ∧ r ≠ SB ∧ r ≠ .a1 ∧ r ≠ .a2 ∧
    r ∉ saved.map Prod.fst := by decide

section Loop
variable {z : Size} (P : Params z.bits)

/-- What holds between blocks, after `i` of them: the hash value is at `hOff`
of the scratch space. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  base : s.gpr SB = sb s₀
  kept : ∀ r ∈ keptRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scrR s₀] s₀.mem s.mem
  hv : ∀ k (hk : k < 8), s.mem.readW (sb s₀ + BitVec.ofNat 64 (hOff + zB z * k)) z.bits =
    (Spec.Blake2.compressBlocks P (H₀ z s₀) s₀.mem (bp s₀) i (t₀ s₀) (fl s₀))[k]
  sv : Spill.Saved (sb s₀) s₀.gpr saved s.mem
  lo : s.mem.readW (sb s₀ + BitVec.ofNat 64 loOff) 64 =
    BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes z.bits)
  hi : s.mem.readW (sb s₀ + BitVec.ofNat 64 hiOff) 64 =
    BitVec.ofNat 64 ((t₀ s₀ + i * Spec.Blake2.blockBytes z.bits) / 2 ^ 64)
  f : s.mem.readW (sb s₀ + BitVec.ofNat 64 fOff) 64 = flagW 64 (fl s₀)

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common P s₀ i s where
  a1 : s.gpr .a1 = blkAddr z s₀ i
  a2 : s.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i)

theorem Common.scr {s₀ : State} (hp : Pre z s₀) {i : Nat} {s : State} (h : Common P s₀ i s) :
    Scr (sb s₀) (t₀ s₀ + i * Spec.Blake2.blockBytes z.bits) (flagW 64 (fl s₀)) s :=
  ⟨h.base, sb_al s₀, by rw [h.rd, h.wr]; exact hp.in_cell (by decide),
    by rw [h.rd, h.wr]; exact hp.in_cell (by decide), by rw [h.rd, h.wr]; exact hp.in_cell (by decide),
    h.lo, h.hi, h.f⟩

theorem hcell_bound (z : Size) {k : Nat} (hk : k < 8) : hOff + zB z * k + zB z ≤ 144 := by
  have := zB_mul_le z hk; have := zB_le z; simp only [hOff]; omega

theorem mcell_bound (z : Size) {j : Nat} (hj : j < 16) : mOff + zB z * j + zB z ≤ 272 := by
  have := zB_mul_le z hj; have := zB_le z; simp only [mOff]; omega

/-! ## One block -/

theorem body_ok (hR : ROk P) {s₀ : State} (hp : Pre z s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv P s₀ i s) :
    WP isa (Impl.Blake2.RISCV64.body P) s fun s' =>
      (eval (.nonzero .a2) s' = some false ∧ Common P s₀ (nb s₀) s') ∨
      (eval (.nonzero .a2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv P s₀ (i + 1) s') := by
  have hC := hL.toCommon
  have h8 := zB_le z
  have h16 : mOff + 16 * zB z ≤ 2040 := by simp only [mOff]; omega
  have hmR : 16 * zB z ≤ 16 * 8 := Nat.mul_le_mul_left _ h8
  -- Copy the block.
  refine WP.seq (WP.mono (cp_ok (z := z) (src := .a1) (by decide) (by decide) (by decide)
    (N := 16) (Nat.le_refl _) (by decide) h16 s (by rw [hC.base]; exact sb_al s₀)
    (fun j hj => by rw [hC.rd, hC.wr, hL.a1]; exact hp.in_blk hi hj)
    (fun j hj => by rw [hC.wr, hC.base]; exact hp.out_cell (by have := mcell_bound z hj; omega))
    (fun j hj => by rw [hC.base, hL.a1]; exact hp.blk_cell hi hj (by simp only [mOff]; omega)))
    fun s₁ h₁ => ?_)
  have hf₁ : Frame [⟨sb s₀ + BitVec.ofNat 64 mOff, 16 * zB z⟩] s.mem s₁.mem := hC.base ▸ h₁.frame
  have hsb₁ : s₁.gpr SB = sb s₀ := (h₁.other _ (by decide) (by decide) (by decide)).trans hC.base
  have hc₁ : ∀ {d w : Nat}, d + w / 8 ≤ mOff → s₁.mem.readW (sb s₀ + BitVec.ofNat 64 d) w =
      s.mem.readW (sb s₀ + BitVec.ofNat 64 d) w := fun hd =>
    cell_frame _ hf₁ (.inl hd) (by simp only [mOff] at hd; omega) (by simp only [mOff]; omega)
  have hS₁ : Scr (sb s₀) (t₀ s₀ + i * Spec.Blake2.blockBytes z.bits) (flagW 64 (fl s₀)) s₁ :=
    ⟨hsb₁, sb_al s₀, by rw [h₁.rd, h₁.wr, hC.rd, hC.wr]; exact hp.in_cell (by decide),
      by rw [h₁.rd, h₁.wr, hC.rd, hC.wr]; exact hp.in_cell (by decide),
      by rw [h₁.rd, h₁.wr, hC.rd, hC.wr]; exact hp.in_cell (by decide),
      by rw [hc₁ (by decide)]; exact hC.lo, by rw [hc₁ (by decide)]; exact hC.hi,
      by rw [hc₁ (by decide)]; exact hC.f⟩
  have hin₁ : ∀ k < 8, InRegions (s₁.rd ++ s₁.wr) (sb s₀ + BitVec.ofNat 64 (hOff + zB z * k)) (zB z) :=
    fun k hk => by rw [h₁.rd, h₁.wr, hC.rd, hC.wr]; exact hp.in_cell (by have := hcell_bound z hk; omega)
  have hh₁ : ∀ k (hk : k < 8), s₁.mem.readW (sb s₀ + BitVec.ofNat 64 (hOff + zB z * k)) z.bits =
      (Spec.Blake2.compressBlocks P (H₀ z s₀) s₀.mem (bp s₀) i (t₀ s₀) (fl s₀))[k] := fun k hk => by
    rw [hc₁ (by rw [bits_div]; have := hcell_bound z hk; simp only [mOff]; omega)]; exact hC.hv k hk
  -- Initialize the work vector.
  refine WP.seq (WP.mono (init_ok P s₁ hS₁ hin₁ _ hh₁) fun s₂ ⟨hv₂, ho₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  have hM : Msg (Spec.Blake2.blockAt z.bits s₀.mem (blkAddr z s₀ i)) (sb s₀) s₂ :=
    ⟨(ho₂ _ SB_not_mem (by decide)).trans hsb₁, sb_al s₀,
      fun j hj => by rw [hrd₂, hwr₂, h₁.rd, h₁.wr, hC.rd, hC.wr]; exact hp.in_cell (by have := mcell_bound z hj; omega),
      fun j hj => by
        rw [hm₂, ← hC.base, h₁.words j hj, hL.a1]
        exact hp.blk_frame hC.frame hi hj⟩
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok P hR hM ⟨hv₂, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩ P.r)
    fun s₃ hR₃ => ?_)
  have o₃ : ∀ q, q ∉ wregs → q ≠ T → q ≠ RT → s₃.gpr q = s₁.gpr q := fun q h1 h2 h3 =>
    (hR₃.other q h1 h2 h3).trans (ho₂ q h1 h2)
  have hm₃ : s₃.mem = s₁.mem := hR₃.mem.trans hm₂
  have hrw₃ : s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := ⟨hR₃.rd.trans hrd₂, hR₃.wr.trans hwr₂⟩
  have hsb₃ : s₃.gpr SB = sb s₀ := (o₃ _ SB_not_mem (by decide) (by decide)).trans hsb₁
  -- The new hash value.
  refine WP.seq (WP.mono (fin_ok s₃ (sb s₀) hsb₃ (sb_al s₀)
    (by rw [hrw₃.1, hrw₃.2]; exact hin₁)
    (fun k hk => by rw [hrw₃.2, h₁.wr, hC.wr]; exact hp.out_cell (by have := hcell_bound z hk; omega))
    _ hR₃.vars (Spec.Blake2.compressBlocks P (H₀ z s₀) s₀.mem (bp s₀) i (t₀ s₀) (fl s₀))
    (by rw [hm₃]; exact hh₁) 8 (Nat.le_refl _)) fun s₄ ⟨hf₄, hF₄, ho₄, hrd₄, hwr₄⟩ => ?_)
  have hc₄ : ∀ {d w : Nat}, d + w / 8 ≤ hOff → s₄.mem.readW (sb s₀ + BitVec.ofNat 64 d) w =
      s₁.mem.readW (sb s₀ + BitVec.ofNat 64 d) w := fun hd => by
    rw [cell_frame _ hF₄ (.inl hd) (by simp only [hOff] at hd; omega)
      (by simp only [hOff]; omega), hm₃]
  have hrw₄ : s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr :=
    ⟨by rw [hrd₄, hrw₃.1, h₁.rd, hC.rd], by rw [hwr₄, hrw₃.2, h₁.wr, hC.wr]⟩
  have o₄ : ∀ q, q ∉ wregs → q ≠ T → q ≠ RT → s₄.gpr q = s.gpr q := fun q h1 h2 h3 => by
    rw [ho₄ q h2, o₃ q h1 h2 h3]
    exact h₁.other q h2 (ne_wreg h1 (by decide)) (ne_wreg h1 (by decide))
  have hS₄ : Scr (sb s₀) (t₀ s₀ + i * Spec.Blake2.blockBytes z.bits) (flagW 64 (fl s₀)) s₄ :=
    ⟨(o₄ _ SB_not_mem (by decide) (by decide)).trans hC.base, sb_al s₀,
      by rw [hrw₄.1, hrw₄.2]; exact hp.in_cell (by decide),
      by rw [hrw₄.1, hrw₄.2]; exact hp.in_cell (by decide),
      by rw [hrw₄.1, hrw₄.2]; exact hp.in_cell (by decide),
      by rw [hc₄ (by decide)]; exact hS₁.lo, by rw [hc₄ (by decide)]; exact hS₁.hi,
      by rw [hc₄ (by decide)]; exact hS₁.f⟩
  -- The next block and its counter.
  refine WP.mono (advance_ok s₄ hS₄ (by rw [hrw₄.2]; exact hp.out_cell (by decide))
    (by rw [hrw₄.2]; exact hp.out_cell (by decide)))
    fun s₅ ⟨ha1₅, ha2₅, hm₅, ho₅, hrd₅, hwr₅⟩ => ?_
  have o₅ : ∀ q, q ∉ wregs → q ≠ T → q ≠ RT → q ≠ .a1 → q ≠ .a2 → s₅.gpr q = s.gpr q :=
    fun q h1 h2 h3 h4 h5 => by
      rw [ho₅ q h4 h5 (ne_wreg h1 (by decide)) (ne_wreg h1 (by decide)) (ne_wreg h1 (by decide)),
        o₄ q h1 h2 h3]
  have ha1₄ : s₄.gpr .a1 = blkAddr z s₀ i := (o₄ _ (by decide) (by decide) (by decide)).trans hL.a1
  have ha2₄ : s₄.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i) :=
    (o₄ _ (by decide) (by decide) (by decide)).trans hL.a2
  have ha2 : s₅.gpr .a2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [ha2₅, ha2₄, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hbb : t₀ s₀ + i * Spec.Blake2.blockBytes z.bits + 2 ^ lbb z.bits =
      t₀ s₀ + (i + 1) * Spec.Blake2.blockBytes z.bits := by
    rw [← bb_pow, Nat.succ_mul, Nat.add_assoc]
  have hsc : Frame [scrR s₀] s.mem s₄.mem := by
    have e₁ : Frame [scrR s₀] s.mem s₁.mem :=
      hf₁.sub fun r hr => ⟨scrR s₀, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact cell_sub s₀ (by simp only [mOff]; omega)⟩
    have e₄ : Frame [scrR s₀] s₃.mem s₄.mem :=
      hF₄.sub fun r hr => ⟨scrR s₀, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact cell_sub s₀ (by simp only [hOff]; omega)⟩
    rw [hm₃] at e₄
    exact e₁.trans e₄
  have hcell : ∀ d, d + 8 ≤ loOff ∨ d = fOff →
      s₅.mem.readW (sb s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (sb s₀ + BitVec.ofNat 64 d) 64 := by
    intro d hd
    have h1 : d + 64 / 8 ≤ hiOff ∨ hiOff + 64 / 8 ≤ d := by
      simp only [hiOff, loOff, fOff] at hd ⊢; omega
    have h2 : d + 64 / 8 ≤ loOff ∨ loOff + 64 / 8 ≤ d := by
      simp only [loOff, fOff] at hd ⊢; omega
    have h3 : d + 64 / 8 ≤ hOff := by simp only [hOff, loOff, fOff] at hd ⊢; omega
    rw [hm₅, cell_sep _ _ _ h1 (by simp only [loOff, fOff] at hd ⊢; omega) (by decide),
      cell_sep _ _ _ h2 (by simp only [loOff, fOff] at hd ⊢; omega) (by decide), hc₄ h3,
      hc₁ (by simp only [hOff, mOff] at h3 ⊢; omega)]
  have hcommon : Common P s₀ (i + 1) s₅ := by
    refine ⟨?_, fun r hr => ?_, by rw [hrd₅, hrw₄.1], by rw [hwr₅, hrw₄.2], ?_, fun k hk => ?_,
      fun p hp' => ?_, ?_, ?_, by rw [hcell fOff (.inr rfl)]; exact hC.f⟩
    · rw [o₅ _ SB_not_mem (by decide) (by decide) (by decide) (by decide)]; exact hC.base
    · obtain ⟨a, b, c, _, d, e, -⟩ := kept_ok r hr
      rw [o₅ r a b c d e]; exact hC.kept r hr
    · refine hC.frame.trans ?_
      rw [hm₅]
      exact (hsc.writeW (r := scrR s₀) (List.mem_singleton_self _) _ (cell_contains s₀ (by decide))).writeW
        (r := scrR s₀) (List.mem_singleton_self _) _ (cell_contains s₀ (by decide))
    · have hb := hcell_bound z hk
      rw [hm₅, cell_sep _ _ _ (by rw [bits_div]; simp only [hiOff, hOff] at hb ⊢; omega)
          (by rw [bits_div]; omega) (by decide),
        cell_sep _ _ _ (by rw [bits_div]; simp only [loOff, hOff] at hb ⊢; omega)
          (by rw [bits_div]; omega) (by decide), hf₄ k hk,
        compressBlocks_succ, F_eq, Vector.getElem_ofFn]
      simp only [hk, ite_true, Fin.getElem_fin]
    · rw [hcell _ (.inl (saved_off p hp'))]; exact hC.sv p hp'
    · rw [hm₅, cell_sep _ _ _ (d := loOff) (e := hiOff) (by decide) (by decide) (by decide),
        Mem.readW_writeW_self64, hbb]
    · rw [hm₅, Mem.readW_writeW_self64, hbb]
  have hev : eval (.nonzero .a2) s₅ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    rw [Wp.eval_nonzero, ha2]
  have := hp.nb_lt
  have hnb : nb s₀ < 2 ^ 64 := (s₀.gpr .a2).isLt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon with a1 := ?_, a2 := ha2 }⟩
    rw [ha1₅, ha1₄, Offset.add_ofNat_add_ofNat, ← bb_pow, ← Nat.mul_succ]

/-! ## The whole function -/

theorem saved_fst : ∀ p ∈ saved, p.1 ≠ SB := by decide

open VG.RISCV64.Wp in
theorem setup_ok {s₀ : State} (hp : Pre z s₀) :
    WP isa (.block (Impl.Blake2.RISCV64.setup (w := z.bits))) s₀ (LInv P s₀ 0) := by
  have h8 := zB_le z
  rw [setup_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine wp_addiI (show imm12 7 by decide) fun s₁ u₁ => ?_
  refine wp_andi (show imm12 (-8) by decide) fun s₂ u₂ =>
    WP.block_nil (M := isa) ?_
  rw [u₁.gpr, align_eq] at u₂
  have hsb₂ : s₂.gpr SB = sb s₀ := u₂.gpr
  have go₂ : ∀ r, r ≠ SB → s₂.gpr r = s₀.gpr r := fun r hr => by rw [u₂.other r hr, u₁.other r hr]
  have hm₂ : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
  have hwr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  have hrd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd]
  refine WP.mono (Spill.save_wp (by rw [hsb₂]; exact sb_al s₀) saved_fits
    (fun p hp' => by rw [hsb₂, hwr₂]; exact hp.out_cell (by have := saved_off p hp'; simp only [loOff] at this; omega)))
    fun s₃ h₃ => ?_
  rw [hsb₂, hm₂] at h₃
  refine WP.mono (ctrF_ok s₃ (sb s₀) (by rw [h₃.gpr, hsb₂]) (sb_al s₀)
    (fun d hd => by
      rw [h₃.wr, hwr₂]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> exact hp.out_cell (by decide)))
    fun s₄ ⟨hm₄, ho₄, hrd₄, hwr₄⟩ => ?_
  have go₄ : ∀ r, r ≠ SB → r ≠ .a3 → r ≠ .a4 → r ≠ T → s₄.gpr r = s₀.gpr r := fun r h0 h3 h4 hT => by
    rw [ho₄ r h3 h4 hT, h₃.gpr, go₂ r h0]
  have hsb₄ : s₄.gpr SB = sb s₀ := by rw [ho₄ _ (by decide) (by decide) (by decide), h₃.gpr, hsb₂]
  have hrw₄ : s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr := ⟨by rw [hrd₄, h₃.rd, hrd₂], by rw [hwr₄, h₃.wr, hwr₂]⟩
  have ha0₄ : s₄.gpr .a0 = st s₀ := go₄ _ (by decide) (by decide) (by decide) (by decide)
  have hf₄ : Frame [scrR s₀] s₀.mem s₄.mem := by
    have hs : Frame [scrR s₀] s₀.mem (Spill.saveMem s₀.mem (sb s₀) s₂.gpr saved) :=
      (Spill.saveMem_frame_base (n := 56) (fun p hp' => saved_off p hp') (by decide) _ _ _).sub
        fun r hr => ⟨scrR s₀, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr
          have := cell_sub s₀ (d := 0) (n := 56) (by decide)
          simpa using this⟩
    rw [hm₄, h₃.mem, h₃.gpr]
    exact ((hs.writeW (List.mem_singleton_self _) _ (cell_contains s₀ (by decide))).writeW
      (List.mem_singleton_self _) _ (cell_contains s₀ (by decide))).writeW
      (List.mem_singleton_self _) _ (cell_contains s₀ (by decide))
  refine WP.mono (cp_ok (z := z) (src := .a0) (by decide) (by decide) (by decide) (N := 8)
    (by decide) (by decide) (by simp only [hOff]; omega) s₄ (by rw [hsb₄]; exact sb_al s₀)
    (fun j hj => by rw [hrw₄.1, hrw₄.2, ha0₄]; exact hp.in_state hj)
    (fun j hj => by rw [hrw₄.2, hsb₄]; exact hp.out_cell (by have := hcell_bound z hj; omega))
    (fun j hj => by rw [hsb₄, ha0₄]; exact hp.state_cell hj (by simp only [hOff]; omega)))
    fun s₅ h₅ => ?_
  have hF₅ : Frame [⟨sb s₀ + BitVec.ofNat 64 hOff, 16 * zB z⟩] s₄.mem s₅.mem := hsb₄ ▸ h₅.frame
  have hc₅ : ∀ {d w : Nat}, d + w / 8 ≤ hOff → s₅.mem.readW (sb s₀ + BitVec.ofNat 64 d) w =
      s₄.mem.readW (sb s₀ + BitVec.ofNat 64 d) w := fun hd =>
    cell_frame _ hF₅ (.inl hd) (by simp only [hOff] at hd; omega) (by simp only [hOff]; omega)
  have hsv₂ : Spill.Saved (sb s₀) s₀.gpr saved (Spill.saveMem s₀.mem (sb s₀) s₂.gpr saved) :=
    fun p hp' => by
      rw [Spill.saveMem_saved (by decide) _ _ _ p hp', go₂ _ (saved_fst p hp')]
  refine ⟨⟨?_, fun r hr => ?_, by rw [h₅.rd, hrw₄.1], by rw [h₅.wr, hrw₄.2], ?_, fun k hk => ?_,
    fun p hp' => ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [h₅.other _ (by decide) (by decide) (by decide), hsb₄]
  · obtain ⟨a, b, c, d, -, -, -⟩ := kept_ok r hr
    rw [h₅.other r b (ne_wreg a (k := 0) (by decide)) (ne_wreg a (k := 1) (by decide)),
      go₄ r d (ne_wreg a (k := 0) (by decide)) (ne_wreg a (k := 1) (by decide)) b]
  · refine hf₄.trans (hF₅.sub fun r hr => ⟨scrR s₀, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_sub s₀ (by simp only [hOff]; omega)
  · have w := h₅.words k hk
    rw [hsb₄, ha0₄] at w
    rw [w, hp.state_frame hf₄ hk, ← stateAt_get' z _ _ hk]
    rfl
  · have := saved_off p hp'
    rw [hc₅ (by simp only [loOff, hOff] at this ⊢; omega), hm₄, h₃.mem, h₃.gpr,
      cell_sep _ _ _ (e := fOff) (by simp only [loOff, fOff] at *; omega) (by simp only [loOff] at *; omega) (by decide),
      cell_sep _ _ _ (e := hiOff) (by simp only [loOff, hiOff] at *; omega) (by simp only [loOff] at *; omega) (by decide),
      cell_sep _ _ _ (e := loOff) (by simp only [loOff] at *; omega) (by simp only [loOff] at *; omega) (by decide)]
    exact hsv₂ p hp'
  · rw [hc₅ (by decide), hm₄, cell_sep _ _ _ (d := loOff) (e := fOff) (by decide) (by decide) (by decide),
      cell_sep _ _ _ (d := loOff) (e := hiOff) (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64, h₃.gpr, go₂ _ (by decide), Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [hc₅ (by decide), hm₄, cell_sep _ _ _ (d := hiOff) (e := fOff) (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64, Nat.zero_mul, Nat.add_zero, Nat.div_eq_of_lt (s₀.gpr .a3).isLt]
  · rw [hc₅ (by decide), hm₄, Mem.readW_writeW_self64, h₃.gpr, go₂ _ (by decide)]
  · rw [h₅.other _ (by decide) (by decide) (by decide),
      go₄ _ (by decide) (by decide) (by decide) (by decide)]
    simp [blkAddr]
  · rw [h₅.other _ (by decide) (by decide) (by decide),
      go₄ _ (by decide) (by decide) (by decide) (by decide)]
    simp [nb]

theorem correct (hR : ROk P) {s₀ : State} (hp : Pre z s₀) :
    WP isa (Impl.Blake2.RISCV64.compress P) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      (compressRISCV64 P).post s₀ s' := by
  refine WP.seq (WP.mono (setup_ok P hp) fun s₁ hL₀ => ?_)
  have hc₁ := hL₀.toCommon
  have ha2₁ : s₁.gpr .a2 = s₀.gpr .a2 := by rw [hL₀.a2]; simp [nb]
  refine WP.seq (WP.mono (Q := Common P s₀ (nb s₀)) ?_ fun s₂ hc => ?_)
  · refine WP.ite (s₁.gpr .a2 == 0) (Wp.eval_zero _ _) (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by rw [ha2₁] at h; simp at h; simp [nb, h]
      exact WP.block_nil (M := isa) (h0 ▸ hc₁)
    · have hpos : 0 < nb s₀ := by
        rw [ha2₁] at h
        simp only [beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv P s₀ i s
      have hstep : ∀ m s, Inv m s → WP isa (Impl.Blake2.RISCV64.body P) s (fun s' =>
          (eval (.nonzero .a2) s' = some false ∧ Common P s₀ (nb s₀) s') ∨
          (eval (.nonzero .a2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
        rintro m s ⟨i, rfl, hi, hL⟩
        refine WP.mono (body_ok P hR hp hi hL) fun s' h => ?_
        rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
        · exact .inl ⟨he, hc⟩
        · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
      exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩
  · have h8 := zB_le z
    have ha0 : s₂.gpr .a0 = st s₀ := hc.kept _ (by decide)
    have hcs : ∀ {d n : Nat}, d + n ≤ 504 →
        Region.Disjoint ⟨sb s₀ + BitVec.ofNat 64 d, n⟩ ⟨s₂.gpr .a0, 8 * zB z⟩ := fun hd => by
      rw [ha0]; exact hp.st_scr.symm.sub_left (cell_sub s₀ hd)
    unfold Impl.Blake2.RISCV64.epilogue
    rw [WP.block_append_iff]
    refine WP.mono (cpOut_ok (z := z) s₂ (by rw [hc.base]; exact sb_al s₀)
      (fun j hj => by rw [hc.rd, hc.wr, hc.base]; exact hp.in_cell (by have := hcell_bound z hj; omega))
      (fun j hj => by rw [hc.wr, ha0]; exact hp.out_state hj)
      (fun j hj => by rw [hc.base]; exact hcs (by have := hcell_bound z hj; omega))) fun s₃ h₃ => ?_
    have hsv : Spill.Saved (sb s₀) s₀.gpr saved s₃.mem :=
      hc.sv.frame h₃.frame fun p hp' r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hcs (by have := saved_off p hp'; simp only [loOff] at this; omega)
    rw [restore_eq]
    refine WP.mono (Spill.restore_wp (sb_al s₀)
      (by rw [h₃.other _ (by decide) (by decide) (by decide), hc.base]) saved_fits (by decide)
      (fun p hp' => by
        rw [h₃.rd, h₃.wr, hc.rd, hc.wr]
        exact hp.in_cell (by have := saved_off p hp'; simp only [loOff] at this; omega)) hsv)
      fun s₄ h₄ => ⟨fun r hr => ?_, ?_, ?_⟩
    · by_cases hs : r ∈ saved.map Prod.fst
      · exact h₄.gpr_of (.inl hs)
      · have hk : r ∈ keptRegs := by revert hr hs; revert r; decide
        obtain ⟨a, b, -⟩ := kept_ok r hk
        rw [h₄.other r hs, h₃.other r b (ne_wreg a (k := 0) (by decide)) (ne_wreg a (k := 1) (by decide))]
        exact hc.kept r hk
    · rw [h₄.other _ (by decide), h₃.other _ (by decide) (by decide) (by decide)]
      exact hc.kept _ (by decide)
    · show Spec.Blake2.stateAt z.bits s₄.mem (st s₀) = _
      rw [h₄.mem]
      refine stateAt_eq' fun k hk => ?_
      rw [← ha0, h₃.words k hk, hc.base, hc.hv k hk]

end Loop

end VG.Proof.Blake2.RISCV64
