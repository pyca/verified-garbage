module
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest

/-! # Fixed-length word scans for DSA validation -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure OrWordsInv (s₀ : State) (B : Addr) (Z e : Nat) (A : Prop) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x15, .x14, .x16] s₀ t
  mem : t.mem = s₀.mem
  pointer : t.gpr .x16 = off B (e + 8 * j)
  val : t.gpr .x15 = 0 ↔ A ∧ ∀ i < j, word s₀.mem B (e + 8 * i) = 0

theorem orWordsStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {A : Prop}
    (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State} (hI : OrWordsInv s₀ B Z e A j t) :
    WP isa (.block (([ld .x3 .x16, .logic .orr .x .x15 .x15 .x3, next .x16] : List Instr) ++
      ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      OrWordsInv s₀ B Z e A (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x15, .x16] (Q := fun u => u.mem = t.mem ∧
    u.gpr .x15 = t.gpr .x15 ||| word t.mem B (e + 8 * j) ∧
    u.gpr .x16 = off B (e + 8 * j + 8))
    (by brun [hI.pointer, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega)]) rfl rfl rfl)
    fun u ⟨⟨hm, hv, hp⟩, hk⟩ => ?_
  refine WP.mono (dec_ok u .x14) fun v ⟨⟨hn, hvm, _⟩, hkv⟩ => ⟨?_, by rw [hn, hk.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (hkv.wr.trans hk.wr), ((hI.keep.trans hk).trans hkv).mono (by decide),
    hvm.trans (hm.trans hI.mem), ?_, ?_⟩
  · rw [hkv.gpr .x16 (by decide), hp, Nat.mul_succ, Nat.add_assoc]
  · rw [hkv.gpr .x15 (by decide), hv, or_eq_zero, hI.val, hI.mem]
    constructor
    · rintro ⟨⟨ha, h⟩, hb⟩
      refine ⟨ha, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      exacts [h i hi, hb]
    · rintro ⟨ha, h⟩
      exact ⟨⟨ha, fun i hi => h i (by omega)⟩, h j (by omega)⟩

theorem orWords_ok {s : State} {B : Addr} {Z w e : Nat} {A : Prop}
    (hs : Scr s B Z) (hp : s.gpr .x16 = off B e)
    (hn : s.gpr .x14 = BitVec.ofNat 64 w) (hv : s.gpr .x15 = 0 ↔ A)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 64) (he : e + 8 * w ≤ Z) :
    WP isa (countLoop .x14 [ld .x3 .x16, .logic .orr .x .x15 .x15 .x3, next .x16]) s fun t =>
      (t.gpr .x15 = 0 ↔ A ∧ ∀ i < w, word s.mem B (e + 8 * i) = 0) ∧
      t.mem = s.mem ∧ Keep [.x3, .x15, .x14, .x16] s t := by
  have h0 : OrWordsInv s B Z e A 0 s :=
    ⟨hs, Keep.refl _ _, rfl, by simpa using hp, by simpa using hv⟩
  exact WP.mono (wp_countdown hw' (by omega) (OrWordsInv s B Z e A)
    (fun j hj t hi _ => orWordsStep_ok he hj hi) h0 hn) fun t hi => ⟨hi.val, hi.mem, hi.keep⟩

end VG.Proof.Dsa.AArch64
