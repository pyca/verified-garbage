module
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # Wordwise zero checks for DSA validation masks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- After `j` words of a loop that ORs words `1, 2, …` into `r15`. -/
structure OrWordsInv (s₀ : State) (B : Addr) (Z e : Nat) (A : Prop) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .r15, .r14] s₀ t
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  val : t.gpr .r15 = 0 ↔ (A ∧ ∀ i, 1 ≤ i → i < j → word s₀.mem B (e + 8 * i) = 0)

theorem orWordsStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {A : Prop}
    (hbx : s₀.gpr .rbx = off B e) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z) {j : Nat} (hj1 : 1 ≤ j) (hj : j < w) {t : State} (hI : OrWordsInv s₀ B Z e A j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)] : List Instr) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ OrWordsInv s₀ B Z e A (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B e := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r15] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .r15 = t.gpr .r15 ||| word t.mem B (e + 8 * j)) ?_ rfl)
    fun t₁ ⟨⟨hm, hbp⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tbx hI.r14, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega_arith)]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], h14, ?_⟩
  rw [(k'.gpr (by decide) : t'.gpr .r15 = t₁.gpr .r15), hbp, or_eq_zero, hI.val, hI.mem]
  constructor
  · rintro ⟨⟨hA, h1⟩, h2⟩
    refine ⟨hA, fun i hi1 hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    exacts [h1 i hi1 hi, h2]
  · rintro ⟨hA, h⟩
    exact ⟨⟨hA, fun i hi1 hi => h i hi1 (by omega_arith)⟩, h j hj1 (by omega_arith)⟩

/-- OR the high limbs into an accumulator that already describes the low limb. -/
theorem orWords_ok {s : State} {B : Addr} {Z w e : Nat} {A : Prop}
    (hs : Scr s B Z) (hbx : s.gpr .rbx = off B e)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h15 : s.gpr .r15 = 0 ↔ A)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (he : e + 8 * w ≤ Z) :
    WP isa (wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)]) s fun t =>
      (t.gpr .r15 = 0 ↔ A ∧ ∀ i, 1 ≤ i → i < w → word s.mem B (e + 8 * i) = 0) ∧
      t.mem = s.mem ∧ Keep [.rax, .r15, .r14] s t := by
  refine WP.mono (wordLoop_ok (start := 1) (N := w) (by omega) hw' (OrWordsInv s B Z e A)
    (fun t h14 hm hk _ => ⟨hs.congr hk.2.2, hk.mono (by decide), hm, h14, ?_⟩)
    (fun j hj1 hj t hi => orWordsStep_ok hbx h12 (by omega) he hj1 hj hi))
    fun t hi => ⟨hi.val, hi.mem, hi.keep⟩
  rw [(hk.gpr (by decide) : t.gpr .r15 = s.gpr .r15), h15]
  exact ⟨fun h => ⟨h, fun i hi1 hi => by omega⟩, fun h => h.1⟩

end VG.Proof.Dsa.X86_64
