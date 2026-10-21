module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass1
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Idx
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Block

/-!
# ML-KEM's 16-bit NTT on AArch64: pass 2

What the inverse NTT's passes share with the forward NTT's pass 2: the
halfwords of a table built block by block (`flatMap_getD`), the offsets of a
block (`seg`), a vector loaded (`ld_step`), and zetas spread to every lane
(`zrep_dup`, `trep_dup`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## The table -/

theorem length_flatMap_range (f : Nat → List Nat) (hf : ∀ b, (f b).length = 32) :
    ∀ n, ((List.range n).flatMap f).length = 32 * n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
      length_flatMap_range f hf n, hf]
    omega

theorem flatMap_getD (f : Nat → List Nat) (hf : ∀ b, (f b).length = 32) :
    ∀ n b i, b < n → i < 32 → ((List.range n).flatMap f).getD (32 * b + i) 0 = (f b).getD i 0 := by
  intro n
  induction n with
  | zero => intro b i hb; omega
  | succ n ih =>
    intro b i hb hi
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hl := length_flatMap_range f hf n
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    by_cases h : b < n
    · rw [ite_eq_left (by omega), ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
      exact ih b i h hi
    · have : b = n := by omega
      subst this
      rw [ite_eq_right (by omega), show 32 * b + i - 32 * b = i by omega]

/-! ## Offsets -/

/-- The offsets `a, a + 1, …, a + 7`. -/
def seg (a : Nat) : List Nat := (List.range 8).map (a + ·)

theorem seg_getD (a : Nat) {e : Nat} (he : e < 8) : (seg a).getD e 0 = a + e := by
  rw [seg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]; rfl

/-! ## A block -/

section
variable {rest : List Instr} {Q : State → Prop}

/-- A load, from a state `w` that differs from `s` only in vector registers. -/
theorem ld_step {s w : State} {rs : List VReg} (cw : VChg rs s w) {t : VReg} {n : Reg} {off : Nat}
    {a : Addr} (ho : off % 16 = 0 ∧ off < 4096 * 16) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ w', VChg (rs ++ [t]) s w' → w'.v t = s.mem.read a 16 → (∀ r, r ≠ t → w'.v r = w.v r) →
      WP isa (.block rest) w' Q) :
    WP isa (.block (.ldrq t n off :: rest)) w Q := by
  rw [← cw.gpr] at ha
  rw [← cw.rd, ← cw.wr] at hin
  refine wp_ldrq ho ha hin fun w' h' => k w' (cw.trans h'.chg) (by rw [h'.v, cw.mem]) h'.other

/-! ## Zetas -/

theorem zrep_dup {x : BitVec 128} {k K K₀ : Nat} {kz : List Nat}
    (hx : vhalf x k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta K))
    (hK : ∀ e < 8, K₀ + kz.getD e 0 = K) : ZRep (ofVHalves fun _ => vhalf x k) K₀ kz :=
  fun e he => by dsimp only; rw [vhalf_ofVHalves _ he, hx, hK e he]

theorem trep_dup {x : BitVec 128} {k K K₀ : Nat} {kz : List Nat}
    (hx : vhalf x k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta K)))
    (hK : ∀ e < 8, K₀ + kz.getD e 0 = K) : TRep (ofVHalves fun _ => vhalf x k) K₀ kz :=
  fun e he => by dsimp only; rw [vhalf_ofVHalves _ he, hx, hK e he]

theorem row_ne2425 : ∀ i < 8, row i ≠ .v24 ∧ row i ≠ .v25 := by decide

end

end VG.Proof.MlKem.AArch64.Ntt16
