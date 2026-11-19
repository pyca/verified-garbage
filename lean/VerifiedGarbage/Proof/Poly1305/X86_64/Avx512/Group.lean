module

import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.ModEq
public import VerifiedGarbage.Proof.Poly1305.Horner
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Load
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Powers

/-! ### `Poly1305.X86_64.Avx512.Powers`, which this module and modules that import it used -/

section

/-!
# Poly1305 on x86-64 with AVX-512: the powers of `r`

`powers` leaves `r⁸` in the low doubleword of every quadword of `Y` and `r^(8 -
π k)` in the high doubleword of quadword `k`, each as limbs below `2²⁷`: `r²`,
then `(r⁴, r³)` in each lane, then `(r^(4 - j), r^(4 - j))` in lane `j`
multiplied by `(r⁴, 1)`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr or_lo ext5 mul_ge val_congr
  mul_modEq rN hreg_ge yreg_ge)
open VG.Spec.Poly1305 (P)

/-- The high doublewords of `Y`, and the limbs of `D`. -/
def yh (s : State) (k i : Nat) : Nat := (qz s (yreg i) k).toNat / 2 ^ 32
def dv (s : State) (k i : Nat) : Nat := (qz s (dreg i) k).toNat

theorem yh_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : yh s k j = yh s k 4 := by
  simp only [yh, yreg_ge h]

theorem cases5 {i : Nat} (hi : i < 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_arith

/-- `f` holds the limbs of `r10 + 2⁶⁴ r11` (of `s`), as `split` computes
them. (Stated inline, as in `Limbs26`: a definition whose body divides would
be unfolded by `rfl`, very slowly.) -/
def SplitOf (s : State) (f : Nat → Nat) : Prop :=
  f 0 = (s.gpr .r10).toNat * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
  f 1 = (s.gpr .r10).toNat * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
  f 2 = ((s.gpr .r11).toNat * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| (s.gpr .r10).toNat / 2 ^ 52) ∧
  f 3 = (s.gpr .r11).toNat * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
  f 4 = (s.gpr .r11).toNat / 2 ^ 40

theorem SplitOf.eq {s : State} {f g : Nat → Nat} (hf : SplitOf s f) (hg : SplitOf s g) :
    ∀ i < 5, f i = g i := by
  intro i hi
  obtain ⟨a0, a1, a2, a3, a4⟩ := hf
  obtain ⟨b0, b1, b2, b3, b4⟩ := hg
  rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

theorem SplitOf.val {s : State} {f : Nat → Nat} (hf : SplitOf s f) : Limbs26.val f = rN s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := hf
  rw [Limbs26.val, a0, a1, a2, a3, a4, rN]
  exact Limbs26.split_val (s.gpr .r10).isLt _

theorem SplitOf.lt {s : State} {f : Nat → Nat} (hf : SplitOf s f) : ∀ i < 5, f i < 2 ^ 26 := by
  intro i hi
  obtain ⟨a0, a1, a2, a3, a4⟩ := hf
  have l := (s.gpr .r10).isLt
  have m := (s.gpr .r11).isLt
  rw [Limbs26.split_or l] at a2
  rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
  · rw [a0]; omega_arith
  · rw [a1]; omega_arith
  · rw [a2]; omega_arith
  · rw [a3]; omega_arith
  · rw [a4]; omega_arith

theorem SplitOf.congr {s s' : State} (hg : s'.gpr = s.gpr) {f : Nat → Nat} (hf : SplitOf s f) :
    SplitOf s' f := by
  simp only [SplitOf, hg]; exact hf

/-! ## `r` into `D` and `H` -/

def lrS : Sym := (Sym.init.run false loadRv).get (by decide +kernel)
theorem lrS_eq : Sym.init.run false loadRv = some lrS := (Option.some_get _).symm

section
variable (E : Env) (k : Nat)
theorem lrS_h0 : (lrS.reg (xi (hreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_h1 : (lrS.reg (xi (hreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_h2 : (lrS.reg (xi (hreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem lrS_h3 : (lrS.reg (xi (hreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_h4 : (lrS.reg (xi (hreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
theorem lrS_d0 : (lrS.reg (xi (dreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_d1 : (lrS.reg (xi (dreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_d2 : (lrS.reg (xi (dreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem lrS_d3 : (lrS.reg (xi (dreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_d4 : (lrS.reg (xi (dreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
end

def srS : Sym := (Sym.init.run false splitR).get (by decide +kernel)
theorem srS_eq : Sym.init.run false splitR = some srS := (Option.some_get _).symm
theorem srS_keep : ∀ i < 5, srS.reg (xi (hreg i)) = .reg (xi (hreg i)) ∧
    srS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

section
variable (E : Env) (k : Nat)
theorem srS_d0 : (srS.reg (xi (dreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem srS_d1 : (srS.reg (xi (dreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem srS_d2 : (srS.reg (xi (dreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem srS_d3 : (srS.reg (xi (dreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem srS_d4 : (srS.reg (xi (dreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
end

theorem loadRv_ok (s : State) :
    WP isa (.block loadRv) s fun s' => vec s s' = s' ∧
      ∀ k < 8, SplitOf s (hv s' k) ∧ SplitOf s (dv s' k) := by
  refine WP.mono (run_ok (by intro h; cases h) lrS_eq) fun s' h => ⟨h.eq, fun k hk => ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hv] <;> rw [h.natw _ hk]
    · rw [lrS_h0]; rfl
    · rw [lrS_h1]; rfl
    · rw [lrS_h2]; rfl
    · rw [lrS_h3]; rfl
    · rw [lrS_h4]; rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [dv] <;> rw [h.natw _ hk]
    · rw [lrS_d0]; rfl
    · rw [lrS_d1]; rfl
    · rw [lrS_d2]; rfl
    · rw [lrS_d3]; rfl
    · rw [lrS_d4]; rfl

theorem splitR_ok (s : State) :
    WP isa (.block splitR) s fun s' => vec s s' = s' ∧
      ∀ k < 8, SplitOf s (dv s' k) ∧ ∀ i < 5, qz s' (hreg i) k = qz s (hreg i) k ∧
        qz s' (yreg i) k = qz s (yreg i) k := by
  refine WP.mono (run_ok (by intro h; cases h) srS_eq) fun s' h => ⟨h.eq, fun k hk => ⟨?_, fun i hi => ⟨?_, ?_⟩⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [dv] <;> rw [h.natw _ hk]
    · rw [srS_d0]; rfl
    · rw [srS_d1]; rfl
    · rw [srS_d2]; rfl
    · rw [srS_d3]; rfl
    · rw [srS_d4]; rfl
  · rw [h.reg _ k hk, (srS_keep i hi).1]; simp only [Q.eval, xr_xi]
  · rw [h.reg _ k hk, (srS_keep i hi).2]; simp only [Q.eval, xr_xi]

/-! ## `initY` -/

def initS : Sym := (Sym.init.run false initY).get (by decide +kernel)
theorem initS_eq : Sym.init.run false initY = some initS := (Option.some_get _).symm
theorem initS_shape : ∀ i < 5, initS.reg (xi (yreg i)) =
      .or (.reg (xi (hreg i))) (.shl (.reg (xi (hreg i))) 32) ∧
    initS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem initY_ok {s : State} (hh : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 32) :
    WP isa (.block initY) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      hv s' k i = hv s k i ∧ yl s' k i = hv s k i ∧ yh s' k i = hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) initS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ?_⟩
  have e : (qz s' (yreg i) k).toNat = hv s k i * 2 ^ 32 + hv s k i := by
    rw [h.natw _ hk, (initS_shape i hi).1]
    have := hh k hk i hi
    simp only [Q.natw, envOf_v, hv] at this ⊢
    rw [show (qz s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qz s (hreg i) k).toNat * 2 ^ 32 by omega_arith,
      Nat.or_comm, or_lo this]
  have := hh k hk i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv]; rw [h.reg _ k hk, (initS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl]; rw [e]; omega_arith
  · simp only [yh]; rw [e]; omega_arith

/-! ## `pairs` -/

def prS : Sym := (Sym.init.run false pairs).get (by decide +kernel)
theorem prS_eq : Sym.init.run false pairs = some prS := (Option.some_get _).symm
theorem prS_shape : ∀ i < 5, prS.reg (xi (hreg i)) =
      .unpl (.reg (xi (hreg i))) (.shr (.reg (xi (yreg i))) 32) ∧
    prS.reg (xi (yreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem pairs_ok (s : State) :
    WP isa (.block pairs) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      hv s' k i = (if k % 2 = 0 then hv s k i else yh s (k - 1) i) ∧
      (qz s' (yreg i) k).toNat = hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) prS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [hv, yh]
    rw [h.natw _ hk, (prS_shape i hi).1]
    simp only [Q.natw, envOf_v]
  · rw [h.natw _ hk, (prS_shape i hi).2]
    simp only [Q.natw, envOf_v, hv]

/-! ## `spread` -/

def spS : Sym := (Sym.init.run false spread).get (by decide +kernel)
theorem spS_eq : Sym.init.run false spread = some spS := (Option.some_get _).symm

/-- Lane `j` of each `H_i` becomes quadword `0` of `H_i` (`j = 0`), quadword
`1` of `H_i`, quadword `0` of `Y_i`, or quadword `0` of `D_i` (`j = 3`). -/
def spH (E : Env) (i k : Nat) : Nat :=
  if k / 2 = 0 then E.v (xi (hreg i)) 0 else if k / 2 = 1 then E.v (xi (hreg i)) 1
  else if k / 2 = 2 then E.v (xi (yreg i)) 0 else E.v (xi (dreg i)) 0

/-- Each `Y_i` becomes `(H_i[0], 1)` in each lane (`1` as limbs, from `rax`). -/
def spY (E : Env) (i k : Nat) : Nat :=
  if k % 2 = 0 then E.v (xi (hreg i)) 0
  else if i = 0 then E.g .rax else (2 ^ 64 - 1 - E.g .rax) &&& E.g .rax

theorem spS_h (E : Env) : ∀ i < 5, ∀ k < 8, (spS.reg (xi (hreg i))).natw E k = spH E i k := by
  intro i hi k hk
  -- Every case in one equation, which the kernel checks with `spS` evaluated once.
  obtain h : ((List.range 5).map fun i => (List.range 8).map fun k => (spS.reg (xi (hreg i))).natw E k) =
      (List.range 5).map fun i => (List.range 8).map fun k => spH E i k := by kernel_rfl
  have h' := congrArg (fun l : List (List Nat) => l[i]?.bind (·[k]?)) h
  simpa only [List.getElem?_map, List.getElem?_range hi, List.getElem?_range hk, Option.map_some,
    Option.bind_some, Option.some.injEq] using h'

theorem spS_y (E : Env) : ∀ i < 5, ∀ k < 8, (spS.reg (xi (yreg i))).natw E k = spY E i k := by
  intro i hi k hk
  -- Every case in one equation, which the kernel checks with `spS` evaluated once.
  obtain h : ((List.range 5).map fun i => (List.range 8).map fun k => (spS.reg (xi (yreg i))).natw E k) =
      (List.range 5).map fun i => (List.range 8).map fun k => spY E i k := by kernel_rfl
  have h' := congrArg (fun l : List (List Nat) => l[i]?.bind (·[k]?)) h
  simpa only [List.getElem?_map, List.getElem?_range hi, List.getElem?_range hk, Option.map_some,
    Option.bind_some, Option.some.injEq] using h'

/-- The limbs of 1. -/
def one (i : Nat) : Nat := if i = 0 then 1 else 0

theorem one_val : Limbs26.val one = 1 := rfl

theorem spread_ok {s : State} (hax : s.gpr .rax = 1) :
    WP isa (.block spread) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      hv s' k i = (if k / 2 = 0 then hv s 0 i else if k / 2 = 1 then hv s 1 i
        else if k / 2 = 2 then (qz s (yreg i) 0).toNat else dv s 0 i) ∧
      (qz s' (yreg i) k).toNat = if k % 2 = 0 then hv s 0 i else one i := by
  refine WP.mono (run_ok (by intro h; cases h) spS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [hv]
    rw [h.natw _ hk, spS_h _ i hi k hk]
    simp only [spH, envOf_v, dv]
  · rw [h.natw _ hk, spS_y _ i hi k hk]
    have ax : (envOf s).g .rax = 1 := by simp only [envOf, hax]; rfl
    simp only [spY, ax, one, envOf_v, hv]
    split
    · rfl
    · split <;> decide

/-! ## `finishY` -/

def fyS : Sym := (Sym.init.run false finishY).get (by decide +kernel)
theorem fyS_eq : Sym.init.run false finishY = some fyS := (Option.some_get _).symm
theorem fyS_shape : ∀ i < 5, fyS.reg (xi (yreg i)) =
      .or (.shl (.reg (xi (hreg i))) 32) (.bc (.reg (xi (hreg i)))) ∧
    fyS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem finishY_ok {s : State} (hh : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 32) :
    WP isa (.block finishY) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      hv s' k i = hv s k i ∧ yl s' k i = hv s 0 i ∧ yh s' k i = hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) fyS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ?_⟩
  have e : (qz s' (yreg i) k).toNat = hv s k i * 2 ^ 32 + hv s 0 i := by
    rw [h.natw _ hk, (fyS_shape i hi).1]
    have := hh k hk i hi
    have := hh 0 (by decide) i hi
    simp only [Q.natw, envOf_v, hv] at *
    rw [show (qz s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qz s (hreg i) k).toNat * 2 ^ 32 by omega_arith,
      or_lo (by omega_arith)]
  have := hh k hk i hi
  have := hh 0 (by decide) i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv]; rw [h.reg _ k hk, (fyS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl]; rw [e]; omega_arith
  · simp only [yh]; rw [e]; omega_arith

/-! ## The powers -/

/-- What `powers` leaves in `Y`, for `r = R`. -/
structure YInv (s : State) (R : Nat) : Prop where
  lo : ∀ k < 8, Limbs26.val (yl s k) ≡ R ^ 8 [MOD P]
  hi : ∀ k < 8, Limbs26.val (yh s k) ≡ R ^ (8 - pi k) [MOD P]
  lob : ∀ k < 8, ∀ i < 5, yl s k i < 2 ^ 27
  hib : ∀ k < 8, ∀ i < 5, yh s k i < 2 ^ 27

def powersV : List Instr :=
  loadRv ++ (initY ++ (mul ++ (pairs ++ (mul ++ (splitR ++ (spread ++ (mul ++ finishY)))))))

theorem powers_eq : powers = loadRg ++ powersV := by
  simp only [powers, powersV, List.append_assoc]

/-- Limb functions equal below 5 (and both repeating limb 4) are equal. -/
theorem fext {f g : Nat → Nat} (hf : ∀ j, 4 ≤ j → f j = f 4) (hg : ∀ j, 4 ≤ j → g j = g 4)
    (h : ∀ i < 5, f i = g i) : f = g := ext5 hf hg h

theorem one_ge {j : Nat} (h : 4 ≤ j) : one j = one 4 := by
  simp only [one, show j ≠ 0 by omega_arith, show (4 : Nat) ≠ 0 by decide, ite_false]

theorem one_lt {i : Nat} : one i < 2 ^ 27 := by
  simp only [one]; split <;> decide

/-- Limbs by lane: `a` in lane 0, `b` in lane 1, `c` in lane 2 and `d` in lane 3. -/
def quad (a b c d : Nat → Nat) (k : Nat) : Nat → Nat :=
  if k / 2 = 0 then a else if k / 2 = 1 then b else if k / 2 = 2 then c else d

theorem quad_apply (a b c d : Nat → Nat) (k i : Nat) :
    quad a b c d k i = (if k / 2 = 0 then a i else if k / 2 = 1 then b i else if k / 2 = 2 then c i else d i) := by
  simp only [quad]; split <;> [rfl; split <;> [rfl; split <;> rfl]]

theorem quad_ge {a b c d : Nat → Nat} (ha : ∀ j, 4 ≤ j → a j = a 4) (hb : ∀ j, 4 ≤ j → b j = b 4)
    (hc : ∀ j, 4 ≤ j → c j = c 4) (hd : ∀ j, 4 ≤ j → d j = d 4) (k : Nat) :
    ∀ j, 4 ≤ j → quad a b c d k j = quad a b c d k 4 := fun j h => by
  simp only [quad]; split <;> [exact ha j h; split <;> [exact hb j h; split <;> [exact hc j h; exact hd j h]]]

/-- Limbs by quadword: `a` in the even ones, `b` in the odd ones. -/
def alt (a b : Nat → Nat) (k : Nat) : Nat → Nat := if k % 2 = 0 then a else b

theorem alt_apply (a b : Nat → Nat) (k i : Nat) : alt a b k i = if k % 2 = 0 then a i else b i := by
  simp only [alt]; split <;> rfl

theorem alt_of_even {a b : Nat → Nat} {k : Nat} (h : k % 2 = 0) : alt a b k = a := by
  simp only [alt, h, ite_true]

theorem alt_of_odd {a b : Nat → Nat} {k : Nat} (h : k % 2 = 1) : alt a b k = b := by
  simp only [alt, h, show (1 : Nat) ≠ 0 by decide, ite_false]

theorem alt_ge {a b : Nat → Nat} (ha : ∀ j, 4 ≤ j → a j = a 4) (hb : ∀ j, 4 ≤ j → b j = b 4) (k : Nat) :
    ∀ j, 4 ≤ j → alt a b k j = alt a b k 4 := fun j h => by
  simp only [alt]; split <;> [exact ha j h; exact hb j h]

theorem powersV_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hax : s.gpr .rax = 1) :
    WP isa (.block powersV) s fun s' => vec s s' = s' ∧ YInv s' (rN s) := by
  have r8 : ∀ {t : State}, vec s t = t → t.gpr .r8 = 0x3ffffff := fun h => by rw [vec_gpr h, hr8]
  have ax : ∀ {t : State}, vec s t = t → t.gpr .rax = 1 := fun h => by rw [vec_gpr h, hax]
  -- `r` in `H` and `D`.
  refine WP.block_append (WP.mono (loadRv_ok s) fun s₁ ⟨v₁, L₁⟩ => ?_)
  let rA := hv s₁ 0
  have rS : SplitOf s rA := (L₁ 0 (by decide)).1
  have A_lt := fun {i : Nat} (hi : i < 5) => rS.lt i hi
  have hA₁ : ∀ k < 8, ∀ i < 5, hv s₁ k i = rA i := fun k hk => (L₁ k hk).1.eq rS
  have rA_ge : ∀ j, 4 ≤ j → rA j = rA 4 := fun _ h => hv_ge _ _ h
  -- `Y = r` in both doublewords.
  refine WP.block_append (WP.mono (initY_ok fun k hk i hi => by
    rw [hA₁ k hk i hi]; have := A_lt hi; omega_arith) fun s₂ ⟨v₂, I₂⟩ => ?_)
  have v₂' := vec_trans v₁ v₂
  -- `H = r²`.
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₂', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₃ M₃ => ?_)
  · rw [(I₂ k hk i hi).1, hA₁ k hk i hi]; have := A_lt hi; omega_arith
  · rw [(I₂ k hk i hi).2.1, hA₁ k hk i hi]; have := A_lt hi; omega_arith
  have hA₂ : ∀ k < 8, hv s₂ k = rA := fun k hk =>
    fext (fun _ h => hv_ge _ _ h) rA_ge fun i hi => by rw [(I₂ k hk i hi).1, hA₁ k hk i hi]
  have yA₂ : ∀ k < 8, yl s₂ k = rA := fun k hk =>
    fext (fun _ h => yl_ge _ _ h) rA_ge fun i hi => by rw [(I₂ k hk i hi).2.1, hA₁ k hk i hi]
  let B := Limbs26.mul (rA) (rA)
  have e₃ : ∀ k < 8, ∀ i < 5, hv s₃ k i = B i := fun k hk i hi => by
    rw [M₃.h k hk i hi, hA₂ k hk, yA₂ k hk]
  have yh₃ : ∀ k < 8, ∀ i < 5, yh s₃ k i = rA i := fun k hk i hi => by
    simp only [yh]; rw [M₃.y i hi k hk]
    have := (I₂ k hk i hi).2.2; simp only [yh] at this; rw [this, hA₁ k hk i hi]
  have B_lt : ∀ i < 5, B i < 2 ^ 27 := fun i hi => by rw [← e₃ 0 (by decide) i hi]; exact M₃.hb 0 (by decide) i hi
  -- `H = (r², r)` in each lane, `Y = r²`.
  refine WP.block_append (WP.mono (pairs_ok s₃) fun s₄ ⟨v₄, P₄⟩ => ?_)
  have v₄' := vec_trans (vec_trans v₂' M₃.vec) v₄
  have h₄ : ∀ k < 8, ∀ i < 5, hv s₄ k i = (if k % 2 = 0 then B i else rA i) := fun k hk i hi => by
    rw [(P₄ k hk i hi).1]; split
    · exact e₃ k hk i hi
    · exact yh₃ (k - 1) (by omega_arith) i hi
  have y₄ : ∀ k < 8, ∀ i < 5, yl s₄ k i = B i := fun k hk i hi => by
    simp only [yl]; rw [(P₄ k hk i hi).2, e₃ k hk i hi]; exact Nat.mod_eq_of_lt (by have := B_lt i hi; omega_arith)
  -- `H = (r⁴, r³)` in each lane.
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₄', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₅ M₅ => ?_)
  · rw [h₄ k hk i hi]; have := B_lt i hi; have := A_lt hi; split <;> omega_arith
  · rw [y₄ k hk i hi]; exact B_lt i hi
  let C4 := Limbs26.mul B B
  let C3 := Limbs26.mul (rA) B
  have yB₄ : ∀ k < 8, yl s₄ k = B := fun k hk =>
    fext (fun _ h => yl_ge _ _ h) (fun _ h => mul_ge _ _ h) (y₄ k hk)
  have e₅ : ∀ k < 8, ∀ i < 5, hv s₅ k i = (if k % 2 = 0 then C4 i else C3 i) := fun k hk i hi => by
    rw [M₅.h k hk i hi, yB₄ k hk]
    have hf : hv s₄ k = if k % 2 = 0 then B else rA := by
      split
      · exact fext (fun _ h => hv_ge _ _ h) (fun _ h => mul_ge _ _ h) fun i hi => by
          rw [h₄ k hk i hi, ite_eq_left ‹_›]
      · exact fext (fun _ h => hv_ge _ _ h) rA_ge fun i hi => by
          rw [h₄ k hk i hi, ite_eq_right ‹_›]
    rw [hf]; split <;> rfl
  have yv₅ : ∀ i < 5, (qz s₅ (yreg i) 0).toNat = B i := fun i hi => by
    rw [M₅.y i hi 0 (by decide), (P₄ 0 (by decide) i hi).2, e₃ 0 (by decide) i hi]
  -- `r` in `D`.
  refine WP.block_append (WP.mono (splitR_ok s₅) fun s₆ ⟨v₆, S₆⟩ => ?_)
  have v₆' := vec_trans (vec_trans v₄' M₅.vec) v₆
  have d₆ : ∀ i < 5, dv s₆ 0 i = rA i :=
    ((S₆ 0 (by decide)).1.congr (vec_gpr (vec_trans v₄' M₅.vec)).symm).eq rS
  -- `H = (r^(4-j), r^(4-j))` in lane `j`, `Y = (r⁴, 1)`.
  refine WP.block_append (WP.mono (spread_ok (ax v₆')) fun s₇ ⟨v₇, D₇⟩ => ?_)
  have v₇' := vec_trans v₆' v₇
  have hv₆ : ∀ k < 8, ∀ i < 5, hv s₆ k i = hv s₅ k i := fun k hk i hi => by
    simp only [hv]; rw [((S₆ k hk).2 i hi).1]
  have e₅0 : ∀ i < 5, hv s₅ 0 i = C4 i := fun i hi => by
    rw [e₅ 0 (by decide) i hi, ite_eq_left (show 0 % 2 = 0 from rfl)]
  have e₅1 : ∀ i < 5, hv s₅ 1 i = C3 i := fun i hi => by
    rw [e₅ 1 (by decide) i hi, ite_eq_right (show ¬ 1 % 2 = 0 by decide)]
  have C4_lt : ∀ i < 5, C4 i < 2 ^ 27 := fun i hi => by
    have := M₅.hb 0 (by decide) i hi; rwa [e₅0 i hi] at this
  have C3_lt : ∀ i < 5, C3 i < 2 ^ 27 := fun i hi => by
    have := M₅.hb 1 (by decide) i hi; rwa [e₅1 i hi] at this
  have B_ge : ∀ j, 4 ≤ j → B j = B 4 := fun j h => mul_ge rA rA h
  have C4_ge : ∀ j, 4 ≤ j → C4 j = C4 4 := fun j h => mul_ge B B h
  have C3_ge : ∀ j, 4 ≤ j → C3 j = C3 4 := fun j h => mul_ge rA B h
  have h₇ : ∀ k < 8, ∀ i < 5, hv s₇ k i = quad C4 C3 B rA k i := fun k hk i hi => by
    rw [(D₇ k hk i hi).1, hv₆ 0 (by decide) i hi, hv₆ 1 (by decide) i hi, e₅0 i hi, e₅1 i hi,
      ((S₆ 0 (by decide)).2 i hi).2, yv₅ i hi, d₆ i hi, quad_apply]
  have y₇ : ∀ k < 8, ∀ i < 5, yl s₇ k i = alt C4 one k i := fun k hk i hi => by
    simp only [yl]; rw [(D₇ k hk i hi).2, hv₆ 0 (by decide) i hi, e₅0 i hi, alt_apply]
    split
    · exact Nat.mod_eq_of_lt (by have := C4_lt i hi; omega_arith)
    · exact Nat.mod_eq_of_lt (Nat.lt_trans one_lt (by decide))
  have X_lt : ∀ k < 8, ∀ i < 5, quad C4 C3 B rA k i < 2 ^ 27 := fun k hk i hi => by
    rw [quad_apply]
    have := C4_lt i hi; have := C3_lt i hi; have := B_lt i hi; have := A_lt hi
    split <;> [omega_arith; split <;> [omega_arith; split <;> omega_arith]]
  -- `H = r^(8 - π k)` in quadword `k`.
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₇', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₈ M₈ => ?_)
  · rw [h₇ k hk i hi]; have := X_lt k hk i hi; omega_arith
  · rw [y₇ k hk i hi, alt_apply]; split
    · exact C4_lt i hi
    · exact one_lt
  -- `Y`: `r⁸` and `r^(8 - π k)`.
  refine WP.mono (finishY_ok fun k hk i hi => by have := M₈.hb k hk i hi; omega_arith) fun s₉ ⟨v₉, F₉⟩ => ?_
  refine ⟨vec_trans (vec_trans v₇' M₈.vec) v₉, ?_⟩
  -- Values and bounds of the powers.
  have q₁ : Limbs26.val rA ≡ rN s [MOD P] := by rw [rS.val]
  have q₂ : Limbs26.val B ≡ rN s ^ 2 [MOD P] := by
    rw [show rN s ^ 2 = rN s * rN s by ring]; exact mul_modEq q₁ q₁
  have q₄ : Limbs26.val C4 ≡ rN s ^ 4 [MOD P] := by
    rw [show rN s ^ 4 = rN s ^ 2 * rN s ^ 2 by ring]; exact mul_modEq q₂ q₂
  have q₃ : Limbs26.val C3 ≡ rN s ^ 3 [MOD P] := by
    rw [show rN s ^ 3 = rN s * rN s ^ 2 by ring]; exact mul_modEq q₁ q₂
  have qX : ∀ k < 8, Limbs26.val (quad C4 C3 B rA k) ≡ rN s ^ (4 - k / 2) [MOD P] := fun k hk => by
    rcases (by omega_arith : k / 2 = 0 ∨ k / 2 = 1 ∨ k / 2 = 2 ∨ k / 2 = 3) with h | h | h | h <;>
      simp only [quad, h, ite_true, ite_false, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
        show (3 : Nat) ≠ 2 by decide]
    · exact q₄
    · exact q₃
    · exact q₂
    · rw [show 4 - 3 = 1 from rfl, Nat.pow_one]; exact q₁
  have e₈ : ∀ k < 8, hv s₈ k = Limbs26.mul (quad C4 C3 B rA k) (alt C4 one k) := fun k hk => by
    have hx : hv s₇ k = quad C4 C3 B rA k :=
      fext (fun _ h => hv_ge _ _ h) (quad_ge C4_ge C3_ge B_ge rA_ge k) (h₇ k hk)
    have hy : yl s₇ k = alt C4 one k :=
      fext (fun _ h => yl_ge _ _ h) (alt_ge (b := one) C4_ge (fun _ h => one_ge h) k) (y₇ k hk)
    exact fext (fun _ h => hv_ge _ _ h) (fun _ h => mul_ge _ _ h) fun i hi => by
      rw [M₈.h k hk i hi, hx, hy]
  have q₈ : ∀ k < 8, Limbs26.val (hv s₈ k) ≡ rN s ^ (8 - pi k) [MOD P] := fun k hk => by
    rw [e₈ k hk]
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
    · have e : 8 - pi k = (4 - k / 2) + 4 := by simp only [pi]; omega_arith
      rw [alt_of_even h0, e, pow_add]
      exact mul_modEq (qX k hk) q₄
    · have e : 8 - pi k = 4 - k / 2 := by simp only [pi]; omega_arith
      rw [alt_of_odd h0, e, ← Nat.mul_one (rN s ^ (4 - k / 2))]
      exact mul_modEq (qX k hk) (by rw [one_val])
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [val_congr (F₉ k hk · · |>.2.1)]
    have := q₈ 0 (by decide)
    rwa [show pi 0 = 0 from rfl] at this
  · rw [val_congr (F₉ k hk · · |>.2.2)]; exact q₈ k hk
  · rw [(F₉ k hk i hi).2.1]; exact M₈.hb 0 (by decide) i hi
  · rw [(F₉ k hk i hi).2.2]; exact M₈.hb k hk i hi

end VG.Proof.Poly1305.X86_64.Avx512

end

end

/-! ### `Poly1305.Horner8`, which only this module used -/

section

/-!
# Poly1305: Horner's rule in eight lanes

As `Horner.lean`, with eight lanes: lane `j` holds `V_j`, a group of blocks
`m₀ … m₇` makes it `(V_j + m_j) r⁸`, and the last group `(V_j + m_j) r^(8-j)`,
after which the lanes are summed. With `S = r⁸ V₀ + r⁷ V₁ + … + r V₇`, the
invariant is `S ≡ r⁸ a` for the accumulator `a` of the blocks so far.
-/

@[expose] public section

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (P leNum)

section
variable {r a : Nat} {b0 b1 b2 b3 b4 b5 b6 b7 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (h4 : b4.length = 16) (h5 : b5.length = 16) (h6 : b6.length = 16) (h7 : b7.length = 16)
include h0 h1 h2 h3 h4 h5 h6 h7

theorem absorbAll_eight :
    absorbAll r a (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) ≡
      r ^ 8 * a + r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 +
        r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 [MOD P] := by
  have l : (b0 ++ b1 ++ b2 ++ b3).length % 16 = 0 := by simp [h0, h1, h2, h3]
  rw [show b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 = (b0 ++ b1 ++ b2 ++ b3) ++ (b4 ++ b5 ++ b6 ++ b7) by
    simp only [List.append_assoc], absorbAll_append l]
  refine Nat.ModEq.trans (absorbAll_four h4 h5 h6 h7) ?_
  have hA : _ ≡ _ [MOD P] := absorbAll_four (r := r) (a := a) h0 h1 h2 h3
  refine ((((hA.mul_left (r ^ 4)).add_right _).add_right _).add_right _).add_right _ |>.trans ?_
  rw [show r ^ 4 * (r ^ 4 * a + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) + r ^ 4 * mv b4 +
      r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 =
    r ^ 8 * a + r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 +
      r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 by ring]

end

/-- The lanes' sum, weighted by the powers of `r` of the last group. -/
abbrev lanes8 (r V0 V1 V2 V3 V4 V5 V6 V7 : Nat) : Nat :=
  r ^ 8 * V0 + r ^ 7 * V1 + r ^ 6 * V2 + r ^ 5 * V3 + r ^ 4 * V4 + r ^ 3 * V5 + r ^ 2 * V6 + r * V7

/-- The weighted values of a group's blocks. -/
abbrev msum8 (r : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : List Byte) : Nat :=
  r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 + r ^ 3 * mv b5 +
    r ^ 2 * mv b6 + r * mv b7

section
variable {r X V0 V1 V2 V3 V4 V5 V6 V7 W0 W1 W2 W3 W4 W5 W6 W7 : Nat}
  {b0 b1 b2 b3 b4 b5 b6 b7 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (h4 : b4.length = 16) (h5 : b5.length = 16) (h6 : b6.length = 16) (h7 : b7.length = 16)
  (hS : lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 ≡ r ^ 8 * X [MOD P])
include h0 h1 h2 h3 h4 h5 h6 h7 hS

omit hS in
theorem absorbAll_eight' :
    absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) ≡
      r ^ 8 * X + msum8 r b0 b1 b2 b3 b4 b5 b6 b7 [MOD P] := by
  refine (absorbAll_eight h0 h1 h2 h3 h4 h5 h6 h7).trans ?_
  rw [show r ^ 8 * X + r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 +
      r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 = r ^ 8 * X + msum8 r b0 b1 b2 b3 b4 b5 b6 b7 by
    simp only [msum8]; ring]

/-- A group of eight blocks, each lane multiplied by `r⁸`. -/
theorem horner8_step (e0 : W0 ≡ (V0 + mv b0) * r ^ 8 [MOD P]) (e1 : W1 ≡ (V1 + mv b1) * r ^ 8 [MOD P])
    (e2 : W2 ≡ (V2 + mv b2) * r ^ 8 [MOD P]) (e3 : W3 ≡ (V3 + mv b3) * r ^ 8 [MOD P])
    (e4 : W4 ≡ (V4 + mv b4) * r ^ 8 [MOD P]) (e5 : W5 ≡ (V5 + mv b5) * r ^ 8 [MOD P])
    (e6 : W6 ≡ (V6 + mv b6) * r ^ 8 [MOD P]) (e7 : W7 ≡ (V7 + mv b7) * r ^ 8 [MOD P]) :
    lanes8 r W0 W1 W2 W3 W4 W5 W6 W7 ≡
      r ^ 8 * absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) [MOD P] := by
  have hA := (absorbAll_eight' (r := r) (X := X) h0 h1 h2 h3 h4 h5 h6 h7).mul_left (r ^ 8)
  have hL : lanes8 r W0 W1 W2 W3 W4 W5 W6 W7 ≡
      r ^ 8 * (lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + msum8 r b0 b1 b2 b3 b4 b5 b6 b7) [MOD P] := by
    refine ((((((((e0.mul_left _).add (e1.mul_left _)).add (e2.mul_left _)).add (e3.mul_left _)).add
      (e4.mul_left _)).add (e5.mul_left _)).add (e6.mul_left _)).add (e7.mul_left _)).trans ?_
    rw [show r ^ 8 * ((V0 + mv b0) * r ^ 8) + r ^ 7 * ((V1 + mv b1) * r ^ 8) +
        r ^ 6 * ((V2 + mv b2) * r ^ 8) + r ^ 5 * ((V3 + mv b3) * r ^ 8) + r ^ 4 * ((V4 + mv b4) * r ^ 8) +
        r ^ 3 * ((V5 + mv b5) * r ^ 8) + r ^ 2 * ((V6 + mv b6) * r ^ 8) + r * ((V7 + mv b7) * r ^ 8) =
        r ^ 8 * (lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + msum8 r b0 b1 b2 b3 b4 b5 b6 b7) by
      simp only [lanes8, msum8]; ring]
  exact hL.trans (((hS.add_right _).mul_left _).trans hA.symm)

/-- The last group, lane `j` multiplied by `r^(8-j)`, and the lanes summed. -/
theorem horner8_last (e0 : W0 ≡ (V0 + mv b0) * r ^ 8 [MOD P]) (e1 : W1 ≡ (V1 + mv b1) * r ^ 7 [MOD P])
    (e2 : W2 ≡ (V2 + mv b2) * r ^ 6 [MOD P]) (e3 : W3 ≡ (V3 + mv b3) * r ^ 5 [MOD P])
    (e4 : W4 ≡ (V4 + mv b4) * r ^ 4 [MOD P]) (e5 : W5 ≡ (V5 + mv b5) * r ^ 3 [MOD P])
    (e6 : W6 ≡ (V6 + mv b6) * r ^ 2 [MOD P]) (e7 : W7 ≡ (V7 + mv b7) * r [MOD P]) :
    W0 + W1 + W2 + W3 + W4 + W5 + W6 + W7 ≡
      absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) [MOD P] := by
  have hA := absorbAll_eight' (r := r) (X := X) h0 h1 h2 h3 h4 h5 h6 h7
  refine (((((((e0.add e1).add e2).add e3).add e4).add e5).add e6).add e7).trans ?_
  rw [show (V0 + mv b0) * r ^ 8 + (V1 + mv b1) * r ^ 7 + (V2 + mv b2) * r ^ 6 + (V3 + mv b3) * r ^ 5 +
      (V4 + mv b4) * r ^ 4 + (V5 + mv b5) * r ^ 3 + (V6 + mv b6) * r ^ 2 + (V7 + mv b7) * r =
      lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + msum8 r b0 b1 b2 b3 b4 b5 b6 b7 by
    simp only [lanes8, msum8]; ring]
  exact (hS.add_right _).trans hA.symm

end

end VG.Proof.Poly1305

end

end


/-!
# Poly1305 on x86-64 with AVX-512: groups of eight blocks

Each group of eight blocks is added to the quadwords of `H` (block `π k` to
quadword `k`) and multiplied by `r⁸` (Horner's rule in eight lanes,
`Horner8.lean`), whose limbs are in the state (`MemY`); the last group is
multiplied quadword by quadword by `r^(8 - π k)`, after which the sum of the
quadwords is the accumulator.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr vec_mem vec_rd vec_wr ext5 val_congr)
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (mv lanes8 absorbAll)

/-- Block `j` of the group at `rsi`. -/
def blk (s : State) (j : Nat) : List Byte := bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * j)) 16

theorem blk_length (s : State) (j : Nat) : (blk s j).length = 16 := Poly1305.length_bytesAt _ _ _

theorem blk_mv (s : State) (k : Nat) : mv (blk s (pi k)) = blo s k + 2 ^ 64 * bhi s k + 2 ^ 128 := by
  rw [mv, Poly1305.leNum_append, blk, Poly1305.length_bytesAt, Poly1305.leNum_bytesAt_16]
  have e₁ : s.gpr .rsi + BitVec.ofNat 64 (16 * pi k) = s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * pi k)) := by
    rw [show 16 * pi k = 8 * (2 * pi k) by omega_using []]
  have e₂ : s.gpr .rsi + BitVec.ofNat 64 (16 * pi k) + 8 =
      s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * pi k + 1)) := by
    rw [BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
      show 16 * pi k + 8 = 8 * (2 * pi k + 1) by omega_using []]
  rw [e₂, e₁]
  simp only [blo, bhi, envOf]
  rfl

/-- The group at `rsi`, block by block. -/
theorem group_bytes (s : State) :
    bytesAt s.mem (s.gpr .rsi) 128 =
      blk s 0 ++ blk s 1 ++ blk s 2 ++ blk s 3 ++ blk s 4 ++ blk s 5 ++ blk s 6 ++ blk s 7 := by
  have e : ∀ n, bytesAt s.mem (s.gpr .rsi) (n + 16) =
      bytesAt s.mem (s.gpr .rsi) n ++ bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 n) 16 :=
    fun n => Poly1305.bytesAt_add _ _ n 16
  rw [(e 112 : bytesAt s.mem (s.gpr .rsi) 128 = _), (e 96 : bytesAt s.mem (s.gpr .rsi) 112 = _),
    (e 80 : bytesAt s.mem (s.gpr .rsi) 96 = _), (e 64 : bytesAt s.mem (s.gpr .rsi) 80 = _),
    (e 48 : bytesAt s.mem (s.gpr .rsi) 64 = _), (e 32 : bytesAt s.mem (s.gpr .rsi) 48 = _),
    (e 16 : bytesAt s.mem (s.gpr .rsi) 32 = _)]
  simp only [blk]
  rw [show BitVec.ofNat 64 (16 * 0) = 0#64 from rfl, BitVec.add_zero]

/-- The value of quadword `k` of `H`. -/
def hval (s : State) (k : Nat) : Nat := Limbs26.val (hv s k)

/-- The lanes of `H` weighted by the powers of `R` of the last group, in the
order of their blocks (block `j` is in quadword `2 j` for `j < 4`, else
`2 (j - 4) + 1`). -/
def wsum (R : Nat) (s : State) : Nat :=
  lanes8 R (hval s 0) (hval s 2) (hval s 4) (hval s 6) (hval s 1) (hval s 3) (hval s 5) (hval s 7)

/-- What holds of the vector registers between groups: `Y` holds the powers
of `R`, and the quadwords of `H` (limbs below `2²⁷`) the accumulator `X`,
after Horner's rule in eight lanes. -/
structure LaneInv (R X : Nat) (s : State) : Prop where
  y : YInv s R
  hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27
  acc : wsum R s ≡ R ^ 8 * X [MOD P]

theorem YInv.of_y {s s' : State} {R : Nat} (h : YInv s R)
    (hy : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k) : YInv s' R := by
  have el : ∀ k < 8, yl s' k = yl s k := fun k hk => ext5 (fun _ h => yl_ge _ _ h) (fun _ h => yl_ge _ _ h)
    fun i hi => by simp only [yl, hy i hi k hk]
  have eh : ∀ k < 8, yh s' k = yh s k := fun k hk => ext5 (fun _ h => yh_ge _ _ h) (fun _ h => yh_ge _ _ h)
    fun i hi => by simp only [yh, hy i hi k hk]
  exact ⟨fun k hk => by rw [el k hk]; exact h.lo k hk, fun k hk => by rw [eh k hk]; exact h.hi k hk,
    fun k hk => by rw [el k hk]; exact h.lob k hk, fun k hk => by rw [eh k hk]; exact h.hib k hk⟩

/-- The multiplier in the state (`mulM`'s) is `R⁸`. -/
structure MemY (R : Nat) (s : State) : Prop where
  m : MemM s
  val : Limbs26.val (mr s) ≡ R ^ 8 [MOD P]

theorem Ctx.of_vec {s s' : State} (h : Ctx s) (hv : vec s s' = s') : Ctx s' := by
  have g := vec_gpr hv
  have rd := vec_rd hv
  have wr := vec_wr hv
  exact ⟨fun i hi => by rw [rd, wr, g]; exact h.ld i hi, fun d h₁ h₂ => by rw [rd, wr, g]; exact h.mb d h₁ h₂⟩

/-- `addGroupM`, then `mulM` by the multiplier in the state: quadword `k`
becomes `(V_k + m_(π k)) · r`. -/
theorem addMulM_ok {s : State} (hc : Ctx s) (hM : MemM s) (hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27) :
    WP isa (.block (addGroupM ++ mulM)) s fun s' => vec s s' = s' ∧
      (∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k) ∧ (∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 27) ∧
      ∀ k < 8, hval s' k ≡ (hval s k + mv (blk s (pi k))) * Limbs26.val (mr s) [MOD P] := by
  refine WP.block_append (WP.mono (addGroupM_ok ⟨hM.pad, hc, hb⟩) fun s₁ A => ?_)
  have hm : mr s₁ = mr s := by funext i; simp only [mr, envOf, vec_gpr A.vec, vec_mem A.vec]
  refine WP.mono (mulM_ok ⟨hc.of_vec A.vec, hM.of_mem (by rw [vec_gpr A.vec]) (vec_mem A.vec), A.hb⟩)
    fun s₂ M => ⟨vec_trans A.vec M.vec, fun i hi k hk => by rw [M.y i hi k hk, A.y i hi k hk], M.hb,
      fun k hk => ?_⟩
  simp only [hval]
  rw [val_congr (M.h k hk), blk_mv, ← A.h k hk, hm]
  exact Limbs26.mul_mod _ _

theorem pi_0 : pi 0 = 0 := rfl
theorem pi_1 : pi 1 = 4 := rfl
theorem pi_2 : pi 2 = 1 := rfl
theorem pi_3 : pi 3 = 5 := rfl
theorem pi_4 : pi 4 = 2 := rfl
theorem pi_5 : pi 5 = 6 := rfl
theorem pi_6 : pi 6 = 3 := rfl
theorem pi_7 : pi 7 = 7 := rfl

/-- A group before the last: the invariant for the blocks so far and the group. -/
theorem group_ok {R X : Nat} {s : State} (hc : Ctx s) (hM : MemY R s) (hI : LaneInv R X s) :
    WP isa (.block (addGroupM ++ mulM)) s fun s' => vec s s' = s' ∧
      LaneInv R (absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128)) s' := by
  refine WP.mono (addMulM_ok hc hM.m hI.hb) fun s' ⟨hv', hy, hb, he⟩ => ⟨hv', hI.y.of_y hy, hb, ?_⟩
  have e : ∀ k < 8, hval s' k ≡ (hval s k + mv (blk s (pi k))) * R ^ 8 [MOD P] := fun k hk =>
    (he k hk).trans (Nat.ModEq.mul_left _ hM.val)
  rw [group_bytes]
  have L := blk_length s
  exact Poly1305.horner8_step (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (by simpa only [pi_0] using e 0 (by decide)) (by simpa only [pi_2] using e 2 (by decide))
    (by simpa only [pi_4] using e 4 (by decide)) (by simpa only [pi_6] using e 6 (by decide))
    (by simpa only [pi_1] using e 1 (by decide)) (by simpa only [pi_3] using e 3 (by decide))
    (by simpa only [pi_5] using e 5 (by decide)) (by simpa only [pi_7] using e 7 (by decide))

/-! ## The last group -/

def shY : List Instr := (List.range 5).map fun i => srl (yreg i) (yreg i) 32

theorem last_eq : last = addGroup ++ (shY ++ mul) := rfl

def shS : Sym := (Sym.init.run false shY).get (by decide +kernel)
theorem shS_eq : Sym.init.run false shY = some shS := (Option.some_get _).symm
theorem shS_shape : ∀ i < 5, shS.reg (xi (yreg i)) = .shr (.reg (xi (yreg i))) 32 ∧
    shS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem shY_ok (s : State) :
    WP isa (.block shY) s fun s' => vec s s' = s' ∧ (∀ k < 8, ∀ i < 5, hv s' k i = hv s k i ∧
      yl s' k i = yh s k i) := by
  refine WP.mono (run_ok (by intro h; cases h) shS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [hv]; rw [h.reg _ k hk, (shS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl, yh]
    rw [h.natw _ hk, (shS_shape i hi).1]
    simp only [Q.natw, envOf_v]
    have := (qz s (yreg i) k).isLt
    omega_using []

/-- The sum of the quadwords, in the order of their blocks. -/
def bsum (s : State) : Nat :=
  hval s 0 + hval s 2 + hval s 4 + hval s 6 + hval s 1 + hval s 3 + hval s 5 + hval s 7

/-- The last group: quadword `k` multiplied by `r^(8 - π k)`, and the sum of
the quadwords is the accumulator. -/
theorem last_ok {R X : Nat} {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hr9 : s.gpr .r9 = 0x1000000)
    (hc : Ctx s) (hI : LaneInv R X s) :
    WP isa (.block last) s fun s' => vec s s' = s' ∧ (∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 27) ∧
      bsum s' ≡ absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128) [MOD P] := by
  rw [last_eq]
  refine WP.block_append (WP.mono (addGroup_ok ⟨hr9, hc, hI.hb⟩) fun s₁ A => ?_)
  have Y₁ := hI.y.of_y A.y
  refine WP.block_append (WP.mono (shY_ok s₁) fun s₂ ⟨v₂, e₂⟩ => ?_)
  have hH : ∀ k < 8, hv s₂ k = hv s₁ k := fun k hk => ext5 (fun _ h => hv_ge _ _ h) (fun _ h => hv_ge _ _ h)
    fun i hi => (e₂ k hk i hi).1
  have hY : ∀ k < 8, yl s₂ k = yh s₁ k := fun k hk => ext5 (fun _ h => yl_ge _ _ h) (fun _ h => yh_ge _ _ h)
    fun i hi => (e₂ k hk i hi).2
  refine WP.mono (mul_ok ⟨by rw [vec_gpr v₂, vec_gpr A.vec, hr8], fun k hk i hi => by
      rw [hH k hk]; exact A.hb k hk i hi, fun k hk i hi => by rw [hY k hk]; exact Y₁.hib k hk i hi⟩)
    fun s₃ M => ⟨vec_trans (vec_trans A.vec v₂) M.vec, M.hb, ?_⟩
  have e : ∀ k < 8, hval s₃ k ≡ (hval s k + mv (blk s (pi k))) * R ^ (8 - pi k) [MOD P] := by
    intro k hk
    simp only [hval]
    rw [val_congr (M.h k hk), hH k hk, hY k hk, blk_mv, ← A.h k hk]
    exact (Limbs26.mul_mod _ _).trans (Nat.ModEq.mul_left _ (Y₁.hi k hk))
  rw [group_bytes]
  have L := blk_length s
  exact Poly1305.horner8_last (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (by simpa only [pi_0] using e 0 (by decide)) (by simpa only [pi_2] using e 2 (by decide))
    (by simpa only [pi_4] using e 4 (by decide)) (by simpa only [pi_6] using e 6 (by decide))
    (by simpa only [pi_1] using e 1 (by decide)) (by simpa only [pi_3] using e 3 (by decide))
    (by simpa only [pi_5] using e 5 (by decide)) (by simpa only [pi_7, show 8 - 7 = 1 from rfl, pow_one] using e 7 (by decide))

end VG.Proof.Poly1305.X86_64.Avx512
