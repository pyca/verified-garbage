module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Load
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Inv
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: the short vector blocks

The vector instructions between the products: `Y` set from `rax`, `rcx` and
`r9` in some quadwords and from 1 in the others, and `S` from `Y` (`setY`);
`Y` from `H`; the accumulator into quadword 0 of `H`; and the folds of the
end, each adding to some quadwords of `H` others.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Impl.Poly1305.X86_64.Avx512 (z srl sll mov shuf bcast zb)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec)
open VG.Proof.Poly1305.X86_64.Avx512 (qz envOf_v cases8)

/-- The register that holds limb `i` before it is broadcast. -/
def lg : Nat → Reg
  | 0 => .rax | 1 => .rcx | _ => .r9

/-- The limbs of 1. -/
def one (i : Nat) : Nat := if i = 0 then 1 else 0

/-- `rax`, `rcx` and `r9` into every quadword of `Y`. -/
def bc3 : List Instr := bcast (yreg 0) .rax ++ bcast (yreg 1) .rcx ++ bcast (yreg 2) .r9

def unpY : List Instr :=
  [z .vpunpcklqdq (yreg 0) (yreg 0) t0, z .vpunpcklqdq (yreg 1) (yreg 1) t1,
   z .vpunpcklqdq (yreg 2) (yreg 2) t1]
def shY2 : List Instr :=
  [shuf (yreg 0) (yreg 0) t0 0x00, shuf (yreg 1) (yreg 1) t1 0x00, shuf (yreg 2) (yreg 2) t1 0x00,
   shuf (yreg 0) (yreg 0) (yreg 0) 0x88, shuf (yreg 1) (yreg 1) (yreg 1) 0x88,
   shuf (yreg 2) (yreg 2) (yreg 2) 0x88]
def shY3 : List Instr :=
  [shuf (yreg 0) (yreg 0) t0 0x00, shuf (yreg 1) (yreg 1) t1 0x00, shuf (yreg 2) (yreg 2) t1 0x00]

def fold1 : List Instr :=
  [0, 1, 2].flatMap fun i => [z .vpunpckhqdq t0 (hreg i) (hreg i), z .vpaddq (hreg i) (hreg i) t0]
def fold2 : List Instr :=
  [0, 1, 2].flatMap fun i => [shuf t0 (hreg i) (hreg i) 0xF5, z .vpaddq (hreg i) (hreg i) t0]
def fold3 : List Instr :=
  [0, 1, 2].flatMap fun i => [shuf t0 (hreg i) (hreg i) 0xEE, z .vpaddq (hreg i) (hreg i) t0]

/-! ## Setting `Y` -/

/-- What a block setting `Y` leaves: limb `i` of quadword `k` of `Y` is
`lg i` where `sel k` and limb `i` of 1 elsewhere, `S` twenty times limbs 1
and 2 of `Y`, and `H` as it was. -/
structure YSet (sel : Nat → Bool) (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 3, ∀ k < 8, yv s' k i = if sel k then (s.gpr (lg i)).toNat else one i
  sr : ∀ i, 1 ≤ i → i < 3 → ∀ k < 8, sv s' k i = (yv s' k i * 2 ^ 4 % 2 ^ 64 + yv s' k i * 2 ^ 2 % 2 ^ 64) % 2 ^ 64
  h : ∀ i < 3, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k

theorem YSet.s1 {sel : Nat → Bool} {s s' : State} (h : YSet sel s s') (hb : ∀ i < 3, (s.gpr (lg i)).toNat ≤ 2 ^ 44)
    {k : Nat} (hk : k < 8) : sv s' k 1 = 20 * yv s' k 1 := by
  have e := h.y 1 (by decide) k hk
  have b := hb 1 (by decide)
  have o : one 1 = 0 := rfl
  rw [h.sr 1 (by decide) (by decide) k hk]
  split at e <;> omega_arith

theorem YSet.s2 {sel : Nat → Bool} {s s' : State} (h : YSet sel s s') (hb : ∀ i < 3, (s.gpr (lg i)).toNat ≤ 2 ^ 44)
    {k : Nat} (hk : k < 8) : sv s' k 2 = 20 * yv s' k 2 := by
  have e := h.y 2 (by decide) k hk
  have b := hb 2 (by decide)
  have o : one 2 = 0 := rfl
  rw [h.sr 2 (by decide) (by decide) k hk]
  split at e <;> omega_arith

theorem YSet.yb {sel : Nat → Bool} {s s' : State} (h : YSet sel s s') (hb : ∀ i < 3, (s.gpr (lg i)).toNat ≤ 2 ^ 44) :
    ∀ k < 8, ∀ i < 3, yv s' k i ≤ 2 ^ 44 := by
  intro k hk i hi
  have e := h.y i hi k hk
  have b := hb i hi
  have o : one i ≤ 1 := by unfold one; split <;> omega_arith
  split at e <;> omega_arith

/-- `YSet` from the shapes of the terms of a block. -/
theorem YSet.of {σ : Sym} {s s' : State} (h : SRel σ s s') {sel : Nat → Bool}
    (ho : (∀ k < 8, sel k = true) ∨ (0 ||| (envOf s).mb 104) / 2 ^ 43 = 1)
    (hy : ∀ i < 3, ∀ k < 8, (σ.reg (xi (yreg i))).natw (envOf s) k =
      if sel k then (envOf s).g (lg i) else if i = 0 then (0 ||| (envOf s).mb 104) / 2 ^ 43 else 0)
    (hs : ∀ i, 1 ≤ i → i < 3 →
      σ.reg (xi (sreg i)) = .add (.shl (σ.reg (xi (yreg i))) 4) (.shl (σ.reg (xi (yreg i))) 2))
    (hh : ∀ i < 3, σ.reg (xi (hreg i)) = .reg (xi (hreg i))) : YSet sel s s' := by
  refine ⟨h.eq, fun i hi k hk => ?_, fun i h1 hi k hk => ?_, fun i hi k hk => ?_⟩
  · simp only [yv]
    rw [h.natw _ hk, hy i hi k hk]
    rcases ho with ho | ho
    · simp only [ho k hk, ite_true, envOf, Avx512.envOf]
    · rw [ho]; simp only [one, envOf, Avx512.envOf]
  · simp only [sv, yv]
    rw [h.natw _ hk, h.natw _ hk, hs i h1 hi]
    rfl
  · rw [h.reg _ k hk, hh i hi]; simp only [Q.eval, xr_xi]

theorem one_mask : (0 ||| 0xfffffffffff) / 2 ^ 43 = 1 := by decide

/-! ## The blocks setting `Y` -/

section
variable (E : Env)

def s0S : Sym := (Sym.init.run false (bc3 ++ twenty)).get (by decide +kernel)
theorem s0S_eq : Sym.init.run false (bc3 ++ twenty) = some s0S := (Option.some_get _).symm
theorem s0S_y : ∀ i < 3, ∀ k < 8, (s0S.reg (xi (yreg i))).natw E k =
    if (fun _ => true : Nat → Bool) k then E.g (lg i) else if i = 0 then (0 ||| E.mb 104) / 2 ^ 43 else 0 := by
  intro i hi k hk
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem s0S_shape : (∀ i, 1 ≤ i → i < 3 →
    s0S.reg (xi (sreg i)) = .add (.shl (s0S.reg (xi (yreg i))) 4) (.shl (s0S.reg (xi (yreg i))) 2)) ∧
    ∀ i < 3, s0S.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

def s1S : Sym := (Sym.init.run true (bc3 ++ zeroOne ++ unpY ++ twenty)).get (by decide +kernel)
theorem s1S_eq : Sym.init.run true (bc3 ++ zeroOne ++ unpY ++ twenty) = some s1S := (Option.some_get _).symm
theorem s1S_y : ∀ i < 3, ∀ k < 8, (s1S.reg (xi (yreg i))).natw E k =
    if k % 2 == 0 then E.g (lg i) else if i = 0 then (0 ||| E.mb 104) / 2 ^ 43 else 0 := by
  intro i hi k hk
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem s1S_shape : (∀ i, 1 ≤ i → i < 3 →
    s1S.reg (xi (sreg i)) = .add (.shl (s1S.reg (xi (yreg i))) 4) (.shl (s1S.reg (xi (yreg i))) 2)) ∧
    ∀ i < 3, s1S.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

def s2S : Sym := (Sym.init.run true (bc3 ++ zeroOne ++ shY2 ++ twenty)).get (by decide +kernel)
theorem s2S_eq : Sym.init.run true (bc3 ++ zeroOne ++ shY2 ++ twenty) = some s2S := (Option.some_get _).symm
theorem s2S_y : ∀ i < 3, ∀ k < 8, (s2S.reg (xi (yreg i))).natw E k =
    if k / 2 % 2 == 0 then E.g (lg i) else if i = 0 then (0 ||| E.mb 104) / 2 ^ 43 else 0 := by
  intro i hi k hk
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem s2S_shape : (∀ i, 1 ≤ i → i < 3 →
    s2S.reg (xi (sreg i)) = .add (.shl (s2S.reg (xi (yreg i))) 4) (.shl (s2S.reg (xi (yreg i))) 2)) ∧
    ∀ i < 3, s2S.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

def s3S : Sym := (Sym.init.run true (bc3 ++ zeroOne ++ shY3 ++ twenty)).get (by decide +kernel)
theorem s3S_eq : Sym.init.run true (bc3 ++ zeroOne ++ shY3 ++ twenty) = some s3S := (Option.some_get _).symm
theorem s3S_y : ∀ i < 3, ∀ k < 8, (s3S.reg (xi (yreg i))).natw E k =
    if decide (k < 4) then E.g (lg i) else if i = 0 then (0 ||| E.mb 104) / 2 ^ 43 else 0 := by
  intro i hi k hk
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem s3S_shape : (∀ i, 1 ≤ i → i < 3 →
    s3S.reg (xi (sreg i)) = .add (.shl (s3S.reg (xi (yreg i))) 4) (.shl (s3S.reg (xi (yreg i))) 2)) ∧
    ∀ i < 3, s3S.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

end

theorem setY0_ok (s : State) : WP isa (.block (bc3 ++ twenty)) s (YSet (fun _ => true) s) :=
  WP.mono (run_ok (fun h => by cases h) s0S_eq) fun _ h =>
    YSet.of h (.inl fun _ _ => rfl) (s0S_y _) s0S_shape.1 s0S_shape.2

theorem setY1_ok {s : State} (hc : Ctx s) (hm : Consts s) :
    WP isa (.block (bc3 ++ zeroOne ++ unpY ++ twenty)) s (YSet (fun k => k % 2 == 0) s) :=
  WP.mono (run_ok (fun _ => hc) s1S_eq) fun _ h =>
    YSet.of h (.inr (by rw [hm.mask]; exact one_mask)) (s1S_y _) s1S_shape.1 s1S_shape.2

theorem setY2_ok {s : State} (hc : Ctx s) (hm : Consts s) :
    WP isa (.block (bc3 ++ zeroOne ++ shY2 ++ twenty)) s (YSet (fun k => k / 2 % 2 == 0) s) :=
  WP.mono (run_ok (fun _ => hc) s2S_eq) fun _ h =>
    YSet.of h (.inr (by rw [hm.mask]; exact one_mask)) (s2S_y _) s2S_shape.1 s2S_shape.2

theorem setY3_ok {s : State} (hc : Ctx s) (hm : Consts s) :
    WP isa (.block (bc3 ++ zeroOne ++ shY3 ++ twenty)) s (YSet (fun k => decide (k < 4)) s) :=
  WP.mono (run_ok (fun _ => hc) s3S_eq) fun _ h =>
    YSet.of h (.inr (by rw [hm.mask]; exact one_mask)) (s3S_y _) s3S_shape.1 s3S_shape.2

/-! ## `Y` from `H`, and `H` from `Y` -/

def yhS : Sym := (Sym.init.run false (yOfH ++ twenty)).get (by decide +kernel)
theorem yhS_eq : Sym.init.run false (yOfH ++ twenty) = some yhS := (Option.some_get _).symm
theorem yhS_shape : ∀ i < 3, yhS.reg (xi (yreg i)) = .reg (xi (hreg i)) ∧
    (1 ≤ i → yhS.reg (xi (sreg i)) = .add (.shl (.reg (xi (hreg i))) 4) (.shl (.reg (xi (hreg i))) 2)) ∧
    yhS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

/-- `Y = H` and `S` twenty times limbs 1 and 2 of it, with `H` as it was. -/
theorem yOfH_ok {s : State} (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44) :
    WP isa (.block (yOfH ++ twenty)) s fun s' => vec s s' = s' ∧ (∀ k < 8, yv s' k = hv s k) ∧
      (∀ k < 8, sv s' k 1 = 20 * yv s' k 1 ∧ sv s' k 2 = 20 * yv s' k 2) ∧
      ∀ i < 3, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k := by
  refine WP.mono (run_ok (fun h => by cases h) yhS_eq) fun s' h => ⟨h.eq, fun k hk => ?_, fun k hk => ?_,
    fun i hi k hk => ?_⟩
  · funext i
    simp only [yv, hv]
    rw [h.reg _ k hk]
    rcases (by omega_arith : i < 3 ∨ 3 ≤ i) with hi | hi
    · rw [(yhS_shape i hi).1]; simp only [Q.eval, xr_xi]
    · have e : ∀ {j}, 2 ≤ j → yreg j = yreg 2 ∧ hreg j = hreg 2 := fun {j} hj => by
        match j, hj with | _ + 2, _ => exact ⟨rfl, rfl⟩
      rw [(e (by omega_arith)).1, (e (by omega_arith)).2, (yhS_shape 2 (by decide)).1]; simp only [Q.eval, xr_xi]
  · have y1 : yv s' k 1 = hv s k 1 := by
      simp only [yv, hv]; rw [h.reg _ k hk, (yhS_shape 1 (by decide)).1]; simp only [Q.eval, xr_xi]
    have y2 : yv s' k 2 = hv s k 2 := by
      simp only [yv, hv]; rw [h.reg _ k hk, (yhS_shape 2 (by decide)).1]; simp only [Q.eval, xr_xi]
    have b1 := hb k hk 1 (by decide)
    have b2 := hb k hk 2 (by decide)
    have e1 : sv s' k 1 = (hv s k 1 * 2 ^ 4 % 2 ^ 64 + hv s k 1 * 2 ^ 2 % 2 ^ 64) % 2 ^ 64 := by
      simp only [sv, hv]; rw [h.natw _ hk, (yhS_shape 1 (by decide)).2.1 (by decide)]; simp only [Q.natw, envOf_v]
    have e2 : sv s' k 2 = (hv s k 2 * 2 ^ 4 % 2 ^ 64 + hv s k 2 * 2 ^ 2 % 2 ^ 64) % 2 ^ 64 := by
      simp only [sv, hv]; rw [h.natw _ hk, (yhS_shape 2 (by decide)).2.1 (by decide)]; simp only [Q.natw, envOf_v]
    omega_arith
  · rw [h.reg _ k hk, (yhS_shape i hi).2.2]; simp only [Q.eval, xr_xi]

def hyS : Sym := (Sym.init.run false hOfY).get (by decide +kernel)
theorem hyS_eq : Sym.init.run false hOfY = some hyS := (Option.some_get _).symm
theorem hyS_shape : ∀ i < 3, hyS.reg (xi (hreg i)) = .reg (xi (yreg i)) ∧
    hyS.reg (xi (yreg i)) = .reg (xi (yreg i)) ∧ hyS.reg (xi (sreg i)) = .reg (xi (sreg i)) := by
  decide +kernel

/-- `H = Y`, with `Y` and `S` as they were. -/
theorem hOfY_ok (s : State) :
    WP isa (.block hOfY) s fun s' => vec s s' = s' ∧ (∀ i < 3, ∀ k < 8, qz s' (hreg i) k = qz s (yreg i) k ∧
      qz s' (yreg i) k = qz s (yreg i) k ∧ qz s' (sreg i) k = qz s (sreg i) k) :=
  WP.mono (run_ok (fun h => by cases h) hyS_eq) fun s' h => ⟨h.eq, fun i hi k hk => by
    refine ⟨?_, ?_, ?_⟩ <;> rw [h.reg _ k hk]
    · rw [(hyS_shape i hi).1]; simp only [Q.eval, xr_xi]
    · rw [(hyS_shape i hi).2.1]; simp only [Q.eval, xr_xi]
    · rw [(hyS_shape i hi).2.2]; simp only [Q.eval, xr_xi]⟩

/-! ## The accumulator into `H` -/

def lhS : Sym := (Sym.init.run false
  [.vop (.vmovq (hreg 0) .rax), .vop (.vmovq (hreg 1) .rcx), .vop (.vmovq (hreg 2) .r9)]).get (by decide +kernel)
theorem lhS_eq : Sym.init.run false
    [.vop (.vmovq (hreg 0) .rax), .vop (.vmovq (hreg 1) .rcx), .vop (.vmovq (hreg 2) .r9)] = some lhS :=
  (Option.some_get _).symm
theorem lhS_shape : ∀ i < 3, lhS.reg (xi (hreg i)) = .lane0 (.gpr (lg i)) := by decide +kernel

/-- `rax`, `rcx` and `r9` into quadword 0 of `H`, zeros elsewhere. -/
theorem lhV_ok (s : State) :
    WP isa (.block [.vop (.vmovq (hreg 0) .rax), .vop (.vmovq (hreg 1) .rcx), .vop (.vmovq (hreg 2) .r9)]) s
      fun s' => vec s s' = s' ∧ ∀ i < 3, ∀ k < 8, hv s' k i = if k = 0 then (s.gpr (lg i)).toNat else 0 :=
  WP.mono (run_ok (fun h => by cases h) lhS_eq) fun s' h => ⟨h.eq, fun i hi k hk => by
    simp only [hv]
    rw [h.natw _ hk, lhS_shape i hi]
    simp only [Q.natw]
    split <;> rfl⟩

/-! ## The folds -/

def fB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 => 2 ^ 44
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 64 - 1⟩

theorem fB_env {s : State} (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44) : EnvOK s fB := by
  refine ⟨fun r k hk => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _)⟩
  have := BitVec.isLt (qz s r k)
  have h0 := hb k hk 0 (by decide)
  have h1 := hb k hk 1 (by decide)
  have h2 := hb k hk 2 (by decide)
  simp only [hv, hreg] at h0 h1 h2
  cases r <;> simp only [fB]
  all_goals omega_arith

def f1S : Sym := (Sym.init.run false fold1).get (by decide +kernel)
theorem f1S_eq : Sym.init.run false fold1 = some f1S := (Option.some_get _).symm
def f2S : Sym := (Sym.init.run false fold2).get (by decide +kernel)
theorem f2S_eq : Sym.init.run false fold2 = some f2S := (Option.some_get _).symm
def f3S : Sym := (Sym.init.run false fold3).get (by decide +kernel)
theorem f3S_eq : Sym.init.run false fold3 = some f3S := (Option.some_get _).symm

theorem fS_ok : ∀ i < 3, ∀ k < 8,
    ((f1S.reg (xi (hreg i))).ok fB k = true ∧ (f1S.reg (xi (hreg i))).bnd fB k ≤ 2 ^ 45) ∧
    ((f2S.reg (xi (hreg i))).ok fB k = true ∧ (f2S.reg (xi (hreg i))).bnd fB k ≤ 2 ^ 45) ∧
    ((f3S.reg (xi (hreg i))).ok fB k = true ∧ (f3S.reg (xi (hreg i))).bnd fB k ≤ 2 ^ 45) := by
  decide +kernel

section
variable (E : Env)
theorem f1S_nat : ∀ i < 3, ∀ j < 4, (f1S.reg (xi (hreg i))).nat E (2 * j) =
    E.v (xi (hreg i)) (2 * j) + E.v (xi (hreg i)) (2 * j + 1) := by
  intro i hi j hj
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem f2S_nat : ∀ i < 3, ∀ j < 2, (f2S.reg (xi (hreg i))).nat E (4 * j) =
    E.v (xi (hreg i)) (4 * j) + E.v (xi (hreg i)) (4 * j + 2) := by
  intro i hi j hj
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
theorem f3S_nat : ∀ i < 3, (f3S.reg (xi (hreg i))).nat E 0 = E.v (xi (hreg i)) 0 + E.v (xi (hreg i)) 4 := by
  intro i hi
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
end

/-- What a fold leaves: `H` below `2⁴⁵`, and the rest but `t0` as it was. -/
structure FoldPost (s s' : State) : Prop where
  vec : vec s s' = s'
  hb : ∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 45

theorem fold_post {σ : Sym} {s s' : State} (h : SRel σ s s') (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44)
    (ho : ∀ i < 3, ∀ k < 8, (σ.reg (xi (hreg i))).ok fB k = true ∧ (σ.reg (xi (hreg i))).bnd fB k ≤ 2 ^ 45) :
    FoldPost s s' :=
  ⟨h.eq, fun k hk i hi => by
    obtain ⟨-, b⟩ := h.nat (fB_env hb) hk (ho i hi k hk).1
    exact Nat.le_trans b (ho i hi k hk).2⟩

theorem fold_nat {σ : Sym} {s s' : State} (h : SRel σ s s') (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44)
    {i k : Nat} (hk : k < 8) (ho : (σ.reg (xi (hreg i))).ok fB k = true) :
    hv s' k i = (σ.reg (xi (hreg i))).nat (envOf s) k :=
  (h.nat (fB_env hb) hk ho).1

theorem fold1_ok {s : State} (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44) :
    WP isa (.block fold1) s fun s' => FoldPost s s' ∧
      ∀ j < 4, ∀ i < 3, hv s' (2 * j) i = hv s (2 * j) i + hv s (2 * j + 1) i :=
  WP.mono (run_ok (fun h => by cases h) f1S_eq) fun _ h =>
    ⟨fold_post h hb fun i hi k hk => (fS_ok i hi k hk).1, fun j hj i hi => by
      rw [fold_nat h hb (by omega_arith) (fS_ok i hi _ (by omega_arith)).1.1, f1S_nat _ i hi j hj, envOf_v, envOf_v]; rfl⟩

theorem fold2_ok {s : State} (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44) :
    WP isa (.block fold2) s fun s' => FoldPost s s' ∧
      ∀ j < 2, ∀ i < 3, hv s' (4 * j) i = hv s (4 * j) i + hv s (4 * j + 2) i :=
  WP.mono (run_ok (fun h => by cases h) f2S_eq) fun _ h =>
    ⟨fold_post h hb fun i hi k hk => (fS_ok i hi k hk).2.1, fun j hj i hi => by
      rw [fold_nat h hb (by omega_arith) (fS_ok i hi _ (by omega_arith)).2.1.1, f2S_nat _ i hi j hj, envOf_v, envOf_v]; rfl⟩

theorem fold3_ok {s : State} (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44) :
    WP isa (.block fold3) s fun s' => FoldPost s s' ∧
      ∀ i < 3, hv s' 0 i = hv s 0 i + hv s 4 i :=
  WP.mono (run_ok (fun h => by cases h) f3S_eq) fun _ h =>
    ⟨fold_post h hb fun i hi k hk => (fS_ok i hi k hk).2.2, fun i hi => by
      rw [fold_nat h hb (by decide) (fS_ok i hi _ (by decide)).2.2.1, f3S_nat _ i hi, envOf_v, envOf_v]; rfl⟩

end VG.Proof.Poly1305.X86_64.Ifma
