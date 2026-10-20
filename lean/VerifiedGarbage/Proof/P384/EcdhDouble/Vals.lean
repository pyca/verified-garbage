module

public import VerifiedGarbage.Impl.P384.EcdhDouble
import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.P256.EcdhDouble.Arithmetic
public import Mathlib.Logic.Function.Basic

/-!
# The values of P-384's raw doubling

`raw_vals`: the field operations of the raw doubling (`Impl/P384/EcdhDouble.lean`,
s2n-bignum's order, with its three linear combinations) leave in `b` the
window's Jacobian doubling of `a` (`dblJF`), by `values_eq`.
-/

@[expose] public section

namespace VG.Proof.P384.EcdhDouble
open VG VG.Impl.Weierstrass VG.Impl.P384.EcdhDouble VG.Proof.Weierstrass

/-- The environment after the raw doubling's operations and combinations. -/
def rawEnv {m : Nat} [NeZero m] (a b : Pt) (E : Nat → Fin m) : Nat → Fin m :=
  let e₁ := runOps (ops1 a b) E
  let e₂ := Function.update e₁ b.y (Fin.ofNat m 12 * e₁ K.S.t3 - Fin.ofNat m 9 * e₁ b.y)
  let e₃ := runOps (ops2 b) e₂
  let e₄ := Function.update e₃ b.x (Fin.ofNat m 4 * e₃ K.S.t3 - Fin.ofNat m 1 * e₃ b.y)
  Function.update e₄ b.y (Fin.ofNat m 3 * e₄ K.S.t1 - Fin.ofNat m 8 * e₄ K.S.t0)

set_option linter.unusedSimpArgs false in
theorem raw_vals {m : Nat} [NeZero m] (E : Nat → Fin m) {a b : Pt}
    (hd : [a.x, a.y, a.z, b.x, b.y, b.z, K.S.t0, K.S.t1, K.S.t2, K.S.t3].Nodup) :
    (rawEnv a b E b.x, rawEnv a b E b.y, rawEnv a b E b.z) = dblJF (E a.x) (E a.y) (E a.z) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h05, h06, h07, h08, h09⟩, ⟨h12, h13, h14, h15, h16, h17, h18, h19⟩,
    ⟨h23, h24, h25, h26, h27, h28, h29⟩, ⟨h34, h35, h36, h37, h38, h39⟩, ⟨h45, h46, h47, h48, h49⟩,
    ⟨h56, h57, h58, h59⟩, ⟨h67, h68, h69⟩, ⟨h78, h79⟩, h89, -⟩ := hd
  rw [← VG.Proof.P256.EcdhDouble.values_eq]
  simp only [rawEnv, ops1, ops2, runOps, List.foldl, FOp.run, Function.update_apply, VG.Proof.P256.EcdhDouble.values,
    h01, h02, h03, h04, h05, h06, h07, h08, h09, h12, h13, h14, h15, h16, h17, h18, h19,
    h23, h24, h25, h26, h27, h28, h29, h34, h35, h36, h37, h38, h39, h45, h46, h47, h48, h49,
    h56, h57, h58, h59, h67, h68, h69, h78, h79, h89, Ne.symm h01, Ne.symm h02, Ne.symm h03,
    Ne.symm h04, Ne.symm h05, Ne.symm h06, Ne.symm h07, Ne.symm h08, Ne.symm h09, Ne.symm h12,
    Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17, Ne.symm h18, Ne.symm h19,
    Ne.symm h23, Ne.symm h24, Ne.symm h25, Ne.symm h26, Ne.symm h27, Ne.symm h28, Ne.symm h29,
    Ne.symm h34, Ne.symm h35, Ne.symm h36, Ne.symm h37, Ne.symm h38, Ne.symm h39, Ne.symm h45,
    Ne.symm h46, Ne.symm h47, Ne.symm h48, Ne.symm h49, Ne.symm h56, Ne.symm h57, Ne.symm h58,
    Ne.symm h59, Ne.symm h67, Ne.symm h68, Ne.symm h69, Ne.symm h78, Ne.symm h79, Ne.symm h89,
    ↓reduceIte, Prod.mk.injEq]
  have h1 : Fin.ofNat m 1 = 1 := rfl
  have h3 : Fin.ofNat m 3 = 3 := rfl
  have h4 : Fin.ofNat m 4 = 4 := rfl
  have h8 : Fin.ofNat m 8 = 8 := rfl
  have h9 : Fin.ofNat m 9 = 9 := rfl
  have h12 : Fin.ofNat m 12 = 12 := rfl
  simp only [h1, h3, h4, h8, h9, h12]
  refine ⟨?_, ?_, ?_⟩ <;> grind

end VG.Proof.P384.EcdhDouble
