module

public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy

/-!
# ML-KEM on x86-64: the bounds of the lazy butterflies

`fwd_hop` and `inv_hop` bound a lazy butterfly of `NTT` (`fwdW`) and of
`NTT⁻¹` (`invW`), for the NTT on registers (`NttR/Model.lean`,
`NttR/InvModel.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem fwd_hop {k : Nat} (hk : (k + 1) * 3329 ≤ 32768) :
    ∀ (a b : BitVec 16) (x y ζ : Zq), Rep k a x → Rep k b y →
      Rep (k + 1) (fwdW a b ζ).1 ((fun x y z => (x + z * y, x - z * y)) x y ζ).1 ∧
        Rep (k + 1) (fwdW a b ζ).2 ((fun x y z => (x + z * y, x - z * y)) x y ζ).2 :=
  fun _ _ _ _ ζ ha hb => fwdW_rep hk ζ ha hb.2.2

theorem inv_hop {k : Nat} (hk : 2 * k * 3329 ≤ 32768) (hk1 : 1 ≤ 2 * k) :
    ∀ (a b : BitVec 16) (x y ζ : Zq), Rep k a x → Rep k b y →
      Rep (2 * k) (invW a b ζ).1 ((fun x y z => (x + y, z * (y - x))) x y ζ).1 ∧
        Rep (2 * k) (invW a b ζ).2 ((fun x y z => (x + y, z * (y - x))) x y ζ).2 :=
  fun _ _ _ _ ζ ha hb => ⟨(invW_rep hk ζ ha hb).1, (invW_rep hk ζ ha hb).2.mono hk1⟩

theorem getElem!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (v : Vector α n) {i : Nat} (hi : i < 256) :
    (v.map f)[i]! = f v[i]! := by
  rw [getElem!_pos _ i (by rw [n_eq]; exact hi), getElem!_pos _ i (by rw [n_eq]; exact hi), Vector.getElem_map]

end VG.Proof.MlKem.X86_64
