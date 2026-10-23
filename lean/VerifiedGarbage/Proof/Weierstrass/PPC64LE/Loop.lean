module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Loop
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Short Weierstrass curves on PPC64LE: loops counted down in `r31`

The ladder, the powers and the tables of bits loop with `r31` counting down:
the body starts with `subi r31, r31, 1` (`wp_decCounter`), and the loop runs
while `r31 ≠ 0` (`more`). `countLoop_ok` runs such a loop `n ≥ 1` times from
an invariant indexed by `r31`, as on 32-bit ARM
(`Proof/Weierstrass/Arm/Loop.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE

/-- A loop whose body takes the invariant from `j` to `j - 1`, with `r31 = j`
in the invariant, run from `n ≥ 1` (below `2⁶⁴`). -/
theorem countLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hr : ∀ j s, Inv j s → s.gpr .r31 = BitVec.ofNat 64 j)
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s → WP isa body s fun s' => Inv (j - 1) s')
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) {s : State} (hs : Inv n s) :
    WP isa (.loop body more) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' hi' => ?_
  have he := eval_nonzero_ofNat (hr _ _ hi') (x := j - 1) (by omega)
  by_cases hj : j - 1 = 0
  · exact .inl ⟨by rw [he]; simp [hj], hQ s' (by rw [hj] at hi'; exact hi')⟩
  · exact .inr ⟨by rw [he]; simp [hj], j - 1, by omega, by omega, by omega, hi'⟩

theorem ofNat_pred64 {j : Nat} (hj : 1 ≤ j) : BitVec.ofNat 64 j - BitVec.ofNat 64 1 = BitVec.ofNat 64 (j - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `r31 -= 1`. -/
theorem wp_decCounter {is : List Instr} {s : State} {Q : State → Prop} {j : Nat} (hj : 1 ≤ j)
    (hb : s.gpr .r31 = BitVec.ofNat 64 j)
    (k : WP isa (.block is) (s.write .r31 (BitVec.ofNat 64 (j - 1))) Q) :
    WP isa (.block (decCounter :: is)) s Q := by
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  rw [hb, ofNat_pred64 hj]; exact k

end VG.Proof.Weierstrass.PPC64LE
