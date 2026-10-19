module

public import VerifiedGarbage.Proof.P256.VerifyTable.Field
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import all Init.Data.Nat.Bitwise.Basic

/-! Runs of field-slot copies: each copy `(o, a)` updates the environment at
`o` with its value at `a`. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

def copies (l : List (Nat × Nat)) : List Instr := l.flatMap fun p => copy 4 p.1 p.2

/-- The environment after the copies `l`. -/
def copiesEnv {F : Type _} : List (Nat × Nat) → (Nat → F) → Nat → F
  | [], E => E
  | p :: l, E => copiesEnv l (Function.update E p.1 (E p.2))

/-- The live slots after the copies `l` from the live slots `V`. -/
def copiesV : List (Nat × Nat) → List Nat → List Nat
  | [], V => V
  | p :: l, V => copiesV l (p.1 :: V)

/-- Each copy reads a live slot. -/
def copiesOk : List (Nat × Nat) → List Nat → Bool
  | [], _ => true
  | p :: l, V => decide (p.2 ∈ V) && copiesOk l (p.1 :: V)

theorem copies_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl) :
    ∀ (l : List (Nat × Nat)) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State},
    Inv M base 8192 C.p Sl V E s → (∀ p∈l,Sl p.1) → copiesOk l V=true →
    WP isa (.block (copies l)) s fun t =>
      ProgKeep M base (l.map Prod.fst) s t ∧ Inv M base 8192 C.p Sl (copiesV l V) (copiesEnv l E) t
  | [], _, _, _, s, hi, _, _ => by
    apply WP.of_runBlock
    exact ⟨s,rfl,ProgKeep.refl _ _ _ _,hi⟩
  | p :: l, base, V, E, s, hi, hs, hok => by
    simp only [copiesOk,Bool.and_eq_true,decide_eq_true_eq] at hok
    change WP isa (.block (copy 4 p.1 p.2 ++ copies l)) s _
    rw [WP.block_append_iff]
    refine WP.mono (copyField_ok layout aligned hi (hs p (List.mem_cons_self ..)) hok.1)
      fun a ⟨ka,ia⟩ => ?_
    refine WP.mono (copies_ok layout aligned l ia (fun q hq => hs q (List.mem_cons_of_mem _ hq)) hok.2)
      fun t ⟨kt,it⟩ => ⟨?_,it⟩
    exact (progKeep_of_op ka (List.mem_cons_self ..)).trans
      (kt.mono fun w hw => List.mem_cons_of_mem _ hw)

end VG.Proof.P256.VerifyTable
