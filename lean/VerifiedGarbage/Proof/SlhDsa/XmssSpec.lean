module

-- separate module: the specification's facts, which every target's proof of `xmssTree` uses

public import VerifiedGarbage.Proof.SlhDsa.Internal
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA: the trees `xmssTree` computes

Target-independent facts the proofs of `xmssTree`
(`Impl/SlhDsa/<Target>/Xmss.lean`) need: the trees as `levels` states them
(`upNodes`, `pick`) are the XMSS tree (`xmss_node`, Algorithm 9) and its
authentication path (`xmss_sign`, Algorithm 10).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.XmssTree

open VG VG.Spec.SlhDsa VG.Proof.SlhDsa

variable {p : Params}

/-! ## The trees, as `levels` computes them -/

theorem length_treeAdrs {a16 : List Byte} (ha : a16.length = 16) : (treeAdrs a16).length = 32 := by
  simp [treeAdrs, ha, length_toByte]

/-- A cleared address has the key pair address 0. -/
theorem setKeyPairAddress_setTypeAndClear_zero {a : Adrs} (h : a.length = 32) (Y : Nat) :
    setKeyPairAddress (setTypeAndClear a Y) 0 = setTypeAndClear a Y := by
  have h1 := length_setTypeAndClear h Y
  apply ext_getD (by rw [length_setKeyPairAddress h1, h1])
  intro j hj
  rw [length_setKeyPairAddress h1] at hj
  rw [getD_setKeyPairAddress h1, getD_setTypeAndClear h, getD_toByte_zero]
  rcases (show j < 16 ∨ (16 ≤ j ∧ j < 20) ∨ (20 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 28) ∨ (28 ≤ j ∧ j < 32) ∨ 32 ≤ j
    by omega) with hr | hr | hr | hr | hr | hr <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

theorem nodeAdrs_tree {a16 : List Byte} (ha : a16.length = 16) (z j : Nat) :
    nodeAdrs a16 TREE 0 z j = setTreeIndex (setTreeHeight (setTypeAndClear (treeAdrs a16) TREE) z) j := by
  rw [nodeAdrs, setKeyPairAddress_setTypeAndClear_zero (length_treeAdrs ha)]

/-- The leaves of an XMSS tree. -/
abbrev leaf (p : Params) (skSeed pkSeed a16 : List Byte) (j : Nat) : List Byte :=
  xmssNode p skSeed j 0 pkSeed (treeAdrs a16)

theorem leaf_eq (skSeed pkSeed a16 : List Byte) (j : Nat) :
    wotsPkGen p skSeed pkSeed (wotsAdrs a16 j) = leaf p skSeed pkSeed a16 j := by
  rw [leaf, xmssNode_zero]; rfl

/-- The nodes `levels` computes `r` heights above the nodes of height `z` of
an XMSS tree: those of height `z + r`. -/
theorem upNodes_xmss {a16 : List Byte} (ha : a16.length = 16) (skSeed pkSeed : List Byte) :
    ∀ (r z k : Nat), upNodes p pkSeed a16 TREE 0 0 z
      ((List.range (2 ^ (k + r))).map fun j => xmssNode p skSeed j z pkSeed (treeAdrs a16)) r =
      (List.range (2 ^ k)).map fun j => xmssNode p skSeed j (z + r) pkSeed (treeAdrs a16)
  | 0, z, k => rfl
  | r + 1, z, k => by
    rw [upNodes, show z + (r + 1) = z + 1 + r by omega, ← upNodes_xmss ha skSeed pkSeed r (z + 1) k]
    refine congrArg (fun L => upNodes p pkSeed a16 TREE 0 0 (z + 1) L r) ?_
    rw [List.length_map, List.length_range, show k + (r + 1) = k + r + 1 by omega,
      show 2 ^ (k + r + 1) / 2 = 2 ^ (k + r) by rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]]
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    have h2 : 2 * j + 1 < 2 ^ (k + r + 1) := by rw [Nat.pow_succ]; omega
    rw [Nat.zero_div, Nat.zero_add, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_map, List.getElem?_range (by omega), List.getElem?_range h2,
      Option.map_some, Option.map_some, Option.getD_some, Option.getD_some, xmssNode_succ, nodeAdrs_tree ha]

/-- The node of the authentication path at height `r` that `levels` picks. -/
theorem pick_xmss {f : Nat → List Byte} {r idx : Nat} (hr : r < p.hp) (hidx : idx < 2 ^ p.hp) :
    pick p.n ((List.range (2 ^ (p.hp - r))).map f) (0 / 2 ^ (0 + r)) idx (0 + r) = f (idx / 2 ^ r ^^^ 1) := by
  have hq : idx / 2 ^ r < 2 ^ (p.hp - r) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel (by omega)]; exact hidx
  have hx : idx / 2 ^ r ^^^ 1 < 2 ^ (p.hp - r) :=
    Nat.xor_lt_two_pow hq (Nat.lt_of_lt_of_le (show 1 < 2 ^ 1 by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  simp only [pick, Nat.zero_div, Nat.zero_add, List.length_map, List.length_range, Nat.zero_le, true_and, hx,
    ↓reduceIte, Nat.sub_zero]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx, Option.map_some, Option.getD_some]

theorem xorB_zero {x : List Byte} {k : Nat} (h : x.length = k) : xorB (List.replicate k 0) x = x := by
  subst h
  induction x with
  | nil => rfl
  | cons a x ih => simp only [xorB, List.length_cons, List.replicate_succ, List.zipWith_cons_cons] at ih ⊢; rw [ih]; simp

end VG.Proof.SlhDsa.X86_64.XmssTree
