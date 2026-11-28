module

-- separate module: the specification's facts, which every module of `forsSign`'s proof uses

public import VerifiedGarbage.Proof.SlhDsa.Fld
import VerifiedGarbage.Proof.SlhDsa.VerifySpec
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.SlhDsa.LevelsSpec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA: the values `forsSign` computes

Target-independent facts the proof of `forsSign`
(`Impl/SlhDsa/X86_64/Fors.lean`) needs about the specification:

* the FORS addresses as their fields (`fld`): a node's, a private key
  value's and the roots';
* `up_node`: the heights `levels` computes (`upNodes`) above aligned nodes
  of the FORS trees are their nodes higher up;
* `pick_eq`, `acc_succ`, `acc_all`: the node of an authentication path a
  subtree's heights XOR in, and the path after all subtrees;
* `index_eq`: index `t` of `base_2b(md, a, k)` from the three bytes
  `Fors.index` reads, any bytes past `md` shifted out.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.Spec.SlhDsa VG.Proof.SlhDsa

/-! ## Addresses -/

section Adrs
variable {a16 : List Byte} (h16 : a16.length = 16) (kp : Nat)
include h16

theorem forsAdrs_fld : forsAdrs a16 kp = fld a16 FORS_TREE kp 0 0 := by
  rw [forsAdrs, treeAdrs_eq, setTypeAndClear_fld h16, setKeyPairAddress_fld h16]

theorem forsAdrs_length : (forsAdrs a16 kp).length = 32 := by
  rw [forsAdrs_fld h16]; exact fld_length h16 _ _ _ _

theorem nodeAdrs_fld (ty z j : Nat) : nodeAdrs a16 ty kp z j = fld a16 ty kp z j := by
  rw [nodeAdrs, treeAdrs_eq, setTypeAndClear_fld h16, setKeyPairAddress_fld h16, setTreeHeight_fld h16,
    setTreeIndex_fld h16]

/-- The address of node `i` of height `z`. -/
theorem node_adrs (z i : Nat) : setTreeIndex (setTreeHeight (forsAdrs a16 kp) z) i = fld a16 FORS_TREE kp z i := by
  rw [forsAdrs_fld h16, setTreeHeight_fld h16, setTreeIndex_fld h16]

/-- The address of the private key value of leaf `i` (`fors_skGen`). -/
theorem sk_adrs (hkp : kp < 2 ^ 32) (i : Nat) :
    setTreeIndex (setKeyPairAddress (setTypeAndClear (forsAdrs a16 kp) FORS_PRF) (getKeyPairAddress (forsAdrs a16 kp)))
      i = fld a16 FORS_PRF kp 0 i := by
  rw [forsAdrs_fld h16, getKeyPairAddress_fld h16, Nat.mod_eq_of_lt hkp, setTypeAndClear_fld h16,
    setKeyPairAddress_fld h16, setTreeIndex_fld h16]

/-- The address of `T_k` of the roots. -/
theorem roots_adrs (hkp : kp < 2 ^ 32) :
    setKeyPairAddress (setTypeAndClear (forsAdrs a16 kp) FORS_ROOTS) (getKeyPairAddress (forsAdrs a16 kp)) =
      fld a16 FORS_ROOTS kp 0 0 := by
  rw [forsAdrs_fld h16, getKeyPairAddress_fld h16, Nat.mod_eq_of_lt hkp, setTypeAndClear_fld h16,
    setKeyPairAddress_fld h16]

theorem getKeyPairAddress_forsAdrs (hkp : kp < 2 ^ 32) : getKeyPairAddress (forsAdrs a16 kp) = kp := by
  rw [forsAdrs_fld h16, getKeyPairAddress_fld h16, Nat.mod_eq_of_lt hkp]

end Adrs

/-! ## The heights above aligned nodes -/

variable (p : Params) (skSeed pkSeed a16 : List Byte) (kp : Nat)

/-- Node `i` of height `z` of the FORS trees of the key pair `kp`. -/
abbrev node (i z : Nat) : List Byte := forsNode p skSeed i z pkSeed (forsAdrs a16 kp)

/-- `⌊b / 2^e⌋ = 2⌊b / 2^(e+1)⌋` for `b` a multiple of `2^(e+1)`. -/
theorem div_two_mul {b e : Nat} (h : 2 ^ (e + 1) ∣ b) : b / 2 ^ e = 2 * (b / 2 ^ (e + 1)) := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.mul_div_cancel_left c (Nat.two_pow_pos (e + 1)), Nat.pow_succ, Nat.mul_assoc,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos e)]

/-- The heights `levels` computes above `2^m` nodes of height `z` of the FORS
trees, the first node `base / 2^z` (a multiple of `2^m`): node `j` of height
`z + r` is node `base / 2^(z+r) + j` of the trees. -/
theorem up_node {base z m : Nat} {L : List (List Byte)} (hL : L.length = 2 ^ m) (hd : 2 ^ (z + m) ∣ base)
    (hl : ∀ j < 2 ^ m, L.getD j [] = node p skSeed pkSeed a16 kp (base / 2 ^ z + j) z) :
    ∀ r ≤ m, (upNodes p pkSeed a16 FORS_TREE kp base z L r).length = 2 ^ (m - r) ∧
      ∀ j < 2 ^ (m - r), (upNodes p pkSeed a16 FORS_TREE kp base z L r).getD j [] =
        node p skSeed pkSeed a16 kp (base / 2 ^ (z + r) + j) (z + r) := by
  intro r
  induction r with
  | zero => intro _; exact ⟨by rw [Nat.sub_zero]; exact hL, fun j hj => by rw [Nat.sub_zero] at hj; exact hl j hj⟩
  | succ r ih =>
    intro hr
    obtain ⟨hlen, hget⟩ := ih (by omega_using [hr])
    have e : 2 ^ (m - r) = 2 * 2 ^ (m - (r + 1)) := by
      rw [show m - r = m - (r + 1) + 1 by omega_using [hr], Nat.pow_succ, Nat.mul_comm]
    have hdv : 2 ^ (z + r + 1) ∣ base :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega_using [hr])) hd
    have hb : base / 2 ^ (z + r) = 2 * (base / 2 ^ (z + r + 1)) := div_two_mul hdv
    rw [Levels.upNodes_succ]
    refine ⟨by rw [Levels.length_step, hlen, e, Nat.mul_div_cancel_left _ (by decide)], fun j hj => ?_⟩
    rw [Levels.getD_step _ _ _ _ _ _ _ _ (by rw [hlen, e, Nat.mul_div_cancel_left _ (by decide)]; exact hj),
      hget (2 * j) (by omega_using [e, hj]), hget (2 * j + 1) (by omega_using [e, hj])]
    simp only [node]
    rw [show z + (r + 1) = z + r + 1 from rfl, forsNode_succ, hb]
    rw [show 2 * (base / 2 ^ (z + r + 1)) + 2 * j = 2 * (base / 2 ^ (z + r + 1) + j) by omega_using [],
      show 2 * (base / 2 ^ (z + r + 1)) + (2 * j + 1) = 2 * (base / 2 ^ (z + r + 1) + j) + 1 by omega_using []]
    rfl

/-! ## The authentication path -/

/-- `pick` from nodes that are a run of a function's values. -/
theorem pick_eq {n first idx z c : Nat} {L : List (List Byte)} (hlen : L.length = c) (f : Nat → List Byte)
    (hget : ∀ j < c, L.getD j [] = f (first + j)) :
    pick n L first idx z =
      if first ≤ idx / 2 ^ z ^^^ 1 ∧ idx / 2 ^ z ^^^ 1 < first + c then f (idx / 2 ^ z ^^^ 1) else toByte 0 n := by
  dsimp only [pick]
  rw [hlen]
  split
  · rename_i h
    rw [hget _ (by omega_using [h]), Nat.add_sub_cancel' h.1]
  · rfl

theorem xorB_zero_left {x : List Byte} {n : Nat} (h : x.length = n) : xorB (toByte 0 n) x = x := by
  subst h
  rw [toByte_zero]
  induction x with
  | nil => rfl
  | cons b x ih => simp only [xorB, List.length_cons, List.replicate_succ, List.zipWith_cons_cons] at ih ⊢; rw [ih]; simp

theorem xorB_zero_right {x : List Byte} {n : Nat} (h : x.length = n) : xorB x (toByte 0 n) = x := by
  subst h
  rw [toByte_zero]
  induction x with
  | nil => rfl
  | cons b x ih => simp only [xorB, List.length_cons, List.replicate_succ, List.zipWith_cons_cons] at ih ⊢; rw [ih]; simp

/-- The sibling at height `r` of the index `idx`. -/
abbrev sib (idx r : Nat) : Nat := idx / 2 ^ r ^^^ 1

/-- The authentication path's node of height `r` of tree `t` once the
subtrees before `u` (of height `s`) have XORed theirs in: the node if one of
them has it. -/
def acc (t idx s a r u : Nat) : List Byte :=
  if sib idx r < u * 2 ^ (s - r) then node p skSeed pkSeed a16 kp (t * 2 ^ (a - r) + sib idx r) r else toByte 0 p.n

theorem acc_zero (t idx s a r : Nat) : acc p skSeed pkSeed a16 kp t idx s a r 0 = toByte 0 p.n := by
  simp [acc]

/-- Subtree `u`'s heights XOR in its node of the path, if it has it. -/
theorem acc_succ (hn : p.n ≤ 32) (t idx s a r u : Nat) :
    xorB (acc p skSeed pkSeed a16 kp t idx s a r u)
      (if u * 2 ^ (s - r) ≤ sib idx r ∧ sib idx r < u * 2 ^ (s - r) + 2 ^ (s - r) then
        node p skSeed pkSeed a16 kp (t * 2 ^ (a - r) + sib idx r) r else toByte 0 p.n) =
      acc p skSeed pkSeed a16 kp t idx s a r (u + 1) := by
  have hl := forsNode_length hn skSeed pkSeed (forsAdrs a16 kp) (t * 2 ^ (a - r) + sib idx r) r
  have e : (u + 1) * 2 ^ (s - r) = u * 2 ^ (s - r) + 2 ^ (s - r) := Nat.succ_mul _ _
  unfold acc
  rw [e]
  by_cases h₁ : sib idx r < u * 2 ^ (s - r)
  · rw [ite_eq_left h₁, ite_eq_right (by omega_using [h₁]), ite_eq_left (by omega_using [h₁]), xorB_zero_right hl]
  · rw [ite_eq_right h₁]
    by_cases h₂ : sib idx r < u * 2 ^ (s - r) + 2 ^ (s - r)
    · rw [ite_eq_left ⟨by omega_using [h₁], h₂⟩, ite_eq_left h₂, xorB_zero_left hl]
    · rw [ite_eq_right (by omega_using [h₂]), ite_eq_right h₂, xorB_zero_left (by simp [toByte_zero])]

/-- The sibling of an index of a tree of height `a` is in the tree. -/
theorem sib_lt {idx a r : Nat} (hidx : idx < 2 ^ a) (hr : r < a) : sib idx r < 2 ^ (a - r) := by
  have h1 : idx / 2 ^ r < 2 ^ (a - r) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos r), ← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hr)]
    exact hidx
  have h2 : 2 ≤ 2 ^ (a - r) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ a - r by omega_using [hr]); simpa using this
  exact Nat.xor_lt_two_pow h1 (by omega_using [h2])

/-- After all `2^(a-s)` subtrees, a node of the path of height `r < s` is the
tree's. -/
theorem acc_all {t idx s a r : Nat} (hidx : idx < 2 ^ a) (hs : s ≤ a) (hr : r < s) :
    acc p skSeed pkSeed a16 kp t idx s a r (2 ^ (a - s)) =
      node p skSeed pkSeed a16 kp (t * 2 ^ (a - r) + sib idx r) r := by
  unfold acc
  rw [ite_eq_left]
  rw [← Nat.pow_add, show a - s + (s - r) = a - r by omega_using [hs, hr]]
  exact sib_lt hidx (by omega_using [hs, hr])

/-! ## The indices -/

/-- Shifting out the low `e` bits of `X·2^e + y`. -/
theorem div_low {X y e sh : Nat} (hy : y < 2 ^ e) (he : e ≤ sh) : (X * 2 ^ e + y) / 2 ^ sh = X / 2 ^ (sh - e) := by
  rw [show sh = e + (sh - e) by omega_using [he], Nat.pow_add, ← Nat.div_div_eq_div_mul,
    show (X * 2 ^ e + y) / 2 ^ e = X by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos e), Nat.div_eq_of_lt hy, Nat.zero_add],
    Nat.add_sub_cancel_left]

/-- Index `t` of `base_2b(md, a, k)`, `0 < a ≤ 14`, `t < k`, `md` its
`⌈k·a / 8⌉` bytes: from the three bytes from byte `⌊t·a / 8⌋`, those past
`md` anything (they are shifted out). -/
theorem index_eq {md : List Byte} {a k t : Nat} (hmd : md.length = (k * a + 7) / 8) (ha : a ≤ 14) (ht : t < k)
    {x₀ x₁ x₂ : Nat} (h₀ : x₀ = (md.getD (t * a / 8) 0).toNat)
    (h₁ : t * a / 8 + 1 < md.length → x₁ = (md.getD (t * a / 8 + 1) 0).toNat)
    (h₂ : t * a / 8 + 2 < md.length → x₂ = (md.getD (t * a / 8 + 2) 0).toNat) (hx₁ : x₁ < 256) (hx₂ : x₂ < 256) :
    (base2b md a k).getD t 0 = (x₀ * 65536 + x₁ * 256 + x₂) / 2 ^ (24 - t * a % 8 - a) % 2 ^ a := by
  rw [base2b_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht, Option.map_some,
    Option.getD_some, digitAt_three md ha t, ← h₀]
  have hc := ceil8 (k * a)
  have hta : (t + 1) * a ≤ k * a := Nat.mul_le_mul_right _ ht
  have e : (t + 1) * a = t * a + a := Nat.succ_mul t a
  have h8 := Nat.div_add_mod (t * a) 8
  have hm := Nat.mod_lt (t * a) (show 0 < 8 by decide)
  have b₁ := ((md.getD (t * a / 8 + 1) 0)).isLt
  have b₂ := ((md.getD (t * a / 8 + 2) 0)).isLt
  generalize (md.getD (t * a / 8 + 1) 0).toNat = y₁ at h₁ b₁ ⊢
  generalize (md.getD (t * a / 8 + 2) 0).toNat = y₂ at h₂ b₂ ⊢
  have hlen : md.length = (k * a + 7) / 8 := hmd
  by_cases c₂ : t * a / 8 + 2 < md.length
  · rw [h₁ (by omega_using [c₂]), h₂ c₂]
  · -- the third byte is shifted out
    have hsh : 8 ≤ 24 - t * a % 8 - a := by omega_using [c₂, hlen, hc, hta, e, h8, hm]
    have l₁ : x₁ * 256 + x₂ = x₁ * 2 ^ 8 + x₂ := rfl
    have l₂ : y₁ * 256 + y₂ = y₁ * 2 ^ 8 + y₂ := rfl
    rw [Nat.add_assoc, Nat.add_assoc, show x₀ * 65536 + (x₁ * 256 + x₂) = (x₀ * 256 + x₁) * 2 ^ 8 + x₂ by omega_using [],
      show x₀ * 65536 + (y₁ * 256 + y₂) = (x₀ * 256 + y₁) * 2 ^ 8 + y₂ by omega_using [],
      div_low hx₂ hsh, div_low b₂ hsh]
    by_cases c₁ : t * a / 8 + 1 < md.length
    · rw [h₁ c₁]
    · -- so is the second
      have hsh' : 8 ≤ 24 - t * a % 8 - a - 8 := by omega_using [c₁, hlen, hc, hta, e, h8, hm]
      rw [show (x₀ * 256 + x₁) = x₀ * 2 ^ 8 + x₁ from rfl, show (x₀ * 256 + y₁) = x₀ * 2 ^ 8 + y₁ from rfl,
        div_low hx₁ hsh', div_low b₁ hsh']

end VG.Proof.SlhDsa.X86_64.Fors
