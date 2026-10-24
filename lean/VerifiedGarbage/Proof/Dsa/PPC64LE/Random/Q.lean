module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Copy
public import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Math

/-!
# DSA sampling on PPC64LE: the sampler's data of q

`SE.Q E qb`: the sampler's data are those of q's octets `qb`, for `q > 1`:
the width of a draw is `drawBytes q` (`Q.draw`), q's significant octets
decode to q (`Q.qs_val`), and a draw copied with its first octet masked
(`cpy`) decodes to the specification's candidate (`Q.cand`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG
open VG.Proof.Dsa (significant qSigOf)

/-- `E` is the sampler's data for q's octets `qb`, and `q > 1`. -/
structure SE.Q (E : SE) (qb : List Byte) : Prop where
  len : qb.length = E.ql
  W : E.W = (significant qb).1
  M : E.M = maskOf (significant qb).2.toNat
  qs : E.qs = qSigOf qb
  gt : 1 < Spec.Dsa.decodeBE qb

theorem SE.Q.draw {E : SE} {qb : List Byte} (h : E.Q qb) :
    Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE qb) = E.W := by
  rw [Dsa.random_drawBytes_scan, h.W]

theorem SE.Q.qs_val {E : SE} {qb : List Byte} (h : E.Q qb) :
    Spec.Dsa.decodeBE E.qs = Spec.Dsa.decodeBE qb := by
  rw [h.qs, qSigOf, Dsa.random_significant_drop]

theorem SE.Q.W_pos {E : SE} {qb : List Byte} (h : E.Q qb) : 0 < E.W := by
  have := (Dsa.random_valid_scan qb).mp h.gt
  rw [h.W]; omega

/-- The draw as the nonce gets it. -/
abbrev cpyList (bs : List Byte) (M W : Nat) : List Byte := (List.range W).map (cpy bs M)

theorem cpyList_take (bs : List Byte) (M W : Nat) : cpyList (bs.take W) M W = cpyList bs M W := by
  simp only [cpyList, List.map_inj_left, List.mem_range]
  intro j hj
  simp only [cpy, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj]
  split
  · rename_i h0; subst h0; rw [ite_eq_left hj]
  · rfl

theorem cpyList_cons (b : Byte) (bs : List Byte) (M : Nat) :
    cpyList (b :: bs) M (bs.length + 1) = (b &&& BitVec.ofNat 8 M) :: bs := by
  apply List.ext_getElem
  · simp [cpyList]
  · intro i h₁ h₂
    simp only [cpyList, List.getElem_map, List.getElem_range, cpy]
    cases i with
    | zero => simp
    | succ i =>
      simp only [Nat.add_one_ne_zero, ite_false, List.getElem_cons_succ]
      simp only [List.length_cons] at h₂
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < bs.length by omega)]

/-- The copied draw decodes to the candidate. -/
theorem SE.Q.cand {E : SE} {qb : List Byte} (h : E.Q qb) {bs : List Byte} (hl : E.W ≤ bs.length) :
    Spec.Dsa.decodeBE (cpyList bs E.M E.W) = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qb) (bs.take E.W) := by
  have hW := h.W_pos
  rw [← cpyList_take]
  obtain ⟨b, rest, he⟩ : ∃ b rest, bs.take E.W = b :: rest := by
    cases hc : bs.take E.W with
    | nil =>
      have := congrArg List.length hc
      rw [List.length_take, Nat.min_eq_left hl, List.length_nil] at this; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hrl : rest.length + 1 = E.W := by
    have := congrArg List.length he
    rw [List.length_take, List.length_cons, Nat.min_eq_left hl] at this; omega
  rw [he, ← hrl, cpyList_cons, Dsa.random_candidate_mask qb b rest (by rw [hrl, h.W]), h.M]

end VG.Proof.Dsa.PPC64LE.Rnd
