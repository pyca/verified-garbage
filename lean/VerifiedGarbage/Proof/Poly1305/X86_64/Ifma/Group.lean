module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Powers
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Group
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: groups of eight blocks

Each group of eight blocks but the last is added to the quadwords of `H`
(block `π k` to quadword `k`) and multiplied by `r⁸`, in `Y` (Horner's rule
in eight lanes, `Horner8.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr vec_mem vec_rd vec_wr)
open VG.Proof.Poly1305.X86_64.Avx512 (qz envOf_v VKeep pi blk blk_mv blk_length group_bytes pi_0 pi_1 pi_2 pi_3
  pi_4 pi_5 pi_6 pi_7)
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (mv lanes8 absorbAll)

/-- `Y` holds `R⁸` in every quadword, with `S`. -/
structure YInv (R : Nat) (s : State) : Prop where
  val : ∀ k < 8, yval s k ≡ R ^ 8 [MOD P]
  b : ∀ k < 8, ∀ i < 3, yv s k i ≤ 2 ^ 44
  sr : ∀ k < 8, sv s k 1 = 20 * yv s k 1 ∧ sv s k 2 = 20 * yv s k 2

theorem YInv.of_ys {R : Nat} {s s' : State} (h : YInv R s) (hy : ∀ k < 8, yv s' k = yv s k)
    (hs : ∀ k < 8, sv s' k = sv s k) : YInv R s' :=
  ⟨fun k hk => by simp only [yval]; rw [hy k hk]; exact h.val k hk,
   fun k hk => by rw [hy k hk]; exact h.b k hk,
   fun k hk => by rw [hs k hk, hy k hk]; exact h.sr k hk⟩

/-- The lanes of `H` weighted by the powers of `R` of the last group, in the
order of their blocks (block `j` is in quadword `2 j` for `j < 4`, else
`2 (j - 4) + 1`). -/
def wsum (R : Nat) (s : State) : Nat :=
  lanes8 R (hval s 0) (hval s 2) (hval s 4) (hval s 6) (hval s 1) (hval s 3) (hval s 5) (hval s 7)

/-- Between groups: `Y` holds `R⁸`, and the quadwords of `H` (limbs at most
`2⁴⁴`) the accumulator `X`, after Horner's rule in eight lanes. -/
structure LaneInv (R X : Nat) (s : State) : Prop where
  y : YInv R s
  hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44
  acc : wsum R s ≡ R ^ 8 * X [MOD P]

theorem LaneInv.of_vk {R X : Nat} {s s' : State} (h : LaneInv R X s) (hk : VKeep s s') : LaneInv R X s' := by
  have eh := VKeep.hv hk
  refine ⟨h.y.of_ys (fun k _ => by rw [VKeep.yv hk]) (fun k _ => by rw [VKeep.sv hk]),
    by rw [eh]; exact h.hb, ?_⟩
  simp only [wsum, hval, eh]; exact h.acc

theorem hval_add {a b c : Nat → Nat} (h : ∀ i < 3, a i = b i + c i) :
    Limbs44.val a = Limbs44.val b + Limbs44.val c := by
  simp only [Limbs44.val, h 0 (by decide), h 1 (by decide), h 2 (by decide)]
  omega

/-- `addGroup`, then `mul` by `Y`: quadword `k` becomes `(V_k + m_(π k)) · Y`. -/
theorem addMul_ok {s : State} (hc : Ctx s) (hm : Consts s) (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44)
    (hy : ∀ k < 8, ∀ i < 3, yv s k i ≤ 2 ^ 44) (hs : ∀ k < 8, sv s k 1 = 20 * yv s k 1 ∧ sv s k 2 = 20 * yv s k 2) :
    WP isa (.block (addGroup ++ mul)) s fun s' => vec s s' = s' ∧
      (∀ k < 8, yv s' k = yv s k) ∧ (∀ k < 8, sv s' k = sv s k) ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44) ∧
      ∀ k < 8, hval s' k ≡ (hval s k + mv (blk s (pi k))) * yval s k [MOD P] := by
  refine WP.block_append (WP.mono (addGroup_ok ⟨hc, hm, hb⟩) fun s₁ A => ?_)
  have ey := yv_of A.y
  have es := sv_of A.sr
  refine WP.mono (mulY_ok (Ctx.of_vec hc A.vec) (by rw [mb_of_vec A.vec, hm.mask]) A.hb
    (fun k hk => by rw [ey k hk]; exact hy k hk) (fun k hk => by rw [es k hk, ey k hk]; exact hs k hk))
    fun s₂ ⟨v₂, E₂, b₂, y₂, z₂⟩ => ⟨vec_trans A.vec v₂, fun k hk => by rw [y₂ k hk, ey k hk],
      fun k hk => by rw [z₂ k hk, es k hk], b₂, fun k hk => ?_⟩
  have e := E₂ k hk
  simp only [hval, yval] at e ⊢
  rw [A.h k hk, ey k hk, ← blk_mv] at e
  exact e

/-- A group before the last: the invariant for the blocks so far and the group. -/
theorem group_ok {R X : Nat} {s : State} (hc : Ctx s) (hm : Consts s) (hI : LaneInv R X s) :
    WP isa (.block (addGroup ++ mul)) s fun s' => vec s s' = s' ∧
      LaneInv R (absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128)) s' := by
  refine WP.mono (addMul_ok hc hm hI.hb hI.y.b hI.y.sr) fun s' ⟨hv', hy, hs, hb, he⟩ =>
    ⟨hv', hI.y.of_ys hy hs, hb, ?_⟩
  have e : ∀ k < 8, hval s' k ≡ (hval s k + mv (blk s (pi k))) * R ^ 8 [MOD P] := fun k hk =>
    (he k hk).trans (Nat.ModEq.mul_left _ (hI.y.val k hk))
  rw [group_bytes]
  have L := blk_length s
  exact Poly1305.horner8_step (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (by simpa only [pi_0] using e 0 (by decide)) (by simpa only [pi_2] using e 2 (by decide))
    (by simpa only [pi_4] using e 4 (by decide)) (by simpa only [pi_6] using e 6 (by decide))
    (by simpa only [pi_1] using e 1 (by decide)) (by simpa only [pi_3] using e 3 (by decide))
    (by simpa only [pi_5] using e 5 (by decide)) (by simpa only [pi_7] using e 7 (by decide))

end VG.Proof.Poly1305.X86_64.Ifma
