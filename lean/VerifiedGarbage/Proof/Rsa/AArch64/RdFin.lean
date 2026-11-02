module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: the factors

`factorsA_ok`: `p = ((b + ϒ) mod 2^(64 v)) / 2` (narrow array 8) and
`q = (b - ϒ) / 2` (9); `stores_ok`: both written under the mask, and the
mask returned.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet

/-- The factors' arithmetic. -/
abbrev factorsA : List (Prog isa) :=
  [.block ones, zeroA nP, addA nP nB nY, halfA nP nP, zeroA nQ, subA nQ nB nY, halfA nQ nQ]

theorem factorsA_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I) {b y : Nat}
    (hb : wv s.mem I.B (slot (vk I.k) nB) (vk I.k) = b) (hy : wv s.mem I.B (slot (vk I.k) nY) (vk I.k) = y) :
    WP isa (seqs factorsA) s fun t => G I m₀ (vk I.k) c t ∧
      wv t.mem I.B (slot (vk I.k) nP) (vk I.k) = (b + y) % 2 ^ (64 * vk I.k) / 2 ∧
      wv t.mem I.B (slot (vk I.k) nQ) (vk I.k) = wsub (64 * vk I.k) b y / 2 := by
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hb32 := hb32_of h L
  have s4 := slot_lt (w := vk I.k) (show nY < 32 by decide)
  have s6 := slot_lt (w := vk I.k) (show nB < 32 by decide)
  have s8 := slot_lt (w := vk I.k) (show nP < 32 by decide)
  have s9 := slot_lt (w := vk I.k) (show nQ < 32 by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (ones_ok s) fun s₁ ⟨⟨h15, _, m₁⟩, k₁⟩ => ?_)
  have g₁ := h.same m₁ k₁ (by decide)
  refine WP.seq (WP.mono (zeroA_ok g₁.ws (j := nP) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  have b₂ : wv s₂.mem I.B (slot (vk I.k) nB) (vk I.k) = b := by
    rw [o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), m₁, hb]
  have y₂ : wv s₂.mem I.B (slot (vk I.k) nY) (vk I.k) = y := by
    rw [o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), m₁, hy]
  refine WP.seq (WP.mono (addA_ok g₂.ws (o := nP) (a := nB) (b := nY) (by decide) (by decide) (by decide)
    (by decide) (by decide) (c := true) ((k₂.gpr .x15 (by decide)).trans h15)) fun s₃ ⟨v₃, _, o₃, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (by omega) o₃ k₃ (by decide)
  simp only [↓reduceIte] at v₃
  rw [b₂, y₂] at v₃
  refine WP.seq (WP.mono (halfA_ok g₃.ws (o := nP) (a := nP) (by decide) (by decide) (by
    rw [o₃.word (.inr (by omega)) (by omega)]; exact (wv_eq_zero_iff _ _ _ _).mp z₂ (vk I.k) (by omega)))
    fun s₄ ⟨v₄, o₄, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (by omega) o₄ k₄ (by decide)
  rw [v₃] at v₄
  refine WP.seq (WP.mono (zeroA_ok g₄.ws (j := nQ) (by decide)) fun s₅ ⟨z₅, o₅, _, _, _, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq (WP.mono (subA_ok g₅.ws (o := nQ) (a := nB) (b := nY) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨v₆, _, _, o₆, k₆⟩ => ?_)
  have g₆ := g₅.out (by decide) (by omega) o₆ k₆ (by decide)
  have b₅ : wv s₅.mem I.B (slot (vk I.k) nB) (vk I.k) = b := by
    rw [o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), b₂]
  have y₅ : wv s₅.mem I.B (slot (vk I.k) nY) (vk I.k) = y := by
    rw [o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), y₂]
  rw [b₅, y₅] at v₆
  have q₆ := sub_wsub (wv_lt _ _ _ _) v₆
  refine WP.mono (halfA_ok g₆.ws (o := nQ) (a := nQ) (by decide) (by decide) (by
    rw [o₆.word (.inr (by omega)) (by omega)]; exact (wv_eq_zero_iff _ _ _ _).mp z₅ (vk I.k) (by omega)))
    fun t ⟨v₇, o₇, k₇⟩ => ⟨g₆.out (by decide) (by omega) o₇ k₇ (by decide), ?_, by rw [v₇, q₆]⟩
  rw [o₇.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
    o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₄]

/-- The stores of `p` (narrow array 8) and `q` (9), and the exit. -/
theorem stores_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {k el dl : Nat}
    {pP pQ pN pE pD : Addr} (ha : RpArgs s.mem B k el dl pP pQ pN pE pD) {c : Bool}
    (hm : word s.mem B (8 * Public.sMask) = mask c) (hk1 : 1 ≤ k) (hk2 : k ≤ 8 * w)
    (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : Apart pP k pQ k) :
    WP isa (seqs (storeA nP VG.Impl.Rsa.AArch64.Recover.sP Public.sK Public.sMask ++
      (storeA nQ VG.Impl.Rsa.AArch64.Recover.sQ Public.sK Public.sMask ++ ([.block retMask] : List (Prog isa))))) s fun t =>
      (List.range k).map (fun i => t.mem (pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w nP) ((k + 7) / 8) else 0) k ∧
      (List.range k).map (fun i => t.mem (pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w nQ) ((k + 7) / 8) else 0) k ∧
      t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧
      (∀ x, (∀ i < k, x ≠ pP + BitVec.ofNat 64 i) → (∀ i < k, x ≠ pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep (.x0 :: mmRegs) s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have sl : ∀ j < 16, slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  have fw : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ i < 32, word m' B (8 * i) = word m B (8 * i) :=
    fun hf i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  have fv : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ j < 16, ∀ n ≤ w + 2,
      wv m' B (slot w j) n = wv m B (slot w j) n := fun hf j hj n hn' =>
    hf.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := sl j hj; exact Or.inl (by omega))
      (by have := sl j hj; omega)
  refine wp_seqs_append (by simp [storeA]) (by simp [storeA]) (WP.mono (storeA_ws h (by decide) (by decide)
    (by decide) ha.p ha.k hm hk1 hk2 oP.wr oP.sep) fun s₁ ⟨b₁, x₁, h₁, f₁, k₁⟩ => ?_)
  have hm₁ : word s₁.mem B (8 * Public.sMask) = mask c := by rw [fw f₁ _ (by decide)]; exact hm
  refine wp_seqs_append (by simp [storeA]) (by simp) (WP.mono (storeA_ws h₁ (by decide) (by decide)
    (by decide) (by rw [fw f₁ _ (by decide)]; exact ha.q) (by rw [fw f₁ _ (by decide)]; exact ha.k) hm₁ hk1 hk2
    (fun i hi => by rw [k₁.wr]; exact oQ.wr i hi) oQ.sep) fun s₂ ⟨b₂, x₂, h₂, f₂, k₂⟩ => ?_)
  have hm₂ : word s₂.mem B (8 * Public.sMask) = mask c := by rw [fw f₂ _ (by decide)]; exact hm₁
  simp only [seqs]
  refine WP.mono (cvExit_ok h₂ hm₂) fun t ⟨⟨hax, hmt⟩, k₃⟩ => ?_
  rw [hmt]
  refine ⟨?_, ?_, hax, fun x n1 n2 => by rw [x₂ x n2, x₁ x n1], ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [← b₁]
    exact List.map_congr_left fun i hi => by
      have hi' := List.mem_range.mp hi
      rw [x₂ _ (fun j hj => a i hi' j hj)]
  · rw [fv f₁ _ (by decide) _ (by omega)] at b₂
    exact b₂

end VG.Proof.Rsa.AArch64.Rd
