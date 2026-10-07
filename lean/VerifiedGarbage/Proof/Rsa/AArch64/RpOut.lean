import VerifiedGarbage.Proof.Rsa.AArch64.RpFin
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail

/-!
# `vg_rsa_recover_primes` on AArch64: the outputs

`p` and `q`, masked, to their outputs and the mask's low bit returned
(`rpStores_ok`); zeros and 0 if no candidate was tried (`rpFail_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The stores of `p` (`fV`) and `q` (`fQ`), and the exit. -/
theorem rpStores_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {k el dl : Nat}
    {pP pQ pN pE pD : Addr} (ha : RpArgs s.mem B k el dl pP pQ pN pE pD) {c : Bool}
    (hm : word s.mem B (8 * Public.sMask) = mask c) (hk1 : 1 ≤ k) (hk2 : k ≤ 8 * w)
    (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : Apart pP k pQ k) :
    WP isa (seqs (storeA fV sP Public.sK Public.sMask ++
      (storeA fQ sQ Public.sK Public.sMask ++ ([.block retMask] : List (Prog isa))))) s fun t =>
      (List.range k).map (fun i => t.mem (pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w fV) ((k + 7) / 8) else 0) k ∧
      (List.range k).map (fun i => t.mem (pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w fQ) ((k + 7) / 8) else 0) k ∧
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

/-- `fail`: zeros to `p` and `q`, and 0 returned. -/
theorem rpFail_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    {k el dl : Nat} {pP pQ pN pE pD : Addr} (ha : RpArgs s.mem B k el dl pP pQ pN pE pD) (hk1 : 1 ≤ k)
    (hk2 : k < 2 ^ 31) (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : Apart pP k pQ k) :
    WP isa fail s fun t =>
      (∀ i < k, t.mem (pP + BitVec.ofNat 64 i) = 0) ∧ (∀ i < k, t.mem (pQ + BitVec.ofNat 64 i) = 0) ∧
      t.gpr .x0 = 0 ∧
      (∀ x, (∀ i < k, x ≠ pP + BitVec.ofNat 64 i) → (∀ i < k, x ≠ pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep (.x0 :: mmRegs) s t := by
  have hn := hs.nowrap
  have fw : ∀ {m m' : Mem} {op : Addr} {len : Nat}, (∀ j < len, Z ≤ ofs B (op + BitVec.ofNat 64 j)) →
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) → ∀ i < 32, word m' B (8 * i) = word m B (8 * i) :=
    fun hsep hx i hi => (frm_scr hsep hx).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  unfold fail
  simp only [seqs]
  refine WP.seq (WP.mono (zeroOut_ok hs h0 hZ (by decide) (by decide) ha.p ha.k hk1 hk2 oP)
    fun s₁ ⟨z₁, x₁, k₁⟩ => ?_)
  have w₁ := fw oP.sep x₁
  have hs₁ := hs.congr k₁.wr
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  refine WP.seq (WP.mono (zeroOut_ok hs₁ h0₁ hZ (by decide) (by decide) (by rw [w₁ _ (by decide)]; exact ha.q)
    (by rw [w₁ _ (by decide)]; exact ha.k) hk1 hk2 ⟨fun i hi => by rw [k₁.wr]; exact oQ.wr i hi, oQ.sep⟩)
    fun s₂ ⟨z₂, x₂, k₂⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ?_
  have kk := (k₁.trans k₂).trans k₃
  rw [hm]
  refine ⟨fun i hi => ?_, z₂, hx, fun x n1 n2 => by rw [x₂ x n2, x₁ x n1], kk.mono (by decide)⟩
  rw [x₂ _ (fun j hj => a i hi j hj)]
  exact z₁ i hi

end VG.Proof.Rsa.AArch64
