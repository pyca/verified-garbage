import VerifiedGarbage.Proof.Rsa.X86_64.RpFin

/-!
# `vg_rsa_recover_primes` on x86-64: the outputs

`p` and `q`, masked, to their outputs and the mask's low bit returned
(`rpStores_ok`); zeros and 0 if no candidate was tried (`rpFail_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stores of `p` (`fV`) and `q` (`fQ`), and the exit. -/
theorem rpStores_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {k el dl : Nat}
    {pP pQ pN pE pD : Addr} {sv : Nat → BitVec 64} (ha : RpArgs s.mem B k el dl pP pQ pN pE pD sv) {c : Bool}
    (hm : word s.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = mask c) (hk1 : 1 ≤ k) (hk2 : k ≤ 8 * w)
    (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : Apart pP k pQ k) :
    WP isa (seqs (storeA fV sP Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
      (storeA fQ sQ Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
        ([.block retMask] : List (Prog isa))))) s fun t =>
      (List.range k).map (fun i => t.mem (pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w fV) ((k + 7) / 8) else 0) k ∧
      (List.range k).map (fun i => t.mem (pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w fQ) ((k + 7) / 8) else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = sv i) ∧
      (∀ x, (∀ i < k, x ≠ pP + BitVec.ofNat 64 i) → (∀ i < k, x ≠ pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep mmRegs s t := by
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
  have hm₁ : word s₁.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = mask c := by rw [fw f₁ _ (by decide)]; exact hm
  refine wp_seqs_append (by simp [storeA]) (by simp) (WP.mono (storeA_ws h₁ (by decide) (by decide)
    (by decide) (by rw [fw f₁ _ (by decide)]; exact ha.q) (by rw [fw f₁ _ (by decide)]; exact ha.k) hm₁ hk1 hk2
    (fun i hi => by rw [k₁.2.2]; exact oQ.wr i hi) oQ.sep) fun s₂ ⟨b₂, x₂, h₂, f₂, k₂⟩ => ?_)
  have hm₂ : word s₂.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = mask c := by rw [fw f₂ _ (by decide)]; exact hm₁
  simp only [seqs]
  refine WP.mono (cvExit_ok h₂ hm₂) fun t ⟨hax, hsv, hmt, k₃⟩ => ?_
  rw [hmt]
  refine ⟨?_, ?_, hax, fun i hi => ?_, fun x n1 n2 => by rw [x₂ x n2, x₁ x n1],
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [← b₁]
    exact List.map_congr_left fun i hi => by
      have hi' := List.mem_range.mp hi
      rw [x₂ _ (fun j hj => a i hi' j hj)]
  · rw [fv f₁ _ (by decide) _ (by omega)] at b₂
    exact b₂
  · rw [hsv i hi, fw f₂ _ (by omega), fw f₁ _ (by omega)]
    exact ha.saved i hi

/-- `fail`: zeros to `p` and `q`, 0 returned, and the saved registers
restored. -/
theorem rpFail_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {k el dl : Nat} {pP pQ pN pE pD : Addr} {sv : Nat → BitVec 64}
    (ha : RpArgs s.mem B k el dl pP pQ pN pE pD sv) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 31)
    (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : Apart pP k pQ k) :
    WP isa fail s fun t =>
      (∀ i < k, t.mem (pP + BitVec.ofNat 64 i) = 0) ∧ (∀ i < k, t.mem (pQ + BitVec.ofNat 64 i) = 0) ∧
      t.gpr .rax = 0 ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = sv i) ∧
      (∀ x, (∀ i < k, x ≠ pP + BitVec.ofNat 64 i) → (∀ i < k, x ≠ pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have hn := hs.nowrap
  have fw : ∀ {m m' : Mem} {op : Addr} {len : Nat}, (∀ j < len, Z ≤ ofs B (op + BitVec.ofNat 64 j)) →
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) → ∀ i < 32, word m' B (8 * i) = word m B (8 * i) :=
    fun hsep hx i hi => (frm_scr hsep hx).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  unfold fail
  simp only [seqs]
  refine WP.seq (WP.mono (zeroOut_ok hs hdi hZ (by decide) (by decide) ha.p ha.k hk1 hk2 oP)
    fun s₁ ⟨z₁, x₁, k₁⟩ => ?_)
  have w₁ := fw oP.sep x₁
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  refine WP.seq (WP.mono (zeroOut_ok hs₁ hdi₁ hZ (by decide) (by decide) (by rw [w₁ _ (by decide)]; exact ha.q)
    (by rw [w₁ _ (by decide)]; exact ha.k) hk1 hk2 ⟨fun i hi => by rw [k₁.2.2]; exact oQ.wr i hi, oQ.sep⟩)
    fun s₂ ⟨z₂, x₂, k₂⟩ => ?_)
  have w₂ := fw oQ.sep x₂
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  have hw : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [w₂ i hi, w₁ i hi]
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = 0 ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = s₂.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide),
      hl₂ 3 (by decide), hl₂ 4 (by decide), hl₂ 5 (by decide), hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ?_
  have kk := (k₁.trans k₂).trans k₃
  rw [hm]
  refine ⟨fun i hi => ?_, z₂, hax, fun i hi => ?_, fun x n1 n2 => by rw [x₂ x n2, x₁ x n1],
    kk.gpr (by decide)⟩
  · rw [x₂ _ (fun j hj => a i hi j hj)]
    exact z₁ i hi
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0.trans (ha.saved 0 (by decide))
    · exact h1.trans (ha.saved 1 (by decide))
    · exact h2.trans (ha.saved 2 (by decide))
    · exact h3.trans (ha.saved 3 (by decide))
    · exact h4.trans (ha.saved 4 (by decide))
    · exact h5.trans (ha.saved 5 (by decide))

end VG.Proof.Rsa.X86_64
