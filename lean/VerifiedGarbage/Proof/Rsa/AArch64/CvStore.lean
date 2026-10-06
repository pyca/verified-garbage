import VerifiedGarbage.Proof.Rsa.AArch64.CvHead

/-!
# `vg_rsa_crt_values` on AArch64: the results

`dP`, `dQ` and `qInv`, masked, to their outputs (`storeA_ws`, which keeps
the working space), and the mask's low bit returned (`cvStores_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Memory below `Z`, after a store outside the working space. -/
theorem frm_scr {m m' : Mem} {B out : Addr} {Z len : Nat} (hsep : ∀ i < len, Z ≤ ofs B (out + BitVec.ofNat 64 i))
    (hx : ∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → m' x = m x) : Frm B [(Z, 2 ^ 64)] m m' :=
  fun x hx' => hx x fun i hi he => by
    have := hsep i hi
    rw [← he] at this
    have := hx' _ List.mem_cons_self
    have : ofs B x < 2 ^ 64 := (x - B).isLt
    omega

/-- `storeA`, which keeps the working space and the header. -/
theorem storeA_ws {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {out : Addr}
    {c : Bool} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem B (8 * sPtr) = out) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hm : word s.mem B (8 * Public.sMask) = mask c) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hout : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (out + BitVec.ofNat 64 i)) :
    WP isa (seqs (storeA j sPtr sLen Public.sMask)) s fun t =>
      (List.range len).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w j) ((len + 7) / 8) else 0) len ∧
      (∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Ws t B Z w ∧
      Frm B [(Z, 2 ^ 64)] s.mem t.mem ∧
      Keep [.x11, .x12, .x8, .x1, .x9, .x15, .x2, .x3, .x5, .x6] s t :=
  WP.mono (storeA_ok h hj hP hL (by decide) hp hl hm hl1 hlw hout hsep) fun t ⟨hb, hx, hwr, hrd, k⟩ =>
    have hf := frm_scr hsep hx
    ⟨hb, hx, h.congr hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by have := h.h256; omega)) k (by decide), hf, k⟩

theorem mask_and_one (c : Bool) : mask c &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 c.toNat := by
  cases c <;> rfl

/-- The mask's low bit returned. -/
theorem cvExit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Bool}
    (hm : word s.mem B (8 * Public.sMask) = mask c) :
    WP isa (.block retMask) s
      fun t => (t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧ t.mem = s.mem) ∧ Keep [.x0, .x3, .x4] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  refine WP.keep [.x0, .x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  brun [retMask, h.x0, hdr_enc (show Public.sMask < 32 by decide), hl Public.sMask (by decide), hm, mask_and_one]

/-- The output bytes `out + i`, `i < len`: writable, outside the working
space. -/
structure OutOk (s : State) (B : Addr) (Z : Nat) (out : Addr) (len : Nat) : Prop where
  wr : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1
  sep : ∀ i < len, Z ≤ ofs B (out + BitVec.ofNat 64 i)

/-- Two outputs with no byte in common. -/
def Apart (o₁ : Addr) (l₁ : Nat) (o₂ : Addr) (l₂ : Nat) : Prop :=
  ∀ i < l₁, ∀ j < l₂, o₁ + BitVec.ofNat 64 i ≠ o₂ + BitVec.ofNat 64 j

/-- The stores of `qInv` (`aX₂`), `dP` (`aX₁`) and `dQ` (`aV`), and the
exit. -/
theorem cvStores_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {k pl ql dl : Nat}
    {pDp pDq pQi pN pP pQ pD : Addr}
    (ha : CvArgs s.mem B k pl ql dl pDp pDq pQi pN pP pQ pD) {c : Bool}
    (hm : word s.mem B (8 * Public.sMask) = mask c)
    (hpl1 : 1 ≤ pl) (hpl2 : pl ≤ 8 * w) (hql1 : 1 ≤ ql) (hql2 : ql ≤ 8 * w)
    (oQi : OutOk s B Z pQi pl) (oDp : OutOk s B Z pDp pl) (oDq : OutOk s B Z pDq ql)
    (a1 : Apart pQi pl pDp pl) (a2 : Apart pQi pl pDq ql) (a3 : Apart pDp pl pDq ql) :
    WP isa (seqs (storeA aX₂ sQi sPl Public.sMask ++
      (storeA aX₁ sDp sPl Public.sMask ++ (storeA aV sDq sQl Public.sMask ++
        ([.block retMask] : List (Prog isa)))))) s
      fun t =>
        (List.range pl).map (fun i => t.mem (pQi + BitVec.ofNat 64 i)) =
          Spec.Rsa.i2osp (if c then wv s.mem B (slot w aX₂) ((pl + 7) / 8) else 0) pl ∧
        (List.range pl).map (fun i => t.mem (pDp + BitVec.ofNat 64 i)) =
          Spec.Rsa.i2osp (if c then wv s.mem B (slot w aX₁) ((pl + 7) / 8) else 0) pl ∧
        (List.range ql).map (fun i => t.mem (pDq + BitVec.ofNat 64 i)) =
          Spec.Rsa.i2osp (if c then wv s.mem B (slot w aV) ((ql + 7) / 8) else 0) ql ∧
        t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧
        (∀ x, (∀ i < pl, x ≠ pQi + BitVec.ofNat 64 i) → (∀ i < pl, x ≠ pDp + BitVec.ofNat 64 i) →
          (∀ i < ql, x ≠ pDq + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
        Keep (.x0 :: mmRegs) s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have sl : ∀ j < 16, slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  -- Header words and arrays below `Z` are kept by each store.
  have fw : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ i < 32, word m' B (8 * i) = word m B (8 * i) :=
    fun hf i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  have fv : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ j < 16, ∀ n ≤ w + 2,
      wv m' B (slot w j) n = wv m B (slot w j) n := fun hf j hj n hn' =>
    hf.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := sl j hj; exact Or.inl (by omega))
      (by have := sl j hj; omega)
  refine wp_seqs_append (by simp [storeA]) (by simp [storeA]) (WP.mono (storeA_ws h (by decide) (by decide)
    (by decide) ha.qi ha.pl hm hpl1 hpl2 oQi.wr oQi.sep) fun s₁ ⟨b₁, x₁, h₁, f₁, k₁⟩ => ?_)
  have hm₁ : word s₁.mem B (8 * Public.sMask) = mask c := by rw [fw f₁ _ (by decide)]; exact hm
  refine wp_seqs_append (by simp [storeA]) (by simp [storeA]) (WP.mono (storeA_ws h₁ (by decide) (by decide)
    (by decide) (by rw [fw f₁ _ (by decide)]; exact ha.dp) (by rw [fw f₁ _ (by decide)]; exact ha.pl) hm₁ hpl1 hpl2
    (fun i hi => by rw [k₁.wr]; exact oDp.wr i hi) oDp.sep) fun s₂ ⟨b₂, x₂, h₂, f₂, k₂⟩ => ?_)
  have hm₂ : word s₂.mem B (8 * Public.sMask) = mask c := by rw [fw f₂ _ (by decide)]; exact hm₁
  refine wp_seqs_append (by simp [storeA]) (by simp) (WP.mono (storeA_ws h₂ (by decide) (by decide)
    (by decide) (by rw [fw f₂ _ (by decide), fw f₁ _ (by decide)]; exact ha.dq)
    (by rw [fw f₂ _ (by decide), fw f₁ _ (by decide)]; exact ha.ql) hm₂ hql1 hql2
    (fun i hi => by rw [k₂.wr, k₁.wr]; exact oDq.wr i hi) oDq.sep) fun s₃ ⟨b₃, x₃, h₃, f₃, k₃⟩ => ?_)
  have hm₃ : word s₃.mem B (8 * Public.sMask) = mask c := by rw [fw f₃ _ (by decide)]; exact hm₂
  simp only [seqs]
  refine WP.mono (cvExit_ok h₃ hm₃) fun t ⟨⟨hax, hmt⟩, k₄⟩ => ?_
  rw [hmt]
  refine ⟨?_, ?_, ?_, hax, fun x n1 n2 n3 => by rw [x₃ x n3, x₂ x n2, x₁ x n1],
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · rw [← b₁]
    exact List.map_congr_left fun i hi => by
      have hi' := List.mem_range.mp hi
      rw [x₃ _ (fun j hj => a2 i hi' j hj), x₂ _ (fun j hj => a1 i hi' j hj)]
  · rw [fv f₁ _ (by decide) _ (by omega)] at b₂
    rw [← b₂]
    exact List.map_congr_left fun i hi => by
      have hi' := List.mem_range.mp hi
      rw [x₃ _ (fun j hj => a3 i hi' j hj)]
  · rw [fv f₂ _ (by decide) _ (by omega), fv f₁ _ (by decide) _ (by omega)] at b₃
    exact b₃

end VG.Proof.Rsa.AArch64
