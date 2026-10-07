import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail

/-!
# `vg_rsa_crt_values` on AArch64: an invalid modulus

`zeroOut` writes zeros to an output (`zeroOut_ok`); `fail` to all three,
and returns 0 (`cvFail_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `zeroOut sPtr sLen`: `len` zeros at `op`. -/
theorem zeroOut_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    {sPtr sLen len : Nat} {op : Addr} (hP : sPtr < 32) (hL : sLen < 32)
    (hO : word s.mem B (8 * sPtr) = op) (hK : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hk1 : 1 ≤ len) (hk' : len < 2 ^ 31) (o : OutOk s B Z op len) :
    WP isa (zeroOut sPtr sLen) s fun t =>
      (∀ i < len, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep [.x1, .x2, .x3] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 len ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [h0, hdr_enc hP, hdr_enc hL, hl sPtr hP, hl sLen hL, hO, hK]) rfl rfl rfl)
    fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := len) (by omega) (by omega) (BInv s₁ op)
    (fun j hj t hI _ => bStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact o.wr i hi) hj hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t hI => ?_
  exact ⟨hI.bytes, fun x hx => by rw [hI.frame x hx, hm₁], (k₁.trans hI.keep).mono (by decide)⟩

/-- `fail`: zeros to `qInv`, `dP` and `dQ`, and 0 returned. -/
theorem cvFail_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    {k pl ql dl : Nat} {pDp pDq pQi pN pP pQ pD : Addr}
    (ha : CvArgs s.mem B k pl ql dl pDp pDq pQi pN pP pQ pD)
    (hpl1 : 1 ≤ pl) (hpl2 : pl < 2 ^ 31) (hql1 : 1 ≤ ql) (hql2 : ql < 2 ^ 31)
    (oQi : OutOk s B Z pQi pl) (oDp : OutOk s B Z pDp pl) (oDq : OutOk s B Z pDq ql)
    (a1 : Apart pQi pl pDp pl) (a2 : Apart pQi pl pDq ql) (a3 : Apart pDp pl pDq ql) :
    WP isa fail s fun t =>
      (∀ i < pl, t.mem (pQi + BitVec.ofNat 64 i) = 0) ∧ (∀ i < pl, t.mem (pDp + BitVec.ofNat 64 i) = 0) ∧
      (∀ i < ql, t.mem (pDq + BitVec.ofNat 64 i) = 0) ∧ t.gpr .x0 = 0 ∧
      (∀ x, (∀ i < pl, x ≠ pQi + BitVec.ofNat 64 i) → (∀ i < pl, x ≠ pDp + BitVec.ofNat 64 i) →
        (∀ i < ql, x ≠ pDq + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep (.x0 :: mmRegs) s t := by
  have hn := hs.nowrap
  -- Words of the header, after stores outside the working space.
  have fw : ∀ {m m' : Mem} {op : Addr} {len : Nat}, (∀ j < len, Z ≤ ofs B (op + BitVec.ofNat 64 j)) →
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) → ∀ i < 32, word m' B (8 * i) = word m B (8 * i) :=
    fun hsep hx i hi => (frm_scr hsep hx).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  unfold fail
  simp only [seqs]
  refine WP.seq (WP.mono (zeroOut_ok hs h0 hZ (by decide) (by decide) ha.dp ha.pl hpl1 hpl2 oDp)
    fun s₁ ⟨z₁, x₁, k₁⟩ => ?_)
  have w₁ := fw oDp.sep x₁
  have hs₁ := hs.congr k₁.wr
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  refine WP.seq (WP.mono (zeroOut_ok hs₁ h0₁ hZ (by decide) (by decide) (by rw [w₁ _ (by decide)]; exact ha.dq)
    (by rw [w₁ _ (by decide)]; exact ha.ql) hql1 hql2 ⟨fun i hi => by rw [k₁.wr]; exact oDq.wr i hi, oDq.sep⟩)
    fun s₂ ⟨z₂, x₂, k₂⟩ => ?_)
  have w₂ := fw oDq.sep x₂
  have hs₂ := hs₁.congr k₂.wr
  have h0₂ : s₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans h0₁
  refine WP.seq (WP.mono (zeroOut_ok hs₂ h0₂ hZ (by decide) (by decide)
    (by rw [w₂ _ (by decide), w₁ _ (by decide)]; exact ha.qi) (by rw [w₂ _ (by decide), w₁ _ (by decide)]; exact ha.pl)
    hpl1 hpl2 ⟨fun i hi => by rw [k₂.wr, k₁.wr]; exact oQi.wr i hi, oQi.sep⟩) fun s₃ ⟨z₃, x₃, k₃⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s₃.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₄⟩ => ?_
  have kk := ((k₁.trans k₂).trans k₃).trans k₄
  rw [hm]
  refine ⟨z₃, fun i hi => ?_, fun i hi => ?_, hx, fun x n1 n2 n3 => by rw [x₃ x n1, x₂ x n3, x₁ x n2],
    kk.mono (by decide)⟩
  · rw [x₃ _ (fun j hj => (a1 j hj i hi).symm), x₂ _ (fun j hj => a3 i hi j hj)]
    exact z₁ i hi
  · rw [x₃ _ (fun j hj => (a2 j hj i hi).symm)]
    exact z₂ i hi

end VG.Proof.Rsa.AArch64
