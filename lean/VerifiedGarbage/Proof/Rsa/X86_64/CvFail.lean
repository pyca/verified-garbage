import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail

/-!
# `vg_rsa_crt_values` on x86-64: an invalid modulus

`zeroOut` writes zeros to an output (`zeroOut_ok`); `fail` to all three,
returns 0 and restores the saved registers (`cvFail_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

/-- `zeroOut sPtr sLen`: `len` zeros at `op`. -/
theorem zeroOut_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {sPtr sLen len : Nat} {op : Addr} (hP : sPtr < 32) (hL : sLen < 32)
    (hO : word s.mem B (8 * sPtr) = op) (hK : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hk1 : 1 ≤ len) (hk' : len < 2 ^ 31) (o : OutOk s B Z op len) :
    WP isa (zeroOut sPtr sLen) s fun t =>
      (∀ i < len, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep [.rsi, .rcx, .rax] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sPtr hP, hl sLen hL, hO, hK]) rfl) fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := len) (by omega) (FailInv s₁ op len) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t hI => ?_
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact o.wr j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (len - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = len))) (by
      xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ len - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show len - j - 1 < 2 ^ 64 by omega)]
      exact ⟨by rw [show len - j - 1 = len - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩) rfl)
      fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
    · intro i hi
      rw [hm, writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact hI.bytes i (by omega)
    · intro x hx
      rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact hI.frame x fun i hi => hx i (by omega)
  exact ⟨hI.bytes, fun x hx => by rw [hI.frame x hx, hm₁], (k₁.trans hI.keep).mono (by decide)⟩

/-- `fail`: zeros to `qInv`, `dP` and `dQ`, 0 returned, and the saved
registers restored. -/
theorem cvFail_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {k pl ql dl : Nat} {pDp pDq pQi pN pP pQ pD : Addr} {sv : Nat → BitVec 64}
    (ha : CvArgs s.mem B k pl ql dl pDp pDq pQi pN pP pQ pD sv)
    (hpl1 : 1 ≤ pl) (hpl2 : pl < 2 ^ 31) (hql1 : 1 ≤ ql) (hql2 : ql < 2 ^ 31)
    (oQi : OutOk s B Z pQi pl) (oDp : OutOk s B Z pDp pl) (oDq : OutOk s B Z pDq ql)
    (a1 : Apart pQi pl pDp pl) (a2 : Apart pQi pl pDq ql) (a3 : Apart pDp pl pDq ql) :
    WP isa fail s fun t =>
      (∀ i < pl, t.mem (pQi + BitVec.ofNat 64 i) = 0) ∧ (∀ i < pl, t.mem (pDp + BitVec.ofNat 64 i) = 0) ∧
      (∀ i < ql, t.mem (pDq + BitVec.ofNat 64 i) = 0) ∧
      t.gpr .rax = 0 ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = sv i) ∧
      (∀ x, (∀ i < pl, x ≠ pQi + BitVec.ofNat 64 i) → (∀ i < pl, x ≠ pDp + BitVec.ofNat 64 i) →
        (∀ i < ql, x ≠ pDq + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have hn := hs.nowrap
  -- Words of the header, after stores outside the working space.
  have fw : ∀ {m m' : Mem} {op : Addr} {len : Nat}, (∀ j < len, Z ≤ ofs B (op + BitVec.ofNat 64 j)) →
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) → ∀ i < 32, word m' B (8 * i) = word m B (8 * i) :=
    fun hsep hx i hi => (frm_scr hsep hx).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  unfold fail
  simp only [seqs]
  refine WP.seq (WP.mono (zeroOut_ok hs hdi hZ (by decide) (by decide) ha.dp ha.pl hpl1 hpl2 oDp)
    fun s₁ ⟨z₁, x₁, k₁⟩ => ?_)
  have w₁ := fw oDp.sep x₁
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  refine WP.seq (WP.mono (zeroOut_ok hs₁ hdi₁ hZ (by decide) (by decide) (by rw [w₁ _ (by decide)]; exact ha.dq)
    (by rw [w₁ _ (by decide)]; exact ha.ql) hql1 hql2 ⟨fun i hi => by rw [k₁.2.2]; exact oDq.wr i hi, oDq.sep⟩)
    fun s₂ ⟨z₂, x₂, k₂⟩ => ?_)
  have w₂ := fw oDq.sep x₂
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.seq (WP.mono (zeroOut_ok hs₂ hdi₂ hZ (by decide) (by decide)
    (by rw [w₂ _ (by decide), w₁ _ (by decide)]; exact ha.qi) (by rw [w₂ _ (by decide), w₁ _ (by decide)]; exact ha.pl)
    hpl1 hpl2 ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact oQi.wr i hi, oQi.sep⟩) fun s₃ ⟨z₃, x₃, k₃⟩ => ?_)
  have w₃ := fw oQi.sep x₃
  have hs₃ := hs₂.congr k₃.2.2
  have hdi₃ : s₃.gpr .rdi = B := (k₃.gpr (by decide)).trans hdi₂
  have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi => hs₃.ld (by omega)
  have hw : ∀ i < 32, word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [w₃ i hi, w₂ i hi, w₁ i hi]
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = 0 ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = s₃.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₃, hdrOff, hl₃ 0 (by decide), hl₃ 1 (by decide), hl₃ 2 (by decide),
      hl₃ 3 (by decide), hl₃ 4 (by decide), hl₃ 5 (by decide), hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₄⟩ => ?_
  have kk := ((k₁.trans k₂).trans k₃).trans k₄
  rw [hm]
  refine ⟨z₃, fun i hi => ?_, fun i hi => ?_, hax, fun i hi => ?_, fun x n1 n2 n3 => by rw [x₃ x n1, x₂ x n3, x₁ x n2],
    kk.gpr (by decide)⟩
  · rw [x₃ _ (fun j hj => (a1 j hj i hi).symm), x₂ _ (fun j hj => a3 i hi j hj)]
    exact z₁ i hi
  · rw [x₃ _ (fun j hj => (a2 j hj i hi).symm)]
    exact z₂ i hi
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0.trans (ha.saved 0 (by decide))
    · exact h1.trans (ha.saved 1 (by decide))
    · exact h2.trans (ha.saved 2 (by decide))
    · exact h3.trans (ha.saved 3 (by decide))
    · exact h4.trans (ha.saved 4 (by decide))
    · exact h5.trans (ha.saved 5 (by decide))

end VG.Proof.Rsa.X86_64
