import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.SelectScan

/-! Selected coordinates and cached powers, with the canonical infinity Y for a zero digit. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

theorem select_words_ok (K : WinCfg) {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (hn : K.M.n=4) (ht : K.tbl<2^31) (hT : K.tbl+2560≤size)
    (hE : K.E.x+160≤size) (hy : K.E.y=K.E.x+32) (hone : K.one<2^256)
    (ha : a≤16) (h8 : s.gpr .r8=BitVec.ofNat 64 a) :
    WP isa (.block (Impl.Ecdh.X86_64.Window5.select K)) s fun t =>
      (∀ i<5,wordsVal t.mem base (K.E.x+32*i) K.M.n=
        if 1≤a then wordsVal s.mem base (K.tbl+160*(a-1)+32*i) K.M.n
        else if i=1 then K.one else 0) ∧
      Outside base K.E.x 160 s.mem t.mem ∧ KeepRegs [.rax,.rcx,.rdx] s t := by
  rw [Impl.Ecdh.X86_64.Window5.select,WP.block_append_iff]
  refine WP.mono (select_scan_ok K hs ht hT hE ha h8) fun u ⟨vu,ou,ku⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have h8u : u.gpr .r8=BitVec.ofNat 64 a := (ku.gpr _ (by decide)).trans h8
  refine WP.mono (ySel0_ok K hu (by omega) h8u (by rw [hn,hy]; omega)) fun t ⟨yt,kt,ot⟩ => ?_
  have vw : ∀ i<5,∀ j<4,word u.mem base (K.E.x+32*i+8*j)=
      if 1≤a then word s.mem base (K.tbl+160*(a-1)+32*i+8*j) else 0 := by
    intro i hi j hj
    have hh := vu (4*i+j) (by omega)
    rwa [show K.E.x+8*(4*i+j)=K.E.x+32*i+8*j by omega,
      show K.tbl+160*(a-1)+8*(4*i+j)=K.tbl+160*(a-1)+32*i+8*j by omega] at hh
  refine ⟨?_,ou.trans (ot.mono (by omega) (by rw [hn,hy]; omega)),ku.trans (kt.mono (by decide))⟩
  intro i hi
  rw [hn]
  by_cases he : i=1
  · subst i
    have yw : ∀ j<4,word t.mem base (K.E.x+32+8*j)=
        (wordOf K.one j &&& bmask (decide (a=0))) ||| word u.mem base (K.E.x+32+8*j) := by
      intro j hj
      simpa only [hy] using yt j (by rw [hn]; exact hj)
    simp only [ite_true,Nat.mul_one]
    by_cases h1 : 1≤a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_congr₂ _ _ _ fun j hj => by
        rw [yw j hj,vw 1 (by decide) j hj,ite_eq_left_of_eq_true _ _ (eq_true h1),
          decide_eq_false (show a≠0 by omega),bv_and_or_false]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_wordOf hone fun j hj => by
        rw [yw j hj,vw 1 (by decide) j hj,ite_eq_right_of_eq_false _ _ (eq_false h1),
          decide_eq_true (show a=0 by omega),bv_and_or_true,bv_or_zero]
  · have uw : ∀ j<4,word t.mem base (K.E.x+32*i+8*j)=word u.mem base (K.E.x+32*i+8*j) := by
      intro j hj
      apply ot.word
      · rw [hn,hy]; omega
      · have := hs.nowrap; omega
    simp only [he,ite_false]
    by_cases h1 : 1≤a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_congr₂ _ _ _ fun j hj => by
        rw [uw j hj,vw i hi j hj,ite_eq_left_of_eq_true _ _ (eq_true h1)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun j hj => by
        rw [uw j hj,vw i hi j hj,ite_eq_right_of_eq_false _ _ (eq_false h1)]

end VG.Proof.Ecdh.X86_64.Secret
