import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

/-- Only odd entries of the existing first generator row are read by width-seven NAF. -/
structure JointGenerator (c : Joint.Cfg) (C : Curve) (base : Addr) (size : Nat)
    (G : Point C) (T : Addr) (s : State) : Prop where
  symbol : s.syms c.tsym=T
  read : ∀ a,1≤a → a≤32 → ∀ i<8,InRegions (s.rd++s.wr)
    (T+BitVec.ofNat 64 (128*(a-1))+BitVec.ofNat 64 (8*i)) 8
  outside : ∀ a,1≤a → a≤32 → ∀ i<8,∀ b<8,size≤ofs base
    (T+BitVec.ofNat 64 (128*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)
  bounds : ∀ a,1≤a → a≤32 →
    wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 0 4<C.p ∧
    wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 32 4<C.p
  point : ∀ a,1≤a → a≤32 →InvJ C
    (toM C.p (2^256) (wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 0 4))
    (toM C.p (2^256) (wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 32 4)) 1 (mul (2*a-1) G)

theorem JointGenerator.keep {c : Joint.Cfg} {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {s t : State} {W : List Nat} (h : JointGenerator c C base size G T s)
    (hk : ProgKeep c.K.M base W s t) (hsym : t.syms=s.syms)
    (hw : ∀ w∈W,w+8*c.K.M.n≤size) (htmp : c.K.M.tmp+8*c.K.M.n≤size) :
    JointGenerator c C base size G T t := by
  have wordeq (a i : Nat) (ha : 1≤a) (ha32 : a≤32) (hi : i<8) :
      word t.mem (T+BitVec.ofNat 64 (128*(a-1))) (8*i)=
      word s.mem (T+BitVec.ofNat 64 (128*(a-1))) (8*i) := by
    apply Mem.readW_congr
    intro b hb
    have ho := h.outside a ha ha32 i hi b (by omega)
    apply hk.mem
    · intro w hm; have := hw w hm; dsimp only [off]; exact Or.inr (by omega)
    · dsimp only [off]; exact Or.inr (by omega)
  have val (a o : Nat) (ha : 1≤a) (ha32 : a≤32) (ho : o=0 ∨ o=32) :
      wordsVal t.mem (T+BitVec.ofNat 64 (128*(a-1))) o 4=
      wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) o 4 := by
    apply wordsVal_of_words₂
    intro i hi
    rcases ho with rfl | rfl
    · simpa only [Nat.zero_add] using wordeq a i ha ha32 (by omega)
    · have e := wordeq a (4+i) ha ha32 (by omega)
      simpa only [Nat.mul_add] using e
  refine ⟨?_,?_,h.outside,?_,?_⟩
  · rw [hsym]; exact h.symbol
  · intro a ha ha32 i hi; rw [hk.rd,hk.wr]; exact h.read a ha ha32 i hi
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 32 ha ha32 (by simp)]
    exact h.bounds a ha ha32
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 32 ha ha32 (by simp)]
    exact h.point a ha ha32

end VG.Proof.Weierstrass.AArch64
