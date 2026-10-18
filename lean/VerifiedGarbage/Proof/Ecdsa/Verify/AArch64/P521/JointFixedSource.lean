module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedPoint
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
/-- Only odd entries of the existing first generator row are read by width-seven NAF. -/
structure FixedGenerator (C : Curve) (base : Addr) (size : Nat)
    (G : Point C) (T : Addr) (s : State) : Prop where
  symbol : s.syms "VG_P521_COMB"=T
  read : ∀ a,1≤a → a≤32 → ∀ i<18,InRegions (s.rd++s.wr)
    (T+BitVec.ofNat 64 (288*(a-1))+BitVec.ofNat 64 (8*i)) 8
  outside : ∀ a,1≤a → a≤32 → ∀ i<18,∀ b<8,size≤ofs base
    (T+BitVec.ofNat 64 (288*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)
  bounds : ∀ a,1≤a → a≤32 →
    wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 0 9<C.p ∧
    wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 72 9<C.p
  point : ∀ a,1≤a → a≤32 →InvJ C
    (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*9)) (wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 0 9))
    (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*9)) (wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 72 9)) 1 (mul (2*a-1) G)

theorem FixedGenerator.keep {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {s t : State} {W : List Nat} (h : FixedGenerator C base size G T s)
    (hk : ProgKeep P521Joint.K.M base W s t) (hsym : t.syms=s.syms)
    (hw : ∀ w∈W,w+8*P521Joint.K.M.n≤size) (htmp : P521Joint.K.M.tmp+8*P521Joint.K.M.n≤size) :
    FixedGenerator C base size G T t := by
  have wordeq (a i : Nat) (ha : 1≤a) (ha32 : a≤32) (hi : i<18) :
      word t.mem (T+BitVec.ofNat 64 (288*(a-1))) (8*i)=
      word s.mem (T+BitVec.ofNat 64 (288*(a-1))) (8*i) := by
    apply Mem.readW_congr
    intro b hb
    have ho := h.outside a ha ha32 i hi b (by omega)
    apply hk.mem
    · intro w hm; have := hw w hm; dsimp only [off]; exact Or.inr (by omega)
    · dsimp only [off]; exact Or.inr (by omega)
  have val (a o : Nat) (ha : 1≤a) (ha32 : a≤32) (ho : o=0 ∨ o=72) :
      wordsVal t.mem (T+BitVec.ofNat 64 (288*(a-1))) o 9=
      wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) o 9 := by
    apply wordsVal_of_words₂
    intro i hi
    rcases ho with rfl | rfl
    · simpa only [Nat.zero_add] using wordeq a i ha ha32 (by omega)
    · have e := wordeq a (9+i) ha ha32 (by omega)
      simpa only [Nat.mul_add] using e
  refine ⟨?_,?_,h.outside,?_,?_⟩
  · rw [hsym]; exact h.symbol
  · intro a ha ha32 i hi; rw [hk.rd,hk.wr]; exact h.read a ha ha32 i hi
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 72 ha ha32 (by simp)]
    exact h.bounds a ha ha32
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 72 ha ha32 (by simp)]
    exact h.point a ha ha32

theorem FixedGenerator.unch {C : Curve} {base T : Addr} {size : Nat}
 {G : Point C} {s t : State} {W : List (Nat×Nat)}
 (h : FixedGenerator C base size G T s)
 (hu : Unch base W s.mem t.mem) (hw : ∀w∈W,w.1+w.2≤size)
 (hr : t.rd=s.rd) (hwr : t.wr=s.wr) (hsy : t.syms=s.syms) :
 FixedGenerator C base size G T t := by
 have wordeq (a i : Nat) (ha : 1≤a) (ha32 : a≤32) (hi : i<18) :
   word t.mem (T+BitVec.ofNat 64 (288*(a-1))) (8*i)=
   word s.mem (T+BitVec.ofNat 64 (288*(a-1))) (8*i) := by
   apply Mem.readW_congr
   intro b hb
   apply hu
   intro w hm
   have ho := h.outside a ha ha32 i hi b (by omega)
   have := hw w hm
   exact Or.inr (by dsimp only [off]; omega)
 have val (a o : Nat) (ha : 1≤a) (ha32 : a≤32) (ho : o=0 ∨ o=72) :
   wordsVal t.mem (T+BitVec.ofNat 64 (288*(a-1))) o 9=
   wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) o 9 := by
   apply wordsVal_of_words₂
   intro i hi
   rcases ho with rfl | rfl
   · simpa only [Nat.zero_add] using wordeq a i ha ha32 (by omega)
   · simpa only [Nat.mul_add] using wordeq a (9+i) ha ha32 (by omega)
 refine ⟨hsy ▸ h.symbol,?_,h.outside,?_,?_⟩
 · intro a ha ha32 i hi; rw [hr,hwr]; exact h.read a ha ha32 i hi
 · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 72 ha ha32 (by simp)]
   exact h.bounds a ha ha32
 · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 72 ha ha32 (by simp)]
   exact h.point a ha ha32

end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
