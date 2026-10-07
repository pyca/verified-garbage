import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPrepTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointGenerator

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

theorem jointGenerator_unch {c : Joint.Cfg} {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {s t : State} {W : List (Nat×Nat)} (h : JointGenerator c C base size G T s)
    (hu : Unch base W s.mem t.mem) (hrd : t.rd=s.rd) (hwr : t.wr=s.wr)
    (hsym : t.syms=s.syms) (hw : ∀ w∈W,w.1+w.2≤size) :
    JointGenerator c C base size G T t := by
  have wordeq (a i : Nat) (ha : 1≤a) (ha32 : a≤32) (hi : i<8) :
      word t.mem (T+BitVec.ofNat 64 (128*(a-1))) (8*i)=
      word s.mem (T+BitVec.ofNat 64 (128*(a-1))) (8*i) := by
    apply Mem.readW_congr
    intro b hb
    have ho := h.outside a ha ha32 i hi b (by omega)
    apply hu
    intro w hm; have := hw w hm; dsimp only [off]; exact Or.inr (by omega)
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
  · intro a ha ha32 i hi; rw [hrd,hwr]; exact h.read a ha ha32 i hi
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 32 ha ha32 (by simp)]
    exact h.bounds a ha ha32
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 32 ha ha32 (by simp)]
    exact h.point a ha ha32


theorem JointTablePair.generators {base T : Addr} {P G : Point p256.C} {u v : Nat}
    {a b s t : State} (h : JointTablePair base P u v a b s t)
    (ga : Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size G T a)
    (gb : Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size G T b) :
    Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size G T s ∧
    Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size G T t := by
  obtain ⟨_,_,_,_,_,_,pa,pb,ta,tb⟩ := h
  have ga' := jointGenerator_unch ga pa.unch pa.keep.rd pa.keep.wr pa.syms (by decide +kernel)
  have gb' := jointGenerator_unch gb pb.unch pb.keep.rd pb.keep.wr pb.syms (by decide +kernel)
  exact ⟨jointGenerator_unch ga' ta.table.unch ta.table.keep.rd ta.table.keep.wr ta.syms (by decide +kernel),
    jointGenerator_unch gb' tb.table.unch tb.table.keep.rd tb.table.keep.wr tb.syms (by decide +kernel)⟩

end VG.Proof.Ecdsa.Verify.AArch64
