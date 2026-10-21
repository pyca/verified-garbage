module

public import VerifiedGarbage.Proof.Mont.Arm.Words
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombSetup
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLoop
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombTail
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Mont.Words32At
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The complete public-row scan selects an affine point, or infinity for zero. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem selectRow_ok (K : TCombCfg) {s : State} {base X : Addr} {size a j : Nat}
    (hs : Scr s base size) (hq : K.Q.x+24*K.L.M.n≤size)
    (hzle : K.zero+8*K.L.M.n≤size)
    (hza : K.zero+8*K.L.M.n≤K.Q.x ∨ K.Q.x+24*K.L.M.n≤K.zero)
    (hone : K.one<2^(64*K.L.M.n)) (hz : wordsVal s.mem base K.zero K.L.M.n=0)
    (hn : 1≤K.L.M.n) (hH : K.H+1<2^31) (ha : a≤K.H)
    (ga : s.gpr .r9=BitVec.ofNat 32 a) (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hX : State.addr (s.syms K.tsym+BitVec.ofNat 32 (16*K.L.M.n*K.H*j))=X)
    (fit : X.toNat+16*K.L.M.n*K.H≤2^32)
    (hr : InRegions (s.rd ++ s.wr) X (16*K.L.M.n*K.H))
    (hd : Region.Disjoint ⟨X,16*K.L.M.n*K.H⟩ ⟨base,size⟩)
    (er : encodable (BitVec.ofNat 32 (16*K.L.M.n*K.H))=true)
    (es : encodable (BitVec.ofNat 32 (16*K.L.M.n))=true)
    (eh : encodable (BitVec.ofNat 32 (K.H+1))=true) :
    WP isa K.select s fun t =>
      wordsVal t.mem base K.Q.x K.L.M.n=
        (if a=0 then 0 else wordsVal s.mem X (16*K.L.M.n*(a-1)) K.L.M.n) ∧
      wordsVal t.mem base K.Q.y K.L.M.n=
        (if a=0 then K.one else wordsVal s.mem X (16*K.L.M.n*(a-1)+8*K.L.M.n) K.L.M.n) ∧
      wordsVal t.mem base K.Q.z K.L.M.n=(if a=0 then 0 else K.one) ∧
      Rest [.r4,.r5,.r7,.r8,.r10] s t ∧ Outside base K.Q.x (24*K.L.M.n) s.mem t.mem := by
  have hy : K.Q.y=K.Q.x+8*K.L.M.n := rfl
  have small := hs.small
  have hHp : 1≤K.H := Nat.two_pow_pos _
  have span : 16*K.L.M.n*(a-1)+16*K.L.M.n≤16*K.L.M.n*K.H := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  unfold TCombCfg.select
  rw [WP.seq_iff]
  refine WP.mono (selectSetup_ok K hs (by omega) gj er) fun s₁ ⟨p₁,g₁,z₁,k₁,O₁⟩ => ?_
  have hs₁ := hs.of_rest k₁ (by decide)
  have hx₁ : State.addr (s₁.gpr .r8)=X := by rw [p₁]; exact hX
  have hr₁ : InRegions (s₁.rd ++ s₁.wr) X (16*K.L.M.n*K.H) := by rw [k₁.rd,k₁.wr]; exact hr
  have ga₁ : s₁.gpr .r9=BitVec.ofNat 32 a := by rw [k₁.gpr .r9 (by decide),ga]
  rw [WP.seq_iff]
  refine WP.mono (scan_loop_ok K hs₁ hx₁ (by omega) (by have := hs.small; omega)
    fit hr₁ hd hn hH ha ga₁ es eh g₁ z₁) fun s₂ I => ?_
  have keep₂ : Rest [.r4,.r5,.r7,.r8,.r10] s s₂ := (k₁.mono (by simp)).trans I.keep
  have hs₂ := hs.of_rest keep₂ (by decide)
  have source : ∀ i<4*K.L.M.n,
      w32 s₁.mem X (16*K.L.M.n*(a-1)+4*i)=w32 s.mem X (16*K.L.M.n*(a-1)+4*i) := by
    intro i hi
    apply congrArg BitVec.toNat
    exact (outside_frame (size := size) O₁ (by omega)).readW
      (r := ⟨X,16*K.L.M.n*K.H⟩)
      (Offset.contains_base (d := 16*K.L.M.n*(a-1)+4*i) (n := 4) X (by omega) (by omega))
      (fun r hr' => by rcases List.mem_singleton.mp hr' with rfl; exact hd) (by decide)
  have raw : ∀ i<4*K.L.M.n,w32 s₂.mem base (K.Q.x+4*i)=
      if a=0 then 0 else w32 s.mem X (16*K.L.M.n*(a-1)+4*i) := by
    intro i hi
    rw [I.val i hi,source i hi]
    by_cases zero : a=0
    · have no : ¬(1≤a ∧ a<K.H+1) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false no)]
      simp only [zero,↓reduceIte]
    · have one : 1≤a := by omega
      have last : a<K.H+1 := by omega
      simp only [zero,one,last,and_self,↓reduceIte]
  have x₂ : wordsVal s₂.mem base K.Q.x K.L.M.n=
      if a=0 then 0 else wordsVal s.mem X (16*K.L.M.n*(a-1)) K.L.M.n := by
    simp only [wordsVal_eq_val32]
    by_cases zero : a=0
    · simp only [zero,↓reduceIte]
      exact val32_of_shifts _ _ _ _ 0 (Nat.two_pow_pos _) fun i hi => by
        rw [raw i (by omega)]
        simp only [zero,↓reduceIte,Nat.zero_shiftRight,Nat.zero_mod]
    · simp only [zero,↓reduceIte]
      exact val32_congr_at fun i hi => by rw [raw i (by omega)]; simp only [zero,↓reduceIte]
  have y₂ : wordsVal s₂.mem base K.Q.y K.L.M.n=
      if a=0 then 0 else wordsVal s.mem X (16*K.L.M.n*(a-1)+8*K.L.M.n) K.L.M.n := by
    simp only [wordsVal_eq_val32]
    have word : ∀ i<2*K.L.M.n,w32 s₂.mem base (K.Q.y+4*i)=
        if a=0 then 0 else w32 s.mem X (16*K.L.M.n*(a-1)+8*K.L.M.n+4*i) := by
      intro i hi
      have e := raw (2*K.L.M.n+i) (by omega)
      rw [show K.Q.x+4*(2*K.L.M.n+i)=K.Q.y+4*i by rw [hy]; omega,
        show 16*K.L.M.n*(a-1)+4*(2*K.L.M.n+i)=16*K.L.M.n*(a-1)+8*K.L.M.n+4*i by omega] at e
      exact e
    by_cases zero : a=0
    · simp only [zero,↓reduceIte]
      exact val32_of_shifts _ _ _ _ 0 (Nat.two_pow_pos _) fun i hi => by
        rw [word i hi]
        simp only [zero,↓reduceIte,Nat.zero_shiftRight,Nat.zero_mod]
    · simp only [zero,↓reduceIte]
      exact val32_congr_at fun i hi => by rw [word i hi]; simp only [zero,↓reduceIte]
  have zero₂ : wordsVal s₂.mem base K.zero K.L.M.n=0 := by
    rw [I.unch.wordsVal (by omega) (by omega),O₁.wordsVal (by omega) (by omega),hz]
  refine WP.mono (selectTail_ok K (a := a) hs₂ hq hzle hza hone (by omega)
    (by rw [keep₂.gpr .r9 (by decide),ga]) zero₂) fun s₃ ⟨x₃,y₃,z₃,k₃,O₃⟩ => ?_
  refine ⟨by rw [x₃,x₂],?_,z₃,keep₂.trans (k₃.mono (by simp)),?_⟩
  · rw [y₃,y₂]
    by_cases zero : a=0 <;> simp only [zero,↓reduceIte]
  · exact ((O₁.mono (Nat.le_refl _) (by omega)).trans
      (I.unch.mono (Nat.le_refl _) (by omega))).trans O₃

end VG.Proof.Weierstrass.Arm.TComb
