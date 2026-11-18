module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombTable
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Weierstrass.CombPointW
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
public import VerifiedGarbage.Impl.Weierstrass.Arm

/-! ### `Weierstrass.Arm.TCombBody`, which only this module used -/

section

/-! One public-index iteration of the signed comb table scan. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem ofNat32_eq {a b : Nat} (ha : a<2^32) (hb : b<2^32) :
    BitVec.ofNat 32 a = BitVec.ofNat 32 b ↔ a=b := by
  constructor
  · intro h
    have e := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using e
  · intro h; rw [h]

theorem sub_zero_iff (x y : BitVec 32) : x-y=0#32 ↔ x=y := by
  constructor
  · intro h
    have e := congrArg (fun z : BitVec 32 => z+y) h
    simpa only [BitVec.sub_add_cancel,BitVec.zero_add] using e
  · intro h; rw [h,BitVec.sub_self]

theorem selectBody_ok (K : TCombCfg) {s : State} {base X : Addr} {size a m : Nat}
    (hs : Scr s base size) (hX : State.addr (s.gpr .r8)=X)
    (ho : K.Q.x+16*K.L.M.n ≤ size) (hi : 16*K.L.M.n ≤ 4096)
    (fit : X.toNat+16*K.L.M.n ≤ 2^32)
    (hr : InRegions (s.rd ++ s.wr) X (16*K.L.M.n))
    (hd : Region.Disjoint ⟨X,16*K.L.M.n⟩ ⟨base,size⟩)
    (ha : a<2^31) (hm : m<2^31)
    (ga : s.gpr .r9=BitVec.ofNat 32 a) (gm : s.gpr .r7=BitVec.ofNat 32 m)
    (es : encodable (BitVec.ofNat 32 (16*K.L.M.n))=true)
    (eh : encodable (BitVec.ofNat 32 (K.H+1))=true)
    (mh : m+1<2^32) (hh : K.H+1<2^32) :
    WP isa (.block K.selectBody) s fun t =>
      (∀ i<4*K.L.M.n, w32 t.mem base (K.Q.x+4*i) =
        if a=m then w32 s.mem X (4*i) else w32 s.mem base (K.Q.x+4*i)) ∧
      Rest [.r4,.r5,.r7,.r8,.r10] s t ∧ Outside base K.Q.x (16*K.L.M.n) s.mem t.mem ∧
      t.gpr .r8=s.gpr .r8+BitVec.ofNat 32 (16*K.L.M.n) ∧
      t.gpr .r7=BitVec.ofNat 32 (m+1) ∧ t.z=decide (m+1=K.H+1) := by
  unfold TCombCfg.selectBody
  rw [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (eqMask_ok (op2_reg s .r7)) fun s₁ ⟨v₁,k₁,mem₁⟩ => ?_
  have cm₁ : s₁.gpr .r10=if decide (a=m) then BitVec.allOnes 32 else 0 := by
    rw [v₁,ga,gm,equality_mask (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a<2^32 by omega_using [ha])] using ha)
      (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show m<2^32 by omega_using [hm])] using hm)]
    simp only [ofNat32_eq (by omega_using [ha] : a<2^32) (by omega_using [hm] : m<2^32),decide_eq_true_eq]
  have hs₁ := hs.of_rest k₁ (by decide)
  have hx₁ : State.addr (s₁.gpr .r8)=X := by rw [k₁.gpr .r8 (by decide),hX]
  have hr₁ : InRegions (s₁.rd ++ s₁.wr) X (16*K.L.M.n) := by rw [k₁.rd,k₁.wr]; exact hr
  refine VG.Proof.X25519.Arm.WP.append
    (selectWords_ok K hs₁ hx₁ ho hi fit hr₁ hd (decide (a=m)) cm₁ (4*K.L.M.n) (Nat.le_refl _))
    fun s₂ ⟨v₂,k₂,O₂⟩ => ?_
  have k₁₂ : Rest [.r4,.r5,.r10] s s₂ := (k₁.mono (by simp)).trans (k₂.mono (by simp))
  refine wp_dp (op2_imm es) fun s₃ u₃ => wp_dp (op2_imm (by decide)) fun s₄ u₄ =>
    wp_cmp (op2_imm eh) fun s₅ f₅ z₅ => WP.block_nil ?_
  have k₃₅ : Rest [.r7,.r8] s₂ s₅ := (u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans (f₅.rest _))
  have mem₅ : s₅.mem=s₂.mem := by rw [f₅.mem,u₄.mem,u₃.mem]
  have g₇ : s₅.gpr .r7=BitVec.ofNat 32 (m+1) := by
    rw [f₅.gpr,u₄.gpr,dpVal,u₃.other .r7 (by decide),k₁₂.gpr .r7 (by decide),gm]
    exact (BitVec.ofNat_add _ _).symm
  refine ⟨?_, (k₁₂.mono (by simp)).trans (k₃₅.mono (by simp)),?_,?_,g₇,?_⟩
  · intro i hii
    rw [mem₅,v₂ i hii,mem₁]
    simp only [decide_eq_true_eq]
  · rw [mem₁] at O₂
    rw [mem₅]
    simpa only [show 4*(4*K.L.M.n)=16*K.L.M.n by omega_using []] using O₂
  · rw [f₅.gpr,u₄.other .r8 (by decide),u₃.gpr,dpVal,k₁₂.gpr .r8 (by decide)]
  · have g₇' : s₄.gpr .r7=BitVec.ofNat 32 (m+1) := by rw [← f₅.gpr,g₇]
    rw [z₅,g₇']
    have e : (BitVec.ofNat 32 (m+1)-BitVec.ofNat 32 (K.H+1)==0) = decide (m+1=K.H+1) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,decide_eq_true_eq]
      change BitVec.ofNat 32 (m+1)-BitVec.ofNat 32 (K.H+1)=0#32 ↔ m+1=K.H+1
      rw [sub_zero_iff,ofNat32_eq mh hh]
    exact e

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombTail`, which only this module used -/

section

/-! Complete the selected affine point, including the zero digit's infinity. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem selField_ok {s : State} {base : Addr} {size n o a b : Nat} (hs : Scr s base size)
    (c : Bool) (hc : s.gpr .r10=if c then BitVec.allOnes 32 else 0)
    (ho : o+8*n≤size) (ha : a+8*n≤size) (hb : b+8*n≤size)
    (hoa : o≤a ∨ a+8*n≤o) (hob : o≤b ∨ b+8*n≤o) :
    WP isa (.block (sel (2*n) o a b)) s fun t =>
      wordsVal t.mem base o n=(if c then wordsVal s.mem base b n else wordsVal s.mem base a n) ∧
      Rest [.r4,.r5] s t ∧ Outside base o (8*n) s.mem t.mem := by
  simp only [wordsVal_eq_val32]
  simpa only [show 4*(2*n)=8*n by omega_using []] using
    (sel_ok c (2*n) hs hc (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]) (by omega_using [hoa]) (by omega_using [hob]))

theorem selectTail_ok (K : TCombCfg) {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (hq : K.Q.x+24*K.L.M.n≤size)
    (hzle : K.zero+8*K.L.M.n≤size)
    (hza : K.zero+8*K.L.M.n≤K.Q.x ∨ K.Q.x+24*K.L.M.n≤K.zero)
    (hone : K.one<2^(64*K.L.M.n))
    (ha : a<2^31) (ga : s.gpr .r9=BitVec.ofNat 32 a)
    (hz : wordsVal s.mem base K.zero K.L.M.n=0) :
    WP isa (.block K.selectTail) s fun t =>
      wordsVal t.mem base K.Q.x K.L.M.n=wordsVal s.mem base K.Q.x K.L.M.n ∧
      wordsVal t.mem base K.Q.y K.L.M.n=(if a=0 then K.one else wordsVal s.mem base K.Q.y K.L.M.n) ∧
      wordsVal t.mem base K.Q.z K.L.M.n=(if a=0 then 0 else K.one) ∧
      Rest [.r4,.r5,.r10] s t ∧ Outside base K.Q.x (24*K.L.M.n) s.mem t.mem := by
  have hy : K.Q.y=K.Q.x+8*K.L.M.n := rfl
  have hzz : K.Q.z=K.Q.x+16*K.L.M.n := by
    simp only [TCombCfg.Q, VG.Impl.Weierstrass.Arm.Point.ptAt, Impl.Weierstrass.Point.elemBytes]
    omega_using []
  have hn := hs.nowrap
  unfold TCombCfg.selectTail
  rw [List.append_assoc,List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs (o := K.Q.z) (n := K.L.M.n)
    (by rw [hzz]; omega_using [hq]) hone) fun s₁ ⟨one₁,k₁,O₁⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (eqMask_ok (op2_imm (by decide))) fun s₂ ⟨mask₂,k₂,mem₂⟩ => ?_
  have k₁₂ : Rest [.r4,.r5,.r10] s s₂ := (k₁.mono (by simp)).trans (k₂.mono (by simp))
  have hs₂ := hs.of_rest k₁₂ (by decide)
  have cm₂ : s₂.gpr .r10=if decide (a=0) then BitVec.allOnes 32 else 0 := by
    rw [mask₂,k₁.gpr .r9 (by decide),ga]
    change 0#32-(((BitVec.ofNat 32 a ^^^ 0#32)-1) >>> 31)=_
    rw [equality_mask (by simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a<2^32 by omega_using [ha])]; exact ha)
      (by decide)]
    have e : BitVec.ofNat 32 a=0#32 ↔ a=0 := by
      exact ofNat32_eq (by omega_using [ha]) (by decide)
    simp only [e,decide_eq_true_eq]
  refine VG.Proof.X25519.Arm.WP.append (selField_ok hs₂ (decide (a=0)) cm₂
    (o := K.Q.y) (a := K.Q.y) (b := K.Q.z) (n := K.L.M.n)
    (by rw [hy]; omega_using [hq]) (by rw [hy]; omega_using [hq]) (by rw [hzz]; omega_using [hq])
    (.inl (Nat.le_refl _)) (.inl (by rw [hy,hzz]; omega_using []))) fun s₃ ⟨y₃,k₃,O₃⟩ => ?_
  have k₁₃ : Rest [.r4,.r5,.r10] s s₃ := k₁₂.trans (k₃.mono (by simp))
  have hs₃ := hs.of_rest k₁₃ (by decide)
  have cm₃ : s₃.gpr .r10=if decide (a=0) then BitVec.allOnes 32 else 0 := by
    rw [k₃.gpr .r10 (by decide),cm₂]
  refine WP.mono (selField_ok hs₃ (decide (a=0)) cm₃
    (o := K.Q.z) (a := K.Q.z) (b := K.zero) (n := K.L.M.n)
    (by rw [hzz]; omega_using [hq]) (by rw [hzz]; omega_using [hq]) hzle (.inl (Nat.le_refl _)) (by rw [hzz]; omega_using [hza]))
    fun s₄ ⟨z₄,k₄,O₄⟩ => ?_
  have oldx : wordsVal s₄.mem base K.Q.x K.L.M.n=wordsVal s.mem base K.Q.x K.L.M.n := by
    rw [O₄.wordsVal (by rw [hzz]; omega_using []) (by omega_using [hq, hn]),O₃.wordsVal (by rw [hy]; omega_using []) (by omega_using [hq, hn]),
      mem₂,O₁.wordsVal (by rw [hzz]; omega_using []) (by omega_using [hq, hn])]
  have oldy : wordsVal s₂.mem base K.Q.y K.L.M.n=wordsVal s.mem base K.Q.y K.L.M.n := by
    rw [mem₂,O₁.wordsVal (by rw [hy,hzz]; omega_using []) (by omega_using [hq, hy, hn])]
  have oz : wordsVal s₃.mem base K.Q.z K.L.M.n=K.one := by
    rw [O₃.wordsVal (by rw [hy,hzz]; omega_using []) (by omega_using [hq, hzz, hn]),mem₂,one₁]
  have zero₃ : wordsVal s₃.mem base K.zero K.L.M.n=0 := by
    rw [O₃.wordsVal (by rw [hy]; omega_using [hza]) (by omega_using [hzle, hn]),mem₂,
      O₁.wordsVal (by rw [hzz]; omega_using [hza]) (by omega_using [hzle, hn]),hz]
  refine ⟨oldx,?_,?_,k₁₃.trans (k₄.mono (by simp)),?_⟩
  · rw [O₄.wordsVal (by rw [hy,hzz]; omega_using []) (by omega_using [hq, hy, hn]),y₃,mem₂,one₁]
    simp only [decide_eq_true_eq]
    split <;> first | rfl | exact mem₂ ▸ oldy
  · rw [z₄,oz,zero₃]
    simp only [decide_eq_true_eq]
  · have O₂ : Outside base K.Q.x (24*K.L.M.n) s₁.mem s₂.mem := by rw [mem₂]; exact Outside.refl _ _ _ _
    exact ((O₁.mono (by rw [hzz]; omega_using []) (by rw [hzz]; omega_using [])).trans O₂).trans
      ((O₃.mono (by rw [hy]; omega_using []) (by rw [hy]; omega_using [])).trans
        (O₄.mono (by rw [hzz]; omega_using []) (by rw [hzz]; omega_using [])))

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombLoop`, which only this module used -/

section

/-! The table scan's public loop retains exactly the chosen entry. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

structure ScanInv (K : TCombCfg) (base X : Addr) (s₀ : State) (a m : Nat) (s : State) : Prop where
  ptr : s.gpr .r8=s₀.gpr .r8+BitVec.ofNat 32 (16*K.L.M.n*(m-1))
  index : s.gpr .r7=BitVec.ofNat 32 m
  keep : Rest [.r4,.r5,.r7,.r8,.r10] s₀ s
  unch : Outside base K.Q.x (16*K.L.M.n) s₀.mem s.mem
  val : ∀ i<4*K.L.M.n, w32 s.mem base (K.Q.x+4*i) =
    if 1≤a ∧ a<m then w32 s₀.mem X (16*K.L.M.n*(a-1)+4*i) else 0

theorem prefix_step {a m : Nat} (hm : 1≤m) (f : Nat → Nat) :
    (if a=m then f m else if 1≤a ∧ a<m then f a else 0) =
      if 1≤a ∧ a<m+1 then f a else 0 := by
  by_cases h : a=m
  · subst a; simp only [↓reduceIte,hm,true_and,Nat.lt_succ_self]
  · have he : (1≤a ∧ a<m) ↔ (1≤a ∧ a<m+1) := by omega_using [h]
    simp only [h,↓reduceIte,he]

theorem scan_step (K : TCombCfg) {s₀ s : State} {base X : Addr} {size a m : Nat}
    (hs₀ : Scr s₀ base size) (hX : State.addr (s₀.gpr .r8)=X)
    (ho : K.Q.x+16*K.L.M.n ≤ size) (hi : 16*K.L.M.n ≤ 4096)
    (fit : X.toNat+16*K.L.M.n*K.H ≤ 2^32)
    (hr : InRegions (s₀.rd ++ s₀.wr) X (16*K.L.M.n*K.H))
    (hd : Region.Disjoint ⟨X,16*K.L.M.n*K.H⟩ ⟨base,size⟩)
    (hn : 1≤K.L.M.n) (hH : K.H+1<2^31)
    (ha : a≤K.H) (ga : s₀.gpr .r9=BitVec.ofNat 32 a)
    (es : encodable (BitVec.ofNat 32 (16*K.L.M.n))=true)
    (eh : encodable (BitVec.ofNat 32 (K.H+1))=true)
    (hm : 1≤m) (mh : m≤K.H) (I : ScanInv K base X s₀ a m s) :
    WP isa (.block K.selectBody) s fun t => ScanInv K base X s₀ a (m+1) t ∧
      t.z=decide (m+1=K.H+1) := by
  have hs := hs₀.of_rest I.keep (by decide)
  have hmul : 16*K.L.M.n*(m-1)+16*K.L.M.n ≤ 16*K.L.M.n*K.H := by
    calc
      16*K.L.M.n*(m-1)+16*K.L.M.n = 16*K.L.M.n*m := by
        rw [← Nat.mul_succ]; congr 1; omega_using [hm]
      _ ≤ 16*K.L.M.n*K.H := Nat.mul_le_mul_left _ mh
  have hop : 16*K.L.M.n*(m-1)<2^32 := by omega_using [fit, hn, hmul]
  have ptrfit : (s₀.gpr .r8).toNat+16*K.L.M.n*(m-1)<2^32 := by
    have hnX : (s₀.gpr .r8).toNat=X.toNat := by rw [← hX,addr_toNat]
    omega_using [fit, hn, hmul, hnX]
  have hx : State.addr (s.gpr .r8)=off X (16*K.L.M.n*(m-1)) := by
    rw [I.ptr,VG.Arm.addr_add ptrfit,hX]
  have efit : (off X (16*K.L.M.n*(m-1))).toNat+16*K.L.M.n ≤ 2^32 := by
    rw [off,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 16*K.L.M.n*(m-1)<2^64 by omega_using [fit, hmul]),
      Nat.mod_eq_of_lt (show X.toNat+16*K.L.M.n*(m-1)<2^64 by omega_using [fit, hmul])]
    omega_using [fit, hmul]
  have er : InRegions (s.rd ++ s.wr) (off X (16*K.L.M.n*(m-1))) (16*K.L.M.n) := by
    rw [I.keep.rd,I.keep.wr]
    exact CallLay.inRegions_sub hr hmul (by omega_using [fit])
  have ed : Region.Disjoint ⟨off X (16*K.L.M.n*(m-1)),16*K.L.M.n⟩ ⟨base,size⟩ :=
    hd.sub_left (Offset.sub_base X hmul)
  refine WP.mono (selectBody_ok K (a := a) (m := m) hs hx ho hi efit er ed (by omega_using [hH, ha]) (by omega_using [hH, mh])
    (by rw [I.keep.gpr .r9 (by decide),ga]) I.index es eh (by omega_using [hH, mh]) (by omega_using [hH]))
    fun t ⟨v,k,O,p,index,z⟩ => ⟨?_,z⟩
  refine ⟨?_,index,I.keep.trans k,I.unch.trans O,?_⟩
  · have he : 16*K.L.M.n*(m-1)+16*K.L.M.n=16*K.L.M.n*m := by
      rw [← Nat.mul_succ]; congr 1; omega_using [hm]
    rw [p,I.ptr,BitVec.add_assoc,← BitVec.ofNat_add,he,show m+1-1=m by omega_using []]
  · intro i hii
    have hoff : 16*K.L.M.n*(m-1)+4*i+4 ≤ 16*K.L.M.n*K.H := by omega_using [ho, hi, fit, hn, hH, ha, hm, mh, hmul, hop, ptrfit, efit, hii]
    have src : w32 s.mem (off X (16*K.L.M.n*(m-1))) (4*i) =
        w32 s₀.mem X (16*K.L.M.n*(m-1)+4*i) := by
      unfold w32 off
      rw [Offset.add_add]
      apply congrArg BitVec.toNat
      exact (outside_frame (size := size) I.unch ho).readW
        (r := ⟨X,16*K.L.M.n*K.H⟩)
        (Offset.contains_base (d := 16*K.L.M.n*(m-1)+4*i) (n := 4) X hoff (by omega_using [fit, hmul, hii]))
        (fun r hr' => by rcases List.mem_singleton.mp hr' with rfl; exact hd) (by decide)
    rw [v i hii,src,I.val i hii]
    exact prefix_step hm (fun q => w32 s₀.mem X (16*K.L.M.n*(q-1)+4*i))

/-- All rows are visited in order, independently of the selected magnitude. -/
theorem scan_loop_ok (K : TCombCfg) {s₀ : State} {base X : Addr} {size a : Nat}
    (hs₀ : Scr s₀ base size) (hX : State.addr (s₀.gpr .r8)=X)
    (ho : K.Q.x+16*K.L.M.n ≤ size) (hi : 16*K.L.M.n ≤ 4096)
    (fit : X.toNat+16*K.L.M.n*K.H ≤ 2^32)
    (hr : InRegions (s₀.rd ++ s₀.wr) X (16*K.L.M.n*K.H))
    (hd : Region.Disjoint ⟨X,16*K.L.M.n*K.H⟩ ⟨base,size⟩)
    (hn : 1≤K.L.M.n) (hH : K.H+1<2^31)
    (ha : a≤K.H) (ga : s₀.gpr .r9=BitVec.ofNat 32 a)
    (es : encodable (BitVec.ofNat 32 (16*K.L.M.n))=true)
    (eh : encodable (BitVec.ofNat 32 (K.H+1))=true)
    (gm : s₀.gpr .r7=1)
    (hz : ∀ i<4*K.L.M.n,w32 s₀.mem base (K.Q.x+4*i)=0) :
    WP isa (.loop (.block K.selectBody) .ne) s₀
      (ScanInv K base X s₀ a (K.H+1)) := by
  have hHp : 1≤K.H := Nat.two_pow_pos _
  refine WP.loop (M := isa)
    (fun j s => 1≤j ∧ j≤K.H ∧ ScanInv K base X s₀ a (K.H+1-j) s)
    (fun j s ⟨j1,jH,I⟩ => ?_) K.H s₀ ?_
  · have m1 : 1≤K.H+1-j := by omega_using [jH]
    have mH : K.H+1-j≤K.H := by omega_using [j1]
    refine WP.mono (scan_step K hs₀ hX ho hi fit hr hd hn hH ha ga es eh m1 mH I)
      fun t ⟨I',z⟩ => ?_
    by_cases je : j=1
    · have me : K.H+1-j+1=K.H+1 := by omega_using [je]
      refine .inl ⟨?_,me ▸ I'⟩
      rw [VG.Proof.X25519.Arm.eval_ne,z,decide_eq_true me]
      rfl
    · have me : ¬K.H+1-j+1=K.H+1 := by omega_using [hHp, je]
      refine .inr ⟨?_,j-1,by omega_using [j1],by omega_using [j1, je],by omega_using [jH],?_⟩
      · rw [VG.Proof.X25519.Arm.eval_ne,z,decide_eq_false me]
        rfl
      · have e : K.H+1-(j-1)=K.H+1-j+1 := by omega_using [j1, jH]
        rw [e]; exact I'
  · refine ⟨hHp,Nat.le_refl _,?_⟩
    have e : K.H+1-K.H=1 := by omega_using []
    rw [e]
    refine ⟨?_,?_,Rest.refl _ _,Outside.refl _ _ _ _,?_⟩
    · simp only [Nat.sub_self,Nat.mul_zero,BitVec.add_zero]
    · exact gm
    · intro i hi'
      rw [hz i hi']
      have h : ¬(1≤a ∧ a<1) := by omega_using []
      simp only [h,↓reduceIte]

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombDigit`, which only this module used -/

section

/-! ### `Weierstrass.Arm.TCombIndex`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.Arm.TCombMagnitude`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.Arm.TCombHorner`, which this module and modules that import it used -/

section

/-! The ARM comb decodes bits using the same Horner invariant as x86. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.X25519.Arm

structure RegOnly (rs : List Reg) (s t : State) : Prop where
  keep : Rest rs s t
  mem : t.mem=s.mem

theorem hornerAt_ok (K : TCombCfg) {v : Nat → Nat} (hv : ∀ i,v i≤1) :
    ∀ k d s, k<32 → K.L.bits%4096+d+k ≤ 4096 →
    (∀ i<k,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4+BitVec.ofNat 32 (K.L.bits%4096+d+i))) 1 ∧
      s.mem (State.addr (s.gpr .r4+BitVec.ofNat 32 (K.L.bits%4096+d+i))) = BitVec.ofNat 8 (v (d+i))) →
    WP isa (.block (K.hornerAt d k)) s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (hornerVal v d k) ∧ RegOnly [.r5,.r9] s t
  | 0,d,s,_,_,_ => by
    unfold TCombCfg.hornerAt
    exact wp_mov (op2_imm (by decide)) fun t u => WP.block_nil
      ⟨u.gpr,⟨u.rest (by simp),u.mem⟩⟩
  | k+1,d,s,hk,ho,hb => by
    rw [TCombCfg.hornerAt]
    refine VG.Proof.X25519.Arm.WP.append
      (hornerAt_ok K hv k (d+1) s (by omega_using [hk]) (by omega_using [ho]) (fun i hi => by
        rw [show K.L.bits%4096+(d+1)+i=K.L.bits%4096+d+(i+1) by omega_using [],
          show d+1+i=d+(i+1) by omega_using []]
        exact hb (i+1) (by omega_using [hi]))) fun s₁ ⟨v₁,k₁⟩ => ?_
    refine wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
    have ptr₂ : s₂.gpr .r4=s.gpr .r4 := by
      rw [u₂.other .r4 (by decide),k₁.keep.gpr .r4 (by decide)]
    have mem₂ : s₂.mem=s.mem := u₂.mem.trans k₁.mem
    have rd₂ : s₂.rd ++ s₂.wr=s.rd ++ s.wr := by rw [u₂.rd,u₂.wr,k₁.keep.rd,k₁.keep.wr]
    have h0 := hb 0 (by omega_using [])
    simp only [Nat.add_zero] at h0
    refine wp_ldrb (by omega_using [ho]) rfl (by rw [ptr₂,rd₂]; exact h0.1) fun s₃ u₃ =>
      wp_dp (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
    refine ⟨?_,⟨k₁.keep.trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))),
      by rw [u₄.mem,u₃.mem,mem₂]⟩⟩
    · rw [u₄.gpr,dpVal,u₃.other .r9 (by decide),u₂.gpr,dpVal,v₁,u₃.gpr,ptr₂,mem₂,h0.2]
      have hn := hornerVal_lt hv (d+1) k
      have hvd := hv d
      have hp : 2^k < 2^31 := Nat.pow_lt_pow_right (by decide) (by omega_using [hk])
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.toNat_setWidth,hornerVal]
      rw [Nat.mod_eq_of_lt (by omega_using [hn, hp] : hornerVal v (d+1) k<2^32),
        Nat.mod_eq_of_lt (by omega_using [hvd] : v d<2^8),Nat.mod_eq_of_lt (by omega_using [hvd] : v d<2^32)]
      omega_using []

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! The signed digit's magnitude uses the same arithmetic theorem as x86. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.X25519.Arm

theorem magnitude_ok (K : TCombCfg) {s : State} {v : Nat}
    (hw : K.w<9) (hv : v<2^K.w) (gv : s.gpr .r9=BitVec.ofNat 32 v) :
    WP isa (.block K.magnitude) s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (magH K.H v) ∧ RegOnly [.r4,.r5,.r9] s t := by
  have enc : encodable (BitVec.ofNat 32 K.H)=true :=
    (by decide : ∀ w<9,encodable (BitVec.ofNat 32 (2^(w-1)))=true) K.w hw
  unfold TCombCfg.magnitude
  refine wp_dp (op2_imm enc) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => wp_dp (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  let D := BitVec.ofNat 32 v-BitVec.ofNat 32 K.H
  let M := 0#32-(D >>> 31)
  have hd : s₁.gpr .r9=D := by rw [u₁.gpr,dpVal,gv]
  have hs : s₂.gpr .r4=D >>> 31 := by rw [u₂.gpr,hd]
  have hm : s₄.gpr .r4=M := by
    rw [u₄.gpr,dpVal,u₃.gpr,u₃.other .r4 (by decide),hs]; rfl
  have hn : s₅.gpr .r9=D ^^^ M := by
    rw [u₅.gpr,dpVal,hm,u₄.other .r9 (by decide),u₃.other .r9 (by decide),u₂.other .r9 (by decide),hd]
  have k₁₂ : Rest [.r4,.r5,.r9] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have k₃₄ : Rest [.r4,.r5,.r9] s₂ s₄ := (u₃.rest (by simp)).trans (u₄.rest (by simp))
  have k₅₆ : Rest [.r4,.r5,.r9] s₄ s₆ := (u₅.rest (by simp)).trans (u₆.rest (by simp))
  refine ⟨?_,⟨(k₁₂.trans k₃₄).trans k₅₆,by rw [u₆.mem,u₅.mem,u₄.mem,u₃.mem,u₂.mem,u₁.mem]⟩⟩
  rw [u₆.gpr,dpVal,hn,u₅.other .r4 (by decide),hm]
  exact magH_fact K.w hw v hv

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! Digit and sign decoding share the public window-address calculation. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm VG.Proof.X25519.Arm

theorem windowIndex_ok (K : TCombCfg) {s : State} {j : Nat}
    (hw : K.w<9) (gj : s.gpr .r11=BitVec.ofNat 32 j) :
    WP isa (.block K.windowIndex) s fun t =>
      t.gpr .r4=t.gpr .r12+BitVec.ofNat 32 (K.w*j+farOff K.L.bits) ∧ RegOnly [.r4] s t := by
  have enc : encodable (BitVec.ofNat 32 K.w)=true :=
    (by decide : ∀ w<9,encodable (BitVec.ofNat 32 w)=true) K.w hw
  unfold TCombCfg.windowIndex
  simp only [List.cons_append,List.nil_append]
  refine wp_mov (op2_imm enc) fun s₁ u₁ => wp_mul fun s₂ u₂ => wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have k₁₂ : Rest [.r4] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have k₃ : Rest [.r4] s s₃ := k₁₂.trans (u₃.rest (by simp))
  have p : s₃.gpr .r4=s₃.gpr .r12+BitVec.ofNat 32 (K.w*j) := by
    rw [u₃.gpr,dpVal,u₂.gpr,u₁.gpr,u₁.other .r11 (by decide),gj,← BitVec.ofNat_mul,
      u₃.other .r12 (by decide)]
  rw [← List.append_nil (far .r4 K.L.bits)]
  refine wp_far (d := K.L.bits) p (by decide) fun s₄ k₄ m₄ p₄ => WP.block_nil
    ⟨p₄,⟨k₃.trans k₄,by rw [m₄,u₃.mem,u₂.mem,u₁.mem]⟩⟩

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! Decode one signed comb digit, reading only the last window's real bits. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.X25519.Arm VG.Proof.Mont.Arm

theorem lastTest_ok (K : TCombCfg) {s : State} {j : Nat}
    (hj : j<2^32) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (gj : s.gpr .r11=BitVec.ofNat 32 j) :
    WP isa (.block K.lastTest) s fun t =>
      t.z=decide (j=K.J-1) ∧ RegOnly [] s t := by
  unfold TCombCfg.lastTest
  refine wp_cmp (op2_imm enc) fun t f z => WP.block_nil ⟨?_,⟨f.rest _,f.mem⟩⟩
  rw [z,gj]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  change BitVec.ofNat 32 j-BitVec.ofNat 32 (K.J-1)=0#32 ↔ j=K.J-1
  rw [sub_zero_iff,ofNat32_eq hj hJ]

theorem hornerWindow_ok (K : TCombCfg) {s : State} {base : Addr} {size len j count : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : K.w<9) (hc : count≤K.w) (hd : K.L.bits<8192)
    (ho : K.L.bits%4096+K.w≤4096) (hl : K.L.bits+K.w*j+count≤len)
    (hp : s.gpr .r4=s.gpr .r12+BitVec.ofNat 32 (K.w*j+farOff K.L.bits))
    {v : Nat → Nat} (hv : ∀ i,v i≤1)
    (hb : ∀ i<count,s.mem (VG.Proof.Mont.off base (K.L.bits+K.w*j+i))=BitVec.ofNat 8 (v i)) :
    WP isa (.block (K.horner count)) s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (hornerVal v 0 count) ∧ RegOnly [.r5,.r9] s t := by
  unfold TCombCfg.horner
  refine hornerAt_ok K hv count 0 s (by omega_using [hw, hc]) (by omega_using [hc, ho]) fun i hi => ?_
  have fa := far_add hd
  have ea : State.addr (s.gpr .r4+BitVec.ofNat 32 (K.L.bits%4096+0+i))=
      VG.Proof.Mont.off base (K.L.bits+K.w*j+i) := by
    rw [hf.ea_reg hs hp (by omega_using [hl, hi, fa])]
    congr 1
    omega_using [fa]
  rw [ea]
  exact ⟨hf.read (by omega_using [hl, hi]),by simpa only [Nat.zero_add] using hb i hi⟩

theorem digitWords_ok (K : TCombCfg) {s : State} {base : Addr} {size len j : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : K.w<9) (ht : K.topBits≤K.w)
    (hj : j<2^32) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (hd : K.L.bits<8192) (ho : K.L.bits%4096+K.w≤4096)
    (hl : K.L.bits+K.w*j+(if j=K.J-1 then K.topBits else K.w)≤len)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    {v : Nat → Nat} (hv : ∀ i,v i≤1)
    (hb : ∀ i<(if j=K.J-1 then K.topBits else K.w),
      s.mem (VG.Proof.Mont.off base (K.L.bits+K.w*j+i))=BitVec.ofNat 8 (v i)) :
    WP isa K.digit s fun t =>
      t.gpr .r9=BitVec.ofNat 32
        (magH K.H (hornerVal v 0 (if j=K.J-1 then K.topBits else K.w))) ∧
      RegOnly [.r4,.r5,.r9] s t := by
  let count := if j=K.J-1 then K.topBits else K.w
  have hc : count≤K.w := by dsimp only [count]; split <;> omega_arith
  unfold TCombCfg.digit
  rw [WP.seq_iff]
  refine WP.mono (windowIndex_ok K hw gj) fun s₁ ⟨p₁,k₁⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (lastTest_ok K hj hJ enc (by rw [k₁.keep.gpr .r11 (by decide),gj]))
    fun s₂ ⟨z₂,k₂⟩ => ?_
  have keep₂ : Rest [.r4] s s₂ := k₁.keep.trans (k₂.keep.mono (by simp))
  have mem₂ : s₂.mem=s.mem := k₂.mem.trans k₁.mem
  have hs₂ := hs.of_rest keep₂ (by decide)
  have hf₂ := hf.of_rest keep₂
  have p₂ : s₂.gpr .r4=s₂.gpr .r12+BitVec.ofNat 32 (K.w*j+farOff K.L.bits) := by
    rw [k₂.keep.gpr .r4 (by decide),p₁,k₂.keep.gpr .r12 (by decide)]
  have decode : WP isa
      (.ite .eq (.block (K.horner K.topBits)) (.block (K.horner K.w))) s₂ fun t =>
      t.gpr .r9=BitVec.ofNat 32 (hornerVal v 0 count) ∧ RegOnly [.r5,.r9] s₂ t := by
    have hh := hornerWindow_ok K hs₂ hf₂ hw hc hd ho hl p₂ hv
      (by intro i hi; rw [mem₂]; exact hb i hi)
    by_cases h : j=K.J-1
    · apply WP.ite true (by change some s₂.z=some true; simp only [z₂,h,decide_true])
      · intro _; simpa only [count,h,↓reduceIte] using hh
      · intro impossible; cases impossible
    · apply WP.ite false (by change some s₂.z=some false; simp only [z₂,h,decide_false])
      · intro impossible; cases impossible
      · intro _; simpa only [count,h,↓reduceIte] using hh
  rw [WP.seq_iff]
  refine WP.mono decode fun s₃ ⟨v₃,k₃⟩ => ?_
  have hvlt : hornerVal v 0 count<2^K.w :=
    Nat.lt_of_lt_of_le (hornerVal_lt hv 0 count) (Nat.pow_le_pow_right (by decide) hc)
  refine WP.mono (magnitude_ok K hw hvlt v₃) fun s₄ ⟨v₄,k₄⟩ =>
    ⟨v₄,⟨((keep₂.mono (by simp)).trans (k₃.keep.mono (by simp))).trans k₄.keep,
      k₄.mem.trans (k₃.mem.trans mem₂)⟩⟩

theorem digit_ok (K : TCombCfg) {s : State} {base : Addr} {size len j k : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : K.w<9) (hj : j<K.J) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (start : K.w*(K.J-1)≤K.L.nbits) (cover : K.L.nbits≤K.w*K.J)
    (hd : K.L.bits<8192) (ho : K.L.bits%4096+K.w≤4096)
    (hl : K.L.bits+K.L.nbits≤len) (hk : k<2^K.L.nbits)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hb : ∀ i<K.L.nbits,s.mem (VG.Proof.Mont.off base (K.L.bits+i))=
      if k.testBit i then 1 else 0) :
    WP isa K.digit s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (magH K.H (combWin K.w k j)) ∧ RegOnly [.r4,.r5,.r9] s t := by
  let count := if j=K.J-1 then K.topBits else K.w
  have bounds := windowBits_bounds hj start cover
  change count≤K.w ∧ K.w*j+count≤K.L.nbits ∧
    (count=K.w ∨ K.w*j+count=K.L.nbits) at bounds
  let v := fun i => (k.testBit (K.w*j+i)).toNat
  have hv : ∀ i,v i≤1 := by
    intro i
    dsimp only [v]
    cases k.testBit (K.w*j+i) <;> decide
  have bytes : ∀ i<count,s.mem (VG.Proof.Mont.off base (K.L.bits+K.w*j+i))=
      BitVec.ofNat 8 (v i) := by
    intro i hi
    rw [show K.L.bits+K.w*j+i=K.L.bits+(K.w*j+i) by omega_using [],hb _ (by omega_using [bounds, hi])]
    dsimp only [v]
    cases k.testBit (K.w*j+i) <;> rfl
  refine WP.mono (digitWords_ok K hs hf hw (topWindow_le (by omega_using [hj]) cover)
    (by omega_using [hj, hJ]) hJ enc hd ho (by omega_using [hl, bounds]) gj hv bytes) fun t ⟨val,keep⟩ => ⟨?_,keep⟩
  rw [val]
  change BitVec.ofNat 32 (magH K.H (hornerVal v 0 count))=_
  rw [window_without_padding bounds.1 bounds.2.2 hk]

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombStep`, which only this module used -/

section

/-! ### `Weierstrass.Arm.TCombEntry`, which only this module used -/

section

/-! ### `Weierstrass.Arm.TCombSelectTable`, which only this module used -/

section

/-! ### `Weierstrass.Arm.TCombSelect`, which only this module used -/

section

/-! ### `Weierstrass.Arm.TCombSetup`, which only this module used -/

section

/-! Initialize the same read-only comb table layout used by P-256. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem selectSetup_ok (K : TCombCfg) {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (ho : K.Q.x+16*K.L.M.n ≤ size)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (enc : encodable (BitVec.ofNat 32 (16*K.L.M.n*K.H))=true) :
    WP isa (.block K.selectSetup) s fun t =>
      t.gpr .r8=s.syms K.tsym+BitVec.ofNat 32 (16*K.L.M.n*K.H*j) ∧
      t.gpr .r7=1 ∧ (∀ i<4*K.L.M.n,w32 t.mem base (K.Q.x+4*i)=0) ∧
      Rest [.r4,.r7,.r8] s t ∧ Outside base K.Q.x (16*K.L.M.n) s.mem t.mem := by
  have hy : K.Q.y=K.Q.x+8*K.L.M.n := rfl
  have hn := hs.nowrap
  unfold TCombCfg.selectSetup
  simp only [List.cons_append]
  refine WP.cons (s' := s.setReg .r8 (s.syms K.tsym)) rfl ?_
  let s₁ := s.setReg .r8 (s.syms K.tsym)
  obtain u₁ : Upd s s₁ .r8 (s.syms K.tsym) := Upd.setReg _ _ _
  refine wp_mov (op2_imm enc) fun s₂ u₂ => wp_mul fun s₃ u₃ =>
    wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  obtain k₁₂ : Rest [.r4,.r8] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  obtain k₃₄ : Rest [.r4,.r8] s₂ s₄ := (u₃.rest (by simp)).trans (u₄.rest (by simp))
  obtain k₄ := k₁₂.trans k₃₄
  obtain hs₄ := hs.of_rest k₄ (by decide)
  obtain mem₄ : s₄.mem=s.mem := by rw [u₄.mem,u₃.mem,u₂.mem,u₁.mem]
  obtain g₈ : s₄.gpr .r8=s.syms K.tsym+BitVec.ofNat 32 (16*K.L.M.n*K.H*j) := by
    rw [u₄.gpr,dpVal,u₃.other .r8 (by decide),u₂.other .r8 (by decide),u₁.gpr,
      u₃.gpr,u₂.gpr,u₂.other .r11 (by decide),u₁.other .r11 (by decide),gj,← BitVec.ofNat_mul]
  rw [List.append_assoc,setConst_eq]
  refine VG.Proof.X25519.Arm.WP.append
    (constSteps_ok hs₄ (o := K.Q.x) (x := 0) (2*K.L.M.n) (by omega_using [ho]))
    fun s₅ ⟨vx,k₅,Ox⟩ => ?_
  obtain hs₅ := hs₄.of_rest k₅ (by decide)
  rw [setConst_eq]
  refine VG.Proof.X25519.Arm.WP.append
    (constSteps_ok hs₅ (o := K.Q.y) (x := 0) (2*K.L.M.n) (by rw [hy]; omega_using [ho]))
    fun s₆ ⟨vy,k₆,Oy⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have mem₇ : s₇.mem=s₆.mem := u₇.mem
  obtain k₄₇ : Rest [.r4,.r7] s₄ s₇ := (k₅.mono (by simp)).trans
    ((k₆.mono (by simp)).trans (u₇.rest (by simp)))
  refine ⟨?_,u₇.gpr,?_,(k₄.mono (by simp)).trans (k₄₇.mono (by simp)),?_⟩
  · rw [k₄₇.gpr .r8 (by decide),g₈]
  · intro i hi
    rw [mem₇]
    by_cases hx : i<2*K.L.M.n
    · rw [Oy.w32 (by rw [hy]; omega_using [hx]) (by omega_using [ho, hn, hi]),vx i hx]
      simp only [Nat.zero_shiftRight,Nat.zero_mod]
    · have hyi : i-2*K.L.M.n<2*K.L.M.n := by omega_using [hi]
      rw [show K.Q.x+4*i=K.Q.y+4*(i-2*K.L.M.n) by rw [hy]; omega_using [hx],vy _ hyi]
      simp only [Nat.zero_shiftRight,Nat.zero_mod]
  · rw [mem₇,← mem₄]
    exact (Ox.mono (Nat.le_refl _) (by omega_using [])).trans (Oy.mono (by rw [hy]; omega_using []) (by rw [hy]; omega_using []))

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Mont.Words32At`, which only this module used -/

section

/-! Compare numbers whose words are stored at different bases and offsets. -/

@[expose] public section
namespace VG.Proof.Mont

private theorem val32_congr_at {m m' : Mem} {base base' : Addr} {d d' : Nat} :
    ∀ {k : Nat}, (∀ i<k,w32 m base (d+4*i)=w32 m' base' (d'+4*i)) →
      val32 m base d k=val32 m' base' d' k
  | 0,_ => rfl
  | k+1,h => by
    rw [val32_succ,val32_succ,h k (Nat.lt_succ_self _),
      val32_congr_at fun i hi => h i (by omega_using [hi])]

end VG.Proof.Mont

end

end


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
  obtain hHp : 1≤K.H := Nat.two_pow_pos _
  obtain span : 16*K.L.M.n*(a-1)+16*K.L.M.n≤16*K.L.M.n*K.H := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by omega_using [ha, hHp])
  unfold TCombCfg.select
  rw [WP.seq_iff]
  refine WP.mono (selectSetup_ok K hs (by omega_using [hq]) gj er) fun s₁ ⟨p₁,g₁,z₁,k₁,O₁⟩ => ?_
  obtain hs₁ := hs.of_rest k₁ (by decide)
  obtain hx₁ : State.addr (s₁.gpr .r8)=X := by rw [p₁]; exact hX
  obtain hr₁ : InRegions (s₁.rd ++ s₁.wr) X (16*K.L.M.n*K.H) := by rw [k₁.rd,k₁.wr]; exact hr
  obtain ga₁ : s₁.gpr .r9=BitVec.ofNat 32 a := by rw [k₁.gpr .r9 (by decide),ga]
  rw [WP.seq_iff]
  refine WP.mono (scan_loop_ok K hs₁ hx₁ (by omega_using [hq]) (by have := hs.small; omega_using [hq, small])
    fit hr₁ hd hn hH ha ga₁ es eh g₁ z₁) fun s₂ I => ?_
  obtain keep₂ : Rest [.r4,.r5,.r7,.r8,.r10] s s₂ := (k₁.mono (by simp)).trans I.keep
  obtain hs₂ := hs.of_rest keep₂ (by decide)
  obtain source : ∀ i<4*K.L.M.n,
      w32 s₁.mem X (16*K.L.M.n*(a-1)+4*i)=w32 s.mem X (16*K.L.M.n*(a-1)+4*i) := by
    intro i hi
    apply congrArg BitVec.toNat
    exact (outside_frame (size := size) O₁ (by omega_using [hq])).readW
      (r := ⟨X,16*K.L.M.n*K.H⟩)
      (Offset.contains_base (d := 16*K.L.M.n*(a-1)+4*i) (n := 4) X (by omega_using [span, hi]) (by omega_using [fit, span, hi]))
      (fun r hr' => by rcases List.mem_singleton.mp hr' with rfl; exact hd) (by decide)
  obtain raw : ∀ i<4*K.L.M.n,w32 s₂.mem base (K.Q.x+4*i)=
      if a=0 then 0 else w32 s.mem X (16*K.L.M.n*(a-1)+4*i) := by
    intro i hi
    rw [I.val i hi,source i hi]
    by_cases zero : a=0
    · have no : ¬(1≤a ∧ a<K.H+1) := by omega_using [zero]
      rw [ite_eq_right_of_eq_false _ _ (eq_false no)]
      simp only [zero,↓reduceIte]
    · have one : 1≤a := by omega_using [zero]
      obtain last : a<K.H+1 := by omega_using [ha]
      simp only [zero,one,last,and_self,↓reduceIte]
  obtain x₂ : wordsVal s₂.mem base K.Q.x K.L.M.n=
      if a=0 then 0 else wordsVal s.mem X (16*K.L.M.n*(a-1)) K.L.M.n := by
    simp only [wordsVal_eq_val32]
    by_cases zero : a=0
    · simp only [zero,↓reduceIte]
      exact val32_of_shifts _ _ _ _ 0 (Nat.two_pow_pos _) fun i hi => by
        rw [raw i (by omega_using [hi])]
        simp only [zero,↓reduceIte,Nat.zero_shiftRight,Nat.zero_mod]
    · simp only [zero,↓reduceIte]
      exact val32_congr_at fun i hi => by rw [raw i (by omega_using [hi])]; simp only [zero,↓reduceIte]
  obtain y₂ : wordsVal s₂.mem base K.Q.y K.L.M.n=
      if a=0 then 0 else wordsVal s.mem X (16*K.L.M.n*(a-1)+8*K.L.M.n) K.L.M.n := by
    simp only [wordsVal_eq_val32]
    obtain word : ∀ i<2*K.L.M.n,w32 s₂.mem base (K.Q.y+4*i)=
        if a=0 then 0 else w32 s.mem X (16*K.L.M.n*(a-1)+8*K.L.M.n+4*i) := by
      intro i hi
      obtain e := raw (2*K.L.M.n+i) (by omega_using [hi])
      rw [show K.Q.x+4*(2*K.L.M.n+i)=K.Q.y+4*i by rw [hy]; omega_using [],
        show 16*K.L.M.n*(a-1)+4*(2*K.L.M.n+i)=16*K.L.M.n*(a-1)+8*K.L.M.n+4*i by omega_using []] at e
      exact e
    by_cases zero : a=0
    · simp only [zero,↓reduceIte]
      exact val32_of_shifts _ _ _ _ 0 (Nat.two_pow_pos _) fun i hi => by
        rw [word i hi]
        simp only [zero,↓reduceIte,Nat.zero_shiftRight,Nat.zero_mod]
    · simp only [zero,↓reduceIte]
      exact val32_congr_at fun i hi => by rw [word i hi]; simp only [zero,↓reduceIte]
  obtain zero₂ : wordsVal s₂.mem base K.zero K.L.M.n=0 := by
    rw [I.unch.wordsVal (by omega_using [hza]) (by omega_using [hzle, small]),O₁.wordsVal (by omega_using [hza]) (by omega_using [hzle, small]),hz]
  refine WP.mono (selectTail_ok K (a := a) hs₂ hq hzle hza hone (by omega_using [hH, ha])
    (by rw [keep₂.gpr .r9 (by decide),ga]) zero₂) fun s₃ ⟨x₃,y₃,z₃,k₃,O₃⟩ => ?_
  refine ⟨by rw [x₃,x₂],?_,z₃,keep₂.trans (k₃.mono (by simp)),?_⟩
  · rw [y₃,y₂]
    by_cases zero : a=0 <;> simp only [zero,↓reduceIte]
  · exact ((O₁.mono (Nat.le_refl _) (by omega_using [])).trans
      (I.unch.mono (Nat.le_refl _) (by omega_using []))).trans O₃

end VG.Proof.Weierstrass.Arm.TComb

end

end


/-! Connect the ARM scan to the shared, kernel-checked comb tables. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem selectTable_ok (K : TCombCfg) {s : State} {base T : Addr} {size a j R p : Nat}
    {tbl : List (List (Nat × Nat))}
    (hs : Scr s base size) (hq : K.Q.x+24*K.L.M.n≤size)
    (hzle : K.zero+8*K.L.M.n≤size)
    (hza : K.zero+8*K.L.M.n≤K.Q.x ∨ K.Q.x+24*K.L.M.n≤K.zero)
    (hone : K.one<2^(64*K.L.M.n)) (hz : wordsVal s.mem base K.zero K.L.M.n=0)
    (hn : 1≤K.L.M.n) (hH : K.H+1<2^31) (ha : a≤K.H)
    (ga : s.gpr .r9=BitVec.ofNat 32 a) (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hT : TableMem s T (tcombWords K.L.M.n R p tbl)) (sym : State.addr (s.syms K.tsym)=T)
    (hJ : tbl.length=K.J) (hRows : ∀ j<K.J,(tbl.getD j []).length=K.H) (hj : j<K.J)
    (hp : 0<p) (hpfit : p≤2^(64*K.L.M.n))
    (hd : Region.Disjoint ⟨T,8*(tcombWords K.L.M.n R p tbl).length⟩ ⟨base,size⟩)
    (er : encodable (BitVec.ofNat 32 (16*K.L.M.n*K.H))=true)
    (es : encodable (BitVec.ofNat 32 (16*K.L.M.n))=true)
    (eh : encodable (BitVec.ofNat 32 (K.H+1))=true) :
    WP isa K.select s fun t =>
      wordsVal t.mem base K.Q.x K.L.M.n=
        (if a=0 then 0 else (combAt tbl j (a-1)).1*R%p) ∧
      wordsVal t.mem base K.Q.y K.L.M.n=
        (if a=0 then K.one else (combAt tbl j (a-1)).2*R%p) ∧
      wordsVal t.mem base K.Q.z K.L.M.n=(if a=0 then 0 else K.one) ∧
      Rest [.r4,.r5,.r7,.r8,.r10] s t ∧ Outside base K.Q.x (24*K.L.M.n) s.mem t.mem := by
  obtain total := table_bytes (n := K.L.M.n) (R := R) (p := p) hJ hRows
  let X := off T (16*K.L.M.n*K.H*j)
  obtain row := hT.row total hj hd
  change X.toNat+16*K.L.M.n*K.H≤2^32 ∧
    InRegions (s.rd ++ s.wr) X (16*K.L.M.n*K.H) ∧
    Region.Disjoint ⟨X,16*K.L.M.n*K.H⟩ ⟨base,size⟩ at row
  obtain hHp : 1≤K.H := Nat.two_pow_pos _
  obtain span : 16*K.L.M.n*K.H*j+16*K.L.M.n*K.H≤8*(tcombWords K.L.M.n R p tbl).length := by
    rw [total,← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hj
  obtain pos : 0<16*K.L.M.n*K.H := Nat.mul_pos (by omega_using [hn]) hHp
  obtain ptr : State.addr (s.syms K.tsym+BitVec.ofNat 32 (16*K.L.M.n*K.H*j))=X := by
    have fit := hT.fit
    obtain sn : (s.syms K.tsym).toNat=T.toNat := by rw [← sym,addr_toNat]
    rw [VG.Arm.addr_add (by rw [sn]; omega_using [hq, hzle, hza, hn, hH, ha, hj, total, hHp, span, pos, fit, sn]),sym]
  obtain entry := hT.entry hJ hRows hj (show a-1<K.H by omega_using [ha, hHp])
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hpfit) (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hpfit)
  rw [Nat.mul_comm j (16*K.L.M.n*K.H)] at entry
  change wordsVal s.mem X (16*K.L.M.n*(a-1)) K.L.M.n=(combAt tbl j (a-1)).1*R%p ∧
    wordsVal s.mem X (16*K.L.M.n*(a-1)+8*K.L.M.n) K.L.M.n=(combAt tbl j (a-1)).2*R%p at entry
  refine WP.mono (selectRow_ok K hs hq hzle hza hone hz hn hH ha ga gj ptr
    row.1 row.2.1 row.2.2 er es eh) fun t ⟨x,y,z,keep,unch⟩ => ?_
  exact ⟨by rw [x,entry.1],by rw [y,entry.2],z,keep,unch⟩

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombSign`, which only this module used -/

section

/-! The digit's sign uses its top bit, with a zero virtual bit in the last window. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.X25519.Arm VG.Proof.Mont.Arm

theorem signRead_ok (K : TCombCfg) {s : State} {base : Addr} {size len j : Nat} {b : Bool}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : 1≤K.w ∧ K.w<9) (hd : K.L.bits<8192)
    (ho : K.L.bits%4096+K.w≤4096) (hl : K.L.bits+K.w*j+K.w≤len)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hb : s.mem (VG.Proof.Mont.off base (K.L.bits+K.w*j+K.w-1))=if b then 1 else 0) :
    WP isa (.block K.signRead) s fun t =>
      t.gpr .r10=(if b then 0 else BitVec.allOnes 32) ∧ RegOnly [.r4,.r10] s t := by
  unfold TCombCfg.signRead
  refine VG.Proof.X25519.Arm.WP.append (windowIndex_ok K hw.2 gj) fun s₁ ⟨p₁,k₁⟩ => ?_
  obtain hs₁ := hs.of_rest k₁.keep (by decide)
  obtain hf₁ := hf.of_rest k₁.keep
  obtain fa := far_add hd
  obtain ea : State.addr (s₁.gpr .r4+BitVec.ofNat 32 (K.L.bits%4096+K.w-1))=
      VG.Proof.Mont.off base (K.L.bits+K.w*j+K.w-1) := by
    rw [hf₁.ea_reg hs₁ p₁ (by omega_using [hw, hl, fa])]
    congr 1
    omega_using [hw, fa]
  refine wp_ldrb (by omega_using [ho]) ea (hf₁.read (by omega_using [hw, hl])) fun s₂ u₂ =>
    wp_dp (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_
  refine ⟨?_,⟨(k₁.keep.mono (by simp)).trans
      ((u₂.rest (by simp)).trans (u₃.rest (by simp))),u₃.mem.trans (u₂.mem.trans k₁.mem)⟩⟩
  rw [u₃.gpr,dpVal,u₂.gpr,k₁.mem,hb]
  cases b <;> rfl

theorem onesMask_ok (s : State) :
    WP isa (.block [.movw .r10 0xffff,.movt .r10 0xffff]) s fun t =>
      t.gpr .r10=BitVec.allOnes 32 ∧ RegOnly [.r10] s t := by
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => WP.block_nil ?_
  exact ⟨by rw [u₂.gpr,u₁.gpr]; rfl,
    ⟨(u₁.rest (by simp)).trans (u₂.rest (by simp)),u₂.mem.trans u₁.mem⟩⟩

theorem signMask_bit_ok (K : TCombCfg) {s : State} {base : Addr} {size len j k : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : 1≤K.w ∧ K.w<9) (hj : j<K.J) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (start : K.w*(K.J-1)≤K.L.nbits) (cover : K.L.nbits≤K.w*K.J)
    (hd : K.L.bits<8192) (ho : K.L.bits%4096+K.w≤4096)
    (hl : K.L.bits+K.L.nbits≤len) (hk : k<2^K.L.nbits)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hb : ∀ i<K.L.nbits,s.mem (VG.Proof.Mont.off base (K.L.bits+i))=
      if k.testBit i then 1 else 0) :
    WP isa K.signMask s fun t =>
      t.gpr .r10=(if k.testBit (K.w*j+(K.w-1)) then 0 else BitVec.allOnes 32) ∧
      RegOnly [.r4,.r10] s t := by
  obtain bounds := windowBits_bounds hj start cover
  change (if j=K.J-1 then K.topBits else K.w)≤K.w ∧
    K.w*j+(if j=K.J-1 then K.topBits else K.w)≤K.L.nbits ∧
    ((if j=K.J-1 then K.topBits else K.w)=K.w ∨
      K.w*j+(if j=K.J-1 then K.topBits else K.w)=K.L.nbits) at bounds
  have read (u : State) (keep : RegOnly [] s u) (hr : K.w*j+K.w≤K.L.nbits) :
      WP isa (.block K.signRead) u fun t =>
        t.gpr .r10=(if k.testBit (K.w*j+(K.w-1)) then 0 else BitVec.allOnes 32) ∧
        RegOnly [.r4,.r10] s t := by
    refine WP.mono (signRead_ok K (j := j) (b := k.testBit (K.w*j+(K.w-1)))
      (hs.of_rest keep.keep (by decide)) (hf.of_rest keep.keep)
      hw hd ho (by omega_using [hl, hr]) (by rw [keep.keep.gpr .r11 (by decide),gj]) ?_)
      fun t ⟨val,rest⟩ => ⟨val,⟨(keep.keep.mono (by simp)).trans rest.keep,rest.mem.trans keep.mem⟩⟩
    rw [keep.mem,show K.L.bits+K.w*j+K.w-1=K.L.bits+(K.w*j+(K.w-1)) by omega_using [hw]]
    exact hb _ (by omega_using [hw, hr])
  unfold TCombCfg.signMask
  by_cases shortTop : K.topBits<K.w
  · simp only [shortTop,↓reduceIte]
    rw [WP.seq_iff]
    refine WP.mono (lastTest_ok K (by omega_using [hj, hJ]) hJ enc gj) fun u ⟨zero,keep⟩ => ?_
    by_cases last : j=K.J-1
    · apply WP.ite true (by change some u.z=some true; simp only [zero,last,decide_true])
      · intro _
        obtain e : K.w*j+K.topBits=K.L.nbits := by
          rw [last]
          exact Nat.add_sub_of_le start
        obtain high : k.testBit (K.w*j+(K.w-1))=false := by
          rw [Nat.testBit_eq_decide_div_mod_eq,
            Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by omega_using [shortTop, e])))]
          decide
        refine WP.mono (onesMask_ok u) fun t ⟨val,rest⟩ => ?_
        refine ⟨?_,⟨(keep.keep.mono (by simp)).trans (rest.keep.mono (by simp)),rest.mem.trans keep.mem⟩⟩
        rw [val,high]
        rfl
      · intro impossible; cases impossible
    · apply WP.ite false (by change some u.z=some false; simp only [zero,last,decide_false])
      · intro impossible; cases impossible
      · intro _
        apply read u keep
        simpa only [last,↓reduceIte] using bounds.2.1
  · simp only [shortTop,↓reduceIte]
    apply read s ⟨Rest.refl _ _,rfl⟩
    obtain cw : K.w≤(if j=K.J-1 then K.topBits else K.w) := by split <;> omega_arith
    omega_using [bounds, cw]

theorem signMask_ok (K : TCombCfg) {s : State} {base : Addr} {size len j k : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : 1≤K.w ∧ K.w<9) (hj : j<K.J) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (start : K.w*(K.J-1)≤K.L.nbits) (cover : K.L.nbits≤K.w*K.J)
    (hd : K.L.bits<8192) (ho : K.L.bits%4096+K.w≤4096)
    (hl : K.L.bits+K.L.nbits≤len) (hk : k<2^K.L.nbits)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hb : ∀ i<K.L.nbits,s.mem (VG.Proof.Mont.off base (K.L.bits+i))=
      if k.testBit i then 1 else 0) :
    WP isa K.signMask s fun t =>
      t.gpr .r10=(if K.H≤combWin K.w k j then 0 else BitVec.allOnes 32) ∧
      RegOnly [.r4,.r10] s t := by
  refine WP.mono (signMask_bit_ok K hs hf hw hj hJ enc start cover hd ho hl hk gj hb)
    fun t ⟨val,keep⟩ => ⟨?_,keep⟩
  rw [val,testBit_top k K.w j hw.1]
  change (if decide (K.H≤combWin K.w k j) then (0 : BitVec 32) else BitVec.allOnes 32)=_
  by_cases h : K.H≤combWin K.w k j
  · simp only [h,decide_true,↓reduceIte]
  · simp only [h,decide_false,↓reduceIte]
    rfl

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombNegate`, which only this module used -/

section

/-! Reflect the selected affine point with the existing field subtraction and selection. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm.Point
open VG.Proof.X25519.Arm

theorem negate_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} (positive : Prop)
    [Decidable positive] (h : Layout K) (hq : K.qBase=Impl.Weierstrass.Point.qAt K.L.M.n)
    (hs : Scr s base 4096) (hf : Far s base 8192)
    (hm : K.F.m=m) (hn : K.F.k=K.L.M.n) (hM : Mont.ModOk K.L.M.n m)
    (hz : wordsVal s.mem base K.zero K.L.M.n=0)
    (hy : wordsVal s.mem base K.Q.y K.L.M.n<m)
    (hmask : ∀ u, Rest VG.Proof.Weierstrass.Arm.Mont.callClob s u →
      Unch base [(K.neg,8*K.L.M.n),(VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n,64*K.L.M.n)] s.mem u.mem →
      WP isa K.signMask u fun v =>
        v.gpr .r10=(if positive then 0 else BitVec.allOnes 32) ∧ RegOnly [.r4,.r10] u v) :
    WP isa (.seq (VG.Impl.Weierstrass.Arm.Mont.subCall K.F K.neg K.zero K.Q.y K.u)
      (.seq K.signMask (.block (sel (2*K.L.M.n) K.Q.y K.Q.y K.neg)))) s fun t =>
      Rest VG.Proof.Weierstrass.Arm.Mont.callClob s t ∧
      Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],
        wordsVal t.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n) ∧
      wordsVal t.mem base K.Q.x K.L.M.n=wordsVal s.mem base K.Q.x K.L.M.n ∧
      wordsVal t.mem base K.Q.y K.L.M.n=
        (if positive then wordsVal s.mem base K.Q.y K.L.M.n else
          (m-wordsVal s.mem base K.Q.y K.L.M.n)%m) ∧
      wordsVal t.mem base K.Q.z K.L.M.n=wordsVal s.mem base K.Q.z K.L.M.n := by
  obtain hl := lay_nums h.n3 h.n6
  have low := h.low
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at low
  obtain ⟨rx,ry,rz,hzero,hneg⟩ := low
  obtain qfit : K.Q.y+8*K.L.M.n≤VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n := by
    simp only [TCombCfg.Q,ptAt,hq]
    exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
  obtain below : Impl.Weierstrass.Point.oAt K.L.M.n≤VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n := by
    exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
  obtain fm : Mont.ModOk K.F.k K.F.m := by rw [hn,hm]; exact hM
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.Arm.Mont.subCall_ok fm hs hf
    (by rw [hn]; omega_using [hl, hneg]) (by rw [hn]; omega_using [hl, hzero]) (by rw [hn]; exact qfit)
    (by rw [hn,hm,hz]; omega_using [hy]) (by rw [hn,hm]; exact hy)) fun u ⟨ku,yu⟩ => ?_)
  rw [hn,hm,hz,Nat.zero_add] at yu
  obtain ou := Outs.unch ku.mem
  rw [hn] at ou
  refine WP.seq (WP.mono (hmask u (by simpa only [hn] using ku.rest) ou)
    fun v ⟨mask,kv⟩ => ?_)
  obtain hsv := (hs.of_rest ku.rest (by decide)).of_rest kv.keep (by decide)
  obtain msk : v.gpr .r10=if decide (¬positive) then BitVec.allOnes 32 else 0 := by
    rw [mask]
    by_cases hp : positive <;> simp [hp]
  refine WP.mono (selField_ok hsv (decide (¬positive)) msk
    (o := K.Q.y) (a := K.Q.y) (b := K.neg) (n := K.L.M.n)
    (by simp only [TCombCfg.Q,ptAt,hq]; omega_using [hl]) (by simp only [TCombCfg.Q,ptAt,hq]; omega_using [hl])
    (by omega_using [hl, hneg]) (.inl (Nat.le_refl _)) (.inr (by
      obtain b : Impl.Weierstrass.Point.oAt K.L.M.n≤K.Q.y := by
        simp only [TCombCfg.Q,ptAt,hq]
        exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
      omega_using [hneg, b]))) fun t ⟨yt,kt,ot⟩ => ?_
  obtain qold : ∀ x ∈ [K.Q.x,K.Q.y,K.Q.z],
      wordsVal v.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n := by
    intro x hx
    rw [kv.mem]
    apply ou.wordsVal
    · have geom : Impl.Weierstrass.Point.oAt K.L.M.n≤x ∧
          x+8*K.L.M.n≤VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n := by
        simp only [TCombCfg.Q,ptAt,hq] at hx
        exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      exact ⟨.inr (by omega_using [hneg, geom]),.inl geom.2⟩
    · have geom : x+8*K.L.M.n≤4096 := by
        simp only [TCombCfg.Q,ptAt,hq] at hx
        exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
      omega_using [geom]
  refine ⟨ku.rest.trans ((kv.keep.mono (by simp [VG.Proof.Weierstrass.Arm.Mont.callClob,VG.Proof.Mont.Arm.clob])).trans
    (kt.mono (by simp [VG.Proof.Weierstrass.Arm.Mont.callClob,VG.Proof.Mont.Arm.clob]))),?_,?_,?_,?_,?_⟩
  · have ov : Unch base [(K.neg,8*K.L.M.n),(VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n,64*K.L.M.n)] s.mem v.mem := by
      rw [kv.mem]; exact ou
    apply (ov.trans ot.unch).cover
    intro w hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with (rfl|rfl)|rfl
    · exact ⟨_,by simp [loopWrites],Nat.le_refl _,Nat.le_refl _⟩
    · refine ⟨(Impl.Weierstrass.Point.ownAt K.L.M.n,4096-Impl.Weierstrass.Point.ownAt K.L.M.n),by simp [loopWrites],?_⟩
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
    · refine ⟨(Impl.Weierstrass.Point.oAt K.L.M.n,72*K.L.M.n),by simp [loopWrites],?_⟩
      simp only [TCombCfg.Q,ptAt,hq]
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
  · intro x hx
    obtain lowx := h.low x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl <;> simp)
    obtain negx := h.negApart x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl <;> simp)
    obtain qy : Impl.Weierstrass.Point.oAt K.L.M.n≤K.Q.y := by
      simp only [TCombCfg.Q,ptAt,hq]
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
    rw [ot.wordsVal (.inl (Nat.le_trans lowx qy)) (by omega_using [hl, lowx]),kv.mem]
    apply ou.wordsVal
    · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      exact ⟨negx.symm,.inl (Nat.le_trans lowx below)⟩
    · omega_using [hl, lowx]
  · rw [ot.wordsVal (by simp only [TCombCfg.Q,ptAt,Impl.Weierstrass.Point.elemBytes,hq]; omega_using [])
      (by simp only [TCombCfg.Q,ptAt,Impl.Weierstrass.Point.elemBytes,hq]; omega_using [hl]),qold _ (by simp)]
  · rw [yt,kv.mem,yu]
    obtain qo := qold K.Q.y (by simp)
    rw [kv.mem] at qo
    rw [qo]
    by_cases hp : positive <;> simp [hp]
  · rw [ot.wordsVal (by simp only [TCombCfg.Q,ptAt,Impl.Weierstrass.Point.elemBytes,hq]; omega_using [])
      (by simp only [TCombCfg.Q,ptAt,Impl.Weierstrass.Point.elemBytes,hq]; omega_using [hl]),qold _ (by simp)]

end VG.Proof.Weierstrass.Arm.TComb

end

end


/-! Decode, select, and reflect one table entry while keeping the accumulator. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm
open VG.Proof.Weierstrass.Arm.Point
open Spec.Weierstrass

theorem entry_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) {s : State} {base T : Addr} {k j : Nat}
    (i : CurveInputs K C tbl base T k s) (hj : j<K.J) (hk : k<2^K.L.nbits)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hd : Region.Disjoint ⟨T,8*(tableWords K C tbl).length⟩ ⟨base,4096⟩) :
    WP isa K.entry s fun t =>
      Rest VG.Proof.Weierstrass.Arm.Mont.callClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],wordsVal t.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n) ∧
      (∀ x ∈ [K.Q.x,K.Q.y,K.Q.z],wordsVal t.mem base x K.L.M.n<C.p) ∧
      Rep C (tmv C K.L.M.n base t K.Q.x) (tmv C K.L.M.n base t K.Q.y)
        (tmv C K.L.M.n base t K.Q.z) (signedPtW C K.w k j) := by
  unfold TCombCfg.entry
  obtain hp : 0<C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  obtain hfit : C.p≤2^(64*K.L.M.n) := Nat.le_of_lt h.modulus.m_lt
  have lo := h.layout.low
  obtain hl := lay_nums h.layout.n3 h.layout.n6
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at lo
  obtain ⟨rx,ry,rz,zlo,nlo⟩ := lo
  obtain qx : K.Q.x=Impl.Weierstrass.Point.qAt K.L.M.n := by simp only [TCombCfg.Q,ptAt,h.qBase]
  refine WP.seq (WP.mono_syms (digit_ok K i.scr i.far h.w9 hj (by have := h.J32; omega_using [this])
    h.encLast h.startBits h.coverBits h.bitsFit h.windowFit h.bitsHigh hk gj i.bits)
    fun u ⟨gu,ku⟩ syu => ?_)
  obtain iu : CurveInputs K C tbl base T k u := i.keep h.layout h.bitsLow h.bitsHigh hd ku.keep
    (by decide) (by rw [ku.mem]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (selectTable_ok K iu.scr
    (by simp only [TCombCfg.Q,ptAt,h.qBase]; omega_using [hl]) (by omega_using [hl, zlo])
    (.inl (by rw [qx]; exact Nat.le_trans zlo (oAt_le_qAt _))) (Nat.lt_of_lt_of_le h.one_lt hfit) iu.zero
    (by have := h.layout.n3; omega_using [this]) h.halfBound (h.magnitude k j) gu
    (by rw [ku.keep.gpr .r11 (by decide),gj]) iu.table iu.symbol h.tables.len h.tables.lenH hj hp hfit hd
    h.encRow h.encEntry h.encH) fun v ⟨xv,yv,zv,kv,ov⟩ syv => ?_)
  obtain ouv := ov.unch.cover (h.layout.q_cover h.qBase)
  obtain iv : CurveInputs K C tbl base T k v := iu.keep h.layout h.bitsLow h.bitsHigh hd kv
    (by decide) ouv syv
  obtain ylt : wordsVal v.mem base K.Q.y K.L.M.n<C.p := by rw [yv]; split <;> first | exact h.one_lt | exact Nat.mod_lt _ hp
  obtain oldR : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],wordsVal v.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n := by
    intro x hx
    obtain lowx := h.layout.low x (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp)
    rw [ov.wordsVal (.inl (by rw [qx]; exact Nat.le_trans lowx (oAt_le_qAt _))) (by have := i.scr.nowrap; omega_using [hl, lowx]),ku.mem]
  obtain mask : ∀ a, Rest VG.Proof.Weierstrass.Arm.Mont.callClob v a →
      Unch base [(K.neg,8*K.L.M.n),(VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n,64*K.L.M.n)] v.mem a.mem →
      WP isa K.signMask a fun b =>
        b.gpr .r10=(if K.H≤combWin K.w k j then 0 else BitVec.allOnes 32) ∧ RegOnly [.r4,.r10] a b := by
    intro a keep mem
    apply signMask_ok K (iv.scr.of_rest keep (by decide)) (iv.far.of_rest keep)
      ⟨h.w1,h.w9⟩ hj (by have := h.J32; omega_using [this]) h.encLast h.startBits h.coverBits h.bitsFit
      h.windowFit h.bitsHigh hk
      (by rw [keep.gpr .r11 (by decide),kv.gpr .r11 (by decide),ku.keep.gpr .r11 (by decide),gj])
    intro b hb
    obtain mem' := (mem.cover h.layout.sub_cover).cover h.layout.loop_cover
    rw [mem'.byte (fun w hw => .inr (by have := h.layout.bounded w hw; have := h.bitsLow; omega_arith))
      (by have := h.bitsHigh; omega_using [hb, this]),iv.bits b hb]
  refine WP.mono (negate_ok K (K.H≤combWin K.w k j) h.layout h.qBase iv.scr iv.far
    h.fieldM h.fieldK h.modulus iv.zero ylt mask) fun t ⟨kt,ot,rt,xt,yt,zt⟩ => ?_
  obtain ku' : Rest VG.Proof.Weierstrass.Arm.Mont.callClob s u := ku.keep.mono (by
    simp [VG.Proof.Weierstrass.Arm.Mont.callClob,VG.Proof.Mont.Arm.clob])
  obtain kv' : Rest VG.Proof.Weierstrass.Arm.Mont.callClob u v := kv.mono (by
    simp [VG.Proof.Weierstrass.Arm.Mont.callClob,VG.Proof.Mont.Arm.clob])
  refine ⟨ku'.trans (kv'.trans kt),?_,fun x hx => (rt x hx).trans (oldR x hx),?_,?_⟩
  · have ou : Unch base (loopWrites K) s.mem u.mem := by rw [ku.mem]; exact Unch.refl _ _ _
    exact (ou.trans (ouv.trans ot)).cover fun w hw => ⟨w,by
      simpa only [List.mem_append,or_self] using hw,Nat.le_refl _,Nat.le_refl _⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    rw [xt,yt,zt,xv,zv]
    refine ⟨?_,?_,?_⟩
    · split <;> first | exact hp | exact Nat.mod_lt _ hp
    · split <;> first | exact ylt | exact Nat.mod_lt _ hp
    · split <;> first | exact hp | exact h.one_lt
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [xt,yt,zt]
    exact combSigned_rep hC h.tables h.unit h.one hj h.w1 xv yv zv ylt

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombAdd`, which only this module used -/

section

/-! Copy an accumulator into the existing point-add routine and copy its result back. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm.Point
open VG.Proof.X25519.Arm

/-- Reuse the point-call implementation for the comb's single addition per digit. -/
theorem add_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} [NeZero m]
    (h : Layout K) (hq : K.qBase=Impl.Weierstrass.Point.qAt K.L.M.n)
    (hs : Scr s base 4096) (hf : Far s base 8192)
    (hm : K.F.m=m) (hn : K.F.k=K.L.M.n) (hM : Mont.ModOk K.L.M.n m)
    (hlt : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.Q.x,K.Q.y,K.Q.z,
      Impl.Weierstrass.Point.aAt K.L.M.n,Impl.Weierstrass.Point.b3At K.L.M.n],
      wordsVal s.mem base x K.L.M.n<m) :
    WP isa K.add s fun t =>
      Rest [.r4,.r10,.r0,.r1,.r2,.r3] s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z], wordsVal t.mem base x K.L.M.n<m) ∧
      (toM m (2^(64*K.L.M.n)) (wordsVal t.mem base K.L.R.x K.L.M.n),
       toM m (2^(64*K.L.M.n)) (wordsVal t.mem base K.L.R.y K.L.M.n),
       toM m (2^(64*K.L.M.n)) (wordsVal t.mem base K.L.R.z K.L.M.n))=
        rcbAdd (Eb K.L.M.n m false s.mem base 9) (Eb K.L.M.n m false s.mem base 10)
          (toM m (2^(64*K.L.M.n)) (wordsVal s.mem base K.L.R.x K.L.M.n))
          (toM m (2^(64*K.L.M.n)) (wordsVal s.mem base K.L.R.y K.L.M.n))
          (toM m (2^(64*K.L.M.n)) (wordsVal s.mem base K.L.R.z K.L.M.n))
          (Eb K.L.M.n m false s.mem base 6) (Eb K.L.M.n m false s.mem base 7)
          (Eb K.L.M.n m false s.mem base 8) := by
  unfold TCombCfg.add
  obtain hl := lay_nums h.n3 h.n6
  have low := h.low
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at low hlt
  obtain ⟨rx,ry,rz,hzero,hneg⟩ := low
  obtain ⟨lx,ly,lz,lqx,lqy,lqz,la,lb⟩ := hlt
  obtain cp := copyPt_conds (a := K.L.R) h.n3 h.n6 rfl (.inl rfl)
    (Nat.le_trans rx (oAt_le_pAt _)) (Nat.le_trans ry (oAt_le_pAt _)) (Nat.le_trans rz (oAt_le_pAt _))
  refine WP.seq (WP.mono (copyPt_ok hs cp.1 cp.2.1 cp.2.2) fun u ⟨px,py,pz,keep,outs⟩ => ?_)
  simp only [TCombCfg.P,ptAt] at px py pz outs
  obtain hsu := hs.of_rest keep (by decide)
  obtain hfu := hf.of_rest keep
  obtain other : ∀ x ∈ [K.Q.x,K.Q.y,K.Q.z,Impl.Weierstrass.Point.aAt K.L.M.n,
      Impl.Weierstrass.Point.b3At K.L.M.n],
      wordsVal u.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n := by
    intro x hx
    apply (Outs.unch outs).wordsVal
    · simp only [TCombCfg.Q,ptAt,hq] at hx
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
    · have := hs.nowrap
      obtain bx : x+8*K.L.M.n≤4096 := by
        simp only [TCombCfg.Q,ptAt,hq] at hx
        exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
      omega_arith
  obtain hltu : ∀ x ∈ rIds,wordsVal u.mem base (enc K.L.M.n false x) K.L.M.n<m := by
    apply rIds_lt_of false
    simp only [Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [px]; exact lx
    · rw [py]; exact ly
    · rw [pz]; exact lz
    · have lt := lqx
      rw [← other K.Q.x (by simp)] at lt
      simp only [TCombCfg.Q,ptAt,hq] at lt
      exact lt
    · have lt := lqy
      rw [← other K.Q.y (by simp)] at lt
      simp only [TCombCfg.Q,ptAt,hq] at lt
      exact lt
    · have lt := lqz
      rw [← other K.Q.z (by simp)] at lt
      simp only [TCombCfg.Q,ptAt,hq] at lt
      exact lt
    · rw [other _ (by simp)]; exact la
    · rw [other _ (by simp)]; exact lb
  refine WP.seq (WP.mono (ptCall_ok hm hn hM (ModOk.odd hM) h.n6 false hsu hfu hltu)
    fun v ⟨kv,ov,lv,eqv⟩ => ?_)
  obtain hsv := hsu.of_rest kv (by decide)
  obtain backIn : ∀ d ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.O.x,K.O.y,K.O.z],d+8*K.L.M.n≤4096 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    refine ⟨by omega_arith,by omega_arith,by omega_arith,?_⟩
    simp only [TCombCfg.O,ptAt]
    exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
  obtain backApart : ∀ d ∈ [K.L.R.x,K.L.R.y,K.L.R.z],∀ e ∈ [K.O.x,K.O.y,K.O.z],
      d+8*K.L.M.n≤e ∨ e+8*K.L.M.n≤d := by
    intro d hd e he
    obtain dl : d+8*K.L.M.n≤Impl.Weierstrass.Point.oAt K.L.M.n := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl <;> with_reducible assumption
    obtain el : Impl.Weierstrass.Point.oAt K.L.M.n≤e := by
      simp only [TCombCfg.O,ptAt] at he
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) e he
    exact .inl (Nat.le_trans dl el)
  refine WP.mono (copyPt_ok hsv backIn h.apart backApart) fun t ⟨tx,ty,tz,kt,ot⟩ => ?_
  refine ⟨(keep.mono (by simp)).trans ((kv.mono (by simp)).trans (kt.mono (by simp))),?_,?_,?_⟩
  · apply ((Outs.unch outs).trans ((Outs.unch ov).trans (Outs.unch ot))).cover
    intro w hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with (rfl|rfl|rfl)|((rfl|rfl)|(rfl|rfl|rfl))
    all_goals simp only [loopWrites,List.mem_cons,List.not_mem_nil,or_false]
    all_goals first
      | exact ⟨_,Or.inl rfl,Nat.le_refl _,Nat.le_refl _⟩
      | exact ⟨_,Or.inr (Or.inl rfl),Nat.le_refl _,Nat.le_refl _⟩
      | exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),Nat.le_refl _,Nat.le_refl _⟩
      | exact ⟨(Impl.Weierstrass.Point.oAt K.L.M.n,72*K.L.M.n),
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
          lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)⟩
      | exact ⟨(Impl.Weierstrass.Point.ownAt K.L.M.n,4096-Impl.Weierstrass.Point.ownAt K.L.M.n),
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),Nat.le_refl _,Nat.le_refl _⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    rw [tx,ty,tz]
    simpa only [TCombCfg.O,ptAt,enc_0,enc_1,enc_2] using And.intro (lv 0 (by decide)) (And.intro (lv 1 (by decide)) (lv 2 (by decide)))
  · rw [tx,ty,tz]
    have ev := eqv
    simp only [Eb,enc_0,enc_1,enc_2] at ev
    simp only [TCombCfg.O,ptAt]
    rw [ev]
    simp only [ptVal,Eb,enc_3,enc_4,enc_5,enc_6,enc_7,enc_8,enc_9,enc_10,Bool.false_eq_true,↓reduceIte]
    rw [px,py,pz]
    obtain oa := other (Impl.Weierstrass.Point.aAt K.L.M.n) (by simp)
    obtain ob := other (Impl.Weierstrass.Point.b3At K.L.M.n) (by simp)
    obtain ox := other K.Q.x (by simp)
    obtain oy := other K.Q.y (by simp)
    obtain oz := other K.Q.z (by simp)
    simp only [TCombCfg.Q,ptAt,hq] at ox oy oz
    rw [oa,ob,ox,oy,oz]

end VG.Proof.Weierstrass.Arm.TComb

end

end


/-! One signed comb digit advances the shared scalar-multiplication invariant. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm
open VG.Proof.Weierstrass.Arm.Point
open Spec.Weierstrass

structure Acc (K : TCombCfg) (C : Curve) (base : Addr) (k j : Nat) (s : State) : Prop where
  lt : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z], wordsVal s.mem base x K.L.M.n<C.p
  rep : Rep C (tmv C K.L.M.n base s K.L.R.x) (tmv C K.L.M.n base s K.L.R.y)
    (tmv C K.L.M.n base s K.L.R.z) (mul (combEW K.w k K.J j) (G C))

theorem step_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) (hG : onCurve C (G C)=true)
    {s : State} {base T : Addr} {k j : Nat}
    (i : CurveInputs K C tbl base T k s) (acc : Acc K C base k j s)
    (hj : 1≤j) (hJ : j≤K.J) (hk : k<2^K.L.nbits) (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hd : Region.Disjoint ⟨T,8*(tableWords K C tbl).length⟩ ⟨base,4096⟩) :
    WP isa K.step s fun t =>
      Rest powClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      CurveInputs K C tbl base T k t ∧ Acc K C base k (j-1) t ∧
      t.gpr .r11=BitVec.ofNat 32 (j-1) ∧ t.z=decide (j-1=0) := by
  apply WP.of_syms
  unfold TCombCfg.step
  obtain dec : WP isa (.block [decCounter]) s fun u =>
      u.gpr .r11=BitVec.ofNat 32 (j-1) ∧ RegOnly [.r11] s u :=
    wp_decCounter hj gj fun u up => WP.block_nil ⟨up.gpr,⟨up.rest (by simp),up.mem⟩⟩
  refine WP.seq (WP.mono_syms dec fun u ⟨gu,ku⟩ syu => ?_)
  obtain iu : CurveInputs K C tbl base T k u := i.keep h.layout h.bitsLow h.bitsHigh hd ku.keep
    (by decide) (by rw [ku.mem]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (entry_ok K h hC iu (by omega_using [hj, hJ]) hk gu hd)
    fun v ⟨kv,ov,rv,lv,pv⟩ syv => ?_)
  obtain iv : CurveInputs K C tbl base T k v := iu.keep h.layout h.bitsLow h.bitsHigh hd kv (by decide) ov syv
  obtain rlt : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],wordsVal v.mem base x K.L.M.n<C.p := by
    intro x hx
    rw [rv x hx,ku.mem]
    exact acc.lt x hx
  obtain rrep : Rep C (tmv C K.L.M.n base v K.L.R.x) (tmv C K.L.M.n base v K.L.R.y)
      (tmv C K.L.M.n base v K.L.R.z) (mul (combEW K.w k K.J j) (G C)) := by
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [rv _ (by simp),rv _ (by simp),rv _ (by simp),ku.mem]
    exact acc.rep
  obtain hlt : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.Q.x,K.Q.y,K.Q.z,
      Impl.Weierstrass.Point.aAt K.L.M.n,Impl.Weierstrass.Point.b3At K.L.M.n],
      wordsVal v.mem base x K.L.M.n<C.p := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨rlt _ (by simp),rlt _ (by simp),rlt _ (by simp),lv _ (by simp),lv _ (by simp),lv _ (by simp),
      iv.coeffA ▸ Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p)),
      iv.coeffB ▸ Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))⟩
  refine WP.seq (WP.mono (add_ok K h.layout h.qBase iv.scr iv.far h.fieldM h.fieldK h.modulus hlt)
    fun a ⟨ka,oa,la,ea⟩ => ?_)
  obtain ga : a.gpr .r11=BitVec.ofNat 32 (j-1) := by
    rw [ka.gpr .r11 (by decide),kv.gpr .r11 (by decide),gu]
  refine wp_testCounter (by have := h.J32; omega_using [hJ, this]) ga fun t ft zt => WP.block_nil (fun syt => ?_)
  obtain keep : Rest powClob s t := (ku.keep.mono (by simp [powClob])).trans
    ((kv.mono (by simp [VG.Proof.Weierstrass.Arm.Mont.callClob,powClob,VG.Proof.Mont.Arm.clob])).trans
      ((ka.mono (by simp [powClob,VG.Proof.Mont.Arm.clob])).trans (ft.rest _)))
  obtain unch : Unch base (loopWrites K) s.mem t.mem := by
    rw [ft.mem]
    obtain ou : Unch base (loopWrites K) s.mem u.mem := by rw [ku.mem]; exact Unch.refl _ _ _
    exact (ou.trans (ov.trans oa)).cover fun w hw => ⟨w,by
      simpa only [List.mem_append,or_self] using hw,Nat.le_refl _,Nat.le_refl _⟩
  refine ⟨keep,unch,i.keep h.layout h.bitsLow h.bitsHigh hd keep (by decide) unch syt,
    ⟨by rw [ft.mem]; exact la,?_⟩,by rw [ft.gpr,ga],zt⟩
  obtain pa : Rep C (tmv C K.L.M.n base a K.L.R.x) (tmv C K.L.M.n base a K.L.R.y)
      (tmv C K.L.M.n base a K.L.R.z)
      (Spec.Weierstrass.add (mul (combEW K.w k K.J j) (G C)) (signedPtW C K.w k (j-1))) := by
    apply hC.add (hC.onCurve_mul hG _) (by
      unfold signedPtW combPtW
      split
      · exact hC.onCurve_mul hG _
      · exact onCurve_negPt (hC.onCurve_mul hG _)) rrep pv
    change _=(toM _ _ _,toM _ _ _,toM _ _ _)
    rw [ea]
    simp only [Eb,enc_9,enc_10]
    rw [iv.coeffA,iv.coeffB,toM_mont h.unit,toM_mont h.unit]
    simp only [rcbAddC,tmv,TCombCfg.Q,ptAt,h.qBase,enc_6,enc_7,enc_8,Bool.false_eq_true,↓reduceIte]
  obtain eqj : j-1+1=j := by omega_using [hj]
  obtain sum := combW_add hC hG (w := K.w) (k := k) (j := j-1) (J := K.J) (by omega_using [hj, hJ])
  change Spec.Weierstrass.add _ (signedPtW C K.w k (j-1))=_ at sum
  rw [eqj] at sum
  rw [sum] at pa
  simpa only [tmv,ft.mem] using pa

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombStart`, which only this module used -/

section

/-! Initialize the comb with its checked affine offset point. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm.Point
open VG.Proof.X25519.Arm

theorem start_ok (K : TCombCfg) {s : State} {base : Addr}
    (h : Layout K) (hs : Scr s base 4096)
    (hx : K.start.1<2^(64*K.L.M.n)) (hy : K.start.2<2^(64*K.L.M.n))
    (hz : K.one<2^(64*K.L.M.n)) (encJ : encodable (BitVec.ofNat 32 K.J)=true) :
    WP isa (.block (ladderSetup K.L ++
      setConst K.L.M.n K.L.R.x K.start.1 ++ setConst K.L.M.n K.L.R.y K.start.2 ++
      setConst K.L.M.n K.L.R.z K.one ++ ([.mov .r11 (.imm (BitVec.ofNat 32 K.J))] : List Instr))) s fun t =>
      Rest [.r4,.r11] s t ∧ Unch base (writes K) s.mem t.mem ∧
      CpOk K.L base t.mem s.mem ∧ t.gpr .r11=BitVec.ofNat 32 K.J ∧
      wordsVal t.mem base K.L.R.x K.L.M.n=K.start.1 ∧
      wordsVal t.mem base K.L.R.y K.L.M.n=K.start.2 ∧
      wordsVal t.mem base K.L.R.z K.L.M.n=K.one := by
  obtain hl := lay_nums h.n3 h.n6
  have low := h.low
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at low
  obtain ⟨rx,ry,rz,hzero,hneg⟩ := low
  obtain ⟨rxy,rxz,ryz⟩ := h.apart
  have nowrap := hs.nowrap
  rw [List.append_assoc,List.append_assoc,List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (ladderSetup_ok hs h.n3 h.n6 h.point)
    fun u ⟨ku,ou,cp⟩ => ?_
  obtain hsu := hs.of_rest ku (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hsu (by omega_using [hl, rx]) hx) fun v ⟨xv,kv,ov⟩ => ?_
  obtain hsv := hsu.of_rest kv (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hsv (by omega_using [hl, ry]) hy) fun a ⟨ya,ka,oa⟩ => ?_
  obtain hsa := hsv.of_rest ka (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hsa (by omega_using [hl, rz]) hz) fun b ⟨zb,kb,ob⟩ => ?_
  refine wp_mov (op2_imm encJ) fun t ut => WP.block_nil ?_
  obtain ub : Unch base [(K.L.R.x,8*K.L.M.n),(K.L.R.y,8*K.L.M.n),(K.L.R.z,8*K.L.M.n)] u.mem t.mem := by
    rw [ut.mem]
    exact ov.unch.trans (oa.unch.trans ob.unch)
  refine ⟨(ku.mono (by simp)).trans ((kv.mono (by simp)).trans
      ((ka.mono (by simp)).trans ((kb.mono (by simp)).trans (ut.rest (by simp))))),?_,?_,ut.gpr,?_,?_,?_⟩
  · apply (ou.trans ub).mono
    intro w hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|(rfl|rfl|rfl) <;> simp [writes]
  · apply cp.keep h.n3 h.n6 ub
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl <;> exact .inl (Nat.le_trans (by assumption) (oAt_le_qAt _))
  · rw [ut.mem,ob.wordsVal (by omega_using [rxz]) (by omega_using [hl, rx]),oa.wordsVal (by omega_using [rxy]) (by omega_using [hl, rx]),xv]
  · rw [ut.mem,ob.wordsVal (by omega_using [ryz]) (by omega_using [hl, ry]),ya]
  · rw [ut.mem,zb]

end VG.Proof.Weierstrass.Arm.TComb

end

end


/-! Correctness of the complete ARM signed-comb scalar multiplication. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm
open VG.Proof.Weierstrass.Arm.Point
open Spec.Weierstrass

theorem comb_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) (hG : onCurve C (G C)=true)
    {s : State} {base T : Addr} {k : Nat}
    (hs : Scr s base 4096) (hf : Far s base 8192)
    (ht : TableMem s T (tableWords K C tbl)) (sym : State.addr (s.syms K.tsym)=T)
    (hd : Region.Disjoint ⟨T,8*(tableWords K C tbl).length⟩ ⟨base,4096⟩)
    (hk : k<2^K.L.nbits) (zero : wordsVal s.mem base K.zero K.L.M.n=0)
    (bits : ∀ i<K.L.nbits,s.mem (off base (K.L.bits+i))=if k.testBit i then 1 else 0)
    (coeffA : wordsVal s.mem base K.L.S.a K.L.M.n=C.a*2^(64*K.L.M.n)%C.p)
    (coeffB : wordsVal s.mem base K.L.S.b3 K.L.M.n=(3*C.b)*2^(64*K.L.M.n)%C.p) :
    WP isa K.comb s fun t =>
      Rest powClob s t ∧ Unch base (writes K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],wordsVal t.mem base x K.L.M.n<C.p) ∧
      Rep C (tmv C K.L.M.n base t K.L.R.x) (tmv C K.L.M.n base t K.L.R.y)
        (tmv C K.L.M.n base t K.L.R.z) (mul k (G C)) := by
  obtain hp : 0<C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have fit := h.modulus.m_lt
  obtain sx : K.start.1<C.p := by rw [h.startX]; exact Nat.mod_lt _ hp
  obtain sy : K.start.2<C.p := by rw [h.startY]; exact Nat.mod_lt _ hp
  unfold TCombCfg.comb
  refine WP.seq (WP.mono_syms (start_ok K h.layout hs (Nat.lt_trans sx fit) (Nat.lt_trans sy fit)
    (Nat.lt_trans h.one_lt fit) h.encJ) fun u ⟨ku,ou,cp,gu,xu,yu,zu⟩ syu => ?_)
  have frame : Frame [⟨base,4096⟩] s.mem u.mem := outside_frame
    (ou.outside (o := 0) (n := 4096) h.layout.bounded) (Nat.le_refl _)
  obtain low := h.layout.low K.zero (by simp)
  obtain hl := lay_nums h.layout.n3 h.layout.n6
  obtain iu : CurveInputs K C tbl base T k u := by
    refine ⟨hs.of_rest ku (by decide),hf.of_rest ku,
      ht.of_frame (by rw [ku.rd,ku.wr]) frame (by simpa only [List.mem_singleton,forall_eq] using hd),
      by rw [syu]; exact sym,?_,?_,?_,?_⟩
    · rw [ou.wordsVal (by
        intro r hr
        simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl|rfl
        · exact h.layout.zeroApart _ (by simp)
        · exact h.layout.zeroApart _ (by simp)
        · exact h.layout.zeroApart _ (by simp)
        · exact (h.layout.negApart K.zero (by simp)).symm
        · exact .inl low) (by omega_using [low, hl]),zero]
    · intro j hj
      rw [ou.byte (fun w hw => .inr (by have := h.layout.bounded w hw; have := h.bitsLow; omega_arith))
        (by have := h.bitsHigh; omega_using [hj, this]),bits j hj]
    · exact cp.2.2.2.1.trans coeffA
    · exact cp.2.2.2.2.trans coeffB
  obtain au : Acc K C base k K.J u := by
    refine ⟨?_,?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      rw [xu,yu,zu]
      exact ⟨sx,sy,h.one_lt⟩
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [xu,yu,zu,h.startX,h.startY,toM_mont h.unit,toM_mont h.unit,h.one,combEW_top,h.tables.start]
      exact rep_affine' hC _ _
  let Inv := fun j t => CurveInputs K C tbl base T k t ∧ Acc K C base k j t ∧
    t.gpr .r11=BitVec.ofNat 32 j ∧ Rest powClob s t ∧ Unch base (writes K) s.mem t.mem
  apply countLoop_ok (Inv := Inv)
    (fun j t hj hJ hi => ?_) (fun t hi => ?_) h.J1
    ⟨iu,au,gu,ku.mono (by simp [powClob,VG.Proof.Mont.Arm.clob]),ou⟩
  · obtain ⟨it,accT,gt,kt,ot⟩ := hi
    refine WP.mono (step_ok K h hC hG it accT hj hJ hk gt hd) fun v ⟨kv,ov,iv,av,gv,zv⟩ => ?_
    refine ⟨⟨iv,av,gv,kt.trans kv,?_⟩,zv⟩
    exact (ot.trans (ov.cover h.layout.loop_cover)).cover fun w hw => ⟨w,by
      simpa only [List.mem_append,or_self] using hw,Nat.le_refl _,Nat.le_refl _⟩
  · obtain ⟨_,accT,_,kt,ot⟩ := hi
    refine ⟨kt,ot,accT.lt,?_⟩
    obtain hk' : k<2^(K.w*K.J) := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) h.coverBits)
    simpa only [combEW_zero hk'] using accT.rep

end VG.Proof.Weierstrass.Arm.TComb
