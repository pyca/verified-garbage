module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombBody
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan

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
  · have he : (1≤a ∧ a<m) ↔ (1≤a ∧ a<m+1) := by omega
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
        rw [← Nat.mul_succ]; congr 1; omega
      _ ≤ 16*K.L.M.n*K.H := Nat.mul_le_mul_left _ mh
  have hop : 16*K.L.M.n*(m-1)<2^32 := by omega
  have ptrfit : (s₀.gpr .r8).toNat+16*K.L.M.n*(m-1)<2^32 := by
    have hnX : (s₀.gpr .r8).toNat=X.toNat := by rw [← hX,addr_toNat]
    omega
  have hx : State.addr (s.gpr .r8)=off X (16*K.L.M.n*(m-1)) := by
    rw [I.ptr,VG.Arm.addr_add ptrfit,hX]
  have efit : (off X (16*K.L.M.n*(m-1))).toNat+16*K.L.M.n ≤ 2^32 := by
    rw [off,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 16*K.L.M.n*(m-1)<2^64 by omega),
      Nat.mod_eq_of_lt (show X.toNat+16*K.L.M.n*(m-1)<2^64 by omega)]
    omega
  have er : InRegions (s.rd ++ s.wr) (off X (16*K.L.M.n*(m-1))) (16*K.L.M.n) := by
    rw [I.keep.rd,I.keep.wr]
    exact CallLay.inRegions_sub hr hmul (by omega)
  have ed : Region.Disjoint ⟨off X (16*K.L.M.n*(m-1)),16*K.L.M.n⟩ ⟨base,size⟩ :=
    hd.sub_left (Offset.sub_base X hmul)
  refine WP.mono (selectBody_ok K (a := a) (m := m) hs hx ho hi efit er ed (by omega) (by omega)
    (by rw [I.keep.gpr .r9 (by decide),ga]) I.index es eh (by omega) (by omega))
    fun t ⟨v,k,O,p,index,z⟩ => ⟨?_,z⟩
  refine ⟨?_,index,I.keep.trans k,I.unch.trans O,?_⟩
  · have he : 16*K.L.M.n*(m-1)+16*K.L.M.n=16*K.L.M.n*m := by
      rw [← Nat.mul_succ]; congr 1; omega
    rw [p,I.ptr,BitVec.add_assoc,← BitVec.ofNat_add,he,show m+1-1=m by omega]
  · intro i hii
    have hoff : 16*K.L.M.n*(m-1)+4*i+4 ≤ 16*K.L.M.n*K.H := by omega
    have src : w32 s.mem (off X (16*K.L.M.n*(m-1))) (4*i) =
        w32 s₀.mem X (16*K.L.M.n*(m-1)+4*i) := by
      unfold w32 off
      rw [Offset.add_add]
      apply congrArg BitVec.toNat
      exact (outside_frame (size := size) I.unch ho).readW
        (r := ⟨X,16*K.L.M.n*K.H⟩)
        (Offset.contains_base (d := 16*K.L.M.n*(m-1)+4*i) (n := 4) X hoff (by omega))
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
  · have m1 : 1≤K.H+1-j := by omega
    have mH : K.H+1-j≤K.H := by omega
    refine WP.mono (scan_step K hs₀ hX ho hi fit hr hd hn hH ha ga es eh m1 mH I)
      fun t ⟨I',z⟩ => ?_
    by_cases je : j=1
    · have me : K.H+1-j+1=K.H+1 := by omega
      refine .inl ⟨?_,me ▸ I'⟩
      rw [VG.Proof.X25519.Arm.eval_ne,z,decide_eq_true me]
      rfl
    · have me : ¬K.H+1-j+1=K.H+1 := by omega
      refine .inr ⟨?_,j-1,by omega,by omega,by omega,?_⟩
      · rw [VG.Proof.X25519.Arm.eval_ne,z,decide_eq_false me]
        rfl
      · have e : K.H+1-(j-1)=K.H+1-j+1 := by omega
        rw [e]; exact I'
  · refine ⟨hHp,Nat.le_refl _,?_⟩
    have e : K.H+1-K.H=1 := by omega
    rw [e]
    refine ⟨?_,?_,Rest.refl _ _,Outside.refl _ _ _ _,?_⟩
    · simp only [Nat.sub_self,Nat.mul_zero,BitVec.add_zero]
    · exact gm
    · intro i hi'
      rw [hz i hi']
      have h : ¬(1≤a ∧ a<1) := by omega
      simp only [h,↓reduceIte]

end VG.Proof.Weierstrass.Arm.TComb
