module
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNaf9
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafTiming

/-! The width-nine recoder's constant time. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (read_x)

structure FastPrep9Checks (K : WinCfg) (src : Nat) : Prop where
  init : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block (Impl.Weierstrass.AArch64.FastNaf.init K src 9 ++ Impl.Weierstrass.AArch64.FastNaf.clear9 K))
  step : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs fastPrepPublic))
    Impl.Weierstrass.AArch64.FastNaf.step9

structure FastPrep9Pair (base : Addr) (size bits k j : Nat) (s t : State) : Prop where
  left : FastPrep9State base size bits k j s
  right : FastPrep9State base size bits k j t
  sp : s.sp=t.sp

theorem FastPrep9Pair.public {base : Addr} {size bits k j : Nat} {s t : State}
    (h : FastPrep9Pair base size bits k j s t) : AArch64.Taint.Agree (Taint.ofRegs fastPrepPublic) s t := by
  have hv := nafVal5_inj (h.left.value.trans h.right.value.symm)
  refine ⟨h.sp,?_⟩
  intro r hr
  simp only [Taint.mem_ofRegs,fastPrepPublic,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.left.scr.x0.trans h.right.scr.x0.symm
  · exact hv.1
  · exact hv.2.1
  · exact hv.2.2.1
  · exact hv.2.2.2.1
  · exact hv.2.2.2.2
  · exact h.left.mask.trans h.right.mask.symm
  · exact h.left.sign.trans h.right.sign.symm
  · exact h.left.zero.trans h.right.zero.symm
  · exact h.left.one.trans h.right.one.symm
  · exact h.left.ptr.trans h.right.ptr.symm

theorem fastPrep9Step_relCT {K : WinCfg} {src : Nat} (hc : FastPrep9Checks K src)
    {base : Addr} {size k j : Nat} (hb : K.bits+520≤size) (hj : j<257)
    (hv : FastNaf.residual 9 k j≤2^256) :
    RelCT isa (FastPrep9Pair base size K.bits k j) Impl.Weierstrass.AArch64.FastNaf.step9
      (fun s t => FastPrep9Pair base size K.bits k (fastNext9 k j) s t ∧
        (s.gpr .x19=0 ↔ FastNaf.residual 9 k (fastNext9 k j)=0) ∧
        (t.gpr .x19=0 ↔ FastNaf.residual 9 k (fastNext9 k j)=0)) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,_,xs,is,ks,_,zs⟩ := fastStep9_ok hp.left hb hj hv
  obtain ⟨_,_,xt,it,kt,_,zt⟩ := fastStep9_ok hp.right hb hj hv
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hc.step _ _ _ _ _ _ trivial trivial hp.public es et,
    ⟨is,it,ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,zs,zt⟩

theorem fastPrep9Loop_relCT {K : WinCfg} {src : Nat} (hc : FastPrep9Checks K src)
    {base : Addr} {size k : Nat} (hb : K.bits+520≤size) (hk : k<2^256) :
    RelCT isa (FastPrep9Pair base size K.bits k 0)
      (.loop Impl.Weierstrass.AArch64.FastNaf.step9 (.nonzero .x .x19)) (fun _ _ => True) := by
  let I := fun n s t => ∃ j,j<257 ∧ n=257-j ∧ FastPrep9Pair base size K.bits k j s t
  have step : ∀ n,RelCT isa (I n) Impl.Weierstrass.AArch64.FastNaf.step9 (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → True) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ m<n,I m s t)) := by
    intro n s t ts tt s' t' ⟨j,hj,hn,hp⟩ es et
    have hv : FastNaf.residual 9 k j≤2^256 := Nat.le_trans
      (FastNaf.residual_boundB 9 (Nat.le_of_lt hk) (j:=j) (by omega))
      (Nat.pow_le_pow_right (by decide) (by omega))
    obtain ⟨he,ip,zs,zt⟩ := fastPrep9Step_relCT hc hb hj hv _ _ _ _ _ _ hp es et
    refine ⟨he,by rw [fastCount_eval zs,fastCount_eval zt],fun _ => trivial,fun hcnd => ?_⟩
    have hz : FastNaf.residual 9 k (fastNext9 k j)≠0 := by
      rw [fastCount_eval zs] at hcnd
      exact of_decide_eq_true (Option.some.inj hcnd)
    have hj' : fastNext9 k j<257 := by
      by_contra h
      exact hz (FastNaf.residual_zero_ge hk (by omega))
    refine ⟨257-fastNext9 k j,?_,fastNext9 k j,hj',rfl,ip⟩
    have : j<fastNext9 k j := by unfold fastNext9; split <;> omega
    omega
  exact (RelCT.loop I step 257).mono (fun _ _ h => ⟨0,by decide,rfl,h⟩) (fun _ _ h => h)

theorem fastPrep9_relCT (K : WinCfg)
    {base : Addr} {size src : Nat} (hsrc : src+32≤size) (hsrc8 : src%8=0)
    (hbits : K.bits<4096) (hbits8 : K.bits%8=0) (hb : K.bits+520≤size) (hc : FastPrep9Checks K src) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      wordsVal s.mem base src 4=wordsVal t.mem base src 4)
      (Impl.Weierstrass.AArch64.FastNaf.prep9 K src) (fun _ _ => True) := by
  intro s t ts tt s' t' hp es et
  have hi : RelCT isa (fun a b => Scr a base size ∧ Scr b base size ∧ a.sp=b.sp ∧
      wordsVal a.mem base src 4=wordsVal s.mem base src 4 ∧ wordsVal b.mem base src 4=wordsVal s.mem base src 4)
      (.block (Impl.Weierstrass.AArch64.FastNaf.init K src 9 ++ Impl.Weierstrass.AArch64.FastNaf.clear9 K))
      (FastPrep9Pair base size K.bits (wordsVal s.mem base src 4) 0) := by
    intro a b ta tb a' b' hab ea eb
    obtain ⟨_,_,xa,ia,ka,_⟩ := fastSetup9_ok K hab.1 hsrc hsrc8 hbits hbits8 hb
    obtain ⟨_,_,xb,ib,kb,_⟩ := fastSetup9_ok K hab.2.1 hsrc hsrc8 hbits hbits8 hb
    obtain ⟨_,rfl⟩ := Exec.det ea xa
    obtain ⟨_,rfl⟩ := Exec.det eb xb
    rw [hab.2.2.2.1] at ia
    rw [hab.2.2.2.2] at ib
    have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0]) a b := by
      refine ⟨hab.2.2.1,?_⟩
      intro r hr; simp only [Taint.mem_ofRegs,List.mem_singleton] at hr; subst r
      exact hab.1.x0.trans hab.2.1.x0.symm
    exact ⟨hc.init _ _ _ _ _ _ trivial trivial pub ea eb,ia,ib,ka.sp.trans (hab.2.2.1.trans kb.sp.symm)⟩
  exact (RelCT.seq hi (fastPrep9Loop_relCT hc hb (wordsVal_lt ..))) _ _ _ _ _ _
    ⟨hp.1,hp.2.1,hp.2.2.1,rfl,hp.2.2.2.symm⟩ es et

end VG.Proof.Weierstrass.AArch64
