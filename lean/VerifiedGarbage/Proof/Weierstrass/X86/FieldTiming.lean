import VerifiedGarbage.Proof.Weierstrass.X86.JacZero
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint

/-! Equal public field values determine branches; addresses and call frames are public. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Mont.X86

def nafτ (rs : List Reg := [.edi,.esp]) : VG.X86.Taint.T :=
  { regs := .ofList rs,flags := false,lens := [8192],bases := [(.edi,0,0)],room := 20 }

theorem nafWf_keep {rs rt : List Reg} {s t : State} (h : VG.X86.Taint.Wf (nafτ rs) s)
    (hw : t.wr=s.wr) (hd : t.gpr .edi=s.gpr .edi) (hp : t.gpr .esp=s.gpr .esp) :
    VG.X86.Taint.Wf (nafτ rt) t := by
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_,?_,?_,?_,?_⟩ ?_
  · intro hn; rw [hw]; exact h.lens hn
  · intro p he
    obtain rfl := List.mem_singleton.mp he
    simp only [VG.X86.Taint.region,hw,hd]
    exact h.bases _ (List.mem_singleton_self _)
  · intro p he; cases he
  · intro he; cases he
  · intro p he; cases he
  · intro he
    have hr := h.room he
    simp only [nafτ,VG.X86.Taint.depth,VG.X86.Taint.nframes,List.drop_zero,
      VG.X86.Taint.argByte,Nat.add_zero,BitVec.add_zero] at hr ⊢
    rw [hw,hp]; exact hr

structure NafPublic (s t : State) : Prop where
  wf₁ : VG.X86.Taint.Wf (nafτ) s
  wf₂ : VG.X86.Taint.Wf (nafτ) t
  edi : s.gpr .edi=t.gpr .edi
  esp : s.gpr .esp=t.gpr .esp
  wr : s.wr=t.wr

theorem NafPublic.keep {s t u v : State} {rs : List Reg} (h : NafPublic s t)
    (ku : Keeps rs s u) (kv : Keeps rs t v) (hd : Reg.edi∉rs) (hp : Reg.esp∉rs) :
    NafPublic u v :=
  ⟨nafWf_keep h.wf₁ ku.wr (ku.gpr _ hd) (ku.gpr _ hp),
    nafWf_keep h.wf₂ kv.wr (kv.gpr _ hd) (kv.gpr _ hp),
    (ku.gpr _ hd).trans (h.edi.trans (kv.gpr _ hd).symm),
    (ku.gpr _ hp).trans (h.esp.trans (kv.gpr _ hp).symm),ku.wr.trans (h.wr.trans kv.wr.symm)⟩

theorem NafPublic.agree {s t : State} (h : NafPublic s t) {rs : List Reg}
    (hr : ∀ r∈rs,s.gpr r=t.gpr r) : VG.X86.Taint.Agree (nafτ rs) s t := by
  refine ⟨⟨?_,fun h => nomatch h⟩,fun _ => h.wr,
    nafWf_keep h.wf₁ rfl rfl rfl,nafWf_keep h.wf₂ rfl rfl rfl,
    fun _ he => (List.not_mem_nil he).elim,fun _ he => (List.not_mem_nil he).elim,
    (fun he => nomatch he),fun _ _ he => (Nat.not_lt_zero _ he).elim⟩
  intro r he
  exact hr r (by simpa only [nafτ,RegSet.mem_ofList] using he)

structure FieldPair (M : Mod) (base : Addr) (size m : Nat) [NeZero m]
    (Sl : Nat → Prop) (V : List Nat) (E : Nat → Fin m) (counter : BitVec 32) (s t : State) : Prop where
  left : Inv M base size m Sl V E s
  right : Inv M base size m Sl V E t
  pub : NafPublic s t
  count₁ : s.gpr .esi=counter
  count₂ : t.gpr .esi=counter

theorem FieldPair.sub {counter : BitVec 32} {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V W : List Nat} {E : Nat → Fin m} {s t : State}
    (h : FieldPair M base size m Sl V E counter s t) (hw : ∀ x∈W,x∈V) :
    FieldPair M base size m Sl W E counter s t := ⟨h.left.sub hw,h.right.sub hw,h.pub,h.count₁,h.count₂⟩

abbrev ScratchCT (c : Prog isa) : Prop :=
  ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (nafτ)) c

theorem scratch_relCT {counter : BitVec 32} {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {c : Prog isa}
    (hc : ScratchCT c) :
    RelCT isa (FieldPair M base size m Sl V E counter) c (fun _ _ => True) := by
  intro s t ts tt u v h es et
  refine ⟨hc _ _ _ _ _ _ trivial trivial (h.pub.agree ?_) es et,trivial⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact h.pub.edi
  · exact h.pub.esp

theorem fieldProgram_relCT {counter : BitVec 32} {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V W : List Nat} {E E' : Nat → Fin m} {c : Prog isa}
    (hc : ScratchCT c)
    (hw : ∀ s,Inv M base size m Sl V E s →
      WP isa c s (fun t => Keeps clob s t ∧ Inv M base size m Sl W E' t)) :
    RelCT isa (FieldPair M base size m Sl V E counter) c (FieldPair M base size m Sl W E' counter) := by
  intro s t ts tt u v h es et
  have kr := scratch_relCT hc s t ts tt u v h es et
  obtain ⟨_,u',eu,ku,iu⟩ := hw s h.left
  obtain ⟨_,v',ev,kv,iv⟩ := hw t h.right
  obtain ⟨-,rfl⟩ := Exec.det es eu
  obtain ⟨-,rfl⟩ := Exec.det et ev
  exact ⟨kr.1,iu,iv,h.pub.keep ku kv (by decide) (by decide),
    (ku.gpr _ (by decide)).trans h.count₁,(kv.gpr _ (by decide)).trans h.count₂⟩

theorem fieldBranch_relCT {counter : BitVec 32} {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {V : List Nat} {E : Nat → Fin m} {a : Nat} (ha : a∈V)
    (hc : ScratchCT (.block (Jacobian.zeroTest M.n a)))
    {yes no : Prog isa} {Q : State → State → Prop}
    (hy : E a=0 → RelCT isa (FieldPair M base size m Sl V E counter) yes Q)
    (hn : E a≠0 → RelCT isa (FieldPair M base size m Sl V E counter) no Q) :
    RelCT isa (FieldPair M base size m Sl V E counter)
      (.seq (.block (Jacobian.zeroTest M.n a)) (.ite .e yes no)) Q := by
  have hz : RelCT isa (FieldPair M base size m Sl V E counter) (.block (Jacobian.zeroTest M.n a))
      (fun s t => FieldPair M base size m Sl V E counter s t ∧
        s.zf=some (decide (E a=0)) ∧ t.zf=some (decide (E a=0))) := by
    intro s t ts tt u v h es et
    have kr := scratch_relCT hc s t ts tt u v h es et
    obtain ⟨_,u',eu,zu,iu,ku⟩ := zeroField_ok (wk:=0) hL hm h.left ha
    obtain ⟨_,v',ev,zv,iv,kv⟩ := zeroField_ok (wk:=0) hL hm h.right ha
    obtain ⟨-,rfl⟩ := Exec.det es eu
    obtain ⟨-,rfl⟩ := Exec.det et ev
    exact ⟨kr.1,⟨iu,iv,h.pub.keep ⟨ku.gpr,ku.rd,ku.wr⟩ ⟨kv.gpr,kv.rd,kv.wr⟩
      (by decide) (by decide),(ku.gpr _ (by decide)).trans h.count₁,
      (kv.gpr _ (by decide)).trans h.count₂⟩,zu,zv⟩
  apply RelCT.seq hz
  apply RelCT.ite
  · intro s t h; exact h.2.1.trans h.2.2.symm
  · intro s t ts tt u v ⟨h,he⟩ es et
    exact hy (of_decide_eq_true (Option.some.inj (h.2.1.symm.trans he))) _ _ _ _ _ _ h.1 es et
  · intro s t ts tt u v ⟨h,he⟩ es et
    exact hn (of_decide_eq_false (Option.some.inj (h.2.1.symm.trans he))) _ _ _ _ _ _ h.1 es et

end VG.Proof.Weierstrass.X86
