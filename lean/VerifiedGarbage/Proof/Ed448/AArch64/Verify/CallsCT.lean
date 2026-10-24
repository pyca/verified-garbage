module

public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Calls
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CT
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract

/-! The equation call may reveal the two public scalar values, whose equality
is established by the caller's hash and reduction correctness proofs. -/

@[expose] public section
namespace VG.Proof.Ed448.AArch64.Verify
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole
open VG.Impl.Ed448.AArch64.Sparse (baseSym baseWords)
open VG.Proof.Ed25519.AArch64.Whole (FR CK)

/-- Fixed-address public scalar values before argument setup. -/
def EquationReady (sig ch:Addr) (S K:Nat) (s:State) : Prop :=
  Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (sig+BitVec.ofNat 64 57) 57)=S ∧
  Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem ch 57)=K

variable {V:Env} {g₁ g₂:Reg → Addr} {v₁ v₂:VReg → BitVec 128} {m₁ m₂:Mem}

theorem equation_ct (hQ:Proof.Ed448.AArch64.Sparse.EqOk) (hV:V.Ok)
    (hcfg:V.sym=baseSym ∧ V.words=baseWords)
    {M:Mem → Prop} (h₁:M m₁) (h₂:M m₂) {args:List (Reg × Src)}
    (hn:(args.map Prod.fst).Nodup) (hv:∀ p∈args,srcValid p.2) (hret:retOk args=true)
    (hr:∀ p∈args,p.1∉preserved) (hl:∀ p∈args,p.1∉linkRegs)
    {hint:VG.Taint.Hint VG.AArch64.Taint.T}
    (ht:(taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome=true)
    (val:Reg → Addr) (S K:Nat)
    (hval:∀ {g vec m₀ t},M m₀ → WCtx V g vec m₀ t → EquationReady (val .x1) (val .x2) S K t →
      ∀ p∈args,srcValue V.E t.mem (t.gpr .x0) p.2=val p.1)
    (hm:∀ r∈[Reg.x0,.x1,.x2,.x3],r∈args.map Prod.fst)
    (hdp:Region.Disjoint ⟨val .x0,57⟩ ⟨val .x3,8192⟩)
    (hds:Region.Disjoint ⟨val .x1,114⟩ ⟨val .x3,8192⟩)
    (hdc:Region.Disjoint ⟨val .x2,57⟩ ⟨val .x3,8192⟩)
    (hnc:(val .x3).toNat+8192≤2^64)
    (hrp:Readable V ⟨val .x0,57⟩) (hrs:Readable V ⟨val .x1,114⟩) (hrc:Readable V ⟨val .x2,57⟩)
    (hws:Writable V ⟨val .x3,8192⟩) (hMT:∀ {m},M m → TblWords V.T m baseWords) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ (EquationReady (val .x1) (val .x2) S K))
      (callS args "vg_ed448_verify_equation" Impl.Ed448.AArch64.Sparse.verifyEquation) (fun _ _ => True):=by
  let Ready:=fun s => Regs args val s ∧ EquationReady (val .x1) (val .x2) S K s
  have setup:RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ (EquationReady (val .x1) (val .x2) S K))
      (.block (setupS args)) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Ready):=by
    apply block_ct h₁ h₂ ht
    intro g vec m₀ t hM hc hp
    refine WP.mono (wsetup_ok hV hc hn hv hret hr) fun u ⟨uc,um,ug⟩ => ⟨uc,?_,?_⟩
    · intro p hpa
      exact (ug p hpa).trans (hval hM hc hp p hpa)
    · change EquationReady _ _ _ _ u
      unfold EquationReady
      rw [um]
      exact hp
  have hw:∀ r∈[(⟨val .x3,8192⟩:Region)],Writable V r:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro r rfl;exact hws
  have hrd:∀ r∈[(⟨val .x0,57⟩:Region),⟨val .x1,114⟩,⟨val .x2,57⟩,TBL V.T baseWords],Readable V r:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl|rfl|rfl|rfl)
    exacts [hrp,hrs,hrc,by simpa only [hcfg.2] using tbl_readable hV]
  have pre:∀ {g vec m₀ t},M m₀ → WCtx V g vec m₀ t → Regs args val t →
      Proof.Ed448.AArch64.Sparse.verifyEquationLocal.pre
        (t.callEntry.withRegions [⟨val .x0,57⟩,⟨val .x1,114⟩,⟨val .x2,57⟩,TBL V.T baseWords]
          [⟨val .x3,8192⟩]):=by
    intro g vec m₀ t hM hc hs
    exact equation_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) (regs_get hs (hm .x3 (by simp))) hdp hds hdc hnc
      (by simpa only [hcfg.1] using hc.2.2) (baseHeld_of hV hcfg hc (hMT hM) hw _ _)
  refine setup.seq (VG.Proof.Ed25519.AArch64.Whole.callEx hQ.ok hQ.ct fun a b h => ?_)
  let rd:List Region:=[⟨val .x0,57⟩,⟨val .x1,114⟩,⟨val .x2,57⟩,TBL V.T baseWords]
  let wr:List Region:=[⟨val .x3,8192⟩]
  let ca:VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Ed448.AArch64.Sparse.verifyEquationLocal V.E V.ins V.outs a:=
    ⟨rd,wr,pre h₁ h.1.1 h.1.2.1,covers_rw hrd hw,fun r hr => (hw r hr).imp And.left id⟩
  let cb:VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Ed448.AArch64.Sparse.verifyEquationLocal V.E V.ins V.outs b:=
    ⟨rd,wr,pre h₂ h.2.1 h.2.2.1,covers_rw hrd hw,fun r hr => (hw r hr).imp And.left id⟩
  obtain ⟨cra,cwa⟩:=ca.covers_state h.1.1.1
  obtain ⟨crb,cwb⟩:=cb.covers_state h.2.1.1
  refine ⟨rd,wr,rd,wr,ca.pre,cb.pre,?_,cra,cwa,crb,cwb⟩
  have hlink:∀ r∈[Reg.x0,.x1,.x2,.x3],r∉linkRegs:=by
    intro r hr
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp (hm r hr)
    exact hl p hp
  have regs:∀ r∈[Reg.x0,.x1,.x2,.x3],a.callEntry.gpr r=val r ∧ b.callEntry.gpr r=val r:=by
    intro r hr
    rw [State.callEntry_gpr _ (hlink r hr),
      State.callEntry_gpr _ (hlink r hr)]
    exact ⟨regs_get h.1.2.1 (hm r hr),regs_get h.2.2.1 (hm r hr)⟩
  change a.sp=b.sp ∧ _
  refine ⟨two_sp h,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (regs .x0 (by simp)).1.trans (regs .x0 (by simp)).2.symm
  · exact (regs .x1 (by simp)).1.trans (regs .x1 (by simp)).2.symm
  · exact (regs .x2 (by simp)).1.trans (regs .x2 (by simp)).2.symm
  · exact (regs .x3 (by simp)).1.trans (regs .x3 (by simp)).2.symm
  · change a.syms baseSym=b.syms baseSym
    simpa only [hcfg.1] using h.1.1.2.2.trans h.2.1.2.2.symm
  · change Spec.Ed448.decodeLE (Spec.Ed448.bytesAt a.mem (a.callEntry.gpr .x1+BitVec.ofNat 64 57) 57)=
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt b.mem (b.callEntry.gpr .x1+BitVec.ofNat 64 57) 57)
    rw [(regs .x1 (by simp)).1,(regs .x1 (by simp)).2]
    exact h.1.2.2.1.trans h.2.2.2.1.symm
  · change Spec.Ed448.decodeLE (Spec.Ed448.bytesAt a.mem (a.callEntry.gpr .x2) 57)=
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt b.mem (b.callEntry.gpr .x2) 57)
    rw [(regs .x2 (by simp)).1,(regs .x2 (by simp)).2]
    exact h.1.2.2.2.trans h.2.2.2.2.symm

end VG.Proof.Ed448.AArch64.Verify
