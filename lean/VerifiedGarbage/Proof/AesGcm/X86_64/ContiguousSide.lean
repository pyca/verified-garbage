module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Leaves
public import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous
import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.ScrubFill
import VerifiedGarbage.Proof.Framework.Lit

/-! The caller's stack and vector cleanup cover the same contiguous entry
for both source/destination layouts. -/

@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.Scrub
open VG.Impl.AesGcm.X86_64 (Fn Callees)
open VG.Impl.AesGcm.X86_64.Contiguous

abbrev allowance := fun (_ : String) => 8

private theorem fillBody {k : Nat} {c : Callees} (hs : CalleesSide k c)
    {sk ker : Prog isa} (fk : Fill k allowance sk ker) (vec wide prep : Bool) :
    Fill k allowance (core (body stub5 vec wide prep sk)) (core (body c vec wide prep ker)) := by
  obtain ⟨hc,_,hg,_,_⟩ := hs
  cases vec <;> cases wide <;> cases prep <;>
    repeat (any_goals (first
      | exact Fill.refl _
      | exact fk
      | refine Fill.seq ?_ ?_
      | exact Fill.hole _ _ (by assumption)
      | refine Fill.ite _ ?_ ?_
      | refine Fill.loop _ ?_
      | refine Fill.call _ _ ?_
      | refine Fill.frame _ _ ?_))

private theorem fillDeferred {k : Nat} {c : Callees} {ctr : Fn} (hs : CalleesSide k c)
    (ht : calleeSide ctr.code k 8=true) :
    Fill k allowance (core (deferredBody stub5 ctrToStub)) (core (deferredBody c ctr)) := by
  obtain ⟨hc,_,hg,_,_⟩ := hs
  fill_calls_wide

private theorem fillSeparate {k : Nat} {ctr gh : Fn} (ct : calleeSide ctr.code k 8=true)
    (hg : calleeSide gh.code k 8=true) :
    Fill k allowance (separate ctrToStub stub5.gh) (separate ctr gh) := by fill_calls_wide

private theorem fillFused {k : Nat} {f : Fn} (hf : calleeSide f.code k 8 = true) :
    Fill k allowance (fused (fnStub "B")) (fused f) := by fill_calls_wide

private theorem frameFill {k : Nat} {r s : Prog isa} (f : Fill k allowance (core r) (core s)) :
    Fill k allowance (framed r) (framed s) := .frame _ _ (.seq (.block _) f)

theorem selectedFill {k : Nat} {c : Callees} {ctr : Fn} {blocks : Option Fn}
    (defer wide : Bool) (n : Nat) (hs : CalleesSide k c) (ct : calleeSide ctr.code k 8=true)
    (hb : ∀ f∈blocks, calleeSide f.code k 8=true) :
    Fill k allowance (selected defer wide n stub5 ctrToStub (blocks.map fun _ => fnStub "B"))
      (selected defer wide n c ctr blocks) := by
  cases blocks with
  | none =>
    cases defer
    · exact frameFill (fillBody hs (fillSeparate ct hs.gh) false wide false)
    · exact frameFill (fillDeferred hs ct)
  | some f =>
    have ready := frameFill (fillBody hs (fillFused (hb f rfl)) true wide true)
    refine .seq (.block _) (.ite _ (.seq (.seq (.block _) (.block _)) ready) ?_)
    cases defer
    · exact frameFill (fillBody hs (fillSeparate ct hs.gh) true wide false)
    · exact frameFill (fillDeferred hs ct)

theorem plainSide (defer : Bool) :
    stubSide (selected defer false 16 stub5 ctrToStub none) 0 allowance 2640 []=true := by
  cases defer <;> lit_decide

theorem vectorSide (wide : Bool) :
    stubSide (selected false wide (if wide then 48 else 16) stub5 ctrToStub (some (fnStub "B")))
      (if wide then 2 else 1) allowance 2640 []=true := by
  cases wide <;> lit_decide

abbrev Sp (c : Prog isa) := c.all (fun i => !isa.writesSp i)=true

private theorem spParts (v : GcmImpl) :
    Sp (Impl.AesGcm.X86_64.oneAad v.callees) ∧ Sp (Impl.AesGcm.X86_64.cryptTailG v.callees true) ∧
    Sp (Impl.AesGcm.X86_64.oneTag v.callees 0) := by
  have a := seal_spSafe v
  simp only [Impl.AesGcm.X86_64.«seal»,Code.all,Bool.and_eq_true] at a
  obtain ⟨_,aa,_,_,⟨tg,_⟩,_⟩ := a
  refine ⟨aa,?_,tg⟩
  simp only [Sp,Impl.AesGcm.X86_64.cryptTailG,Code.all,GcmImpl.callees,v.ctr.spSafe]
  decide +kernel

private theorem spBody (v : GcmImpl) {p : Prog isa} (hp : Sp p) (vec wide prep : Bool) :
    Sp (core (body v.callees vec wide prep p)) := by
  obtain ⟨aa,tail,tg⟩ := spParts v
  unfold Sp at *
  cases vec <;> cases wide <;> cases prep <;>
    simp only [core,body,aad,bulk,finishScalar,Code.all,hp,aa,tail,tg,Bool.true_and,Bool.and_true,ite_true,ite_false,
      Bool.false_eq_true,Bool.false_and] <;> decide +kernel

private theorem spDeferred (v : GcmImpl) {ctr : Fn} (ct : Sp ctr.code) :
    Sp (core (deferredBody v.callees ctr)) := by
  obtain ⟨aa,tail,tg⟩ := spParts v
  unfold Sp at *
  simp only [Impl.AesGcm.X86_64.oneTag,Code.all,Bool.and_eq_true] at tg
  simp only [core,deferredBody,bulk,Impl.AesGcm.X86_64.Contiguous.call,Code.all,ct,aa,tail,tg.2,Bool.true_and,Bool.and_true]
  decide +kernel

theorem selectedSp (v : GcmImpl) {ctr : Fn} (defer wide : Bool) (n : Nat) {b : Option Fn}
    (ct : Sp ctr.code) (hb : ∀ f∈b, Sp f.code) : Sp (selected defer wide n v.callees ctr b) := by
  have split : Sp (separate ctr v.callees.gh) := by
    simp only [Sp,separate,Impl.AesGcm.X86_64.Contiguous.call,Code.all,GcmImpl.callees,v.gh.spSafe,ct,Bool.true_and,Bool.and_true]
    decide +kernel
  have base (vec : Bool) : Sp (if defer then framed (deferredBody v.callees ctr) else one v.callees vec wide false (separate ctr v.callees.gh)) := by
    cases defer
    · exact withStackArgScratch_spSafe (spBody v split vec wide false)
    · exact withStackArgScratch_spSafe (spDeferred v ct)
  cases b with
  | none => exact base false
  | some f =>
    have fusedSp : Sp (fused f) := by
      simp only [Sp,fused,Impl.AesGcm.X86_64.Contiguous.call,Code.all,hb f rfl,Bool.and_true]
      decide +kernel
    exact onFlag_spSafe (withStackArgScratch_spSafe (spBody v fusedSp true wide true)) (base true)

end VG.Proof.AesGcm.X86_64.ContiguousSeal
