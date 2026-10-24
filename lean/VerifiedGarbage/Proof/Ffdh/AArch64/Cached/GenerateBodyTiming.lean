module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BodyTimingState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateBody
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete attempt-body timing is governed by public geometry and the reviewed returned status. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)

def TailReady (q : BodyPublic) (s : State) : Prop :=
 ModState q.scalar.p s ∧ OutputReady (bodyOutput q) s

def bodyRangePublic (q : BodyPublic) : RangePublic :=
 ⟨scalarWs q.scalar,by change 0<q.scalar.p.w;have :=q.scalar.p.positive;omega,q.scalar.p.width⟩

theorem bodyComb_output (M : Mont) {q : BodyPublic} {s : State} (h : BodyReady q s) :
 WP isa (Comb.code M.mm) s (TailReady q) := by
 obtain ⟨bs,h⟩ :=h
 have length :=h.scalar.length
 refine WP.mono (comb_correct M h.scalar.initial q.bitsPositive q.bitsBound
  (length ▸ q.scalar.size) (length ▸ q.width) h.bound q.table) ?_
 rintro t ⟨state,_,controls,_,stable,rest⟩
 exact ⟨state,state.good,controls.source,
  (stable sY (by decide) (by decide) (by decide) (by decide)).trans h.y,
  length ▸ controls.length,fun i hi =>by rw [rest.wr];exact h.write i hi⟩

theorem bodyRange_finish {q : BodyPublic} {s : State} (h : TailReady q s) :
 WP isa Generate.publicRange s (FinishReady (bodyOutput q)) := by
 obtain ⟨state,good,x,y,len,write⟩ :=h
 refine WP.mono (publicRange_ok state q.scalar.odd) ?_
 rintro t ⟨stateT,_,flag,header,frame,rest⟩
 refine ⟨⟨stateT.good,(publicRangeFrame_header frame (by decide) (by decide)).trans x,
  (publicRangeFrame_header frame (by decide) (by decide)).trans y,
  (publicRangeFrame_header frame (by decide) (by decide)).trans len,
  fun i hi =>by rw [rest.wr];exact write i hi⟩,?_,?_⟩
 · exact decide (1<wv s.mem q.scalar.p.B (slot q.scalar.p.w 6) q.scalar.p.w ∧
    wv s.mem q.scalar.p.B (slot q.scalar.p.w 6) q.scalar.p.w<q.scalar.p.P-1)
 · change word t.mem q.scalar.p.B (8*sTmp)=_
   rw [header,flag]
   exact (bit_decide _).symm

theorem acceptedBody_ct (M : Mont) : RelCT isa (Two BodyReady)
 (.seq (Comb.code M.mm) (.seq Generate.publicRange Generate.finish)) (fun _ _ =>True) := by
 refine RelCT.seq (two_post (Ψ:=TailReady)
  (two_map bodyComb (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨bs,h.scalar.initial,h.bound⟩) (comb_ct M))
  (fun _ _ h =>bodyComb_output M h)) ?_
 exact RelCT.seq (two_post (Ψ:=fun q s =>FinishReady (bodyOutput q) s)
  (two_map bodyRangePublic (fun q s h =>⟨q.scalar.p.mi,h.1.good,q.scalar.p.room⟩) publicRange_ct)
  (fun _ _ h =>bodyRange_finish h)) (two_map bodyOutput (fun _ _ h =>h) finish_ct)

theorem generateBody_ct (M : Mont) : RelCT isa (Two BodyReady) (generateBody M.mm) (fun _ _ =>True) := by
 unfold generateBody
 refine RelCT.seq (two_post (Ψ:=BodyRangeDone)
  (two_map BodyPublic.scalar (fun _ _ h =>by obtain ⟨bs,h⟩:=h;exact ⟨bs,h.scalar⟩) scalarRange_ct)
  (fun _ _ h =>bodyRangeDone_ok h)) ?_
 refine RelCT.ite ?_ ?_ ?_
 · rintro s t ⟨q,hs,ht,_⟩
   rw [eval_zero,eval_zero,hs.2,ht.2]
 · exact (two_map bodyOutput (fun _ _ h =>bodyReady_output h) fail_ct).mono
    (fun _ _ h =>by rcases h.1 with ⟨q,hs,ht,sp⟩;exact ⟨q,hs.1,ht.1,sp⟩) (fun _ _ h =>h)
 · exact (acceptedBody_ct M).mono
    (fun _ _ h =>by rcases h.1 with ⟨q,hs,ht,sp⟩;exact ⟨q,hs.1,ht.1,sp⟩) (fun _ _ h =>h)

end VG.Proof.Ffdh.AArch64.Cached
