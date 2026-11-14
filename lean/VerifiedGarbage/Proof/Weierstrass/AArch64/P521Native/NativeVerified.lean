module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeExchange
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.TimingFront
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeWindow
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeEntry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Sig

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config windowLoop)

structure TimingWindowPre (origin s : State) : Prop where
  data : ∃k,WindowData (origin.gpr .x3) (origin.sp-3456#64) k s
  point : canonicalPoint s.mem (origin.gpr .x3) 1072
  counter : s.gpr .x19=105#64
  output : s.gpr .x20=origin.gpr .x0
  sp : s.sp=origin.sp-3456#64

structure TimingFinishPre (origin s : State) : Prop where
  workspace : s.gpr .x0=origin.gpr .x3
  table : s.gpr .x26=origin.sp-3456#64
  counter : s.gpr .x19=1#64
  output : s.gpr .x20=origin.gpr .x0
  sp : s.sp=origin.sp-3456#64

private theorem TimingExchange_TimingBody_TimingState_native_prime : config.C.p=fieldPrime := by
  dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,Spec.P521.curve,Spec.P521.p,fieldPrime]

theorem timing_front_ready (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n) {s : State} (pre : PrepareStackPre s) :
    WP isa nativeFront (allocated 3456 s) (TimingWindowPre s) := by
  refine WP.mono (native_front_api_ok hc law ha order orderBound pre) fun t post => ?_
  obtain ⟨_,_,_,_,_,_,_,_,_,_,result,out,sp,_⟩:=post
  have primeOne : 1<fieldPrime := by have h:=hc.p_ge; rw [TimingExchange_TimingBody_TimingState_native_prime] at h; omega_arith
  refine ⟨⟨_,result.data⟩,?_,result.counter,out,sp⟩
  change wordsVal t.mem (s.gpr .x3) 1072 9<fieldPrime ∧
    wordsVal t.mem (s.gpr .x3) 1144 9<fieldPrime ∧ wordsVal t.mem (s.gpr .x3) 1216 9<fieldPrime
  rw [result.accumulatorX,result.accumulatorY,result.accumulatorZ]
  exact ⟨by omega_arith,primeOne,by omega_arith⟩

theorem timing_window_ready {origin s : State} (pre : PrepareStackPre origin)
    (ready : TimingWindowPre origin s) : WP isa windowLoop s (TimingFinishPre origin) := by
  obtain ⟨k,data⟩:=ready.data
  refine WP.mono (native_window_ok data pre.table_scratch.symm ready.point ready.counter) fun t post => ?_
  exact ⟨post.workspace,post.tablePointer,post.counter,post.outputPointer.trans ready.output,post.sp.trans ready.sp⟩

def entryPublic (s t : State) : Prop :=
  AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3]) s t

theorem TimingWindowPre.public {a b s t : State} (hs : TimingWindowPre a s) (ht : TimingWindowPre b t)
    (pub : entryPublic a b) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20]) s t := by
  obtain ⟨_,ds⟩:=hs.data
  obtain ⟨_,dt⟩:=ht.data
  refine ⟨hs.sp.trans ((congrArg (fun v => v-3456#64) pub.1).trans ht.sp.symm),?_⟩
  intro r hr
  simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact ds.scr.x0.trans ((pub.2 .x3 (by decide)).trans dt.scr.x0.symm)
  · exact hs.counter.trans ht.counter.symm
  · exact ds.readable.reg.trans ((congrArg (fun v => v-3456#64) pub.1).trans dt.readable.reg.symm)
  · exact hs.output.trans ((pub.2 .x0 (by decide)).trans ht.output.symm)

theorem TimingFinishPre.public {a b s t : State} (hs : TimingFinishPre a s) (ht : TimingFinishPre b t)
    (pub : entryPublic a b) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20]) s t := by
  refine ⟨hs.sp.trans ((congrArg (fun v => v-3456#64) pub.1).trans ht.sp.symm),?_⟩
  intro r hr
  simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact hs.workspace.trans ((pub.2 .x3 (by decide)).trans ht.workspace.symm)
  · exact hs.counter.trans ht.counter.symm
  · exact hs.table.trans ((congrArg (fun v => v-3456#64) pub.1).trans ht.table.symm)
  · exact hs.output.trans ((pub.2 .x0 (by decide)).trans ht.output.symm)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config windowLoop finishAndWrite)

def nativeTimedBody : Prog isa := .seq nativeFront (.seq windowLoop finishAndWrite)

private theorem TimingExchange_TimingBody_wp_result {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (e : Exec isa c s trace t) : Q t := by
  obtain ⟨_,u,eu,qu⟩:=h
  obtain ⟨_,rfl⟩:=Exec.det e eu
  exact qu

private theorem TimingExchange_TimingBody_entry_allocated {a b : State} (h : entryPublic a b) :
    entryPublic (allocated 3456 a) (allocated 3456 b) :=
  ⟨congrArg (fun sp => sp-3456#64) h.1,h.2⟩

private theorem TimingExchange_TimingBody_window_public_narrow {a b : State}
    (h : AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20]) a b) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26]) a b := by
  refine ⟨h.1,?_⟩
  intro r hr
  apply h.2 r
  simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
  rcases hr with rfl|rfl|rfl <;> simp

theorem native_timed_body_traces (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n)
    {a b a' b' : State} {ta tb : List Leak} (pa : PrepareStackPre a) (pb : PrepareStackPre b)
    (pub : entryPublic a b)
    (ea : Exec isa nativeTimedBody (allocated 3456 a) ta a')
    (eb : Exec isa nativeTimedBody (allocated 3456 b) tb b') : ta=tb := by
  cases ea with
  | seq fa wa =>
    cases eb with
    | seq fb wb =>
      have frontTrace := native_front_constantTime _ _ _ _ _ _ trivial trivial (TimingExchange_TimingBody_entry_allocated pub) fa fb
      have readyA := TimingExchange_TimingBody_wp_result (timing_front_ready hc law ha order orderBound pa) fa
      have readyB := TimingExchange_TimingBody_wp_result (timing_front_ready hc law ha order orderBound pb) fb
      have windowPublic := TimingWindowPre.public readyA readyB pub
      cases wa with
      | seq wina fina =>
        cases wb with
        | seq winb finb =>
          have windowTrace := window_constantTime _ _ _ _ _ _ trivial trivial (TimingExchange_TimingBody_window_public_narrow windowPublic) wina winb
          have finishA := TimingExchange_TimingBody_wp_result (timing_window_ready pa readyA) wina
          have finishB := TimingExchange_TimingBody_wp_result (timing_window_ready pb readyB) winb
          have finishPublic := TimingFinishPre.public finishA finishB pub
          have finishTrace := finish_constantTime _ _ _ _ _ _ trivial trivial finishPublic fina finb
          rw [frontTrace,windowTrace,finishTrace]

private theorem TimingExchange_TimingBody_seq_parts {a b : Prog isa} {s t : State} {trace : List Leak}
    (e : Exec isa (.seq a b) s trace t) :
    ∃u ta tb,trace=ta++tb ∧ Exec isa a s ta u ∧ Exec isa b u tb t := by
  cases e with
  | seq ea eb => exact ⟨_,_,_,rfl,ea,eb⟩

private theorem TimingExchange_TimingBody_nil_parts {s t : State} {trace : List Leak}
    (e : Exec isa (.block []) s trace t) : trace=[] ∧ t=s := by
  cases e with
  | block hn =>
    simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at hn
    exact ⟨hn.2.symm,hn.1.symm⟩

private theorem TimingExchange_TimingBody_body_to_timed {s t : State} {trace : List Leak}
    (e : Exec isa VG.Impl.Weierstrass.AArch64.P521Native.body s trace t) :
    Exec isa nativeTimedBody s trace t := by
  obtain ⟨u,tp,tr,rfl,p,r⟩:=TimingExchange_TimingBody_seq_parts e
  obtain ⟨v,trc,tb,rfl,rc,b⟩:=TimingExchange_TimingBody_seq_parts r
  obtain ⟨w,tbl,tn,rfl,bl,n⟩:=TimingExchange_TimingBody_seq_parts b
  obtain ⟨x,tno,tw,rfl,no,ww⟩:=TimingExchange_TimingBody_seq_parts n
  obtain ⟨y,twi,tf,rfl,wi,f⟩:=TimingExchange_TimingBody_seq_parts ww
  obtain ⟨z,tfi,te,rfl,fi,empty⟩:=TimingExchange_TimingBody_seq_parts f
  obtain ⟨rfl,rfl⟩:=TimingExchange_TimingBody_nil_parts empty
  have assembled:=Exec.seq (Exec.seq p (Exec.seq rc (Exec.seq bl no))) (Exec.seq wi fi)
  simpa only [nativeTimedBody,nativeFront,nativeRecodeArithmetic,nativeFrontArithmetic,
    List.append_assoc,List.append_nil] using assembled

theorem native_body_traces (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n)
    {a b a' b' : State} {ta tb : List Leak} (pa : PrepareStackPre a) (pb : PrepareStackPre b)
    (pub : entryPublic a b)
    (ea : Exec isa VG.Impl.Weierstrass.AArch64.P521Native.body (allocated 3456 a) ta a')
    (eb : Exec isa VG.Impl.Weierstrass.AArch64.P521Native.body (allocated 3456 b) tb b') : ta=tb :=
  native_timed_body_traces hc law ha order orderBound pa pb pub (TimingExchange_TimingBody_body_to_timed ea) (TimingExchange_TimingBody_body_to_timed eb)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config outerBlock000 outerBlock172 exchange body sequence)

private theorem TimingExchange_seq_parts {a b : Prog isa} {s t : State} {trace : List Leak}
    (e : Exec isa (.seq a b) s trace t) :
    ∃u ta tb,trace=ta++tb ∧ Exec isa a s ta u ∧ Exec isa b u tb t := by
  cases e with
  | seq ea eb => exact ⟨_,_,_,rfl,ea,eb⟩

private theorem TimingExchange_nil_parts {s t : State} {trace : List Leak}
    (e : Exec isa (.block []) s trace t) : trace=[] ∧ t=s := by
  cases e with
  | block hn =>
    simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at hn
    exact ⟨hn.2.symm,hn.1.symm⟩

private theorem TimingExchange_alloc_parts {c : Prog isa} {s t : State} {trace : List Leak}
    (room : 3456≤s.sp.toNat) (e : Exec isa (.frame (.alloc 3456) c (.free 3456)) s trace t) :
    ∃u,Exec isa c (allocated 3456 s) trace u := by
  have pushKnown : isa.push (.alloc 3456) s=some (allocated 3456 s) := by
    simp only [isa,push,show 0<3456 from by decide,show 3456<4096 from by decide,
      show 3456%16=0 from by decide,room,and_self,ite_true]
    rfl
  cases e with
  | frame hp eb _ =>
    have eq := Option.some.inj (pushKnown.symm.trans hp)
    subst eq
    exact ⟨_,by simpa only [isa,addrs,List.map_nil,List.nil_append,List.append_nil] using eb⟩

private theorem TimingExchange_exchange_body_parts {s t : State} {trace : List Leak}
    (pre : PrepareStackPre s) (e : Exec isa exchange s trace t) :
    ∃u,Exec isa body (allocated 3456 (nativeSavedState s)) trace u := by
  obtain ⟨a,tp,tr,rfl,ep,rest⟩:=TimingExchange_seq_parts e
  obtain ⟨hp,ha⟩:=Exec.det ep (native_prologue_exec s)
  subst hp
  subst ha
  obtain ⟨b,tf,te,rfl,ef,tail⟩:=TimingExchange_seq_parts rest
  obtain ⟨c,ts,tn,rfl,es,en⟩:=TimingExchange_seq_parts tail
  obtain ⟨hn,he⟩:=TimingExchange_nil_parts en
  subst hn
  subst he
  obtain ⟨hs,_⟩:=Exec.det es (native_epilogue_exec b)
  subst hs
  have inner:=TimingExchange_alloc_parts (s:=nativeSavedState s) pre.room ef
  simpa only [List.nil_append,List.append_nil] using inner

private theorem TimingExchange_entry_public_of_contract {s t : State} (h : nativeContract.pub s t) : entryPublic s t := by
  sig_pub [nativeContract,Spec.EcKey.P521.inst,Spec.Ecdh.Instance.exchangeContract,
    Spec.Ecdh.Instance.exchangeSig,Spec.P521.curve,Spec.EcKey.scratchWords,abi,argRegs] at h
  obtain ⟨sp,_,g0,g1,g2,g3⟩:=h
  exact ⟨sp,fun r hr => by
    simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact g0
    · exact g1
    · exact g2
    · exact g3⟩

theorem native_exchange_constantTime (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n) :
    ConstantTime isa nativeContract.pre nativeContract.pub exchange := by
  intro a b ta tb a' b' pa pb pub ea eb
  have stackA:=prepare_stack_pre pa
  have stackB:=prepare_stack_pre pb
  obtain ⟨u,ua⟩:=TimingExchange_exchange_body_parts stackA ea
  obtain ⟨v,vb⟩:=TimingExchange_exchange_body_parts stackB eb
  have pubData:=TimingExchange_entry_public_of_contract pub
  have publicSaved : entryPublic (nativeSavedState a) (nativeSavedState b) := pubData
  have preA := prepare_stack_pre (native_pre_saved pa)
  have preB := prepare_stack_pre (native_pre_saved pb)
  exact native_body_traces hc law ha order orderBound preA preB publicSaved ua vb

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config exchange)

private theorem native_post_of {s t : State} (h : VG.Proof.Ecdh.AArch64.EPost config s t) :
    nativeContract.post s t := by
  sig_post [nativeContract,Spec.EcKey.P521.inst,Spec.Ecdh.Instance.exchangeContract,
    Spec.Ecdh.Instance.exchangeSig,Spec.P521.curve,Spec.EcKey.scratchWords,abi,argRegs]
  change VG.Proof.Ecdh.AArch64.EPost config s t
  exact h

 theorem native_verified (law : Law Spec.P521.curve) (inv : InvSounds) (order : PrimeOrder Spec.P521.curve) :
    Verified target exchange nativeContract := by
  have hc : BaseCfgOk config := (VG.Proof.Ecdsa.AArch64.P521.p521_ok inv).toBaseCfgOk
  have ha : AM3 config.C := (VG.Proof.Ecdsa.AArch64.P521.p521_ok inv).am3
  have hn : 17≤config.C.n := by decide +kernel
  refine ⟨?_,native_exchange_constantTime hc law ha order hn,native_contract_satisfiable⟩
  intro s pre
  obtain ⟨trace,t,exec,api,gp,rd,wr,sp⟩ := native_exchange_api_ok hc law ha order pre
  have vec : exchange.allInstrs keepsV=true := by lit_decide
  exact ⟨trace,t,exec,⟨gp,sp,Exec.preservedV exec vec⟩,native_post_of api⟩

end VG.Proof.Weierstrass.AArch64.P521Native
