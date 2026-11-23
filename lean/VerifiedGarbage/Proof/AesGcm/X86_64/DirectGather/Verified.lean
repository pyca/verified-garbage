module
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Call

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.DirectFinish
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Quick
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Short
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Post
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
meta import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Semantics
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Return
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Flagged
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Gather.DirectTail
open VG VG.Impl.AesGcm.X86_64 VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64.DirectGather

abbrev xArgs : List Reg := [.rbx,.rdx,.rsi,.rdi,.r10,.rcx]

theorem xor_check : ∃ hc,(taint.check (Taint.ofRegs xArgs) tailXor hc).isSome=true := ⟨_,by taint_decide⟩

theorem tailLoad_check : ∃ hc,(taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 8))]) hc).isSome=true :=
  ⟨_,by taint_decide⟩

theorem tailRest_check : ∃ hc,(taint.check (Taint.ofRegs [.r11,.r15]) (.block tailArgs.tail) hc).isSome=true :=
  ⟨_,by taint_decide⟩

theorem tailArgs_rel {a : TailArgs} {H₁ H₂ : Spec.Gcm.Block} {s t : State} (p : TailPre a H₁ s) (q : TailPre a H₂ t) :
    RelCT isa (fun x y => x=s ∧ y=t) (.block tailArgs) fun _ _ => True := by
  have wp {u : State} (slot : InRegions (u.rd++u.wr) (u.gpr .rsp+8#64) 8) :
      WP isa (.block [.mov .r11 (.mem (at_ .rsp 8))]) u (Gather.LdF .r11 .rsp 8 u) := by
    refine WP.of_runBlock ⟨_,by xrun [slot],?_⟩
    exact ⟨rfl,fun r h => gpr_setReg_of_ne _ _ h,rfl,rfl,rfl⟩
  refine Gather.rel_ld (l:=tailArgs.tail) (Gather.LdF .r11 .rsp 8) ?_ ?_ ?_
  · rintro _ _ ⟨rfl,rfl⟩
    exact ⟨wp (p.env.rsp ▸ p.stackR),wp (q.env.rsp ▸ q.stackR)⟩
  · refine rel_taint [.rsp] ?_ tailLoad_check
    rintro _ _ ⟨rfl,rfl⟩ r hr
    rw [List.mem_singleton.mp hr,p.env.rsp,q.env.rsp]
  · refine rel_taint [.r11,.r15] (Gather.ld_agree (rs:=[.r15]) ?_ ?_) tailRest_check
    · rintro _ _ ⟨rfl,rfl⟩ r hr
      rw [List.mem_singleton.mp hr,p.env.r15,q.env.r15]
    · rintro _ _ ⟨rfl,rfl⟩
      rw [p.env.rsp,q.env.rsp,p.desc,q.desc]

theorem start_check : ∃ hc,(taint.check (Taint.ofRegs [.r15]) (.block tailStart) hc).isSome=true :=
  ⟨_,by taint_decide⟩

theorem cmp_check : ∃ hc,(taint.check (Taint.ofRegs [.r10,.rbp]) (.block [.alu .cmp .r10 (.reg .rbp)]) hc).isSome=true :=
  ⟨_,by taint_decide⟩

theorem second_check : ∃ hc,(taint.check (Taint.ofRegs [.r11]) (.block secondArgs) hc).isSome=true :=
  ⟨_,by taint_decide⟩

theorem skip_rel {P : State → State → Prop} : RelCT isa P (.block []) fun _ _ => True :=
  rel_taint [] (fun _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩

theorem finish_check (has : Bool) : ∃ hc,(taint.check (Taint.ofRegs [.r14,.r15])
    (.block (Impl.AesGcm.X86_64.Short.finLens ++ (if has then Impl.AesGcm.X86_64.Short.finGh2 else Impl.AesGcm.X86_64.Short.finGh1) ++
      Impl.AesGcm.X86_64.Short.tagK 0)) hc).isSome=true := by
  cases has <;> exact ⟨_,by taint_decide⟩

theorem finish_rel {P : State → State → Prop} {a : TailArgs} (has : Bool)
    (env : ∀ x y,P x y → Env a.ctx (a.work+16#64) a.work a.sp x ∧ Env a.ctx (a.work+16#64) a.work a.sp y) :
    RelCT isa P (.block (Impl.AesGcm.X86_64.Short.finLens ++ (if has then Impl.AesGcm.X86_64.Short.finGh2 else Impl.AesGcm.X86_64.Short.finGh1) ++
      Impl.AesGcm.X86_64.Short.tagK 0)) fun _ _ => True := by
  refine rel_taint _ ?_ (finish_check has)
  intro x y hp r hr
  obtain ⟨e,f⟩ := env _ _ hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact e.r14.trans f.r14.symm
  · exact e.r15.trans f.r15.symm

def rValue (a : TailArgs) (second : Bool) (r : Reg) : Addr :=
  match r with
  | .rbx => if second then a.source2 else a.tail1
  | .rdx => a.work+1040#64
  | .rsi => a.output
  | .rdi => a.work+512#64
  | .r10 => if second then BitVec.ofNat 64 (a.firstLen%16) else 0
  | .rcx => if second then BitVec.ofNat 64 a.remaining else BitVec.ofNat 64 (a.firstLen%16)
  | _ => 0

abbrev XRegs (a : TailArgs) (two : Bool) (s : State) := ∀ r ∈ xArgs,s.gpr r=rValue a two r

theorem TailsStart.xorRegs {a : TailArgs} {s t : State} (b : TailsStart a s t) : XRegs a false t := by
  intro r hr
  simp only [xArgs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  exacts [b.cursors.first,b.key,b.cursors.out,b.auth,b.off,b.cursors.count]

theorem xor_rel {P : State → State → Prop} {a : TailArgs} {two : Bool}
    (regs : ∀ x y,P x y → XRegs a two x ∧ XRegs a two y) : RelCT isa P tailXor fun _ _ => True :=
  rel_taint xArgs (fun _ _ h r hr => ((regs _ _ h).1 r hr).trans ((regs _ _ h).2 r hr).symm) xor_check

theorem firstTail_rel {a : TailArgs} {o₁ o₂ : State} :
    RelCT isa (fun s t => TailsStart a o₁ s ∧ TailsStart a o₂ t) (.ite .e (.block []) tailXor) fun _ _ => True := by
  refine RelCT.ite (fun _ _ h => by simp only [eval,h.1.zf,h.2.zf]) skip_rel ?_
  exact xor_rel (fun _ _ h => ⟨h.1.1.xorRegs,h.1.2.xorRegs⟩)

theorem second_xregs {a : TailArgs} {o s v : State} {H : Spec.Gcm.Block} (p : TailPre a H o)
    (b : TailsStart a o s) (one : SpanAt a.span1 s (a.firstLen%16) v) (pos : 0<a.secondLen) :
    WP isa (.block secondArgs) v (XRegs a true) := by
  obtain ⟨slot,rr⟩ := second_slot p b one pos
  obtain ⟨w,run,_,src,ct,regs,_,_,_⟩ := secondArgs_ok one b.cursors slot rr
  refine WP.of_runBlock ⟨w,run,?_⟩
  intro r hr
  simp only [xArgs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · exact src
  · exact (regs _ (by decide) (by decide)).trans ((one.regs _ (by decide) (by decide) (by decide) (by decide)).trans b.key)
  · exact (regs _ (by decide) (by decide)).trans ((one.regs _ (by decide) (by decide) (by decide) (by decide)).trans b.cursors.out)
  · exact (regs _ (by decide) (by decide)).trans ((one.regs _ (by decide) (by decide) (by decide) (by decide)).trans b.auth)
  · exact (regs _ (by decide) (by decide)).trans (by simpa [rValue] using one.ptr)
  · exact ct

theorem tails_rel {a : TailArgs} {o₁ o₂ s t : State} {H₁ H₂ : Spec.Gcm.Block}
    (p : TailPre a H₁ o₁) (q : TailPre a H₂ o₂) (b : TailsStart a o₁ s) (c : TailsStart a o₂ t) :
    RelCT isa (fun x y => x=s ∧ y=t) tails fun _ _ => True := by
  have first := (firstTail_rel (a:=a) (o₁:=o₁) (o₂:=o₂)).mono (P':=fun x y => x=s ∧ y=t)
    (by rintro x y ⟨hx,hy⟩; subst x; subst y; exact ⟨b,c⟩) (fun _ _ _ => trivial)
  refine RelCT.seq (first.wp (F₁:=SpanAt a.span1 s (a.firstLen%16)) (F₂:=SpanAt a.span1 t (a.firstLen%16))
    (by rintro x y ⟨hx,hy⟩; subst x; subst y; exact ⟨firstTail_ok p b,firstTail_ok q c⟩)) ?_
  let At := fun (s u : State) => SpanAt a.span1 s (a.firstLen%16) u
  let Cmp := fun (s u : State) => At s u ∧ u.zf=some (decide (a.firstLen%16=a.remaining))
  have cmp {x u : State} (cu : TailCursors a x) (h : At x u) : WP isa (.block [.alu .cmp .r10 (.reg .rbp)]) u (Cmp x) := by
    obtain ⟨v,r,k,z⟩ := cmpSecond_ok cu h p.bounded
    exact WP.of_runBlock ⟨v,r,k,z⟩
  have test := rel_taint (P:=fun u v => True ∧ At s u ∧ At t v) _ (fun u v h r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.2.1.ptr.trans h.2.2.ptr.symm
    · rw [h.2.1.regs _ (by decide) (by decide) (by decide) (by decide),h.2.2.regs _ (by decide) (by decide) (by decide) (by decide),
        b.cursors.rem,c.cursors.rem]) cmp_check
  refine RelCT.seq (test.wp (F₁:=Cmp s) (F₂:=Cmp t) (fun _ _ h => ⟨cmp b.cursors h.2.1,cmp c.cursors h.2.2⟩)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval,h.2.1.2,h.2.2.2]) skip_rel ?_
  let P := fun (x y : State) => (True ∧ Cmp s x ∧ Cmp t y) ∧ eval .e x=some false
  have load := rel_taint (P:=P) _ (fun x y h r hr => by
    rw [List.mem_singleton.mp hr,h.1.2.1.1.regs _ (by decide) (by decide) (by decide) (by decide),
      h.1.2.2.1.regs _ (by decide) (by decide) (by decide) (by decide),b.cursors.desc,c.cursors.desc]) second_check
  refine RelCT.seq (load.wp (F₁:=XRegs a true) (F₂:=XRegs a true) (fun x y h => ?_)) ?_
  · have hz := h.2
    simp only [eval,h.1.2.1.2,Option.some.injEq,decide_eq_false_iff_not] at hz
    have pos : 0<a.secondLen := by omega_using [a.counts p.firstLe,hz]
    exact ⟨second_xregs p b h.1.2.1.1 pos,second_xregs q c h.1.2.2.1 pos⟩
  · exact xor_rel (fun _ _ h => h.2)

theorem start_wp {a : TailArgs} {H : Spec.Gcm.Block} {s : State} (p : TailPre a H s) (cu : TailCursors a s) :
    WP isa (.block tailStart) s (TailsStart a s) := by
  obtain ⟨b,run,mb,cb,auth,key,off,zfb,eb,rd,wr,_⟩ := tailStart_ok p.env cu
  refine WP.of_runBlock ⟨b,run,eb,cb,key,auth,off,zfb,?_,rd,wr⟩
  intro pos
  refine ((zero_frame mb).readW (r:=a.secondSlot) (a:=a.secondSlot.base) (w:=64) (by simp [Region.Contains])
    (fun r hr => ?_) (by decide)).trans (p.second pos)
  simp only [List.mem_singleton] at hr
  exact hr ▸ (p.slotWork pos).sub_right (Offset.sub_base a.work (by decide))

theorem branch_rel {a : TailArgs} {H₁ H₂ : Spec.Gcm.Block} {s t : State} (p : TailPre a H₁ s) (q : TailPre a H₂ t)
    (cu : TailCursors a s) (cv : TailCursors a t) (fs : s.zf=some (BitVec.ofNat 64 a.remaining==0))
    (ft : t.zf=some (BitVec.ofNat 64 a.remaining==0)) :
    RelCT isa (fun x y => x=s ∧ y=t)
      (.ite .e (.block (Impl.AesGcm.X86_64.Short.finLens ++ Impl.AesGcm.X86_64.Short.finGh1 ++ Impl.AesGcm.X86_64.Short.tagK 0))
      (.seq (.block tailStart) (.seq tails (.block (Impl.AesGcm.X86_64.Short.finLens ++ Impl.AesGcm.X86_64.Short.finGh2 ++ Impl.AesGcm.X86_64.Short.tagK 0)))))
      fun _ _ => True := by
  refine RelCT.ite (by rintro x y ⟨hx,hy⟩; subst x; subst y; simp only [eval,fs,ft]) ?_ ?_
  · exact finish_rel false (by rintro x y ⟨⟨hx,hy⟩,_⟩; subst x; subst y; exact ⟨p.env,q.env⟩)
  · have st := rel_taint (P:=fun x y => (x=s ∧ y=t) ∧ eval .e x=some false) _ (fun x y h r hr => by
      obtain ⟨⟨hx,hy⟩,_⟩ := h
      subst x; subst y
      rw [List.mem_singleton.mp hr,p.env.r15,q.env.r15]) start_check
    refine RelCT.seq (st.wp (F₁:=TailsStart a s) (F₂:=TailsStart a t)
      (by rintro x y ⟨⟨hx,hy⟩,_⟩; subst x; subst y; exact ⟨start_wp p cu,start_wp q cv⟩)) ?_
    have both : RelCT isa (fun x y => True ∧ TailsStart a s x ∧ TailsStart a t y) tails fun _ _ => True := by
      intro x y tr u v w h e f
      exact tails_rel p q h.2.1 h.2.2 x y tr u v w ⟨rfl,rfl⟩ e f
    refine RelCT.seq (both.wp (F₁:=Env a.ctx (a.work+16#64) a.work a.sp) (F₂:=Env a.ctx (a.work+16#64) a.work a.sp)
      (fun _ _ h => ⟨WP.mono (tails_ok p h.2.1) (fun _ v => v.env),WP.mono (tails_ok q h.2.2) (fun _ v => v.env)⟩)) ?_
    exact finish_rel true (fun _ _ h => h.2)

theorem twoTail_rel {a : TailArgs} {H₁ H₂ : Spec.Gcm.Block} {s t : State} (p : TailPre a H₁ s) (q : TailPre a H₂ t) :
    RelCT isa (fun x y => x=s ∧ y=t) twoTail fun _ _ => True := by
  let A := fun H u => TailPre a H u ∧ TailCursors a u ∧ u.zf=some (BitVec.ofNat 64 a.remaining==0)
  have wp {H : Spec.Gcm.Block} {u : State} (h : TailPre a H u) : WP isa (.block tailArgs) u (A H) := by
    obtain ⟨w,run,pre,c,z,_,_,_⟩ := tailArgs_ok h
    exact WP.of_runBlock ⟨w,run,pre,c,z⟩
  refine RelCT.seq ((tailArgs_rel p q).wp (F₁:=A H₁) (F₂:=A H₂)
    (by rintro x y ⟨hx,hy⟩; subst x; subst y; exact ⟨wp p,wp q⟩)) ?_
  intro x y tr u v w h e f
  obtain ⟨_,⟨px,cx,fx⟩,⟨qy,cy,fy⟩⟩ := h
  exact branch_rel px qy cx cy fx fy x y tr u v w ⟨rfl,rfl⟩ e f

end VG.Proof.AesGcm.X86_64.Gather.DirectTail

namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather Gather.DirectTail Short
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.AesGcm.X86_64.DirectGather (quick firstBlocks)
open VG.Impl.AesGcm.X86_64.Short (finKsA finPowP)

theorem tailArgs_eq {s t : State} (pb : Pub s t) (nz : 0<Cnt s) : tailArgs t=tailArgs s := by
  simp only [tailArgs,K,SP,AL,pb.rdi,pb.rsp,pb.r9,pb.w,pb.src,pb.dst,pb.eL,pb.cnt,pb.sb nz,pb.sl nz]
  by_cases two : 1<Cnt s
  · simp only [two,ite_true,pb.sb two]
  · simp only [two,ite_false]

namespace Layout
variable {th : Nat} {s t : State} (p : Layout (CtxMode.flaggedT th) s) (q : Layout (CtxMode.flaggedT th) t)
include p

theorem initial_a0 {u : State} (ht : 16≤th) (e : Initial s u) (nonce : NL s=12) :
    Fast.A0 CtxMode.prepared16 (K s) (W s) (SP s) (s.gpr .rsi).toNat (Ad s) (AL s).toNat (Dst s) (L s) (Nn s) u :=
  OneEntry.aadPre (nonce ▸ p.oneCtx (CtxMode.flaggedT th).ge) (p.preparedExt ht) e rfl nonce rfl rfl

theorem constants_wp {u m v : State} (nz : 0<Cnt s) (h : WholeDone s u m v) :
    WP isa (.block finPowP) v (KsInputs (K s) (W s) (SP s) (s.gpr .rsi).toNat) := by
  have frame := p.whole_frame (Nat.ne_of_gt nz) h
  have ext := p.ext.keep (h.2.rd.trans h.1.rd) (h.2.wr.trans h.1.wr) frame p.ext_apart
  have rd (i : Nat) (ok : i+16≤1032) := in_off ext.cov ok (show 1032<2^64 by decide)
  obtain ⟨_,_,_,r⟩ := firstMem_slots m.mem (W s) (sb s 0) (Dst s) (L s)
  have rounds := (p.whole_slot nz h (d:=176) (by decide) (by decide)).trans (r.trans h.1.rounds.1)
  refine WP.mono (Fast.finPowP_run v h.2.env.r13 (rd 272 (by decide)) (rd 256 (by decide))) fun z ⟨_,_,_,_,o⟩ => ?_
  exact ⟨h.2.env.keep (fun r hr => o.gpr _ (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> decide)) o.rd o.wr,o.mem ▸ rounds⟩

include q

theorem constants_rel {u m v u' m' v' : State} (pb : Pub s t) (nz : 0<Cnt s)
    (hs : WholeDone s u m v) (ht : WholeDone t u' m' v') :
    RelCT isa (fun x y => x=v ∧ y=v') (.seq (.block finPowP) finKsA) fun _ _ => True := by
  have pow := rel_taint (c:=.block finPowP) (P:=fun x y => x=v ∧ y=v') [.r13] (fun x y h r hr => by
    obtain ⟨hx,hy⟩ := h; subst x; subst y
    rw [List.mem_singleton.mp hr,hs.2.env.r13,ht.2.env.r13]; exact pb.rdi.symm) ⟨_,by taint_decide⟩
  refine RelCT.seq (pow.wp (F₁:=KsInputs (K s) (W s) (SP s) (s.gpr .rsi).toNat)
    (F₂:=KsInputs (K t) (W t) (SP t) (t.gpr .rsi).toNat) (by
      rintro x y ⟨hx,hy⟩; subst x; subst y
      exact ⟨p.constants_wp nz hs,q.constants_wp (pb.cnt ▸ nz) ht⟩)) ?_
  refine finKsA_rel_inputs.mono (fun _ _ h => ⟨h.2.1,?_⟩) (fun _ _ _ => trivial)
  simpa only [K,SP,pb.rdi,pb.rsp,pb.rsi,pb.w] using h.2.2

theorem quick_rel (hf : ShortFacts) (T : BlocksTo.SealFn (CtxMode.flaggedT th)) (ht : 16≤th) (pb : Pub s t)
    {u v : State} (e : Initial s u) (f : Initial t v) (g : frontGo false s=true) :
    RelCT isa (fun x y => x=u ∧ y=v) (quick T.fn) fun _ _ => True := by
  have gt : frontGo false t=true := (pb.eFront false).trans g
  obtain ⟨n,c,al,_⟩ := front_limits (p.front (CtxMode.flaggedT th).ge) g
  have nonce : NL s=12 := by simp [NL,n]
  have nonce' : NL t=12 := by simpa only [NL,pb.rcx] using nonce
  have nz : 0<Cnt s := by omega
  have nz' : 0<Cnt t := pb.cnt ▸ nz
  let C := p.oneCtx (CtxMode.flaggedT th).ge
  have aa := (Fast.aad_rel C.lay C.dE (M:=CtxMode.prepared16) (R:=(s.gpr .rsi).toNat) (Np:=Nn s)
    (A:=Ad s) (al:=(AL s).toNat) al).mono (P':=fun x y => x=u ∧ y=v) (by
      rintro x y ⟨hx,hy⟩; subst x; subst y
      exact ⟨p.initial_a0 ht e nonce,by
        simpa only [K,SP,Ad,AL,Nn,pb.rdi,pb.rsp,pb.r8,pb.r9,pb.rdx,pb.rsi,pb.eL,pb.w,pb.dst] using q.initial_a0 ht f nonce'⟩)
    (fun _ _ _ => trivial)
  have front : RelCT isa (fun x y => x=u ∧ y=v) (.seq Impl.AesGcm.X86_64.Fast.aad (firstBlocks T.fn)) fun _ _ => True := by
    refine RelCT.seq (aa.wp (F₁:=AadDone s u) (F₂:=AadDone t v) (by
      rintro x y ⟨hx,hy⟩; subst x; subst y
      exact ⟨p.aad_wp hf ht e nonce al,q.aad_wp hf ht f nonce' (by simpa only [AL,pb.r9] using al)⟩)) ?_
    intro x y tr tz x' y' h ex ey
    have b := h.2.2
    have be := b.env
    have fa := q.first_args nz' b.frame b.rd b.wr
    have ib := q.inputs b nz'
    simp only [K,SP,pb.rdi,pb.rsp,pb.w] at be
    simp only [SP,pb.rsp,pb.src,pb.dst,pb.sb nz,pb.sl nz,pb.eL] at fa
    simp only [K,SP,pb.rdi,pb.rsp,pb.rsi,pb.w,pb.dst,pb.sb nz,pb.sl nz,pb.eL] at ib
    exact firstBlocks_rel T h.2.1.env be (p.first_args nz h.2.1.frame h.2.1.rd h.2.1.wr) fa (p.inputs h.2.1 nz) ib
      x y tr tz x' y' ⟨rfl,rfl⟩ ex ey
  apply RelCT.assoc
  refine RelCT.seq (front.wp (F₁:=fun x => ∃ m,WholeDone s u m x) (F₂:=fun y => ∃ m,WholeDone t v m y) (by
    rintro x y ⟨hx,hy⟩; subst x; subst y
    exact ⟨p.aad_blocks_wp hf T ht e g,q.aad_blocks_wp hf T ht f gt⟩)) ?_
  apply RelCT.assoc
  let P := fun x y => True ∧ (∃ m,WholeDone s u m x) ∧ ∃ m,WholeDone t v m y
  have const : RelCT isa P (.seq (.block finPowP) finKsA) fun _ _ => True := by
    intro x y tr tz x' y' h ex ey
    obtain ⟨_,⟨m,hs⟩,⟨m',ht'⟩⟩ := h
    exact p.constants_rel q pb nz hs ht' x y tr tz x' y' ⟨rfl,rfl⟩ ex ey
  refine RelCT.seq (const.wp (F₁:=fun x => ∃ H,TailPre (tailArgs s) H x) (F₂:=fun y => ∃ H,TailPre (tailArgs t) H y)
    (fun x y h => ?_)) ?_
  · obtain ⟨_,⟨m,hs⟩,⟨m',ht'⟩⟩ := h
    exact ⟨WP.mono (p.key_schedule hf ht g hs) (fun _ h => ⟨_,h.1⟩), WP.mono (q.key_schedule hf ht gt ht') (fun _ h => ⟨_,h.1⟩)⟩
  · intro x y tr tz x' y' h ex ey
    obtain ⟨_,⟨H,px⟩,⟨H',qy⟩⟩ := h
    rw [tailArgs_eq pb nz] at qy
    exact twoTail_rel px qy x y tr tz x' y' ⟨rfl,rfl⟩ ex ey

end Layout
end VG.Proof.AesGcm.X86_64.DirectGather

namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.X86_64.RegUpd Gather
open VG.Impl.AesGcm.X86_64 (at_ oneEntry saved)
open VG.Impl.AesGcm.X86_64.DirectGather (dispatch enter quick)
open VG.Impl.AesGcm.X86_64.SealGather (frontCore frontTest)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

namespace Layout
variable {M : CtxMode} {s t : State} (p : Layout M s) (q : Layout M t)
include p

theorem entry_after_test {u : State} (h : Gather.Same s u) : WP isa (.block (oneEntry 48 24 32)) u (Initial s) := by
  have c := p.oneCtx M.ge
  have sp := same_rsp h
  have rd := h.rd
  have wr := h.wr
  have regs := h.gpr
  have args (i : Nat) : stackArg u i=stackArg s i := by simp only [stackArg,stackArgAddr,h.mem,sp]
  have si := regs .rsi (by decide) (by decide) (by decide)
  have c' : OneCtx u 6 (K s) (W s) (SP s) (Nn s) (Ad s) (Dst s) (NL s) (AL s).toNat (L s) :=
    {c with
      perm := c.perm.of_eq rd wr
      args := by rw [rd,wr]; exact c.args
      nonce := c.nonce.of_eq rd wr
      aad := c.aad.of_eq rd wr
      data := c.data.of_eq rd wr
      rounds := by rw [si]; exact c.rounds}
  refine WP.mono (oneEntryAt_okL (id:=2) (il:=3) (by decide) (by decide) c'
    (regs _ (by decide) (by decide) (by decide)) sp (regs _ (by decide) (by decide) (by decide))
    (args 2) (congrArg BitVec.toNat (args 3)) (by rw [h.mem]; rfl) (c'.args 5 (by decide))) fun z ⟨e,_⟩ => ?_
  refine ⟨e.env,si ▸ e.rounds,e.aad,e.alen.trans (regs _ (by decide) (by decide) (by decide)),e.dat,e.len,
    e.r12.trans (regs _ (by decide) (by decide) (by decide)),e.rbp.trans (regs _ (by decide) (by decide) (by decide)),
    e.rsp,?_,h.mem ▸ e.frame,e.rd.trans rd,e.wr.trans wr⟩
  intro v hv
  apply (e.saved _ hv).trans
  simp only [saved,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl <;> exact regs _ (by decide) (by decide) (by decide)

theorem enter_wp {pr : Prog isa} {P : State → Prop} {u : State} (h : Gather.Same s u)
    (k : ∀ v,Initial s v → WP isa pr v P) : WP isa (enter pr) u P :=
  WP.seq (WP.mono (p.entry_after_test h) k)

include q

theorem entry_rel {u v : State} (pb : Pub s t) (a : Gather.Same s u) (b : Gather.Same t v) :
    RelCT isa (fun x y => x=u ∧ y=v) (.block (oneEntry 48 24 32)) fun _ _ => True := by
  have load {x : State} (rr : InRegions (x.rd++x.wr) (x.gpr .rsp+48#64) 8) :
      WP isa (.block [.mov .rax (.mem (at_ .rsp 48))]) x (LdF .rax .rsp 48 x) := by
    refine WP.of_runBlock ⟨_,by xrun [rr],?_⟩
    exact ⟨rfl,fun r hr => gpr_setReg_of_ne _ _ hr,rfl,rfl,rfl⟩
  have ag : ∀ x y : State,x=u ∧ y=v → ∀ r ∈ [Reg.rsp],x.gpr r=y.gpr r := by
    rintro x y ⟨hx,hy⟩ r hr; subst x; subst y
    rw [List.mem_singleton.mp hr,same_rsp a,same_rsp b,pb.rsp]
  refine rel_ld (l:=(oneEntry 48 24 32).tail) (LdF .rax .rsp 48) ?_ (rel_taint [.rsp] ag ⟨_,by taint_decide⟩) ?_
  · rintro x y ⟨hx,hy⟩; subst x; subst y
    exact ⟨load (by rw [a.rd,a.wr,same_rsp a]; exact (p.oneCtx M.ge).args 5 (by decide)),
      load (by rw [b.rd,b.wr,same_rsp b]; exact (q.oneCtx M.ge).args 5 (by decide))⟩
  · refine rel_taint [.rax,.rsp] (ld_agree ag ?_) ⟨_,by taint_decide⟩
    rintro x y ⟨hx,hy⟩; subst x; subst y
    rw [a.mem,b.mem,same_rsp a,same_rsp b]
    exact pb.w.symm

theorem enter_rel {pr : Prog isa} {u v : State} (pb : Pub s t) (a : Gather.Same s u) (b : Gather.Same t v)
    (k : ∀ x y,Initial s x → Initial t y → RelCT isa (fun z w => z=x ∧ w=y) pr fun _ _ => True) :
    RelCT isa (fun x y => x=u ∧ y=v) (enter pr) fun _ _ => True := by
  refine RelCT.seq ((p.entry_rel q pb a b).wp (F₁:=Initial s) (F₂:=Initial t) (by
    rintro x y ⟨hx,hy⟩; subst x; subst y
    exact ⟨p.entry_after_test a,q.entry_after_test b⟩)) ?_
  intro x y tr tz x' y' h ex ey
  exact k x y h.2.1 h.2.2 x y tr tz x' y' ⟨rfl,rfl⟩ ex ey

omit q in
theorem dispatch_wp {fast slow : Prog isa} {P : State → Prop}
    (good : ∀ u, Initial s u → frontGo false s=true → WP isa fast u P)
    (other : ∀ u, Initial s u → WP isa slow u P) : WP isa (dispatch fast slow) s P := by
  apply WP.seq
  refine WP.mono (frontTest_wp (p.front M.ge) false) fun u ⟨same,flag⟩ => ?_
  refine WP.ite (frontGo false s) (by simp only [eval,flag]) (fun go => p.enter_wp same (fun v e => good v e go))
    (fun _ => p.enter_wp same other)

theorem dispatch_rel {fast slow : Prog isa} (pb : Pub s t)
    (good : ∀ u v, Initial s u → Initial t v → frontGo false s=true →
      RelCT isa (fun x y => x=u ∧ y=v) fast fun _ _ => True)
    (other : ∀ u v, Initial s u → Initial t v → RelCT isa (fun x y => x=u ∧ y=v) slow fun _ _ => True) :
    RelCT isa (fun x y => x=s ∧ y=t) (dispatch fast slow) fun _ _ => True := by
  refine RelCT.seq (frontTest_rel (p.front M.ge) (q.front M.ge) pb false) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval,h.1.2,h.2.2,pb.eFront]) ?_ ?_
  · intro x y tr tz x' y' h ex ey
    have go := h.2
    simp only [eval,h.1.1.2,Option.some.injEq] at go
    exact p.enter_rel q pb h.1.1.1 h.1.2.1 (fun _ _ a b => good _ _ a b go) x y tr tz x' y' ⟨rfl,rfl⟩ ex ey
  · intro x y tr tz x' y' h ex ey
    exact p.enter_rel q pb h.1.1.1 h.1.2.1 other x y tr tz x' y' ⟨rfl,rfl⟩ ex ey

end Layout
end VG.Proof.AesGcm.X86_64.DirectGather


/-! Allocate the private 2560-byte working area inside the existing gather API's stack budget. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

def workSig (words : Nat) : Sig where
  params := [("ctx", .array false .u64 words), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16), ("scratch", .array true .u64 320)]

abbrev Condition := Addr → Addr → Addr → Addr → Addr → Mem → Prop

def workContract (words : Nat) (P : Condition) : Contract isa :=
  (workSig words).contract X86_64.abi
    (pre := fun ctx rounds _ _ _ _ src cnt _ len _ _ => P ctx rounds src cnt len)
    (post := fun ctx rounds nonce nl aad al src cnt dst len tag _ =>
      Proof.AesGcm.sealGatherRoundsPost 64 ctx rounds nonce nl aad al src cnt dst len tag)
    (writeArgs := true) (stack := 2512)

abbrev plainCondition : Condition := fun ctx rounds src cnt len =>
  Spec.Gcm.sealGatherPre 64 ctx rounds 0 0 0 0 src cnt 0 len 0

abbrev readyCondition (threshold : Nat) : Condition := fun ctx rounds src cnt len =>
  Proof.AesGcm.Flag.sealGatherFlaggedPre threshold 64 ctx rounds 0 0 0 0 src cnt 0 len 0

theorem layout_of_work {M : CtxMode} {words : Nat} {P : Condition} {s : State}
    (nwords : M.len = words * 8)
    (valid : P (K s) (s.gpr .rsi) (Src s) (stackArg s 1) (stackArg s 3) s.mem →
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) ∧
      gl s (Cnt s) = L s ∧ M.ok s.mem (K s))
    (h : (workContract words P).pre s) : Layout M s := by
  sig_pre [workContract, workSig, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or,
    List.cons_append, Sig.descRegion] at h
  sig_split h
  rename_i w₁ w₂ rd wr g₁ _ _ _ rdd rt rW g₂ ok on oa od ot ow g₃
  sig_split g₁
  rename_i kd kt kw nd nt nw ad at_ aw dt dw dds dd tw tds tt wds wl
  sig_split g₂
  rename_i _ _ bk bn ba bd bt bw bds bl
  obtain ⟨dl, da⟩ := dd
  obtain ⟨tl, ta⟩ := tt
  obtain ⟨ods, ol⟩ := g₃
  obtain ⟨hr, hg, hpw⟩ := valid h
  simp only [show (2 * (64 / 8) : Nat) = 16 from rfl] at *
  have ar : stackArgAddr s 0 = SP s + 8#64 := by simp [stackArgAddr, SP]
  rw [ar] at rd da ta g₁

  refine ⟨?_, wr, ?_, ?_, ?_, nd, nt, nw, ad, at_, aw, dds.symm, tds.symm, wds.symm,
    fun r h' => ⟨(dl r h').symm, (tl r h').symm, (wl r h').symm⟩, dt, dw, tw, da, ta, g₁,
    rdd, rt, rW, ?_, bn, ba, bds, bl, bd, bt, bw, ?_, on, oa, ods, ol, od, ot, ow,
    w₁, w₂, hr, hg, hpw⟩
  · change s.rd = [⟨K s, M.len⟩, _, _, _] ++ _ ++ _
    rw [nwords]
    exact rd
  · rw [kR, nwords]; exact kd
  · rw [kR, nwords]; exact kt
  · rw [kR, nwords]; exact kw
  · rw [kR, nwords]; exact bk
  · rw [nwords]; exact ok

theorem post_of_work {words : Nat} {P : Condition} {s u : State} (h : Proof.AesGcm.sealGatherPostG s u) :
    (workContract words P).post s u := by
  sig_post [workContract, workSig, Proof.AesGcm.sealGatherRoundsPost,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
  exact fun _ _ => h

theorem pub_of_work {words : Nat} {P : Condition} {s t : State} (hp : (workContract words P).pub s t) :
    Proof.AesGcm.sealGatherPub s t := by
  sig_pub_keep [workContract, workSig, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, qMd, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, fun i hi => hd i (by simpa using hi), qMd⟩

abbrev workSat (s : State) : State := {s with wr := [⟨0, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]}

theorem plain_work_sat : ∃ s, (workContract 32 plainCondition).pre s := by
  sig_implies_sat [workContract, workSig, plainCondition, Spec.Gcm.sealGatherPre,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
    [workSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using workSat gatherSat

theorem ready_work_sat {t : Nat} (ht : t ≤ 48) : ∃ s, (workContract 129 (readyCondition t)).pre s := by
  refine ⟨workSat gatherSatF, ?_⟩
  sig_pre [workContract, workSig, readyCondition, Proof.AesGcm.Flag.sealGatherFlaggedPre,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq,
    workSat, gatherSatF, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.Flag.flaggedPowers_of_zeroMem ht
        (fun _ hi => by simp only [Proof.AesGcm.Flag.ctx_ne1024 hi, ctx_lowF (Nat.lt_of_lt_of_le hi (by decide)), ite_false])
        (by decide)

abbrev Finished (p : Prog isa) : Prog isa :=
  .seq p (.block (Impl.AesGcm.X86_64.tagOut (Impl.AesGcm.X86_64.at_ .rsp 40) ++ Impl.AesGcm.X86_64.restore))

theorem work_verified {p : Prog isa} {M : CtxMode} {words : Nat} {P : Condition}
    (layouts : ∀ s, (workContract words P).pre s → Layout M s)
    (sat : ∃ s, (workContract words P).pre s)
    (body : ∀ {s}, Layout M s → WP isa p s (BodyDone M s))
    (timing : ∀ {s t}, Layout M s → Layout M t → Pub s t →
      RelCT isa (fun a b => a = s ∧ b = t) p (fun _ _ => True))
    (mx : (Finished p).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (Finished p) (workContract words P) := by
  refine ⟨fun s hs => ?_, fun s t _ _ _ _ hs ht pub e f => ?_, sat⟩
  · have h := layouts s hs
    obtain ⟨tr, z, run, regs, post⟩ := WP.seq (WP.mono (body h) fun _ done => return_wp h done)
    exact ⟨tr, z, run, abiPreserved_of_exec mx run regs, post_of_work post⟩
  · have h := layouts s hs
    have k := layouts t ht
    have pb := Pub.of (pub_of_work pub)
    have stage := (timing h k pb).wp (F₁ := BodyDone M s) (F₂ := BodyDone M t) (by
      rintro x y ⟨rfl, rfl⟩
      exact ⟨body h, body k⟩)
    exact (RelCT.seq stage ((return_rel h k pb).mono (fun _ _ z => z.2) (fun _ _ z => z))
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e f).1

abbrev Functional (M : CtxMode) (p : Prog isa) :=
  ∀ {s}, Layout M s → WP isa p s (BodyDone M s)

abbrev Timing (M : CtxMode) (p : Prog isa) :=
  ∀ {s t}, Layout M s → Layout M t → Pub s t →
    RelCT isa (fun a b => a = s ∧ b = t) p (fun _ _ => True)

structure CoreSafe (p : Prog isa) : Prop where
  sp : (Finished p).all (fun i => !isa.writesSp i) = true
  depth : (Finished p).x86_64Depth ≤ 2512
  mx : (Finished p).allInstrs (fun i => !loadsMxcsr i) = true

theorem plain_framed {p : Prog isa} (body : Functional CtxMode.base p) (ct : Timing CtxMode.base p)
    (guard : CoreSafe p) : Verified X86_64.target (Impl.AesGcm.X86_64.DirectGather.framed p)
      (Proof.AesGcm.sealGatherRoundsContract X86_64.abi 5128) := by
  apply X86_64.Verified.stackArgScratchL (sig := Spec.Gcm.sealGatherSig) (nm := "scratch")
    (e := .u64) (n := 320) (pre := Spec.Gcm.sealGatherPre 64) (post := Proof.AesGcm.sealGatherRoundsPost 64)
    (wa := true) (stack := 2512) (bytes := 2616) (hpostOut := fun vs m a b r hl _ hb _ =>
      (Proof.AesGcm.sealGatherPostOut_local _) vs m a b r hl hb) _ (by decide) (by decide) (by decide)
    guard.sp guard.depth (Proof.AesGcm.sealGatherPre_local _) (Proof.AesGcm.sealGatherPost_local _) gatherFrameSat_pre
  apply work_verified (words := 32) (P := plainCondition) _ plain_work_sat body ct guard.mx
  intro s h
  apply layout_of_work (words := 32) (nwords := rfl) _ h
  intro v
  exact ⟨v.1, v.2, trivial⟩

theorem ready_framed {t : Nat} (ht : t ≤ 48) {p : Prog isa}
    (body : Functional (CtxMode.flaggedT t) p) (ct : Timing (CtxMode.flaggedT t) p) (guard : CoreSafe p) :
    Verified X86_64.target (Impl.AesGcm.X86_64.DirectGather.framed p)
      (Proof.AesGcm.Flag.sealGatherFlaggedRoundsContract t X86_64.abi 5128) := by
  apply X86_64.Verified.stackArgScratchL (sig := Spec.Gcm.sealGatherPreparedSig) (nm := "scratch")
    (e := .u64) (n := 320) (pre := Proof.AesGcm.Flag.sealGatherFlaggedPre t 64)
    (post := Proof.AesGcm.sealGatherRoundsPost 64) (wa := true) (stack := 2512) (bytes := 2616)
    (hpostOut := fun vs m a b r hl _ hb _ => (Proof.AesGcm.Flag.sealGatherFlaggedPostOut_local _) vs m a b r hl hb)
    _ (by decide) (by decide) (by decide) guard.sp guard.depth (Proof.AesGcm.Flag.sealGatherFlaggedPre_local _ _)
    (Proof.AesGcm.Flag.sealGatherFlaggedPost_local _) (gatherFrameSatFlagged_pre ht)
  apply work_verified (words := 129) (P := readyCondition t) _ (ready_work_sat ht) body ct guard.mx
  intro s h
  exact layout_of_work rfl (fun v => v) h

end VG.Proof.AesGcm.X86_64.DirectGather

/-! The prepared two-fragment path seals exactly the plaintext listed by the caller. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather.Layout
open VG VG.X86_64 Gather Gather.DirectTail Short
open VG.Impl.AesGcm.X86_64.DirectGather (quick)
open VG.Spec.Gcm (Block blockAt inc32 gctr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

theorem quick_wp {th : Nat} {s u : State} (h : Layout (CtxMode.flaggedT th) s) (hf : ShortFacts)
    (T : BlocksTo.SealFn (CtxMode.flaggedT th)) (ht : 16≤th) (e : Initial s u) (g : frontGo false s=true) :
    WP isa (quick T.fn) u (BodyDone (CtxMode.flaggedT th) s) := by
  obtain ⟨nonce,count,_,_⟩ := front_limits (h.front (CtxMode.flaggedT th).ge) g
  have nz : 0<Cnt s := by omega
  have hn : NL s=12 := by simp [NL,nonce]
  apply WP.seq_assoc
  refine WP.seq (WP.mono (h.aad_blocks_wp hf T ht e g) fun v ⟨m,whole⟩ => ?_)
  apply WP.seq_assoc
  refine WP.seq (WP.mono (h.key_schedule hf ht g whole) fun k ⟨pre,mask,ks,keys,kr,kw⟩ => ?_)
  refine WP.mono (twoTail_ok pre) fun t done => ?_
  let a := tailArgs s
  have le : a.consumed ≤ L s := Nat.le_trans (Nat.mul_div_le ..) pre.firstLe
  have len : a.consumed+a.remaining=L s := Nat.add_sub_of_le le
  have wf := h.whole_frame (Nat.ne_of_gt nz) whole
  have wk : (⟨W s+1024#64,64⟩ : Region).Sub ⟨W s,2560⟩ := Lay.wSub (by decide)
  have fk := wf.trans (keys.sub (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst r; exact ⟨_,List.mem_cons_self ..,wk⟩))
  have outSub : a.outR.Sub (dR s) := Offset.sub_base _ (Nat.le_of_eq len)
  have pref : (⟨Dst s,a.consumed⟩ : Region).Sub (dR s) := Region.sub_prefix le
  have prWork := h.d_w.sub_left pref
  have lim : L s≤2^64 := Nat.le_of_lt (BitVec.isLt _)
  have preLim : (tailArgs s).consumed ≤ 2^64 := Nat.le_trans le lim
  have prOut : (⟨Dst s,a.consumed⟩ : Region).Disjoint a.outR := Offset.disjoint_base (Dst s) (Nat.le_refl _) (len ▸ lim) |>.symm
  have fPre : qDst s t=qDst s v := by
    refine (bytesAt_frame done.frame (fun r hr => ?_) preLim).trans
      (bytesAt_frame keys (fun r hr => ?_) preLim)
    · simp only [finalFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      exacts [prWork.sub_right (Region.sub_prefix (by decide)),prWork.sub_right (Lay.wSub (by decide)),prOut]
    · simp only [List.mem_singleton] at hr
      subst r; exact prWork.sub_right wk
  have full : bytesAt t.mem (Dst s) (L s)=qDst s v ++ a.cipherBytes k.mem := by
    calc
      _ = bytesAt t.mem (Dst s) (a.consumed+a.remaining) := by rw [len]
      _ = _ := by rw [bytesAt_add]; exact (congrArg (fun x => x ++ _) fPre).trans (congrArg (fun x => _ ++ x) done.data)
  obtain ⟨c,ctr,y,j,saved⟩ := h.whole_summary nz whole
  obtain ⟨hash,cipherFn⟩ := h.ctx_framed wf (R:=(s.gpr .rsi).toNat) (by omega_using [h.rounds])
  have eqFn : ciphOf v.mem (K s) (s.gpr .rsi).toNat=qCiph s := cipherFn
  rw [eqFn,ctr] at ks
  rw [eqFn,j] at mask
  have ct := cipher_suffix a (qCiph s) (inc32 (qJ s)) k.mem pre.firstLe pre.bounded (by
    simpa only [add_ofNat_ofNat] using ks)
  have sr (p : Addr) (n : Nat) (sub : (⟨p,n⟩ : Region).Sub ⟨sb s 0,sl s 0⟩) (b : n≤2^64) :=
    bytesAt_frame fk (fun r hr => (h.slice_apart nz r hr).sub_left sub) b
  have sr0 := sr _ _ (Region.sub_prefix (Nat.mul_div_le (sl s 0) 16)) (by omega_using [show sl s 0<2^64 from BitVec.isLt _])
  have sR : (savedR (W s)).Sub ⟨W s,2560⟩ := Lay.wSub (by decide)
  have sk := saved.frame keys (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst r; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  refine ⟨done.env,done.rd.trans (kr.trans (whole.2.rd.trans whole.1.rd)),
    done.wr.trans (kw.trans (whole.2.wr.trans whole.1.wr)),sk.frame done.frame ?_,fk.trans (done.frame.sub ?_),?_,?_⟩
  · intro r hr
    simp only [finalFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact (h.d_w.symm.sub_left sR).sub_right outSub
  · intro r hr
    simp only [finalFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,Region.sub_prefix (by decide)⟩
    · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨dR s,by simp [changed],outSub⟩
  · rw [full,h.prefix_text fk count,Proof.Gcm.gctr_eq,Proof.Gcm.xorKs_append,c,ct,sr0,length_bytesAt,Nat.zero_add]
    simp only [icb,iv,hn]; rfl
  · have yy := blockAt_frame (p:=Split.yA (W s)) keys (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      simp only [Split.yA,add_ofNat_ofNat]
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
    have al := length_bytesAt s.mem (Ad s) (AL s).toNat
    have cl := length_bytesAt v.mem (Dst s) a.consumed
    have tl := cipher_length (m:=k.mem) pre.firstLe
    have ta := done.tag
    change blockAt t.mem (W s)=Spec.Gcm.ghashFrom (Spec.Gcm.ctxH v.mem (K s)) (blockAt k.mem (Split.yA (W s))) _ ^^^ blockAt k.mem (W s+1024#64) at ta
    rw [hash,yy,y,mask] at ta
    have mix := auth_suffix (qH s) (qAad s) (qDst s v) (a.cipherBytes k.mem)
      (by change (bytesAt v.mem (Dst s) a.consumed).length%16=0; rw [cl]; exact Nat.mul_mod_right ..)
      (by rw [tl]; exact pre.bounded)
    change (qAad s).length=(AL s).toNat at al
    change (qDst s v).length=a.consumed at cl
    change (a.cipherBytes k.mem).length=a.remaining at tl
    simp only [al,cl,tl,len] at mix
    rw [Short.bytesAt_toBytes',ta,Proof.Gcm.fullTag_eq,full]
    change _=Spec.Gcm.toBytes (_ ^^^ (ciph s) (Spec.Gcm.j0 (hk s) (iv s)))
    rw [show iv s=qIv s by simp only [iv,qIv,hn]]
    apply congrArg (fun z => Spec.Gcm.toBytes (z ^^^ (qCiph s) (qJ s)))
    simpa only [authBlocks,qAad,ad,length_bytesAt] using mix

end VG.Proof.AesGcm.X86_64.DirectGather.Layout

/-! Link direct encryption of a TLS-shaped or arbitrary record to the exported gather contract. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Impl.AesGcm.X86_64 (Fn Callees)
open VG.Impl.AesGcm.X86_64.DirectGather (plain prepared general enter quick dispatch)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)

structure InitializedProof (M : CtxMode) (body : Prog isa) : Prop where
  run : ∀ {s u}, Layout M s → Layout.Initial s u → WP isa body u (BodyDone M s)
  rel : ∀ {s t u v}, Layout M s → Layout M t → Pub s t → Layout.Initial s u → Layout.Initial t v →
    RelCT isa (fun x y => x = u ∧ y = v) body (fun _ _ => True)

theorem plain_rounds {c : Callees} {ctr : Fn} (h : InitializedProof CtxMode.base (general c ctr none))
    (safe : CoreSafe (enter (general c ctr none))) :
    Verified X86_64.target (plain c ctr) (Proof.AesGcm.sealGatherRoundsContract X86_64.abi 5128) :=
  plain_framed (fun p => p.enter_wp (Gather.Same.refl _) (fun _ e => h.run p e))
    (fun p q pb => p.enter_rel q pb (Gather.Same.refl _) (Gather.Same.refl _) (fun _ _ e f => h.rel p q pb e f)) safe

theorem prepared_rounds {t : Nat} (ht : 16 ≤ t) (hn : t ≤ 48) (hf : ShortFacts)
    {c : Callees} {ctr : Fn} (T : BlocksTo.SealFn (CtxMode.flaggedT t))
    (h : InitializedProof (CtxMode.flaggedT t) (general c ctr (some T.fn)))
    (safe : CoreSafe (dispatch (quick T.fn) (general c ctr (some T.fn)))) :
    Verified X86_64.target (prepared c ctr T.fn) (Proof.AesGcm.Flag.sealGatherFlaggedRoundsContract t X86_64.abi 5128) :=
  ready_framed hn (fun p => p.dispatch_wp (fun _ e g => p.quick_wp hf T ht e g) (fun _ e => h.run p e))
    (fun p q pb => p.dispatch_rel q pb (fun _ _ e f g => p.quick_rel q hf T ht pb e f g)
      (fun _ _ e f => h.rel p q pb e f)) safe

theorem plain_public {p : Prog isa} (h : Verified X86_64.target p (Proof.AesGcm.sealGatherRoundsContract X86_64.abi 5128)) :
    Verified X86_64.target p (Spec.Gcm.sealGatherPreparedApi.contract X86_64.abi 5128) :=
  Proof.AesGcm.Flag.sealGather_keyed (Flag.sealGather_of_base h)

theorem prepared_public {a b : Prog isa} {t : Nat} (ht : t = 16 ∨ t = 48)
    (ha : Verified X86_64.target a (Proof.AesGcm.Flag.sealGatherFlaggedRoundsContract t X86_64.abi 5128))
    (hb : Verified X86_64.target b (Proof.AesGcm.sealGatherRoundsContract X86_64.abi 5128)) :
    Verified X86_64.target (Impl.Gcm.X86_64.Flag.onFlag t a b) (Spec.Gcm.sealGatherPreparedApi.contract X86_64.abi 5128) :=
  Proof.AesGcm.Flag.sealGather_keyed (Flag.sealGather_onFlagF ht ha hb)

end VG.Proof.AesGcm.X86_64.DirectGather
