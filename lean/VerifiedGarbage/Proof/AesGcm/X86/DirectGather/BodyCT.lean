module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.TagBridge
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Setup
public import VerifiedGarbage.Proof.Framework.X86.Rel2
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.TextCT
public import VerifiedGarbage.Proof.AesGcm.X86.Open
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86.Gather.LoopCT
meta import VerifiedGarbage.Impl.AesGcm.X86
meta import VerifiedGarbage.Impl.AesGcm.X86.DirectGather
meta import VerifiedGarbage.Proof.AesGcm.X86.Open
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.TCB.X86.State

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Impl.AesGcm.X86.DirectGather (body frameArgs sourceSlot)

theorem Prepared.publicArgs {s t e f : State} (h : Prepared s e) (k : Prepared t f)
    (hp : Gather.gatherPub s t) : pubN 12 e f := by
  have sp : SP s = SP t := congrArg (· - 2612#32) hp.1
  refine ⟨(h.regs _ (by decide)).trans (sp.trans (k.regs .esp (by decide)).symm),?_⟩
  intro i hi
  by_cases last : i = 11
  · subst i
    rw [h.scratch,k.scratch]
    exact congrArg (· + 52#32) sp
  · rw [h.arg_eq i (by omega),k.arg_eq i (by omega)]
    apply hp.2.1
    unfold sourceSlot
    split <;> (first | split <;> omega | omega)

theorem sealGather_ct_of_body (v : GcmImpl)
    (hb : ∀ s t e f, Gather.Lay s → Gather.Lay t → Gather.gatherPub s t →
      Prepared s e → Prepared t f → RelCT isa (Eq2 e f) (body v.callees) TT) :
    ConstantTime isa Gather.gatherPre Gather.gatherPub (Impl.AesGcm.X86.DirectGather.sealGather v.callees) := by
  apply ct_of
  intro s t hs ht hp
  obtain ⟨e,run,h⟩ := prepare_run (Gather.lay hs)
  obtain ⟨f,run',k⟩ := prepare_run (Gather.lay ht)
  apply Gather.rel_alloc
  intro a b lt rt a' b' he e₁ e₂
  obtain ⟨rfl,rfl⟩ := he
  cases e₁ with
  | seq p q =>
    cases e₂ with
    | seq p' q' =>
      obtain ⟨rfl,rfl⟩ := Option.some.inj (run.symm.trans (Exec.block_iff.mp p))
      obtain ⟨rfl,rfl⟩ := Option.some.inj (run'.symm.trans (Exec.block_iff.mp p'))
      obtain ⟨te,_⟩ := hb _ _ _ _ (Gather.lay hs) (Gather.lay ht) hp h k _ _ _ _ _ _ ⟨rfl,rfl⟩ q q'
      exact ⟨by rw [show SP s = SP t from congrArg (· - 2612#32) hp.1,te],trivial⟩

theorem DescEq.of_bytes {a : Text} {m n : Mem} (fit : a.Src.toNat+a.count*8 ≤ 2^32)
    (eq : ∀ j<a.count*8, m (w64 a.Src+BitVec.ofNat 64 j) = n (w64 a.Src+BitVec.ofNat 64 j)) :
    DescEq a m n :=
  fun _ hi => ⟨Gather.sb_agree fit eq hi,Gather.sl_agree fit eq hi⟩

private theorem fixedCT {P : State → Prop} {c : Prog isa} {s t : State}
    (ct : CT P c) (hs : P s) (ht : P t) : RelCT isa (Eq2 s t) c TT :=
  RelCT.mono ct (fun _ _ ⟨rfl,rfl⟩ => ⟨hs,ht⟩) fun _ _ _ => trivial

theorem tagSuffix_rel (v : GcmImpl) {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
    {e f x y : State} {T : BitVec 32} (a : OTIn p e x) (b : OTIn p f y)
    (tx : arg e 8 = T) (ty : arg f 8 = T) (fx : T.toNat + 16 ≤ 2^32)
    (wx : Covers [⟨w64 T,16⟩] e.wr) (wy : Covers [⟨w64 T,16⟩] f.wr) :
    RelCT isa (Eq2 x y) (.seq (oneTag v.callees 0) (.seq (tagOut 0) (.block restore))) TT := by
  have tag := oneTag_pc (vg := v) G (o := 0) (.inl rfl)
  refine rel_seq (fixedCT tag.ct ⟨(e,x),a,rfl⟩ ⟨(f,y),b,rfl⟩)
    (tag.wp (e,x) x ⟨a,rfl⟩) (tag.wp (f,y) y ⟨b,rfl⟩) ?_
  intro u w hu hw
  let P := fun s => WEnv (p.2 8) s ∧ slotv s.mem (p.2 8) tpO = T
  have ux : P u := ⟨⟨hu.1.env.ebp,hu.1.env.wW,G.L.fw⟩,hu.1.tp.trans tx⟩
  have uy : P w := ⟨⟨hw.1.env.ebp,hw.1.env.wW,G.L.fw⟩,hw.1.tp.trans ty⟩
  refine rel_seq (fixedCT (tagOut_ct (I := P) rfl (fun _ h => h)) ux uy)
    (tagOut_ok ux.1 (by decide) ux.2 (hu.1.wr ▸ wx) fx)
    (tagOut_ok uy.1 (by decide) uy.2 (hw.1.wr ▸ wy) fx) ?_
  intro u' w' hu' hw'
  apply rel_taint [.ebp] _ ⟨_,by taint_decide⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [hu'.2.2.1,hw'.2.2.1,ux.1.ebp,uy.1.ebp]

theorem entry_pc {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p) :
    Pc (fun (e : State) s => OP 12 11 e ∧ pubSw 12 8 e=p ∧ s=e)
      (oneEntry 11 (keep 8 tpO)) (OEnt p) := by
  have pc := oneEntry_pc 12 11 rfl (by decide) [(8,tpO)] (by decide) (by decide) (by simp)
    (OP 12 11) (fun _ h => h) p G (by taint_decide) (by taint_decide)
  simpa using pc.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem setupEnv {s e u : State} {p : BitVec 32 × (Nat → BitVec 32)} (l : Gather.Lay s)
    (hp : Prepared s e) (eq : pubSw 12 8 e=p) (bp : u.gpr .ebp=p.2 8)
    (sp : u.gpr .esp=p.1) (rd : u.rd=e.rd) (wr : u.wr=e.wr) : KeepEnv (work s) (SP s) 12 u := by
  have op := hp.op l
  have w : arg e 11 = work s := hp.scratch
  have k : e.gpr .esp=SP s := hp.regs _ (by decide)
  have pW := pubSw_W eq (m:=11) (by decide) rfl
  have ps := pubSw_esp eq
  rw [←w,←k]
  exact ⟨bp.trans pW.symm,sp.trans ps.symm,wr ▸ op.wW,by rw [rd,wr]; exact op.argR,
    op.w_a.symm,op.fg,op.fw⟩

theorem text_eq {s t : State} (h : Gather.gatherPub s t) : text s=text t := by
  simp only [text,Gather.K,work,SP,Gather.Src,Gather.Dst,Gather.Cnt,Gather.L,
    h.1,h.2.1 0 (by decide),h.2.1 1 (by decide),h.2.1 6 (by decide),h.2.1 7 (by decide),
    h.2.1 8 (by decide),h.2.1 9 (by decide)]

theorem pieces_from_start (v : GcmImpl) {a : Text} {u : State} {icb : Spec.Gcm.Block}
    (p : TextInput a u) (at0 : TextAt a u icb 0 u) :
    WP isa (Impl.AesGcm.X86.DirectGather.pieces v.callees) u (TextAt a u icb a.count) :=
  p.pieces_ok v (by simpa [Text.desc,atByte] using at0.ptr) at0.count at0.off at0.ctr

private theorem setup_rel {c : List Instr} {x y : State} {W S : BitVec 32}
    (h : KeepEnv W S 12 x) (k : KeepEnv W S 12 y)
    (code : c=Impl.AesGcm.X86.DirectGather.loopSetup ∨ c=Impl.AesGcm.X86.DirectGather.tagSetup) :
    RelCT isa (Eq2 x y) (.block c) TT := by
  have regs : ∀ r ∈ [Reg.ebp,.esp], x.gpr r=y.gpr r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact h.ebp.trans k.ebp.symm
    · exact h.esp.trans k.esp.symm
  rcases code with rfl | rfl <;> exact rel_taint _ regs ⟨_,by taint_decide⟩

private theorem descriptors {s u : State} (l : Gather.Lay s) (fr : Frame [Gather.stkR s] s.mem u.mem)
    {j : Nat} (hj : j<Gather.Cnt s*8) :
    u.mem (w64 (Gather.Src s)+BitVec.ofNat 64 j)=s.mem (w64 (Gather.Src s)+BitVec.ofNat 64 j) := by
  apply fr
  intro r hr hx
  obtain rfl := List.mem_singleton.mp hr
  exact l.bds _ hx (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj,l.ods]))

private theorem finishKeep {s u y : State} {icb : Spec.Gcm.Block}
    (k : KeepEnv (work s) (SP s) 12 u) (a : TextAt (text s) u icb (text s).count y) :
    KeepEnv (work s) (SP s) 12 y :=
  k.keep (a.env.ebp.trans k.ebp.symm) (a.env.esp.trans k.esp.symm) a.rd a.wr

private theorem tagWritable {s e : State} (l : Gather.Lay s) (p : Prepared s e) :
    Covers [Gather.tgR s] e.wr := by
  rw [p.wr]
  exact covers_of_mem (List.mem_cons_of_mem _ (l.wr ▸ by simp))

theorem body_rel (v : GcmImpl)
    {s t e f : State} (l : Gather.Lay s) (m : Gather.Lay t) (pub : Gather.gatherPub s t)
    (h : Prepared s e) (k : Prepared t f) : RelCT isa (Eq2 e f) (body v.callees) TT := by
  let P := pubSw 12 8 e
  have ef : pubSw 12 8 f = P := (pubSw_eq (i:=8) (by decide) (h.publicArgs k pub)).symm
  have G := (h.op l).ol rfl (by decide) (p:=P) rfl
  have en := entry_pc G
  have au := oneAad_pc (vg:=v) G
  have sp : SP t=SP s := congrArg (· - 2612#32) pub.1.symm
  have w : work t=work s := congrArg (· + 52#32) sp
  have eq := text_eq pub
  unfold body
  refine rel_seq (fixedCT en.ct ⟨e,h.op l,rfl,rfl⟩ ⟨f,k.op m,ef,rfl⟩)
    (en.wp e e ⟨h.op l,rfl,rfl⟩) (en.wp f f ⟨k.op m,ef,rfl⟩) ?_
  intro c d hc hd
  refine rel_seq (fixedCT au.ct ⟨(e,c),hc,rfl⟩ ⟨(f,d),hd,rfl⟩)
    (au.wp (e,c) c ⟨hc,rfl⟩) (au.wp (f,d) d ⟨hd,rfl⟩) ?_
  intro a b ha hb
  have ka := setupEnv l h (p:=P) rfl ha.1.o.env.ebp ha.1.o.env.esp ha.1.o.rd ha.1.o.wr
  have kb := setupEnv m k ef hb.1.o.env.ebp hb.1.o.env.esp hb.1.o.rd hb.1.o.wr
  refine rel_seq (setup_rel ka (w ▸ sp ▸ kb) (.inl rfl)) (loopSetup_ok ka) (loopSetup_ok kb) ?_
  intro u z hu hz
  have ux : BeforeText P s e c a u := ⟨l,h,rfl,hc,ha.1,ha.2,hu⟩
  have zy : BeforeText P t f d b z := ⟨m,k,ef,hd,hb.1,hb.2,hz⟩
  obtain ⟨pu,iu,fu⟩ := ux.start
  obtain ⟨pz,iz,fz⟩ := zy.start
  have de : DescEq (text s) u.mem z.mem := by
    refine DescEq.of_bytes pu.descFit (fun j hj => ?_)
    change j<(arg s 7).toNat*8 at hj
    have hj' : j<(arg t 7).toNat*8 := (pub.2.1 7 (by decide)) ▸ hj
    have dr := descriptors m fz hj'
    rw [show Gather.Src t=Gather.Src s from (pub.2.1 6 (by decide)).symm] at dr
    exact (descriptors l fu hj).trans ((pub.2.2 _ hj).trans dr.symm)
  refine rel_seq (pieces_rel v pu (eq ▸ pz) de iu (eq ▸ iz))
    (pieces_from_start v pu iu) (pieces_from_start v pz iz) ?_
  intro x y hx hy
  have kx := finishKeep (ka.keep (hu.regs _ (by decide)) (hu.regs _ (by decide)) hu.rd hu.wr) hx
  have ky := finishKeep (kb.keep (hz.regs _ (by decide)) (hz.regs _ (by decide)) hz.rd hz.wr) hy
  have permx : InRegions x.wr (w64 (SP s)) 4 := by
    rw [hx.wr]; exact pu.spW _ _ ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩
  have permy : InRegions y.wr (w64 (SP t)) 4 := by
    rw [hy.wr]; exact pz.spW _ _ ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩
  refine rel_seq (setup_rel kx (w ▸ sp ▸ ky) (.inr rfl))
    (tagSetup_ok kx permx pu.argW) (tagSetup_ok ky permy pz.argW) ?_
  intro x' y' hx' hy'
  exact tagSuffix_rel v G (tagBridge_ok ux pu hx hx') (tagBridge_ok zy pz hy hy')
    (h.arg_eq 8 (by decide)) ((k.arg_eq 8 (by decide)).trans (pub.2.1 10 (by decide)).symm)
    l.ot (tagWritable l h) ((pub.2.1 10 (by decide)) ▸ tagWritable m k)

theorem sealGather_ct (v : GcmImpl) :
    ConstantTime isa Gather.gatherPre Gather.gatherPub (Impl.AesGcm.X86.DirectGather.sealGather v.callees) :=
  sealGather_ct_of_body v (fun _ _ _ _ l m hp h k => body_rel v l m hp h k)

end VG.Proof.AesGcm.X86.DirectGather
end
