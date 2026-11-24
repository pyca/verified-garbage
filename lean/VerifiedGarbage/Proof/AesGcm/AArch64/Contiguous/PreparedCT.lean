module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PreparedSeal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.BatchCT
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericAlignedCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Finish

/-! The lengths, key size and addresses determine the trace of the prepared
seal. The two runs may have different keys, plaintexts and ciphertexts. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.Contiguous
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)
open VG.Proof.Gcm.AArch64.Pmull (MulKey)
open VG.Spec.Gcm (Block)

theorem auth_rel {wn n : Nat} {Ctx St W SP O P : Addr} {a b : State}
    (v : GcmImpl) (g : GhashWithImpl) (fused : Bool) (L : Lay wn Ctx St W)
    (ea : Env wn Ctx St W SP a) (eb : Env wn Ctx St W SP b)
    (da : DataOk wn St W a O n) (db : DataOk wn St W b O n)
    (oa : a.gpr .x27 = word O (done fused n)) (ob : b.gpr .x27 = word O (done fused n))
    (na : a.mem.readW (word W lenO) 64 = BitVec.ofNat 64 n) (nb : b.mem.readW (word W lenO) 64 = BitVec.ofNat 64 n)
    (pa : GhWCall a Ctx (word St 16) (word W 512) P) (pb : GhWCall b Ctx (word St 16) (word W 512) P)
    (sa : a.mem.readW (word a.sp 16) 64 = P) (sb : b.mem.readW (word b.sp 16) 64 = P)
    (ra : InRegions (a.rd++a.wr) (word a.sp 16) 8) (rb : InRegions (b.rd++b.wr) (word b.sp 16) 8) :
    RelCT isa (Eq2 a b) (.seq (.block (authRemainder fused)) (authBlocks v.callees g.fn)) TT := by
  refine rel_seq (rel_taint [.x19,.x20,.x21,.x27] (ea.sp.trans eb.sp.symm)
    (by agree_tac [ea.x19,eb.x19,ea.x20,eb.x20,ea.x21,eb.x21,oa,ob]) (by cases fused <;> exact ⟨_,by taint_decide⟩))
    (WP.with_rdwr (authCallArgs (x := []) fused L ea da oa na rfl (by decide)))
    (WP.with_rdwr (authCallArgs (x := []) fused L eb db ob nb rfl (by decide))) ?_
  intro u z ⟨⟨_,_,_,hu,mu⟩,rd,wr⟩ ⟨⟨_,_,_,hz,mz⟩,rd',wr'⟩
  have su := hu.env.sp.trans ea.sp.symm
  have sz := hz.env.sp.trans eb.sp.symm
  have small : (n - done fused n - 0) / 16 < 2^64 := by have := hu.call.n_lt; omega
  refine rel_ite (eval_zero hu.call.x3 small) (eval_zero hz.call.x3 small) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (hu.env.sp.trans hz.env.sp.symm) (by agree_tac []) ⟨.block [] 256,by decide⟩
  exact pwSel_rel v g (k := 16) (by decide)
    (by rw [su,mu]; exact sa) (by rw [su,rd,wr]; exact ra)
    (by rw [sz,mz]; exact sb) (by rw [sz,rd',wr']; exact rb)
    hu.call ⟨by rw [rd,wr]; exact pa.reads,pa.yp,pa.sp,mu ▸ pa.repr⟩
    hz.call ⟨by rw [rd',wr']; exact pb.reads,pb.yp,pb.sp,mz ▸ pb.repr⟩ (hu.env.sp.trans hz.env.sp.symm)

private theorem prefix_rel {wn R n : Nat} {Ctx W D O P : Addr} {a b : State} {aa ai ba bi : List Byte}
    (v : GcmImpl) (fused : Bool)
    (x : Ready wn R n Ctx W D O P aa ai a) (y : Ready wn R n Ctx W D O P ba bi b)
    (sp : a.sp = b.sp) :
    RelCT isa (Eq2 a b) (if fused then batches (!v.stitch) else .block []) TT := by
  cases fused
  · change RelCT isa (Eq2 a b) (.block []) TT
    exact rel_taint [] sp (by agree_tac []) ⟨.block [] 256,by decide⟩
  · refine batches_rel (!v.stitch) x.env (sp ▸ y.env) ?_ x.x26 x.src.lt x.powers y.powers x.pw y.pw x.pRead y.pRead x.dstSlot y.dstSlot
    intro r hr ne
    simp only [Fast.stRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (ne rfl).elim
    · exact x.env.x19.trans y.env.x19.symm
    · exact x.env.x20.trans y.env.x20.symm
    · exact x.env.x21.trans y.env.x21.symm
    · exact x.x22.trans y.x22.symm
    · exact x.x23.trans y.x23.symm
    · exact x.x26.trans y.x26.symm

private theorem text_rel {wn R n : Nat} {Ctx W D O P : Addr} {a b : State} {aa ai ba bi : List Byte}
    (v : GcmImpl) (fused : Bool) (L : Lay wn Ctx (word W 16) W)
    (x : Ready wn R n Ctx W D O P aa ai a) (y : Ready wn R n Ctx W D O P ba bi b)
    {u z : State} (f : recordPrefix x fused u) (h : recordPrefix y fused z) (sp : a.sp = b.sp) (hv : v.ctr.scratch ≤ wn-512) :
    RelCT isa (Eq2 u z) (.seq (.block (remainder fused)) (Impl.AesGcm.AArch64.Contiguous.Tail.finalAligned v.callees)) TT := by
  have slot {s u : State} {m iv : List Byte} (q : Ready wn R n Ctx W D O P m iv s)
      (f : Prefix wn R n (done fused n) Ctx (word W 16) W s.sp D O (paddedAad m) (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH s.mem Ctx) iv)) s u) :
      u.mem.readW (word W dstO) 64 = O :=
    ((prefix_writes (done_le fused n) L.hWn.1 f.frame).readW (r := slotR W dstO) (Region.contains_self _ _)
      (writes_slot L (by decide) (by decide) q.dst.ok) (by decide)).trans q.dstSlot
  have setup {s u : State} {m iv : List Byte} (q : Ready wn R n Ctx W D O P m iv s)
      (f : Prefix wn R n (done fused n) Ctx (word W 16) W s.sp D O (paddedAad m) (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH s.mem Ctx) iv)) s u) :=
    remainder_ok fused f.x23 f.x26 q.src.lt f.env.x19 (f.env.perm.wR (by decide)) (slot q f)
  refine rel_seq (rel_taint [.x19] (f.env.sp.trans (sp.trans h.env.sp.symm)) (by agree_tac [f.env.x19,h.env.x19])
    (by cases fused <;> exact ⟨_,by taint_decide⟩)) (setup x f) (setup y h) ?_
  intro s t fs ht
  have build {s u t : State} {m iv : List Byte} (q : Ready wn R n Ctx W D O P m iv s)
      (f : Prefix wn R n (done fused n) Ctx (word W 16) W s.sp D O (paddedAad m) (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH s.mem Ctx) iv)) s u)
      (r : TailArgs fused n D O u t) : CrInG wn true Ctx (word W 16) W s.sp t.gpr R (done fused n)
         (word D (done fused n)) (word O (done fused n)) (n-done fused n) t := by
    have n22 := f.x22.trans q.x22
    refine r.crIn f.env ?_ ?_ (q.src.of_eq f.rd f.wr) (q.dst.of_eq f.rd f.wr) q.mode
    · rw [n22]; rcases q.rates with e|e|e <;> rw [e] <;> decide
    · rw [n22,toNat_ofNat_of_lt (by rcases q.rates with e|e|e <;> rw [e] <;> decide)]
  exact Tail.finalAligned_rel L v (build x f fs) (sp ▸ build y h ht) (done_mod ..) hv

private theorem normal_rel {wn R n : Nat} {Ctx W D O P : Addr} {a b : State} {aa ai ba bi : List Byte}
    (v : GcmImpl) (g : GhashWithImpl) (fused : Bool)
    (L : Lay wn Ctx (word W 16) W)
    (x : Ready wn R n Ctx W D O P aa ai a) (y : Ready wn R n Ctx W D O P ba bi b)
    (ext : External wn n W O P a) (ext' : External wn n W O P b)
    (sp : a.sp = b.sp) (tag : a.gpr .x28 = b.gpr .x28)
    {u z : State} (f : recordPrefix x fused u) (h : recordPrefix y fused z) (hv : v.ctr.scratch ≤ wn-512) :
    RelCT isa (Eq2 u z) (.seq (remaining v.callees g.fn fused) tagReturn) TT := by
  apply Fast.RelCT.assoc'
  apply Fast.RelCT.assoc'
  refine rel_seq (text_rel v fused L x y f h sp hv) (remainingText_ok v fused L x f hv) (remainingText_ok v fused L y h hv) ?_
  intro u w f h
  obtain ⟨nu,_,_,pu,su,ru⟩ := f.authInput fused L x ext
  obtain ⟨nw,_,_,pw,sw,rw'⟩ := h.authInput fused L y ext'
  refine rel_seq (auth_rel v g fused L f.env (sp ▸ h.env) (x.dst.ok.of_eq f.rd f.wr) (y.dst.ok.of_eq h.rd h.wr)
    f.x27 h.x27 nu nw pu pw su sw ru rw') (authenticate_ok v g fused L x ext f) (authenticate_ok v g fused L y ext' h) ?_
  intro i j m k
  have eq22 := (m.x22.trans x.x22).trans (k.x22.trans y.x22).symm
  have eq28 := m.x28.trans (tag.trans k.x28.symm)
  unfold tagReturn
  exact rel_taint [.x19,.x20,.x21,.x22,.x23,.x24,.x26,.x28]
    (m.env.sp.trans (sp.trans k.env.sp.symm))
    (by agree_tac [m.env.x19,k.env.x19,m.env.x20,k.env.x20,m.env.x21,k.env.x21,eq22,m.x23,k.x23,
      m.x24,k.x24,m.x26,k.x26,eq28]) ⟨_,by taint_decide⟩

/-- For a shared continuation after a public branch, each alternative may
establish the trace of the continuation using its own postcondition. -/
private theorem branchReturn {a b : State} {cond : Cond} {value : Bool} {yes no ret : Prog isa}
    (ca : isa.eval cond a = some value) (cb : isa.eval cond b = some value)
    (y : value = true → RelCT isa (Eq2 a b) (.seq yes ret) TT)
    (n : value = false → RelCT isa (Eq2 a b) (.seq no ret) TT) :
    RelCT isa (Eq2 a b) (.seq (.ite cond yes no) ret) TT := by
  intro _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  cases ea with
  | seq ba ra =>
    cases eb with
    | seq bb rb =>
      cases ba with
      | iteT xa ya =>
        rw [ca] at xa; obtain rfl := Option.some.inj xa
        cases bb with
        | iteT _ yb =>
          have h := (y rfl _ _ _ _ _ _ ⟨rfl,rfl⟩ (.seq ya ra) (.seq yb rb)).1
          exact ⟨by simpa using h, trivial⟩
        | iteF xb _ => rw [cb] at xb; cases xb
      | iteF xa na =>
        rw [ca] at xa; obtain rfl := Option.some.inj xa
        cases bb with
        | iteT xb _ => rw [cb] at xb; cases xb
        | iteF _ nb =>
          have h := (n rfl _ _ _ _ _ _ ⟨rfl,rfl⟩ (.seq na ra) (.seq nb rb)).1
          exact ⟨by simpa using h, trivial⟩

theorem record_rel {wn R n : Nat} {Ctx W D O P : Addr} {a b : State} {aa ai ba bi : List Byte}
    (v : GcmImpl) (g : GhashWithImpl) (fused : Bool) (gh : Proof.Gcm.AArch64.Stitch.Gh8Ok)
    (L : Lay wn Ctx (word W 16) W)
    (x : Ready wn R n Ctx W D O P aa ai a) (y : Ready wn R n Ctx W D O P ba bi b)
    (ext : External wn n W O P a) (ext' : External wn n W O P b)
    (sp : a.sp = b.sp) (tag : a.gpr .x28 = b.gpr .x28)
    (hn : fused = true → 128 ≤ n) (hv : v.ctr.scratch ≤ wn-512) :
    RelCT isa (Eq2 a b) (afterFront v.callees g.fn fused (!v.stitch)) TT := by
  refine rel_seq (prefix_rel v fused x y sp) (recordPrefix_ok v fused gh L x hn) (recordPrefix_ok v fused gh L y hn) ?_
  intro u z f h
  cases fused
  · exact normal_rel v g false L x y ext ext' sp tag f h hv
  · apply Fast.RelCT.assoc'
    refine rel_seq (rel_taint [.x26] (f.env.sp.trans (sp.trans h.env.sp.symm))
      (by agree_tac [f.x26,h.x26]) ⟨_,by taint_decide⟩) (groupTest_ok f) (groupTest_ok h) ?_
    intro i j ⟨fi, ci⟩ ⟨hj, cj⟩
    apply branchReturn ci cj
    · intro _
      have eq22 := (fi.x22.trans x.x22).trans (hj.x22.trans y.x22).symm
      have eq28 := fi.x28.trans (tag.trans hj.x28.symm)
      unfold tagReturn
      exact rel_taint [.x19,.x20,.x21,.x22,.x26,.x28]
        (fi.env.sp.trans (sp.trans hj.env.sp.symm))
        (by agree_tac [fi.env.x19,hj.env.x19,fi.env.x20,hj.env.x20,fi.env.x21,hj.env.x21,eq22,fi.x26,hj.x26,eq28])
        ⟨_,by taint_decide⟩
    · intro _; exact normal_rel v g true L x y ext ext' sp tag fi hj hv

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
