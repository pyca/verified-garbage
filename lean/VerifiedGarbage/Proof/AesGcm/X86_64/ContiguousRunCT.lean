module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousTailCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousTiming
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousRecord
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase

/-! Compose the common payload and finalization leakage theorems. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Aes (bytesAt)
open Short (SpanLayout ShortFacts rel_next)

structure AfterBulk (M : CtxMode) (Ctx W SP S D : Addr) (R n al : Nat) (u : State) : Prop where
  scalar : ScalarI Ctx W SP S (D+BitVec.ofNat 64 (16*(n/16))) R al n (n%16) u
  origin : ∃ s, AfterAad M Ctx W SP S D R n al s ∧ ObPost Ctx W SP D n s u
  slotWork : (⟨SP+8#64,8⟩ : Region).Disjoint ⟨W,2560⟩
  ext : CtxExt M Ctx (W+16#64) W SP (D+BitVec.ofNat 64 (16*(n/16))) (n%16) u

theorem AfterBulk.vec {Ctx W SP S D : Addr} {R n al : Nat} {M : CtxMode} {u : State} (h : AfterBulk M Ctx W SP S D R n al u) :
    TailI Ctx W SP S (D+BitVec.ofNat 64 (16*(n/16))) R n (n%16) u :=
  ⟨⟨h.scalar.tag.env,h.scalar.tag.rounds.1,h.scalar.tag.dat,h.scalar.tag.len⟩,h.scalar.slot,h.scalar.src,h.scalar.tag.tlen,h.slotWork⟩

theorem afterBulk_ok {M : CtxMode} {Ctx W SP S D : Addr} {R n al : Nat} {s u : State}
    (h : AfterAad M Ctx W SP S D R n al s) (p : ObPost Ctx W SP D n s u) :
    AfterBulk M Ctx W SP S D R n al u := by
  have re : n-16*(n/16)=n%16 := by omega_arith
  have off : n-n%16=16*(n/16) := by omega_arith
  have d := (h.reg.data.of_eq p.rd p.wr).drop (k:=16*(n/16)) (by omega_arith)
  have q := ((inputData h.reg).of_eq p.rd p.wr).drop (k:=16*(n/16)) (by omega_arith)
  have x := h.reg.ext.obPost p
  rw [re] at d q x
  have keep (i : Nat) (lo : 128≤i) (hi : i+8≤192) : u.mem.readW (W+BitVec.ofNat 64 i) 64=s.mem.readW (W+BitVec.ofNat 64 i) 64 :=
    (obFrame_B p.frame).readW (Region.contains_self _ _) (kept_oneFrameB h.reg.lay h.reg.data.ok.w h.ob.t_w (.inl ⟨lo,hi⟩)) (by decide)
  have tag : OneT Ctx W SP R al (D+BitVec.ofNat 64 (16*(n/16))) (n%16) n u :=
    ⟨p.env,⟨(keep 176 (by decide) (by decide)).trans h.reg.rounds.1,h.reg.rounds.2⟩,(keep 184 (by decide) (by decide)).trans h.alen,p.dat,p.len,d.ok,p.tlen⟩
  have src : u.mem.readW (SP+8#64) 64=S := by
    exact (bulkSlot p h.apart h.slotDst (by decide)).trans h.src
  refine ⟨⟨tag,by rw [p.rd,p.wr]; exact h.read,src,by rw [off]; exact q,d,?_⟩,⟨s,h,p⟩,h.apart,x⟩
  rw [off]
  rcases h.reg.sD with same|apart
  · exact .inl (by rw [same])
  · exact .inr ((apart.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)))

def FinishCT (M : CtxMode) (f : Prog isa) : Prop :=
  ∀ {Ctx W SP S D : Addr} {R n al : Nat}, Lay Ctx (W+16#64) W SP → (R=10 ∨ R=12 ∨ R=14) →
    (⟨D,n⟩ : Region).Disjoint ⟨W,2560⟩ →
    RelCT isa (fun a b => AfterBulk M Ctx W SP S D R n al a ∧ AfterBulk M Ctx W SP S D R n al b) f (fun _ _ => True)

theorem finishPlain_ct (facts : ShortFacts) (v : GcmImpl) (vec wide : Bool) {M : CtxMode} :
    FinishCT M (if vec then Contiguous.finishVec false wide else Contiguous.finishScalar v.callees) := by
  intro Ctx W SP S D R n al L hR dw
  cases vec
  · exact (finishScalar_ct v L (Nat.mod_le _ _) (Nat.mod_lt _ (by decide)) (dw.sub_left
      (Offset.sub_base _ (show 16*(n/16)+n%16≤n by omega_arith)))).mono
      (fun _ _ h => ⟨h.1.scalar,h.2.scalar⟩) fun _ _ h => h
  · apply finishVec_ct false wide (Nat.mod_le _ _) hR (by omega_arith) (fun _ h => h.vec)
    intro u h
    have e := h.scalar.tag.env
    exact (facts.finPow u (by rw [e.r13,BitVec.ofInt_natCast]; exact e.perm.ctxR (by decide))).mono fun t ⟨_,_,_,_,o⟩ =>
      ⟨e.keep (fun r hr => o.gpr _ (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;
                                        rcases hr with rfl|rfl|rfl|rfl <;> decide)) o.rd o.wr,o.mem,o.rd,o.wr⟩

theorem finishPrepared_ct (wide : Bool) {np : Nat} {hn : 8≤np ∧ np≤24} :
    FinishCT (CtxMode.preparedN np hn) (Contiguous.finishVec true wide) := by
  intro Ctx W SP S D R n al L hR dw
  apply finishVec_ct true wide (Nat.mod_le _ _) hR (by omega_arith) (fun _ h => h.vec)
  intro u h
  have e := h.scalar.tag.env
  exact (Fast.finPowP_run u e.r13 (in_off h.ext.cov (show 272+16≤1024 by decide) (show 1024<2^64 by decide))
    (in_off h.ext.cov (show 256+16≤1024 by decide) (show 1024<2^64 by decide))).mono fun t ⟨_,_,_,_,o⟩ =>
    ⟨e.keep (fun r hr => o.gpr _ (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;
                                      rcases hr with rfl|rfl|rfl|rfl <;> decide)) o.rd o.wr,o.mem,o.rd,o.wr⟩

theorem run_ct {M : CtxMode} {k fin : Prog isa} {hash : Bool} (hb : BulkOk M (Contiguous.bulk k) hash)
    (hc : KernelCT M k) (hw : KernelKeeps M k) (hf : FinishCT M fin)
    {Ctx W SP S D : Addr} {R n al : Nat} (L : Lay Ctx (W+16#64) W SP) (hR : R=10 ∨ R=12 ∨ R=14)
    (dw : (⟨D,n⟩ : Region).Disjoint ⟨W,2560⟩) :
    RelCT isa (fun a b => AfterAad M Ctx W SP S D R n al a ∧ AfterAad M Ctx W SP S D R n al b)
      (.seq (Contiguous.bulk k) fin) (fun _ _ => True) := by
  have wp (s) (h : AfterAad M Ctx W SP S D R n al s) :=
    (hb h.reg h.ob h.src h.read h.apart).mono fun _ ⟨p,_⟩ => afterBulk_ok h p
  exact RelCT.seq (rel_next ((bulk_ct hc hw).mono (fun _ _ h => ⟨h.1.toBulkIn,h.2.toBulkIn⟩) (fun _ _ h => h)) wp wp)
    (hf L hR dw)

structure RecordInput (M : CtxMode) (o : State) (Ctx W SP Np A S D : Addr) (nl al n R : Nat) : Prop where
  ctx : OneCtx o 5 Ctx W SP Np A D nl al n
  ext : CtxExt M Ctx (W+16#64) W SP D n o
  geom : SpanLayout o S S D W SP n n
  nowrap : S.toNat+n≤2^64
  src : o.mem.readW (SP+8#64) 64=S
  dst : o.mem.readW (SP+16#64) 64=D
  nonce : o.gpr .rdx=Np
  nlEq : (o.gpr .rcx).toNat=nl
  alEq : (o.gpr .r9).toNat=al
  rounds : (o.gpr .rsi).toNat=R

def RecordCT (M : CtxMode) (record : Prog isa) : Prop :=
  ∀ {o p : State} {Ctx W SP Np A S D : Addr} {nl al n R : Nat},
    RecordInput M o Ctx W SP Np A S D nl al n R → RecordInput M p Ctx W SP Np A S D nl al n R →
    RelCT isa (fun a b => OneEntry o Ctx W SP A D n a ∧ OneEntry p Ctx W SP A D n b) record (fun _ _ => True)

theorem RecordInput.afterAad {M : CtxMode} {o u z : State} {Ctx W SP Np A S D : Addr} {nl al n R : Nat}
    (h : RecordInput M o Ctx W SP Np A S D nl al n R)
    (m : OneMid o Ctx W SP D n (ctxH o.mem Ctx) (bytesAt o.mem Np nl) (bytesAt o.mem A al) u.mem z) :
    AfterAad M Ctx W SP S D R n al z :=
  h.rounds ▸ afterAad_ok h.ctx h.ext h.geom h.nowrap h.alEq h.src h.dst m

theorem RecordInput.slot {M : CtxMode} {o u : State} {Ctx W SP Np A S D : Addr} {nl al n R : Nat}
    (h : RecordInput M o Ctx W SP Np A S D nl al n R) (e : OneEntry o Ctx W SP A D n u) :
    u.mem.readW (SP+8#64) 64=S := by
  rw [e.frame.readW (w:=64) (r:=⟨SP+8#64,8⟩) (Region.contains_self _ _) (fun b hb => by
    obtain rfl := List.mem_singleton.mp hb
    exact (h.ctx.dA.sub_left (Region.sub_prefix (show 8≤8*5 by decide))).sub_right (Lay.wSub (by decide))) (by decide),h.src]

theorem ordinaryAad_ct (v : GcmImpl) {M : CtxMode} {o p : State} {Ctx W SP Np A S D : Addr} {nl al n R : Nat}
    (a : RecordInput M o Ctx W SP Np A S D nl al n R) (b : RecordInput M p Ctx W SP Np A S D nl al n R) :
    RelCT isa (fun s t => OneEntry o Ctx W SP A D n s ∧ OneEntry p Ctx W SP A D n t) (oneAad v.callees)
      (fun x y => AfterAad M Ctx W SP S D R n al x ∧ AfterAad M Ctx W SP S D R n al y) := by
  have w {p : State} (h : RecordInput M p Ctx W SP Np A S D nl al n R) (s) (e : OneEntry p Ctx W SP A D n s) :=
    (oneMid_ok v h.ctx e h.nonce h.nlEq h.alEq).mono fun _ m => h.afterAad m
  exact rel_next ((oneAad_rel v a.ctx.lay a.ctx.dE (T:=none) (R:=R) (Np:=Np) (nl:=nl)).mono
    (P':=fun s t => OneEntry o Ctx W SP A D n s ∧ OneEntry p Ctx W SP A D n t)
    (fun _ _ h => ⟨h.1.aadPre a.ctx a.ext a.nonce a.nlEq a.alEq a.rounds,h.2.aadPre b.ctx b.ext b.nonce b.nlEq b.alEq b.rounds⟩)
    (fun _ _ _ => trivial)) (w a) (w b)

theorem plain_ct (facts : ShortFacts) (v : GcmImpl) (vec wide : Bool) {M : CtxMode} {k : Prog isa}
    (hb : BulkOk M (Contiguous.bulk k)) (hc : KernelCT M k) (hw : KernelKeeps M k) :
    RecordCT M (Contiguous.body v.callees vec wide false k) := by
  intro o p Ctx W SP Np A S D nl al n R a b
  exact RelCT.seq (ordinaryAad_ct v a b) (run_ct hb hc hw (finishPlain_ct facts v vec wide) a.ctx.lay (a.rounds ▸ a.ctx.rounds) a.ctx.dE)

theorem preparedAad_ct (facts : ShortFacts) (v : GcmImpl) (wide : Bool) {np : Nat} {hn : 8≤np ∧ np≤24}
    {o p : State} {Ctx W SP Np A S D : Addr} {nl al n R : Nat}
    (a : RecordInput (CtxMode.preparedN np hn) o Ctx W SP Np A S D nl al n R)
    (b : RecordInput (CtxMode.preparedN np hn) p Ctx W SP Np A S D nl al n R) :
    RelCT isa (fun s t => OneEntry o Ctx W SP A D n s ∧ OneEntry p Ctx W SP A D n t) (Contiguous.aad v.callees true wide true)
      (fun x y => AfterAad (CtxMode.preparedN np hn) Ctx W SP S D R n al x ∧ AfterAad (CtxMode.preparedN np hn) Ctx W SP S D R n al y) := by
  have w {p : State} (h : RecordInput (CtxMode.preparedN np hn) p Ctx W SP Np A S D nl al n R) (s) (e : OneEntry p Ctx W SP A D n s) :=
    (Fast.condE_ok (any:=!wide) h.ctx e h.nlEq h.alEq).mono fun _ ⟨z,f,_⟩ => And.intro z f
  have pre := rel_next (Fast.cond_rel (F₁:=OneEntry o Ctx W SP A D n) (F₂:=OneEntry p Ctx W SP A D n)
      (fun _ e => Short.condS_of e a.nlEq a.alEq) (fun _ e => Short.condS_of e b.nlEq b.alEq)
      (by rw [← a.nlEq]; exact BitVec.isLt _) (by rw [← a.alEq]; exact BitVec.isLt _) a.ctx.data.ok.lt) (w a) (w b)
  refine RelCT.seq pre (rel_ite_e (fun _ _ h => by rw [h.1.1,h.2.1]) ((ordinaryAad_ct v a b).mono
    (fun _ _ h => ⟨h.1.1.2,h.1.2.2⟩) (fun _ _ h => h)) ?_)
  by_cases fast : Fast.IsFast nl al n (!wide)
  · obtain ⟨h12,h17,_⟩ := fast
    subst h12
    have wf {p : State} (h : RecordInput (CtxMode.preparedN np hn) p Ctx W SP Np A S D 12 al n R) (s) (e : OneEntry p Ctx W SP A D n s) :=
      (Fast.aad_mid facts h.ctx h.ext e h.nonce h.nlEq h.alEq (by omega)).mono fun _ m => h.afterAad m
    apply RelCT.mono (rel_next ((Fast.aad_rel a.ctx.lay a.ctx.dE (M:=CtxMode.preparedN np hn) (R:=R) (Np:=Np) (A:=A) (al:=al) (by omega)).mono
      (P':=fun x y => OneEntry o Ctx W SP A D n x ∧ OneEntry p Ctx W SP A D n y)
      (fun _ _ h => ⟨h.1.aadPre a.ctx a.ext a.nonce a.nlEq a.alEq a.rounds,h.2.aadPre b.ctx b.ext b.nonce b.nlEq b.alEq b.rounds⟩)
      (fun _ _ _ => trivial)) (wf a) (wf b)) (fun _ _ h => ⟨h.1.1.2,h.1.2.2⟩) (fun _ _ h => h)
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [fast] at this

theorem prepared_ct (facts : ShortFacts) (v : GcmImpl) (wide : Bool) {np : Nat} {hn : 8≤np ∧ np≤24}
    (pow : wide → Short.PowOk (CtxMode.preparedN np hn) VG.Impl.AesGcm.X86_64.Short.powersP VG.Impl.AesGcm.X86_64.Short.ghashP)
    (pc : wide → Short.PowCT VG.Impl.AesGcm.X86_64.Short.powersP VG.Impl.AesGcm.X86_64.Short.ghashP)
    {k : Prog isa} (hb : BulkOk (CtxMode.preparedN np hn) (Contiguous.bulk k)) (hc : KernelCT (CtxMode.preparedN np hn) k)
    (hw : KernelKeeps (CtxMode.preparedN np hn) k) : RecordCT (CtxMode.preparedN np hn) (Contiguous.body v.callees true wide true k) := by
  intro o p Ctx W SP Np A S D nl al n R a b
  have long := RelCT.seq (preparedAad_ct facts v wide a b) (run_ct hb hc hw (finishPrepared_ct wide) a.ctx.lay (a.rounds ▸ a.ctx.rounds) a.ctx.dE)
  cases wide
  · exact long
  · have w {p : State} (h : RecordInput (CtxMode.preparedN np hn) p Ctx W SP Np A S D nl al n R) (s) (e : OneEntry p Ctx W SP A D n s) :=
      (Short.condE_ok h.ctx e h.nlEq h.alEq).mono fun _ ⟨z,f,_⟩ => And.intro z f
    have pre := rel_next (Short.cond_rel (F₁:=OneEntry o Ctx W SP A D n) (F₂:=OneEntry p Ctx W SP A D n)
      (fun _ e => Short.condS_of e a.nlEq a.alEq) (fun _ e => Short.condS_of e b.nlEq b.alEq)
      (by rw [← a.nlEq]; exact BitVec.isLt _) (by rw [← a.alEq]; exact BitVec.isLt _) a.ctx.data.ok.lt) (w a) (w b)
    refine RelCT.seq pre (rel_ite_e (fun _ _ h => by rw [h.1.1,h.2.1]) (long.mono
      (fun _ _ h => ⟨h.1.1.2,h.1.2.2⟩) (fun _ _ h => h)) ?_)
    by_cases hs : Short.IsShort nl al n
    · exact (bounded_relational facts (pc rfl) a.ctx b.ctx a.ext b.ext (pow rfl) a.geom b.geom (by decide)
        a.nonce a.nlEq a.alEq a.rounds b.nonce b.nlEq b.alEq b.rounds hs).mono (fun _ _ h =>
        ⟨⟨h.1.1.2,a.slot h.1.1.2⟩,h.1.2.2,b.slot h.1.2.2⟩) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

end VG.Proof.AesGcm.X86_64.ContiguousSeal
