module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousBody
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-! Select the prepared or ordinary record strategy with common ciphertext semantics. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt ctxH)
open VG.Spec.Aes (bytesAt)
open Short (ShortFacts SpanLayout SealPostFrom)
open Gcm.X86_64.Pclmul (Only)

private theorem powersPost {Ctx W SP : Addr} {s t : State} (e : Env Ctx (W+16#64) W SP s)
    {H : Block} {rs : List XReg} (o : Only rs s t) (z : t.xmm .xmm0=VG.Proof.Gcm.X86_64.revMask)
    (one : t.xmm .xmm1=VG.Impl.Gcm.X86_64.Pclmul.poly) (h1 : Short.IsH1 H (t.xmm .xmm3))
    (h2 : Short.IsH2 H (t.xmm .xmm3) (t.xmm .xmm6)) : VecPowerPost Ctx W SP H s t :=
  ⟨z,one,h1,h2,e.keep (fun r hr => o.gpr _ (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> decide)) o.rd o.wr,o.mem,o.rd,o.wr⟩

theorem finish_plain (facts : ShortFacts) (v : GcmImpl) (vec wide : Bool) {M : CtxMode} :
    FinishOk M (if vec then Contiguous.finishVec false wide else Contiguous.finishScalar v.callees) := by
  intro Ctx W SP S D R n al s u H icb a reg ob post bulk hH hcb hal habs read src apart _ _ _ _
  cases vec
  · exact finishScalar_ok v reg ob post bulk hH hcb hal habs read src
  · apply finishVec_ok false wide reg ob post bulk hH hcb hal habs read src apart
    obtain e := post.env
    have keep := ctx_oneFrameB reg.lay ob.data.ctx ob.t_c
    have eq : blockAt u.mem (Ctx+240#64) = H :=
      (blockAt_frame (obFrame_B post.frame) (fun r hr => (keep r hr).sub_left (Lay.ctxSub (by decide)))).trans hH
    refine (facts.finPow u (by rw [e.r13,BitVec.ofInt_natCast]; exact e.perm.ctxR (by decide))).mono fun t ⟨z,one,h1,h2,o⟩ => ?_
    rw [e.r13,BitVec.ofInt_natCast,eq] at h1 h2
    exact powersPost e o z one h1 h2

theorem finish_prepared (facts : ShortFacts) (wide : Bool) {np : Nat} {hn : 8≤np ∧ np≤24} :
    FinishOk (CtxMode.preparedN np hn) (Contiguous.finishVec true wide) := by
  intro Ctx W SP S D R n al s u H icb a reg ob post bulk hH hcb hal habs read src apart _ _ _ _
  apply finishVec_ok true wide reg ob post bulk hH hcb hal habs read src apart
  have X := reg.ext
  have fr := obFrame_B post.frame
  have keep : ∀ r ∈ oneFrameB W D SP n, (⟨Ctx,(CtxMode.preparedN np hn).len⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact X.cw.sub_right (Region.sub_prefix (by decide))
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact X.cd
    · exact X.ct.symm
  have ext := X.keep post.rd post.wr fr keep
  have pp := ext.ok 0 (by have := hn.1; omega)
  simp only [Nat.mul_zero,Nat.add_zero] at pp
  have eq : ctxH u.mem Ctx = H := (blockAt_frame fr (fun r hr => (keep r hr).sub_left
    (Offset.sub_base _ (show 240+16≤1024 by decide)))).trans hH
  rw [eq] at pp
  refine (Fast.finPowP_ok facts u post.env.r13 (in_off ext.cov (show 272+16≤1024 by decide) (show 1024<2^64 by decide))
    (in_off ext.cov (show 256+16≤1024 by decide) (show 1024<2^64 by decide)) pp.2 pp.1).mono fun t ⟨z,one,h1,h2,o⟩ =>
    powersPost post.env o z one h1 h2

def RecordOk (M : CtxMode) (f : Prog isa) : Prop :=
  ∀ {o u : State} {Ctx W SP Np A S D : Addr} {nl al n : Nat},
    OneCtx o 5 Ctx W SP Np A D nl al n → CtxExt M Ctx (W+16#64) W SP D n o →
    SpanLayout o S S D W SP n n → S.toNat+n≤2^64 → o.mem.readW (SP+8#64) 64=S → o.mem.readW (SP+16#64) 64=D →
    OneEntry o Ctx W SP A D n u → o.gpr .rdx=Np → (o.gpr .rcx).toNat=nl → (o.gpr .r9).toNat=al →
    WP isa f u (SealPostFrom o Ctx W SP D n (o.gpr .rsi).toNat al (ctxH o.mem Ctx)
      (Spec.Gcm.j0 (ctxH o.mem Ctx) (bytesAt o.mem Np nl)) (bytesAt o.mem A al) (bytesAt o.mem S n))

theorem plain_ok (facts : ShortFacts) (v : GcmImpl) (vec wide : Bool) {M : CtxMode} (k : Prog isa)
    (hb : BulkOk M (Contiguous.bulk k)) : RecordOk M (Contiguous.body v.callees vec wide false k) := by
  intro o u Ctx W SP Np A S D nl al n C X geo wrap src dst E hp hl ha
  exact body_ok hb (finish_plain facts v vec wide) C X geo wrap ha src dst (oneMid_ok v C E hp hl ha)

theorem prepared_ok (facts : ShortFacts) (v : GcmImpl) (wide : Bool) {np : Nat} {hn : 8≤np ∧ np≤24}
    (pow : wide → Short.PowOk (CtxMode.preparedN np hn) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP)
    (k : Prog isa) (hb : BulkOk (CtxMode.preparedN np hn) (Contiguous.bulk k)) :
    RecordOk (CtxMode.preparedN np hn) (Contiguous.body v.callees true wide true k) := by
  intro o u Ctx W SP Np A S D nl al n C X geo wrap src dst E hp hl ha
  have long {z : State} (init : OneEntry o Ctx W SP A D n z) : WP isa
      (.seq (Contiguous.aad v.callees true wide true) (.seq (Contiguous.bulk k) (Contiguous.finishVec true wide))) z
      (SealPostFrom o Ctx W SP D n (o.gpr .rsi).toNat al (ctxH o.mem Ctx)
        (Spec.Gcm.j0 (ctxH o.mem Ctx) (bytesAt o.mem Np nl)) (bytesAt o.mem A al) (bytesAt o.mem S n)) := by
    apply body_ok hb (finish_prepared facts wide) C X geo wrap ha src dst
    refine WP.seq ((Fast.condE_ok (any:=!wide) C init hl ha).mono fun t ⟨cond,f,keep⟩ => ?_)
    refine WP.ite (decide ¬Fast.IsFast nl al n (!wide)) (eval_e cond) (fun _ => ?_) (fun hh => ?_)
    · simpa only [keep.mem] using oneMid_ok v C f hp hl ha
    · obtain ⟨h12,h17,_⟩ := Decidable.not_not.mp (of_decide_eq_false hh)
      subst h12
      simpa only [keep.mem] using Fast.aad_mid facts C X f hp hl ha (by omega)
  cases wide
  · exact long E
  · refine WP.seq ((Short.condE_ok C E hl ha).mono fun t ⟨cond,f,keep⟩ => ?_)
    refine WP.ite (decide ¬Short.IsShort nl al n) (eval_e cond) (fun _ => long f) (fun hh => ?_)
    have orig := E.frame.readW (w:=64) (r:=⟨SP+8#64,8⟩) (Region.contains_self _ _) (fun b hb => by
      obtain rfl := List.mem_singleton.mp hb
      exact (C.dA.sub_left (Region.sub_prefix (show 8≤8*5 by decide))).sub_right (Lay.wSub (by decide))) (by decide)
    exact bounded_ok facts C X (pow rfl) geo (by decide) (by rw [keep.mem,orig,src]) f hp hl ha
      (Decidable.not_not.mp (of_decide_eq_false hh))

end VG.Proof.AesGcm.X86_64.ContiguousSeal
