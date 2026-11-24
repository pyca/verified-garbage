module
public import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedInput
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous

/-! The compact AVX-512 seal receives a single source span directly
from the ABI. Identical and disjoint buffers satisfy the same theorem. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short
open VG.Spec.Aes (bytesAt)
variable {M : CtxMode} {o s o' : State} {Ctx W SP Np A S D : Addr} {nl al n R k : Nat}
private theorem args_ok (C : OneCtx o k Ctx W SP Np A D nl al n)
    (E : OneEntry o Ctx W SP A D n s) (hk : 0 < k)
    (src : s.mem.readW (SP+8#64) 64 = S) : WP isa (.block Contiguous.boundedArgs) s fun t =>
      OneEntry o Ctx W SP A D n t ∧ SpanEntryArgs S S n t := by
  have d : InRegions (s.rd++s.wr) (SP+8#64) 8 := by
    rw [E.rd,E.wr]; exact C.args 0 hk
  have l : InRegions (s.rd++s.wr) (W+208#64) 8 := in_left (in_off E.env.perm.w (by decide) (by decide))
  let t := ((s.setReg .rbx S).setReg .r10 (BitVec.ofNat 64 n)).setReg .r11 S
  refine WP.of_runBlock ⟨t,?_,?_,rfl,rfl,rfl⟩
  · unfold Contiguous.boundedArgs t
    xrun [Contiguous.src,E.env.r15,E.rsp,d,l,src,E.len]
  · refine OneEntry.keep C.lay E ?_ rfl rfl (Frame.refl _ _)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem bounded_ok (hF : ShortFacts) (C : OneCtx o k Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W+16#64) W SP D n o) (pow : PowOk M powersP ghashP)
    (geo : SpanLayout o S S D W SP n n) (hk : 0 < k) (src : s.mem.readW (SP+8#64) 64 = S)
    (E : OneEntry o Ctx W SP A D n s) (hp : o.gpr .rdx = Np) (hl : (o.gpr .rcx).toNat = nl)
    (ha : (o.gpr .r9).toNat = al) (hs : IsShort nl al n) : WP isa Contiguous.bounded s
      (SealPostFrom o Ctx W SP D n (o.gpr .rsi).toNat al (Spec.Gcm.ctxH o.mem Ctx)
        (Spec.Gcm.j0 (Spec.Gcm.ctxH o.mem Ctx) (bytesAt o.mem Np nl)) (bytesAt o.mem A al) (bytesAt o.mem S n)) := by
  unfold Contiguous.bounded Contiguous.call
  apply WP.seq
  refine WP.mono (args_ok C E hk src) fun _ h => ?_
  have run := (run_cut hF C X pow h.1 geo hp hl ha hs h.2).wp
  refine WP.mono run fun t ht => ?_
  simpa only [SealRunPost,SealPostFrom,spanBytes,Nat.sub_self,bytesAt,List.range_zero,List.map_nil,List.append_nil] using ht

theorem bounded_relational (hF : ShortFacts) (hpc : PowCT powersP ghashP)
    (C : OneCtx o k Ctx W SP Np A D nl al n) (C' : OneCtx o' k Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W+16#64) W SP D n o) (X' : CtxExt M Ctx (W+16#64) W SP D n o')
    (pow : PowOk M powersP ghashP) (geo : SpanLayout o S S D W SP n n) (geo' : SpanLayout o' S S D W SP n n) (hk : 0 < k)
    (hp : o.gpr .rdx = Np) (hl : (o.gpr .rcx).toNat = nl) (ha : (o.gpr .r9).toNat = al)
    (hr : (o.gpr .rsi).toNat = R) (hp' : o'.gpr .rdx = Np) (hl' : (o'.gpr .rcx).toNat = nl)
    (ha' : (o'.gpr .r9).toNat = al) (hr' : (o'.gpr .rsi).toNat = R) (hs : IsShort nl al n) :
    RelCT isa (fun a b => (OneEntry o Ctx W SP A D n a ∧ a.mem.readW (SP+8#64) 64 = S) ∧
        (OneEntry o' Ctx W SP A D n b ∧ b.mem.readW (SP+8#64) 64 = S)) Contiguous.bounded
      (fun _ _ => True) := by
  unfold Contiguous.bounded Contiguous.call
  refine RelCT.seq (rel_next (rel_taint [.rsp,.r15] (fun _ _ h r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact h.1.1.rsp.trans h.2.1.rsp.symm
      · exact h.1.1.env.r15.trans h.2.1.env.r15.symm) ⟨_,by taint_decide⟩)
    (fun _ h => args_ok C h.1 hk h.2) (fun _ h => args_ok C' h.1 hk h.2)) ?_
  refine CallRun.rel (fun _ _ h =>
    ⟨(run_cut hF C X pow h.1.1 geo hp hl ha hs h.1.2).mono (fun _ _ => trivial),
     (run_cut hF C' X' pow h.2.1 geo' hp' hl' ha' hs h.2.2).mono (fun _ _ => trivial)⟩)
    (fun _ _ h => h.1.1.rsp.trans h.2.1.rsp.symm) ?_
  exact bounded_rel hpc C C' (pow X).choose_spec (pow X').choose_spec geo geo'
    hp hl ha hr hp' hl' ha' hr' hs

end VG.Proof.AesGcm.X86_64.ContiguousSeal
