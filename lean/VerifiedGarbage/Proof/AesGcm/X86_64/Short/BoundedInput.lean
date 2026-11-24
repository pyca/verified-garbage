module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedSpans
public import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedSeal
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedSeal

/-! Direct one-span specialization of the common bounded seal for identical buffers. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.Short
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
variable {M : CtxMode} {o s o' : State} {Ctx W SP Np A D : Addr} {nl al n R k : Nat}

theorem sameGeo (C : OneCtx o k Ctx W SP Np A D nl al n) : SpanLayout o D D D W SP n n :=
  ⟨Nat.le_refl _,C.data.ok.rd,.inl rfl,C.dE,C.t_d.symm,fun lt => False.elim (Nat.lt_irrefl _ lt),
    fun lt => False.elim (Nat.lt_irrefl _ lt), fun lt => False.elim (Nat.lt_irrefl _ lt),
    fun lt => False.elim (Nat.lt_irrefl _ lt)⟩

private theorem sameArgs_ok (C : OneCtx o k Ctx W SP Np A D nl al n)
    (E : OneEntry o Ctx W SP A D n s) : WP isa (.block sameArgs) s fun t =>
      OneEntry o Ctx W SP A D n t ∧ SpanEntryArgs D D n t := by
  have d : InRegions (s.rd++s.wr) (W+200#64) 8 := in_left (in_off E.env.perm.w (by decide) (by decide))
  have l : InRegions (s.rd++s.wr) (W+208#64) 8 := in_left (in_off E.env.perm.w (by decide) (by decide))
  let t := ((s.setReg .rbx D).setReg .r10 (BitVec.ofNat 64 n)).setReg .r11 D
  refine WP.of_runBlock ⟨t,?_,?_,rfl,rfl,rfl⟩
  · unfold sameArgs t
    xrun [E.env.r15,d,l,E.dat,E.len]
  · refine OneEntry.keep C.lay E ?_ rfl rfl (Frame.refl _ _)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem boundedSame_ok (hF : ShortFacts) (C : OneCtx o k Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W+16#64) W SP D n o) (pow : PowOk M powersP ghashP)
    (E : OneEntry o Ctx W SP A D n s) (hp : o.gpr .rdx = Np) (hl : (o.gpr .rcx).toNat = nl)
    (ha : (o.gpr .r9).toNat = al) (hs : IsShort nl al n) : WP isa boundedSame s
      (SealRunPost o Ctx W SP Np A D nl al n) := by
  apply WP.seq
  refine WP.mono (sameArgs_ok C E) fun _ h => ?_
  have run := (run_cut hF C X pow h.1 (sameGeo C) hp hl ha hs h.2).wp
  refine WP.mono run fun t ht => ?_
  simpa only [SealRunPost,SealPostFrom,spanBytes,Nat.sub_self,bytesAt,List.range_zero,List.map_nil,List.append_nil] using ht

theorem boundedSame_rel (hF : ShortFacts) (hpc : PowCT powersP ghashP)
    (C : OneCtx o k Ctx W SP Np A D nl al n) (C' : OneCtx o' k Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W+16#64) W SP D n o) (X' : CtxExt M Ctx (W+16#64) W SP D n o')
    (pow : PowOk M powersP ghashP)
    (hp : o.gpr .rdx = Np) (hl : (o.gpr .rcx).toNat = nl) (ha : (o.gpr .r9).toNat = al)
    (hr : (o.gpr .rsi).toNat = R) (hp' : o'.gpr .rdx = Np) (hl' : (o'.gpr .rcx).toNat = nl)
    (ha' : (o'.gpr .r9).toNat = al) (hr' : (o'.gpr .rsi).toNat = R) (hs : IsShort nl al n) :
    RelCT isa (fun a b => OneEntry o Ctx W SP A D n a ∧ OneEntry o' Ctx W SP A D n b) boundedSame
      (fun _ _ => True) := by
  refine RelCT.seq (rel_next (rel_taint [.r15] (fun _ _ h r hr => by
      rw [List.mem_singleton.mp hr,h.1.env.r15,h.2.env.r15]) ⟨_,by taint_decide⟩)
    (fun _ h => sameArgs_ok C h) (fun _ h => sameArgs_ok C' h)) ?_
  refine CallRun.rel (fun _ _ h =>
    ⟨(run_cut hF C X pow h.1.1 (sameGeo C) hp hl ha hs h.1.2).mono (fun _ _ => trivial),
     (run_cut hF C' X' pow h.2.1 (sameGeo C') hp' hl' ha' hs h.2.2).mono (fun _ _ => trivial)⟩)
    (fun _ _ h => h.1.1.rsp.trans h.2.1.rsp.symm) ?_
  exact bounded_rel hpc C C' (pow X).choose_spec (pow X').choose_spec (sameGeo C) (sameGeo C')
    hp hl ha hr hp' hl' ha' hr' hs

end VG.Proof.AesGcm.X86_64.Short
