module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Entry
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.TextDone
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Piece
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

/-! Nonce and associated-data initialization for the arbitrary-fragment path. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

abbrev GeneralAad (s u : State) := OneMid s (K s) (W s) (SP s) (Dst s) (L s) (hk s) (iv s) (ad s) u.mem

variable {M : CtxMode} {s d : State}
theorem general_aad_wp (v : GcmImpl) (h : Layout M s) {u : State} (e : Layout.Initial s u) :
    WP isa (oneAad v.callees) u (GeneralAad s u) :=
  oneMid_ok v (h.oneCtx M.ge) e rfl rfl rfl

theorem general_aad_rel (v : GcmImpl) (h : Layout M s) (g : Layout M d) (pub : Gather.Pub s d) :
    RelCT isa (fun u z => Layout.Initial s u ∧ Layout.Initial d z) (oneAad v.callees) fun _ _ => True := by
  have c := h.oneCtx M.ge
  apply (oneAad_rel v c.lay c.dE (T:=none) (M:=M) (R:=R s) (Np:=Nn s) (nl:=NL s)
    (al:=(AL s).toNat) (A:=Ad s)).mono _ (fun _ _ _ => trivial)
  intro u z ⟨e,f⟩
  refine ⟨e.aadPre c h.ext rfl rfl rfl rfl, ?_⟩
  have other := f.aadPre (g.oneCtx M.ge) g.ext rfl rfl rfl rfl
  have key : K d=K s := pub.rdi
  have nonce : Nn d=Nn s := pub.rdx
  have nonceLen : NL d=NL s := congrArg BitVec.toNat pub.rcx
  have ap : Ad d=Ad s := pub.r8
  have al : AL d=AL s := pub.r9
  have sp : SP d=SP s := pub.rsp
  have rounds : R d=R s := congrArg BitVec.toNat pub.rsi
  have len : L d=L s := congrArg BitVec.toNat pub.len
  have work : W d=W s := pub.a 5 (by decide)
  change OneS M (K d) (W d) (SP d) (R d) (Ad d) (AL d).toNat (Dst d) (L d) none z ∧
    z.gpr .r12=Nn d ∧ z.gpr .rbp=BitVec.ofNat 64 (NL d) ∧
    DataOk (W d+16#64) (W d) (SP d) z (Nn d) (NL d) at other
  simpa only [key,nonce,nonceLen,ap,al,sp,rounds,len,work,pub.dst] using other

end VG.Proof.AesGcm.X86_64.DirectGather

/-! The descriptor loop encrypts bytes following an optional, already authenticated first-slice prefix. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gctr blockAt zeros padLen)
open VG.Proof.Gcm (Ctr Absorbed)

def skip (pre i : Nat) := if i=0 then pre else 0
def consumed (s : State) (pre i : Nat) := gl s i+skip pre i
def plainPrefix (s : State) (pre i : Nat) :=
  if i=0 then bytesAt s.mem (sb s 0) pre else pt s i

structure LoopAt (_M : CtxMode) (s : State) (pre i : Nat) (t : State) : Prop where
  env : Env (K s) (W s+16#64) (W s) (SP s) t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  saved : SavedAt t.mem (W s) s
  frame : Frame (changed s) s.mem t.mem
  preLen : pre≤L s
  inFirst : 0<Cnt s → pre≤sl s 0
  noFirst : Cnt s=0 → pre=0
  aligned : pre%16=0
  desc : t.mem.readW (W s+256#64) 64=Src s+BitVec.ofNat 64 (16*i)
  num : t.mem.readW (W s+224#64) 64=BitVec.ofNat 64 (Cnt s-i)
  span : t.mem.readW (W s+240#64) 64=BitVec.ofNat 64 (consumed s pre i-pre)
  skipAt : t.mem.readW (W s+264#64) 64=BitVec.ofNat 64 (skip pre i)
  data : t.mem.readW (W s+200#64) 64=Dst s+BitVec.ofNat 64 pre
  len : t.mem.readW (W s+208#64) 64=BitVec.ofNat 64 (L s-pre)
  total : t.mem.readW (W s+192#64) 64=BitVec.ofNat 64 (L s)
  aad : t.mem.readW (W s+184#64) 64=AL s
  rounds : RoundsAt t.mem (W s) (R s)
  key : ciphOf t.mem (K s) (R s)=ciph s
  hkey : blockAt t.mem (K s+240#64)=hk s
  j0 : blockAt t.mem (W s+16#64)=Spec.Gcm.j0 (hk s) (iv s)
  auth : Absorbed t.mem (W s+16#64+16#64) (W s+16#64+32#64) (hk s)
    (ad s ++ zeros (padLen (ad s).length) ++ bytesAt t.mem (Dst s) pre)
  ctr : Ctr t.mem (W s+16#64+48#64) (W s+16#64+64#64) (ciph s) (icb s) (consumed s pre i)
  out : bytesAt t.mem (Dst s) (consumed s pre i)=gctr (ciph s) (icb s) (plainPrefix s pre i)

theorem LoopAt.done {M : CtxMode} {s t : State} {pre : Nat} (h : Layout M s)
    (a : LoopAt M s pre (Cnt s) t) : TextDone M s t pre := by
  refine ⟨a.env,a.rd,a.wr,a.saved,a.frame,?_,a.preLen,a.aligned,a.data,a.len,a.total,a.aad,
    a.rounds,a.key,a.hkey,a.j0,a.auth⟩
  have out := a.out
  by_cases z : Cnt s=0
  · have pre0 := a.noFirst z
    have len0 : L s=0 := by rw [← h.glen,z,gl_zero]
    simpa [z,pre0,len0,consumed,skip,plainPrefix,gl_zero,pt,Spec.Gcm.gathered,Sig.listed,bytesAt] using out
  · simpa [consumed,skip,plainPrefix,z,h.glen] using out

end VG.Proof.AesGcm.X86_64.DirectGather
