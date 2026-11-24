module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousBulk
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousCtr
import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Call
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous
/-! Equal leakage from different keys and plaintexts with the same public
pointers, lengths, and round count. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open Split (SealRegions)
open Short (rel_next)
open Split.Compact (compactContract compactInput callable)

structure KernelIn (M : CtxMode) (Ctx W SP S D : Addr) (R n : Nat) (s : State) : Prop where
  reg : SealRegions M Ctx W SP D S R n n s
  count : s.gpr .rax=BitVec.ofNat 64 (n/16)
  read : InRegions (s.rd++s.wr) (SP+8#64) 8
  src : s.mem.readW (SP+8#64) 64=S
  dst : s.mem.readW (W+200#64) 64=D
  len : s.mem.readW (W+208#64) 64=BitVec.ofNat 64 n

def KernelCT (M : CtxMode) (kernel : Prog isa) : Prop :=
  ∀ {Ctx W SP S D : Addr} {R n : Nat}, RelCT isa
    (fun a b => KernelIn M Ctx W SP S D R n a ∧ KernelIn M Ctx W SP S D R n b) kernel (fun _ _ => True)

private structure CallArgs (Ctx W SP S D : Addr) (R n : Nat) (s t : State) : Prop where
  k : t.gpr .rdi=Ctx
  nr : t.gpr .rsi=BitVec.ofNat 64 R
  cb : t.gpr .rdx=W+16#64+48#64
  y : t.gpr .rcx=W+16#64+16#64
  src : t.gpr .r8=S
  count : t.gpr .r9=BitVec.ofNat 64 (n/16)
  dst : t.gpr .r10=D
  work : t.gpr .rax=W+448#64
  sp : t.gpr .rsp=SP
  mem : t.mem=s.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr

theorem fused_ct {M : CtxMode} (T : BlocksTo.SealFn M) : KernelCT M (Contiguous.fused T.fn) := by
  intro Ctx W SP S D R n
  apply Split.rel_each
  intro a b ⟨ha,hb⟩
  have pre {s : State} (h : KernelIn M Ctx W SP S D R n s) :
      WP isa (.block Contiguous.fusedArgs) s (CallArgs Ctx W SP S D R n s) :=
    (fusedArgs_ok h.reg.env h.reg.rounds h.read h.src h.dst).mono fun _ ⟨k,r,c,y,i,q,d,w,g,m,rd,wr⟩ =>
      ⟨k,r,c,y,i,q.trans h.count,d,w,(g _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans h.reg.env.rsp,m,rd,wr⟩
  unfold Contiguous.fused Contiguous.call
  refine RelCT.seq (rel_next (F₁:=fun s => s=a) (F₂:=fun s => s=b)
    (G₁:=CallArgs Ctx W SP S D R n a) (G₂:=CallArgs Ctx W SP S D R n b)
    (rel_taint [.r13,.r14,.r15,.rsp] (fun x y h => by
      obtain ⟨rfl,rfl⟩ := h; exact env_agree ha.reg.env hb.reg.env) ⟨_,by taint_decide⟩)
    (fun _ eq => by subst eq; exact pre ha) (fun _ eq => by subst eq; exact pre hb)) ?_
  refine RelCT.frame (fun _ _ hp => hp.1.sp.trans hp.2.sp.symm)
    (RelCT.callEx (k:=compactContract M) (callable T) T.ct fun _ _ hp => ?_)
  obtain ⟨x,y,⟨hx,hy⟩,rfl,rfl⟩ := hp
  have leaf {s t : State} (h : KernelIn M Ctx W SP S D R n s) (args : CallArgs Ctx W SP S D R n s t) :=
    compactInput h.reg (Nat.mul_div_le n 16) args.sp args.rd args.wr args.mem args.k args.nr args.cb args.y args.src
      args.count args.dst args.work
  obtain ⟨p₁,r₁,w₁,g₁,sp₁,sc₁⟩ := leaf ha hx
  obtain ⟨p₂,r₂,w₂,g₂,sp₂,sc₂⟩ := leaf hb hy
  refine ⟨_,_,_,_,p₁,p₂,?_,r₁,w₁,r₂,w₂,by simp [pushed_rsp,hx.sp,hy.sp]⟩
  constructor
  all_goals first
    | exact sp₂.trans sp₁.symm
    | exact sc₂.trans sc₁.symm
    | (try simp only [BlocksTo.K,BlocksTo.C,BlocksTo.Y,BlocksTo.Src,BlocksTo.Dst,↓reduceIte])
      rw [g₂ _ (by decide),g₁ _ (by decide)]
      first | exact hy.k.trans hx.k.symm | exact hy.nr.trans hx.nr.symm | exact hy.cb.trans hx.cb.symm
            | exact hy.y.trans hx.y.symm | exact hy.src.trans hx.src.symm | exact hy.count.trans hx.count.symm
            | exact hy.dst.trans hx.dst.symm

private structure HashReady (Ctx W SP D : Addr) (n : Nat) (s : State) : Prop where
  lay : Lay Ctx (W+16#64) W SP
  env : Env Ctx (W+16#64) W SP s
  data : DataW Ctx (W+16#64) W SP s D n
  dst : s.mem.readW (W+200#64) 64=D
  len : s.mem.readW (W+208#64) 64=BitVec.ofNat 64 n

theorem separate_ct {M : CtxMode} (ctr : Proof.Aes.X86_64.Ctr32ToImpl) (gh : GhashImpl) :
    KernelCT M (Contiguous.separate ⟨ctr.callee.name,ctr.callee.code⟩ gh.fn) := by
  intro Ctx W SP S D R n
  let q := n/16
  let C : State → Prop := fun t => HashReady Ctx W SP D n t ∧ CtrToCall t Ctx (cbA W) S D (W+448#64) R q
  have prep {s : State} (h : KernelIn M Ctx W SP S D R n s) : WP isa (.block Contiguous.ctrArgs) s C := by
    refine (ctrArgs_ok h.reg (Nat.mul_div_le n 16) h.count h.read h.src h.dst).mono fun t ⟨saved,rd,wr,mem,call⟩ => ?_
    exact ⟨⟨h.reg.lay,h.reg.env.of_saved saved rd wr,h.reg.data.of_eq rd wr,mem ▸ h.dst,mem ▸ h.len⟩,call⟩
  have finishCtr {s : State} (h : C s) : WP isa (.call ctr.callee.name ctr.callee.code) s (HashReady Ctx W SP D n) := by
    refine (ctrTo_call ctr h.2).mono fun t o => ?_
    have ft := o.frame
    rw [h.1.env.rsp] at ft
    have atW (i : Nat) (lo : 176≤i) (hi : i+8≤240) : t.mem.readW (W+BitVec.ofNat 64 i) 64=s.mem.readW (W+BitVec.ofNat 64 i) 64 := by
      refine ft.readW (r:=⟨W+BitVec.ofNat 64 i,8⟩) (Region.contains_self _ _) (fun b hb => ?_) (by decide)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      · rw [cbA,add_ofNat_assoc]; exact Offset.disjoint W (e:=64) (.inr (by omega_using [lo])) (by omega_using [hi]) (by decide)
      · exact ((h.1.data.ok.w.sub_left (Region.sub_prefix (Nat.mul_div_le n 16))).sub_right (Lay.wSub (by omega_using [hi]))).symm
      · exact Offset.disjoint W (.inl (by omega_using [hi])) (by omega_using [hi]) (by decide)
      · exact (h.1.lay.stk_w (by omega_using [hi])).symm
    exact ⟨h.1.lay,h.1.env.of_saved o.saved o.rd o.wr,h.1.data.of_eq o.rd o.wr,(atW 200 (by decide) (by decide)).trans h.1.dst,
      (atW 208 (by decide) (by decide)).trans h.1.len⟩
  unfold Contiguous.separate Contiguous.call
  refine RelCT.seq (rel_next (rel_taint [.r13,.r14,.r15,.rsp] (fun _ _ h => env_agree h.1.reg.env h.2.reg.env)
    ⟨_,by taint_decide⟩) (fun _ => prep) (fun _ => prep)) ?_
  refine RelCT.seq (rel_next (ctrTo_rel ctr (fun _ _ h => ⟨_,_,_,_,_,_,_,h.1.2,h.2.2,h.1.1.env.rsp.trans h.2.1.env.rsp.symm⟩))
    (fun _ => finishCtr) (fun _ => finishCtr)) ?_
  apply Split.rel_each
  intro u z ⟨hu,hz⟩
  let H : State → Prop := fun t => GhCall t (Ctx+240#64) (yA W) D (W+448#64) q ∧ t.gpr .rsp=SP
  have prepH {s : State} (h : HashReady Ctx W SP D n s) : WP isa (.block Contiguous.hashArgs) s H := by
    refine (hashArgs_ok h.lay h.env h.data h.dst h.len).mono fun t ⟨saved,_,_,_,call⟩ => ⟨call,(saved _ (by decide)).trans h.env.rsp⟩
  refine RelCT.seq (rel_next (F₁:=fun s => s=u) (F₂:=fun s => s=z) (G₁:=H) (G₂:=H)
    (rel_taint [.r13,.r14,.r15,.rsp] (fun _ _ ⟨hu',hz'⟩ => by subst hu'; subst hz'; exact env_agree hu.env hz.env)
      ⟨_,by taint_decide⟩) (fun _ h => by subst h; exact prepH hu) (fun _ h => by subst h; exact prepH hz))
    (gh_rel gh (fun _ _ h => ⟨_,_,_,_,_,h.1.1,h.2.1,h.1.2.trans h.2.2.symm⟩))

end VG.Proof.AesGcm.X86_64.ContiguousSeal
