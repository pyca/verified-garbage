module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousRecord
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
/-! The contiguous record ABI passes the original source and destination as
separate words. Preserve the return address, callee-saved registers and tag. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)
open VG.Spec.Aes (bytesAt)
open Short (SpanLayout)

abbrev K (s : State) := s.gpr .rdi
abbrev SP (s : State) := s.gpr .rsp
abbrev S (s : State) := stackArg s 0
abbrev D (s : State) := stackArg s 1
abbrev N (s : State) := (stackArg s 2).toNat
abbrev T (s : State) := stackArg s 3
abbrev W (s : State) := stackArg s 4

structure EntryPre (M : CtxMode) (s : State) : Prop where
  ctx : OneCtx s 5 (K s) (W s) (SP s) (s.gpr .rdx) (s.gpr .r8) (D s) (s.gpr .rcx).toNat (s.gpr .r9).toNat (N s)
  ext : CtxExt M (K s) (W s+16#64) (W s) (SP s) (D s) (N s) s
  geo : SpanLayout s (S s) (S s) (D s) (W s) (SP s) (N s) (N s)
  nowrap : (S s).toNat+N s≤2^64
  tw : Covers [⟨T s,16⟩] s.wr
  td : (⟨T s,16⟩ : Region).Disjoint ⟨D s,N s⟩
  tW : (⟨T s,16⟩ : Region).Disjoint ⟨W s,2560⟩
  rt : (⟨SP s,8⟩ : Region).Disjoint ⟨T s,16⟩

def EntryPost (s t : State) : Prop :=
  encryptWith (ctxCiph s.mem (K s) (s.gpr .rsi).toNat) (ctxH s.mem (K s)) 16
    (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (S s) (N s))
    (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) = (bytesAt t.mem (D s) (N s),bytesAt t.mem (T s) 16)

theorem entry_ok {M : CtxMode} {body : Prog isa} (h : RecordOk M body) {s : State} (p : EntryPre M s) :
    WP isa (.seq (.block (oneEntry 40 16 24)) (.seq body (.seq (.block (tagOut (at_ .rsp 32))) (.block restore)))) s
      fun t => gprPreserved s t ∧ EntryPost s t := by
  have C := p.ctx
  refine WP.seq ((oneEntryAt_okL (id:=1) (il:=2) (wo:=40) (by decide) (by decide) C rfl rfl rfl rfl rfl rfl
    (C.args 4 (by decide))).mono fun u ⟨E,_⟩ => ?_)
  refine WP.seq ((h C p.ext p.geo p.nowrap rfl E rfl rfl rfl).mono fun v ⟨env,rd,wr,saved,frame,ct,tag⟩ => WP.seq ?_)
  have sub : Region.Sub ⟨SP s+32#64,8⟩ ⟨SP s+8#64,8*5⟩ := by
    rw [show 32#64 = (BitVec.ofNat 64 (8+24)) from rfl,← add_ofNat_assoc]; exact Offset.sub_base _ (by decide)
  have slot : v.mem.readW (v.gpr .rsp+32#64) 64=T s := by
    rw [env.rsp,frame.readW (Region.contains_self _ _) (fun b hb => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl
      · exact C.dA.sub_left sub
      · exact C.dAD.sub_left sub
      · exact Offset.disjoint_below _ (n:=24) (d:=32) (k:=8) (by decide)) (by decide)]; rfl
  obtain ⟨z,run,tagOut,fr,g,zr,zw⟩ := tagOut_ok (b:=.rsp) (d:=32) env.r15 slot
    (by rw [env.rsp,rd,wr]; exact C.args 3 (by decide)) env.perm.w (wr ▸ p.tw)
  refine WP.of_runBlock ⟨z,run,?_⟩
  have ez := env.keep (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact g _ (by decide) (by decide) (by decide)) zr zw
  have sz : SavedAt z.mem (W s) s := saved.frame fr fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact (p.tW.sub_right (Lay.wSub (by decide))).symm
  have ret : z.mem.readW (SP s) 64 = s.mem.readW (SP s) 64 := by
    rw [ret_kept fr (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact p.rt),
        ret_kept frame (fun r hr => by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl
          · exact C.rW
          · exact C.rD
          · exact Offset.base_disjoint_below _ (n:=24) (k:=8) (by decide))]
  refine (exit_ok ez.r15 ez.rsp (covers_left ez.perm.w) sz ret).mono fun t ⟨regs,mem,_⟩ => ⟨regs,?_⟩
  have dst : bytesAt z.mem (D s) (N s) = bytesAt v.mem (D s) (N s) :=
    bytesAt_frame fr (fun b hb => by obtain rfl := List.mem_singleton.mp hb; exact p.td.symm) (by have := C.data.ok.lt; omega_arith)
  unfold EntryPost
  rw [Spec.Gcm.encryptWith,mem,tagOut,tag,dst,ct,Proof.Gcm.fullTag_eq,Proof.Gcm.length_gctr,length_bytesAt,length_bytesAt]
  simp only [Prod.mk.injEq,true_and]
  rw [List.take_of_length_le (by rw [Cmac.toBytes_length])]

end VG.Proof.AesGcm.X86_64.ContiguousSeal
