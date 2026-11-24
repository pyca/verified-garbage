module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneAuthStage
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.TagReturn
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Front
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Spec.Gcm
open VG.Proof.Gcm VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (Y loadRev)
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone (tagPrep hwReturn)
open VG.Spec.Aes (bytesAt)
variable {wn : Nat} {C St W SP : Addr} {s a b u : State}

private theorem loadLength (e : Env wn C St W SP s) :
    WP isa (.block [.ldr .x .x26 .x19 lenO]) s fun t =>
      t.gpr .x26 = s.mem.readW (W+240#64) 64 ∧ Regs [.x26] s t ∧ t.v = s.v := by
  have h := e.perm.wR (d := 240) (n := 8) (by decide)
  refine WP.of_runBlock ⟨_,by arun [e.x19,h],?_⟩
  refine ⟨?_,⟨by others_tac,rfl,rfl,rfl,rfl⟩,rfl⟩
  simp only [gpr_write,ite_true]; rfl

theorem tagPrep_ok (e : Env wn C St W SP s) :
    WP isa (.block tagPrep) s fun t =>
      Fast.HKey (ctxH s.mem C) t ∧
      t.v Y = ext8 (blockAt s.mem (St+16#64)) (blockAt s.mem (St+16#64)) ∧
      t.gpr .x26 = s.mem.readW (W+240#64) 64 ∧ Regs [.x0,.x5,.x6,.x7,.x26] s t := by
  unfold tagPrep
  rw [WP.block_append_iff,WP.block_append_iff]
  refine (Fast.rawKey_ok e rfl).mono ?_
  intro v ⟨hk,reg⟩
  have ve := e.of_regs reg
  refine (loadRev_ok Y .x20 16 v (by decide) (by decide) (by rw [ve.x20]; exact ve.perm.stR (by decide))).mono ?_
  intro w ⟨y,r⟩
  have we := ve.keep (fun q _ => by rw [r.gpr]) r.sp r.rd r.wr
  refine (loadLength we).mono ?_
  intro z ⟨len,rz,vz⟩
  have kz := hk.of_v (by rw [vz,r.v _ (by decide)]) (by rw [vz,r.v _ (by decide)]) (by rw [vz,r.v _ (by decide)])
  refine ⟨kz,?_,?_,⟨?_,rz.mem.trans (r.mem.trans reg.mem),rz.sp.trans (r.sp.trans reg.sp),
    rz.rd.trans (r.rd.trans reg.rd),rz.wr.trans (r.wr.trans reg.wr)⟩⟩
  · rw [vz,y,ve.x20,reg.mem,rev64b_read]
  · rw [len,r.mem,reg.mem]
  · intro q h
    have small : [Reg.x26] ⊆ [.x0,.x5,.x6,.x7,.x26] := by decide
    have earlier : [Reg.x0,.x5,.x6,.x7] ⊆ [.x0,.x5,.x6,.x7,.x26] := by decide
    rw [rz.others _ (fun x => h (small x)),r.gpr]
    exact reg.others q (fun x => h (earlier x))

theorem hwFinish_ok (law : MulKey) (c : Inner wn W s) (f : FrontOut wn W s a)
    (e : EncOut wn (s.gpr .x1).toNat (stackArg s 0).toNat (s.gpr .x0) (W+16#64) W s.sp
      (s.gpr .x6) (s.gpr .x7) (inc32 (J s)) (aadHash s) a b)
    (au : AuthOut wn W s b u) :
    WP isa hwReturn u fun z => GprAbi s z ∧ result s z := by
  have hp := returnPrep c f e au.frame
  have hb := returnPrep (t := b) c f e (Frame.refl _ _)
  refine WP.seq ((tagPrep_ok au.env).mono ?_)
  rintro w ⟨key,y,len,r⟩
  rw [hp.hash] at key
  rw [au.hash,hb.cipher,←hp.cipher] at y
  have rounds := (r.others .x22 (by decide)).trans ((au.kept .x22 (by decide)).trans (e.x22.trans f.input.x22))
  have tag := (r.others .x28 (by decide)).trans ((au.kept .x28 (by decide)).trans (e.x28.trans f.x28))
  have wr := r.wr.trans (au.wr.trans (e.wr.trans f.wr))
  refine (Tag.return_ok (n := (stackArg s 0).toNat) (al := (s.gpr .x5).toNat) law (au.env.of_regs r)
    key y c.nr rounds (by simpa using len.trans hp.len) (stackArg s 0).isLt
    (by change w.mem.readW (W+224#64) 64 = _; rw [r.mem,hp.alen]; simp) (s.gpr .x5).isLt
    (r.mem ▸ hp.saved) (wr ▸ c.tag) tag c.tagWork).mono ?_
  intro z ⟨out,abi,fr⟩
  rw [r.mem] at out fr
  have ct : ctBytes s z = ctBytes s u := by
    apply bytesAt_frame fr _ (Nat.le_of_lt (stackArg s 0).isLt)
    intro q h; obtain rfl := List.mem_singleton.mp h; exact c.dstTag
  rw [hp.j,hp.key] at out
  refine ⟨abi,?_⟩
  change sealed s z z
  rw [sealed,encryptWith_eq,gctr_eq,←hp.cipher,fullTag_eq,ct,out]
  simp only [aadBytes,ctBytes,length_bytesAt]
  rfl

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
