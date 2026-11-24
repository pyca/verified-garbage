module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneAuth
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneReturn
import VerifiedGarbage.Proof.AesGcm.AArch64.Body

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Spec.Gcm VG.Proof.Gcm
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone (padded)
variable {wn : Nat} {W : Addr} {s a b : State}

abbrev authCode (v : Calls) : Prog isa := .seq (.block DirectGather.suffixStart) (VG.Impl.AesGcm.AArch64.Contiguous.Standalone.padded v.callees)

structure AuthOut (wn : Nat) (W : Addr) (s b t : State) : Prop where
  env : Env wn (s.gpr .x0) (W+16#64) W s.sp t
  kept : Kept b.gpr t
  hash : blockAt t.mem (W+16#64+16#64) = ghash (ctxH s.mem (s.gpr .x0)) (blocks (VG.Proof.Gcm.padded (aadBytes s) (ctBytes s b)))
  frame : Frame (padFrame (W+16#64) W) b.mem t.mem
  rd : t.rd=b.rd
  wr : t.wr=b.wr

theorem auth_stage (v : GcmImpl) (c : Inner wn W s) (f : FrontOut wn W s a)
    (e : EncOut wn (s.gpr .x1).toNat (stackArg s 0).toNat (s.gpr .x0) (W+16#64) W s.sp
      (s.gpr .x6) (s.gpr .x7) (inc32 (J s)) (aadHash s) a b) :
    WP isa (authCode v.calls) b (AuthOut wn W s b) := by
  obtain ⟨j,le,slot,acc⟩ := e.auth
  have before := returnPrep (t := b) c f e (Frame.refl _ _)
  have h : ctxH a.mem (s.gpr .x0) = ctxH s.mem (s.gpr .x0) := by
    apply blockAt_frame f.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact c.lay.cw'.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
  rw [h] at acc
  refine (WP.with_rdwr (auth_ok c.lay v e.env (k := b.gpr) (fun _ _ => rfl)
    (c.dst.ok.of_eq (e.rd.trans f.rd) (e.wr.trans f.wr)) le e.x26 slot (aadBytes s) _ before.hash acc)).mono ?_
  rintro t ⟨⟨env,keep,h,fr⟩,rd,wr⟩
  exact ⟨env,keep,h,fr,rd,wr⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
