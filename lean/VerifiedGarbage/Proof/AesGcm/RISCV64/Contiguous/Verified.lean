module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Contract
import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Timing
import VerifiedGarbage.Proof.AesGcm.RISCV64.GatherBs
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous

/-! # Verified public RISC-V contiguous AES-GCM, including register and stack scrubbing -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Spec.Gcm VG.RISCV64.Scrub
open VG.Spec.Aes (bytesAt)

private def witness : State := { GatherBs.gatherBsSat with
  gpr := fun r => match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 | .a7 => 0x4000 | _ => 0
  rd := [⟨0x1000,256⟩,⟨0x2000,0⟩,⟨0x3000,0⟩,⟨0x5000,1248⟩,⟨0x9000,24⟩]
  wr := [⟨0x4000,0⟩,⟨0,16⟩] }

private theorem sat : ∃ s,contract.pre s := by
  refine ⟨witness,?_⟩
  sig_pre [contract,sealContiguousBitslicedContract,sealContiguousAuxSig,sealContiguousSig,bitslicedParam,
    sealBitslicedPre,Spec.Gcm.sealPre,VG.RISCV64.abi,VG.RISCV64.argRegs,List.getD,List.range,List.range.loop,witness,
    GatherBs.gatherBsSat,stackArg,stackArgAddr]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.ctxSlicedRepr_of_zero (GatherBs.gatherBsSatMem_zero (p := (0x5000 : Addr)) (n := 1248) (by decide)) (GatherBs.gatherBsSatMem_zero (p := (0x1000 : Addr)) (n := 256) (by decide))

private theorem correct (run : PreparedInvocationLaw) : Verified target (framedWith VG.Impl.Gcm.RISCV64.Prepared.preparedInvocation) contract :=
  ⟨fun _ h => WP.mono (framed_prepared_wp run (caller_of_pre h) (prepared_of_pre h)) fun _ ⟨abi,result⟩ => ⟨abi,post_of_sealed result⟩,
    VG.Proof.Gather.RISCV64.ct_of fun _ _ h k p => framed_prepared_rel run (caller_of_pre h) (caller_of_pre k) (prepared_of_pre h) (prepared_of_pre k) (args_of_pub p),sat⟩

private theorem post_out : PostOut contract 0 := by
  intro s t u h out same _
  obtain data := caller_of_pre h
  have kept (r : Region) (cover : Covers [r] s.wr) (len : r.len<2^64) :
      bytesAt u.mem r.base r.len=bytesAt t.mem r.base r.len := by
    apply Proof.AesGcm.bytesAt_congr
    intro i hi
    obtain ⟨q,mem,hit⟩ := cover (r.base+BitVec.ofNat 64 i) 1 ⟨r,.head _,Offset.contains_base r.base (d := i) (n := 1) (k := r.len) (by omega) (by omega)⟩
    exact same _ ⟨q,List.mem_append_right _ mem,hit⟩
  have dst := kept _ data.dst (stackArg s 0).isLt
  have tag := kept _ data.tag (by decide : 16<2^64)
  sig_post [contract,sealContiguousBitslicedContract,sealContiguousAuxSig,sealContiguousSig,bitslicedParam,sealContiguousPost,
    VG.RISCV64.abi,VG.RISCV64.argRegs,List.getD,List.range,List.range.loop] at out ⊢
  simpa only [dst,tag] using out

theorem scrubbed (run : PreparedInvocationLaw) :
    VerifiedScrubbed target VG.Impl.AesGcm.RISCV64.Contiguous.code contract 0 :=
  verifiedScrubbedSel (api := sealContiguousBitslicedApi) (W := 4656)
    {code := framedWith VG.Impl.Gcm.RISCV64.Prepared.preparedInvocation,verified := correct run} VG.Impl.AesGcm.RISCV64.Contiguous.scrubFrames []
    post_out (by lit_decide) (hbp_nil _) residue

end VG.Proof.AesGcm.RISCV64.Contiguous
