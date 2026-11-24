module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.BoundCT
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Scrub
import VerifiedGarbage.Proof.AesGcm.Rounds
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks.Lit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Lit
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # Verified contiguous POWER AES-GCM seal with cleared secret register and stack residue -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.PPC64LE.Scrub VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

theorem post_of_result {s t : State} (z : finished s t) : contract.post s t := by
  sig_post [contract,sealContiguousContract,sealContiguousSig,sealContiguousPost,
    VG.PPC64LE.abi,VG.PPC64LE.argRegs,List.getD,List.range,List.range.loop]
  intro key valid
  obtain ⟨cx,hh,_⟩ := Proof.AesGcm.keyRounds_ctx valid
  change (_,_) = encryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) _ _ _ _ _ at z
  rw [cx,hh,←encrypt_eq] at z
  exact z.symm

private def witness : State := { Gather.gatherSat with
  gpr := fun r => match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 | .r10 => 0x4000 | _ => 0
  mem := fun _ => 0
  rd := [⟨0x1000,256⟩,⟨0x2000,0⟩,⟨0x3000,0⟩,⟨0x9060,16⟩]
  wr := [⟨0x4000,0⟩,⟨0,16⟩] }

private theorem sat : ∃ s,contract.pre s := by
  refine ⟨witness,?_⟩
  sig_pre [contract,sealContiguousContract,sealContiguousSig,Spec.Gcm.sealPre,VG.PPC64LE.abi,VG.PPC64LE.argRegs,
    List.getD,List.range,List.range.loop,witness,Gather.gatherSat,stackArg,stackArgAddr,Mem.readW,Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)

private theorem correct [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] : Verified target framed contract :=
  ⟨fun _ h => WP.mono (framed_wp (layout_of_pre h)) fun _ ⟨abi,out⟩ => ⟨abi,post_of_result out⟩,timing,sat⟩

private theorem post_out : PostOut contract 0 := by
  intro s t u h out same _
  have params := layout_of_pre h
  have keep (r : Region) (mem : r∈[dstR s,tagR s]) (fit : r.len≤2^64) : bytesAt u.mem r.base r.len=bytesAt t.mem r.base r.len := by
    apply Proof.AesGcm.bytesAt_congr
    intro i hi
    exact same _ ⟨r,List.mem_append_right _ (params.wr ▸ mem),Offset.contains_base _ (by omega : i+1≤r.len) (Nat.lt_of_lt_of_le hi fit)⟩
  have dst := keep (dstR s) (by simp) (Nat.le_of_lt (stackArg s 0).isLt)
  have tag := keep (tagR s) (by simp) (by decide : 16≤2^64)
  sig_post [contract,sealContiguousContract,sealContiguousSig,sealContiguousPost,
    VG.PPC64LE.abi,VG.PPC64LE.argRegs,List.getD,List.range,List.range.loop] at out ⊢
  simpa only [dst,tag] using out

theorem scrubbed [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    VerifiedScrubbed target VG.Impl.AesGcm.PPC64LE.Contiguous.code contract 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.sealContiguousApi) {code := framed,verified := correct}
    1280 VG.Proof.AesGcm.PPC64LE.Scrub.clearAll post_out (by dsimp only;lit_decide)

end VG.Proof.AesGcm.PPC64LE.Contiguous
