module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealGather
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.CT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame

/-! ### `AesGcm.PPC64LE.Gather.Verified`, which this module and modules that import it used -/

section

/-!
# AES-GCM encryption out of place, from a list of slices, PPC64LE: the shared contract

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_seal_gather`, with the 2832 bytes of stack below the stack
pointer that its frame and its call use (`Proof.AesGcm.sealGatherRoundsContract`):
its postcondition from the one the proof is written against
(`gatherPost_of`), its public arguments as `gatherPub` (`gatherPub_of`), and
a state that satisfies its precondition (`gatherSat`), for
`GatherSplit/Verified.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Gather

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.SealGather
open VG.Proof.ChaCha20Poly1305.PPC64LE.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Proof.AesGcm.sealGatherRoundsContract PPC64LE.abi 2832).post s s' := by
  sig_post [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Proof.AesGcm.sealGatherRoundsPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArgs_three, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.sealGatherRoundsContract PPC64LE.abi 2832).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, PPC64LE.abi,
    PPC64LE.argRegs, stackArgs_three, List.append_eq] at hp
  obtain ⟨qsp, q3, q4, q5, q6, q7, q8, q9, q10, a0, a1, a2, hd⟩ := hp
  exact ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, a1, a2, hd⟩

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather`: no
slices, nonce, additional data or text; the tag at `0x5000`, its address
the third stack argument, at `sp + 112`. -/
def gatherSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9071 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9060, 24⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

end VG.Proof.AesGcm.PPC64LE.Gather

end

end

-- separate module: the gather caller reserves the split-seal call's deeper frame.
/-! # The split gather caller's stack and buffer layout -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather
open VG.Proof.ChaCha20Poly1305.PPC64LE.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)


def contract : Contract isa := Proof.AesGcm.sealGatherRoundsContract PPC64LE.abi 2960

structure Layout (s : State) : Prop where
  base : Gather.Lay s
  stack : ∀ r∈[cR s,nR s,aR s,dsR s]++lsR s++[dR s,tgR s,argR s], (below s.sp 2960).Disjoint r
  space : 2960≤s.sp.toNat


theorem layout_pre {s : State} (h : contract.pre s) : Layout s := by
  sig_pre [contract,Proof.AesGcm.sealGatherRoundsContract,Spec.Gcm.sealGatherSig,Spec.Gcm.sealGatherPre,PPC64LE.abi,
    PPC64LE.argRegs,Gather.stackArgs_three,List.append_eq] at h
  simp only [List.map_append,List.filter_append,List.filter_map,List.map_map,List.filterMap_append,
    List.filterMap_map,List.map_cons,List.map_nil,List.filter_cons,List.filter_nil,Function.comp_def,
    Bool.not_false,Bool.false_eq_true,ite_true,ite_false,filter_true',filter_false',filterMap_some',
    filterMap_none',List.map_id',Sig.conj_cons,Sig.conj_append,Sig.conj_map,Bool.cond_false,Bool.cond_true,
    List.filterMap_cons,List.filterMap_nil,List.append_nil,List.nil_append,Sig.conj,Bool.true_or,
    List.cons_append,Sig.pairFacts] at h
  rw [pairFacts_ro _ (by simp)] at h
  obtain ⟨w₁,w₂,rd,wr,⟨cd,ct,nd,nt,ad,at_,dt,dds,⟨dl,da⟩,tds,⟨tl,ta⟩,-⟩,
    bc,bn,ba,bd,bt,⟨bds,bl,barg⟩,oc,on,oa,od,ot,⟨ods,ol⟩,hR,hg⟩ := h
  have hb : Region.Sub (stkR s) (below s.sp 2960) := below_sub (by decide) (by decide)
  have hp : gatherPre s :=
    ⟨by rw [rd]; simp,wr,cd,ct,nd,nt,ad,at_,dds.symm,tds.symm,
      fun r hr => ⟨(dl r hr).symm,(tl r hr).symm⟩,dt,da,ta,
      bc.sub_left hb,bn.sub_left hb,ba.sub_left hb,bds.sub_left hb,
      fun r hr => (bl r hr).sub_left hb,barg.sub_left hb,bd.sub_left hb,bt.sub_left hb,
      oc,on,oa,ods,ol,od,ot,by omega_using [w₁],by omega_using [w₂],hR,hg⟩
  refine ⟨Gather.lay hp,?_,w₁⟩
  intro r hr
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl) | hr) | (rfl | rfl | rfl)
  exacts [bc,bn,ba,bds,bl r hr,bd,bt,barg]

end VG.Proof.AesGcm.PPC64LE.GatherSplit
