module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealGather
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.CT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame

/-!
# AES-GCM encryption out of place, from a list of slices, PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_seal_gather`, with the 2832 bytes of stack below the stack
pointer that its frame and its call use (`Spec.Gcm.sealGatherContract`),
implies the one the proof is written against (`gatherPPC64LE`,
`gather_implies`), and so the code, calling `vg_aes_gcm_seal` by its shared
contract (`seal_framed`), is `Verified` against it (`sealGather_verified`).
As for ChaCha20-Poly1305 (`Proof/ChaCha20Poly1305/PPC64LE/Gather/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Gather

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.SealGather
open VG.Proof.ChaCha20Poly1305.PPC64LE.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem gatherPre_of_spec {s : State} (h : (Spec.Gcm.sealGatherContract PPC64LE.abi 2832).pre s) :
    gatherPre s := by
  sig_pre [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, PPC64LE.abi,
    PPC64LE.argRegs, stackArgs_three, List.append_eq] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or,
    List.cons_append, Sig.pairFacts] at h
  rw [pairFacts_ro _ (by simp)] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨cd, ct, nd, nt, ad, at_, dt, dds, ⟨dl, da⟩, tds, ⟨tl, ta⟩, -⟩,
    bc, bn, ba, bd, bt, ⟨bds, bl, barg⟩, oc, on, oa, od, ot, ⟨ods, ol⟩, hR, hg⟩ := h
  exact ⟨by rw [rd]; simp, wr, cd, ct, nd, nt, ad, at_, dds.symm, tds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm⟩, dt, da, ta, bc, bn, ba, bds, bl, barg, bd, bt, oc, on, oa,
    ods, ol, od, ot, w₁, by omega, hR, hg⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.Gcm.sealGatherContract PPC64LE.abi 2832).post s s' := by
  sig_post [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArgs_three, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Spec.Gcm.sealGatherContract PPC64LE.abi 2832).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, PPC64LE.abi,
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

theorem gatherSat_pre : ∃ s, (Spec.Gcm.sealGatherContract PPC64LE.abi 2832).pre s := by
  sig_implies_sat [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, PPC64LE.abi,
    PPC64LE.argRegs, stackArgs_three, List.append_eq]
    [gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using gatherSat

theorem gather_implies : gatherPPC64LE.Implies (Spec.Gcm.sealGatherContract PPC64LE.abi 2832) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (hs : gatherPPC64LE.pre s) :
    ∃ t s', Exec isa sealGather s t s' ∧ abiPreserved s s' ∧ gatherPPC64LE.post s s' :=
  sealGather_wp seal_framed.1 hs

theorem sealGather_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target sealGather (Spec.Gcm.sealGatherContract PPC64LE.abi 2832) :=
  Verified.of_correct (k := gatherPPC64LE) sealGather_correct (sealGather_ct seal_framed.1 seal_framed.2.1)
    gather_implies

end VG.Proof.AesGcm.PPC64LE.Gather
