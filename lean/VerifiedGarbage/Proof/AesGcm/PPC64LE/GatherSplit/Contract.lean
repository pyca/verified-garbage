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
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `AesGcm.PPC64LE.Gather.CT`, which this module and modules that import it used -/

section

/-!
# AES-GCM encryption out of place, from a list of slices, PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments and
descriptors agree (`gatherPub`) leak the same trace: the frame's push, the
entry, the loads of the call's arguments and of the return address are at
the stack pointer or our frame; the gathering is constant time by
`gather_rel` (`Proof/Gather/PPC64LE/LoopCT.lean`); and the call is constant
time by its callee's contract, whose public arguments agree
(`body_rel`). As for ChaCha20-Poly1305
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Gather

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.SealGather
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint ct_of gather_rel)

theorem entered_desc {σ₁ σ₂ e₁ e₂ : State} (h₁ : Lay σ₁) (h₂ : Lay σ₂)
    (hq : gatherPub σ₁ σ₂) (he₁ : Entered σ₁ e₁) (he₂ : Entered σ₂ e₂) :
    ∀ j<Cnt σ₁*16,e₁.mem (Src σ₁+BitVec.ofNat 64 j)=e₂.mem (Src σ₁+BitVec.ofNat 64 j) := by
  obtain ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ := hq
  intro j hj
  have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ hj (by have := h₁.ods; omega_using [hj, this])
  have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
    simp only [dsR, Src, Cnt, ← q9, ← q10]; exact hx
  rw [he₁.mem, he₂.mem, Lay.keepE h₁.bds.symm hx, Lay.keepE h₂.bds.symm hx₂]
  exact hdesc j hj

theorem body_rel (hv : SealOk)
    (hct : ConstantTime isa (Proof.AesGcm.sealRoundsContract PPC64LE.abi 1264).pre
      (Proof.AesGcm.sealRoundsContract PPC64LE.abi 1264).pub sealCode)
    {σ₁ σ₂ e₁ e₂ : State} (h₁ : Lay σ₁) (h₂ : Lay σ₂) (hq : gatherPub σ₁ σ₂)
    (he₁ : Entered σ₁ e₁) (he₂ : Entered σ₂ e₂) :
    RelCT isa (Eq2 e₁ e₂) body TT := by
  unfold body
  obtain ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ := hq
  have hP : Pf σ₁=Pf σ₂ := by simp only [Pf,Bs,qsp]
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← q9, ← q10, ← a0, ← a1] at g₂
  have hd := entered_desc h₁ h₂ ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ he₁ he₂
  refine rel_seq (gather_rel hd g₁ g₂ (by rw [he₁.sp, he₂.sp, hP])) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂)
    fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_taint [.r12] (by rw [hg₁.sp, hg₂.sp, hP]) (by simp [hg₁.r12, hg₂.r12, hP])
    (by taint_decide)) (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by simp only [rdC, cR, nR, aR, C, Nn, NL, Ad, AL, aOut, Pf, Bs, q3, q5, q6, q7, q8, qsp]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, a0, a1, a2]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r3₁, r4₁, r5₁, r6₁, r7₁, r8₁, r9₁, r10₁⟩ := hc₁.callGpr
  obtain ⟨r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, r10₂⟩ := hc₂.callGpr
  refine rel_seq (RelCT.call hv hct (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ?_, cv₁, cw₁, cv₂, cw₂⟩
      simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, r3₁, r4₁, r5₁, r6₁, r7₁,
        r8₁, r9₁, r10₁, r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, r10₂, hc₁.sp, hc₂.sp, hP, hc₁.arg h₁, hc₂.arg h₂, C, Nn,
        Ad, Dst, Tg, q3, q4, q5, q6, q7, q8, a0, a1, a2, and_self])
    (called_wp hv h₁ hc₁) (called_wp hv h₂ hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- The return address.
  exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by simp) (by taint_decide)


end VG.Proof.AesGcm.PPC64LE.Gather

end

end

/-! ### `AesGcm.PPC64LE.Gather.Verified`, which this module and modules that import it used -/

section

/-!
# AES-GCM encryption out of place, from a list of slices, PPC64LE: the shared contract

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_seal_gather`, with the 1424 bytes of stack below the stack
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
    (Proof.AesGcm.sealGatherRoundsContract PPC64LE.abi 1424).post s s' := by
  sig_post [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Proof.AesGcm.sealGatherRoundsPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArgs_three, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.sealGatherRoundsContract PPC64LE.abi 1424).pub s₁ s₂) :
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


def contract : Contract isa := Proof.AesGcm.sealGatherRoundsContract PPC64LE.abi 1552

structure Layout (s : State) : Prop where
  base : Gather.Lay s
  stack : ∀ r∈[cR s,nR s,aR s,dsR s]++lsR s++[dR s,tgR s,argR s], (below s.sp 1552).Disjoint r
  space : 1552≤s.sp.toNat


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
  have hb : Region.Sub (stkR s) (below s.sp 1552) := below_sub (by decide) (by decide)
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
