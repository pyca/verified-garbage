module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Top
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Contracts
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Top
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Contracts
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.TCB.Axioms

/-! # `vg_mlkem768_keygen` and `vg_mlkem1024_keygen` hashing `ek` during the matrix

`Kem16.keyGenH` meets `Spec.MlKem.keyGenContract` with 128 bytes of stack, for
the `x3` calls: the contract (as `Hybrid/Final.lean` for encapsulation), the
taint analyses of its pieces, decided on each parameter set, and `Verified`
(`keyGenH768_verified`, `keyGenH1024_verified`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (entryContractS entryS_tables habs_of)
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash hole symSums)
open VG.Proof.MlKem

/-! ## The pieces' taint analyses -/

theorem habsK768 : ∀ blk, 136 * blk < (Kem16.kgSrc lay768).len → ∃ h,
    (taint.check (Taint.ofRegs [(Kem16.kgSrc lay768).r, .x28])
      (.block (Hybrid.absorbBlock (Kem16.kgSrc lay768) blk)) h).isSome = true :=
  habs_of _ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩

theorem habsK1024 : ∀ blk, 136 * blk < (Kem16.kgSrc Impl.MlKem1024.AArch64.lay1024).len → ∃ h,
    (taint.check (Taint.ofRegs [(Kem16.kgSrc Impl.MlKem1024.AArch64.lay1024).r, .x28])
      (.block (Hybrid.absorbBlock (Kem16.kgSrc Impl.MlKem1024.AArch64.lay1024) blk)) h).isSome = true :=
  habs_of _ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩

theorem kgPre768_taint : ∃ h, ((VectorSymbols.analysis restSymbols).check
    (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Kem16.kgPre lay768) h).isSome = true := ⟨_, by taint_decide⟩

theorem kgPre1024_taint : ∃ h, ((VectorSymbols.analysis restSymbols).check
    (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Kem16.kgPre Impl.MlKem1024.AArch64.lay1024) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem kgRow768_taint : ∀ i < lay768.k, ∃ h, ((VectorSymbols.analysis restSymbols).check
    (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Kem16.kgRow lay768 i) h).isSome = true := fun i hi => by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by have : lay768.k = 3 := rfl; omega) with rfl | rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem kgRow1024_taint : ∀ i < Impl.MlKem1024.AArch64.lay1024.k, ∃ h, ((VectorSymbols.analysis restSymbols).check
    (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Kem16.kgRow Impl.MlKem1024.AArch64.lay1024 i) h).isSome = true :=
  fun i hi => by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by
    have : Impl.MlKem1024.AArch64.lay1024.k = 4 := rfl; omega) with rfl | rfl | rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem kgTail768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgTail c lay768) h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem kgTail1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgTail c Impl.MlKem1024.AArch64.lay1024) h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem kgPre768_depth : (Kem16.kgPre lay768).aarch64Depth ≤ 1 := by decide
theorem kgPre1024_depth : (Kem16.kgPre Impl.MlKem1024.AArch64.lay1024).aarch64Depth ≤ 1 := by decide

/-! ## ML-KEM-768 -/

theorem keyGenS768_base : (keyGenAArch64S lay768).Implies (Spec.MlKem.keyGenContract abi 128) := by
  mlkem_implies [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenAArch64S, keyGenAArch64, lay768,
      KemLay.params, Spec.MlKem.mlKem768, KemLay.ekLen, KemLay.dkLen, AArch64.abi, AArch64.argRegs]
      [VG.Proof.MlKem.AArch64.KeyGen.sat] using VG.Proof.MlKem.AArch64.KeyGen.sat

def keyGenH768Contract := Spec.MlKem.keyGenContract (abi.withConsts constants) 128

theorem keyGenH768_entry {s : State} (h : keyGenH768Contract.pre s) :
    (entryContractS (keyGenAArch64S lay768)).pre s := by
  unfold keyGenH768Contract Spec.MlKem.keyGenContract constants at h
  have hp := pre_consts.mp h
  exact ⟨keyGenS768_base.pre _ hp.1, hp.2⟩

theorem keyGenH768_post {s t : State} (h : keyGenH768Contract.pre s)
    (hp : (keyGenAArch64S lay768).post s t) : keyGenH768Contract.post s t := by
  unfold keyGenH768Contract Spec.MlKem.keyGenContract constants at h ⊢
  have hh := pre_consts.mp h
  exact keyGenS768_base.post (stripConsts constants s) t hh.1 hp

theorem keyGenH768_pub {s t : State} (hs : keyGenH768Contract.pre s) (ht : keyGenH768Contract.pre t)
    (hp : keyGenH768Contract.pub s t) : (entryContractS (keyGenAArch64S lay768)).pub s t := by
  unfold keyGenH768Contract Spec.MlKem.keyGenContract constants at hs ht hp
  have hsp := pre_consts.mp hs
  have htp := pre_consts.mp ht
  have hpp := pub_consts.mp hp
  exact ⟨keyGenS768_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1, hpp.2⟩

theorem keyGenH768_sat : ∃ s, keyGenH768Contract.pre s := by
  refine ⟨addTables VG.Proof.MlKem.AArch64.KeyGen.sat, ?_⟩
  unfold keyGenH768Contract Spec.MlKem.keyGenContract constants
  apply pre_consts.mpr
  constructor
  · change (Spec.MlKem.keyGenContract abi 128).pre
      (stripConsts constants (addTables VG.Proof.MlKem.AArch64.KeyGen.sat))
    rw [strip_addTables]
    sig_pre [Spec.MlKem.keyGenSig, abi, argRegs]
    and_intros
    all_goals first
     | rfl
     | decide
     | exact Region.disjoint_of_sep (by decide)
  · change ConstsOk constants 128 (addTables VG.Proof.MlKem.AArch64.KeyGen.sat)
    refine ⟨?_, tableMem_held, ?_⟩
    · rfl
    · intro r hr
      rw [constants_regions] at hr
      rcases hr with _|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩
      all_goals first
       | contradiction
       | (refine ⟨by decide, ?_, ?_⟩
          · intro q hq
            change q ∈ VG.Proof.MlKem.AArch64.KeyGen.sat.wr at hq
            simp only [VG.Proof.MlKem.AArch64.KeyGen.sat, List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
          · intro q hq
            change q ∈ [below (0x100000:Addr) 128] at hq
            rw [List.mem_singleton.mp hq]
            exact Region.disjoint_of_sep (by decide))

theorem keyGenH768_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (Kem16.keyGenH (fixedHash v.callee) v.callee lay768) keyGenH768Contract := by
  refine Verified.of_correct (T := AArch64.target) (k := entryContractS (keyGenAArch64S lay768)) ?_
    (keyGenH_ct v (fixedHash v.callee) (FixedHash.kgG768_correct v) VG.Proof.MlKem.AArch64.KeyGen.wf768 Noise.room768 (FixedHash.kgA768_depth v) kgPre768_depth
      (FixedHash.kgA768_taint v.callee v.callerSums) kgPre768_taint kgRow768_taint habsK768
      (kgTail768_taint v.callee (symSums v))) ?_
  · intro s h
    have ss := preKS h.1
    have ts := entryS_tables h
    exact using_correctH v (fixedHash v.callee) (FixedHash.kgG768_correct v) (keygen_unstrip (pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 ss.1))
      ⟨ss.2.1, ss.2.2⟩ Noise.room768 ts.1 ts.2 (FixedHash.kgA768_depth v) kgPre768_depth
  · exact ⟨fun _ h => keyGenH768_entry h, fun _ _ h hp => keyGenH768_post h hp,
      fun _ _ hs ht hp => keyGenH768_pub hs ht hp, keyGenH768_sat⟩

/-! ## ML-KEM-1024 -/

theorem keyGenS1024_base : (keyGenAArch64S Impl.MlKem1024.AArch64.lay1024).Implies (Spec.MlKem1024.keyGenContract abi 128) := by
  mlkem_implies [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenAArch64S, keyGenAArch64, Impl.MlKem1024.AArch64.lay1024,
      KemLay.params, Spec.MlKem.mlKem1024, KemLay.ekLen, KemLay.dkLen, AArch64.abi, AArch64.argRegs]
      [VG.Proof.MlKem1024.AArch64.KeyGen.sat] using VG.Proof.MlKem1024.AArch64.KeyGen.sat

def keyGenH1024Contract := Spec.MlKem1024.keyGenContract (abi.withConsts constants) 128

theorem keyGenH1024_entry {s : State} (h : keyGenH1024Contract.pre s) :
    (entryContractS (keyGenAArch64S Impl.MlKem1024.AArch64.lay1024)).pre s := by
  unfold keyGenH1024Contract Spec.MlKem1024.keyGenContract constants at h
  have hp := pre_consts.mp h
  exact ⟨keyGenS1024_base.pre _ hp.1, hp.2⟩

theorem keyGenH1024_post {s t : State} (h : keyGenH1024Contract.pre s)
    (hp : (keyGenAArch64S Impl.MlKem1024.AArch64.lay1024).post s t) : keyGenH1024Contract.post s t := by
  unfold keyGenH1024Contract Spec.MlKem1024.keyGenContract constants at h ⊢
  have hh := pre_consts.mp h
  exact keyGenS1024_base.post (stripConsts constants s) t hh.1 hp

theorem keyGenH1024_pub {s t : State} (hs : keyGenH1024Contract.pre s) (ht : keyGenH1024Contract.pre t)
    (hp : keyGenH1024Contract.pub s t) : (entryContractS (keyGenAArch64S Impl.MlKem1024.AArch64.lay1024)).pub s t := by
  unfold keyGenH1024Contract Spec.MlKem1024.keyGenContract constants at hs ht hp
  have hsp := pre_consts.mp hs
  have htp := pre_consts.mp ht
  have hpp := pub_consts.mp hp
  exact ⟨keyGenS1024_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1, hpp.2⟩

theorem keyGenH1024_sat : ∃ s, keyGenH1024Contract.pre s := by
  refine ⟨addTables VG.Proof.MlKem1024.AArch64.KeyGen.sat, ?_⟩
  unfold keyGenH1024Contract Spec.MlKem1024.keyGenContract constants
  apply pre_consts.mpr
  constructor
  · change (Spec.MlKem1024.keyGenContract abi 128).pre
      (stripConsts constants (addTables VG.Proof.MlKem1024.AArch64.KeyGen.sat))
    rw [strip_addTables]
    sig_pre [Spec.MlKem1024.keyGenSig, abi, argRegs]
    and_intros
    all_goals first
     | rfl
     | decide
     | exact Region.disjoint_of_sep (by decide)
  · change ConstsOk constants 128 (addTables VG.Proof.MlKem1024.AArch64.KeyGen.sat)
    refine ⟨?_, tableMem_held, ?_⟩
    · rfl
    · intro r hr
      rw [constants_regions] at hr
      rcases hr with _|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩
      all_goals first
       | contradiction
       | (refine ⟨by decide, ?_, ?_⟩
          · intro q hq
            change q ∈ VG.Proof.MlKem1024.AArch64.KeyGen.sat.wr at hq
            simp only [VG.Proof.MlKem1024.AArch64.KeyGen.sat, List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
          · intro q hq
            change q ∈ [below (0x100000:Addr) 128] at hq
            rw [List.mem_singleton.mp hq]
            exact Region.disjoint_of_sep (by decide))

theorem keyGenH1024_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (Kem16.keyGenH (fixedHash v.callee) v.callee Impl.MlKem1024.AArch64.lay1024) keyGenH1024Contract := by
  refine Verified.of_correct (T := AArch64.target) (k := entryContractS (keyGenAArch64S Impl.MlKem1024.AArch64.lay1024)) ?_
    (keyGenH_ct v (fixedHash v.callee) (FixedHash.kgG1024_correct v) VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 Noise.room1024 (FixedHash.kgA1024_depth v) kgPre1024_depth
      (FixedHash.kgA1024_taint v.callee v.callerSums) kgPre1024_taint kgRow1024_taint habsK1024
      (kgTail1024_taint v.callee (symSums v))) ?_
  · intro s h
    have ss := preKS h.1
    have ts := entryS_tables h
    exact using_correctH v (fixedHash v.callee) (FixedHash.kgG1024_correct v) (keygen_unstrip (pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 ss.1))
      ⟨ss.2.1, ss.2.2⟩ Noise.room1024 ts.1 ts.2 (FixedHash.kgA1024_depth v) kgPre1024_depth
  · exact ⟨fun _ h => keyGenH1024_entry h, fun _ _ h hp => keyGenH1024_post h hp,
      fun _ _ hs ht hp => keyGenH1024_pub hs ht hp, keyGenH1024_sat⟩

end VG.Proof.MlKem.AArch64.KeyGen
