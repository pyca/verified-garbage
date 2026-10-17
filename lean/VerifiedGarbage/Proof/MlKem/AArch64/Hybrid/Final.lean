module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The hashing encapsulations meet `Spec.MlKem.encapsContract` with 128 bytes of stack

As `Optimized/Contracts.lean`, `ContractSat.lean` and
`FixedHash/EncapsVerified.lean`, for the stack of the x3 calls.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash prf prf_valid enG768_correct enG1024_correct)
open VG.Proof.MlKem

/-! ## ML-KEM-768 -/

theorem encapsS768_base : (encapsAArch64S lay768).Implies (Spec.MlKem.encapsContract abi 128) := by
  mlkem_implies [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encapsAArch64S, encapsAArch64, lay768,
      KemLay.params, Spec.MlKem.mlKem768, KemLay.ekLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs]
      [VG.Proof.MlKem.AArch64.Encaps.sat] using VG.Proof.MlKem.AArch64.Encaps.sat

def encapsH768Contract := Spec.MlKem.encapsContract (abi.withConsts constants) 128

theorem encapsH768_entry {s : State} (h : encapsH768Contract.pre s) :
    (entryContractS (encapsAArch64S lay768)).pre s := by
  unfold encapsH768Contract Spec.MlKem.encapsContract constants at h
  have hp := (pre_consts.mp h)
  exact ⟨encapsS768_base.pre _ hp.1,hp.2⟩

theorem encapsH768_post {s t : State} (h : encapsH768Contract.pre s)
    (hp : (encapsAArch64S lay768).post s t) : encapsH768Contract.post s t := by
  unfold encapsH768Contract Spec.MlKem.encapsContract constants at h ⊢
  have hh := pre_consts.mp h
  exact encapsS768_base.post (stripConsts constants s) t hh.1 hp

theorem encapsH768_pub {s t : State} (hs : encapsH768Contract.pre s) (ht : encapsH768Contract.pre t)
    (hp : encapsH768Contract.pub s t) : (entryContractS (encapsAArch64S lay768)).pub s t := by
  unfold encapsH768Contract Spec.MlKem.encapsContract constants at hs ht hp
  have hsp := pre_consts.mp hs
  have htp := pre_consts.mp ht
  have hpp := pub_consts.mp hp
  exact ⟨encapsS768_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1,hpp.2⟩

theorem encapsH768_sat : ∃s,encapsH768Contract.pre s := by
  refine ⟨addTables VG.Proof.MlKem.AArch64.Encaps.sat,?_⟩
  unfold encapsH768Contract Spec.MlKem.encapsContract constants
  apply pre_consts.mpr
  constructor
  · change (Spec.MlKem.encapsContract abi 128).pre (stripConsts constants (addTables VG.Proof.MlKem.AArch64.Encaps.sat))
    rw [strip_addTables]
    sig_pre [Spec.MlKem.encapsSig,abi,argRegs]
    and_intros
    all_goals first
     | rfl
     | decide
     | exact Region.disjoint_of_sep (by decide)
  · change ConstsOk constants 128 (addTables VG.Proof.MlKem.AArch64.Encaps.sat)
    refine ⟨?_,tableMem_held,?_⟩
    · rfl
    · intro r hr
      rw [constants_regions] at hr
      rcases hr with _|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩
      all_goals first
       | contradiction
       | (refine ⟨by decide,?_,?_⟩
          · intro q hq
            change q∈VG.Proof.MlKem.AArch64.Encaps.sat.wr at hq
            simp only [VG.Proof.MlKem.AArch64.Encaps.sat,List.mem_cons,List.not_mem_nil,or_false] at hq
            rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
          · intro q hq
            change q∈[below (0x100000:Addr) 128] at hq
            rw [List.mem_singleton.mp hq]
            exact Region.disjoint_of_sep (by decide))

theorem encapsH768_ct :
    ConstantTime isa (entryContractS (encapsAArch64S lay768)).pre (entryContractS (encapsAArch64S lay768)).pub
      (Impl.MlKem.AArch64.Hybrid.encaps fixedHash prf lay768) :=
  encapsH_ct fixedHash prf VG.Proof.MlKem.AArch64.KeyGen.wf768 hashOk768 habs768 startH768_taint restH768_taint

theorem encapsH768_verified :
    Verified AArch64.target (Impl.MlKem.AArch64.Hybrid.encaps fixedHash prf lay768) encapsH768Contract := by
  refine Verified.of_correct (T:=AArch64.target) (k:=entryContractS (encapsAArch64S lay768)) ?_ encapsH768_ct ?_
  · intro s h
    have ss := preS h.1
    have ts := entryS_tables h
    exact using_correctH fixedHash prf_valid enG768_correct
      (kem_unstrip (Encaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 ss.1)) ⟨ss.2.sp, ss.2.args⟩ hashOk768
      Noise.room768 VG.Proof.MlKem.AArch64.Encaps.calls768 ts.1 ts.2 matrixH768_depth tailH_depth
  · exact ⟨fun _ h=>encapsH768_entry h,fun _ _ h hp=>encapsH768_post h hp,
      fun _ _ hs ht hp=>encapsH768_pub hs ht hp,encapsH768_sat⟩

/-! ## ML-KEM-1024 -/

theorem encapsS1024_base :
    (encapsAArch64S Impl.MlKem1024.AArch64.lay1024).Implies (Spec.MlKem1024.encapsContract abi 128) := by
  mlkem_implies [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encapsAArch64S, encapsAArch64,
      Impl.MlKem1024.AArch64.lay1024, KemLay.params, Spec.MlKem.mlKem1024, KemLay.ekLen, KemLay.ctLen,
      AArch64.abi, AArch64.argRegs] [VG.Proof.MlKem1024.AArch64.Encaps.sat]
      using VG.Proof.MlKem1024.AArch64.Encaps.sat

def encapsH1024Contract := Spec.MlKem1024.encapsContract (abi.withConsts constants) 128

theorem encapsH1024_entry {s : State} (h : encapsH1024Contract.pre s) :
    (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pre s := by
  unfold encapsH1024Contract Spec.MlKem1024.encapsContract constants at h
  have hp := (pre_consts.mp h)
  exact ⟨encapsS1024_base.pre _ hp.1,hp.2⟩

theorem encapsH1024_post {s t : State} (h : encapsH1024Contract.pre s)
    (hp : (encapsAArch64S Impl.MlKem1024.AArch64.lay1024).post s t) : encapsH1024Contract.post s t := by
  unfold encapsH1024Contract Spec.MlKem1024.encapsContract constants at h ⊢
  have hh := pre_consts.mp h
  exact encapsS1024_base.post (stripConsts constants s) t hh.1 hp

theorem encapsH1024_pub {s t : State} (hs : encapsH1024Contract.pre s) (ht : encapsH1024Contract.pre t)
    (hp : encapsH1024Contract.pub s t) :
    (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pub s t := by
  unfold encapsH1024Contract Spec.MlKem1024.encapsContract constants at hs ht hp
  have hsp := pre_consts.mp hs
  have htp := pre_consts.mp ht
  have hpp := pub_consts.mp hp
  exact ⟨encapsS1024_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1,hpp.2⟩

theorem encapsH1024_sat : ∃s,encapsH1024Contract.pre s := by
  refine ⟨addTables VG.Proof.MlKem1024.AArch64.Encaps.sat,?_⟩
  unfold encapsH1024Contract Spec.MlKem1024.encapsContract constants
  apply pre_consts.mpr
  constructor
  · change (Spec.MlKem1024.encapsContract abi 128).pre
      (stripConsts constants (addTables VG.Proof.MlKem1024.AArch64.Encaps.sat))
    rw [strip_addTables]
    sig_pre [Spec.MlKem1024.encapsSig,abi,argRegs]
    and_intros
    all_goals first
     | rfl
     | decide
     | exact Region.disjoint_of_sep (by decide)
  · change ConstsOk constants 128 (addTables VG.Proof.MlKem1024.AArch64.Encaps.sat)
    refine ⟨?_,tableMem_held,?_⟩
    · rfl
    · intro r hr
      rw [constants_regions] at hr
      rcases hr with _|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩
      all_goals first
       | contradiction
       | (refine ⟨by decide,?_,?_⟩
          · intro q hq
            change q∈VG.Proof.MlKem1024.AArch64.Encaps.sat.wr at hq
            simp only [VG.Proof.MlKem1024.AArch64.Encaps.sat,List.mem_cons,List.not_mem_nil,or_false] at hq
            rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
          · intro q hq
            change q∈[below (0x100000:Addr) 128] at hq
            rw [List.mem_singleton.mp hq]
            exact Region.disjoint_of_sep (by decide))

theorem encapsH1024_ct :
    ConstantTime isa (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pre
      (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pub
      (Impl.MlKem.AArch64.Hybrid.encaps fixedHash prf Impl.MlKem1024.AArch64.lay1024) :=
  encapsH_ct fixedHash prf VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 hashOk1024 habs1024 startH1024_taint
    restH1024_taint

theorem encapsH1024_verified :
    Verified AArch64.target (Impl.MlKem.AArch64.Hybrid.encaps fixedHash prf Impl.MlKem1024.AArch64.lay1024)
      encapsH1024Contract := by
  refine Verified.of_correct (T:=AArch64.target)
    (k:=entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)) ?_ encapsH1024_ct ?_
  · intro s h
    have ss := preS h.1
    have ts := entryS_tables h
    exact using_correctH fixedHash prf_valid enG1024_correct
      (kem_unstrip (Encaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 ss.1)) ⟨ss.2.sp, ss.2.args⟩
      hashOk1024 Noise.room1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024 ts.1 ts.2 matrixH1024_depth
      tailH_depth
  · exact ⟨fun _ h=>encapsH1024_entry h,fun _ _ h hp=>encapsH1024_post h hp,
      fun _ _ hs ht hp=>encapsH1024_pub hs ht hp,encapsH1024_sat⟩

end VG.Proof.MlKem.AArch64.Hybrid
