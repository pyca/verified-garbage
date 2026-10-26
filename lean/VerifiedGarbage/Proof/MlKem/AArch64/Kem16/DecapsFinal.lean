module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Contracts
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.DecapsStart

import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Final
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsChecks
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
meta import VerifiedGarbage.Proof.Sha3.AArch64.Callers.Sums
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Decaps
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Contracts
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Decaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.TCB.Axioms
public import Aesop.BuiltinRules
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Consts
public import VerifiedGarbage.Proof.Sha3.AArch64.Callers.Sums
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.TCB.AArch64.Target

/-! # The hashing decapsulation's contract and checks

For ML-KEM-768 and ML-KEM-1024, hashing `z ‖ c` in the matrix's third state:
the taint analyses of the first phase (`startJ768_taint`) and of the blocks of
`z ‖ c` (`habsJ768`), and the contract with the 128 bytes of stack of the x3
calls, as `Hybrid/Final.lean` (`decapsH768Contract`), for
`Kem16P/DecapsFinal.lean`. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash hole prfW prfW_valid deG768_correct deG1024_correct symSums
  deStart768_depth deStart1024_depth)
open VG.Proof.MlKem

/-! ## The checks -/

theorem startJ768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (.seq (FixedHashDecaps.deStartUsing (fixedHash c) lay768) (.block (Kem16.startJ lay768))) h).isSome=true := by
  taint_decide_generic c := hole using hS

theorem startJ1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (.seq (FixedHashDecaps.deStartUsing (fixedHash c) Impl.MlKem1024.AArch64.lay1024)
        (.block (Kem16.startJ Impl.MlKem1024.AArch64.lay1024))) h).isSome=true := by
  taint_decide_generic c := hole using hS

theorem habsJ768 : ∀ blk, 136 * blk < (Kem16.jSrc lay768).len → ∃ h,
    (taint.check (Taint.ofRegs [(Kem16.jSrc lay768).r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock (Kem16.jSrc lay768) blk)) h).isSome = true :=
  habs_of _ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩

theorem habsJ1024 : ∀ blk, 136 * blk < (Kem16.jSrc Impl.MlKem1024.AArch64.lay1024).len → ∃ h,
    (taint.check (Taint.ofRegs [(Kem16.jSrc Impl.MlKem1024.AArch64.lay1024).r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock (Kem16.jSrc Impl.MlKem1024.AArch64.lay1024) blk)) h).isSome =
        true :=
  habs_of _ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩

theorem srcOkJ768 : SrcOk (Kem16.jSrc lay768) := ⟨.inr (.inr rfl), by decide, by decide, by decide⟩
theorem srcOkJ1024 : SrcOk (Kem16.jSrc Impl.MlKem1024.AArch64.lay1024) := ⟨.inr (.inr rfl), by decide, by decide, by decide⟩
theorem hashOkJ768 : HashOk lay768 (Kem16.jSrc lay768) := ⟨by decide, by decide, by decide⟩
theorem hashOkJ1024 : HashOk Impl.MlKem1024.AArch64.lay1024 (Kem16.jSrc Impl.MlKem1024.AArch64.lay1024) :=
  ⟨by decide, by decide, by decide⟩

/-! ## ML-KEM-768 -/

theorem decapsS768_base : (decapsAArch64S lay768).Implies (Spec.MlKem.decapsContract abi 128) := by
  mlkem_implies [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsAArch64S, decapsAArch64, lay768,
      KemLay.params, Spec.MlKem.mlKem768, KemLay.dkLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs]
      [VG.Proof.MlKem.AArch64.Decaps.sat] using VG.Proof.MlKem.AArch64.Decaps.sat

def decapsH768Contract := Spec.MlKem.decapsContract (abi.withConsts constants) 128

theorem decapsH768_entry {s : State} (h : decapsH768Contract.pre s) :
    (entryContractS (decapsAArch64S lay768)).pre s := by
  unfold decapsH768Contract Spec.MlKem.decapsContract constants at h
  have hp := (pre_consts.mp h)
  exact ⟨decapsS768_base.pre _ hp.1,hp.2⟩

theorem decapsH768_post {s t : State} (h : decapsH768Contract.pre s)
    (hp : (decapsAArch64S lay768).post s t) : decapsH768Contract.post s t := by
  unfold decapsH768Contract Spec.MlKem.decapsContract constants at h ⊢
  have hh := pre_consts.mp h
  exact decapsS768_base.post (stripConsts constants s) t hh.1 hp

theorem decapsH768_pub {s t : State} (hs : decapsH768Contract.pre s) (ht : decapsH768Contract.pre t)
    (hp : decapsH768Contract.pub s t) : (entryContractS (decapsAArch64S lay768)).pub s t := by
  unfold decapsH768Contract Spec.MlKem.decapsContract constants at hs ht hp
  have hsp := pre_consts.mp hs
  have htp := pre_consts.mp ht
  have hpp := pub_consts.mp hp
  exact ⟨decapsS768_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1,hpp.2⟩

theorem decapsH768_sat : ∃s,decapsH768Contract.pre s := by
  refine ⟨addTables VG.Proof.MlKem.AArch64.Decaps.sat,?_⟩
  unfold decapsH768Contract Spec.MlKem.decapsContract constants
  apply pre_consts.mpr
  constructor
  · change (Spec.MlKem.decapsContract abi 128).pre (stripConsts constants (addTables VG.Proof.MlKem.AArch64.Decaps.sat))
    rw [strip_addTables]
    sig_pre [Spec.MlKem.decapsSig,abi,argRegs]
    and_intros
    all_goals first
     | rfl
     | decide
     | exact Region.disjoint_of_sep (by decide)
  · change ConstsOk constants 128 (addTables VG.Proof.MlKem.AArch64.Decaps.sat)
    refine ⟨?_,tableMem_held,?_⟩
    · rfl
    · intro r hr
      rw [constants_regions] at hr
      rcases hr with _|⟨_,_|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩⟩
      all_goals first
       | contradiction
       | (refine ⟨by decide,?_,?_⟩
          · intro q hq
            change q∈VG.Proof.MlKem.AArch64.Decaps.sat.wr at hq
            simp only [VG.Proof.MlKem.AArch64.Decaps.sat,List.mem_cons,List.not_mem_nil,or_false] at hq
            rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
          · intro q hq
            change q∈[below (0x100000:Addr) 128] at hq
            rw [List.mem_singleton.mp hq]
            exact Region.disjoint_of_sep (by decide))

/-! ## ML-KEM-1024 -/

theorem decapsS1024_base :
    (decapsAArch64S Impl.MlKem1024.AArch64.lay1024).Implies (Spec.MlKem1024.decapsContract abi 128) := by
  mlkem_implies [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsAArch64S, decapsAArch64,
      Impl.MlKem1024.AArch64.lay1024, KemLay.params, Spec.MlKem.mlKem1024, KemLay.dkLen, KemLay.ctLen,
      AArch64.abi, AArch64.argRegs] [VG.Proof.MlKem1024.AArch64.Decaps.sat]
      using VG.Proof.MlKem1024.AArch64.Decaps.sat

def decapsH1024Contract := Spec.MlKem1024.decapsContract (abi.withConsts constants) 128

theorem decapsH1024_entry {s : State} (h : decapsH1024Contract.pre s) :
    (entryContractS (decapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pre s := by
  unfold decapsH1024Contract Spec.MlKem1024.decapsContract constants at h
  have hp := (pre_consts.mp h)
  exact ⟨decapsS1024_base.pre _ hp.1,hp.2⟩

theorem decapsH1024_post {s t : State} (h : decapsH1024Contract.pre s)
    (hp : (decapsAArch64S Impl.MlKem1024.AArch64.lay1024).post s t) : decapsH1024Contract.post s t := by
  unfold decapsH1024Contract Spec.MlKem1024.decapsContract constants at h ⊢
  have hh := pre_consts.mp h
  exact decapsS1024_base.post (stripConsts constants s) t hh.1 hp

theorem decapsH1024_pub {s t : State} (hs : decapsH1024Contract.pre s) (ht : decapsH1024Contract.pre t)
    (hp : decapsH1024Contract.pub s t) :
    (entryContractS (decapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pub s t := by
  unfold decapsH1024Contract Spec.MlKem1024.decapsContract constants at hs ht hp
  have hsp := pre_consts.mp hs
  have htp := pre_consts.mp ht
  have hpp := pub_consts.mp hp
  exact ⟨decapsS1024_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1,hpp.2⟩

theorem decapsH1024_sat : ∃s,decapsH1024Contract.pre s := by
  refine ⟨addTables VG.Proof.MlKem1024.AArch64.Decaps.sat,?_⟩
  unfold decapsH1024Contract Spec.MlKem1024.decapsContract constants
  apply pre_consts.mpr
  constructor
  · change (Spec.MlKem1024.decapsContract abi 128).pre
      (stripConsts constants (addTables VG.Proof.MlKem1024.AArch64.Decaps.sat))
    rw [strip_addTables]
    sig_pre [Spec.MlKem1024.decapsSig,abi,argRegs]
    and_intros
    all_goals first
     | rfl
     | decide
     | exact Region.disjoint_of_sep (by decide)
  · change ConstsOk constants 128 (addTables VG.Proof.MlKem1024.AArch64.Decaps.sat)
    refine ⟨?_,tableMem_held,?_⟩
    · rfl
    · intro r hr
      rw [constants_regions] at hr
      rcases hr with _|⟨_,_|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩⟩
      all_goals first
       | contradiction
       | (refine ⟨by decide,?_,?_⟩
          · intro q hq
            change q∈VG.Proof.MlKem1024.AArch64.Decaps.sat.wr at hq
            simp only [VG.Proof.MlKem1024.AArch64.Decaps.sat,List.mem_cons,List.not_mem_nil,or_false] at hq
            rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
          · intro q hq
            change q∈[below (0x100000:Addr) 128] at hq
            rw [List.mem_singleton.mp hq]
            exact Region.disjoint_of_sep (by decide))

end VG.Proof.MlKem.AArch64.Hybrid
