module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Contracts

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Decaps
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsChecks
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsPrefix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Contracts
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Decaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsPrefix
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.TCB.Axioms

/-! # The 16-bit `vg_mlkem768_decaps` and `vg_mlkem1024_decaps`

As `FixedHash/DecapsVerified.lean`, for `Kem16.decaps`: the decryption and
`G` before the matrix as there, the matrix sampled with 16 bits, and the
16-bit re-encryption, with the taint analysis of the rest decided on each
parameter set (`decapsW768_verified`, `decapsW1024_verified`). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Optimized
variable {P : KemLay}

theorem decaps_using_prefixW (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6
      [⟨.x28,KEM.MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) {s : State}
    (hp : Pre P (Decaps.deL P) s) (calls : Calls P) (tables : Tables s)
    (depth : (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P).aarch64Depth≤1) :
    WP isa (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P) s
      (fun t=>BInvW true P (Decaps.deL P) s t.mem (Decaps.rhoD P s) 0 t ∧ MatrixTable P (Decaps.deL P) s t) :=
  WP.mono (decaps_using_prefix hash hG hp calls tables depth) fun _ ⟨hb,ht⟩ =>
    ⟨BInvW.zero hb.kb (by rw [hb.acc]; rfl) hb.rho,ht⟩

theorem kemMatrixW768_depth : (Paired.matrix lay768 false true).aarch64Depth≤1 := by decide
theorem kemMatrixW1024_depth : (Paired.matrix Impl.MlKem1024.AArch64.lay1024 false true).aarch64Depth≤1 := by
  decide

theorem deRestW768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.deRest (fixedHash c) (prfW c) lay768) h).isSome=true := by
  taint_decide_generic c := hole using hS

theorem deRestW1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.deRest (fixedHash c) (prfW c) Impl.MlKem1024.AArch64.lay1024) h).isSome=true := by
  taint_decide_generic c := hole using hS

theorem decapsW768_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContract (decapsAArch64 lay768)).pre (entryContract (decapsAArch64 lay768)).pub
      (Kem16.decaps (fixedHash v.callee) (prfW v.callee) lay768) :=
  decaps_using_ct VG.Proof.MlKem.AArch64.KeyGen.wf768
    (fun hp tables=>decaps_using_prefixW (fixedHash v.callee) (deG768_correct v) hp
      VG.Proof.MlKem.AArch64.Encaps.calls768 tables (deStart768_depth v))
    (deStart768_taint v.callee (symSums v)) (deRestW768_taint v.callee (symSums v))

theorem decapsW768_verified (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target
    (Kem16.decaps (fixedHash v.callee) (prfW v.callee) lay768) decaps768Contract := by
  refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (decapsAArch64 lay768)) ?_ (decapsW768_ct v) ?_
  · intro s h
    exact Decaps.using_correctW (fixedHash v.callee) (prfW_valid v) (deG768_correct v) (deJ768_correct v)
      (kem_unstrip (Decaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 h.1)) Noise.room768
      VG.Proof.MlKem.AArch64.Encaps.calls768 (entry_tables h) (deStart768_depth v) kemMatrixW768_depth
  · exact ⟨fun _ h=>decaps768_entry h,fun _ _ h hp=>decaps768_post h hp,
      fun _ _ hs ht hp=>decaps768_pub hs ht hp,decaps768_sat⟩

theorem decapsW1024_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContract (decapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pre
      (entryContract (decapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pub
      (Kem16.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024) :=
  decaps_using_ct VG.Proof.MlKem1024.AArch64.KeyGen.wf1024
    (fun hp tables=>decaps_using_prefixW (fixedHash v.callee) (deG1024_correct v) hp
      VG.Proof.MlKem1024.AArch64.Encaps.calls1024 tables (deStart1024_depth v))
    (deStart1024_taint v.callee (symSums v)) (deRestW1024_taint v.callee (symSums v))

theorem decapsW1024_verified (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target
    (Kem16.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024) decaps1024Contract := by
  refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (decapsAArch64 Impl.MlKem1024.AArch64.lay1024))
    ?_ (decapsW1024_ct v) ?_
  · intro s h
    exact Decaps.using_correctW (fixedHash v.callee) (prfW_valid v) (deG1024_correct v) (deJ1024_correct v)
      (kem_unstrip (Decaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 h.1)) Noise.room1024
      VG.Proof.MlKem1024.AArch64.Encaps.calls1024 (entry_tables h) (deStart1024_depth v) kemMatrixW1024_depth
  · exact ⟨fun _ h=>decaps1024_entry h,fun _ _ h hp=>decaps1024_post h hp,
      fun _ _ hs ht hp=>decaps1024_pub hs ht hp,decaps1024_sat⟩

end VG.Proof.MlKem.AArch64.FixedHash
