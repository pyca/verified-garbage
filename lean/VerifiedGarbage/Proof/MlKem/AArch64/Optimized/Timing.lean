module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecapsTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Depth
public import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps

/-! # Concrete ML-KEM-768 and ML-KEM-1024 timing certificates -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem

theorem keyGen768_ct :
    ConstantTime isa (entryContract (keyGenAArch64 lay768)).pre
      (entryContract (keyGenAArch64 lay768)).pub
      (Impl.MlKem.AArch64.Optimized.keyGenWith Sha3.AArch64.Sha3.callee lay768) :=
  keyGen_ct (keccak:=Sha3.AArch64.Sha3.backend) VG.Proof.MlKem.AArch64.KeyGen.wf768
    kgA768_depth Sha3.AArch64.Sha3.backend.mlkemKgATaint kgRest768_taint

theorem encaps768_ct :
    ConstantTime isa (entryContract (encapsAArch64 lay768)).pre
      (entryContract (encapsAArch64 lay768)).pub
      (Impl.MlKem.AArch64.Optimized.encapsWith Sha3.AArch64.Sha3.callee lay768) :=
  encaps_ct (keccak:=Sha3.AArch64.Sha3.backend) VG.Proof.MlKem.AArch64.KeyGen.wf768
    enA768_depth Sha3.AArch64.Sha3.backend.mlkemEnATaint enRest768_taint

theorem decaps768_ct :
    ConstantTime isa (entryContract (decapsAArch64 lay768)).pre
      (entryContract (decapsAArch64 lay768)).pub
      (Impl.MlKem.AArch64.Optimized.decapsWith Sha3.AArch64.Sha3.callee lay768) :=
  decaps_ct (keccak:=Sha3.AArch64.Sha3.backend) VG.Proof.MlKem.AArch64.KeyGen.wf768 VG.Proof.MlKem.AArch64.Encaps.calls768
    deStart768_depth deStart768_taint deRest768_taint

theorem keyGen1024_ct :
    ConstantTime isa (entryContract (keyGenAArch64 Impl.MlKem1024.AArch64.lay1024)).pre
      (entryContract (keyGenAArch64 Impl.MlKem1024.AArch64.lay1024)).pub
      (Impl.MlKem.AArch64.Optimized.keyGenWith Sha3.AArch64.Sha3.callee Impl.MlKem1024.AArch64.lay1024) :=
  keyGen_ct (keccak:=Sha3.AArch64.Sha3.backend) VG.Proof.MlKem1024.AArch64.KeyGen.wf1024
    kgA1024_depth Sha3.AArch64.Sha3.backend.mlkem1024KgATaint kgRest1024_taint

theorem encaps1024_ct :
    ConstantTime isa (entryContract (encapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pre
      (entryContract (encapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pub
      (Impl.MlKem.AArch64.Optimized.encapsWith Sha3.AArch64.Sha3.callee Impl.MlKem1024.AArch64.lay1024) :=
  encaps_ct (keccak:=Sha3.AArch64.Sha3.backend) VG.Proof.MlKem1024.AArch64.KeyGen.wf1024
    enA1024_depth Sha3.AArch64.Sha3.backend.mlkem1024EnATaint enRest1024_taint

theorem decaps1024_ct :
    ConstantTime isa (entryContract (decapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pre
      (entryContract (decapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pub
      (Impl.MlKem.AArch64.Optimized.decapsWith Sha3.AArch64.Sha3.callee Impl.MlKem1024.AArch64.lay1024) :=
  decaps_ct (keccak:=Sha3.AArch64.Sha3.backend) VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024
    deStart1024_depth deStart1024_taint deRest1024_taint

end VG.Proof.MlKem.AArch64.Optimized
