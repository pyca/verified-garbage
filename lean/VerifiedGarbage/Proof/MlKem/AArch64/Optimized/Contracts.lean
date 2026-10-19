module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
public import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
meta import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64

theorem keyGen768_base : (keyGenAArch64 lay768).Implies (Spec.MlKem.keyGenContract abi 16) := by
  mlkem_implies [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenAArch64, lay768, KemLay.params, Spec.MlKem.mlKem768,
      KemLay.ekLen, KemLay.dkLen, AArch64.abi, AArch64.argRegs] [VG.Proof.MlKem.AArch64.KeyGen.sat] using VG.Proof.MlKem.AArch64.KeyGen.sat

def keyGen768Contract := Spec.MlKem.keyGenContract (abi.withConsts constants) 16

theorem keyGen768_entry {s : State} (h : keyGen768Contract.pre s) :
 (entryContract (keyGenAArch64 lay768)).pre s := by
 unfold keyGen768Contract Spec.MlKem.keyGenContract constants at h
 have hp := (pre_consts.mp h)
 exact ⟨keyGen768_base.pre _ hp.1,hp.2⟩

theorem decaps768_base : (decapsAArch64 lay768).Implies (Spec.MlKem.decapsContract abi 16) := by
  mlkem_implies [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsAArch64, lay768, KemLay.params,
      Spec.MlKem.mlKem768, KemLay.dkLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs] [VG.Proof.MlKem.AArch64.Decaps.sat] using VG.Proof.MlKem.AArch64.Decaps.sat

def decaps768Contract := Spec.MlKem.decapsContract (abi.withConsts constants) 16

theorem decaps768_entry {s : State} (h : decaps768Contract.pre s) :
 (entryContract (decapsAArch64 lay768)).pre s := by
 unfold decaps768Contract Spec.MlKem.decapsContract constants at h
 have hp := (pre_consts.mp h)
 exact ⟨decaps768_base.pre _ hp.1,hp.2⟩

theorem keyGen1024_base : (keyGenAArch64 VG.Impl.MlKem1024.AArch64.lay1024).Implies (Spec.MlKem1024.keyGenContract abi 16) := by
  mlkem_implies [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenAArch64, VG.Impl.MlKem1024.AArch64.lay1024,
      KemLay.params, Spec.MlKem.mlKem1024, KemLay.ekLen, KemLay.dkLen, AArch64.abi, AArch64.argRegs] [VG.Proof.MlKem1024.AArch64.KeyGen.sat]
      using VG.Proof.MlKem1024.AArch64.KeyGen.sat

def keyGen1024Contract := Spec.MlKem1024.keyGenContract (abi.withConsts constants) 16

theorem keyGen1024_entry {s : State} (h : keyGen1024Contract.pre s) :
 (entryContract (keyGenAArch64 VG.Impl.MlKem1024.AArch64.lay1024)).pre s := by
 unfold keyGen1024Contract Spec.MlKem1024.keyGenContract constants at h
 have hp := (pre_consts.mp h)
 exact ⟨keyGen1024_base.pre _ hp.1,hp.2⟩

theorem decaps1024_base : (decapsAArch64 VG.Impl.MlKem1024.AArch64.lay1024).Implies (Spec.MlKem1024.decapsContract abi 16) := by
  mlkem_implies [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsAArch64, VG.Impl.MlKem1024.AArch64.lay1024,
      KemLay.params, Spec.MlKem.mlKem1024, KemLay.dkLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs] [VG.Proof.MlKem1024.AArch64.Decaps.sat]
      using VG.Proof.MlKem1024.AArch64.Decaps.sat

def decaps1024Contract := Spec.MlKem1024.decapsContract (abi.withConsts constants) 16

theorem decaps1024_entry {s : State} (h : decaps1024Contract.pre s) :
 (entryContract (decapsAArch64 VG.Impl.MlKem1024.AArch64.lay1024)).pre s := by
 unfold decaps1024Contract Spec.MlKem1024.decapsContract constants at h
 have hp := (pre_consts.mp h)
 exact ⟨decaps1024_base.pre _ hp.1,hp.2⟩

theorem keyGen768_post {s t : State} (h : keyGen768Contract.pre s)
 (hp : (keyGenAArch64 lay768).post s t) : keyGen768Contract.post s t := by
 unfold keyGen768Contract Spec.MlKem.keyGenContract constants at h ⊢
 have hh := pre_consts.mp h
 exact keyGen768_base.post (stripConsts constants s) t hh.1 hp

theorem keyGen768_pub {s t : State} (hs : keyGen768Contract.pre s) (ht : keyGen768Contract.pre t)
 (hp : keyGen768Contract.pub s t) : (entryContract (keyGenAArch64 lay768)).pub s t := by
 unfold keyGen768Contract Spec.MlKem.keyGenContract constants at hs ht hp
 have hsp := pre_consts.mp hs
 have htp := pre_consts.mp ht
 have hpp := pub_consts.mp hp
 exact ⟨keyGen768_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1,hpp.2⟩

theorem decaps768_post {s t : State} (h : decaps768Contract.pre s)
 (hp : (decapsAArch64 lay768).post s t) : decaps768Contract.post s t := by
 unfold decaps768Contract Spec.MlKem.decapsContract constants at h ⊢
 have hh := pre_consts.mp h
 exact decaps768_base.post (stripConsts constants s) t hh.1 hp

theorem decaps768_pub {s t : State} (hs : decaps768Contract.pre s) (ht : decaps768Contract.pre t)
 (hp : decaps768Contract.pub s t) : (entryContract (decapsAArch64 lay768)).pub s t := by
 unfold decaps768Contract Spec.MlKem.decapsContract constants at hs ht hp
 have hsp := pre_consts.mp hs
 have htp := pre_consts.mp ht
 have hpp := pub_consts.mp hp
 exact ⟨decaps768_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1,hpp.2⟩

theorem keyGen1024_post {s t : State} (h : keyGen1024Contract.pre s)
 (hp : (keyGenAArch64 VG.Impl.MlKem1024.AArch64.lay1024).post s t) : keyGen1024Contract.post s t := by
 unfold keyGen1024Contract Spec.MlKem1024.keyGenContract constants at h ⊢
 have hh := pre_consts.mp h
 exact keyGen1024_base.post (stripConsts constants s) t hh.1 hp

theorem keyGen1024_pub {s t : State} (hs : keyGen1024Contract.pre s) (ht : keyGen1024Contract.pre t)
 (hp : keyGen1024Contract.pub s t) : (entryContract (keyGenAArch64 VG.Impl.MlKem1024.AArch64.lay1024)).pub s t := by
 unfold keyGen1024Contract Spec.MlKem1024.keyGenContract constants at hs ht hp
 have hsp := pre_consts.mp hs
 have htp := pre_consts.mp ht
 have hpp := pub_consts.mp hp
 exact ⟨keyGen1024_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1,hpp.2⟩

theorem decaps1024_post {s t : State} (h : decaps1024Contract.pre s)
 (hp : (decapsAArch64 VG.Impl.MlKem1024.AArch64.lay1024).post s t) : decaps1024Contract.post s t := by
 unfold decaps1024Contract Spec.MlKem1024.decapsContract constants at h ⊢
 have hh := pre_consts.mp h
 exact decaps1024_base.post (stripConsts constants s) t hh.1 hp

theorem decaps1024_pub {s t : State} (hs : decaps1024Contract.pre s) (ht : decaps1024Contract.pre t)
 (hp : decaps1024Contract.pub s t) : (entryContract (decapsAArch64 VG.Impl.MlKem1024.AArch64.lay1024)).pub s t := by
 unfold decaps1024Contract Spec.MlKem1024.decapsContract constants at hs ht hp
 have hsp := pre_consts.mp hs
 have htp := pre_consts.mp ht
 have hpp := pub_consts.mp hp
 exact ⟨decaps1024_base.pub (stripConsts constants s) (stripConsts constants t) hsp.1 htp.1 hpp.1,hpp.2⟩
end VG.Proof.MlKem.AArch64.Optimized
