import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedField
import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.P256.VerifyArithmetic Spec.Weierstrass

theorem field_relCT (raw : RawCorrect) {k : Kind} (cert : Proof.P256.VerifyAllocated.Case k)
    {base : Addr} {V Out : List Nat} {E : Nat → Fe C}
    (hslots : ∀ op∈operations k,∀ x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true)
    (hout : ∀ x∈Out,x∈validAfter (operations k) V)
    (hobs : ∀ x∈Out,∀ i<4,Proof.P256.VerifyAllocated.observe k (x+8*i))
    (hct : FieldCT (VG.Impl.P256.VerifyAllocated.program k)) :
    RelCT isa (FieldPair K.M base 8192 C.p Sl V E) (VG.Impl.P256.VerifyAllocated.program k)
      (FieldPair K.M base 8192 C.p Sl Out (runOps (operations k) E)) :=
  fieldWP_relCT hct fun _ hi => WP.mono (field_ok raw cert hi hslots hreads hout hobs)
    fun _ ⟨hk,it⟩ => ⟨it,hk.regs.sp⟩

theorem field_all_relCT (raw : RawCorrect) {k : Kind} (cert : Proof.P256.VerifyAllocated.Case k)
    (hk : k≠.doubleRR) {base : Addr} {V : List Nat} {E : Nat → Fe C}
    (hslots : ∀ op∈operations k,∀ x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true)
    (hct : FieldCT (VG.Impl.P256.VerifyAllocated.program k)) :
    RelCT isa (FieldPair K.M base 8192 C.p Sl V E) (VG.Impl.P256.VerifyAllocated.program k)
      (FieldPair K.M base 8192 C.p Sl (validAfter (operations k) V) (runOps (operations k) E)) :=
  fieldWP_relCT hct fun _ hi => WP.mono (field_all_ok raw cert hk hi hslots hreads)
    fun _ ⟨hk,it⟩ => ⟨it,hk.regs.sp⟩

end VG.Proof.Ecdsa.Verify.AArch64.Allocated
