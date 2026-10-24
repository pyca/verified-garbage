module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptGeometry
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.NativeTimingState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-! Every reviewed ABI input establishes the native attempt's complete geometry and public policy. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

def attemptNativeParameters (s : State) (g : AttemptGeometry s) : Parameters :=
 checkedParameters (stackArg s 1) (s.gpr .x0) (stackArg s 3) ((stackArg s 2).toNat*8)
  (s.gpr .x6).toNat (attemptDomain s) g.room g.small g.large g.checked

def attemptFront (s : State) (g : AttemptGeometry s) : FrontPublic :=by
 let p:=attemptNativeParameters s g
 have positive : 0<p.k :=by change 0<(s.gpr .x6).toNat;have :=g.small;omega
 have odd : p.P%2=1 :=by
  have mod:=VG.Proof.Ffdh.domainValid_mod g.checked
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at mod
  exact mod.1.1.1
 have bitsPositive : 0<p.N :=generation_bits_positive g.checked
 have bitsBound : p.N≤8192 :=generation_bits_bound positive g.large
 have width : p.N≤8*p.k :=Nat.le_trans (VG.Proof.Ffdh.VettedPolicy.bits_le_bound _) (scalarBound_bits_fit positive)
 have valid : Spec.Ffdh.parametersValid (attemptParameters s)=true :=by
  have h:=g.checked
  unfold Spec.Ffdh.domainValid at h
  simp only [Bool.and_eq_true] at h
  exact h.1
 exact ⟨⟨⟨p,s.gpr .x4,(s.gpr .x5).toNat,attemptDomain s,rfl,positive,
   by change (s.gpr .x6).toNat<2^31;have :=g.large;omega,g.shape,
   by simp only [attemptDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range],rfl,odd⟩,
  s.gpr .x2,Spec.Ffdh.keyStatus (attemptParameters s) (attemptScalar s),bitsPositive,bitsBound,width,rfl,valid,g.outsideX⟩,
  s.gpr .x7,(stackArg s 4).toNat,g.checked,rfl,rfl,g.separateRand,g.separateDomain,g.separateContext⟩

theorem attempt_native_state {s : State} (g : AttemptGeometry s) : NativeState (attemptFront s g) (attemptRandom s) s :=by
 refine ⟨g.scratch,g.view,g.domain,g.random,?_,rfl,rfl,rfl,?_,?_,rfl,?_,?_,g.stackB,g.stackCtx,g.writeX,rfl⟩
 · change (attemptRandom s).length=(s.gpr .x6).toNat
   simp only [attemptRandom,Spec.Rsa.bytesAt,List.length_map,List.length_range]
   exact g.randLength
 · exact (ofNat_toNat64 _).symm
 · exact (ofNat_toNat64 _).symm
 · rfl
 · rfl

end VG.Proof.Ffdh.AArch64.Cached
