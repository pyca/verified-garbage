module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeGeometry
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTimingState
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-! The initializer ABI establishes its complete native input predicate. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

def precomputeNativeParameters (s : State) (g : PrecomputeGeometry s) : Parameters :=
 checkedParameters (s.gpr .x5) (s.gpr .x0) (s.gpr .x0) ((s.gpr .x6).toNat*8)
  (s.gpr .x4).toNat (precomputeDomain s) g.room g.small g.large g.checked

def precomputeInputPublic (s : State) (g : PrecomputeGeometry s) : PrecomputePublic :=
 ⟨precomputeNativeParameters s g,s.gpr .x2,precomputeDomain s,(s.gpr .x3).toNat,s.syms Policy.tableSym,
  rfl,g.small,g.large,g.shape,by simp only [precomputeDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range],
  g.checked,rfl,rfl,rfl⟩

theorem precompute_input_ready {s : State} (g : PrecomputeGeometry s) :
 PrecomputeReady (precomputeInputPublic s g) s :=by
 have space : ContextSpace (precomputeNativeParameters s g) s :=by
  constructor
  · intro i hi
    apply g.context.st
    change 8*i+8≤(s.gpr .x1).toNat*8
    change i<3+34*(((s.gpr .x4).toNat+7)/8) at hi
    rw [g.count];omega
  · intro i hi
    apply g.contextOutside
    change i<8*(3+34*(((s.gpr .x4).toNat+7)/8)) at hi
    rw [g.count];omega
 have output : Scr s (s.gpr .x0) 24 :=by
  have h:=g.context.sub (o:=0) (n:=24) (by rw [g.count];omega) (by decide)
  simpa only [off,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
 have source : PublicSource (precomputeNativeParameters s g) (s.gpr .x2) (precomputeDomain s) s :=by
  refine ⟨src_source g.source,g.source.out,?_⟩
  intro i hi
  change 8*(3+34*(((s.gpr .x4).toNat+7)/8))≤_
  change 8*(3+34*(((s.gpr .x4).toNat+7)/8))≤ofs (s.gpr .x0) (s.gpr .x2+BitVec.ofNat 64 i)
  rw [←g.count];simpa only [Nat.mul_comm] using g.domainOutside i hi
 exact ⟨g.scratch,space,output,source,g.span,rfl,rfl,(ofNat_toNat64 _).symm,(ofNat_toNat64 _).symm,rfl,
  policyConsts_table g.constants g.scratch (by have :=g.room;dsimp only [slot,hdrBytes] at this;omega),rfl⟩

end VG.Proof.Ffdh.AArch64.Cached
