module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! A public domain byte comparison, preserving an exact mismatch accumulator. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem read1_eq (m : Mem) (p : Addr) : m.read p 1=m p := by
 change (0#0 ++ m p : BitVec (0+8))=m p
 exact BitVec.zero_width_append _ _
private theorem byte_zext (b : Byte) : (b.setWidth 32).setWidth 64=BitVec.ofNat 64 b.toNat := by
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 have := b.isLt
 omega

theorem byte_cast_eq (b c : Byte) : BitVec.ofNat 64 b.toNat=BitVec.ofNat 64 c.toNat ↔ b=c := by
 constructor
 · intro eq
   have := congrArg BitVec.toNat eq
   have := b.isLt
   have := c.isLt
   apply BitVec.eq_of_toNat_eq
   simp only [BitVec.toNat_ofNat] at *
   omega
 · rintro rfl;rfl

theorem policyCompareStep {s : State} {src dst : Addr} {bs cs : List Byte} {i : Nat}
 (first : Source src bs s) (second : Source dst cs s) (inside : i<bs.length) (insideC : i<cs.length)
 (ptr1 : s.gpr .x1=off src i) (ptr2 : s.gpr .x2=off dst i) :
 WP isa (.block Policy.compareBody) s fun t =>
 (t.gpr .x1=off src (i+1) ∧ t.gpr .x2=off dst (i+1) ∧
 t.gpr .x11=s.gpr .x11 ||| (BitVec.ofNat 64 (bs.getD i 0).toNat ^^^ BitVec.ofNat 64 (cs.getD i 0).toNat) ∧
 t.mem=s.mem) ∧ Keep [.x1,.x2,.x8,.x9,.x11] s t := by
 refine WP.keep [.x1,.x2,.x8,.x9,.x11] ?_ rfl rfl rfl
 unfold Policy.compareBody
 brun [ptr1,ptr2,first.readable i inside,second.readable i insideC,
  first.bytes i inside,second.bytes i insideC,read1_eq,byte_zext]

end VG.Proof.Ffdh.AArch64.Cached
