module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Exact matches cap the width by the reviewed policy, never increase it. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem publicCarry {a b : Nat} (fitA : a<2^64) (fitB : b<2^64) :
 decide (2^64≤(BitVec.ofNat 64 a).toNat+(~~~BitVec.ofNat 64 b).toNat+1)=decide (b≤a) := by
 simp only [BitVec.toNat_not,BitVec.toNat_ofNat]
 rw [Nat.mod_eq_of_lt fitA,Nat.mod_eq_of_lt fitB]
 apply decide_eq_decide.mpr
 omega

theorem policyMatch_ok {s : State} {B : Addr} {Z N cap : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (width : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (fit : N<2^64)
 (limit : s.gpr .x6=BitVec.ofNat 64 cap) (capFit : cap<2^64) :
 WP isa (.block Policy.matched) s fun t =>
 (t.mem=s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N cap)) ∧ t.gpr .x7=1#64) ∧
 Keep [.x7,.x9,.x10] s t := by
 have choose : (if decide (cap≤N) then BitVec.ofNat 64 cap else BitVec.ofNat 64 N)=BitVec.ofNat 64 (min N cap) := by
  by_cases h : cap≤N
  · simp only [decide_eq_true h,ite_true,Nat.min_eq_right h]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,Nat.min_eq_left (show N≤cap by omega)]
 refine WP.keep [.x7,.x9,.x10] ?_ rfl rfl rfl
 unfold Policy.matched
 brun [base,hdr_enc (show sBits<32 by decide),scratch.ld (d:=8*sBits) (by unfold sBits;omega),
  scratch.st (d:=8*sBits) (by unfold sBits;omega),width,limit,Bool.toNat_true,publicCarry fit capFit,choose]

end VG.Proof.Ffdh.AArch64.Cached
