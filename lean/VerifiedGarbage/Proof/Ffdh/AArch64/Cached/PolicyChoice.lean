module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecordEnv
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyCompareArgs
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
/-! A cap is applied only after the complete vetted-domain match. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyMatch.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

def choiceClobbers : List Reg := [.x1,.x2,.x5,.x7,.x8,.x9,.x10,.x11]

theorem policyChoice_ok {s : State} {B src rec : Addr} {Z k N : Nat} {dom : List Byte} {g : Policy.Group}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (source : Source src dom s) (record : PolicyRecordAt B rec g s)
 (shape : dom.length=2*k ∨ dom.length=3*k) (positive : 0<k) (size : k<2^28)
 (domain : word s.mem B (8*sDom)=src) (length : word s.mem B (8*sDL)=BitVec.ofNat 64 dom.length)
 (width : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (fit : N<2^64)
 (pointer : s.gpr .x4=off rec 8) (cap : s.gpr .x6=BitVec.ofNat 64 g.bits)
 (test : s.gpr .x3=BitVec.ofNat 64 k-BitVec.ofNat 64 g.len) :
 WP isa Policy.recordChoice s fun t =>
 (t.mem=if k=g.len ∧ dom=g.domain.take dom.length then
  s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N g.bits)) else s.mem) ∧
 (t.gpr .x7=if k=g.len ∧ dom=g.domain.take dom.length then 1#64 else s.gpr .x7) ∧
 Keep choiceClobbers s t := by
 unfold Policy.recordChoice
 refine WP.ite (decide (k=g.len)) ?_ ?_ ?_
 · rw [eval_zero,test]
   change some (BitVec.ofNat 64 k-BitVec.ofNat 64 g.len == 0#64)=_
   rw [sub_zero_iff (by omega) (by have := record.lenFit;omega)]
 · intro yes
   have same := of_decide_eq_true yes
   have limit : dom.length≤g.domain.length := by rw [policyDomain_length];omega
   rw [WP.seq_iff]
   refine WP.mono (policyCompare_ok scratch room base domain length pointer source
    (record.source.take dom.length) (by simp only [List.length_take];omega) (by omega) (by omega)) ?_
   rintro u ⟨equal,memU,restU⟩
   have choose : isa.eval (.zero .x .x11) u=some (decide (dom=g.domain.take dom.length)) := by
    rw [eval_zero]
    change some (u.gpr .x11 == 0#64)=_
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq,decide_eq_true_eq] using equal
   refine WP.ite (decide (dom=g.domain.take dom.length)) choose ?_ ?_
   · intro yesDomain
     have sameDomain := of_decide_eq_true yesDomain
     have matched : k=g.len ∧ dom=g.domain.take dom.length := ⟨same,sameDomain⟩
     refine WP.mono (policyMatch_ok (scratch.congr restU.wr) room
      ((restU.gpr .x0 (by simp [compareClobbers])).trans base) (memU ▸ width) fit
      ((restU.gpr .x6 (by simp [compareClobbers])).trans cap) (by have := record.bitsFit;omega)) ?_
     rintro t ⟨⟨memT,countT⟩,restT⟩
     refine ⟨?_,?_,(restU.trans restT).mono (by simp [compareClobbers,choiceClobbers])⟩
     · simpa only [ite_eq_left matched,memU] using memT
     · simpa only [ite_eq_left matched] using countT
   · intro noDomain
     have different := of_decide_eq_false noDomain
     refine WP.block_nil ⟨?_,?_,restU.mono (by simp [compareClobbers,choiceClobbers])⟩
     · simpa only [same,different,and_false,ite_false] using memU
     · simpa only [same,different,and_false,ite_false] using restU.gpr .x7 (by simp [compareClobbers])
 · intro no
   have different := of_decide_eq_false no
   refine WP.block_nil ⟨?_,?_,(Keep.refl [] s).mono (by simp)⟩
   · simp only [different,false_and,ite_false]
   · simp only [different,false_and,ite_false]

end VG.Proof.Ffdh.AArch64.Cached
