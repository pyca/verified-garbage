import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.Naf5
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

def nafRaw (x : BitVec 64) : BitVec 64 :=
  if x &&& 1=0 then 0 else (x &&& 31)-(((x &&& 31) &&& 16) <<< 1)

theorem nafMask (x : BitVec 64) : x &&& 31=BitVec.ofNat 64 (x.toNat%32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change x.toNat &&& (2^5-1) = (x.toNat%32)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem nafRaw_eq {x : BitVec 64} {k j : Nat}
    (hx : x.toNat%32=Naf5.residual k j%32) : nafRaw x=BitVec.ofInt 64 (Naf5.digit k j) := by
  have H : ∀ r : Fin 32,
      (if r.val%2=0 then (0 : BitVec 64) else BitVec.ofNat 64 r.val-
        ((BitVec.ofNat 64 r.val &&& 16) <<< 1)) =
      BitVec.ofInt 64 (if r.val%2=0 then 0 else if r.val<16 then (r.val:Int) else (r.val:Int)-32) := by decide
  have he : x &&& 1=0 ↔ x.toNat%2=0 := by
    rw [←BitVec.toNat_inj]
    change x.toNat &&& 1=0 ↔ x.toNat%2=0
    rw [Nat.and_one_is_mod]
  simp only [nafRaw,he,nafMask,hx,Naf5.digit_mod32]
  have hp : x.toNat%2=Naf5.residual k j%32%2 := by omega
  rw [hp]
  change (if Naf5.residual k j%32%2=0 then (0:BitVec 64) else
    (x &&& (31:BitVec 64))-(BitVec.ofNat 64 (Naf5.residual k j%32) &&& 16) <<< 1)=_
  rw [nafMask,hx]
  exact H ⟨Naf5.residual k j%32,Nat.mod_lt _ (by decide)⟩

theorem nafChoose_ok (s : State) (h10 : s.gpr .x10=31) (h11 : s.gpr .x11=16)
    (h13 : s.gpr .x13=1) :
    WP isa Naf.chooseDigit s fun t => t.gpr .x2=nafRaw (s.gpr .x5) ∧ Keeps [.x1,.x2,.x3] s t := by
  rw [Naf.chooseDigit]
  refine WP.seq ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    h13,Option.some.injEq,exists_eq_left']
  by_cases h : s.gpr .x5 &&& 1=0
  · refine WP.ite false ?_ (by intro h; cases h) (fun _ => ?_)
    · simp only [eval,read_x,RegUpd.gpr_write,ite_true,BitVec.setWidth_eq,Size.bits]
      simpa only [Option.some.injEq,bne_eq_false_iff_eq] using h
    refine WP.mono (movz0_ok _ .x2) fun t ⟨ht,kt⟩ => ?_
    refine ⟨by rw [ht,nafRaw,ite_eq_left h],?_,kt.mem,kt.rd,kt.wr,kt.sp⟩
    intro r hr
    have hr' : r≠.x1 ∧ r≠.x2 ∧ r≠.x3 := by simpa using hr
    rw [kt.gpr r (by simpa using hr'.2.1)]
    simp only [RegUpd.gpr_write,hr'.1,ite_false]
  · refine WP.ite true ?_ (fun _ => ?_) (by intro h; cases h)
    · simp only [eval,read_x,RegUpd.gpr_write,ite_true,BitVec.setWidth_eq,Size.bits]
      simpa only [Option.some.injEq,bne_iff_ne] using h
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
      BitVec.setWidth_eq,Option.some.injEq,exists_eq_left',nafRaw,h,ite_false,
      reduceCtorEq,ite_true,h10,h11,show 1<Size.x.bits from by decide]
    refine ⟨rfl,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

end VG.Proof.Weierstrass.AArch64
