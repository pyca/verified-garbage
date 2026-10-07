import VerifiedGarbage.Impl.Weierstrass.X86_64.FastNaf
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafSubtract
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafChoose

/-! Width-five and width-seven public digit selection on x86-64. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

def fastOdd (w : Nat) (x : BitVec 64) : BitVec 64 :=
  let y := x &&& BitVec.ofNat 64 (2^w-1)
  if y.toNat<2^(w-1) then y else y-BitVec.ofNat 64 (2^w)

theorem fastMask (x : BitVec 64) {w : Nat} (hw : FastNaf.Width w) :
    x &&& BitVec.ofNat 64 (2^w-1)=BitVec.ofNat 64 (x.toNat%2^w) := by
  have hm : 2^w-1<2^64 := by rcases hw with rfl|rfl <;> decide
  have hp : 0<2^w := Nat.two_pow_pos w
  have hb : 2^w≤2^64 := by rcases hw with rfl|rfl <;> decide
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hm]
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hb)]

theorem fastDigit_mod {w : Nat} (hw : FastNaf.Width w) (k j : Nat) :
    FastNaf.digit w k j =
      if FastNaf.residual w k j%2^w%2=0 then 0
      else if FastNaf.residual w k j%2^w<2^(w-1) then (FastNaf.residual w k j%2^w:Int)
      else (FastNaf.residual w k j%2^w:Int)-(2^w:Int) := by
  rcases hw with rfl|rfl
  · exact Naf5.digit_mod32 k j
  · exact FastNaf7.digit_mod128 k j

theorem fastOdd_eq {x : BitVec 64} {w k j : Nat} (hw : FastNaf.Width w)
    (hx : x.toNat%2^w=FastNaf.residual w k j%2^w)
    (ho : FastNaf.residual w k j%2≠0) : fastOdd w x=BitVec.ofInt 64 (FastNaf.digit w k j) := by
  rw [fastOdd,fastMask x hw,fastDigit_mod hw k j]
  rcases hw with rfl|rfl
  all_goals
    simp only [BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceSub] at hx ⊢
    have hp : x.toNat%2≠0 := by omega
    split <;> split <;> simp_all only []
    all_goals
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,BitVec.toNat_ofInt,BitVec.toNat_sub]
      omega

theorem fastChoose_ok (s : State) {w : Nat} (hw : FastNaf.Width w) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.choose w) s fun t =>
      t.gpr .rcx=fastOdd w (s.gpr .r8) ∧ Keeps [.rcx] s t := by
  have hm : (BitVec.ofNat 32 (2^w-1)).signExtend 64=BitVec.ofNat 64 (2^w-1) := by
    rcases hw with rfl|rfl <;> rfl
  have ht : (BitVec.ofNat 32 (2^(w-1))).signExtend 64=BitVec.ofNat 64 (2^(w-1)) := by
    rcases hw with rfl|rfl <;> rfl
  have hp : (BitVec.ofNat 32 (2^w)).signExtend 64=BitVec.ofNat 64 (2^w) := by
    rcases hw with rfl|rfl <;> rfl
  have hb : 2^(w-1)<2^64 := by rcases hw with rfl|rfl <;> decide
  rw [Impl.Weierstrass.X86_64.FastNaf.choose]
  refine WP.seq ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    hm,ht,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb,
    ite_true,Option.some.injEq,exists_eq_left']
  refine WP.ite (decide ((s.gpr .r8 &&& BitVec.ofNat 64 (2^w-1)).toNat<2^(w-1))) ?_ (fun h => ?_) (fun h => ?_)
  · rfl
  · apply WP.block_nil
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,ite_true,fastOdd,
        of_decide_eq_true h,ite_true]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
      Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hp,
      ite_true,Option.some.injEq,exists_eq_left']
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [fastOdd,of_decide_eq_false h,ite_false]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

end VG.Proof.Weierstrass.X86_64
