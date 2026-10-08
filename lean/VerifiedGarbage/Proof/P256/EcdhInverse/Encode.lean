import Mathlib.Tactic.NormNum
import VerifiedGarbage.Proof.P256.EcdhInverse.Rounds

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem encode_row (x : BitVec 64) {k : Nat} (hk : k=41 ∨ k=62) :
    (x &&& 0xfffff) ||| BitVec.ofInt 64 (-(2^k)) =
      BitVec.ofInt 64 ((x.toNat%2^20 : Nat)- (2^k : Int)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or,BitVec.toNat_and]
  have ha : x.toNat%1048576<1048576 := Nat.mod_lt _ (by decide)
  have hp : x.toNat &&& (0xfffff : BitVec 64).toNat=x.toNat%1048576 := by
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 20
  rw [hp]
  rcases hk with rfl|rfl
  all_goals
    norm_num only [BitVec.toNat_ofInt]
    rw [Nat.or_comm]
  · have ho := Nat.shiftLeft_add_eq_or_of_lt (by exact ha : x.toNat%1048576<2^20) 17592183947264
    norm_num only [Nat.shiftLeft_eq] at ho
    rw [show Int.toNat 18446741874686296064=18446741874686296064 by decide,←ho]
    omega
  · have ho := Nat.shiftLeft_add_eq_or_of_lt (by exact ha : x.toNat%1048576<2^20) 13194139533312
    norm_num only [Nat.shiftLeft_eq] at ho
    rw [show Int.toNat 13835058055282163712=13835058055282163712 by decide,←ho]
    omega


def encodeCode : List Instr :=
  [.movz .x .x28 65535 0,
   .movk .x .x28 15 1,
   .logic .and .x .x4 .x2 .x28,
   .movz .x .x28 0 0,
   .movk .x .x28 65024 2,
   .movk .x .x28 65535 3,
   .logic .orr .x .x4 .x4 .x28,
   .movz .x .x28 65535 0,
   .movk .x .x28 15 1,
   .logic .and .x .x5 .x3 .x28,
   .movz .x .x28 0 0,
   .movk .x .x28 49152 3,
   .logic .orr .x .x5 .x5 .x28]

theorem encodeCode_ok (s : State) :
    WP isa (.block encodeCode) s fun t =>
      t.gpr .x4=BitVec.ofInt 64 (((s.gpr .x2).toNat%2^20 : Nat)-(2^41 : Int)) ∧
      t.gpr .x5=BitVec.ofInt 64 (((s.gpr .x3).toNat%2^20 : Nat)-(2^62 : Int)) ∧
      Keeps [.x4,.x5,.x28] s t := by
  apply WP.of_runBlock
  simp only [encodeCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',show (16*0:Nat)<Size.x.bits by decide,
    show (16*1:Nat)<Size.x.bits by decide,show (16*2:Nat)<Size.x.bits by decide,
    show (16*3:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · change ((s.gpr .x2 &&& 0xfffff) ||| BitVec.ofInt 64 (-(2^41)))=_
    exact encode_row _ (Or.inl rfl)
  · change ((s.gpr .x3 &&& 0xfffff) ||| BitVec.ofInt 64 (-(2^62)))=_
    exact encode_row _ (Or.inr rfl)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h4,h5,h28⟩ := hr
    simp only [RegUpd.gpr_write,h4,h5,h28,↓reduceIte]

end VG.Proof.P256.EcdhInverse
