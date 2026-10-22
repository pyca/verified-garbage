module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialNextPair
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialPrimeMachine
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialLoopScalar
public import VerifiedGarbage.Proof.RsaKeyGen.Table32

/-! The loop invariant for the shared packed table of trial primes. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

structure TrialPlan where
  base : Addr
  bytes : Nat
  candidate : Nat
  width : Nat
  table : Nat
  count : Nat
  candidateFits : candidate + 8 * width ≤ bytes
  widthSmall : 8 * width < 2 ^ 32
  widthPositive : 0 < width
  tableFits : table + 4 * count ≤ bytes
  countPositive : 0 < count
  countBound : count ≤ 512

namespace TrialPlan

def start (P : TrialPlan) : BitVec 32 := BitVec.ofNat 32 (P.base.toNat + P.candidate)
def tableStart (P : TrialPlan) : BitVec 32 := BitVec.ofNat 32 (P.base.toNat + P.table)
def number (P : TrialPlan) (s : State) : Nat := val32 s.mem P.base P.candidate (2 * P.width)

end TrialPlan

structure TrialLoopState (P : TrialPlan) (initial : State) (sp : BitVec 32) (k : Nat)
    (values : Nat → BitVec 32) (s : State) : Prop where
  machine : TrialMachine initial P.base P.bytes sp values s
  start : values 0 = P.start
  last : values 1 = P.start + BitVec.ofNat 32 (8 * P.width)
  table : values 2 = P.tableStart + BitVec.ofNat 32 (4 * k)
  count : values 3 = BitVec.ofNat 32 (P.count - k)
  flag : values 5 = BitVec.ofNat 32 (tr (2 * k) (P.number initial)).toNat

def TrialLoopInv (P : TrialPlan) (initial : State) (sp : BitVec 32) (k : Nat) (s : State) : Prop :=
  ∃ values, TrialLoopState P initial sp k values s

theorem trial_bit_or (a b : Bool) : BitVec.ofNat 32 a.toNat ||| BitVec.ofNat 32 b.toNat =
    BitVec.ofNat 32 (a || b).toNat := by cases a <;> cases b <;> rfl

theorem trial_low_pair {i : Nat} (hi : i < 512) :
    BitVec.ofNat 32 (tabWord32 i) &&& 65535 = BitVec.ofNat 32 (tabEntry (2 * i)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (65535 : BitVec 32).toNat = 2 ^ 16 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (tabWord32_lt hi), tabWord32_lo hi, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := tabEntry_facts (i := 2 * i) (by omega); omega)]

theorem trial_high_pair {i : Nat} (hi : i < 512) :
    BitVec.ofNat 32 (tabWord32 i) >>> 16 = BitVec.ofNat 32 (tabEntry (2 * i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (tabWord32_lt hi), tabWord32_hi hi, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := tabEntry_facts (i := 2 * i + 1) (by omega); omega)]

end VG.Proof.Dsa.X86.Generation
