module

public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Params
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # A state meets the probable-prime test's precondition

An all-ones candidate of `bits` bits at its offset of a working space of 5120
words, and an empty tape. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Impl.Dsa.AArch64.ProbablePrime

def satBase : Addr := 0x100000

def satMemory (bits : Nat) : Mem := fun a =>
  if (a - (satBase + BitVec.ofNat 64 (candidate bits))).toNat < bits / 8 then 0xFF#8 else 0

def satState (bits : Nat) : State where
  gpr r := match r with
    | .x0 => 0x100000 | .x1 => 5120 | .x2 => 0x200000 | .x3 => 0
    | .x4 => 0x300000 | _ => 0
  sp := 0x400000
  mem := satMemory bits
  rd := [⟨0x200000, 0⟩]
  wr := [⟨0x100000, 40960⟩, ⟨0x300000, 8⟩]

theorem foldl_ones : ∀ (n acc : Nat),
    (List.replicate n (0xFF#8)).foldl (fun x b => 256 * x + b.toNat) acc = acc * 256 ^ n + (256 ^ n - 1)
  | 0, acc => by simp
  | n + 1, acc => by
    rw [List.replicate_succ, List.foldl_cons, foldl_ones n, Nat.pow_succ]
    have ff : (0xFF#8).toNat = 255 := rfl
    rw [ff]
    have pos : 0 < 256 ^ n := Nat.pow_pos (by decide)
    generalize 256 ^ n = p at *
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    grind

theorem sat_candidate {bits : Nat} (hb : Supported bits) :
    candidateOf bits (satState bits) = 2 ^ bits - 1 := by
  have hl : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have bytes : Spec.Rsa.bytesAt (satMemory bits) (satBase + BitVec.ofNat 64 (candidate bits)) (bits / 8) =
      List.replicate (bits / 8) 0xFF#8 := by
    unfold Spec.Rsa.bytesAt
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.length_map, List.length_range] at hi
    unfold satMemory
    rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ite_eq_left hi
  change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt (satMemory bits) (satBase + BitVec.ofNat 64 (candidate bits))
    (bits / 8)) = _
  rw [bytes, VG.Proof.Dsa.decodeBE_os2ip]
  unfold Spec.Rsa.os2ip
  rw [foldl_ones, Nat.zero_mul, Nat.zero_add]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, show 8 * (bits / 8) = bits by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide]

theorem sat_odd {bits : Nat} (hb : Supported bits) : candidateOf bits (satState bits) % 2 = 1 := by
  rw [sat_candidate hb]
  have : 2 ^ bits % 2 = 0 := by
    rw [show bits = (bits - 1) + 1 by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide, Nat.pow_succ]; omega
  have := Nat.two_pow_pos bits
  omega

theorem sat_length {bits : Nat} (hb : Supported bits) :
    Spec.Dsa.bitLength (candidateOf bits (satState bits)) = bits := by
  rw [sat_candidate hb]
  have low : 1 ≤ bits := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have half : 2 ^ bits = 2 ^ (bits - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have pos := Nat.two_pow_pos (bits - 1)
  exact (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mpr ⟨by omega, by omega⟩

theorem satisfiable {bits : Nat} (hb : Supported bits) : ∃ s, (contract bits).pre s := by
  refine ⟨satState bits, ?_⟩
  sig_pre [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact sat_odd hb
    | exact sat_length hb
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel

end VG.Proof.Dsa.AArch64.ProbablePrime
