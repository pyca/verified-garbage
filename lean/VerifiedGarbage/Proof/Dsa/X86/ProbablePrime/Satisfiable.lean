module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABI
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.RsaKeyGen.KeyCheck
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # A state meets the precondition: an all-ones candidate and an empty tape -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Impl.Dsa.X86.ProbablePrime

def satArgument : Nat → BitVec 32
  | 0 => 0x10000
  | 1 => 2000
  | 2 => 0x5000
  | 3 => 0
  | _ => 0x2000

/-- The arguments at the stack pointer plus 4. -/
def satArguments : Mem := fun a =>
  (satArgument ((a - 0x20004#64).toNat / 4)).extractLsb' (8 * ((a - 0x20004#64).toNat % 4)) 8

def satBase (bits : Nat) : Addr := 0x10000#64 + BitVec.ofNat 64 (scratchBytes (width bits))

def satMemory (bits : Nat) : Mem := fun a =>
  if (a - 0x20004#64).toNat < 20 then satArguments a
  else if (a - satBase bits).toNat < bits / 8 then 0xFF#8
  else constMem 0x30000#64 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState (bits : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory bits
  rd := [⟨0x5000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x10000, 16000⟩, ⟨0x2000, 8⟩, ⟨0x20004, 20⟩]
  syms _ := 0x30000

theorem scratch_bound {bits : Nat} (b : Bits bits) : scratchBytes (width bits) + bits / 8 ≤ 16000 := by
  have := b.width_high
  have := b.high
  unfold scratchBytes VG.Impl.Bignum.X86.PublicContext.slot VG.Impl.Bignum.X86.PublicContext.stride
    VG.Impl.Bignum.hdrBytes
  omega

theorem sat_argument_word (i : Nat) (index : i < 5) :
    satArguments.readW (BitVec.ofNat 64 (0x20004 + 4 * i)) 32 = satArgument i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem sat_arguments (bits : Nat) (i : Nat) (index : i < 5) : arg (satState bits) i = satArgument i := by
  have address : argAddr (satState bits) i = BitVec.ofNat 64 (0x20004 + 4 * i) := by
    change ((0x20000#32 + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) = _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold arg
  rw [address, ← sat_argument_word i index]
  apply Mem.readW_congr
  intro j hj
  change (if _ then _ else _) = _
  refine ite_eq_left ?_
  change ((BitVec.ofNat 64 (0x20004 + 4 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 20
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem satBase_toNat {bits : Nat} (b : Bits bits) :
    (satBase bits).toNat = 0x10000 + scratchBytes (width bits) := by
  have := scratch_bound b
  unfold satBase
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem os2ip_ones : ∀ (n acc : Nat),
    (List.replicate n (0xFF#8)).foldl (fun x b => 256 * x + b.toNat) acc = acc * 256 ^ n + (256 ^ n - 1)
  | 0, acc => by simp
  | n + 1, acc => by
    rw [List.replicate_succ, List.foldl_cons, os2ip_ones n, Nat.pow_succ]
    have ff : (0xFF#8).toNat = 255 := rfl
    rw [ff]
    have pos : 0 < 256 ^ n := Nat.pow_pos (by decide)
    generalize 256 ^ n = p at *
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    grind

theorem sat_candidate {bits : Nat} (b : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) ((satArgument 0).setWidth 64) =
      2 ^ bits - 1 := by
  have bound := scratch_bound b
  have baseNat := satBase_toNat b
  have bytes : Spec.Rsa.bytesAt (satMemory bits) ((satArgument 0).setWidth 64 +
      BitVec.ofNat 64 (layout bits).candidate) ((layout bits).bits / 8) = List.replicate (bits / 8) 0xFF#8 := by
    change Spec.Rsa.bytesAt (satMemory bits) (satBase bits) (bits / 8) = _
    unfold Spec.Rsa.bytesAt
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.length_map, List.length_range] at hi
    unfold satMemory
    rw [ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, baseNat]; omega),
      ite_eq_left (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, baseNat]; omega)]
  unfold Proof.Dsa.ProbablePrime.candidateAt
  rw [bytes, VG.Proof.Dsa.decodeBE_os2ip]
  unfold Spec.Rsa.os2ip
  rw [os2ip_ones, Nat.zero_mul, Nat.zero_add]
  have whole := b.whole
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, show 8 * (bits / 8) = bits by omega]

theorem sat_odd {bits : Nat} (b : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) ((satArgument 0).setWidth 64) % 2 = 1 := by
  rw [sat_candidate b]
  have : 2 ^ bits % 2 = 0 := by
    rw [show bits = (bits - 1) + 1 by have := b.low; omega, Nat.pow_succ]; omega
  have := Nat.two_pow_pos bits
  omega

theorem sat_length {bits : Nat} (b : Bits bits) :
    Spec.Dsa.bitLength
      (Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) ((satArgument 0).setWidth 64)) = bits := by
  rw [sat_candidate b]
  have low := b.low
  have half : 2 ^ bits = 2 ^ (bits - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have pos := Nat.two_pow_pos (bits - 1)
  have := VG.Proof.RsaKeyGen.bitLength_of (n := 2 ^ bits - 1) (b := bits - 1) (by omega)
    (by rw [show bits - 1 + 1 = bits by omega]; omega)
  rw [show bits - 1 + 1 = bits by omega] at this
  exact this

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, packed_length]

theorem sat_table {bits : Nat} (b : Bits bits) :
    Abi.constsHeld (satState bits).mem (fun name => ((satState bits).syms name).setWidth 64)
      VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have bound := scratch_bound b
  have baseNat := satBase_toNat b
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by rw [packed_length]; decide
  have small : i < 1024 := by simpa only [packed_length] using index
  change (satMemory bits).readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 =
    VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  have held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i index
  refine Eq.trans (Mem.readW_congr (m := satMemory bits)
    (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_) held
  intro j hj
  change (if _ then _ else _) = _
  rw [ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega),
    ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, baseNat]; omega)]
  rfl

theorem sat_argAddr (bits : Nat) : argAddr (satState bits) 0 = 0x20004#64 := by
  change ((0x20000#32 + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64) = _
  decide

theorem satisfiable {bits : Nat} (b : Bits bits) : ∃ s, (contract bits).pre s := by
  refine ⟨satState bits, ?_⟩
  sig_pre [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments bits 0 (by decide), sat_arguments bits 1 (by decide), sat_arguments bits 2 (by decide),
    sat_arguments bits 3 (by decide), sat_arguments bits 4 (by decide), sat_argAddr]
  simp only [packed_regions, List.forall_mem_singleton]
  sig_and_intros
  all_goals first
    | exact sat_table b
    | exact sat_odd b
    | exact sat_length b
    | (have := scratch_bound b; change _ ≤ 8 * 2000; omega)
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)

end VG.Proof.Dsa.X86.ProbablePrime
