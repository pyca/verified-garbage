module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Verified
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig

/-!
# DSA's probable-prime test on PPC64LE: a state meets the precondition

An all-ones candidate of `bits` bits at the start of a working space of
2000 words, an empty tape, and the table at `0x30000`. `verified`: with
`correct` and `constantTime`, the test is verified.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- The witness's memory. -/
def satMemory (bits : Nat) : Mem := fun a =>
  if (a - 0x10000#64).toNat < bits / 8 then 0xFF#8
  else constMem 0x30000#64 VG.Impl.RsaKeyGen.TrialTable32.packed a

/-- The witness. -/
def satState (bits : Nat) : State where
  gpr r := if r = .r3 then 0x10000 else if r = .r4 then 2000 else if r = .r5 then 0x5000 else
    if r = .r7 then 0x2000 else 0
  lr := 0
  sp := 0x20000
  mem := satMemory bits
  rd := [⟨0x5000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x10000, 16000⟩, ⟨0x2000, 8⟩]
  unknowns _ := 0
  syms _ := 0x30000

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

theorem sat_candidate {bits : Nat} (hb : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) 0x10000#64 = 2 ^ bits - 1 := by
  have hs := shape_of hb
  have hl := hs.hlen8
  have h384 : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have bytes : Spec.Rsa.bytesAt (satMemory bits) (0x10000#64 + BitVec.ofNat 64 (layout bits).candidate)
      ((layout bits).bits / 8) = List.replicate (bits / 8) 0xFF#8 := by
    change Spec.Rsa.bytesAt (satMemory bits) (0x10000#64 + BitVec.ofNat 64 0) (bits / 8) = _
    unfold Spec.Rsa.bytesAt
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.length_map, List.length_range] at hi
    unfold satMemory
    rw [ite_eq_left (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  unfold Proof.Dsa.ProbablePrime.candidateAt
  rw [bytes, VG.Proof.Dsa.decodeBE_os2ip]
  unfold Spec.Rsa.os2ip
  rw [os2ip_ones, Nat.zero_mul, Nat.zero_add]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, show 8 * (bits / 8) = bits by rw [← hs.hlen]; omega]

theorem sat_odd {bits : Nat} (hb : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) 0x10000#64 % 2 = 1 := by
  rw [sat_candidate hb]
  have : 2 ^ bits % 2 = 0 := by
    rw [show bits = (bits - 1) + 1 by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide, Nat.pow_succ]; omega
  have := Nat.two_pow_pos bits
  omega

theorem sat_length {bits : Nat} (hb : Bits bits) :
    Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) 0x10000#64) = bits := by
  rw [sat_candidate hb]
  have low : 1 ≤ bits := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have half : 2 ^ bits = 2 ^ (bits - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have pos := Nat.two_pow_pos (bits - 1)
  exact (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mpr ⟨by omega, by omega⟩

theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

theorem sat_table {bits : Nat} (hb : Bits bits) :
    Abi.constsHeld (satMemory bits) (fun _ => 0x30000#64) VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; decide
  have small : i < 1024 := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at index; exact index
  have h384 : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  refine Eq.trans (Mem.readW_congr (m := satMemory bits)
    (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_)
    (constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i index)
  intro j hj
  change (if _ then _ else _) = _
  rw [ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  rfl

theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.TrialTable32.packed_length]

theorem satisfiable {bits : Nat} (hb : Bits bits) : ∃ s, (contract bits).pre s := by
  have hs := shape_of hb
  have hkw : keyOff + 8 * keyWords bits ≤ 16000 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨satState bits, ?_⟩
  unfold contract Proof.Dsa.ProbablePrime.contract
  refine pre_consts.mpr ⟨?_, ?_⟩
  · sig_pre [Proof.Dsa.ProbablePrime.sig, abi, argRegs, stripConsts]
    sig_and_intros
    all_goals first
      | exact sat_odd hb
      | exact sat_length hb
      | (show _ ≤ 8 * 2000; omega)
      | decide
      | exact Region.disjoint_of_sep (by decide +kernel)
  · refine ⟨?_, sat_table hb, ?_, ?_⟩
    · simp only [constRegs, packed_regions]; rfl
    · simp only [constRegs, packed_regions]
      simp only [List.forall_mem_singleton, satState, abi, List.forall_mem_cons, stackBelow]
      exact ⟨by decide, ⟨Region.disjoint_of_sep (by decide +kernel), Region.disjoint_of_sep (by decide +kernel)⟩,
        Region.disjoint_of_sep (by decide +kernel)⟩
    · simp only [constRegs, packed_regions, List.forall_mem_singleton, satState]
      decide

/-- `vg_dsa_probable_prime_{bits}`, calling the round `Ri`, is verified. -/
theorem verified (Ri : RoundImpl) (bits : Nat) (hb : Bits bits := by decide) :
    Verified target (code bits Ri.name Ri.code) (contract bits) :=
  ⟨correct Ri hb, constantTime Ri hb, satisfiable hb⟩

end VG.Proof.Dsa.PPC64LE.Prime
