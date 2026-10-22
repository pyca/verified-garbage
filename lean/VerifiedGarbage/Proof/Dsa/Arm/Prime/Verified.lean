module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top1
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top2
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top3
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top6
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top7
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Dsa.ProbablePrime
meta import VerifiedGarbage.TCB.Arm.Target

/-! # `vg_dsa_probable_prime_{bits}` on ARMv7 is verified against the shared contract

For the widths of DSA's primes (`Bits`) and any implementation of the
Miller–Rabin round it calls (`RoundImpl`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (code layout keyOff keyWords)
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {bits : Nat}

theorem prime_contract_correct (v : RoundImpl) (hb : Bits bits) (enc : PreEnc bits) (s : State)
    (h : (Spec.Dsa.ProbablePrime.contract (layout bits) abi 144).pre s) :
    ∃ tr t, Exec isa (code bits v.name v.code) s tr t ∧ abiPreserved s t ∧
      (Spec.Dsa.ProbablePrime.contract (layout bits) abi 144).post s t := by
  have hc := cin_of_pre bits s h
  obtain ⟨tr, t, run, preserved, r0, keeps, used⟩ := prime_ok v hb enc hc
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨r0, keeps, used⟩

/-- Calls with the same public arguments and leak have the same public parameters. -/
theorem mkP_eq {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (p3 : s.gpr .r3 = t.gpr .r3) (a0 : stackArg s 0 = stackArg t 0)
    (hc : Spec.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)) =
      Spec.Dsa.ProbablePrime.candidateAt (layout bits) t.mem (State.addr (t.gpr .r0)))
    (hr : Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (t.gpr .r2)) (t.gpr .r3).toNat) :
    mkP bits s = mkP bits t := by
  unfold mkP; rw [hc, hr, sp, p0, p2, p3, a0]

theorem prime_contract_ct (v : RoundImpl) (hb : Bits bits) (enc : PreEnc bits) :
    ConstantTime isa (Spec.Dsa.ProbablePrime.contract (layout bits) abi 144).pre
      (Spec.Dsa.ProbablePrime.contract (layout bits) abi 144).pub (code bits v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := cin_of_pre bits s hs
  have it := cin_of_pre bits t ht
  sig_pub [Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, leak, p0, -, p2, p3, a0⟩ := hp
  obtain ⟨hc, hl⟩ := List.cons.inj leak
  have hr := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
  exact (prime_ct v hb enc s t tr1 tr2 u w ⟨is, it, sp, mkP_eq sp p0 p2 p3 a0 hc hr⟩ e1 e2).1

theorem decodeBE_ff (n acc : Nat) :
    (List.replicate n (0xFF : Byte)).foldl (fun x b => 256 * x + b.toNat) acc = (acc + 1) * 256 ^ n - 1 := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    have : (0xFF : Byte).toNat = 255 := rfl
    rw [this, show 256 * acc + 255 + 1 = (acc + 1) * 256 by omega, Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm 256]

/-- A state satisfying the contract: the candidate of `bits` ones at `0x1000`, in a working space of
6224 words, no `rand`, `used` at 0, and the stack at `0x80000`. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 6224 | .r2 => 0x20000 | .r3 => 0 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a.toNat < 0x10000 ∧ 0x1000 ≤ a.toNat then 0xFF else 0
  rd := [⟨0x20000, 0⟩, ⟨0x80000, 4⟩]
  wr := [⟨0x1000, 49792⟩, ⟨0, 8⟩]

theorem sat_bytes {n : Nat} (hn : n ≤ 384) :
    Spec.Rsa.bytesAt satState.mem (0x1000 + BitVec.ofNat 64 0) n = List.replicate n 0xFF := by
  refine List.eq_replicate_iff.mpr ⟨by simp [Spec.Rsa.bytesAt], fun b hb => ?_⟩
  simp only [Spec.Rsa.bytesAt, List.mem_map, List.mem_range] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  have : (0x1000 + BitVec.ofNat 64 0 + BitVec.ofNat 64 i : Addr).toNat = 0x1000 + i := by
    rw [BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat, show (0x1000 : Addr).toNat = 4096 from rfl]; omega
  simp only [satState, this]
  rw [ite_eq_left (show 0x1000 + i < 0x10000 ∧ 0x1000 ≤ 0x1000 + i by omega)]

theorem sat_cand (hb : Bits bits) :
    Spec.Dsa.ProbablePrime.candidateAt (layout bits) satState.mem 0x1000 = 2 ^ bits - 1 := by
  have h8 : bits = 8 * (bits / 8) := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hl : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  show Spec.Dsa.decodeBE (Spec.Rsa.bytesAt satState.mem (0x1000 + BitVec.ofNat 64 0) (bits / 8)) = _
  rw [sat_bytes hl, Spec.Dsa.decodeBE, decodeBE_ff, Nat.zero_add, Nat.one_mul,
    show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, ← h8]

theorem prime_contract_sat (hb : Bits bits) : ∃ s, (Spec.Dsa.ProbablePrime.contract (layout bits) abi 144).pre s := by
  refine ⟨satState, ?_⟩
  have hc := sat_cand hb
  have hpos : 0 < bits := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hsz : keyOff + 8 * keyWords bits ≤ 8 * 6224 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  sig_pre [Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig, abi, argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide)
    | decide
    | skip
  · exact hsz
  · obtain ⟨k, rfl⟩ : ∃ k, bits = k + 1 := ⟨bits - 1, by omega⟩
    show Spec.Dsa.ProbablePrime.candidateAt (layout (k + 1)) satState.mem 4096 % 2 = 1
    rw [hc, Nat.pow_succ]
    have := Nat.one_le_two_pow (n := k)
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, bits = k + 1 := ⟨bits - 1, by omega⟩
    show Spec.Dsa.bitLength (Spec.Dsa.ProbablePrime.candidateAt (layout (k + 1)) satState.mem 4096) = k + 1
    rw [hc, VG.Proof.Dsa.bitLength_iff_bounds hpos, Nat.add_sub_cancel, Nat.pow_succ]
    have := Nat.one_le_two_pow (n := k)
    omega

theorem prime_verified (v : RoundImpl) (bits : Nat) (hb : Bits bits := by decide)
    (enc : PreEnc bits := by decide) :
    Verified target (code bits v.name v.code) (Spec.Dsa.ProbablePrime.contract (layout bits) abi 144) :=
  ⟨prime_contract_correct v hb enc, prime_contract_ct v hb enc, prime_contract_sat hb⟩

end

end VG.Proof.Dsa.Arm.Prime
