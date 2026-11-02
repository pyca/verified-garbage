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
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # `vg_dsa_probable_prime` on ARMv7 is verified against the shared contract

For every size of `sizes` (`Bits`), the second stack argument, and any
implementation of the Miller–Rabin round it calls (`RoundImpl`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (code layout keyOff keyWords)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem prime_contract_correct (v : RoundImpl) (s : State) (h : primeK.pre s) :
    ∃ tr t, Exec isa (code v.name v.code) s tr t ∧ abiPreserved s t ∧ primeK.post s t := by
  have hc := cin_of_pre s h
  obtain ⟨tr, t, run, preserved, r0, keeps, used⟩ := prime_ok v hc
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨r0, keeps, used⟩

section
variable {bits : Nat}

/-- Calls with the same public arguments and leak have the same public parameters. -/
theorem mkP_eq {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (p3 : s.gpr .r3 = t.gpr .r3) (a0 : stackArg s 0 = stackArg t 0)
    (hc : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)) =
      Proof.Dsa.ProbablePrime.candidateAt (layout bits) t.mem (State.addr (t.gpr .r0)))
    (hr : Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (t.gpr .r2)) (t.gpr .r3).toNat) :
    mkP bits s = mkP bits t := by
  unfold mkP; rw [hc, hr, sp, p0, p2, p3, a0]

end

theorem prime_contract_ct (v : RoundImpl) : ConstantTime isa primeK.pre primeK.pub (code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := cin_of_pre s hs
  have it := cin_of_pre t ht
  sig_pub [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at hp
  obtain ⟨sp, leak, p0, -, p2, p3, a0, a1⟩ := hp
  rw [← a1] at leak
  obtain ⟨-, leak⟩ := List.cons.inj leak
  obtain ⟨hc, hl⟩ := List.cons.inj leak
  have hr := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
  rw [← a1] at it
  exact (prime_ct v s t tr1 tr2 u w ⟨is, it, sp, mkP_eq sp p0 p2 p3 a0 hc hr⟩ e1 e2).1

/-- A state satisfying the contract: the candidate of 160 ones at `0x1000`, in a working space of
6224 words, no `rand`, `used` at 0, and the stack at `0x80000`, its second word the size 160. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 6224 | .r2 => 0x20000 | .r3 => 0 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a.toNat < 0x10000 ∧ 0x1000 ≤ a.toNat then 0xFF else if a = 0x80004 then 160 else 0
  rd := [⟨0x20000, 0⟩, ⟨0x80000, 8⟩]
  wr := [⟨0x1000, 49792⟩, ⟨0, 8⟩]

theorem prime_contract_sat : ∃ s, primeK.pre s := by
  refine ⟨satState, ?_⟩
  have ha : stackArg satState 1 = 160 := by decide
  sig_pre [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val]
  rw [ha]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide)
    | decide

theorem prime_verified (v : RoundImpl) : Verified target (code v.name v.code) primeK :=
  ⟨prime_contract_correct v, prime_contract_ct v, prime_contract_sat⟩

end VG.Proof.Dsa.Arm.Prime
