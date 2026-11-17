module

import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Ecb
public import VerifiedGarbage.Proof.TripleDes.Scratch
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.TripleDes.Arm.Bitsliced
import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Ecb
meta import VerifiedGarbage.Proof.TripleDes.Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Impl.TripleDes.Arm.Bitsliced
meta import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint

/-!
# Bitsliced Triple DES ECB on ARMv7 meets its contract, with the working space as an argument

The proof is written against `ecbC`, which states the working space of 1024
bytes at `r3`, and moved to `Proof.TripleDes.ecbScratchContract`.

Constant time is the taint analysis's: the pointers and the count of blocks
are public, and the working space is a writable region whose public slots
keep the pointers and the counters public through memory.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Bitsliced

open VG VG.Arm VG.Impl.TripleDes.Arm.Bitslice
open VG.Spec.TripleDes (Direction)

/-- The ECB contract as the code sees it. -/
def ecbC (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
    let buf : Region := ⟨State.addr (s.gpr .r3), 1024⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧ (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
        (Spec.TripleDes.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem ecb_ok (d : Direction) (s : State) (hs : (ecbC d).pre s) :
    ∃ t s', Exec isa (ecb d) s t s' ∧ abiPreserved s s' ∧ (ecbC d).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, fD, fK, fB⟩ := hs
  obtain ⟨t, s', he, hp, hb⟩ := ecb_wp d ⟨rd, wr, kd, kb, db, fD, fK, fB⟩
  exact ⟨t, s', he, ⟨hp, Exec.sp he⟩, VG.Proof.TripleDes.Bitslice.ecb_blocks _ _ _ _ _ _ hb⟩

/-- The initial taint: the arguments, and the working space, the second
writable region, at `r3`. -/
def τE : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 1024], bases := [(.r3, 1)] }

theorem ecb_agree (d : Direction) {s₁ s₂ : State} (h₁ : (ecbC d).pre s₁) (h₂ : (ecbC d).pre s₂)
    (hp : (ecbC d).pub s₁ s₂) : VG.Arm.Taint.Agree τE s₁ s₂ := by
  have wf : ∀ s, (ecbC d).pre s → VG.Arm.Taint.Wf τE s := fun s ⟨_, wr, _, _, db, fD, _, fB⟩ => by
    refine ⟨fun _ => ⟨by simp [wr, τE], ?_, ?_⟩, ?_, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩
    · simp only [wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil]
      exact ⟨db, fun _ h => h.elim, trivial⟩
    · simp only [wr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only [State.addr, BitVec.toNat_setWidth] <;> omega_arith
    · intro p hp'
      simp only [τE, List.mem_singleton] at hp'; subst hp'
      simp [VG.Arm.Taint.region, wr]
  obtain ⟨psp, p0, p1, p2, p3⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf _ h₁, wf _ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [τE, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p2, p3]

theorem encrypt_ct : ConstantTime isa (ecbC .encrypt).pre (ecbC .encrypt).pub encrypt :=
  VG.Taint.constantTime (A := VG.Arm.taint) τE (fun _ _ h₁ h₂ hp => ecb_agree .encrypt h₁ h₂ hp)
    (by taint_decide)

theorem decrypt_ct : ConstantTime isa (ecbC .decrypt).pre (ecbC .decrypt).pub decrypt :=
  VG.Taint.constantTime (A := VG.Arm.taint) τE (fun _ _ h₁ h₂ hp => ecb_agree .decrypt h₁ h₂ hp)
    (by taint_decide)

/-- `ecb(0x1000, 0x2000, 0, 0x3000)`. -/
def ecbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem encrypt_verified :
    Verified target encrypt (Proof.TripleDes.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct (k := ecbC .encrypt) (ecb_ok .encrypt) encrypt_ct ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val,
    ecbC, State.addr] [ecbSat] using ecbSat

theorem decrypt_verified :
    Verified target decrypt (Proof.TripleDes.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct (k := ecbC .decrypt) (ecb_ok .decrypt) decrypt_ct ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val,
    ecbC, State.addr] [ecbSat] using ecbSat

end VG.Proof.TripleDes.Arm.Bitsliced
