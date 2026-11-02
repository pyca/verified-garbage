module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MillerRabin.RISCV64.CT
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Core

/-!
# The Miller–Rabin round on RISC-V: verified against the shared contract

`fnContract` states the shared contract's postcondition on the registers
(`fnPost`, `round_implies`); with correctness (`fn_correct`, given the core's
`CoreOk`) and constant time (`round_ct`), `round` is verified for the
`frameBytes` bytes of stack its frame uses (`round_verified_of`), and with
`Core.lean`'s `core_ok`, unconditionally (`round_verified`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64

open VG VG.RISCV64 VG.Impl.MillerRabin.RISCV64
open VG.Proof.Rsa.Mont (numAt wOf)
open VG.Proof.MillerRabin.Round (compact Layout Prepared roundContract)

/-- The shared contract, its postcondition on the registers. -/
def fnContract : Contract isa where
  pre := (roundContract RISCV64.abi compact frameBytes).pre
  post := fnPost
  pub := (roundContract RISCV64.abi compact frameBytes).pub

/-- A four-limb prepared working space for the candidate 3 at `0x1000`, as on
ARMv7 and PPC64LE. -/
def satWord (i : Nat) : BitVec 64 :=
  if i = 6 then 4 else if i = 7 then 0x5555555555555555 else
    if 8 ≤ i ∧ i < 16 then BitVec.ofNat 64 (0x1100 + 48 * (i - 8)) else
    if i = 28 then 48 else if i = 32 then 3 else if i = 62 then 2 else
    if i = 86 then 1 else if i = 92 then 2 else if i = 194 then 1 else if i = 198 then 2 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 2048 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

theorem sat_layout : Layout compact satMem 0x1000 256 := by
  simp only [Layout, compact, Proof.Rsa.Mont.Layout, Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff,
    forall_const, true_and]
  decide +kernel

theorem sat_prepared : Prepared compact satMem 0x1000 := by
  have hw : wOf satMem 0x1000 = 4 := by decide +kernel
  have hc : numAt satMem 0x1000 4 0 = 3 := by decide +kernel
  have h5 : numAt satMem 0x1000 4 5 = 2 := by decide +kernel
  have h9 : numAt satMem 0x1000 4 9 = 1 := by decide +kernel
  have h10 : numAt satMem 0x1000 4 10 = 2 := by decide +kernel
  have h27 : numAt satMem 0x1000 4 27 = 1 := by decide +kernel
  simp only [Prepared, compact, hw, hc, h5, h9, h10, h27]
  decide +kernel

/-- A state meeting the precondition: the working space at `0x1000`, the
stack at `0x8000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 256 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 2048⟩]

theorem round_implies : fnContract.Implies (roundContract RISCV64.abi compact frameBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, fnPost]
  pub := fun _ _ _ _ h => h
  sat := by
    refine ⟨satState, ?_⟩
    have e : frameBytes = 95 + 1 := rfl
    rw [e]
    sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, RISCV64.abi,
      RISCV64.argRegs]
    exact ⟨by decide, by decide, rfl, Region.disjoint_of_sep (by decide), by decide, sat_layout, sat_prepared,
      by decide⟩

/-- `vg_miller_rabin_round`, given the core (`Core.lean`'s `core_ok`). -/
theorem round_verified_of (hcore : CoreOk) :
    Verified RISCV64.target round (roundContract RISCV64.abi compact frameBytes) :=
  Verified.of_correct (fn_correct hcore) round_ct round_implies

/-- `vg_miller_rabin_round`, verified against the shared contract. -/
theorem round_verified : Verified RISCV64.target round (roundContract RISCV64.abi compact frameBytes) :=
  round_verified_of core_ok

end VG.Proof.MillerRabin.RISCV64
