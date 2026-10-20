module

public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified

/-! # Shared Miller–Rabin round: the callable contract on AArch64 -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64

def roundPre (s : State) : Prop :=
  let ws := s.gpr .x0
  let n := (s.gpr .x1).toNat
  s.rd = [] ∧ s.wr = [⟨ws, n * 8⟩] ∧ ws.toNat + n * 8 ≤ 2 ^ 64 ∧
    Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem ws n ∧
    Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem ws

def roundPost (s t : State) : Prop :=
  let ws := s.gpr .x0
  let w := Spec.Rsa.Mont.wOf s.mem ws
  let c := Spec.Rsa.Mont.numAt s.mem ws w 0
  (∀ b, Spec.Rsa.Mont.numAt s.mem ws w 5 = b % c * 2 ^ (64 * w) % c →
    ((t.gpr .x0).setWidth 32).toNat = if Spec.MillerRabin.round c b then 1 else 0) ∧
    Spec.MillerRabin.Keeps Spec.MillerRabin.compact ws (s.gpr .x1).toNat w s.mem t.mem

def roundPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    Spec.Rsa.Mont.wOf s.mem (s.gpr .x0) = Spec.Rsa.Mont.wOf t.mem (t.gpr .x0)

def roundContract : Contract isa where
  pre := roundPre
  post := roundPost
  pub := roundPub

/-- A four-limb prepared workspace for candidate 3, proving satisfiability
without relying on an imported domain or an assumed prime certificate. -/
private def satWord (i : Nat) : BitVec 64 :=
  if i = 6 then 4 else if i = 7 then 0x5555555555555555 else
    if 8 ≤ i ∧ i < 16 then BitVec.ofNat 64 (0x1100 + 48 * (i - 8)) else
    if i = 28 then 48 else if i = 32 then 3 else if i = 62 then 2 else
    if i = 86 then 1 else if i = 92 then 2 else if i = 194 then 1 else if i = 198 then 2 else 0

private def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 2048 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

private def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 256 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 2048⟩]

private theorem sat_layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact
    satMem 0x1000 256 := by
  simp only [Spec.MillerRabin.Layout, Spec.MillerRabin.compact, Spec.Rsa.Mont.Layout,
    Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
  decide +kernel

private theorem sat_prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact
    satMem 0x1000 := by
  have hw : Spec.Rsa.Mont.wOf satMem 0x1000 = 4 := by decide +kernel
  have hc : Spec.Rsa.Mont.numAt satMem 0x1000 4 0 = 3 := by
    rw [VG.Proof.Bignum.AArch64.MontFn.numAt_eq]; decide +kernel
  have h5 : Spec.Rsa.Mont.numAt satMem 0x1000 4 5 = 2 := by
    rw [VG.Proof.Bignum.AArch64.MontFn.numAt_eq]; decide +kernel
  have h9 : Spec.Rsa.Mont.numAt satMem 0x1000 4 9 = 1 := by
    rw [VG.Proof.Bignum.AArch64.MontFn.numAt_eq]; decide +kernel
  have h10 : Spec.Rsa.Mont.numAt satMem 0x1000 4 10 = 2 := by
    rw [VG.Proof.Bignum.AArch64.MontFn.numAt_eq]; decide +kernel
  have h27 : Spec.Rsa.Mont.numAt satMem 0x1000 4 27 = 1 := by
    rw [VG.Proof.Bignum.AArch64.MontFn.numAt_eq]; decide +kernel
  simp only [Spec.MillerRabin.Prepared, Spec.MillerRabin.compact, hw, hc, h5, h9, h10, h27]
  decide +kernel

theorem round_implies : roundContract.Implies
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact) where
  pre := by
    intro s h
    sig_pre [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argRegs] at h
    sig_split h
    sig_reduce [roundContract, roundPre, Spec.MillerRabin.Prepared]
    sig_and_intros
    sig_close
    all_goals dsimp only [Spec.MillerRabin.compact] at *; with_reducible assumption
  post := by sig_implies_post [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig,
    roundContract, roundPost, abi, argRegs]
  pub := by
    rintro s t - - h
    sig_pub [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig,
      roundContract, roundPub, abi, argRegs] at h
    obtain ⟨hsp, hw, h0, h1⟩ := h
    exact ⟨hsp, h0, h1, List.singleton_inj.mp hw⟩
  sat := by
    refine ⟨satState, ?_⟩
    sig_pre [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argRegs]
    sig_and_intros
    all_goals first
      | exact sat_layout
      | exact sat_prepared
      | decide +kernel

end VG.Proof.MillerRabin.AArch64
