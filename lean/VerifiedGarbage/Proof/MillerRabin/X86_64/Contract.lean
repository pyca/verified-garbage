module

public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Framework.Offset

/-! # Shared Miller–Rabin round: the callable contract on X86_64 -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64

def roundPre (s : State) : Prop :=
  let ws := s.gpr .rdi
  let n := (s.gpr .rsi).toNat
  s.rd = [] ∧ s.wr = [⟨ws, n * 8⟩] ∧ ws.toNat + n * 8 ≤ 2 ^ 64 ∧
    120 ≤ (s.gpr .rsp).toNat ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨ws, n * 8⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - 120#64, 120⟩ ⟨ws, n * 8⟩ ∧
    Spec.MillerRabin.Layout Spec.MillerRabin.extended s.mem ws n ∧
    Spec.MillerRabin.Prepared Spec.MillerRabin.extended s.mem ws

def roundPost (s t : State) : Prop :=
  let ws := s.gpr .rdi
  let w := Spec.Rsa.Mont.wOf s.mem ws
  let c := Spec.Rsa.Mont.numAt s.mem ws w 0
  (∀ b, Spec.Rsa.Mont.numAt s.mem ws w 5 = b % c * 2 ^ (64 * w) % c →
    ((t.gpr .rax).setWidth 32).toNat = if Spec.MillerRabin.round c b then 1 else 0) ∧
    Spec.MillerRabin.Keeps Spec.MillerRabin.extended ws (s.gpr .rsi).toNat w s.mem t.mem

def roundPub (s t : State) : Prop :=
  s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    Spec.Rsa.Mont.wOf s.mem (s.gpr .rdi) = Spec.Rsa.Mont.wOf t.mem (t.gpr .rdi)

def roundContract : Contract isa where
  pre := roundPre
  post := roundPost
  pub := roundPub

/-- A four-limb prepared workspace for candidate 3, proving satisfiability
without relying on an imported domain or an assumed prime certificate. -/
private def satWord (i : Nat) : BitVec 64 :=
  if i = 6 then 4 else if i = 7 then 0x5555555555555555 else
    if 8 ≤ i ∧ i < 16 then BitVec.ofNat 64 (0x1100 + 48 * (i - 8)) else
    if i = 32 then 3 else if i = 62 then 2 else
    if i = 182 then 1 else if i = 188 then 2 else if i = 176 then 1 else if i = 180 then 2 else 0

private def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 2048 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

private def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 256 | .rsp => 0x8000 | _ => 0
  cf := false
  zf := false
  sf := false
  of := false
  mem := satMem
  rd := []
  wr := [⟨0x1000, 2048⟩]

private theorem sat_layout : Spec.MillerRabin.Layout Spec.MillerRabin.extended
    satMem 0x1000 256 := by
  simp only [Spec.MillerRabin.Layout, Spec.MillerRabin.extended, Spec.Rsa.Mont.Layout,
    Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
  decide +kernel

private theorem sat_prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.extended
    satMem 0x1000 := by
  have hw : Spec.Rsa.Mont.wOf satMem 0x1000 = 4 := by decide +kernel
  have hc : Spec.Rsa.Mont.numAt satMem 0x1000 4 0 = 3 := by
    rw [VG.Proof.Bignum.X86_64.MontFn.numAt_eq]; decide +kernel
  have h5 : Spec.Rsa.Mont.numAt satMem 0x1000 4 5 = 2 := by
    rw [VG.Proof.Bignum.X86_64.MontFn.numAt_eq]; decide +kernel
  have h25 : Spec.Rsa.Mont.numAt satMem 0x1000 4 25 = 1 := by
    rw [VG.Proof.Bignum.X86_64.MontFn.numAt_eq]; decide +kernel
  have h26 : Spec.Rsa.Mont.numAt satMem 0x1000 4 26 = 2 := by
    rw [VG.Proof.Bignum.X86_64.MontFn.numAt_eq]; decide +kernel
  have h24 : Spec.Rsa.Mont.numAt satMem 0x1000 4 24 = 1 := by
    rw [VG.Proof.Bignum.X86_64.MontFn.numAt_eq]; decide +kernel
  simp only [Spec.MillerRabin.Prepared, Spec.MillerRabin.extended, hw, hc, h5, h25, h26, h24]
  decide +kernel

theorem round_implies : roundContract.Implies
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.extended 120) where
  pre := by
    intro s h
    sig_pre [stackBelow, Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argRegs] at h
    sig_split h
    rename_i hsp hrd hwr hret hstk hnowrap hLayout hc3 hodd hinv hxm hr1 hrm1 he
    sig_reduce [roundContract, roundPre, Spec.MillerRabin.Prepared, stackBelow]
    sig_and_intros
    sig_close
    all_goals dsimp only [Spec.MillerRabin.extended] at *
    · exact hstk
    · exact hr1
    · exact hrm1
    · exact he
    · exact h
  post := by sig_implies_post [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig,
    roundContract, roundPost, abi, argRegs]
  pub := by
    rintro s t - - h
    sig_pub [stackBelow, Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig,
      roundContract, roundPub, abi, argRegs] at h
    obtain ⟨hsp, hw, h0, h1⟩ := h
    exact ⟨hsp, h0, h1, List.singleton_inj.mp hw⟩
  sat := by
    refine ⟨satState, ?_⟩
    sig_pre [stackBelow, Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argRegs]
    sig_and_intros
    all_goals first
      | exact sat_layout
      | exact sat_prepared
      | exact Region.disjoint_of_le (by decide +kernel) (by decide +kernel) (by decide +kernel)
      | decide +kernel

end VG.Proof.MillerRabin.X86_64
