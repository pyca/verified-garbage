module

public import VerifiedGarbage.Proof.MillerRabin.Workspace

public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.MillerRabin.Arm.Base
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The Miller–Rabin round on ARMv7: the contract its callers use

`roundContract`: the round's contract, as the code needs it and its callers
establish it: the working space laid out for Montgomery multiplication
(`LayoutLite`, with its first 28 arrays) and the candidate, the witness,
Montgomery one and minus one, the exponent and the word `2^(t mod 64)` after
it in it (`PreparedLite`), as in the shared contract, without its
representation's choice and stride. Only the arrays `wJs` and the header
words 23, 26, 29 and 30 change (`KeepsLite`).
It implies `Spec.MillerRabin.roundContract` (`round_implies`, `Proof/MillerRabin/Arm/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt)

export VG.Proof.MillerRabin.Workspace (LayoutLite PreparedLite read_congr_on readW_congr_on layout_congr numAt_congr prepared_congr)

/-- Only the header words 23, 26, 29 and 30 and the arrays `wJs` change. -/
def KeepsLite (ws : Addr) (len w : Nat) (m m' : Mem) : Prop :=
  ∀ i < 8 * len, (∀ k ∈ [23, 26, 29, 30], i < 8 * k ∨ 8 * k + 8 ≤ i) →
    (∀ j ∈ wJs, i < arrAt w j ∨ arrAt w j + 8 * (w + 2) ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

def roundPre (s : State) : Prop :=
  let ws := State.addr (s.gpr .r0)
  let n := (s.gpr .r1).toNat
  s.rd = [] ∧ s.wr = [⟨ws, 8 * n⟩] ∧ (s.gpr .r0).toNat + 8 * n ≤ 2 ^ 32 ∧ 56 ≤ s.sp.toNat ∧
    (FrameStack.belowA s.sp 56).Disjoint ⟨ws, 8 * n⟩ ∧ LayoutLite s.mem ws n ∧ PreparedLite s.mem ws

def roundPost (s t : State) : Prop :=
  let ws := State.addr (s.gpr .r0)
  let w := wOf s.mem ws
  let c := numAt s.mem ws w 0
  (∀ b, numAt s.mem ws w 5 = b % c * 2 ^ (64 * w) % c →
    (t.gpr .r0).toNat = if Spec.MillerRabin.round c b then 1 else 0) ∧
    KeepsLite ws (s.gpr .r1).toNat w s.mem t.mem

def roundPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    wOf s.mem (State.addr (s.gpr .r0)) = wOf t.mem (State.addr (t.gpr .r0))

/-- The round's contract on ARMv7, as its callers use it. -/
def roundContract : Contract isa where
  pre := roundPre
  post := roundPost
  pub := roundPub

end VG.Proof.MillerRabin.Arm
