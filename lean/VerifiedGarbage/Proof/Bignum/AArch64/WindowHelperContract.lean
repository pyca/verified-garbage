module

public import VerifiedGarbage.Proof.Rsa.MontWindowContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Bignum.Layout
import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Impl.Bignum.AArch64.Core
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! ABI bridge for the reviewed five-bit Montgomery window contract. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowHelper
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Keeps arrAt aM minvWord)


/-- The shared ABI specialized to its two arguments. -/
def fnContract : Contract isa where
  pre s :=
    let ws := s.gpr .x0
    let n := (s.gpr .x1).toNat
    let w := wOf s.mem ws
    s.rd = [] ∧ s.wr = [⟨ws, n * 8⟩] ∧ ws.toNat + n * 8 ≤ 2 ^ 64 ∧
      Proof.Rsa.MontWindow.WindowLayout s.mem ws n ∧
      ((s.mem.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat *
        (wordAt s.mem ws minvWord).toNat + 1) % 2 ^ 64 = 0 ∧
      numAt s.mem ws w 6 < numAt s.mem ws w aM ∧
      Proof.Rsa.MontWindow.digit s.mem ws < 32 ∧
      ∀ j < 32, numAt s.mem ws w (8 + j) < numAt s.mem ws w aM
  post s t :=
    let ws := s.gpr .x0
    let w := wOf s.mem ws
    let M := numAt s.mem ws w aM
    numAt t.mem ws w 6 < M ∧
      numAt t.mem ws w 6 * (2 ^ (64 * w)) ^ 32 % M =
        numAt s.mem ws w 6 ^ 32 * numAt s.mem ws w (8 + Proof.Rsa.MontWindow.digit s.mem ws) % M ∧
      wordAt t.mem ws 20 = 0 ∧ wordAt t.mem ws 27 = 0 ∧
      Proof.Rsa.MontWindow.Keeps ws (s.gpr .x1).toNat w s.mem t.mem
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    wOf s.mem (s.gpr .x0) = wOf t.mem (t.gpr .x0)

def satWord (k : Nat) : BitVec 64 :=
  if k = 6 then 2 else if k = 7 then 0xFFFFFFFFFFFFFFFF
  else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 32)
  else if k = 25 then 0x1200 else if k = 32 then 1 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 1536 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 192 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 1536⟩]

theorem fn_implies :
    fnContract.Implies (Proof.Rsa.MontWindow.windowContract abi) where
  pre := by sig_implies_pre [Proof.Rsa.MontWindow.windowContract, Proof.Rsa.MontWindow.sig, fnContract, Proof.Rsa.MontWindow.aY, Proof.Rsa.MontWindow.pendingWord, Proof.Rsa.MontWindow.digitWord, abi, argRegs]
  post := by sig_implies_post [Proof.Rsa.MontWindow.windowContract, Proof.Rsa.MontWindow.sig, fnContract, Proof.Rsa.MontWindow.aY, Proof.Rsa.MontWindow.pendingWord, Proof.Rsa.MontWindow.digitWord, abi, argRegs]
  pub := by
    rintro s t _ _ h
    sig_pub [Proof.Rsa.MontWindow.windowContract, Proof.Rsa.MontWindow.sig, fnContract, Proof.Rsa.MontWindow.aY, Proof.Rsa.MontWindow.pendingWord, Proof.Rsa.MontWindow.digitWord, abi, argRegs] at h
    obtain ⟨hsp, hw, h0, h1⟩ := h
    exact ⟨hsp, h0, h1, List.singleton_inj.mp hw⟩
  sat := by
    sig_implies_sat [Proof.Rsa.MontWindow.windowContract, Proof.Rsa.MontWindow.sig, fnContract, Proof.Rsa.MontWindow.aY, Proof.Rsa.MontWindow.pendingWord, Proof.Rsa.MontWindow.digitWord, abi, argRegs]
        [satState] using satState


end VG.Proof.Bignum.AArch64.WindowHelper
