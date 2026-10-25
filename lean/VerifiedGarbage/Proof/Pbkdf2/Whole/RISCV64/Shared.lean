module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.CT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Contract

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: the shared contract

`pbkdf2`'s generic proof (`correct`, `ct`) is written against `pbkR`, with
the stack its frames and its callees use; it is moved to the shared
contract of an instance `I` of the hash function (`generic_implies`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)

theorem pbkImp (I : Spec.Hmac.Instance) (n : Nat) (hs : ∃ s, (I.pbkdf2Contract RISCV64.abi (n + 1)).pre s) :
    (pbkR I.S (n + 1)).Implies (I.pbkdf2Contract RISCV64.abi (n + 1)) := by
  generic_implies [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, pbkR, RISCV64.abi, RISCV64.argRegs] using hs

variable {F : Fns}

/-- `pbkdf2` against the shared contract, given the taint checks of its pieces. -/
theorem shared (hF : FnsOK F) (hc : Checks F) {I : Spec.Hmac.Instance} (hSH : hF.hH.SH = I.S)
    (hs : ∃ s, (I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)).pre s) :
    Verified RISCV64.target F.pbkdf2 (I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) := by
  obtain ⟨n, hn⟩ : ∃ n, F.itB + F.frB + F.X = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by have := (layout (F := F)).2.2.2.2.2.2.2; simp only [Fns.bytes] at this; omega)).symm⟩
  have imp := pbkImp I n (by rw [← hn]; exact hs)
  rw [← hSH] at imp
  have v : Verified RISCV64.target F.pbkdf2 (pbkR hF.hH.SH (n + 1)) :=
    ⟨fun s hs' => by
      obtain ⟨t, s', he, h₁, h₂⟩ := correct hF (by rw [hn]; exact hs'); rw [hn] at h₂; exact ⟨t, s', he, h₁, h₂⟩,
      by rw [← hn]; exact ct hF hc, imp.sat_left⟩
  rw [hn]
  exact v.of_implies imp

/-- A state satisfying `pbkdf2`'s precondition: an empty password, salt and
output, and `c = 1`. -/
def pbkSat : State where
  gpr r := match r with
    | .a0 => 0x10000 | .a2 => 0x20000 | .a4 => 1 | .a5 => 0x30000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩]
  wr := [⟨0x30000, 0⟩]

end VG.Proof.Pbkdf2.Whole.RISCV64
