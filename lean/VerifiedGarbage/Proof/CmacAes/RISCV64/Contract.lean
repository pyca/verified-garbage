module

public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.Mem
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact

/-!
# AES-CMAC on RISC-V: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). A call (`jal`) stores nothing in memory,
so no stack is used.
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_subkeys(schedule = a0, rounds = a1, subkeys = a2, scratch = a3)`. -/
def subkeysRISCV64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let subk : Region := ⟨s.gpr .a2, 32⟩
    let scr : Region := ⟨s.gpr .a3, 2176⟩
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      (s.gpr .a2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) 16
    Spec.Aes.bytesAt s'.mem (s.gpr .a2) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_update(schedule = a0, rounds = a1, state = a2, data = a3, n = a4, scratch = a5)`. -/
def updateRISCV64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let state : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .a2) 16 =
      Spec.Cmac.chain (ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .a2) 16)
        (Spec.Cmac.blocksAt s.mem (s.gpr .a3) 16 (s.gpr .a4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_finalize(key = a0, rounds = a1, state = a2, last = a3, last_len = a4, scratch = a5)`. -/
def finalizeRISCV64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 272⟩
    let state : Region := ⟨s.gpr .a2, 16⟩
    let last : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .a0).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) ∧
      (s.gpr .a4).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (s.gpr .a0 + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (s.gpr .a4).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .a2) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .a2) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

end VG.Proof.CmacAes.RISCV64
