module

public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.Mem
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact

/-!
# AES-CMAC on PPC64LE: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). A call (`bl`) stores nothing in memory,
so no stack is used.
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_subkeys(schedule = r3, rounds = r4, subkeys = r5, scratch = r6)`. -/
def subkeysPPC64LE : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let subk : Region := ⟨s.gpr .r5, 32⟩
    let scr : Region := ⟨s.gpr .r6, 2176⟩
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      (s.gpr .r5).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) 16
    Spec.Aes.bytesAt s'.mem (s.gpr .r5) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_update(schedule = r3, rounds = r4, state = r5, data = r6, n = r7, scratch = r8)`. -/
def updatePPC64LE : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let state : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 2176⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .r5).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 16 * (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .r5) 16 =
      Spec.Cmac.chain (ciphAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .r5) 16)
        (Spec.Cmac.blocksAt s.mem (s.gpr .r6) 16 (s.gpr .r7).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_finalize(key = r3, rounds = r4, state = r5, last = r6, last_len = r7, scratch = r8)`. -/
def finalizePPC64LE : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 272⟩
    let state : Region := ⟨s.gpr .r5, 16⟩
    let last : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 2176⟩
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .r3).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14) ∧
      (s.gpr .r7).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .r3) (s.gpr .r4).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (s.gpr .r3 + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (s.gpr .r7).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .r5) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .r5) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.sp = s₂.sp

end VG.Proof.CmacAes.PPC64LE
