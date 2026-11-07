module

public import VerifiedGarbage.Impl.CmacAes.X86_64.Callee
public import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
public import VerifiedGarbage.Proof.CmacAes.X86_64.AesNi
import VerifiedGarbage.Proof.Framework.EntryBranch

/-!
# Implementations of `vg_cmac_aes_update` on x86-64

An `UpdateImpl` is what a function that calls `vg_cmac_aes_update` needs of
it, so that its proof holds for every implementation: each is a variant of
the interface `CmacAesUpdate` on x86-64 (`Variants/CmacAesUpdate/X86_64/`),
and each caller (in `Generic/CmacAesUpdate/X86_64/`) is emitted once for
each of them (see `TCB/Emit.lean`). Every implementation is proven against
the same contract, `updateX86_64`, makes at most one level of calls, and
uses at most 8 bytes of stack (the return address of its call of
`vg_aes_ctr32`).

There are two kinds: the chaining by calls of an implementation of
`vg_aes_ctr32` on one block at a time (`UpdateImpl.ctr32`, e.g. the
baseline `vg_cmac_aes_update`), and, for the implementations that need
AES-NI, the chaining in AES-NI registers for two blocks or more and by calls
of the implementation for fewer (`UpdateImpl.hybrid`, e.g.
`vg_cmac_aes_update_aesni`). Each comes with the implementation of
`vg_aes_ctr32` that goes with it (`ctr`), the one it calls, for the callers
that also run counter mode or call the other CMAC functions (AES-CCM,
AES-SIV).
-/

@[expose] public section

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- An implementation of `vg_cmac_aes_update` on x86-64. -/
structure UpdateImpl where
  /-- Its symbol and code. -/
  callee : Impl.CmacAes.X86_64.Update
  /-- It makes at most one level of calls. -/
  depth : callee.code.depth ≤ 1
  ok : ∀ s, updateX86_64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s'
  ct : ConstantTime isa updateX86_64.pre updateX86_64.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- It uses at most 8 bytes of stack. -/
  xdepth : callee.code.x86_64Depth ≤ 8
  /-- What the names of its callers' instances end with (e.g. `_aesni_cbc`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_ctr32` that goes with it, for callers
  that also call it or the other CMAC functions made with it. -/
  ctr : Ctr32Impl

theorem update_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.update v.callee) := by
  have h : (Impl.CmacAes.X86_64.update v.callee).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    have hv : v.callee.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
      rw [Code.allInstrs_eq, List.all_eq_true]
      exact fun i hi => by simp [v.nosp i hi]
    simp only [Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.allInstrs, hv]
    decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem update_depth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.update v.callee).depth = 1 := by
  simp [Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.depth, v.depth]

theorem update_xdepth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.update v.callee).x86_64Depth = 8 := by
  simp [Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.x86_64Depth, v.noStack]

/-- The chaining by calls of `v` on one block at a time,
`vg_cmac_aes_update` with `v`'s suffix. -/
def UpdateImpl.ctr32 (v : Ctr32Impl) : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update" ++ v.suffix, Impl.CmacAes.X86_64.update v.callee⟩
  depth := by rw [update_depth]
  ok := update_correct v
  ct := update_ct v
  nosp := update_nosp v
  mxcsr := update_mx v
  spSafe := update_spSafe v
  xdepth := by rw [update_xdepth]
  suffix := v.suffix
  features := v.features
  ctr := v

/-! ## The chaining in AES-NI registers -/

theorem aesniCbc_nosp : NoSp Impl.CmacAes.X86_64.AesNi.update := by
  have : ((instrs Impl.CmacAes.X86_64.AesNi.update).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

theorem aesniCbc_depth : Impl.CmacAes.X86_64.AesNi.update.depth = 0 := by decide +kernel

theorem aesniCbc_xdepth : Impl.CmacAes.X86_64.AesNi.update.x86_64Depth = 0 := by decide +kernel

theorem aesniCbc_mx : Impl.CmacAes.X86_64.AesNi.update.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem aesniCbc_spSafe : Impl.CmacAes.X86_64.AesNi.update.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by decide +kernel)

/-! ## The choice by the number of blocks -/

/-- `hybrid v`, for the proofs of a state satisfying the precondition (which
`Verified` asks of each branch): the chaining in AES-NI registers for two
blocks or more, otherwise by a call of `v` (`Verified.entryBranch`). The
comparison writes only the flags, which the contract does not read, and
leaks nothing; the branch depends only on `n` (`r8`), which is public. -/
theorem hybrid_verified (v : Ctr32Impl) {s₀ : State} (h₀ : updateX86_64.pre s₀) :
    Verified X86_64.target (Impl.CmacAes.X86_64.hybrid v.callee) updateX86_64 := by
  refine Verified.entryBranch (p := fun s => decide (2 ≤ (s.gpr .r8).toNat)) (fun _ => [])
    ⟨AesNi.update_ok, AesNi.update_ct, _, h₀⟩ ⟨update_correct v, update_ct v, _, h₀⟩
    (fun s hs => ⟨_, rfl, ?_, fun _ => ⟨hs, fun _ a q => ⟨a, q⟩⟩, fun _ => ⟨hs, fun _ a q => ⟨a, q⟩⟩⟩)
    ?_ ⟨_, h₀⟩
  · show Option.map (!·) (some (decide ((s.gpr .r8).toNat <
      ((2 : BitVec 32).signExtend 64).toNat))) = _
    rw [show ((2 : BitVec 32).signExtend 64).toNat = 2 from by decide]
    simp only [Option.map_some, ← decide_not, Nat.not_lt]
  · intro s s' u u' _ _ hq e e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    exact ⟨rfl, by rw [hq.2.2.2.2.1], fun _ => hq, fun _ => hq⟩

theorem hybrid_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.hybrid v.callee) := by
  intro i hi
  simp only [Impl.CmacAes.X86_64.hybrid, Code.iteCold, instrs, List.nil_append, List.mem_append,
    List.mem_singleton] at hi
  rcases hi with rfl | hi | hi
  · rfl
  · exact aesniCbc_nosp i hi
  · exact update_nosp v i hi

/-- The chaining in AES-NI registers for two blocks or more, otherwise by
calls of `v` on one block at a time: `vg_cmac_aes_update` with `v`'s
suffix, for an implementation `v` that needs AES-NI. -/
def UpdateImpl.hybrid (v : Ctr32Impl) : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update" ++ v.suffix, Impl.CmacAes.X86_64.hybrid v.callee⟩
  depth := by
    have h₁ := aesniCbc_depth; have h₂ := update_depth v
    simp only [Impl.CmacAes.X86_64.hybrid, Code.iteCold, Code.depth, Nat.max_le] at *
    exact ⟨Nat.zero_le _, ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, h₁ ▸ Nat.zero_le _⟩, Nat.le_of_eq h₂⟩
  ok := fun s hs => (hybrid_verified v hs).1 s hs
  ct := fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ => (hybrid_verified v h₁).2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂
  nosp := hybrid_nosp v
  mxcsr := by
    have := aesniCbc_mx; have := update_mx v
    simp only [Impl.CmacAes.X86_64.hybrid, Code.iteCold, Code.allInstrs] at *
    simp only [*]
    rfl
  spSafe := by
    have := aesniCbc_spSafe; have := update_spSafe v
    simp only [Impl.CmacAes.X86_64.hybrid, Code.iteCold, Code.all] at *
    simp only [*]
    rfl
  xdepth := by
    simp only [Impl.CmacAes.X86_64.hybrid, Code.iteCold, Code.x86_64Depth, aesniCbc_xdepth, update_xdepth]
    decide
  suffix := v.suffix
  features := v.features
  ctr := v

end VG.Proof.CmacAes.X86_64
