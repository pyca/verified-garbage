import VerifiedGarbage.Impl.CmacAes.X86_64.Callee
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.CmacAes.X86_64.AesNi

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
`vg_aes_ctr32` on one block at a time (`UpdateImpl.ctr32`, e.g.
`vg_cmac_aes_update_aesni`), and the chaining in AES-NI registers,
`vg_cmac_aes_update_aesni_cbc` (`UpdateImpl.aesniCbc`). Each comes with the
implementation of `vg_aes_ctr32` that goes with it (`ctr`), for the callers
that also run counter mode or call the other CMAC functions (AES-CCM,
AES-SIV): the one it is built on, or for the chaining in registers,
`vg_aes_ctr32_aesni`, which needs no CPU features the AES-NI CPUs it is
chosen for lack.
-/

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
  callee := ⟨Spec.Cmac.aesUpdateApi.name ++ v.suffix, Impl.CmacAes.X86_64.update v.callee⟩
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

theorem aesniCbc_nosp : NoSp Impl.CmacAes.X86_64.AesNi.update := by
  have : ((instrs Impl.CmacAes.X86_64.AesNi.update).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- The chaining in AES-NI registers, `vg_cmac_aes_update_aesni_cbc`, which
goes with `vg_aes_ctr32_aesni`. -/
def UpdateImpl.aesniCbc : UpdateImpl where
  callee := ⟨Spec.Cmac.aesUpdateApi.name ++ "_aesni_cbc", Impl.CmacAes.X86_64.AesNi.update⟩
  depth := by decide +kernel
  ok := AesNi.update_ok
  ct := AesNi.update_ct
  nosp := aesniCbc_nosp
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  xdepth := by decide +kernel
  suffix := "_aesni_cbc"
  features := ["aes"]
  ctr := .aesni

end VG.Proof.CmacAes.X86_64
