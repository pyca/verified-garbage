module
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Work
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarCT

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutputCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
meta import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-! # FFDH on x86-64: successful scalar attempts use the shared exponentiation timing proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A checked scalar and its two full-width output buffers. -/
def WorkIn (p : GkP) (s : State) : Prop := ∃ rb mi,
  CheckPrivate.Work p.kp (p.xb rb) mi s ∧ s.gpr .rdi = off p.B (inner p.w) ∧
    p.mv = true ∧ Buffers p rb s

theorem work_inner (p : GkP) (s : State) (h : WorkIn p s) : CheckPrivate.Inner p.kp s := by
  obtain ⟨rb, mi, hw, hd, hm, _⟩ := h
  exact ⟨_, mi, hw, hd, hm⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
