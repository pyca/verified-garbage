module

import VerifiedGarbage.Proof.Ffdh.X86.ExchangeCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # `vg_ffdh_exchange` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Exchange

open VG VG.X86

theorem correct (s : State) (h : (Spec.Ffdh.exchangeContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.Exchange.code s trace t ∧ abiPreserved s t ∧
      (Spec.Ffdh.exchangeContract abi stack).post s t := by
  obtain ⟨trace, t, E, V, P⟩ := operation_ok (exchangeABI_of h)
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

/-- An output of 64 bytes, a domain of 128, `p_len` 64, x of one byte, y of 64 and a working space of
1056 words, apart. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 0x10
    else if a = 0x20008 then 64
    else if a = 0x2000d then 0x20
    else if a = 0x20010 then 128
    else if a = 0x20014 then 64
    else if a = 0x20019 then 0x40
    else if a = 0x2001c then 1
    else if a = 0x20021 then 0x30
    else if a = 0x20024 then 64
    else if a = 0x20029 then 0x90
    else if a = 0x2002c then 0x20
    else if a = 0x2002d then 4 else 0
  rd := [⟨8192, 128⟩, ⟨16384, 1⟩, ⟨12288, 64⟩]
  wr := [⟨4096, 64⟩, ⟨36864, 8448⟩, ⟨0x20004, 44⟩]

theorem satisfiable : ∃ s, (Spec.Ffdh.exchangeContract abi stack).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 128 := by decide
  have a4 : arg satState 4 = 64 := by decide
  have a5 : arg satState 5 = 16384 := by decide
  have a6 : arg satState 6 = 1 := by decide
  have a7 : arg satState 7 = 12288 := by decide
  have a8 : arg satState 8 = 64 := by decide
  have a9 : arg satState 9 = 36864 := by decide
  have a10 : arg satState 10 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argSlots, argVal, argBytes,
    stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp, satState, Spec.Rsa.scratchWords] using satState

theorem verified : Verified target Impl.Ffdh.X86.Exchange.code (Spec.Ffdh.exchangeContract abi stack) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.Exchange
