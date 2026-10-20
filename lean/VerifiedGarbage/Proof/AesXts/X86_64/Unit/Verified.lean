module

import VerifiedGarbage.Proof.AesXts.X86_64.Unit.CT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Contract
public import VerifiedGarbage.Proof.AesXts.X86_64.Variant
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Dec
import VerifiedGarbage.Proof.AesXts.X86_64.Body

/-!
# XTS-AES of data units on x86-64: `Verified`

Correctness (`encrypt_wp`, `decrypt_wp`) and constant time (`encrypt_ct`,
`decrypt_ct`) for any implementation `v` of the whole-block functions, a
state satisfying the precondition (`unitSat`), and the shared contracts of
`Spec/Xts/Contract.lean`, with 16 bytes of stack: the return addresses of the
call of the whole-block function and of its call of a block function.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.Impl.AesXts.X86_64Unit

theorem encrypt_mx (v : XtsImpl) : (encrypt v.xts).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, tweak, encSteal, swap, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem decrypt_mx (v : XtsImpl) : (decrypt v.xts).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, tweak, decSteal, swap, Code.allInstrs, v.encMxcsr, v.decMxcsr]; decide +kernel

theorem encrypt_spSafe (v : XtsImpl) : (encrypt v.xts).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, tweak, encSteal, swap, Code.all, v.encSpSafe]; decide +kernel

theorem decrypt_spSafe (v : XtsImpl) : (decrypt v.xts).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, tweak, decSteal, swap, Code.all, v.encSpSafe, v.decSpSafe]; decide +kernel

theorem encrypt_correct (v : XtsImpl) (s : State) (hs : (unitX86_64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.xts) s t s' ∧ abiPreserved s s' ∧ (unitX86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : XtsImpl) (s : State) (hs : (unitX86_64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.xts) s t s' ∧ abiPreserved s s' ∧ (unitX86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at 0 (the stack argument, zero). -/
def unitSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 10 | .rcx => 0x3000 | .r8 => 0x4000 | .r9 => 16
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x4000, 16⟩, ⟨0, 2432⟩]

theorem encrypt_verified (v : XtsImpl) :
    Verified X86_64.target (encrypt v.xts) (Spec.Xts.aesEncryptUnitContract X86_64.abi 16) :=
  Verified.of_correct (encrypt_correct v) (encrypt_ct v) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitX86_64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, argR, retR, stk, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified (v : XtsImpl) :
    Verified X86_64.target (decrypt v.xts) (Spec.Xts.aesDecryptUnitContract X86_64.abi 16) :=
  Verified.of_correct (decrypt_correct v) (decrypt_ct v) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitX86_64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, argR, retR, stk, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

end VG.Proof.AesXts.X86_64.Unit
