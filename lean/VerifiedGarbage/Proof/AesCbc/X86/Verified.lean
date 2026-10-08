import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCbc.X86.CT

/-!
# AES-CBC on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), a state satisfying the precondition, and the shared contracts of
`Spec/Cbc/Contract.lean`, with 24 bytes of stack: each call of a block
function pushes its five arguments and the return address.
-/

namespace VG.Proof.AesCbc.X86

open VG VG.X86 VG.Impl.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, whole, encBody, blkCall, Code.all, v.encSpSafe]
  decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.dec).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, whole, decBody, blkCall, Code.all, v.decSpSafe]
  decide +kernel

/-- A state satisfying the precondition: the schedule at `0x1000`, 10
rounds, the chaining value at `0x2000`, no blocks at `0x3000` and the scratch
buffer at `0x4000`, as stack arguments at `0x8004`. -/
def sat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 24⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩]

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (encrypt v.enc) (Spec.Cbc.aesEncryptContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (encBody_ok v) hs) (whole_ct (encBody_ok v) (encBody_ct v)) (by
    have a0 : arg sat 0 = 0x1000 := by decide
    have a1 : arg sat 1 = 10 := by decide
    have a2 : arg sat 2 = 0x2000 := by decide
    have a3 : arg sat 3 = 0x3000 := by decide
    have a4 : arg sat 4 = 0 := by decide
    have a5 : arg sat 5 = 0x4000 := by decide
    have e : argAddr sat 0 = 0x8004 := by decide
    have esp : sat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cbc.aesEncryptContract, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, cbcX86, modeX86, cbcMode, ciphOf, cbc, cts] [a0, a1, a2, a3, a4, a5, e, esp] using sat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (decrypt v.dec) (Spec.Cbc.aesDecryptContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (decBody_ok v) hs) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    have a0 : arg sat 0 = 0x1000 := by decide
    have a1 : arg sat 1 = 10 := by decide
    have a2 : arg sat 2 = 0x2000 := by decide
    have a3 : arg sat 3 = 0x3000 := by decide
    have a4 : arg sat 4 = 0 := by decide
    have a5 : arg sat 5 = 0x4000 := by decide
    have e : argAddr sat 0 = 0x8004 := by decide
    have esp : sat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cbc.aesDecryptContract, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, cbcX86, modeX86, cbcMode, ciphOf, cbc, cts] [a0, a1, a2, a3, a4, a5, e, esp] using sat)

end VG.Proof.AesCbc.X86
