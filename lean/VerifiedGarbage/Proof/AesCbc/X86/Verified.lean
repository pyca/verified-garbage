module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Impl.AesCbc.X86
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Proof.AesCbc.X86.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-CBC on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), a state satisfying the precondition, and the shared contracts of
`Spec/Cbc/Contract.lean`, with 24 bytes of stack: each call of a block
function pushes its five arguments and the return address.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86

open VG VG.X86 VG.Impl.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)

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

theorem enc_implies : (cbcX86 true).Implies (Proof.AesCbc.encryptRoundsContract X86.abi 24) := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 10 := by decide
  have a2 : arg sat 2 = 0x2000 := by decide
  have a3 : arg sat 3 = 0x3000 := by decide
  have a4 : arg sat 4 = 0 := by decide
  have a5 : arg sat 5 = 0x4000 := by decide
  have e : argAddr sat 0 = 0x8004 := by decide
  have esp : sat.gpr .esp = 0x8000 := rfl
  sig_implies [Proof.AesCbc.encryptRoundsContract, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, cbcX86, modeX86, cbcMode, ciphOf, cbc, cts] [a0, a1, a2, a3, a4, a5, e, esp] using sat

theorem dec_implies : (cbcX86 false).Implies (Proof.AesCbc.decryptRoundsContract X86.abi 24) := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 10 := by decide
  have a2 : arg sat 2 = 0x2000 := by decide
  have a3 : arg sat 3 = 0x3000 := by decide
  have a4 : arg sat 4 = 0 := by decide
  have a5 : arg sat 5 = 0x4000 := by decide
  have e : argAddr sat 0 = 0x8004 := by decide
  have esp : sat.gpr .esp = 0x8000 := rfl
  sig_implies [Proof.AesCbc.decryptRoundsContract, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, cbcX86, modeX86, cbcMode, ciphOf, cbc, cts] [a0, a1, a2, a3, a4, a5, e, esp] using sat

/-! ## Leaving of the scratch buffer only what the block function writes -/

theorem encryptZ_verified (v : BlocksImpl) :
    Verified X86.target (encryptZ v.enc) (Proof.AesCbc.encryptRoundsContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => (wholeZ_wp (encBody_okB v) hs).mono fun _ h => ⟨h.1, h.2.1⟩)
    (wholeZ_ct (encBody_ok v) (encBody_ct v)) enc_implies

theorem decryptZ_verified (v : BlocksImpl) :
    Verified X86.target (decryptZ v.dec) (Proof.AesCbc.decryptRoundsContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => (wholeZ_wp (decBody_okB v) hs).mono fun _ h => ⟨h.1, h.2.1⟩)
    (wholeZ_ct (decBody_ok v) (decBody_ct v)) dec_implies

/-- `encryptZ` leaves each byte of the scratch buffer from offset
`v.encWritten` on unchanged or zero. -/
theorem encryptZ_tail (v : BlocksImpl) (s : State) (hs : (cbcX86 true).pre s) (t : List Leak) (s' : State)
    (he : Exec isa (encryptZ v.enc) s t s') : ∀ i, v.encWritten ≤ i → i < 2176 →
      s'.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) ∨
        s'.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) = 0 := by
  obtain ⟨t', s'', he', -, -, h⟩ := wholeZ_wp (encBody_okB v) hs
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact h

theorem decryptZ_tail (v : BlocksImpl) (s : State) (hs : (cbcX86 false).pre s) (t : List Leak) (s' : State)
    (he : Exec isa (decryptZ v.dec) s t s') : ∀ i, v.decWritten ≤ i → i < 2176 →
      s'.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) ∨
        s'.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) = 0 := by
  obtain ⟨t', s'', he', -, -, h⟩ := wholeZ_wp (decBody_okB v) hs
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact h

end VG.Proof.AesCbc.X86
