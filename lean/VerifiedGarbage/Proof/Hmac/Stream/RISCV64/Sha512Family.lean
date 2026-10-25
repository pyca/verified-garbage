module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Init
public import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Update
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Finalize
public import VerifiedGarbage.Proof.Hmac.Stream.Reloc
public import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Proof.Sha512.Stream
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
public import VerifiedGarbage.Proof.Sha512.RISCV64.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# HMAC over the SHA-512 family on RISC-V

The streaming functions of SHA-384, SHA-512, SHA-512/224 and SHA-512/256 as
HMAC's code over any streaming hash function calls them (`hash`): the hash
function's `init` (from its initial hash value `iv`) and `finalize` (writing
its `D`-byte digest), and SHA-512's `update`, which keep their working space
in frames of their own, within 208 bytes below the stack pointer; and what
the proofs need of them (`ok`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Sha512Family

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open Spec.Sha512 (HashValue)

/-- The streaming functions of the hash function with initial hash value
`iv` (whose `init` is `initN`) and a digest of `D` bytes, written by
`finC` (named `finN`). -/
def hash (iv : HashValue) (D : Nat) (initN finN : String) (finC : Prog isa) : Hash where
  b := 7
  N := 64
  D := D
  F := 208
  initN := initN
  initC := Impl.Sha512.RISCV64.Stream.initWith iv
  updN := Spec.Sha512.updateApi.name
  updC := Impl.Sha512.RISCV64.Stream.update
  finN := finN
  finC := finC

theorem updSd : sdepth Impl.Sha512.RISCV64.Stream.update ≤ 208 := by decide +kernel

/-- What the proofs need of them, for a hash function `HF` of SHA-512's block
whose digest is the first `D` bytes of the final hash value from `iv`. -/
def ok (iv : HashValue) (D : Nat) (initN finN : String) (finC : Prog isa) (HF : Spec.Hmac.HashFunction)
    (hB : HF.blockSize = 128) (hD : 0 < D ∧ D ≤ 64)
    (hinit : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith iv) (Proof.Sha512.initRISCV64 iv))
    (hfin : Verified RISCV64.target finC (Proof.Sha512.finalizeDRISCV64 D)) (hfs : sdepth finC ≤ 208)
    (htake : ∀ x, HF.hash x = (Spec.Sha512.finalHash iv x).take D) :
    HashOK (hash iv D initN finN finC) where
  SH := ⟨HF, 192, D, Spec.Sha512.Repr iv⟩
  hS := rfl
  hD := rfl
  hB := hB
  hb := .inr rfl
  hN := by show 0 < 64 ∧ 64 ≤ 64; decide
  hD0 := hD.1
  hD64 := hD.2
  hF := by show 208 ≤ 1024; decide
  init s hs := hinit.1 s hs
  upd s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha512.RISCV64.Stream.Update.update_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr hc => h iv m hr hc⟩
  fin s hs := by
    obtain ⟨t, s', he, ha, h⟩ := hfin.1 s hs
    exact ⟨t, s', he, ha, fun m hr hl hc => (h iv m hr hl hc).trans (htake m).symm⟩
  initSd := Nat.zero_le _
  updSd := updSd
  finSd := hfs
  reloc m m' p q x hx h hr := Proof.Hmac.Stream.sha512_reloc iv m m' p q x hx h hr
  congr _ _ _ _ h hr := Proof.Sha512.Stream.repr_congr (fun i hi => h i hi) hr
  hashLen x := by
    rw [htake, List.length_take, Proof.Hmac.Generic.Common.finalHash_length]
    show min D 64 = D
    omega

end VG.Proof.Hmac.Stream.RISCV64.Sha512Family
