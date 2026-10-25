module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Init
public import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Update
public import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
public import VerifiedGarbage.Proof.Sha256.Scratch
public import VerifiedGarbage.Proof.Hmac.Stream.Reloc
public import VerifiedGarbage.Spec.Sha256.Contract

/-!
# HMAC over SHA-256 and SHA-224 on RISC-V

The streaming functions of SHA-256 and SHA-224 as HMAC's code over any
streaming hash function calls them (`hash256`, `hash224`): each hash
function's `init` and `finalize`, and SHA-256's `update`, which keep their
working space in frames of their own, within 144 bytes below the stack
pointer; and what the proofs need of them (`ok256`, `ok224`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Sha256Family

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)

/-- SHA-256's streaming functions. -/
def hash256 : Hash where
  b := 6
  N := 32
  D := 32
  F := 144
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.RISCV64.Stream.init
  updN := Spec.Sha256.updateApi.name
  updC := Impl.Sha256.RISCV64.Stream.update
  finN := Spec.Sha256.finalizeApi.name
  finC := Impl.Sha256.RISCV64.Stream.finalize

/-- SHA-224's: its own `init` and `finalize`, and SHA-256's `update`. -/
def hash224 : Hash where
  b := 6
  N := 32
  D := 28
  F := 144
  initN := Spec.Sha256.init224Api.name
  initC := Impl.Sha256.RISCV64.Stream.init224
  updN := Spec.Sha256.updateApi.name
  updC := Impl.Sha256.RISCV64.Stream.update
  finN := Spec.Sha256.finalize224Api.name
  finC := Impl.Sha256.RISCV64.Stream.finalize224

theorem initSd : sdepth Impl.Sha256.RISCV64.Stream.init ≤ 144 := by decide +kernel
theorem init224Sd : sdepth Impl.Sha256.RISCV64.Stream.init224 ≤ 144 := by decide +kernel
theorem updSd : sdepth Impl.Sha256.RISCV64.Stream.update ≤ 144 := by decide +kernel
theorem finSd : sdepth Impl.Sha256.RISCV64.Stream.finalize ≤ 144 := by decide +kernel
theorem fin224Sd : sdepth Impl.Sha256.RISCV64.Stream.finalize224 ≤ 144 := by decide +kernel

open Proof.Sha256.RISCV64.Stream.Finalize (finalHash_length)

/-- What the proofs need of SHA-256's. -/
def ok256 : HashOK hash256 where
  SH := Spec.Hmac.sha256S
  hS := rfl
  hD := rfl
  hB := rfl
  hb := .inl rfl
  hN := by decide
  hD0 := by decide
  hD64 := by decide
  hF := by decide
  init s hs := Proof.Sha256.RISCV64.Stream.init_verified.1 s hs
  upd s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha256.RISCV64.Stream.Update.update_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr hc => h _ m hr hc⟩
  fin s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha256.RISCV64.Stream.Finalize.finalize_verified.1 s hs
    refine ⟨t, s', he, ha, fun m hr _ hc => ?_⟩
    rw [show hash256.D = 4 * 8 from rfl, h _ m hr hc]
    exact List.take_of_length_le (Nat.le_of_eq (finalHash_length _ m))
  initSd := initSd
  updSd := updSd
  finSd := finSd
  reloc m m' p q x hx h hr := Proof.Hmac.Stream.sha256_reloc _ m m' p q x hx h hr
  congr _ _ _ _ h hr := Proof.Sha256.reprFrom_congr (fun i hi => h i hi) hr
  hashLen x := finalHash_length _ x

/-- What the proofs need of SHA-224's. -/
def ok224 : HashOK hash224 where
  SH := Spec.Hmac.sha224S
  hS := rfl
  hD := rfl
  hB := rfl
  hb := .inl rfl
  hN := by decide
  hD0 := by decide
  hD64 := by decide
  hF := by decide
  init s hs := Proof.Sha256.RISCV64.Stream.init224_verified.1 s hs
  upd s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha256.RISCV64.Stream.Update.update_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr hc => h _ m hr hc⟩
  fin s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha256.RISCV64.Stream.Finalize.finalize224_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr _ hc => h _ m hr hc⟩
  initSd := init224Sd
  updSd := updSd
  finSd := fin224Sd
  reloc m m' p q x hx h hr := Proof.Hmac.Stream.sha256_reloc _ m m' p q x hx h hr
  congr _ _ _ _ h hr := Proof.Sha256.reprFrom_congr (fun i hi => h i hi) hr
  hashLen x := by
    show (List.take 28 _).length = 28
    rw [List.length_take, finalHash_length]; rfl

end VG.Proof.Hmac.Stream.RISCV64.Sha256Family
