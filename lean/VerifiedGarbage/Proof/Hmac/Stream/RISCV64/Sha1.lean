module

import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Shared
public import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
meta import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
public import VerifiedGarbage.Proof.Hmac.Stream.Reloc
public import VerifiedGarbage.Proof.Hmac.Scratch
public import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Hmac.Stream.Reloc
meta import VerifiedGarbage.Proof.Hmac.Scratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash

/-!
# HMAC-SHA-1 on RISC-V

SHA-1's streaming functions as HMAC's code over any streaming hash function
calls them (`hash`), which keep their working space in frames of their own,
within 144 bytes below the stack pointer; what the proofs need of them
(`ok`); the constant time of HMAC's code for them, which the kernel checks;
and the functions against the shared contracts of `Spec.Hmac.sha1I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Sha1

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)

/-- SHA-1's streaming functions. -/
def hash : Hash where
  b := 6
  N := 20
  D := 20
  F := 144
  initN := Spec.Sha1.initApi.name
  initC := Impl.Sha1.RISCV64.Stream.init
  updN := Spec.Sha1.updateApi.name
  updC := Impl.Sha1.RISCV64.Stream.update
  finN := Spec.Sha1.finalizeApi.name
  finC := Impl.Sha1.RISCV64.Stream.finalize

theorem initSd : sdepth Impl.Sha1.RISCV64.Stream.init ≤ 144 := by decide +kernel
theorem updSd : sdepth Impl.Sha1.RISCV64.Stream.update ≤ 144 := by decide +kernel
theorem finSd : sdepth Impl.Sha1.RISCV64.Stream.finalize ≤ 144 := by decide +kernel

/-- What the proofs need of them. -/
def ok : HashOK hash where
  SH := Spec.Hmac.sha1S
  hS := rfl
  hD := rfl
  hB := rfl
  hb := .inl rfl
  hN := by decide
  hD0 := by decide
  hD64 := by decide
  hF := by decide
  init s hs := Proof.Sha1.RISCV64.Stream.init_verified.1 s hs
  upd s hs := Proof.Sha1.RISCV64.Stream.update_verified.1 s hs
  fin s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha1.RISCV64.Stream.finalize_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr _ hc => h m hr hc⟩
  initSd := initSd
  updSd := updSd
  finSd := finSd
  reloc m m' p q x hx h hr := Proof.Hmac.Stream.sha1_reloc m m' p q x hx h hr
  congr _ _ _ _ h hr := Proof.Hmac.sha1_local (fun i hi => h i hi) hr
  hashLen x := by simp [hash, Spec.Hmac.sha1S, Spec.Hmac.sha1, Spec.Sha1.hash, Spec.Sha1.wordBytes,
    List.length_flatMap, List.map_const']

/-! ## Constant time -/

theorem init_ct : ConstantTime isa (initG ok.SH (hash.ibytes + hash.F)).pre
    (initG ok.SH (hash.ibytes + hash.F)).pub hash.init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem fin_ct : ConstantTime isa (finG ok.SH (hash.fbytes + hash.F)).pre
    (finG ok.SH (hash.fbytes + hash.F)).pub hash.finalize :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

/-! ## The shared contracts -/

theorem init : Verified RISCV64.target hash.init
    (Spec.Hmac.sha1I.initAnyKeyContract RISCV64.abi (hash.ibytes + hash.F)) :=
  Shared.init ok rfl init_ct (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, Hash.ibytes, Hash.iso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.initSat 84)

theorem finalize : Verified RISCV64.target hash.finalize
    (Spec.Hmac.sha1I.finalizeContract RISCV64.abi (hash.fbytes + hash.F)) :=
  Shared.finalize ok rfl fin_ct (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, Hash.fbytes, Hash.fso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.finSat 84 20)

end VG.Proof.Hmac.Stream.RISCV64.Sha1
