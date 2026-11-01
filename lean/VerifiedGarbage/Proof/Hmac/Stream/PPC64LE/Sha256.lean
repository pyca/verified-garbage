module

import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Update
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Finalize
public import VerifiedGarbage.Proof.Sha256.Scratch
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.Reloc
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Init
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Update
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Finalize
meta import VerifiedGarbage.Proof.Sha256.Scratch
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.Proof.Hmac.Stream.Reloc
import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Shared

/-!
# HMAC-SHA-256 on PPC64LE

SHA-256's streaming functions as HMAC's code over any streaming hash function
calls them (`hash`); what the proofs need of them (`ok`); the constant time
of HMAC's code for them, which the kernel checks; and the functions against
the shared contracts of `Spec.Hmac.sha256I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Sha256

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

/-- SHA-256's streaming functions. -/
def hash : Hash where
  B := 64
  N := 32
  D := 32
  FD := 32
  W := 160
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.PPC64LE.Stream.init
  updN := "vg_sha256_update_scratch"
  updC := Impl.Sha256.PPC64LE.Stream.update
  finN := "vg_sha256_finalize_scratch"
  finC := Impl.Sha256.PPC64LE.Stream.finalize
  hmacInitN := "vg_hmac_sha256_init_scratch"

/-- What the proofs need of them. -/
def ok : HashOK hash where
  SH := Spec.Hmac.sha256S
  hS := rfl
  hD := rfl
  hB := rfl
  dims := ⟨by decide, by decide, by decide, by decide⟩
  hN4 := by decide
  hD0 := by decide
  hDB := by decide
  hD4 := by decide
  hDF := by decide
  hFD64 := by decide
  fh := Spec.Sha256.finalHash Spec.Sha256.H0
  init s hs := Proof.Sha256.PPC64LE.Stream.init_verified.1 s ⟨hs.1, hs.2.1⟩
  upd s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha256.PPC64LE.Stream.Update.update_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr hc => h _ m hr hc⟩
  fin s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha256.PPC64LE.Stream.Finalize.finalize_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr _ hc => h _ m hr hc⟩
  initFd := by decide +kernel
  updFd := by decide +kernel
  finFd := by decide +kernel
  initPf := by decide +kernel
  updPf := by decide +kernel
  finPf := by decide +kernel
  reloc m m' p q x hx h hr := Proof.Hmac.Stream.sha256_reloc _ m m' p q x hx h hr
  congr _ _ _ _ h hr := Proof.Sha256.reprFrom_congr (fun i hi => h i hi) hr
  fhLen x := Proof.Sha256.PPC64LE.Stream.Finalize.finalHash_length _ x
  hashTake x := (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.PPC64LE.Stream.Finalize.finalHash_length _ x))).symm

/-! ## Constant time -/

theorem init_ct : ConstantTime isa (initG ok.SH (hash.W + 48) 96).pre (initG ok.SH (hash.W + 48) 96).pub
    hash.init :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem fin_ct : ConstantTime isa (finG ok.SH (hash.W + 48 + hash.FD) 96).pre
    (finG ok.SH (hash.W + 48 + hash.FD) 96).pub hash.finalize :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem long_ct : ConstantTime isa (longG ok.SH hash.lbytes 144).pre (longG ok.SH hash.lbytes 144).pub
    hash.initLong :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

/-! ## The shared contracts -/

theorem initScratch : Verified PPC64LE.target hash.init (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha256I PPC64LE.abi 96) :=
  Shared.initScratch ok rfl (by decide) init_ct (by
    inst_sat [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
      Spec.Hmac.initPre, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi, PPC64LE.argRegs]
      using initSat 96 832)

theorem finalizeScratch :
    Verified PPC64LE.target hash.finalize (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha256I PPC64LE.abi 96) :=
  Shared.finalizeScratch ok rfl (by decide) fin_ct (by
    inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
      Proof.Hmac.finalizeScratchSig, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
      PPC64LE.argRegs]
      using finSat 96 32 832)

theorem longScratch : Verified PPC64LE.target hash.initLong (Shared.longScratchContract ok.SH (hash.lbytes / 8)) :=
  Shared.longScratch ok (by decide) long_ct (by
    inst_sat [Shared.longScratchContract, Shared.longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha256S, Spec.Hmac.sha256,
      PPC64LE.abi, PPC64LE.argRegs]
      using longSat 96 384)

theorem initAny : Verified PPC64LE.target (initCode hash Spec.Hmac.sha256I 6)
    (Spec.Hmac.sha256I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha256I)) :=
  Shared.initAny (b := 6) (.inl rfl) rfl (by decide)
    (Shared.initFrame initScratch (by decide) (by
      inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 96 0))
    (Shared.longFrame longScratch (by decide) Proof.Hmac.sha256_local (by decide) (by
      inst_sat [Shared.longContract, Shared.longPre, Spec.Hmac.initSig, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
        Spec.Hmac.sha256, longFrame, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using longSat 96 0))
    (by
      inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 96 0)

theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha256I) .r7 hash.finalize)
    (Spec.Hmac.sha256I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha256I)) :=
  Shared.finalizeFrame finalizeScratch (by decide) Proof.Hmac.sha256_local (by decide) (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using finSat 96 32 0)

end VG.Proof.Hmac.Stream.PPC64LE.Sha256
