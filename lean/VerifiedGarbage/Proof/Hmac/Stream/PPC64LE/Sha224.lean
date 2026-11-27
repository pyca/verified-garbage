module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
meta import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Finalize
public import VerifiedGarbage.Proof.Sha256.Scratch
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.Reloc
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Init
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Finalize
meta import VerifiedGarbage.Proof.Sha256.Scratch
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.Proof.Hmac.Stream.Reloc
import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Hmac.Scratch
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest

/-!
# HMAC-SHA-224 on PPC64LE

SHA-224's streaming functions as HMAC's code over any streaming hash function
calls them (`sha224Hash`,
in `Impl/Hmac/Stream/PPC64LE/Fn.lean`): SHA-224's `init`, and SHA-256's `update` and `finalize`,
which writes the whole final hash value (32 bytes), whose first 28 bytes are
the digest; what the proofs need of them (`ok`); the constant time of HMAC's
code for them, which the kernel checks; and the functions against the shared
contracts of `Spec.Hmac.sha224I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Sha224

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash sha224Hash hmacFrame longFrame initCode)

/-- What the proofs need of them. -/
def ok : HashOK sha224Hash where
  SH := Spec.Hmac.sha224S
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
  fh := Spec.Sha256.finalHash Spec.Sha256.H0_224
  init s hs := Proof.Sha256.PPC64LE.Stream.init224_verified.1 s ⟨hs.1, hs.2.1⟩
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
  hashTake _ := rfl

/-! ## Constant time -/

theorem init_ct : ConstantTime isa (initG ok.SH (sha224Hash.W + 48) 96).pre (initG ok.SH (sha224Hash.W + 48) 96).pub
    sha224Hash.init :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem fin_ct : ConstantTime isa (finG ok.SH (sha224Hash.W + 48 + sha224Hash.FD) 96).pre
    (finG ok.SH (sha224Hash.W + 48 + sha224Hash.FD) 96).pub sha224Hash.finalize :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem long_ct : ConstantTime isa (longG ok.SH sha224Hash.lbytes 144).pre (longG ok.SH sha224Hash.lbytes 144).pub
    sha224Hash.initLong :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

/-! ## The shared contracts -/

theorem initScratch : Verified PPC64LE.target sha224Hash.init (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha224I PPC64LE.abi 96) :=
  Shared.initScratch ok rfl (by decide) init_ct (by
    inst_sat [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
      Spec.Hmac.initPre, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, PPC64LE.abi, PPC64LE.argRegs]
      using initSat 96 832)

theorem finalizeScratch :
    Verified PPC64LE.target sha224Hash.finalize (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha224I PPC64LE.abi 96) :=
  Shared.finalizeScratch ok rfl (by decide) fin_ct (by
    inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
      Proof.Hmac.finalizeScratchSig, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, PPC64LE.abi,
      PPC64LE.argRegs]
      using finSat 96 28 832)

theorem longScratch : Verified PPC64LE.target sha224Hash.initLong (Shared.longScratchContract ok.SH (sha224Hash.lbytes / 8)) :=
  Shared.longScratch ok (by decide) long_ct (by
    inst_sat [Shared.longScratchContract, Shared.longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha224S, Spec.Hmac.sha224,
      PPC64LE.abi, PPC64LE.argRegs]
      using longSat 96 384)

theorem initAny : Verified PPC64LE.target (initCode sha224Hash Spec.Hmac.sha224I 6)
    (Spec.Hmac.sha224I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha224I)) :=
  Shared.initAny (b := 6) (.inl rfl) rfl (by decide)
    (Shared.initFrame initScratch (by decide) Proof.Hmac.sha224_local (by decide) (by
      inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 96 0))
    (Shared.longFrame longScratch (by decide) Proof.Hmac.sha224_local (by decide) (by
      inst_sat [Shared.longContract, Shared.longPre, Spec.Hmac.initSig, Spec.Hmac.sha224I, Spec.Hmac.sha224S,
        Spec.Hmac.sha224, longFrame, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using longSat 96 0))
    (by
      inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 96 0)

theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha224I) .r7 sha224Hash.finalize)
    (Spec.Hmac.sha224I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha224I)) :=
  Shared.finalizeFrame finalizeScratch (by decide) Proof.Hmac.sha224_local (by decide) (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using finSat 96 28 0)


/-! ## The one-shot digest

The one-shot digest over any streaming hash function
(`Impl/MdStream/PPC64LE/Digest.lean`) for these streaming functions: its
constant time, which the kernel checks, and its contract. -/

theorem digest_ct : ConstantTime isa (MdStream.PPC64LE.Digest.digestG ok.SH sha224Hash.lbytes 96).pre
    (MdStream.PPC64LE.Digest.digestG ok.SH sha224Hash.lbytes 96).pub (Impl.MdStream.PPC64LE.Digest.digest sha224Hash) :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => MdStream.PPC64LE.Digest.agree hp) (by taint_decide)

theorem digestScratch :
    Verified PPC64LE.target (Impl.MdStream.PPC64LE.Digest.digest sha224Hash) (MdStream.PPC64LE.Digest.digestScratchContract ok.SH (sha224Hash.lbytes / 8)) :=
  MdStream.PPC64LE.Digest.digestScratch ok (by decide) digest_ct (by
    inst_sat [MdStream.PPC64LE.Digest.digestScratchContract, MdStream.PPC64LE.Digest.digestScratchSig, Spec.Sha256.digestPost,
      Spec.Hmac.sha224S, Spec.Hmac.sha224, PPC64LE.abi, PPC64LE.argRegs]
      using MdStream.PPC64LE.Digest.digestSat 28 sha224Hash.lbytes)

theorem digest : Verified PPC64LE.target (Impl.MdStream.PPC64LE.Digest.code sha224Hash) (Spec.Sha256.digestContract PPC64LE.abi 28 Spec.Sha256.sha224 (96 + Impl.MdStream.PPC64LE.Digest.frameBytes sha224Hash)) :=
  MdStream.PPC64LE.Digest.digestFrame (SH := ok.SH) (bytes := Impl.MdStream.PPC64LE.Digest.frameBytes sha224Hash)
    digestScratch (by decide) (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha224S,
      Spec.Hmac.sha224, PPC64LE.abi, PPC64LE.argRegs]
      using MdStream.PPC64LE.Digest.digestSat 28 0)

end VG.Proof.Hmac.Stream.PPC64LE.Sha224
