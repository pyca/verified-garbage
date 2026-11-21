module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
meta import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512Family
public import VerifiedGarbage.Proof.Hmac.Contract
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512Family
import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest

/-!
# HMAC-SHA-512/256 on PPC64LE

SHA-512/256's streaming functions (`sha512FamilyHash`), as HMAC's code over any
streaming hash function calls them; the constant time of HMAC's code for
them, which the kernel checks; and the functions against the shared contracts
of `Spec.Hmac.sha512_256I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Sha512_256

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash sha512_256Hash hmacFrame longFrame initCode)

/-- What the proofs need of them. -/
def ok : HashOK sha512_256Hash :=
  Sha512Family.ok Spec.Sha512.H0_512_256 32 _ _ Spec.Hmac.sha512_256 rfl ⟨by decide, by decide, by decide⟩
    (fun _ => rfl)

/-! ## Constant time -/

theorem init_ct : ConstantTime isa (initG ok.SH (sha512_256Hash.W + 48) 96).pre (initG ok.SH (sha512_256Hash.W + 48) 96).pub
    sha512_256Hash.init :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem fin_ct : ConstantTime isa (finG ok.SH (sha512_256Hash.W + 48 + sha512_256Hash.FD) 96).pre
    (finG ok.SH (sha512_256Hash.W + 48 + sha512_256Hash.FD) 96).pub sha512_256Hash.finalize :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem long_ct : ConstantTime isa (longG ok.SH sha512_256Hash.lbytes 144).pre (longG ok.SH sha512_256Hash.lbytes 144).pub
    sha512_256Hash.initLong :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

/-! ## The shared contracts -/

theorem initScratch : Verified PPC64LE.target sha512_256Hash.init (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha512_256I PPC64LE.abi 96) :=
  Shared.initScratch ok rfl (by decide) init_ct (by
    inst_sat [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
      Spec.Hmac.initPre, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, PPC64LE.abi, PPC64LE.argRegs]
      using initSat 192 1872)

theorem finalizeScratch :
    Verified PPC64LE.target sha512_256Hash.finalize (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha512_256I PPC64LE.abi 96) :=
  Shared.finalizeScratch ok rfl (by decide) fin_ct (by
    inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
      Proof.Hmac.finalizeScratchSig, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, PPC64LE.abi,
      PPC64LE.argRegs]
      using finSat 192 32 1872)

theorem longScratch : Verified PPC64LE.target sha512_256Hash.initLong (Shared.longScratchContract ok.SH (sha512_256Hash.lbytes / 8)) :=
  Shared.longScratch ok (by decide) long_ct (by
    inst_sat [Shared.longScratchContract, Shared.longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256,
      PPC64LE.abi, PPC64LE.argRegs]
      using longSat 192 576)

theorem initAny : Verified PPC64LE.target (initCode sha512_256Hash Spec.Hmac.sha512_256I 7)
    (Spec.Hmac.sha512_256I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha512_256I)) :=
  Shared.initAny (b := 7) (.inr rfl) rfl (by decide)
    (Shared.initFrame initScratch (by decide) Proof.Hmac.sha512_256_local (by decide) (by
      inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 192 0))
    (Shared.longFrame longScratch (by decide) Proof.Hmac.sha512_256_local (by decide) (by
      inst_sat [Shared.longContract, Shared.longPre, Spec.Hmac.initSig, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S,
        Spec.Hmac.sha512_256, longFrame, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using longSat 192 0))
    (by
      inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 192 0)

theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha512_256I) .r7 sha512_256Hash.finalize)
    (Spec.Hmac.sha512_256I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha512_256I)) :=
  Shared.finalizeFrame finalizeScratch (by decide) Proof.Hmac.sha512_256_local (by decide) (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using finSat 192 32 0)


/-! ## The one-shot digest

The one-shot digest over any streaming hash function
(`Impl/MdStream/PPC64LE/Digest.lean`) for these streaming functions: its
constant time, which the kernel checks, and its contract. -/

theorem digest_ct : ConstantTime isa (MdStream.PPC64LE.Digest.digestG ok.SH sha512_256Hash.lbytes 96).pre
    (MdStream.PPC64LE.Digest.digestG ok.SH sha512_256Hash.lbytes 96).pub (Impl.MdStream.PPC64LE.Digest.digest sha512_256Hash) :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => MdStream.PPC64LE.Digest.agree hp) (by taint_decide)

theorem digestScratch :
    Verified PPC64LE.target (Impl.MdStream.PPC64LE.Digest.digest sha512_256Hash) (MdStream.PPC64LE.Digest.digestScratchContract ok.SH (sha512_256Hash.lbytes / 8)) :=
  MdStream.PPC64LE.Digest.digestScratch ok (by decide) digest_ct (by
    inst_sat [MdStream.PPC64LE.Digest.digestScratchContract, MdStream.PPC64LE.Digest.digestScratchSig, Spec.Sha256.digestPost,
      Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, PPC64LE.abi, PPC64LE.argRegs]
      using MdStream.PPC64LE.Digest.digestSat 32 sha512_256Hash.lbytes)

theorem digest : Verified PPC64LE.target (Impl.MdStream.PPC64LE.Digest.code sha512_256Hash) (Spec.Sha512.digestContract PPC64LE.abi 32 Spec.Sha512.sha512_256 (96 + Impl.MdStream.PPC64LE.Digest.frameBytes sha512_256Hash)) :=
  MdStream.PPC64LE.Digest.digestFrame (SH := ok.SH) (bytes := Impl.MdStream.PPC64LE.Digest.frameBytes sha512_256Hash)
    digestScratch (by decide) (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha512_256S,
      Spec.Hmac.sha512_256, PPC64LE.abi, PPC64LE.argRegs]
      using MdStream.PPC64LE.Digest.digestSat 32 0)

end VG.Proof.Hmac.Stream.PPC64LE.Sha512_256
