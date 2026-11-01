module

import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512Family
public import VerifiedGarbage.Proof.Hmac.Contract
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512Family
import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Shared
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-!
# HMAC-SHA-384 on PPC64LE

SHA-384's streaming functions (`Sha512Family.hash`), as HMAC's code over any
streaming hash function calls them; the constant time of HMAC's code for
them, which the kernel checks; and the functions against the shared contracts
of `Spec.Hmac.sha384I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Sha384

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

/-- SHA-384's streaming functions. -/
def hash : Hash :=
  Sha512Family.hash Spec.Sha512.H0_384 48 Spec.Sha512.init384Api.name "vg_hmac_sha384_init_scratch"

/-- What the proofs need of them. -/
def ok : HashOK hash :=
  Sha512Family.ok Spec.Sha512.H0_384 48 _ _ Spec.Hmac.sha384 rfl ⟨by decide, by decide, by decide⟩
    (fun _ => rfl)

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

theorem initScratch : Verified PPC64LE.target hash.init (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha384I PPC64LE.abi 96) :=
  Shared.initScratch ok rfl (by decide) init_ct (by
    inst_sat [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
      Spec.Hmac.initPre, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, PPC64LE.abi, PPC64LE.argRegs]
      using initSat 192 1872)

theorem finalizeScratch :
    Verified PPC64LE.target hash.finalize (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha384I PPC64LE.abi 96) :=
  Shared.finalizeScratch ok rfl (by decide) fin_ct (by
    inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
      Proof.Hmac.finalizeScratchSig, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, PPC64LE.abi,
      PPC64LE.argRegs]
      using finSat 192 48 1872)

theorem longScratch : Verified PPC64LE.target hash.initLong (Shared.longScratchContract ok.SH (hash.lbytes / 8)) :=
  Shared.longScratch ok (by decide) long_ct (by
    inst_sat [Shared.longScratchContract, Shared.longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha384S, Spec.Hmac.sha384,
      PPC64LE.abi, PPC64LE.argRegs]
      using longSat 192 576)

theorem initAny : Verified PPC64LE.target (initCode hash Spec.Hmac.sha384I 7)
    (Spec.Hmac.sha384I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha384I)) :=
  Shared.initAny (b := 7) (.inr rfl) rfl (by decide)
    (Shared.initFrame initScratch (by decide) (by
      inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 192 0))
    (Shared.longFrame longScratch (by decide) Proof.Hmac.sha384_local (by decide) (by
      inst_sat [Shared.longContract, Shared.longPre, Spec.Hmac.initSig, Spec.Hmac.sha384I, Spec.Hmac.sha384S,
        Spec.Hmac.sha384, longFrame, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using longSat 192 0))
    (by
      inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 192 0)

theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha384I) .r7 hash.finalize)
    (Spec.Hmac.sha384I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha384I)) :=
  Shared.finalizeFrame finalizeScratch (by decide) Proof.Hmac.sha384_local (by decide) (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using finSat 192 48 0)

end VG.Proof.Hmac.Stream.PPC64LE.Sha384
