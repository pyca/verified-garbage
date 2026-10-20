module

import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFinCT
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInitCT
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.IterateCT
public import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
import VerifiedGarbage.Impl.Sha256.X86.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Md5.X86.Compress
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
import VerifiedGarbage.Proof.Pbkdf2.MdHmac
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Impl.Sha256.X86.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Md5.X86.Compress
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
meta import VerifiedGarbage.Proof.Pbkdf2.MdHmac
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha256.X86.Compress
meta import VerifiedGarbage.Proof.Sha512.Spec
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# HMAC-SHA-512/256's `init` and `finalize` and PBKDF2-HMAC-SHA-512/256's `iterate` on x86 (32-bit)

The generic proofs at SHA-512/256 (see `Instances.lean`): the taint checks of
their blocks, and their contracts moved to the shared ones (`sig_implies`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initW initG finW finG iterW iterG countF)

theorem sha512_256_iterChecks : Iterate.Checks sha512_256M := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_finChecks : HmacFin.Checks sha512_256M := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_iterImp : (iterW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 32 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 32 234

theorem sha512_256_finImp : (finW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 192 32 234
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 192 32 234

theorem sha512_256_iterate : Verified X86.target sha512_256M.iterate (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW sha512_256Ok sha512_256_iterChecks (by decide) sha512_256_iterImp.sat_left).of_implies sha512_256_iterImp

theorem sha512_256_finalize : Verified X86.target sha512_256M.hmacFin (Spec.Hmac.sha512_256I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW sha512_256Ok sha512_256_finChecks (by decide) sha512_256_finImp.sat_left).of_implies sha512_256_finImp

theorem sha512_256_initChecks : HmacInit.Checks sha512_256M := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_initImp : (initW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 234

theorem sha512_256_init : Verified X86.target sha512_256M.hmacInit (Spec.Hmac.sha512_256I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW sha512_256Ok sha512_256_initChecks (by decide) sha512_256_initImp.sat_left).of_implies sha512_256_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances
