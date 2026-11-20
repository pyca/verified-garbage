module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Sha256.PostOut
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
meta import VerifiedGarbage.Proof.Sha256.PostOut
public import VerifiedGarbage.Proof.Sha256.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Sha256.RISCV64.Fn
public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Sha256.RISCV64.Contract
public import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Impl.Sha256.RISCV64.Fn
meta import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Contract
meta import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `Sha256.RISCV64.Shared`, which only this module used -/

section

/-!
# SHA-256 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Sha256/RISCV64/Contract.lean`); these
theorems move them to the shared contracts of `Spec/Sha256/Contract.lean`,
which the artifacts are emitted with.

`update` and `finalize` keep their working space in a frame of their own,
of 144 bytes (`Impl.Sha256.RISCV64.Stream.frameBytes`), the `stack` of their
contracts. SHA-224 is SHA-256 from another initial hash value (`init224`),
with its digest the first 7 words of the final hash value (`finalize224`);
its `update` is SHA-256's.
-/

@[expose] public section

namespace VG.Proof.Sha256.RISCV64.Shared

open _root_.VG.RISCV64

theorem init :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.init (Spec.Sha256.initContract RISCV64.abi) :=
  Proof.Sha256.RISCV64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initFromRISCV64,
      Spec.Sha256.Repr, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.initSat] using Proof.Sha256.RISCV64.Stream.initSat)

theorem init224 :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.init224 (Spec.Sha256.init224Contract RISCV64.abi) :=
  Proof.Sha256.RISCV64.Stream.init224_verified.of_implies (by
    contract_implies [Spec.Sha256.init224Contract, Spec.Sha256.initSig, Proof.Sha256.initFromRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.initSat] using Proof.Sha256.RISCV64.Stream.initSat)

theorem update :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.update
      (Spec.Sha256.updateContract RISCV64.abi 144) :=
  Proof.Sha256.RISCV64.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Spec.Sha256.updatePost,
      Proof.Sha256.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.Update.sat] using Proof.Sha256.RISCV64.Stream.Update.sat)

/-- `finalizeNRISCV64 8`, writing all of the final hash value. -/
def finalize8 : Contract RISCV64.isa :=
  { Proof.Sha256.finalizeNRISCV64 8 with
    post := fun s s' => ∀ iv m, Spec.Sha256.ReprFrom iv s.mem (s.gpr .a0) m →
      s.gpr .a1 = BitVec.ofNat 64 m.length →
      Spec.Sha256.bytesAt s'.mem (s.gpr .a2) 32 = Spec.Sha256.finalHash iv m }

theorem finalize8_verified :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.finalize finalize8 :=
  Proof.Sha256.RISCV64.Stream.Finalize.finalize_verified.of_implies
    ⟨fun _ h => h, fun _ _ _ h iv m hr hc => by
      have := h iv m hr hc
      rwa [List.take_of_length_le (by rw [Proof.Sha256.RISCV64.Stream.Finalize.finalHash_length])]
        at this,
      fun _ _ _ _ h => h, Proof.Sha256.RISCV64.Stream.Finalize.finalize_verified.2.2⟩

theorem finalize :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.finalize
      (Spec.Sha256.finalizeContract RISCV64.abi 144) :=
  finalize8_verified.of_implies (by
    contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Spec.Sha256.finalizePost,
      finalize8, Proof.Sha256.finalizeNRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.Finalize.sat] using Proof.Sha256.RISCV64.Stream.Finalize.sat 8)

/-- `finalizeNRISCV64 7`, for SHA-224's digest of the messages hashed from
its initial hash value. -/
def finalize224R : Contract RISCV64.isa :=
  { Proof.Sha256.finalizeNRISCV64 7 with
    post := fun s s' => ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem (s.gpr .a0) m →
      s.gpr .a1 = BitVec.ofNat 64 m.length →
      Spec.Sha256.bytesAt s'.mem (s.gpr .a2) 28 = Spec.Sha256.sha224 m }

theorem finalize224R_verified :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.finalize224 finalize224R :=
  Proof.Sha256.RISCV64.Stream.Finalize.finalize224_verified.of_implies
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h _ m hr hc, fun _ _ _ _ h => h,
      Proof.Sha256.RISCV64.Stream.Finalize.finalize224_verified.2.2⟩

theorem finalize224 :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.finalize224
      (Spec.Sha256.finalize224Contract RISCV64.abi 144) :=
  finalize224R_verified.of_implies (by
    contract_implies [Spec.Sha256.finalize224Contract, Spec.Sha256.finalize224Sig,
      Spec.Sha256.finalize224Post, finalize224R, Proof.Sha256.finalizeNRISCV64, RISCV64.abi,
      RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.Finalize.sat] using Proof.Sha256.RISCV64.Stream.Finalize.sat 7)

end VG.Proof.Sha256.RISCV64.Shared

end

end

/-!
# SHA-224 and SHA-256 on RISC-V, without secret residue

Each of the streaming and one-shot functions as emitted
(`Impl.Sha256.RISCV64.Fn`): the function followed by
`Impl.Scrub.RISCV64.scrubTail`, which clears the caller-saved registers and
the stack its frames used. Each theorem below states that one meets its
contract in constant time and returns without secret residue
(`VerifiedScrubbed`, by `RISCV64.Scrub.verifiedScrubbed`), which is what its
registration binds. Their postconditions read the memory on return only
within their buffers (`Proof/Sha256/PostOut.lean`). HMAC, PBKDF2, DSA and
RSA call their code itself, not these functions.

The `digest` functions instead clear only the runs of doublewords that the
residue analysis (`RISCV64.rtaint`) finds may differ between two runs
(`RISCV64.Scrub.verifiedScrubbedSelT`, whose analysis the kernel evaluates
here). Their code wipes most of its own scratch space, which leaves few such
doublewords. Their correctness is HMAC's proof of the one-shot digest
(`Proof.Hmac.Stream.RISCV64.Sha256.digest`, `Sha224.digest`), of the same
code.
-/

@[expose] public section

namespace VG.Proof.Sha256.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

/-- `vg_sha256_init` as emitted (`Impl.Sha256.RISCV64.Fn.init`) meets its contract in constant
time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Sha256.RISCV64.Fn.init (Spec.Sha256.initContract RISCV64.abi) 0 :=
  verifiedScrubbed (api := Spec.Sha256.initApi) (W := 0)
    { code := Impl.Sha256.RISCV64.Stream.init, verified := Shared.init }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.initPost_out Spec.Sha256.H0 64))
    (show scrubSide Impl.Sha256.RISCV64.Stream.init 0 0 [] = true by lit_decide)

/-- `vg_sha224_init` as emitted (`Impl.Sha256.RISCV64.Fn.init224`) meets its contract in constant
time and returns without secret residue. -/
theorem init224_scrubbed :
    VerifiedScrubbed target Impl.Sha256.RISCV64.Fn.init224 (Spec.Sha256.init224Contract RISCV64.abi) 0 :=
  verifiedScrubbed (api := Spec.Sha256.init224Api) (W := 0)
    { code := Impl.Sha256.RISCV64.Stream.init224, verified := Shared.init224 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.initPost_out Spec.Sha256.H0_224 64))
    (show scrubSide Impl.Sha256.RISCV64.Stream.init224 0 0 [] = true by lit_decide)

/-- `vg_sha256_update` as emitted (`Impl.Sha256.RISCV64.Fn.update`) meets its contract in constant
time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed target Impl.Sha256.RISCV64.Fn.update (Spec.Sha256.updateContract RISCV64.abi 144) 0 :=
  verifiedScrubbed (api := Spec.Sha256.updateApi) (W := 144)
    { code := Impl.Sha256.RISCV64.Stream.update, verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out 64))
    (show scrubSide Impl.Sha256.RISCV64.Stream.update 144 0 [] = true by lit_decide)

/-- `vg_sha256_finalize` as emitted (`Impl.Sha256.RISCV64.Fn.finalize`) meets its contract in constant
time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed target Impl.Sha256.RISCV64.Fn.finalize (Spec.Sha256.finalizeContract RISCV64.abi 144) 0 :=
  verifiedScrubbed (api := Spec.Sha256.finalizeApi) (W := 144)
    { code := Impl.Sha256.RISCV64.Stream.finalize, verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out 64))
    (show scrubSide Impl.Sha256.RISCV64.Stream.finalize 144 0 [] = true by lit_decide)

/-- `vg_sha224_finalize` as emitted (`Impl.Sha256.RISCV64.Fn.finalize224`) meets its contract in constant
time and returns without secret residue. -/
theorem finalize224_scrubbed :
    VerifiedScrubbed target Impl.Sha256.RISCV64.Fn.finalize224 (Spec.Sha256.finalize224Contract RISCV64.abi 144) 0 :=
  verifiedScrubbed (api := Spec.Sha256.finalize224Api) (W := 144)
    { code := Impl.Sha256.RISCV64.Stream.finalize224, verified := Shared.finalize224 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out 64))
    (show scrubSide Impl.Sha256.RISCV64.Stream.finalize224 144 0 [] = true by lit_decide)

/-- `vg_sha256_digest` as emitted (`Impl.Sha256.RISCV64.Fn.digest`) meets its contract in constant
time and returns without secret residue. -/
theorem digest_scrubbed :
    VerifiedScrubbed target Impl.Sha256.RISCV64.Fn.digest (Spec.Sha256.digestContract RISCV64.abi 32 Spec.Sha256.hash 288) 0 :=
  verifiedScrubbedSelT (api := Spec.Sha256.digest256Api) (W := 288)
    { code := Impl.MdStream.RISCV64.Digest.digest Impl.Sha256.RISCV64.Fn.hash256,
      verified := Proof.Hmac.Stream.RISCV64.Sha256.digest }
    _ [] (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 64 (by decide)))
    (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_sha224_digest` as emitted (`Impl.Sha256.RISCV64.Fn.digest224`) meets its contract in constant
time and returns without secret residue. -/
theorem digest224_scrubbed :
    VerifiedScrubbed target Impl.Sha256.RISCV64.Fn.digest224 (Spec.Sha256.digestContract RISCV64.abi 28 Spec.Sha256.sha224 288) 0 :=
  verifiedScrubbedSelT (api := Spec.Sha256.digest224Api) (W := 288)
    { code := Impl.MdStream.RISCV64.Digest.digest Impl.Sha256.RISCV64.Fn.hash224,
      verified := Proof.Hmac.Stream.RISCV64.Sha224.digest }
    _ [] (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 64 (by decide)))
    (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

end VG.Proof.Sha256.RISCV64
