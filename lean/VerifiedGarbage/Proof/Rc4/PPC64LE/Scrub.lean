module

public import VerifiedGarbage.Impl.Rc4.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc4.PPC64LE.Verified
public import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RC4 on PPC64LE, without secret residue

`vg_rc4_init` and `vg_rc4_apply`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the
volatile registers they write, the vector registers of their lookups and
replacements among them. They use no stack, so none is wiped. Their
postconditions read the memory on return only within their buffers, by the
target-independent lemmas RISC-V's proofs use (`Proof/Rc4/Scratch.lean`,
`Proof/Rc4/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE.Scrub

open VG.Spec.Rc4 VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem initOut (stack : Nat) : PostOut (Spec.Rc4.initContract PPC64LE.abi stack) (Spec.Rc4.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc4.initPostOut_local _)

theorem applyOut (stack : Nat) : PostOut (Spec.Rc4.applyContract PPC64LE.abi stack) (Spec.Rc4.applySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain (Proof.Rc4.applyPostOut_local _)

/-! ## The functions as emitted -/

/-- `vg_rc4_init` as emitted (`Impl.Rc4.PPC64LE.Fn.init`) meets its contract in
constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Rc4.PPC64LE.Fn.init
      (Spec.Rc4.initContract PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Rc4.initApi) { code := Impl.Rc4.PPC64LE.init, verified := Proof.Rc4.PPC64LE.init_verified }
    0 ⟨true, true, [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (initOut _)
    (by dsimp only; lit_decide)

/-- `vg_rc4_apply` as emitted (`Impl.Rc4.PPC64LE.Fn.apply`) meets its contract in
constant time and returns without secret residue. -/
theorem apply_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Rc4.PPC64LE.Fn.apply
      (Spec.Rc4.applyContract PPC64LE.abi) 0 :=
  verifiedScrubbedAll (api := Spec.Rc4.applyApi) { code := Impl.Rc4.PPC64LE.apply, verified := Proof.Rc4.PPC64LE.apply_verified }
    0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (applyOut _)
    (by dsimp only; lit_decide)

end VG.Proof.Rc4.PPC64LE.Scrub
