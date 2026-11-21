module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Scrypt.X86.Whole.Verified
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Scrub
public import VerifiedGarbage.Impl.Scrypt.X86.Fn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Scrypt.X86.Whole.Verified
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Scrub
meta import VerifiedGarbage.Impl.Scrypt.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Lit

/-!
# scrypt on x86 (32-bit), without secret residue

`vg_scrypt` runs in a frame of nine words and calls PBKDF2-HMAC-SHA256 and
ROMix below it, within the 116 bytes of stack its contract reserves. The
code as emitted (`Impl.Scrypt.X86.Fn.scrypt`) then zeroes those bytes below
`esp` and clears the registers a callee may change, and returns without
secret residue (`X86.Scrub.verifiedScrubbedAll`), given that its postcondition
reads the memory on return only within `out` (`scryptOut`, as on ARMv7,
`Proof/Scrypt/Arm/Scrub.lean`).

It is generic over the SHA-256 backend of the PBKDF2 it calls
(`Proof/Variants/Sha256/X86.lean`): its code with PBKDF2's stub backend,
whose compression, `update` and `finalize` are `.block []`
(`Proof.Pbkdf2.Whole.X86.Scrub.sha256Stub`), is evaluated once
(`scrypt_side`), and `Fill` gives the same of every backend from its own
facts (`Backend.cmpScrub`, `updScrub`, `finScrub` and its stacks), with no
evaluation of its code (`Proof/Framework/X86/ScrubCall.lean`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.X86.Scrub

open VG VG.X86 VG.X86.Scrub
open VG.Proof.Scrypt.X86.Whole (pbkName pbkOf scrypt_verified scrypt_spSafe)
open VG.Proof.Pbkdf2.Whole.X86.Scrub (sha256Stub)

/-! ## The postcondition -/

/-- The `n` bytes at `o` read the memory only within `⟨o, N⟩`, `n ≤ N`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n ≤ N) (hn : n < 2 ^ 64) :
    Spec.Scrypt.bytesAt m₂ o n = Spec.Scrypt.bytesAt m₁ o n := by
  unfold Spec.Scrypt.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [this, hN]) (by omega_using [this, hn]))).symm

theorem scryptOut (stack : Nat) :
    PostOut (Spec.Scrypt.scryptContract X86.abi stack) (Spec.Scrypt.scryptSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (sig := Spec.Scrypt.scryptSig) fun
    | [_, _, _, _, _, _, _, _, _, _, _, out, outLen], m, m₁, m₂, ret, _, hb, h => by
      simp only [Spec.Scrypt.scryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ ret at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ ret
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have hle : (outLen.setWidth X86.abi.ptrBits).toNat ≤ outLen.toNat * 1 := by
        rw [BitVec.toNat_setWidth, Nat.mul_one]; exact Nat.mod_le _ _
      rw [bytesAt_of hb.2.2.2.2.2 hle (by have := outLen.isLt; omega)]
      exact h

/-! ## The cleanup's side condition, whatever the backend -/

materialize_code scryptStubLit := Impl.Scrypt.X86.scrypt "" sha256Stub.pbkdf2

theorem scrypt_side : scrubFSide (Impl.Scrypt.X86.scrypt "" sha256Stub.pbkdf2) [] 96 = true := by
  lit_decide

theorem scrypt_fill (name sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (Impl.Scrypt.X86.scrypt "" sha256Stub.pbkdf2)
      (Impl.Scrypt.X86.scrypt name (Proof.Sha256.X86.Variants.fns sfx cN c u f).pbkdf2) := by
  fill_calls

/-- `scrubFSide` of `vg_scrypt`, whatever the backend. -/
theorem scrypt_scrub (v : Proof.Sha256.X86.Variants.Backend) :
    scrubFSide (Impl.Scrypt.X86.scrypt (pbkName v) (pbkOf v)) [] 116 = true :=
  scrubFSide_of_fill (scrypt_fill _ _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
    (calleeSide_of_le v.stream.updSU v.updScrub) (calleeSide_of_le v.stream.finSU v.finScrub)) scrypt_side

/-! ## The function as emitted -/

/-- `vg_scrypt` with the backend `v`, as emitted (`Impl.Scrypt.X86.Fn.scrypt`),
meets its contract in constant time and returns without secret residue. -/
theorem scrypt_scrubbed (v : Proof.Sha256.X86.Variants.Backend) :
    VerifiedScrubbed target (Impl.Scrypt.X86.Fn.scrypt (pbkName v) (pbkOf v))
      (Spec.Scrypt.scryptContract X86.abi 116) 0 :=
  verifiedScrubbedAll (api := Spec.Scrypt.scryptApi)
    { suffix := v.suffix
      code := Impl.Scrypt.X86.scrypt (pbkName v) (pbkOf v)
      verified := scrypt_verified v
      spSafe := scrypt_spSafe v }
    (scryptOut _) (hs := scrypt_scrub v)

end VG.Proof.Scrypt.X86.Scrub
