module

public import VerifiedGarbage.Proof.Sha3.X86.Instances
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Impl.Sha3.X86.Instances
import VerifiedGarbage.Proof.Sha3.PostOut
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Sha3.X86.Instances
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Impl.Sha3.X86.Instances
meta import VerifiedGarbage.Proof.Sha3.PostOut
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# SHA-3's `finalize` and SHAKE's `finalize` and `squeeze` on x86 (32-bit), without secret residue

Each keeps the sponge's working space in a frame of its own and calls the
sponge's padding or squeezing (`Impl.Sha3.X86.Instances`). The code as
emitted (`Impl.Sha3.X86.Fn`) then zeroes the stack it and its callee use and
clears the registers a callee may change, and returns without secret residue
(`X86.Scrub.verifiedScrubbedAll`), given that its postcondition reads
the memory on return only within the buffers (`Proof.Sha3.PostOut`, and
`xofSqueezeOut` for SHAKE's `squeeze`, whose `outlen` is a 32-bit word here).
-/

@[expose] public section

namespace VG.Proof.Sha3.X86.Scrub

open VG.Spec.Sha3 VG.X86 VG.X86.Scrub
open VG.Proof.Sha3.PostOut (agreeBuf bytesAt_congr stateAgree)

theorem finalizeOut (H : HashFn) (hlen : H.len < 2 ^ 64) (stack : Nat) :
    PostOut (finalizeContract X86.abi H stack) ((finalizeSig H.len).retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha3.PostOut.finalizePost_out H 32 hlen)

theorem xofFinalizeOut (X : Xof) (stack : Nat) :
    PostOut (xofFinalizeContract X86.abi X stack) (xofFinalizeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha3.PostOut.xofFinalizePost_out X 32)

/-- `xofSqueezePost` reads only the state and `out`, with 32-bit pointers
(`Proof.Sha3.PostOut.xofSqueezePost_out` at 64). -/
theorem xofSqueezePost_out32 (X : Xof) : ∀ vs m m₁ m₂ r, vs.length = (xofSqueezeSig.words 32).length →
    (∀ b ∈ Sig.bufs xofSqueezeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (xofSqueezeSig.words 32) (xofSqueezePost X 32) vs m m₁ r →
      Curry.apply (xofSqueezeSig.words 32) (xofSqueezePost X 32) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ol, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [xofSqueezeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hb
  refine ⟨fun msg n hx => ?_, h.2⟩
  obtain ⟨h1, h2⟩ := h.1 msg n hx
  refine ⟨?_, fun d => ?_⟩
  · show bytesAt m₂ ot (ol.setWidth 32).toNat = _
    have hw : (ol.setWidth 32).toNat ≤ ol.toNat := by
      rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _
    rw [bytesAt_congr fun i hi => agreeBuf (n := ol.toNat * Elem.size .u8)
      (by simp only [Elem.size]; have := ol.isLt; omega_using []) hb.2 i
      (by simp only [Elem.size]; omega_using [hi, hw])]
    exact h1
  · show squeezeFrom X.rate (stateAt m₂ st) _ d = _
    rw [stateAgree hb.1]
    exact h2 d

theorem xofSqueezeOut (X : Xof) (stack : Nat) :
    PostOut (xofSqueezeContract X86.abi X stack) (xofSqueezeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (xofSqueezePost_out32 X)

/-- `vg_sha3_224_finalize` as emitted (`Impl.Sha3.X86.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_224_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.finalize hashSha3_224.rate hashSha3_224.len)
      (finalizeContract X86.abi hashSha3_224 680) 0 :=
  verifiedScrubbedAll (api := finalizeSha3_224Api)
    { code := Impl.Sha3.X86.Instances.finalize hashSha3_224.rate hashSha3_224.len
      stack := 680
      verified := Proof.Sha3.X86.Instances.finalize_sha3_224 }
    (finalizeOut _ (by decide) _)

/-- `vg_sha3_256_finalize` as emitted (`Impl.Sha3.X86.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_256_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.finalize hashSha3_256.rate hashSha3_256.len)
      (finalizeContract X86.abi hashSha3_256 680) 0 :=
  verifiedScrubbedAll (api := finalizeSha3_256Api)
    { code := Impl.Sha3.X86.Instances.finalize hashSha3_256.rate hashSha3_256.len
      stack := 680
      verified := Proof.Sha3.X86.Instances.finalize_sha3_256 }
    (finalizeOut _ (by decide) _)

/-- `vg_sha3_384_finalize` as emitted (`Impl.Sha3.X86.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_384_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.finalize hashSha3_384.rate hashSha3_384.len)
      (finalizeContract X86.abi hashSha3_384 680) 0 :=
  verifiedScrubbedAll (api := finalizeSha3_384Api)
    { code := Impl.Sha3.X86.Instances.finalize hashSha3_384.rate hashSha3_384.len
      stack := 680
      verified := Proof.Sha3.X86.Instances.finalize_sha3_384 }
    (finalizeOut _ (by decide) _)

/-- `vg_sha3_512_finalize` as emitted (`Impl.Sha3.X86.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_512_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.finalize hashSha3_512.rate hashSha3_512.len)
      (finalizeContract X86.abi hashSha3_512 680) 0 :=
  verifiedScrubbedAll (api := finalizeSha3_512Api)
    { code := Impl.Sha3.X86.Instances.finalize hashSha3_512.rate hashSha3_512.len
      stack := 680
      verified := Proof.Sha3.X86.Instances.finalize_sha3_512 }
    (finalizeOut _ (by decide) _)

/-- `vg_shake128_finalize` as emitted (`Impl.Sha3.X86.Fn.xofFinalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_shake128_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.xofFinalize xofShake128.rate)
      (xofFinalizeContract X86.abi xofShake128 676) 0 :=
  verifiedScrubbedAll (api := finalizeShake128Api)
    { code := Impl.Sha3.X86.Instances.xofFinalize xofShake128.rate
      stack := 676
      verified := Proof.Sha3.X86.Instances.finalize_shake128 }
    (xofFinalizeOut _ _)

/-- `vg_shake256_finalize` as emitted (`Impl.Sha3.X86.Fn.xofFinalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_shake256_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.xofFinalize xofShake256.rate)
      (xofFinalizeContract X86.abi xofShake256 676) 0 :=
  verifiedScrubbedAll (api := finalizeShake256Api)
    { code := Impl.Sha3.X86.Instances.xofFinalize xofShake256.rate
      stack := 676
      verified := Proof.Sha3.X86.Instances.finalize_shake256 }
    (xofFinalizeOut _ _)

/-- `vg_shake128_squeeze` as emitted (`Impl.Sha3.X86.Fn.xofSqueeze`) meets its contract in
constant time and returns without secret residue. -/
theorem squeeze_shake128_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.xofSqueeze xofShake128.rate)
      (xofSqueezeContract X86.abi xofShake128 680) 32 :=
  verifiedScrubbedAll (api := squeezeShake128Api)
    { code := Impl.Sha3.X86.Instances.xofSqueeze xofShake128.rate
      stack := 680
      verified := Proof.Sha3.X86.Instances.squeeze_shake128 }
    (xofSqueezeOut _ _)

/-- `vg_shake256_squeeze` as emitted (`Impl.Sha3.X86.Fn.xofSqueeze`) meets its contract in
constant time and returns without secret residue. -/
theorem squeeze_shake256_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.xofSqueeze xofShake256.rate)
      (xofSqueezeContract X86.abi xofShake256 680) 32 :=
  verifiedScrubbedAll (api := squeezeShake256Api)
    { code := Impl.Sha3.X86.Instances.xofSqueeze xofShake256.rate
      stack := 680
      verified := Proof.Sha3.X86.Instances.squeeze_shake256 }
    (xofSqueezeOut _ _)

end VG.Proof.Sha3.X86.Scrub
