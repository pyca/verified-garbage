module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Scratch
public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64.Fn
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
meta import VerifiedGarbage.Proof.Hmac.AnyKey
meta import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Impl.Hmac.Stream.RISCV64.Fn
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# HMAC on RISC-V, without secret residue

Each hash's HMAC `init` and `finalize` as emitted
(`Impl.Hmac.Stream.RISCV64.Fn`): `finalize` followed by
`Impl.Scrub.RISCV64.scrubTail`, which clears the caller-saved registers and
the stack its frames used (`RISCV64.Scrub.verifiedScrubbed`); `init`
followed by `Impl.Scrub.RISCV64.scrubTailSel`, which clears only the runs of
doublewords that the residue analysis (`RISCV64.rtaint`) finds may differ
between two runs (`RISCV64.Scrub.verifiedScrubbedSelT`, whose analysis the
kernel evaluates here): its code wipes most of its own scratch space, which
leaves few such doublewords. Each theorem below states that one meets its
contract in constant time and returns without secret residue
(`VerifiedScrubbed`), which is what its registration binds. Their
postconditions read the memory on return only within their buffers, as on
x86-64 (`Proof/Pbkdf2/Md/X86_64/ScrubStream.lean`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

theorem hmacInitAnyOut (I : Spec.Hmac.Instance) (hR : Proof.Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (stack : Nat) : PostOut (I.initAnyKeyContract abi stack) ((Spec.Hmac.initSig I.S).retBits 64) := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Hmac.initPostOut_local I.S _ hR hS)

/-- HMAC's `finalize`'s postcondition reads the memory on return only within
`out`, the HMAC's bytes. -/
theorem hmacFinOut (I : Spec.Hmac.Instance) (hD : I.S.digestBytes < 2 ^ 64) (stack : Nat) :
    PostOut (I.finalizeContract abi stack) ((Spec.Hmac.finalizeSig I.S).retBits 64) := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨inn, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨otr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Hmac.finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < I.S.digestBytes, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hD, hi]))).symm
    intro k0 text h1 h2 hri hc hro
    show Spec.Sha256.bytesAt m₂ out I.S.digestBytes = _
    rw [Sha256.Stream.bytesAt_congr ho]
    exact h k0 text h1 h2 hri hc hro

/-- `vg_hmac_md5_init` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem md5_init_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.init Md5.hash)
      (Spec.Hmac.md5I.initAnyKeyContract RISCV64.abi (Md5.hash.ibytes + Md5.hash.F)) 0 :=
  verifiedScrubbedSelT (api := Spec.Hmac.md5I.initAnyKeyApi)
    (W := Md5.hash.ibytes + Md5.hash.F)
    { code := Md5.hash.init, verified := Md5.init }
    _ [] (hmacInitAnyOut Spec.Hmac.md5I Proof.Hmac.md5_local (by decide) _) (by lit_decide)
    (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_hmac_md5_finalize` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem md5_finalize_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.finalize Md5.hash)
      (Spec.Hmac.md5I.finalizeContract RISCV64.abi (Md5.hash.fbytes + Md5.hash.F)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.md5I.finalizeApi)
    (W := Md5.hash.fbytes + Md5.hash.F)
    { code := Md5.hash.finalize, verified := Md5.finalize }
    (hmacFinOut Spec.Hmac.md5I (by decide) _) (by lit_decide)

/-- `vg_hmac_sha1_init` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem sha1_init_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.init Sha1.hash)
      (Spec.Hmac.sha1I.initAnyKeyContract RISCV64.abi (Sha1.hash.ibytes + Sha1.hash.F)) 0 :=
  verifiedScrubbedSelT (api := Spec.Hmac.sha1I.initAnyKeyApi)
    (W := Sha1.hash.ibytes + Sha1.hash.F)
    { code := Sha1.hash.init, verified := Sha1.init }
    _ [] (hmacInitAnyOut Spec.Hmac.sha1I Proof.Hmac.sha1_local (by decide) _) (by lit_decide)
    (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_hmac_sha1_finalize` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem sha1_finalize_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.finalize Sha1.hash)
      (Spec.Hmac.sha1I.finalizeContract RISCV64.abi (Sha1.hash.fbytes + Sha1.hash.F)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha1I.finalizeApi)
    (W := Sha1.hash.fbytes + Sha1.hash.F)
    { code := Sha1.hash.finalize, verified := Sha1.finalize }
    (hmacFinOut Spec.Hmac.sha1I (by decide) _) (by lit_decide)

/-- `vg_hmac_sha224_init` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem sha224_init_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.init Sha256Family.hash224)
      (Spec.Hmac.sha224I.initAnyKeyContract RISCV64.abi (Sha256Family.hash224.ibytes + Sha256Family.hash224.F)) 0 :=
  verifiedScrubbedSelT (api := Spec.Hmac.sha224I.initAnyKeyApi)
    (W := Sha256Family.hash224.ibytes + Sha256Family.hash224.F)
    { code := Sha256Family.hash224.init, verified := Sha224.init }
    _ [] (hmacInitAnyOut Spec.Hmac.sha224I Proof.Hmac.sha224_local (by decide) _) (by lit_decide)
    (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_hmac_sha224_finalize` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem sha224_finalize_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.finalize Sha256Family.hash224)
      (Spec.Hmac.sha224I.finalizeContract RISCV64.abi (Sha256Family.hash224.fbytes + Sha256Family.hash224.F)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha224I.finalizeApi)
    (W := Sha256Family.hash224.fbytes + Sha256Family.hash224.F)
    { code := Sha256Family.hash224.finalize, verified := Sha224.finalize }
    (hmacFinOut Spec.Hmac.sha224I (by decide) _) (by lit_decide)

/-- `vg_hmac_sha256_init` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem sha256_init_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.init Sha256Family.hash256)
      (Spec.Hmac.sha256I.initAnyKeyContract RISCV64.abi (Sha256Family.hash256.ibytes + Sha256Family.hash256.F)) 0 :=
  verifiedScrubbedSelT (api := Spec.Hmac.sha256I.initAnyKeyApi)
    (W := Sha256Family.hash256.ibytes + Sha256Family.hash256.F)
    { code := Sha256Family.hash256.init, verified := Sha256.init }
    _ [] (hmacInitAnyOut Spec.Hmac.sha256I Proof.Hmac.sha256_local (by decide) _) (by lit_decide)
    (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_hmac_sha256_finalize` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem sha256_finalize_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.finalize Sha256Family.hash256)
      (Spec.Hmac.sha256I.finalizeContract RISCV64.abi (Sha256Family.hash256.fbytes + Sha256Family.hash256.F)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha256I.finalizeApi)
    (W := Sha256Family.hash256.fbytes + Sha256Family.hash256.F)
    { code := Sha256Family.hash256.finalize, verified := Sha256.finalize }
    (hmacFinOut Spec.Hmac.sha256I (by decide) _) (by lit_decide)

/-- `vg_hmac_sha384_init` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem sha384_init_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.init Sha384.hash)
      (Spec.Hmac.sha384I.initAnyKeyContract RISCV64.abi (Sha384.hash.ibytes + Sha384.hash.F)) 0 :=
  verifiedScrubbedSelT (api := Spec.Hmac.sha384I.initAnyKeyApi)
    (W := Sha384.hash.ibytes + Sha384.hash.F)
    { code := Sha384.hash.init, verified := Sha384.init }
    _ [] (hmacInitAnyOut Spec.Hmac.sha384I Proof.Hmac.sha384_local (by decide) _) (by lit_decide)
    (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_hmac_sha384_finalize` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem sha384_finalize_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.finalize Sha384.hash)
      (Spec.Hmac.sha384I.finalizeContract RISCV64.abi (Sha384.hash.fbytes + Sha384.hash.F)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha384I.finalizeApi)
    (W := Sha384.hash.fbytes + Sha384.hash.F)
    { code := Sha384.hash.finalize, verified := Sha384.finalize }
    (hmacFinOut Spec.Hmac.sha384I (by decide) _) (by lit_decide)

/-- `vg_hmac_sha512_init` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_init_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.init Sha512.hash)
      (Spec.Hmac.sha512I.initAnyKeyContract RISCV64.abi (Sha512.hash.ibytes + Sha512.hash.F)) 0 :=
  verifiedScrubbedSelT (api := Spec.Hmac.sha512I.initAnyKeyApi)
    (W := Sha512.hash.ibytes + Sha512.hash.F)
    { code := Sha512.hash.init, verified := Sha512.init }
    _ [] (hmacInitAnyOut Spec.Hmac.sha512I Proof.Hmac.sha512_local (by decide) _) (by lit_decide)
    (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_hmac_sha512_finalize` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_finalize_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.finalize Sha512.hash)
      (Spec.Hmac.sha512I.finalizeContract RISCV64.abi (Sha512.hash.fbytes + Sha512.hash.F)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha512I.finalizeApi)
    (W := Sha512.hash.fbytes + Sha512.hash.F)
    { code := Sha512.hash.finalize, verified := Sha512.finalize }
    (hmacFinOut Spec.Hmac.sha512I (by decide) _) (by lit_decide)

/-- `vg_hmac_sha512_224_init` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_224_init_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.init Sha512_224.hash)
      (Spec.Hmac.sha512_224I.initAnyKeyContract RISCV64.abi (Sha512_224.hash.ibytes + Sha512_224.hash.F)) 0 :=
  verifiedScrubbedSelT (api := Spec.Hmac.sha512_224I.initAnyKeyApi)
    (W := Sha512_224.hash.ibytes + Sha512_224.hash.F)
    { code := Sha512_224.hash.init, verified := Sha512_224.init }
    _ [] (hmacInitAnyOut Spec.Hmac.sha512_224I Proof.Hmac.sha512_224_local (by decide) _) (by lit_decide)
    (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_hmac_sha512_224_finalize` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_224_finalize_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.finalize Sha512_224.hash)
      (Spec.Hmac.sha512_224I.finalizeContract RISCV64.abi (Sha512_224.hash.fbytes + Sha512_224.hash.F)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha512_224I.finalizeApi)
    (W := Sha512_224.hash.fbytes + Sha512_224.hash.F)
    { code := Sha512_224.hash.finalize, verified := Sha512_224.finalize }
    (hmacFinOut Spec.Hmac.sha512_224I (by decide) _) (by lit_decide)

/-- `vg_hmac_sha512_256_init` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_256_init_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.init Sha512_256.hash)
      (Spec.Hmac.sha512_256I.initAnyKeyContract RISCV64.abi (Sha512_256.hash.ibytes + Sha512_256.hash.F)) 0 :=
  verifiedScrubbedSelT (api := Spec.Hmac.sha512_256I.initAnyKeyApi)
    (W := Sha512_256.hash.ibytes + Sha512_256.hash.F)
    { code := Sha512_256.hash.init, verified := Sha512_256.init }
    _ [] (hmacInitAnyOut Spec.Hmac.sha512_256I Proof.Hmac.sha512_256_local (by decide) _) (by lit_decide)
    (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_hmac_sha512_256_finalize` as emitted (`Impl.Hmac.Stream.RISCV64.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_256_finalize_scrubbed :
    VerifiedScrubbed target (Impl.Hmac.Stream.RISCV64.Fn.finalize Sha512_256.hash)
      (Spec.Hmac.sha512_256I.finalizeContract RISCV64.abi (Sha512_256.hash.fbytes + Sha512_256.hash.F)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha512_256I.finalizeApi)
    (W := Sha512_256.hash.fbytes + Sha512_256.hash.F)
    { code := Sha512_256.hash.finalize, verified := Sha512_256.finalize }
    (hmacFinOut Spec.Hmac.sha512_256I (by decide) _) (by lit_decide)

end VG.Proof.Hmac.Stream.RISCV64.Scrub
