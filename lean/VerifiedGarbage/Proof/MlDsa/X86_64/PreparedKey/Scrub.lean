module

public import VerifiedGarbage.Impl.MlDsa.X86_64.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.BackendAvx2
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Avx2Lit
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.MlDsa.X86_64.PreparedKey
meta import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Prepare
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.BackendAvx2
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Avx2Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-DSA's preparation of keys on x86-64, without secret residue

`vg_mldsa*_prepare_verifying_key` and `vg_mldsa*_prepare_signing_key`, over
each implementation of the polynomial arithmetic but the samplers
(`Proof/Variants/MlDsaArith/X86_64.lean`), each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers that the residue analysis (`X86_64.RTaint`) finds may hold secrets.
Their NTTs run between Intel's MCDT prologue and epilogue, so they load
MXCSR; every path through them ends with its epilogue, which loads back the
caller's (`X86_64.mxClass`). Their postconditions read the memory on return
only within `prepared`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.PreparedKey.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Spec.MlDsa
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith params)
open VG.Proof.MlDsa.X86_64.Verify.Prepare (preparePublic_verified prepareSecret_verified preparePublic_spSafe
  prepareSecret_spSafe)

/-! ## The postconditions -/

theorem agreeBuf {m₁ m₂ : Mem} {q : Addr} {N : Nat} (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega) (by omega))).symm

theorem bytesAt_congr {m₁ m₂ : Mem} {q : Addr} {n N : Nat} (hn : n ≤ N)
    (h : ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i)) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n :=
  List.map_congr_left fun i hi => h i (by have := List.mem_range.mp hi; omega)

/-- A polynomial stored in the `1024` bytes at `q + d` of a buffer of `N`
bytes at `q`, in memories that agree on the buffer. -/
theorem polyStored_congr {m₁ m₂ : Mem} {q : Addr} {d N : Nat} {f : Poly} (hd : d + 4 * n ≤ N)
    (h : ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i))
    (hf : PolyStored m₁ (q + BitVec.ofNat 64 d) f) : PolyStored m₂ (q + BitVec.ofNat 64 d) f := by
  intro i hi
  rw [← hf i hi]
  congr 1
  apply Mem.readW_congr
  intro t ht
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  exact h _ (by simp only [n] at hi hd; omega)

theorem pub_bytes : ∀ p ∈ params, preparedPublicKeyBytes p < 2 ^ 64 := by decide
theorem sec_bytes : ∀ p ∈ params, preparedSecretKeyBytes p < 2 ^ 64 := by decide

theorem pubOut {p : Params} (hp : p ∈ params) :
    PostOut (preparePublicKeyContract p X86_64.abi 32) ((preparePublicKeySig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨prep, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [preparePublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hw := agreeBuf (pub_bytes p hp) hb.2.1
    obtain ⟨h₁, h₂⟩ := h
    change Spec.Sha3.bytesAt m₁ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen at h₁
    change PreparedPublicKey p m₁ prep at h₂
    change Spec.Sha3.bytesAt m₂ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen ∧ PreparedPublicKey p m₂ prep
    have e := bytesAt_congr (n := p.pkLen) (by simp [preparedPublicKeyBytes]) hw
    refine ⟨?_, fun i hi => ?_⟩
    · exact e.trans h₁
    · rw [e]
      exact polyStored_congr (N := preparedPublicKeyBytes p)
        (by simp only [preparedPublicKeyBytes]; have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.k by omega)
            rw [Nat.mul_add, Nat.mul_one] at this; omega) hw (h₂ i hi)

theorem secOut {p : Params} (hp : p ∈ params) :
    PostOut (prepareSecretKeyContract p X86_64.abi 32) ((prepareSecretKeySig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨sk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨prep, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [prepareSecretKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hw := agreeBuf (sec_bytes p hp) hb.2.1
    obtain ⟨h₁, h₂⟩ := h
    change Spec.Sha3.bytesAt m₁ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen at h₁
    change PreparedSecretKey p m₁ prep at h₂
    change Spec.Sha3.bytesAt m₂ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen ∧ PreparedSecretKey p m₂ prep
    have e := bytesAt_congr (n := p.skLen) (by simp [preparedSecretKeyBytes]) hw
    refine ⟨?_, fun i hi => ?_⟩
    · exact e.trans h₁
    · rw [e]
      exact polyStored_congr (N := preparedSecretKeyBytes p)
        (by simp only [preparedSecretKeyBytes]
            have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.ℓ + 2 * p.k by omega)
            rw [Nat.mul_add, Nat.mul_one] at this; omega) hw (h₂ i hi)

/-! ## The registrations -/

/-- The residue analysis of the code of the preparation of a public key over
the arithmetic `v`. -/
abbrev PubRes (v : ArithImpl) (p : Params) :=
  RScrub.Analysed (preparePublicKeySig p) 32 [] (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith v.code) p)

/-- The residue analysis of the code of the preparation of a private key over
the arithmetic `v`. -/
abbrev SecRes (v : ArithImpl) (p : Params) :=
  RScrub.Analysed (prepareSecretKeySig p) 32 [] (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith v.code) p)

/-- An implementation of the polynomial arithmetic but the samplers, with
the residue analysis of the preparation of each key over it, `none` for one
the analysis does not handle. -/
structure PrepImpl where
  arith : ArithImpl
  pub44 : Option (PubRes arith mlDsa44) := none
  sec44 : Option (SecRes arith mlDsa44) := none
  pub65 : Option (PubRes arith mlDsa65) := none
  sec65 : Option (SecRes arith mlDsa65) := none
  pub87 : Option (PubRes arith mlDsa87) := none
  sec87 : Option (SecRes arith mlDsa87) := none

open VG.X86_64.RScrub in
/-- `vg_<module>_prepare_verifying_key` over `v`, without secret residue given its analysis. -/
def pubReg (v : ArithImpl) (p : Params) (module name : String) (hp : p ∈ params) (a : Option (PubRes v p)) :
    Registration (preparePublicKeyApi p module name) X86_64.target :=
  withScrub {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith v.code) p
    stack := 32
    verified := preparePublic_verified (prims_okWith v) hp
    spSafe := preparePublic_spSafe (prims_okWith v) hp } (pubOut hp) [] (pubOk_nil _) a

open VG.X86_64.RScrub in
/-- `vg_<module>_prepare_signing_key` over `v`, without secret residue given its analysis. -/
def secReg (v : ArithImpl) (p : Params) (module name : String) (hp : p ∈ params) (a : Option (SecRes v p)) :
    Registration (prepareSecretKeyApi p module name) X86_64.target :=
  withScrub {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith v.code) p
    stack := 32
    verified := prepareSecret_verified (prims_okWith v) hp
    spSafe := prepareSecret_spSafe (prims_okWith v) hp } (secOut hp) [] (pubOk_nil _) a

/-! ## The analyses -/

def pub44Sse2Ks : List Nat :=
  keep_for% (preparePublicKeySig mlDsa44) 32 (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.sse2.code) mlDsa44) []

theorem pub44Sse2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (preparePublicKeySig mlDsa44) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.sse2.code) mlDsa44) h).any
      (RScrub.resOkB · 32 pub44Sse2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of pub44Sse2Ks (by taint_decide)

def pub65Sse2Ks : List Nat :=
  keep_for% (preparePublicKeySig mlDsa65) 32 (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.sse2.code) mlDsa65) []

theorem pub65Sse2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (preparePublicKeySig mlDsa65) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.sse2.code) mlDsa65) h).any
      (RScrub.resOkB · 32 pub65Sse2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of pub65Sse2Ks (by taint_decide)

def pub87Sse2Ks : List Nat :=
  keep_for% (preparePublicKeySig mlDsa87) 32 (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.sse2.code) mlDsa87) []

theorem pub87Sse2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (preparePublicKeySig mlDsa87) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.sse2.code) mlDsa87) h).any
      (RScrub.resOkB · 32 pub87Sse2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of pub87Sse2Ks (by taint_decide)

def sec44Sse2Ks : List Nat :=
  keep_for% (prepareSecretKeySig mlDsa44) 32 (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.sse2.code) mlDsa44) []

theorem sec44Sse2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (prepareSecretKeySig mlDsa44) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.sse2.code) mlDsa44) h).any
      (RScrub.resOkB · 32 sec44Sse2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of sec44Sse2Ks (by taint_decide)

def sec65Sse2Ks : List Nat :=
  keep_for% (prepareSecretKeySig mlDsa65) 32 (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.sse2.code) mlDsa65) []

theorem sec65Sse2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (prepareSecretKeySig mlDsa65) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.sse2.code) mlDsa65) h).any
      (RScrub.resOkB · 32 sec65Sse2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of sec65Sse2Ks (by taint_decide)

def sec87Sse2Ks : List Nat :=
  keep_for% (prepareSecretKeySig mlDsa87) 32 (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.sse2.code) mlDsa87) []

theorem sec87Sse2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (prepareSecretKeySig mlDsa87) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.sse2.code) mlDsa87) h).any
      (RScrub.resOkB · 32 sec87Sse2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of sec87Sse2Ks (by taint_decide)

/-- `ArithImpl.sse2`, with its analyses. -/
def sse2 : PrepImpl where
  arith := ArithImpl.sse2
  pub44 := some ⟨pub44Sse2Ks, pub44Sse2Ok⟩
  sec44 := some ⟨sec44Sse2Ks, sec44Sse2Ok⟩
  pub65 := some ⟨pub65Sse2Ks, pub65Sse2Ok⟩
  sec65 := some ⟨sec65Sse2Ks, sec65Sse2Ok⟩
  pub87 := some ⟨pub87Sse2Ks, pub87Sse2Ok⟩
  sec87 := some ⟨sec87Sse2Ks, sec87Sse2Ok⟩

def pub44Avx2Ks : List Nat :=
  keep_for% (preparePublicKeySig mlDsa44) 32 (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.avx2.code) mlDsa44) []

theorem pub44Avx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (preparePublicKeySig mlDsa44) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.avx2.code) mlDsa44) h).any
      (RScrub.resOkB · 32 pub44Avx2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of pub44Avx2Ks (by taint_decide)

def pub65Avx2Ks : List Nat :=
  keep_for% (preparePublicKeySig mlDsa65) 32 (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.avx2.code) mlDsa65) []

theorem pub65Avx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (preparePublicKeySig mlDsa65) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.avx2.code) mlDsa65) h).any
      (RScrub.resOkB · 32 pub65Avx2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of pub65Avx2Ks (by taint_decide)

def pub87Avx2Ks : List Nat :=
  keep_for% (preparePublicKeySig mlDsa87) 32 (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.avx2.code) mlDsa87) []

theorem pub87Avx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (preparePublicKeySig mlDsa87) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith ArithImpl.avx2.code) mlDsa87) h).any
      (RScrub.resOkB · 32 pub87Avx2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of pub87Avx2Ks (by taint_decide)

def sec44Avx2Ks : List Nat :=
  keep_for% (prepareSecretKeySig mlDsa44) 32 (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.avx2.code) mlDsa44) []

theorem sec44Avx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (prepareSecretKeySig mlDsa44) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.avx2.code) mlDsa44) h).any
      (RScrub.resOkB · 32 sec44Avx2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of sec44Avx2Ks (by taint_decide)

def sec65Avx2Ks : List Nat :=
  keep_for% (prepareSecretKeySig mlDsa65) 32 (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.avx2.code) mlDsa65) []

theorem sec65Avx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (prepareSecretKeySig mlDsa65) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.avx2.code) mlDsa65) h).any
      (RScrub.resOkB · 32 sec65Avx2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of sec65Avx2Ks (by taint_decide)

def sec87Avx2Ks : List Nat :=
  keep_for% (prepareSecretKeySig mlDsa87) 32 (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.avx2.code) mlDsa87) []

theorem sec87Avx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init (prepareSecretKeySig mlDsa87) 32 [])
      (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith ArithImpl.avx2.code) mlDsa87) h).any
      (RScrub.resOkB · 32 sec87Avx2Ks (Impl.Scrub.X86_64.chunks 32)) = true :=
  RScrub.Analysed.ok_of sec87Avx2Ks (by taint_decide)

/-- `ArithImpl.avx2`, with its analyses. -/
def avx2 : PrepImpl where
  arith := ArithImpl.avx2
  pub44 := some ⟨pub44Avx2Ks, pub44Avx2Ok⟩
  sec44 := some ⟨sec44Avx2Ks, sec44Avx2Ok⟩
  pub65 := some ⟨pub65Avx2Ks, pub65Avx2Ok⟩
  sec65 := some ⟨sec65Avx2Ks, sec65Avx2Ok⟩
  pub87 := some ⟨pub87Avx2Ks, pub87Avx2Ok⟩
  sec87 := some ⟨sec87Avx2Ks, sec87Avx2Ok⟩

end VG.Proof.MlDsa.X86_64.PreparedKey.Scrub
