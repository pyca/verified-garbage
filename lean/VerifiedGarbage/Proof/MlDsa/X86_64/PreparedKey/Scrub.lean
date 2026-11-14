module

public import VerifiedGarbage.Impl.MlDsa.X86_64.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Entry
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA's preparation of keys on x86-64, without secret residue

`vg_mldsa*_prepare_verifying_key` and `vg_mldsa*_prepare_signing_key`, over
each implementation of the polynomial arithmetic but the samplers
(`Proof/Variants/MlDsaArith/X86_64.lean`): each a call of the preparation
inside Intel's MXCSR prologue and epilogue (`Verify.Prepare.preparePublicEntry_verified`),
followed by `Impl.Scrub.X86_64.scrubTail` with every granule of its 56 bytes
of stack wiped and MXCSR's status flags cleared (`X86_64.RScrub.withScrubAllX`):
it restores MXCSR from `rbx`, which only the contract of the function it calls
keeps. Their postconditions read the memory on return only within `prepared`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.PreparedKey.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Spec.MlDsa
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith params)
open VG.Proof.MlDsa.X86_64.Verify.Prepare (preparePublicEntry_verified prepareSecretEntry_verified
  preparePublicEntry_spSafe prepareSecretEntry_spSafe)

/-! ## The postconditions -/

theorem agreeBuf {m₁ m₂ : Mem} {q : Addr} {N : Nat} (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hN, hi]))).symm

theorem bytesAt_congr {m₁ m₂ : Mem} {q : Addr} {n N : Nat} (hn : n ≤ N)
    (h : ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i)) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n :=
  List.map_congr_left fun i hi => h i (by have := List.mem_range.mp hi; omega_using [hn, this])

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
  exact h _ (by simp only [n] at hi hd; omega_using [hd, hi, ht])

theorem pub_bytes : ∀ p ∈ params, preparedPublicKeyBytes p < 2 ^ 64 := by decide
theorem sec_bytes : ∀ p ∈ params, preparedSecretKeyBytes p < 2 ^ 64 := by decide

theorem pubOut {p : Params} (hp : p ∈ params) :
    PostOut (preparePublicKeyContract p X86_64.abi 56) ((preparePublicKeySig p).retBits 64) :=
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
        (by simp only [preparedPublicKeyBytes]; have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

theorem secOut {p : Params} (hp : p ∈ params) :
    PostOut (prepareSecretKeyContract p X86_64.abi 56) ((prepareSecretKeySig p).retBits 64) :=
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
            have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.ℓ + 2 * p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

/-! ## The registrations -/

open VG.X86_64.RScrub in
/-- `vg_<module>_prepare_verifying_key` over `v`: the preparation inside Intel's MXCSR prologue
and epilogue, with every granule of its stack wiped (`withScrubAllX`). -/
def pubReg (v : ArithImpl) (p : Params) (module name : String) (hp : p ∈ params) :
    Registration (preparePublicKeyApi p module name) X86_64.target :=
  withScrubAllX {
    suffix := v.code.sfx
    code := Impl.Mcdt.X86_64.mcdtCall (Proof.MlDsa.preparePublicInternalName module ++ v.code.sfx)
      (Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith v.code) p)
    stack := 56
    verified := preparePublicEntry_verified (prims_okWith v) hp _
    spSafe := preparePublicEntry_spSafe (prims_okWith v) hp _ } (pubOut hp)

open VG.X86_64.RScrub in
/-- `vg_<module>_prepare_signing_key` over `v`: the preparation inside Intel's MXCSR prologue
and epilogue, with every granule of its stack wiped (`withScrubAllX`). -/
def secReg (v : ArithImpl) (p : Params) (module name : String) (hp : p ∈ params) :
    Registration (prepareSecretKeyApi p module name) X86_64.target :=
  withScrubAllX {
    suffix := v.code.sfx
    code := Impl.Mcdt.X86_64.mcdtCall (Proof.MlDsa.prepareSecretInternalName module ++ v.code.sfx)
      (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith v.code) p)
    stack := 56
    verified := prepareSecretEntry_verified (prims_okWith v) hp _
    spSafe := prepareSecretEntry_spSafe (prims_okWith v) hp _ } (secOut hp)

end VG.Proof.MlDsa.X86_64.PreparedKey.Scrub
