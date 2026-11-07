module

public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.MlDsa.Arith.Mem

/-!
# ML-DSA with prepared keys: the contracts of its internal functions

Not trusted: the contracts of the internal functions (`Rust.Internal`) that
`vg_mldsa*_sign_message_prepared` and `vg_mldsa*_verify_message_prepared`
(`Spec/MlDsa/PreparedKey.lean`) call, and that the ordinary entries
`vg_mldsa*_sign` and `vg_mldsa*_verify` share with them:

* the signing and verification kernels, `vg_mldsa*_sign_with_cache` and
  `vg_mldsa*_verify_with_cache`, which take an optional read-only slice of the
  key's polynomials: an empty one selects decoding and transforming the key;
* signing and verification of a message representative `μ` with a prepared
  key, `vg_mldsa*_sign_prepared` and `vg_mldsa*_verify_prepared`.

Their results and permitted leakage are those of `signContract` and
`verifyContract`.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The spec's stored polynomial (`PolyStored`) is `PolyIs`. -/
theorem polyStored_iff {m : Mem} {p : Addr} {f : Poly} : PolyStored m p f ↔ PolyIs m p f := by
  constructor
  · intro h
    apply Arith.polyIs_of_toNat
    intro i hi
    rw [show f[i]! = f[i]'hi from getElem!_pos f i hi]
    exact h i hi
  · intro h i hi
    have := Arith.polyIs_toNat h hi
    rw [show f[i]! = f[i]'hi from getElem!_pos f i hi] at this
    exact this

/-- The prepared public key, as `PolyIs`. -/
theorem preparedPublicKey_iff {p : Params} {m : Mem} {key : Addr} :
    PreparedPublicKey p m key ↔ ∀ i < p.k,
      PolyIs m (key + BitVec.ofNat 64 (p.pkLen + 4 * n * i))
        (preparedPublicPolys p (bytesAt m key p.pkLen))[i]! :=
  forall_congr' fun _ => imp_congr_right fun _ => polyStored_iff

/-- The prepared private key, as `PolyIs`. -/
theorem preparedSecretKey_iff {p : Params} {m : Mem} {key : Addr} :
    PreparedSecretKey p m key ↔ ∀ i < p.ℓ + 2 * p.k,
      PolyIs m (key + BitVec.ofNat 64 (p.skLen + 4 * n * i))
        (preparedSecretPolys p (bytesAt m key p.skLen))[i]! :=
  forall_congr' fun _ => imp_congr_right fun _ => polyStored_iff

/-! ## Signing and verifying a message representative with a prepared key -/

def preparedSignSig (p : Params) : Sig where
  params := [("sk", .array false .u8 (preparedSecretKeyBytes p)), ("mu", .array false .u8 64),
    ("rnd", .array false .u8 32), ("sig", .array true .u8 p.sigLen),
    ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

/-- `signContract` of the encoded key a prepared private key begins with. -/
def preparedSignContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (preparedSignSig p).contract A
    (pre := fun sk _mu _rnd _sig _scratch m => PreparedSecretKey p m sk)
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeak p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

def preparedVerifySig (p : Params) : Sig where
  params := [("pk", .array false .u8 (preparedPublicKeyBytes p)), ("mu", .array false .u8 64),
    ("sig", .array false .u8 p.sigLen), ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

/-- `verifyContract` of the encoded key a prepared public key begins with. -/
def preparedVerifyContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (preparedVerifySig p).contract A
    (pre := fun pk _mu _sig _scratch m => PreparedPublicKey p m pk)
    (post := fun pk mu sig _scratch m _m' r =>
      let v := fun b => verifyMu p b (bytesAt m pk p.pkLen) (bytesAt m mu 64) (bytesAt m sig p.sigLen)
      (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk mu sig _scratch m =>
      leakBytes (bytesAt m pk p.pkLen ++ bytesAt m mu 64 ++ bytesAt m sig p.sigLen))

/-! ## The kernels with an optional polynomial cache -/

/-- The secret polynomials of `sk`, stored at `cache`. -/
def CachedSecretPolys (p : Params) (m : Mem) (cache : Addr) (sk : List Byte) : Prop :=
  ∀ i < p.ℓ + 2 * p.k, PolyIs m (cache + BitVec.ofNat 64 (4 * n * i))
    (preparedSecretPolys p sk)[i]!

/-- The public polynomials of `pk`, stored at `cache`. -/
def CachedPublicPolys (p : Params) (m : Mem) (cache : Addr) (pk : List Byte) : Prop :=
  ∀ i < p.k, PolyIs m (cache + BitVec.ofNat 64 (4 * n * i))
    (preparedPublicPolys p pk)[i]!

def signWithCacheSig (p : Params) : Sig :=
  { signSig p with params := (signSig p).params ++
      [("cache", .slice false .u8 "cache_len")] }

/-- `signContract`, with an empty cache or the secret polynomials of `sk`. -/
def signWithCacheContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (signWithCacheSig p).contract A
    (pre := fun sk _mu _rnd _sig _scratch cache cacheLen m =>
      cacheLen = 0 ∨
      (cacheLen.toNat = 4 * n * (p.ℓ + 2 * p.k) ∧
        CachedSecretPolys p m cache (bytesAt m sk p.skLen)))
    (post := fun sk mu rnd sig _scratch _cache _cacheLen m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch _cache _cacheLen m =>
      signLeak p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

def verifyWithCacheSig (p : Params) : Sig :=
  { verifySig p with params := (verifySig p).params ++
      [("cache", .slice false .u8 "cache_len")] }

/-- `verifyContract`, with an empty cache or the public polynomials of `pk`. -/
def verifyWithCacheContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (verifyWithCacheSig p).contract A
    (pre := fun pk _mu _sig _scratch cache cacheLen m =>
      cacheLen = 0 ∨
      (cacheLen.toNat = 4 * n * p.k ∧
        CachedPublicPolys p m cache (bytesAt m pk p.pkLen)))
    (post := fun pk mu sig _scratch _cache _cacheLen m _m' r =>
      let v := fun b => verifyMu p b (bytesAt m pk p.pkLen) (bytesAt m mu 64) (bytesAt m sig p.sigLen)
      (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk mu sig _scratch _cache _cacheLen m =>
      leakBytes (bytesAt m pk p.pkLen ++ bytesAt m mu 64 ++ bytesAt m sig p.sigLen))

/-! ## Keys, encoded or prepared -/

/-- The length of a private key: encoded, or prepared (`prepared`). -/
def secretKeyLen (p : Params) (prepared : Bool) : Nat := if prepared then preparedSecretKeyBytes p else p.skLen

/-- The length of a public key: encoded, or prepared (`prepared`). -/
def publicKeyLen (p : Params) (prepared : Bool) : Nat := if prepared then preparedPublicKeyBytes p else p.pkLen

/-- The private key at `a` is a prepared one, if `prepared`. -/
def SecretKeyOk (p : Params) (prepared : Bool) (m : Mem) (a : Addr) : Prop :=
  prepared = true → PreparedSecretKey p m a

/-- The public key at `a` is a prepared one, if `prepared`. -/
def PublicKeyOk (p : Params) (prepared : Bool) (m : Mem) (a : Addr) : Prop :=
  prepared = true → PreparedPublicKey p m a

/-! ## The names of the internal functions -/

def signWithCacheName (module : String) : String := s!"vg_{module}_sign_with_cache"
def verifyWithCacheName (module : String) : String := s!"vg_{module}_verify_with_cache"
def preparedSignName (module : String) : String := s!"vg_{module}_sign_prepared"
def preparedVerifyName (module : String) : String := s!"vg_{module}_verify_prepared"

end VG.Proof.MlDsa
