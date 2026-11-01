module

public import VerifiedGarbage.Spec.MlKem.Contract

/-!
# ML-KEM-1024: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of ML-KEM-1024's key
generation, encapsulation key check, encapsulation and decapsulation, in
terms of `Spec/MlKem.lean`, for any target: `A` is the target's calling
convention.

They are those of ML-KEM-768 (`Spec/MlKem/Contract.lean`, whose notes all
apply here) for the parameter set `mlKem1024` (FIPS 203 Table 2: `k = 4`,
`η₁ = η₂ = 2`, `d_u = 11`, `d_v = 5`), with its sizes (Table 3): an
encapsulation key of 1568 bytes, a decapsulation key of 3168 bytes, and a
ciphertext of 1568 bytes. The same outcome (`Outcome`: 1, or 0 only if some
`SampleNTT` does not finish within `minIterations` iterations), the same leak
(`ρ`, the seed of `Â`, public in the encapsulation key, and nothing else: in
particular, not whether decapsulation rejected the ciphertext implicitly),
and the same keys: a decapsulation key is kept as the seed `d ‖ z` and
expanded by `vg_mlkem1024_keygen`, so there is no decapsulation key check.
Their documentation is that of `Contract.lean` (`Params.keyGenApi`, …), for
`mlKem1024`.

The working space `scratch` is 48 KiB, for the 16 entries of `Â` (the
matrix is 4 × 4) besides what ML-KEM-768 needs.
-/

@[expose] public section

namespace VG.Spec.MlKem1024

open Spec.MlKem
open Sha3 (bytesAt)

/-- `vg_mlkem1024_keygen(seed: *const [u8; 64], ek: *mut [u8; 1568], dk: *mut [u8; 3168], scratch: *mut [u64; 6144]) -> u32`.
`seed` holds `d ‖ z`; `scratch` is working space. -/
def keyGenSig : Sig where
  params := [("seed", .array false .u8 64), ("ek", .array true .u8 1568),
    ("dk", .array true .u8 3168), ("scratch", .array true .u64 6144)]
  ret := some .u32

/-- With the 64 bytes `d ‖ z` at `seed`: writes
`ML-KEM.KeyGen_internal(d, z)` (Algorithm 16) of ML-KEM-1024 to `ek` and
`dk`, and returns 1; or returns 0 (see `Outcome`). May leak `ρ`, the seed
of `Â` in the encapsulation key. -/
def keyGenContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keyGenSig.contract A
    (post := fun seed ek dk _scratch m m' r =>
      Outcome (fun iters => keyGenInternal mlKem1024 iters (bytesAt m seed 32)
          (bytesAt m (seed + 32) 32)) r
        (bytesAt m' ek 1568, bytesAt m' dk 3168))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ek _dk _scratch m => leakRho (keyGenRho mlKem1024 (bytesAt m seed 32)))

/-- `vg_mlkem1024_check_ek(ek: *const [u8; 1568]) -> u32`. -/
def checkEkSig : Sig where
  params := [("ek", .array false .u8 1568)]
  ret := some .u32

/-- Returns 1 if the 1568 bytes at `ek` pass the encapsulation key check of
§7.2 for ML-KEM-1024 (the modulus check: every integer they encode is less
than `q`), and 0 otherwise. Constant time. -/
def checkEkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkEkSig.contract A
    (post := fun ek m _m' r => r = if ekCheck mlKem1024 (bytesAt m ek 1568) then 1 else 0)
    (stack := stack)

/-- `vg_mlkem1024_encaps(ek: *const [u8; 1568], m: *const [u8; 32], key: *mut [u8; 32], ct: *mut [u8; 1568], scratch: *mut [u64; 6144]) -> u32`.
`m` is the randomness; `scratch` is working space. -/
def encapsSig : Sig where
  params := [("ek", .array false .u8 1568), ("m", .array false .u8 32),
    ("key", .array true .u8 32), ("ct", .array true .u8 1568),
    ("scratch", .array true .u64 6144)]
  ret := some .u32

/-- With the encapsulation key at `ek` and the 32 bytes of randomness at
`m`: writes the shared secret key and the ciphertext of
`ML-KEM.Encaps_internal(ek, m)` (Algorithm 17) of ML-KEM-1024 to `key` and
`ct`, and returns 1; or returns 0 (see `Outcome`). May leak `ρ`, the seed of
`Â` in `ek`. (The contract holds for any `ek`; the standard requires it to
have passed the check of §7.2.) -/
def encapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encapsSig.contract A
    (post := fun ek msg key ct _scratch m m' r =>
      Outcome (fun iters => encapsInternal mlKem1024 iters (bytesAt m ek 1568) (bytesAt m msg 32))
        r (bytesAt m' key 32, bytesAt m' ct 1568))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m => leakRho (ekRho mlKem1024 (bytesAt m ek 1568)))

/-- `vg_mlkem1024_decaps(dk: *const [u8; 3168], ct: *const [u8; 1568], key: *mut [u8; 32], scratch: *mut [u64; 6144]) -> u32`.
`scratch` is working space. -/
def decapsSig : Sig where
  params := [("dk", .array false .u8 3168), ("ct", .array false .u8 1568),
    ("key", .array true .u8 32), ("scratch", .array true .u64 6144)]
  ret := some .u32

/-- With the decapsulation key at `dk` and the ciphertext at `ct`: writes
the shared secret key `ML-KEM.Decaps_internal(dk, c)` (Algorithm 18) of
ML-KEM-1024 to `key`, and returns 1; or returns 0 (see `Outcome`). May leak
`ρ`, the seed of `Â` in the encapsulation key in `dk`, and nothing else: in
particular, not whether the ciphertext was rejected implicitly. -/
def decapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decapsSig.contract A
    (post := fun dk ct key _scratch m m' r =>
      Outcome (fun iters => decapsInternal mlKem1024 iters (bytesAt m dk 3168) (bytesAt m ct 1568))
        r (bytesAt m' key 32))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun dk _ct _key _scratch m => leakRho (dkRho mlKem1024 (bytesAt m dk 3168)))

/-! ## The functions on every target -/

/-- `vg_mlkem1024_keygen` on every target. -/
def keyGenApi : Api :=
  mlKem1024.keyGenApi "VG.Spec.MlKem1024" keyGenSig fun A stack => keyGenContract A stack

/-- `vg_mlkem1024_check_ek` on every target. -/
def checkEkApi : Api :=
  mlKem1024.checkEkApi "VG.Spec.MlKem1024" checkEkSig fun A stack => checkEkContract A stack

/-- `vg_mlkem1024_encaps` on every target. -/
def encapsApi : Api :=
  mlKem1024.encapsApi "VG.Spec.MlKem1024" encapsSig fun A stack => encapsContract A stack

/-- `vg_mlkem1024_decaps` on every target. -/
def decapsApi : Api :=
  mlKem1024.decapsApi "VG.Spec.MlKem1024" decapsSig fun A stack => decapsContract A stack

end VG.Spec.MlKem1024
