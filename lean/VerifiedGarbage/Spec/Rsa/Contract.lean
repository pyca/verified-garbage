module

public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.TCB.Artifact

/-!
# RSA primitives: the contracts, on every target

**Trusted** (as every file in `Spec/`). In the module `rsa`:

* `vg_rsa_public_precompute`: the values of a public key's modulus that
  RSAEP needs (`Rsa.publicPrecompute`), to be kept with the key;
* `vg_rsa_private_crt`: RSADP and RSASP1 with the private key
  `(p, q, dP, dQ, qInv)` (`Rsa.privateCrt`);
* `vg_rsa_crt_values`: the CRT values `(dP, dQ, qInv)` of the private key
  `(p, q, d)` (`Rsa.crtKey`), for `vg_rsa_private_crt`;
* `vg_rsa_recover_primes`: the prime factors `(p, q)` of the modulus of the
  private key `(n, e, d)` (`Rsa.primesKey`), for `vg_rsa_crt_values`;
* `vg_rsa_public_precomputed_checked`: RSAEP and RSAVP1 (`Rsa.publicOp`)
  within BoringSSL's limits on the public exponent (`Rsa.publicOpChecked`),
  from the values `vg_rsa_public_precompute` computed, without computing
  them again (`publicCheckedContract` states the same operation given the
  modulus itself, for the code of the RSA padding functions that call it;
  it is not a function of the module);
* `vg_rsa_private_checked`: `vg_rsa_private_crt` given the public exponent
  too, releasing a result only if it passes BoringSSL's check against it
  (`Rsa.privateChecked`);
* `vg_rsa_private_precompute`: the values of a private key that
  `vg_rsa_private_checked` computes from it on every call
  (`Rsa.privatePrecompute`), to be kept with the key;
* `vg_rsa_private_crt_precomputed`: `vg_rsa_private_crt` from the values
  `vg_rsa_private_precompute` computed, without computing them again;
* `vg_rsa_private_checked_precomputed`: `vg_rsa_private_checked` from the
  values `vg_rsa_private_precompute` computed, without computing them
  again;
* `vg_rsa_check_key`: BoringSSL's `RSA_check_key` of the private key
  `(n, e, d, p, q, dP, dQ, qInv)` (`Rsa.checkKey`);
* `vg_rsa_check_crt_key`: the same checks of the CRT form
  `(n, e, p, q, dP, dQ, qInv)` alone (`Rsa.checkCrtKey`), for loading a key.

A private key is brought to the CRT form once, when it is loaded, and every
operation is `vg_rsa_private_checked`.

Every number is a slice of octets, most significant first, with a length of
its own (a `Sig` slice carries its own length). The modulus `n` is `n_len`
octets, from 64 to 1024, and so are the input and the output, and the
factors `vg_rsa_recover_primes` writes; `e` and `d` are at most `n_len`
octets; `p` and its values (`dP`, `qInv`) are `p_len` octets, and `q` and
`dQ` are `q_len` octets, each below `n_len`. These are preconditions, on the
public lengths; everything about the values is checked: the function returns
1 and writes its results, or returns 0 and writes zeros (but
`vg_rsa_private_checked`, which returns 2 and writes zeros on its internal
error, and `vg_rsa_check_key` and `vg_rsa_check_crt_key`, which write
nothing).

The signature determines memory validity, separation and that the pointers
and lengths are public, through `Sig.contract`. The public key, `n` and `e`,
is public too, and may affect timing (`leak`): an implementation may, for
instance, branch on the bits of `e`. The input is secret (RSAEP may encrypt
a secret), and so is every part of a private key. `vg_rsa_recover_primes`
may also leak how many candidates it tried, which is 1 or 2 for most keys
(SP 800-56B Rev. 2 Appendix C.1, note 1). The return
value depends on secrets (whether the input is below `n`, and whether the
private key is consistent).

`scratch` is working space of at least `16 n_len + 32` `u64`s, or, for the
public-key functions (`vg_rsa_public_precompute`, `vg_rsa_public_checked`
and `vg_rsa_public_precomputed_checked`), `8 ⌈n_len / 8⌉ + 48`, whose
contents on return are unspecified. `stack` is the number of bytes below the stack
pointer that an implementation's calls and frames use. The functions may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.Rsa

/-- The bytes at `p`, in increasing address order. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- The least working space, in `u64`s, for a modulus of `nLen` octets. -/
def scratchWords (nLen : Nat) : Nat := 16 * nLen + 32

/-- The least working space, in `u64`s, of the public-key functions for a
modulus of `nLen` octets: a header of 32 words and 8 numbers of
`⌈nLen / 8⌉ + 2` words. -/
def publicScratchWords (nLen : Nat) : Nat := 8 * modulusWords nLen + 48

/-- The bounds on the modulus' length, in octets. -/
def lenValid (nLen : Nat) : Prop := 64 ≤ nLen ∧ nLen ≤ 1024

/-- The postcondition of a function returning `res`, `nLen` octets or
`none`, at `out`. -/
def written (m' : Mem) (out : Addr) (nLen : Nat) (r : BitVec 32) : Option (List Byte) → Prop
  | some y => r = 1 ∧ bytesAt m' out nLen = y
  | none => r = 0 ∧ bytesAt m' out nLen = List.replicate nLen 0

/-- The postcondition of a function returning `res`, octet strings or `none`,
at the addresses and lengths `outs`: each string at its address, or zeros
at all of them. -/
def writtenAll (m' : Mem) (outs : List (Addr × Nat)) (r : BitVec 32) : Option (List (List Byte)) → Prop
  | some ys => r = 1 ∧ outs.map (fun o => bytesAt m' o.1 o.2) = ys
  | none => r = 0 ∧ ∀ o ∈ outs, bytesAt m' o.1 o.2 = List.replicate o.2 0

/-- The `n` words of 64 bits at `p`. -/
def wordsAt (m : Mem) (p : Addr) (n : Nat) : List (BitVec 64) :=
  (List.range n).map fun i => m.readW (p + BitVec.ofNat 64 (8 * i)) 64

/-- The words of the precomputed values of a modulus of `nLen` octets
(`publicPrecompute`). -/
def precomputedWords (nLen : Nat) : Nat := 2 * modulusWords nLen

/-- The `# Safety` items on the working space. -/
def scratchSafety : List String :=
  ["`scratch_len` must be at least `16 * n_len + 32`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-- The `# Safety` items on the working space of the public-key functions. -/
def publicScratchSafety : List String :=
  ["`scratch_len` must be at least `8 * ⌈n_len / 8⌉ + 48`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-! ## The public-key operation's signature -/

/-- `vg_rsa_public_checked(out: *mut u8, out_len: usize, n: *const u8, n_len: usize,
e: *const u8, e_len: usize, input: *const u8, input_len: usize,
scratch: *mut u64, scratch_len: usize) -> u32`. -/
def publicSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("input", .slice false .u8 "input_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-! ## `vg_rsa_public_precompute` -/

/-- `vg_rsa_public_precompute(pre: *mut u64, pre_len: usize, n: *const u8,
n_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def publicPrecomputeSig : Sig where
  params := [("pre", .slice true .u64 "pre_len"), ("n", .slice false .u8 "n_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The precomputed values of the modulus `n` (`publicPrecompute`). Timing
may depend on `n`, which is public. -/
def publicPrecomputeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  publicPrecomputeSig.contract A
    (pre := fun _pre preLen _n nLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ preLen.toNat = precomputedWords nLen.toNat ∧
        publicScratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun pre preLen n nLen _scratch _scratchLen m m' r =>
      match publicPrecompute (bytesAt m n nLen.toNat) with
      | some ws => r = 1 ∧ wordsAt m' pre preLen.toNat = ws
      | none => r = 0 ∧ wordsAt m' pre preLen.toNat = List.replicate preLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _pre _preLen n nLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

def publicPrecomputeApi : Api where
  module := "rsa"
  name := "vg_rsa_public_precompute"
  sig := publicPrecomputeSig
  writeArgs := true
  contracts := some fun A stack => publicPrecomputeContract A stack
  summary := "The values of an RSA modulus that `vg_rsa_public_precomputed_checked` takes, \
    so that they are computed once per public key rather than once per operation. With the modulus \
    `n` (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, its first byte \
    not zero) of `w = ⌈n_len / 8⌉` words of 64 bits, writes `n` and then `R² mod n` for \
    `R = 2^(64 w)` to `pre` (`w` words each, least significant first) and returns 1; or \
    writes zeros and returns 0 if `n` is not such a modulus.\n\n\
    Contract: `VG.Spec.Rsa.publicPrecomputeContract`. Timing may depend on the pointers, \
    the lengths and the contents of `n`."
  safety := ["`n_len` must be in 64..=1024.", "`pre_len` must be `2 * ⌈n_len / 8⌉`."] ++
    publicScratchSafety

/-! ## The signature of the public-key operation from precomputed values -/

/-- `vg_rsa_public_precomputed_checked(out: *mut u8, out_len: usize, pre: *const u64,
pre_len: usize, e: *const u8, e_len: usize, input: *const u8,
input_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def publicPrecomputedSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("pre", .slice false .u64 "pre_len"),
    ("e", .slice false .u8 "e_len"), ("input", .slice false .u8 "input_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-! ## `vg_rsa_private_crt` -/

/-- `vg_rsa_private_crt(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, input: *const u8, input_len: usize, p: *const u8, p_len: usize,
q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8,
dq_len: usize, qinv: *const u8, qinv_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def privateCrtSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("input", .slice false .u8 "input_len"), ("p", .slice false .u8 "p_len"),
    ("q", .slice false .u8 "q_len"), ("dp", .slice false .u8 "dp_len"),
    ("dq", .slice false .u8 "dq_len"), ("qinv", .slice false .u8 "qinv_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- RSADP of the input with the private key `(p, q, dP, dQ, qInv)` of the
modulus `n` (`privateCrt`). Constant time but for `n`. -/
def privateCrtContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privateCrtSig.contract A
    (pre := fun _out outLen _n nLen _input inputLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen input _inputLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen _scratch _scratchLen m m' r =>
      written m' out nLen.toNat r
        (privateCrt (bytesAt m n nLen.toNat) (bytesAt m input nLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen _input _inputLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

def privateCrtApi : Api where
  module := "rsa"
  name := "vg_rsa_private_crt"
  sig := privateCrtSig
  writeArgs := true
  contracts := some fun A stack => privateCrtContract A stack
  summary := "The RSA private-key operation: RSADP (RFC 8017 §5.1.2), which is also RSASP1 \
    (§5.2.1), with the private key `(p, q, dP, dQ, qInv)` (§3.2's second form, with two \
    primes). With the modulus `n` (`n_len` bytes, most significant first, odd, from 512 to \
    8192 bits, its first byte not zero), writes the result of step 2.b for the input \
    (`n_len` bytes, most significant first) to `out` (`n_len` bytes, most significant \
    first) and returns 1; or writes zeros and returns 0 if `n` is not such a modulus, the \
    input is not below `n`, `p q ≠ n`, or `qInv ≥ p`. `p`, `dp` and `qinv` are `p_len` \
    bytes, and `q` and `dq` are `q_len` bytes, all most significant first. For a valid RSA \
    key the result is `input^d mod n`; nothing checks that `p` and `q` are prime or that \
    the exponents match a public exponent.\n\n\
    Contract: `VG.Spec.Rsa.privateCrtContract`. Constant time but for the modulus: timing \
    may depend on the pointers, the lengths and the contents of `n`, not on the input or \
    the private key."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `input_len` must be `n_len`.",
    "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++ scratchSafety

/-! ## `vg_rsa_crt_values` -/

/-- `vg_rsa_crt_values(dp: *mut u8, dp_len: usize, dq: *mut u8,
dq_len: usize, qinv: *mut u8, qinv_len: usize, n: *const u8, n_len: usize,
p: *const u8, p_len: usize, q: *const u8, q_len: usize, d: *const u8,
d_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def crtValuesSig : Sig where
  params := [("dp", .slice true .u8 "dp_len"), ("dq", .slice true .u8 "dq_len"),
    ("qinv", .slice true .u8 "qinv_len"), ("n", .slice false .u8 "n_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("d", .slice false .u8 "d_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The CRT values of the private key `(p, q, d)` of the modulus `n`
(`crtKey`). Constant time but for `n`. -/
def crtValuesContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  crtValuesSig.contract A
    (pre := fun _dp dpLen _dq dqLen _qinv qinvLen _n nLen _p pLen _q qLen _d dLen _scratch
        scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧
        qLen.toNat < nLen.toNat ∧ dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧
        dqLen.toNat = qLen.toNat ∧ 1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun dp _dpLen dq _dqLen qinv _qinvLen n nLen p pLen q qLen d dLen _scratch
        _scratchLen m m' r =>
      writtenAll m' [(dp, pLen.toNat), (dq, qLen.toNat), (qinv, pLen.toNat)] r
        ((crtKey (bytesAt m n nLen.toNat) (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat)
          (bytesAt m d dLen.toNat)).map fun v => [v.1, v.2.1, v.2.2]))
    (writeArgs := true) (stack := stack)
    (leak := some fun _dp _dpLen _dq _dqLen _qinv _qinvLen n nLen _p _pLen _q _qLen _d _dLen
        _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

def crtValuesApi : Api where
  module := "rsa"
  name := "vg_rsa_crt_values"
  sig := crtValuesSig
  writeArgs := true
  contracts := some fun A stack => crtValuesContract A stack
  summary := "The CRT values of an RSA private key `(p, q, d)` (SP 800-56B Rev. 2 §6.2.2's \
    prime-factor format), which bring it to the CRT format `(p, q, dP, dQ, qInv)` that \
    `vg_rsa_private_crt` takes: `dP = d mod (p - 1)`, `dQ = d mod (q - 1)` and \
    `qInv = q⁻¹ mod p` (§6.2.2's CRT format). With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero), `p` (`p_len` \
    bytes), `q` (`q_len` bytes) and `d` (`d_len` bytes), all most significant first, writes \
    `dP` to `dp` and `qInv` to `qinv` (`p_len` bytes each) and `dQ` to `dq` (`q_len` bytes), \
    most significant first, and returns 1; or writes zeros to all three and returns 0 if `n` \
    is not such a modulus, `p q ≠ n`, or `q` has no inverse modulo `p`. Nothing checks that \
    `p` and `q` are prime or that `d` is the key's private exponent.\n\n\
    Contract: `VG.Spec.Rsa.crtValuesContract`. Constant time but for the modulus: timing \
    may depend on the pointers, the lengths and the contents of `n`, not on the private key."
  safety := ["`n_len` must be in 64..=1024.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`.",
    "`d_len` must be in 1..=`n_len`."] ++ scratchSafety

/-! ## `vg_rsa_recover_primes` -/

/-- `vg_rsa_recover_primes(p: *mut u8, p_len: usize, q: *mut u8,
q_len: usize, n: *const u8, n_len: usize, e: *const u8, e_len: usize,
d: *const u8, d_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def recoverPrimesSig : Sig where
  params := [("p", .slice true .u8 "p_len"), ("q", .slice true .u8 "q_len"),
    ("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("d", .slice false .u8 "d_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The prime factors of the modulus of the private key `(n, e, d)`
(`primesKey`). Constant time but for the public key and the number of
candidates the recovery tried. -/
def recoverPrimesContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  recoverPrimesSig.contract A
    (pre := fun _p pLen _q qLen _n nLen _e eLen _d dLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ pLen.toNat = nLen.toNat ∧ qLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧ 1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun p _pLen q _qLen n nLen e eLen d dLen _scratch _scratchLen m m' r =>
      writtenAll m' [(p, nLen.toNat), (q, nLen.toNat)] r
        ((primesKey (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
          (bytesAt m d dLen.toNat)).1.map fun v => [v.1, v.2]))
    (writeArgs := true) (stack := stack)
    (leak := some fun _p _pLen _q _qLen n nLen e eLen d dLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        [(primesKey (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
          (bytesAt m d dLen.toNat)).2])

def recoverPrimesApi : Api where
  module := "rsa"
  name := "vg_rsa_recover_primes"
  sig := recoverPrimesSig
  writeArgs := true
  contracts := some fun A stack => recoverPrimesContract A stack
  summary := s!"The prime factors `p > q` of the modulus of an RSA private key `(n, e, d)` \
    (SP 800-56B Rev. 2 §6.2.2's basic format), which bring it to the prime-factor format \
    `(p, q, d)` that `vg_rsa_crt_values` takes, recovered by SP 800-56B Rev. 2 Appendix C.1 \
    with the candidates `g = 2, 3, …` and at most {recoverTries} of them. With the modulus \
    `n` (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, its first byte \
    not zero), the public exponent `e` (`e_len` bytes) and the private exponent `d` \
    (`d_len` bytes), both most significant first, writes `p` and `q` (`n_len` bytes each, \
    most significant first) and returns 1; or writes zeros to both and returns 0 if `n` is \
    not such a modulus or its factors are not found. For a valid RSA key the factors are \
    found, but for a negligible fraction of keys.\n\n\
    Contract: `VG.Spec.Rsa.recoverPrimesContract`. Constant time but for the public key \
    and the number of candidates the recovery tried (1 or 2 for most keys): timing may \
    depend on the pointers, the lengths, the contents of `n` and `e`, and that number, not \
    otherwise on `d`."
  safety := ["`n_len` must be in 64..=1024.", "`p_len` and `q_len` must be `n_len`.",
    "`e_len` and `d_len` must be in 1..=`n_len`."] ++ scratchSafety

/-! ## BoringSSL's checks

The functions below check what BoringSSL checks (`Rsa.publicOpChecked`,
`Rsa.privateChecked`, `Rsa.checkKey`, `Rsa.checkCrtKey`). The public-key
operations without the check of `e` are retired; `vg_rsa_private_crt` remains, as the
operation that `vg_rsa_private_checked` checks. -/

/-- The public exponent and its limits, in the summaries. -/
def exponentDoc : String :=
  "the public exponent `e` (`e_len` bytes, most significant first, odd, from 3 to \
    `2^33 - 1`: BoringSSL's limits)"

/-! ### `vg_rsa_public_checked` -/

/-- RSAEP of the input with the public key `(n, e)`, within BoringSSL's
limits (`publicOpChecked`). Constant time but for the public key. -/
def publicCheckedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  publicSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _input inputLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen e eLen input _inputLen _scratch _scratchLen m m' r =>
      written m' out nLen.toNat r
        (publicOpChecked (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
          (bytesAt m input nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _input _inputLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

def publicCheckedApi : Api where
  module := "rsa"
  name := "vg_rsa_public_checked"
  sig := publicSig
  writeArgs := true
  contracts := some fun A stack => publicCheckedContract A stack
  summary := s!"The RSA public-key operation: RSAEP (RFC 8017 §5.1.1), which is also RSAVP1 \
    (§5.2.2), for a public key within BoringSSL's limits. With the modulus `n` (`n_len` \
    bytes, most significant first, odd, from 512 to 8192 bits, its first byte not zero) and \
    {exponentDoc}, writes `input^e mod n` (`n_len` bytes, most significant first) to `out` \
    and returns 1; or writes zeros and returns 0 if `n` or `e` is not such a number or the \
    input (`n_len` bytes, most significant first) is not below `n`.\n\n\
    Contract: `VG.Spec.Rsa.publicCheckedContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths and the contents of `n` and `e`, not on \
    the input."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `input_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`."] ++ publicScratchSafety

/-! ### `vg_rsa_public_precomputed_checked` -/

/-- RSAEP of the input with the public key `(n, e)`, within BoringSSL's
limits, given `n` by its precomputed values (`publicPrecompute`): for
whichever `n_len`-octet modulus `pre` holds the values of, as
`publicCheckedContract`. If `pre` holds the values of no modulus, the result
is unspecified (but memory safety and constant time are not). Constant time
but for the public key. -/
def publicPrecomputedCheckedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  publicPrecomputedSig.contract A
    (pre := fun _out outLen _pre preLen _e eLen _input inputLen _scratch scratchLen _ =>
      lenValid outLen.toNat ∧ preLen.toNat = precomputedWords outLen.toNat ∧
        inputLen.toNat = outLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ outLen.toNat ∧
        publicScratchWords outLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen pre preLen e eLen input _inputLen _scratch _scratchLen m m' r =>
      ∀ nB : List Byte, nB.length = outLen.toNat →
        publicPrecompute nB = some (wordsAt m pre preLen.toNat) →
        written m' out outLen.toNat r
          (publicOpChecked nB (bytesAt m e eLen.toNat) (bytesAt m input outLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen pre preLen e eLen _input _inputLen _scratch _scratchLen m =>
      (wordsAt m pre preLen.toNat).map (·.toNat) ++ (bytesAt m e eLen.toNat).map (·.toNat))

def publicPrecomputedCheckedApi : Api where
  module := "rsa"
  name := "vg_rsa_public_precomputed_checked"
  sig := publicPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => publicPrecomputedCheckedContract A stack
  summary := s!"The RSA public-key operation: RSAEP (RFC 8017 §5.1.1), which is also RSAVP1 \
    (§5.2.2), for a public key within BoringSSL's limits, with the modulus given by the \
    values `vg_rsa_public_precompute` wrote for it to `pre`. With those values \
    of a modulus `n` of `out_len` bytes and {exponentDoc}, writes `input^e mod n` \
    (`out_len` bytes, most significant first) to `out` and returns 1; or writes zeros and \
    returns 0 if `e` is not such a number or the input (`out_len` bytes, most significant \
    first) is not below `n`.\n\n\
    Contract: `VG.Spec.Rsa.publicPrecomputedCheckedContract`. Constant time but for the \
    public key: timing may depend on the pointers, the lengths and the contents of `pre` \
    and `e`, not on the input."
  safety := ["`out_len` must be in 64..=1024.", "`input_len` must be `out_len`.",
    "`pre_len` must be `2 * ⌈out_len / 8⌉`.", "`e_len` must be in 1..=`out_len`.",
    "For the result to be RSAEP's, `pre` must hold what `vg_rsa_public_precompute` wrote \
      for a modulus of `out_len` bytes (returning 1); otherwise it is unspecified."] ++
    publicScratchSafety

/-! ### `vg_rsa_private_checked` -/

/-- The postcondition of a function with the outcome `o` (`Outcome`) of
`nLen` octets at `out`: 1 and the result, 0 and zeros if the key or the
input is refused, or 2 and zeros on the internal error. -/
def writtenOutcome (m' : Mem) (out : Addr) (nLen : Nat) (r : BitVec 32) : Outcome → Prop
  | .ok y => r = 1 ∧ bytesAt m' out nLen = y
  | .invalid => r = 0 ∧ bytesAt m' out nLen = List.replicate nLen 0
  | .fault => r = 2 ∧ bytesAt m' out nLen = List.replicate nLen 0

/-- `vg_rsa_private_checked(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, e: *const u8, e_len: usize, input: *const u8,
input_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize,
dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize,
qinv: *const u8, qinv_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def privateCheckedSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("input", .slice false .u8 "input_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("dp", .slice false .u8 "dp_len"), ("dq", .slice false .u8 "dq_len"),
    ("qinv", .slice false .u8 "qinv_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- RSADP of the input with the private key `(p, q, dP, dQ, qInv)` of the
modulus `n`, checked against the public exponent `e` (`privateChecked`).
Constant time but for the public key. -/
def privateCheckedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privateCheckedSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _input inputLen _p pLen _q qLen _dp dpLen _dq dqLen
        _qinv qinvLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen e eLen input _inputLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen _scratch _scratchLen m m' r =>
      writtenOutcome m' out nLen.toNat r
        (privateChecked (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
          (bytesAt m input nLen.toNat) (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat)
          (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _input _inputLen _p _pLen _q _qLen _dp _dpLen
        _dq _dqLen _qinv _qinvLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

def privateCheckedApi : Api where
  module := "rsa"
  name := "vg_rsa_private_checked"
  sig := privateCheckedSig
  writeArgs := true
  contracts := some fun A stack => privateCheckedContract A stack
  summary := s!"The RSA private-key operation: RSADP (RFC 8017 §5.1.2), which is also RSASP1 \
    (§5.2.1), with the private key `(p, q, dP, dQ, qInv)` (§3.2's second form, with two \
    primes), checked against the public exponent as BoringSSL checks it \
    (`rsa_default_private_transform`). With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero) and \
    {exponentDoc}, computes the result `m` of step 2.b for the input (`n_len` bytes, most \
    significant first), and if `m^e mod n` is the input, writes `m` to `out` (`n_len` \
    bytes, most significant first) and returns 1. Writes zeros and returns 0 if `n` or `e` \
    is not such a number, the input is not below `n`, `p q ≠ n`, or `qInv ≥ p`; writes \
    zeros and returns 2 (an internal error) if `m^e mod n` is not the input, which is the \
    case for no input if `vg_rsa_check_key` accepts the key and `p` and `q` are prime: the \
    result is never released unless it passes the check, so that a fault in its \
    computation does not reveal the key. `p`, `dp` and `qinv` are `p_len` bytes, and `q` \
    and `dq` are `q_len` bytes, all most significant first.\n\n\
    Contract: `VG.Spec.Rsa.privateCheckedContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths and the contents of `n` and `e`, not on \
    the input or the private key."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `input_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++ scratchSafety

/-! ### `vg_rsa_private_precompute` -/

/-- The words of the precomputed values of a private key whose modulus is
`nLen` octets and whose factors are `pLen` and `qLen` octets
(`privatePrecompute`). -/
def privatePrecomputedWords (nLen pLen qLen : Nat) : Nat :=
  precomputedWords nLen + primeWords pLen + primeWords qLen

/-- `pre` holds the precomputed values (`privatePrecompute`) of the private
key with the modulus at `n` and the factors at `p` and `q`. -/
def privatePreOk (m : Mem) (n : Addr) (nLen : Nat) (p : Addr) (pLen : Nat) (q : Addr) (qLen : Nat)
    (pre : Addr) (preLen : Nat) : Prop :=
  privatePrecompute (bytesAt m n nLen) (bytesAt m p pLen) (bytesAt m q qLen) = some (wordsAt m pre preLen)

/-- The public part of the precomputed values of a private key at `pre`, for
a modulus of `nLen` octets: the values of the modulus (`publicPrecompute`),
which timing may depend on. -/
def privatePreLeak (m : Mem) (pre : Addr) (nLen : Nat) : List Nat :=
  (wordsAt m pre (precomputedWords nLen)).map (·.toNat)

/-- `vg_rsa_private_precompute(pre: *mut u64, pre_len: usize, n: *const u8,
n_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize,
scratch: *mut u64, scratch_len: usize) -> u32`. -/
def privatePrecomputeSig : Sig where
  params := [("pre", .slice true .u64 "pre_len"), ("n", .slice false .u8 "n_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The precomputed values of the private key with the modulus `n` and the
factors `p` and `q` (`privatePrecompute`). Constant time but for `n`. -/
def privatePrecomputeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privatePrecomputeSig.contract A
    (pre := fun _pre preLen _n nLen _p pLen _q qLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧
        qLen.toNat < nLen.toNat ∧
        preLen.toNat = privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun pre preLen n nLen p pLen q qLen _scratch _scratchLen m m' r =>
      match privatePrecompute (bytesAt m n nLen.toNat) (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) with
      | some ws => r = 1 ∧ wordsAt m' pre preLen.toNat = ws
      | none => r = 0 ∧ wordsAt m' pre preLen.toNat = List.replicate preLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _pre _preLen n nLen _p _pLen _q _qLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

def privatePrecomputeApi : Api where
  module := "rsa"
  name := "vg_rsa_private_precompute"
  sig := privatePrecomputeSig
  writeArgs := true
  contracts := some fun A stack => privatePrecomputeContract A stack
  summary := "The values of an RSA private key that `vg_rsa_private_checked_precomputed` \
    takes, so that they are computed once per key rather than once per operation. With the \
    modulus `n` (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, its first \
    byte not zero) of `w = ⌈n_len / 8⌉` words of 64 bits and its factors `p` (`p_len` bytes) \
    and `q` (`q_len` bytes), both most significant first, of `w_p = max(2, ⌈p_len / 8⌉)` and \
    `w_q = max(2, ⌈q_len / 8⌉)` words, writes to `pre` what `vg_rsa_public_precompute` \
    writes for `n` (`2 w` words), then `R_p mod p` for `R_p = 2^(64 w_p)` (`w_p` words) and \
    `R_q mod q` for `R_q = 2^(64 w_q)` (`w_q` words), each least significant first, and \
    returns 1; or writes zeros and returns 0 if `n` is not such a modulus or `p q ≠ n`. \
    `pre` then holds secrets, as the private key does.\n\n\
    Contract: `VG.Spec.Rsa.privatePrecomputeContract`. Constant time but for the modulus: \
    timing may depend on the pointers, the lengths and the contents of `n`, not on `p` or \
    `q`."
  safety := ["`n_len` must be in 64..=1024.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`pre_len` must be `2 * ⌈n_len / 8⌉ + max(2, ⌈p_len / 8⌉) + max(2, ⌈q_len / 8⌉)`.",
    "The contents of `pre` on return may contain secrets; the caller must destroy them \
      after use."] ++ scratchSafety

/-! ### `vg_rsa_private_crt_precomputed` -/

/-- `vg_rsa_private_crt_precomputed`: `privateCrtSig` with a final
read-only slice of precomputed `u64` words. -/
def privateCrtPrecomputedSig : Sig where
  params := privateCrtSig.params ++ [("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `privateCrtContract` with the precomputed values of the key
(`privatePrecompute`): its result when `pre` holds them; otherwise the
result is unspecified (but memory safety and constant time are not).
Constant time but for `n` and the public part of `pre`. -/
def privateCrtPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privateCrtPrecomputedSig.contract A
    (pre := fun _out outLen _n nLen _input inputLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat)
    (post := fun out _outLen n nLen input _inputLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen _scratch _scratchLen pre preLen m m' r =>
      privatePreOk m n nLen.toNat p pLen.toNat q qLen.toNat pre preLen.toNat →
        written m' out nLen.toNat r
          (privateCrt (bytesAt m n nLen.toNat) (bytesAt m input nLen.toNat)
            (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
            (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen _input _inputLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _scratch _scratchLen pre _preLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat) ++ privatePreLeak m pre nLen.toNat)

def privateCrtPrecomputedApi : Api where
  module := "rsa"
  name := "vg_rsa_private_crt_precomputed"
  sig := privateCrtPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => privateCrtPrecomputedContract A stack
  summary := "`vg_rsa_private_crt` (RSADP and RSASP1, RFC 8017 §5.1.2 and §5.2.1, with the \
    private key `(p, q, dP, dQ, qInv)`) given also `pre`, the `pre_len` words \
    `vg_rsa_private_precompute` wrote for `n`, `p` and `q` (returning 1), so that it does \
    not compute them again. With those values, writes to `out` and returns exactly what \
    `vg_rsa_private_crt` writes and returns for the other arguments. If `pre` does not hold \
    those values, the result is unspecified; memory safety and the timing guarantee still \
    apply.\n\n\
    Contract: `VG.Spec.Rsa.privateCrtPrecomputedContract`. Constant time but for the \
    modulus: timing may depend on the pointers, the lengths, the contents of `n` and the \
    first `2 * ⌈n_len / 8⌉` words of `pre` (the values of `n`), not on the input, the \
    private key or the rest of `pre`."
  safety := privateCrtApi.safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉ + max(2, ⌈p_len / 8⌉) + max(2, ⌈q_len / 8⌉)`.",
      "For the result to be the private-key operation's, `pre` must hold what \
        `vg_rsa_private_precompute` wrote for `n`, `p` and `q` (returning 1)."]

/-! ### `vg_rsa_private_checked_precomputed` -/

/-- `vg_rsa_private_checked_precomputed`: `privateCheckedSig` with a final
read-only slice of precomputed `u64` words. -/
def privateCheckedPrecomputedSig : Sig where
  params := privateCheckedSig.params ++ [("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `privateCheckedContract` with the precomputed values of the key
(`privatePrecompute`): its outcome when `pre` holds them; otherwise the
result is unspecified (but memory safety and constant time are not).
Constant time but for the public key and the public part of `pre`. -/
def privateCheckedPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privateCheckedPrecomputedSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _input inputLen _p pLen _q qLen _dp dpLen _dq dqLen
        _qinv qinvLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat)
    (post := fun out _outLen n nLen e eLen input _inputLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen _scratch _scratchLen pre preLen m m' r =>
      privatePreOk m n nLen.toNat p pLen.toNat q qLen.toNat pre preLen.toNat →
        writtenOutcome m' out nLen.toNat r
          (privateChecked (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
            (bytesAt m input nLen.toNat) (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat)
            (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _input _inputLen _p _pLen _q _qLen _dp _dpLen
        _dq _dqLen _qinv _qinvLen _scratch _scratchLen pre _preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        privatePreLeak m pre nLen.toNat)

def privateCheckedPrecomputedApi : Api where
  module := "rsa"
  name := "vg_rsa_private_checked_precomputed"
  sig := privateCheckedPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => privateCheckedPrecomputedContract A stack
  summary := "`vg_rsa_private_checked` (RSADP and RSASP1, RFC 8017 §5.1.2 and §5.2.1, with \
    the private key `(p, q, dP, dQ, qInv)`, checked against the public exponent as BoringSSL \
    checks it) given also `pre`, the `pre_len` words `vg_rsa_private_precompute` wrote for \
    `n`, `p` and `q` (returning 1), so that it does not compute them again. With those \
    values, writes to `out` and returns exactly what `vg_rsa_private_checked` writes and \
    returns for the other arguments. If `pre` does not hold those values, the result is \
    unspecified; memory safety and the timing guarantee still apply.\n\n\
    Contract: `VG.Spec.Rsa.privateCheckedPrecomputedContract`. Constant time but for the \
    public key: timing may depend on the pointers, the lengths, the contents of `n` and `e` \
    and the first `2 * ⌈n_len / 8⌉` words of `pre` (the values of `n`), not on the input, \
    the private key or the rest of `pre`."
  safety := privateCheckedApi.safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉ + max(2, ⌈p_len / 8⌉) + max(2, ⌈q_len / 8⌉)`.",
      "For the result to be the private-key operation's, `pre` must hold what \
        `vg_rsa_private_precompute` wrote for `n`, `p` and `q` (returning 1)."]

/-! ### `vg_rsa_check_key` -/

/-- `vg_rsa_check_key(n: *const u8, n_len: usize, e: *const u8, e_len: usize,
d: *const u8, d_len: usize, p: *const u8, p_len: usize, q: *const u8,
q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize,
qinv: *const u8, qinv_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def checkKeySig : Sig where
  params := [("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("d", .slice false .u8 "d_len"), ("p", .slice false .u8 "p_len"),
    ("q", .slice false .u8 "q_len"), ("dp", .slice false .u8 "dp_len"),
    ("dq", .slice false .u8 "dq_len"), ("qinv", .slice false .u8 "qinv_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- BoringSSL's `RSA_check_key` of the private key
`(n, e, d, p, q, dP, dQ, qInv)` (`checkKey`): 1 if it accepts the key, 0 if
not. Constant time but for the public key. -/
def checkKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkKeySig.contract A
    (pre := fun _n nLen _e eLen _d dLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv qinvLen
        _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun n nLen e eLen d dLen p pLen q qLen dp _dpLen dq _dqLen qinv _qinvLen _scratch
        _scratchLen m _m' r =>
      r = if checkKey (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m d dLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun n nLen e eLen _d _dLen _p _pLen _q _qLen _dp _dpLen _dq _dqLen _qinv
        _qinvLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

def checkKeyApi : Api where
  module := "rsa"
  name := "vg_rsa_check_key"
  sig := checkKeySig
  writeArgs := true
  contracts := some fun A stack => checkKeyContract A stack
  summary := "Checks an RSA private key `(n, e, d, p, q, dP, dQ, qInv)` exactly as \
    BoringSSL's `RSA_check_key` does. With the modulus `n` (`n_len` bytes), the public \
    exponent `e` (`e_len` bytes), the private exponent `d` (`d_len` bytes), `p`, `dp` and \
    `qinv` (`p_len` bytes) and `q` and `dq` (`q_len` bytes), all most significant first, \
    returns 1 if `n` is odd, from 512 to 8192 bits and its first byte not zero, `e` is odd \
    and from 3 to `2^33 - 1`, `d < n`, `p < n`, `q < n`, `p q = n`, \
    `d e ≡ 1 (mod p - 1)`, `d e ≡ 1 (mod q - 1)`, `dP < p - 1`, `e dP ≡ 1 (mod p - 1)`, \
    `dQ < q - 1`, `e dQ ≡ 1 (mod q - 1)`, `qInv < p` and `q qInv ≡ 1 (mod p)`; and 0 \
    otherwise. Like `RSA_check_key`, it does not check that `p` and `q` are prime; if they \
    are, `vg_rsa_private_checked` never returns its internal error for a key it accepts.\n\n\
    Contract: `VG.Spec.Rsa.checkKeyContract`. Constant time but for the public key: timing \
    may depend on the pointers, the lengths and the contents of `n` and `e`, not on the \
    private key."
  safety := ["`n_len` must be in 64..=1024.", "`e_len` and `d_len` must be in 1..=`n_len`.",
    "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++ scratchSafety

/-! ### `vg_rsa_check_crt_key` -/

/-- `vg_rsa_check_crt_key(n: *const u8, n_len: usize, e: *const u8,
e_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize,
dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize,
qinv: *const u8, qinv_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def checkCrtKeySig : Sig where
  params := [("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("dp", .slice false .u8 "dp_len"), ("dq", .slice false .u8 "dq_len"),
    ("qinv", .slice false .u8 "qinv_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The checks of BoringSSL's `RSA_check_key` on the CRT form
`(n, e, p, q, dP, dQ, qInv)` of a private key (`checkCrtKey`): 1 if they
accept the key, 0 if not. Constant time but for the public key. -/
def checkCrtKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkCrtKeySig.contract A
    (pre := fun _n nLen _e eLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv qinvLen _scratch
        scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv _qinvLen _scratch
        _scratchLen m _m' r =>
      r = if checkCrtKey (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq _dqLen _qinv _qinvLen
        _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

def checkCrtKeyApi : Api where
  module := "rsa"
  name := "vg_rsa_check_crt_key"
  sig := checkCrtKeySig
  writeArgs := true
  contracts := some fun A stack => checkCrtKeyContract A stack
  summary := "Checks the CRT form `(n, e, p, q, dP, dQ, qInv)` of an RSA private key as \
    BoringSSL's `RSA_check_key` checks it, without the private exponent `d`, which the \
    private-key operations do not use. With the modulus `n` (`n_len` bytes), the public \
    exponent `e` (`e_len` bytes), `p`, `dp` and `qinv` (`p_len` bytes) and `q` and `dq` \
    (`q_len` bytes), all most significant first, returns 1 if `n` is odd, from 512 to 8192 \
    bits and its first byte not zero, `e` is odd and from 3 to `2^33 - 1`, `p q = n`, \
    `dP < p - 1`, `e dP ≡ 1 (mod p - 1)`, `dQ < q - 1`, `e dQ ≡ 1 (mod q - 1)`, \
    `qInv < p` and `q qInv ≡ 1 (mod p)`; and 0 otherwise. It does not check that `p` and `q` \
    are prime; if they are, `vg_rsa_private_checked` never returns its internal error for a \
    key it accepts.\n\n\
    Contract: `VG.Spec.Rsa.checkCrtKeyContract`. Constant time but for the public key: timing \
    may depend on the pointers, the lengths and the contents of `n` and `e`, not on the \
    private key."
  safety := ["`n_len` must be in 64..=1024.", "`e_len` must be in 1..=`n_len`.",
    "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++ scratchSafety

end VG.Spec.Rsa
