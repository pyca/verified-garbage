module

public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# Finite-field Diffie–Hellman: the contracts, on every target

**Trusted** (as every file in `Spec/`). In the module `ffdh`, the whole
operations of `Spec/Ffdh.lean`, so that Rust keeps only the randomness, the
loops over random tapes, allocation and encoding:

* `vg_ffdh_check_domain`: `parametersValid` of imported (p, g, q), with p
  of exactly `p_len` octets (`domainValid`);
* `vg_ffdh_check_public`: `publicValid` of an imported y;
* `vg_ffdh_check_private`: `privateFrom` of an imported (y, x);
* `vg_ffdh_generate_key`: one attempt of `generate`, from random octets;
* `vg_ffdh_exchange`: `exchange`, padded to the modulus' length.

The domain is one buffer, `domain`: p, g and, if `domain_len` is `3 p_len`,
q, each `p_len` octets, most significant first (with leading zeros: g and q
are below p); with `domain_len = 2 p_len` there is no q. p is `p_len` octets
from 64 to 1024 (512 to 8192 bits), and so are y, the peer's public value,
the shared value and a generated x; an imported x is 1 to `p_len` octets.
These are preconditions on public lengths. Rust strips leading zeros from p
(and refuses a p of other lengths, which no valid domain has) and pads the
other values to their widths (refusing a value longer than p, which no valid
domain or key has); everything else about the values is checked here.

`vg_ffdh_check_domain` checks the domain once, on import. The other
functions' results are specified only for a domain it accepts, and,
for `vg_ffdh_exchange`, a peer `vg_ffdh_check_public` accepted, as
the types of the Rust API guarantee: they need not check the domain again
(its subgroup check is an exponentiation). For other inputs their results
are unspecified, but not their memory safety or their timing.

What timing may depend on (`leak`), as the Rust API has documented: the
domain, the public values and the lengths are public; a private scalar and
the random octets of a key are secret, and only the status may depend on
them (whether a sample was in range or gave a degenerate public value,
whether an imported key is consistent, whether the shared value is
degenerate). The exponentiation of an imported x may run over its `x_len`
octets, its public encoding length, leading zeros included. Parameter
generation computes only public values (the candidates and their witnesses),
so its timing may depend on all of them (`GenerationContract.lean`).

`scratch` is working space of at least `16 p_len + 32` `u64`s, whose contents
on return are unspecified. `stack` is the number of bytes below the stack
pointer that an implementation's calls and frames use. The functions may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.Ffdh

open VG.Spec.Rsa (bytesAt wordsAt os2ip i2osp powMod written scratchWords)
open VG.Spec.RsaKeyGen (bitLength Rand)

/-! ## Encodings -/

/-- The bounds on p's length, in octets: 512 to 8192 bits. -/
def pLenValid (pLen : Nat) : Prop := 64 ≤ pLen ∧ pLen ≤ 1024

/-- The lengths of a domain buffer: p and g, and q if there is one. -/
def domainLenValid (pLen domainLen : Nat) : Prop :=
  domainLen = 2 * pLen ∨ domainLen = 3 * pLen

/-- The parameters a domain buffer holds: p, g and, if there are three
components, q. -/
def domainOf (pLen : Nat) (dom : List Byte) : Parameters :=
  ⟨os2ip (dom.take pLen), os2ip ((dom.drop pLen).take pLen),
    if dom.length = 3 * pLen then some (os2ip ((dom.drop (2 * pLen)).take pLen)) else none⟩

/-- `parametersValid`, with p of exactly `pLen` octets (its first octet not
zero), so that the shared value has `pLen` octets. -/
def domainValid (pLen : Nat) (dom : List Byte) : Bool :=
  parametersValid (domainOf pLen dom) && 256 ^ (pLen - 1) ≤ (domainOf pLen dom).p

/-- The `# Safety` items on the working space. -/
def scratchSafety : List String :=
  ["`scratch_len` must be at least `16 * p_len + 32`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-- The `# Safety` items on the domain. -/
def domainSafety : List String :=
  ["`p_len` must be in 64..=1024.", "`domain_len` must be `2 * p_len` or `3 * p_len`."]

/-- The `# Safety` item on a domain the result is specified for. -/
def checkedSafety : String :=
  "For the result to be specified, `domain` must be one that `vg_ffdh_check_domain` \
    accepted (returned 1 for); otherwise it is unspecified."

/-! ## `vg_ffdh_check_domain` -/

/-- `vg_ffdh_check_domain(domain: *const u8, domain_len: usize, p_len: usize,
scratch: *mut u64, scratch_len: usize) -> u32`. -/
def checkDomainSig : Sig where
  params := [("domain", .slice false .u8 "domain_len"), ("p_len", .int .usize true),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- 1 if the domain is valid (`domainValid`), 0 otherwise. Timing may depend
on the domain. -/
def checkDomainContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkDomainSig.contract A
    (pre := fun _domain domainLen pLen _scratch scratchLen _ =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun domain domainLen pLen _scratch _scratchLen m _m' r =>
      r.toNat = if domainValid pLen.toNat (bytesAt m domain domainLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun domain domainLen _pLen _scratch _scratchLen m =>
      (bytesAt m domain domainLen.toNat).map (·.toNat))

def checkDomainApi : Api where
  module := "ffdh"
  name := "vg_ffdh_check_domain"
  sig := checkDomainSig
  writeArgs := true
  contracts := some fun A stack => checkDomainContract A stack
  summary := "Checks imported finite-field Diffie–Hellman parameters (SP 800-56A Rev. 3 \
    §5.5.2, without primality tests). `domain` is p, g and, if `domain_len` is \
    `3 * p_len`, q, each `p_len` bytes, most significant first. Returns 1 if p has \
    512 to 8192 bits, its first byte is not zero and it is odd, `1 < g < p − 1`, and, \
    with q, q is odd, `2 < q < p − 1`, q divides `p − 1` and `g^q mod p = 1`; \
    otherwise 0. Does not test p or q for primality: the caller must establish \
    their provenance.\n\n\
    Contract: `VG.Spec.Ffdh.checkDomainContract`. Timing may depend on the pointers, \
    the lengths and the domain."
  safety := domainSafety ++ scratchSafety

/-! ## `vg_ffdh_check_public` -/

/-- `vg_ffdh_check_public(domain: *const u8, domain_len: usize, p_len: usize,
y: *const u8, y_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def checkPublicSig : Sig where
  params := [("domain", .slice false .u8 "domain_len"), ("p_len", .int .usize true),
    ("y", .slice false .u8 "y_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- For a valid domain, 1 if y is a valid public value (`publicValid`), 0
otherwise. Timing may depend on the domain and y. -/
def checkPublicContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkPublicSig.contract A
    (pre := fun _domain domainLen pLen _y yLen _scratch scratchLen _ =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
        yLen.toNat = pLen.toNat ∧ scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun domain domainLen pLen y yLen _scratch _scratchLen m _m' r =>
      let dom := bytesAt m domain domainLen.toNat
      domainValid pLen.toNat dom →
        r.toNat = if publicValid ⟨domainOf pLen.toNat dom, os2ip (bytesAt m y yLen.toNat)⟩
          then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun domain domainLen _pLen y yLen _scratch _scratchLen m =>
      (bytesAt m domain domainLen.toNat).map (·.toNat) ++
        (bytesAt m y yLen.toNat).map (·.toNat))

def checkPublicApi : Api where
  module := "ffdh"
  name := "vg_ffdh_check_public"
  sig := checkPublicSig
  writeArgs := true
  contracts := some fun A stack => checkPublicContract A stack
  summary := "Checks an imported finite-field Diffie–Hellman public value (SP 800-56A \
    Rev. 3 §5.6.2.3.1, and §5.6.2.3.2 with q). With `domain` as `vg_ffdh_check_domain` \
    takes it and y (`p_len` bytes, most significant first), returns 1 if \
    `1 < y < p − 1` and, with q, `y^q mod p = 1`; otherwise 0.\n\n\
    Contract: `VG.Spec.Ffdh.checkPublicContract`. Timing may depend on the pointers, \
    the lengths, the domain and y."
  safety := domainSafety ++ ["`y_len` must be `p_len`.", checkedSafety] ++ scratchSafety

/-! ## `vg_ffdh_check_private` -/

/-- The status of an imported key pair: 2 if x is out of range, else 1 if
`privateFrom` accepts the pair, else 0. -/
def privateStatus (a : Parameters) (y x : Nat) : Nat :=
  if !privateValid a x then 2 else if (privateFrom a y x).isSome then 1 else 0

/-- `vg_ffdh_check_private(domain: *const u8, domain_len: usize, p_len: usize,
y: *const u8, y_len: usize, x: *const u8, x_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def checkPrivateSig : Sig where
  params := [("domain", .slice false .u8 "domain_len"), ("p_len", .int .usize true),
    ("y", .slice false .u8 "y_len"), ("x", .slice false .u8 "x_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- For a valid domain, `privateStatus` of y and x. Timing may depend on the
domain, y and the status, not otherwise on x. -/
def checkPrivateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkPrivateSig.contract A
    (pre := fun _domain domainLen pLen _y yLen _x xLen _scratch scratchLen _ =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
        yLen.toNat = pLen.toNat ∧ 1 ≤ xLen.toNat ∧ xLen.toNat ≤ pLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun domain domainLen pLen y yLen x xLen _scratch _scratchLen m _m' r =>
      let dom := bytesAt m domain domainLen.toNat
      domainValid pLen.toNat dom →
        r.toNat = privateStatus (domainOf pLen.toNat dom) (os2ip (bytesAt m y yLen.toNat))
          (os2ip (bytesAt m x xLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun domain domainLen pLen y yLen x xLen _scratch _scratchLen m =>
      let dom := bytesAt m domain domainLen.toNat
      let yB := bytesAt m y yLen.toNat
      dom.map (·.toNat) ++ yB.map (·.toNat) ++
        [privateStatus (domainOf pLen.toNat dom) (os2ip yB) (os2ip (bytesAt m x xLen.toNat))])

def checkPrivateApi : Api where
  module := "ffdh"
  name := "vg_ffdh_check_private"
  sig := checkPrivateSig
  writeArgs := true
  contracts := some fun A stack => checkPrivateContract A stack
  summary := "Checks an imported finite-field Diffie–Hellman key pair (SP 800-56A Rev. 3 \
    §5.6.2.1.2 and §5.6.2.1.4). With `domain` as `vg_ffdh_check_domain` takes it, y \
    (`p_len` bytes) and x (`x_len` bytes), most significant first: returns 2 if x is \
    not in `1..q` (`1..p − 1` without q); 1 if y is a valid public value (as \
    `vg_ffdh_check_public` checks it) and `y = g^x mod p`; 0 otherwise.\n\n\
    Contract: `VG.Spec.Ffdh.checkPrivateContract`. Timing may depend on the pointers, \
    the lengths, the domain, y and the value returned, not otherwise on x; the \
    exponentiation may run over all `x_len` bytes of x, leading zeros included."
  safety := domainSafety ++ ["`y_len` must be `p_len`.", "`x_len` must be in 1..=`p_len`.",
    checkedSafety] ++ scratchSafety

/-! ## `vg_ffdh_generate_key` -/

/-- The status of a key-generation attempt with the scalar x: 1 if it gives
a key (`privateFrom` of `g^x mod p` and x), 2 if x is out of range, 3 if
the public value is not valid. -/
def keyStatus (a : Parameters) (x : Nat) : Nat :=
  if !privateValid a x then 2 else if (privateFrom a (powMod a.g x a.p) x).isSome then 1 else 3

/-- `vg_ffdh_generate_key(x: *mut u8, x_len: usize, y: *mut u8, y_len: usize,
domain: *const u8, domain_len: usize, p_len: usize, rand: *const u8,
rand_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def generateKeySig : Sig where
  params := [("x", .slice true .u8 "x_len"), ("y", .slice true .u8 "y_len"),
    ("domain", .slice false .u8 "domain_len"), ("p_len", .int .usize true),
    ("rand", .slice false .u8 "rand_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- For a valid domain, one attempt of `generate` with the scalar
`scalarOfOctets` of `rand`: `keyStatus`, and for 1 the scalar and the public
value at `x` and `y`, `p_len` octets each; zeros at both otherwise. Timing
may depend on the domain and the status, not otherwise on `rand`. -/
def generateKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  generateKeySig.contract A
    (pre := fun _x xLen _y yLen _domain domainLen pLen _rand randLen _scratch scratchLen _ =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
        xLen.toNat = pLen.toNat ∧ yLen.toNat = pLen.toNat ∧ randLen.toNat = pLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun x _xLen y _yLen domain domainLen pLen rand randLen _scratch _scratchLen m m' r =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let s := scalarOfOctets a (bytesAt m rand randLen.toNat)
      domainValid pLen.toNat dom →
        r.toNat = keyStatus a s ∧
          if keyStatus a s = 1 then
            bytesAt m' x pLen.toNat = i2osp s pLen.toNat ∧
              bytesAt m' y pLen.toNat = i2osp (powMod a.g s a.p) pLen.toNat
          else bytesAt m' x pLen.toNat = List.replicate pLen.toNat 0 ∧
            bytesAt m' y pLen.toNat = List.replicate pLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _x _xLen _y _yLen domain domainLen pLen rand randLen _scratch _scratchLen m =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      dom.map (·.toNat) ++ [keyStatus a (scalarOfOctets a (bytesAt m rand randLen.toNat))])

def generateKeyApi : Api where
  module := "ffdh"
  name := "vg_ffdh_generate_key"
  sig := generateKeySig
  writeArgs := true
  contracts := some fun A stack => generateKeyContract A stack
  summary := "One attempt at a finite-field Diffie–Hellman key pair (SP 800-56A Rev. 3 \
    §5.6.1.1.4, rejection sampling). With `domain` as `vg_ffdh_check_domain` takes it, \
    takes `rand` (`p_len` random bytes, most significant first) modulo `2^b`, where b is \
    the bit length of q (of `p − 1` without q), as x. Returns 2 if x is not in `1..q` \
    (`1..p − 1`); 3 if `y = g^x mod p` is not a valid public value (as \
    `vg_ffdh_check_public` checks it); otherwise 1, and writes x and y (`p_len` bytes \
    each, most significant first) to `x` and `y`. `x` and `y` are zeros but for 1. For \
    2 and 3 the caller tries again with fresh random bytes.\n\n\
    Contract: `VG.Spec.Ffdh.generateKeyContract`. Timing may depend on the pointers, \
    the lengths, the domain and the value returned, not otherwise on `rand` or x; the \
    exponentiation may run over the bytes of q (`p − 1`)."
  safety := domainSafety ++ ["`x_len`, `y_len` and `rand_len` must be `p_len`.",
    checkedSafety] ++ scratchSafety

/-! ## `vg_ffdh_exchange` -/

/-- The shared value of the scalar x with the peer's public value y in the
domain `a`: `exchange`, which needs of the private key only its domain and
x. -/
def exchangeOp (a : Parameters) (x y : Nat) : Option (List Byte) :=
  exchange ⟨⟨a, powMod a.g x a.p⟩, x⟩ ⟨a, y⟩

/-- `vg_ffdh_exchange(out: *mut u8, out_len: usize, domain: *const u8,
domain_len: usize, p_len: usize, x: *const u8, x_len: usize, peer: *const u8,
peer_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def exchangeSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("domain", .slice false .u8 "domain_len"),
    ("p_len", .int .usize true), ("x", .slice false .u8 "x_len"),
    ("peer", .slice false .u8 "peer_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- For a valid domain and a valid peer, `exchangeOp`: 1 and the shared value
at `out`, or 0 and zeros. Timing may depend on the domain, the peer and the
status, not otherwise on x. -/
def exchangeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  exchangeSig.contract A
    (pre := fun _out outLen _domain domainLen pLen _x xLen _peer peerLen _scratch scratchLen _ =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
        outLen.toNat = pLen.toNat ∧ peerLen.toNat = pLen.toNat ∧ 1 ≤ xLen.toNat ∧
        xLen.toNat ≤ pLen.toNat ∧ scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen domain domainLen pLen x xLen peer peerLen _scratch _scratchLen m m' r =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let y := os2ip (bytesAt m peer peerLen.toNat)
      domainValid pLen.toNat dom → publicValid ⟨a, y⟩ →
        written m' out outLen.toNat r (exchangeOp a (os2ip (bytesAt m x xLen.toNat)) y))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen domain domainLen pLen x xLen peer peerLen _scratch _scratchLen m =>
      let dom := bytesAt m domain domainLen.toNat
      let yB := bytesAt m peer peerLen.toNat
      dom.map (·.toNat) ++ yB.map (·.toNat) ++
        [if (exchangeOp (domainOf pLen.toNat dom) (os2ip (bytesAt m x xLen.toNat))
          (os2ip yB)).isSome then 1 else 0])

def exchangeApi : Api where
  module := "ffdh"
  name := "vg_ffdh_exchange"
  sig := exchangeSig
  writeArgs := true
  contracts := some fun A stack => exchangeContract A stack
  summary := "Finite-field Diffie–Hellman (SP 800-56A Rev. 3 §5.7.1.1, PKCS #3 §8). With \
    `domain` as `vg_ffdh_check_domain` takes it, the private scalar x (`x_len` bytes) and \
    the peer's public value y (`p_len` bytes), most significant first, computes \
    `z = y^x mod p`; returns 0 and writes zeros if z is 0, 1 or `p − 1`, and otherwise \
    returns 1 and writes z (`p_len` bytes, most significant first) to `out`. Applies no \
    KDF.\n\n\
    Contract: `VG.Spec.Ffdh.exchangeContract`. Timing may depend on the pointers, the \
    lengths, the domain, y and the value returned, not otherwise on x; the \
    exponentiation may run over all `x_len` bytes of x, leading zeros included."
  safety := domainSafety ++ ["`out_len` and `peer_len` must be `p_len`.",
    "`x_len` must be in 1..=`p_len`.", checkedSafety,
    "For the result to be specified, `peer` must also be a value that \
      `vg_ffdh_check_public` accepted for this domain."] ++ scratchSafety

end VG.Spec.Ffdh
