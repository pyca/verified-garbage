module

public import VerifiedGarbage.Spec.Ffdh.Contract

/-!
# Finite-field Diffie–Hellman: deriving an imported scalar's public value

**Trusted.** A new API, `vg_ffdh_derive_public`: the key pair of an imported
private scalar x alone, `privateFrom` of `g^x mod p` and x, with its status
`keyStatus`, as `vg_ffdh_generate_key` reports it for a generated scalar.

Importing x alone with `vg_ffdh_exchange` (the peer value g) and then
`vg_ffdh_check_private` computes `g^x mod p` twice, once to derive y and
once to check it; this computes it once. As for the other functions on an
imported x, timing may depend on the domain, the lengths and the status,
and the exponentiation may run over x's `x_len` octets, its public encoding
length, leading zeros included.
-/

@[expose] public section

namespace VG.Spec.Ffdh

open VG.Spec.Rsa (bytesAt os2ip i2osp powMod scratchWords)

/-- `vg_ffdh_derive_public(y: *mut u8, y_len: usize, domain: *const u8,
domain_len: usize, p_len: usize, x: *const u8, x_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def derivePublicSig : Sig where
  params := [("y", .slice true .u8 "y_len"), ("domain", .slice false .u8 "domain_len"),
    ("p_len", .int .usize true), ("x", .slice false .u8 "x_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- For a valid domain, `keyStatus` of the imported x, and for 1 the public
value `g^x mod p` at `y`, `p_len` octets; zeros otherwise. Timing may depend
on the domain and the status, not otherwise on x. -/
def derivePublicContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  derivePublicSig.contract A
    (pre := fun _y yLen _domain domainLen pLen _x xLen _scratch scratchLen _ =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
        yLen.toNat = pLen.toNat ∧ 1 ≤ xLen.toNat ∧ xLen.toNat ≤ pLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun y _yLen domain domainLen pLen x xLen _scratch _scratchLen m m' r =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let s := os2ip (bytesAt m x xLen.toNat)
      domainValid pLen.toNat dom →
        r.toNat = keyStatus a s ∧
          if keyStatus a s = 1 then bytesAt m' y pLen.toNat = i2osp (powMod a.g s a.p) pLen.toNat
          else bytesAt m' y pLen.toNat = List.replicate pLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _y _yLen domain domainLen pLen x xLen _scratch _scratchLen m =>
      let dom := bytesAt m domain domainLen.toNat
      dom.map (·.toNat) ++ [keyStatus (domainOf pLen.toNat dom) (os2ip (bytesAt m x xLen.toNat))])

def derivePublicApi : Api where
  module := "ffdh"
  name := "vg_ffdh_derive_public"
  sig := derivePublicSig
  writeArgs := true
  contracts := some fun A stack => derivePublicContract A stack
  summary := "Derives the public value of an imported finite-field Diffie–Hellman private \
    key (SP 800-56A Rev. 3 §5.6.2.1.2 for x's range, §5.6.1.1 for `y = g^x mod p`). \
    With `domain` as `vg_ffdh_check_domain` takes it and x (`x_len` bytes, most \
    significant first): \
    returns 2 if x is not in `1..q` (`1..p − 1` without q); 1 if `y = g^x mod p` is a \
    valid public value (as `vg_ffdh_check_public` checks it), writing y (`p_len` bytes, \
    most significant first) to `y`; 3 otherwise. Writes zeros to `y` unless it returns \
    1.\n\n\
    Contract: `VG.Spec.Ffdh.derivePublicContract`. Timing may depend on the pointers, \
    the lengths, the domain and the value returned, not otherwise on x; the \
    exponentiation may run over all `x_len` bytes of x, leading zeros included."
  safety := domainSafety ++ ["`y_len` must be `p_len`.", "`x_len` must be in 1..=`p_len`.",
    checkedSafety] ++ scratchSafety

end VG.Spec.Ffdh
