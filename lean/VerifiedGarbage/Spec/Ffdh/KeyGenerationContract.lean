module

public import VerifiedGarbage.Spec.Ffdh.KeyGeneration

/-! # Complete native private-key generation across entropy refills -/

@[expose] public section

namespace VG.Spec.Ffdh

open VG.Spec.Rsa (bytesAt wordsAt i2osp)

def keyInitSig : Sig where
  params := [("state", .array true .u64 16), ("p_len", .int .usize true)]
  ret := some .u32

def keyInitContract {M : ISA} (A : Abi M) : Contract M :=
  keyInitSig.contract A
    (post := fun state len _ m' r =>
      match keyInit len.toNat with
      | none => r.toNat = 0 ∧ wordsAt m' state 4 = List.replicate 4 0
      | some values => r.toNat = 1 ∧ wordsAt m' state 4 = values.map (BitVec.ofNat 64))

def keyInitApi : Api where
  module := "ffdh"
  name := "vg_ffdh_key_generation_init"
  sig := keyInitSig
  contracts := some fun A _ => keyInitContract A
  summary := "Initialize native finite-field Diffie–Hellman key generation. Returns 1 \
    for a domain width in 64..=1024 bytes, initializing the rejection budgets and \
    first entropy request; returns 0 and clears the first four state words otherwise. \
    The remaining state words are private workspace. Contract: `VG.Spec.Ffdh.keyInitContract`."
  safety := []

/-- `vg_ffdh_generate_key_search(x: *mut u8, x_len: usize, y: *mut u8, y_len: usize,
used: *mut [u64; 1], domain: *const u8, domain_len: usize, p_len: usize,
rand: *const u8, rand_len: usize, scratch: *mut u64, scratch_len: usize,
state: *mut [u64; 16]) -> u32`. -/
def keySearchSig : Sig where
  params := [("x", .slice true .u8 "x_len"), ("y", .slice true .u8 "y_len"),
    ("used", .array true .u64 1), ("domain", .slice false .u8 "domain_len"),
    ("p_len", .int .usize true), ("rand", .slice false .u8 "rand_len"),
    ("scratch", .slice true .u64 "scratch_len"), ("state", .array true .u64 16)]
  ret := some .u32

def keySearchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keySearchSig.contract A
    (pre := fun _x xLen _y yLen _used domain domainLen pLen _rand _randLen _scratch scratchLen state m =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
      xLen.toNat = pLen.toNat ∧ yLen.toNat = pLen.toNat ∧
      Spec.Rsa.scratchWords pLen.toNat ≤ scratchLen.toNat ∧
      domainValid pLen.toNat (bytesAt m domain domainLen.toNat) ∧
      (m.readW state 64).toNat ≤ 128 ∧ (m.readW (state + 8) 64).toNat ≤ 128 ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 pLen.toNat)
    (post := fun x _xLen y _yLen used domain domainLen pLen rand randLen _scratch _scratchLen state m m' r =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let result := keySearch a pLen.toNat
        ⟨(m.readW state 64).toNat, (m.readW (state + 8) 64).toNat⟩ (bytesAt m rand randLen.toNat)
      r.toNat = result.status ∧
      (match result.outcome with
        | .accepted sx sy => bytesAt m' x pLen.toNat = i2osp sx pLen.toNat ∧
            bytesAt m' y pLen.toNat = i2osp sy pLen.toNat
        | _ => bytesAt m' x pLen.toNat = List.replicate pLen.toNat 0 ∧
            bytesAt m' y pLen.toNat = List.replicate pLen.toNat 0) ∧
      wordsAt m' state 4 = [BitVec.ofNat 64 result.retries.keys,
        BitVec.ofNat 64 result.retries.scalars, BitVec.ofNat 64 pLen.toNat,
        BitVec.ofNat 64 (if result.status = 0 then pLen.toNat else 0)] ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used])
    (writeArgs := true) (stack := stack)
    (leak := some fun _x _xLen _y _yLen _used domain domainLen pLen rand randLen _scratch _scratchLen state m =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let retries := KeyRetries.mk (m.readW state 64).toNat (m.readW (state + 8) 64).toNat
      dom.map (·.toNat) ++ (wordsAt m state 4).map (·.toNat) ++
        (keySearch a pLen.toNat retries (bytesAt m rand randLen.toNat)).statuses)

def keySearchApi : Api where
  module := "ffdh"
  name := "vg_ffdh_generate_key_search"
  sig := keySearchSig
  writeArgs := true
  contracts := some fun A stack => keySearchContract A stack
  summary := "Generate a finite-field Diffie–Hellman key pair with native rejection sampling. \
    Owns both range-rejection and degenerate-public-value retry budgets. Returns 1 \
    with the key pair, 3 when a budget is exhausted, or 0 to request more entropy. \
    On 0, discard `used` bytes from `rand`, preserve the suffix and extend it \
    to `state[3]` bytes before calling again. On 0 and 3, both outputs are zero. \
    Contract: `VG.Spec.Ffdh.keySearchContract`. Timing may depend on the public domain, \
    controller policy and sequence of attempt statuses, not otherwise on secret scalar bytes."
  safety := domainSafety ++ ["`domain` must be one that `vg_ffdh_check_domain` accepted \
      (returned 1 for): the attempts' statuses, which the controller branches on, are \
      specified only for such a domain.",
    "`state` must be initialized by `vg_ffdh_key_generation_init` for `p_len`, or be the \
      state returned by this routine.",
    "`x_len` and `y_len` must be `p_len`."] ++ scratchSafety

end VG.Spec.Ffdh
