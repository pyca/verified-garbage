module

public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSA primitives: the contracts of their internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

* `vg_rsa_private_crt`: RSADP and RSASP1 with the private key
  `(p, q, dP, dQ, qInv)` (`Rsa.privateCrt`), the operation that
  `vg_rsa_private_checked` checks;
* `vg_rsa_public_checked`: RSAEP and RSAVP1 (`Rsa.publicOp`) within
  BoringSSL's limits on the public exponent (`Rsa.publicOpChecked`), given
  the modulus itself, for the code of the RSA padding functions that call it;
* `vg_rsa_public_precomputed_checked`: the same, from the values
  `vg_rsa_public_precompute` computed (`Rsa.publicPrecompute`), without
  computing them again;
* `vg_rsa_private_checked`: `vg_rsa_private_crt`'s operation given the
  public exponent too, releasing a result only if it passes BoringSSL's
  check against it (`Rsa.privateChecked`), or returning 2 and writing zeros
  on its internal error;
* `vg_rsa_check_crt_key`: the checks of `vg_rsa_check_key`
  (`Spec.Rsa.checkKeyContract`) on the CRT form `(n, e, p, q, dP, dQ, qInv)`
  alone (`Rsa.checkCrtKey`), which writes nothing. No verified function
  calls it, and it is not emitted: its proofs share their code with
  `vg_rsa_check_key`'s.

Their arguments are as in `Spec/Rsa/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG.Spec.Rsa

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

/-! ## `vg_rsa_public_precomputed_checked` -/

/-- `vg_rsa_public_precomputed_checked(out: *mut u8, out_len: usize, pre: *const u64,
pre_len: usize, e: *const u8, e_len: usize, input: *const u8,
input_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def publicPrecomputedSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("pre", .slice false .u64 "pre_len"),
    ("e", .slice false .u8 "e_len"), ("input", .slice false .u8 "input_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- RSAEP of the input with the public key `(n, e)`, within BoringSSL's
limits, given `n` by its precomputed values (`publicPrecompute`): for
whichever `n_len`-octet modulus `pre` holds the values of, the result
of `publicOpChecked`. If `pre` holds the values of no modulus, the result
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

/-! ## `vg_rsa_private_checked` -/

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

/-! ## `vg_rsa_check_crt_key` -/

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

end VG.Proof.Rsa
