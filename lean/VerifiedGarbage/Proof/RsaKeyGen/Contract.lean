module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract

/-!
# RSA key generation: the contracts of its internal functions

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose. Only the
callers' contracts, in `Spec/`, are trusted.

`vg_rsa_keygen_key`, the key from its two primes (`Spec.RsaKeyGen.keyFromPrimes`),
which `vg_rsa_generate` (`Spec.RsaKeyGen.keySearchContract`) calls for each
pair of primes. An implementation of it may call one helper:
`vg_rsa_keygen_inverse`, a binary extended GCD on numbers in its working space,
so that the code of its several inversions is emitted once.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Spec VG.Spec.RsaKeyGen
open VG.Spec.Rsa (bytesAt os2ip i2osp scratchWords)

/-- The octets of each number of `vg_rsa_keygen_inverse`'s working space for a
length of `len` octets: `8 ⌈len / 8⌉`. -/
def inverseBytes (len : Nat) : Nat := 8 * ((len + 7) / 8)

/-- Number `j` of the working space at `ws` for a length of `len` octets: the
`inverseBytes len` octets at `ws + 160 + j (inverseBytes len + 8)`, least
significant first. The first 160 octets are a header the function may use,
and the 8 octets after each number are working space too. -/
def inverseNum (m : Mem) (ws : Addr) (len j : Nat) : Nat :=
  os2ip (bytesAt m (ws + BitVec.ofNat 64 (160 + j * (inverseBytes len + 8))) (inverseBytes len)).reverse

/-- The octets of the working space `vg_rsa_keygen_inverse` may write, by
offset: the header's octets 100 to 111, and the numbers 0 to 7 and 11 to 14,
each with the 8 octets after it. -/
def inverseWrites (len i : Nat) : Prop :=
  (100 ≤ i ∧ i < 112) ∨ ∃ j, (j < 8 ∨ (11 ≤ j ∧ j < 15)) ∧
    160 + j * (inverseBytes len + 8) ≤ i ∧ i < 160 + (j + 1) * (inverseBytes len + 8)

/-- `vg_rsa_keygen_inverse(ws: *mut u64, ws_len: usize, len: usize)`. -/
def inverseSig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("len", .int .usize true)]

/-- With `a` the number 0 of the working space and `m` the number 8, odd and
more than 1, and the numbers 1, 2, 3, 9 and 10 `m`, 1, 0, `2^(8 B) − m` and
0 (`B = inverseBytes len`): leaves `gcd(a, m)` in the number 1, and in the
number 3 an `x < m` with `x a ≡ gcd(a, m) (mod m)`, which is `a⁻¹ mod m`
when the gcd is 1; it writes nothing else but the octets `inverseWrites`
names. Constant time. -/
def inverseContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  inverseSig.contract A
    (pre := fun ws wsLen len m =>
      1 ≤ len.toNat ∧ len.toNat ≤ 1024 ∧
        160 + 15 * (inverseBytes len.toNat + 8) ≤ 8 * wsLen.toNat ∧
        inverseNum m ws len.toNat 8 % 2 = 1 ∧ 1 < inverseNum m ws len.toNat 8 ∧
        inverseNum m ws len.toNat 1 = inverseNum m ws len.toNat 8 ∧
        inverseNum m ws len.toNat 2 = 1 ∧ inverseNum m ws len.toNat 3 = 0 ∧
        inverseNum m ws len.toNat 9 + inverseNum m ws len.toNat 8 = 2 ^ (8 * inverseBytes len.toNat) ∧
        inverseNum m ws len.toNat 10 = 0)
    (post := fun ws wsLen len m m' _ =>
      (∀ i, i < 8 * wsLen.toNat → ¬ inverseWrites len.toNat i →
        m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)) ∧
      inverseNum m' ws len.toNat 1 = Nat.gcd (inverseNum m ws len.toNat 0) (inverseNum m ws len.toNat 8) ∧
        (inverseNum m ws len.toNat 8 : Int) ∣
          (inverseNum m' ws len.toNat 3 : Int) * inverseNum m ws len.toNat 0 - inverseNum m' ws len.toNat 1 ∧
        inverseNum m' ws len.toNat 3 < inverseNum m ws len.toNat 8)
    (stack := stack)

/-! ## `vg_rsa_keygen_key` -/

/-- `keyFromPrimes` for primes of `pLen` octets: the key, as octets: `n` and
`d` of `2 pLen`, and `p`, `q`, `dP`, `dQ` and `qInv` of `pLen`. -/
def keyOp (pLen : Nat) (eB pB qB : List Byte) : Except Failure (List (List Byte)) ⊕ Unit :=
  match keyFromPrimes (16 * pLen) (os2ip eB) (os2ip pB) (os2ip qB) with
  | .inl (.ok k) =>
    .inl (.ok [i2osp k.n (2 * pLen), i2osp k.d (2 * pLen), i2osp k.p pLen, i2osp k.q pLen,
      i2osp k.dP pLen, i2osp k.dQ pLen, i2osp k.qInv pLen])
  | .inl (.error f) => .inl (.error f)
  | .inr () => .inr ()

/-- The status `vg_rsa_keygen_key` returns. -/
def keyStatus : Except Failure (List (List Byte)) ⊕ Unit → Nat
  | .inl (.ok _) => 1
  | .inr () => 2
  | .inl (.error _) => 0

/-- `vg_rsa_keygen_key(n: *mut u8, n_len: usize, d: *mut u8, d_len: usize,
p: *mut u8, p_len: usize, q: *mut u8, q_len: usize, dp: *mut u8,
dp_len: usize, dq: *mut u8, dq_len: usize, qinv: *mut u8, qinv_len: usize,
e: *const u8, e_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def keySig : Sig where
  params := [("n", .slice true .u8 "n_len"), ("d", .slice true .u8 "d_len"),
    ("p", .slice true .u8 "p_len"), ("q", .slice true .u8 "q_len"),
    ("dp", .slice true .u8 "dp_len"), ("dq", .slice true .u8 "dq_len"),
    ("qinv", .slice true .u8 "qinv_len"), ("e", .slice false .u8 "e_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The key from the primes at `p` and `q` (`keyOp`): 1 and the key at `n`,
`d`, `p`, `q`, `dp`, `dq` and `qinv`; 2 if `d` is too small, to generate the
primes again; 0 if a check failed; zeros at all seven but for 1. Constant
time but for `e` and the status. -/
def keyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keySig.contract A
    (pre := fun _n nLen _d dLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv qinvLen _e eLen
        _scratch scratchLen _ =>
      primeLenValid pLen.toNat ∧ nLen.toNat = 2 * pLen.toNat ∧ dLen.toNat = nLen.toNat ∧
        qLen.toNat = pLen.toNat ∧ dpLen.toNat = pLen.toNat ∧ dqLen.toNat = pLen.toNat ∧
        qinvLen.toNat = pLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ 8 ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun n nLen d _dLen p pLen q _qLen dp _dpLen dq _dqLen qinv _qinvLen e eLen
        _scratch _scratchLen m m' r =>
      let res := keyOp pLen.toNat (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
        (bytesAt m q pLen.toNat)
      let outs := [(n, nLen.toNat), (d, nLen.toNat), (p, pLen.toNat), (q, pLen.toNat),
        (dp, pLen.toNat), (dq, pLen.toNat), (qinv, pLen.toNat)]
      r.toNat = keyStatus res ∧
        match res with
        | .inl (.ok ys) => outs.map (fun o => bytesAt m' o.1 o.2) = ys
        | _ => ∀ o ∈ outs, bytesAt m' o.1 o.2 = List.replicate o.2 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _n _nLen _d _dLen p pLen q _qLen _dp _dpLen _dq _dqLen _qinv _qinvLen e
        eLen _scratch _scratchLen m =>
      (bytesAt m e eLen.toNat).map (·.toNat) ++
        [keyStatus (keyOp pLen.toNat (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m q pLen.toNat))])

end VG.Proof.RsaKeyGen
