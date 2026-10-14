module

public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Rsa.Mont

/-!
# A shared, callable Miller–Rabin round

**Trusted.** One strong probable-prime test (FIPS 186-5 Appendix B.3.1,
steps 4.3–4.5), using the same mathematical test as RSA key generation.
This is a round, not a primality certificate or a witness-sampling policy.
RSA and FFDH keep their own witness counts and rejection-sampling policies.

The input is an already prepared Montgomery workspace, so a caller can
reuse the modulus and exponent preparation across witnesses. Array 5 holds
the witness in Montgomery form. The additional arrays hold Montgomery one,
minus one, the shifted exponent, and a table of sixteen powers. The two
layouts below describe the existing RSA workspaces; they have identical
mathematical semantics. A registration selects its layout, and CPU variants
must use that same layout and contract.

All numbers, including the candidate, witness and exponent, are secret.
Only the workspace address, capacity and number of limbs may affect timing.
The caller decides whether to release the result of the test. The contract
does not release a rejected candidate or a failing witness as timing data.
-/

@[expose] public section

namespace VG.Spec.MillerRabin

open VG.Spec.Rsa (splitTwos)
open VG.Spec.Rsa.Mont (wordAt wOf numAt arrAt)

/-- One strong probable-prime test, with the decomposition of candidate-1
computed mathematically rather than supplied as a trusted input. -/
def round (candidate witness : Nat) : Bool :=
  let (a, m) := splitTwos (candidate - 1)
  RsaKeyGen.mrIteration candidate a m witness

/-- A shift in 1..=4 congruent to the exponent of two in candidate-1
modulo four. It aligns the lowest nonzero exponent window. -/
def shift (candidate : Nat) : Nat :=
  let a := (splitTwos (candidate - 1)).1
  if a % 4 = 0 then 4 else a % 4

def exponent (candidate : Nat) : Nat := (candidate - 1) / 2 ^ shift candidate

/-- Additional arrays and temporary header words in a prepared workspace.
Indices and offsets describe representations, not different algorithms. -/
structure Workspace where
  table : Nat
  base : Nat
  exponent : Nat
  one : Nat
  minusOne : Nat
  flag : Nat
  value : Nat
  words : Nat
  windows : Nat
  digit : Nat
  stride : Option Nat
  deriving DecidableEq, Repr

/-- The representation with the witness occupying table entry one. -/
def extended : Workspace := ⟨8, 9, 24, 25, 26, 22, 26, 27, 28, 31, none⟩

/-- The representation with separate witness, one and minus-one arrays. -/
def compact : Workspace := ⟨11, 8, 27, 9, 10, 23, 26, 29, 30, 1, some 28⟩

/-- The first eight arrays use the Montgomery multiplication contract's
layout. The extra arrays fit, with a maximum of 8192-bit candidates. -/
def Layout (L : Workspace) (m : Mem) (ws : Addr) (wsLen : Nat) : Prop :=
  let w := wOf m ws
  (L = extended ∨ L = compact) ∧
    Rsa.Mont.Layout m ws wsLen ∧ 4 ≤ w ∧ w ≤ 128 ∧
    arrAt w (max (L.table + 16) (max (L.exponent + 1) (max (L.one + 1) (L.minusOne + 1)))) ≤
      8 * wsLen ∧
    match L.stride with
    | none => True
    | some k => wordAt m ws k = BitVec.ofNat 64 (8 * (w + 2))

/-- Mathematical initialization of the candidate, witness and exponent.
No assumption says the candidate is prime. -/
def Prepared (L : Workspace) (m : Mem) (ws : Addr) : Prop :=
  let w := wOf m ws
  let c := numAt m ws w 0
  let R := 2 ^ (64 * w)
  3 ≤ c ∧ c % 2 = 1 ∧
    ((m.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64).toNat *
      (wordAt m ws Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0 ∧
    numAt m ws w 5 < c ∧
    numAt m ws w L.one = R % c ∧ numAt m ws w L.minusOne = c - R % c ∧
    numAt m ws w L.exponent = exponent c ∧
    m.readW (ws + BitVec.ofNat 64 (arrAt w L.exponent + 8 * w)) 64 =
      BitVec.twoPow 64 ((splitTwos (c - 1)).1 % 64)

/-- Only the table, accumulator, temporary, selected witness, copied base
and five counter/flag words may change. In particular, the modulus,
Montgomery header, prepared exponent and constants remain reusable. -/
def Keeps (L : Workspace) (ws : Addr) (wsLen w : Nat) (m m' : Mem) : Prop :=
  ∀ i < 8 * wsLen,
    (∀ k ∈ [L.flag, L.value, L.words, L.windows, L.digit], i < 8 * k ∨ 8 * k + 8 ≤ i) →
    (∀ j ∈ [2, 3, 5, 6, L.base], i < arrAt w j ∨ arrAt w j + 8 * (w + 2) ≤ i) →
    (i < arrAt w L.table ∨ arrAt w (L.table + 16) ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

def roundSig : Sig where
  params := [("ws", .slice true .u64 "ws_len")]
  ret := some .u32

/-- Returns 1 exactly when the witness passes one Miller–Rabin round.
The implication quantifies over the ordinary witness represented by array
5: congruent witnesses have the same test result. The input is already in
Montgomery form, avoiding conversion or modulus preparation on each call. -/
def roundContract {I : ISA} (A : Abi I) (L : Workspace) (stack : Nat := 0) : Contract I :=
  roundSig.contract A
    (pre := fun ws wsLen m => Layout L m ws wsLen.toNat ∧ Prepared L m ws)
    (post := fun ws wsLen m m' r =>
      let w := wOf m ws
      let c := numAt m ws w 0
      (∀ b, numAt m ws w 5 = b % c * 2 ^ (64 * w) % c →
        r.toNat = if round c b then 1 else 0) ∧
      Keeps L ws wsLen.toNat w m m')
    (stack := stack)
    (leak := some fun ws _ m => [wOf m ws])

/-- The same callable algorithm for both representations. The selected
representation is reflected in its contract and emitted safety documentation. -/
def roundApi (L : Workspace) : Api where
  module := "miller_rabin"
  name := "vg_miller_rabin_round"
  sig := roundSig
  contracts := some fun A stack => roundContract A L stack
  summary := "One strong Miller–Rabin round (FIPS 186-5 Appendix B.3.1, steps 4.3–4.5) \
    in a prepared RSA Montgomery workspace. Returns 1 if the witness passes, 0 otherwise. \
    Uses fixed windows of four bits, with no witness-dependent table address. This is \
    neither a primality certificate nor a choice of witness distribution or round count. \
    The caller supplies those policies.\n\n\
    Contract: `VG.Spec.MillerRabin.roundContract`. Timing may depend on the pointers, \
    lengths and limb count, not on the candidate, witness, exponent or test result."
  safety := ["`ws` must satisfy `VG.Spec.MillerRabin.Layout` and \
      `VG.Spec.MillerRabin.Prepared` for the representation below; in particular its \
      Montgomery header must be initialized, with 4..=128 limbs and an odd candidate >= 3.",
    s!"The power table begins at array {L.table}, the copied base is array {L.base}, \
      the shifted exponent is array {L.exponent}, Montgomery one is array {L.one}, \
      and Montgomery minus one is array {L.minusOne}. Array 5 contains the witness \
      in Montgomery form. Arrays have `w + 2` words after the 32-word header.",
    s!"After the exponent's `w` words, one word holds `2^((v2(candidate-1)) mod 64)`. \
      The exponent is `(candidate-1) / 2^sigma`, for sigma in 1..=4 congruent to \
      `v2(candidate-1)` modulo 4. Header words {L.flag}, {L.value}, {L.words}, \
      {L.windows}, {L.digit} and the table and working arrays may change.",
    match L.stride with
    | none => "This representation computes array strides from the public limb count."
    | some k => s!"Header word {k} must hold the array stride `8 * (w + 2)` in bytes.",
    "The working space may contain secrets on return and must be destroyed after use."]

end VG.Spec.MillerRabin
