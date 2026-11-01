module

public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# A shared, callable Miller–Rabin round

Not trusted: the contract of an internal function (`Rust.Internal`), which only
verified code calls, that its proofs and its callers' compose.

`vg_miller_rabin_round`: one strong probable-prime test (FIPS 186-5 Appendix B.3.1,
steps 4.3–4.5), using the same mathematical test as RSA key generation.
This is a round, not a primality certificate or a witness-sampling policy.
RSA and FFDH keep their own witness counts and rejection-sampling policies.

The input is an already prepared Montgomery workspace, so a caller can
reuse the modulus and exponent preparation across witnesses. Array 5 holds
the witness in Montgomery form. The additional arrays hold Montgomery one,
minus one, the shifted exponent, and a table of sixteen powers. The two
layouts below describe the existing RSA workspaces; they have identical
mathematical semantics. A target's code selects its layout, and CPU variants
must use that same layout and contract.

All numbers, including the candidate, witness and exponent, are secret.
Only the workspace address, capacity and number of limbs may affect timing.
The caller decides whether to release the result of the test. The contract
does not release a rejected candidate or a failing witness as timing data.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Round

open VG.Spec
open VG.Spec.Rsa (splitTwos)
open VG.Proof.Rsa.Mont (wordAt wOf numAt arrAt)

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

end VG.Proof.MillerRabin.Round
