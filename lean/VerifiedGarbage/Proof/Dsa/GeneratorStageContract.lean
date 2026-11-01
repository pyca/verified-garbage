module

public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-!
# DSA's generator search and domain check at fixed offsets of a working space

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

A callable piece of DSA parameter generation:
`vg_dsa_generator_{bits}` runs the last stage of one parameter attempt
(`Spec.Dsa.generateParameters`), once p and q are found: FIPS 186-4
A.2.1's generator search `Spec.Dsa.generator p q hs` over the h candidates
of the `hs` tape, from its front, and then `Spec.Dsa.parametersValid` of
the resulting domain. Parameter generation calls it for every p it accepts,
whatever the hash it derives candidates with, so that every hash backend's
generator calls one copy of it.

p, q and the exponent (p − 1) / q are stored big-endian at fixed offsets
of a working space, as its `Layout` gives them. The function returns 1 when
the search finds a g for which the domain is valid, and then writes
p ‖ q ‖ g (`Spec.Dsa.encodeParams`) at the layout's `packed` offset; it
returns 0 when the search finds no g, or the domain it finds is invalid,
and parameter generation goes on with its next seed. Only the bytes of the
layout's `scratch` ranges may change.

p, q and the h candidates are public: parameter generation discloses all of
its tapes and its output, and the search's running time depends on them
(how many candidates it reads).
-/

@[expose] public section
namespace VG.Proof.Dsa.GeneratorStage

open VG.Spec VG.Spec.Dsa
open VG.Impl.Dsa.GeneratorStage (Layout)
open VG.Spec.Rsa (bytesAt)
open VG.Proof.Dsa.ModPow (Keeps)

/-- The number of `n` big-endian bytes at offset `d` of `ws` in memory `m`. -/
def numberAt (m : Mem) (ws : Addr) (d n : Nat) : Nat :=
  decodeBE (bytesAt m (ws + BitVec.ofNat 64 d) n)

/-- p in memory `m`. -/
def pAt (L : Layout) (m : Mem) (ws : Addr) : Nat := numberAt m ws L.p L.pLen

/-- q in memory `m`. -/
def qAt (L : Layout) (m : Mem) (ws : Addr) : Nat := numberAt m ws L.q L.qLen

/-- The h candidates of a tape of `pLen`-byte chunks. -/
def candidates (pLen : Nat) (hs : List Byte) : List Nat :=
  (generationChunks pLen hs).map decodeBE

/-- The stage: the generator search over `hs`, then the domain check of
what it finds; `none` sends parameter generation on to its next seed. This
is the step of `Spec.Dsa.generateParameters`'s `attempt` that follows
`primeFromSeed`. -/
def stage (p q : Nat) (hs : List Nat) : Option Params := do
  let g ← generator p q hs
  if parametersValid ⟨p, q, g⟩ then some ⟨p, q, g⟩ else none

/-- The working space and the h candidates. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("hs", .slice false .u8 "hs_len")]
  ret := some .u32

/-- For a working space of at least `L.size` bytes holding an odd p of
exactly `8 * L.pLen` bits, a positive q, and the exponent (p − 1) / q, and
a tape of whole `L.pLen`-byte h candidates: 1 with p ‖ q ‖ g at
`L.packed` when `stage` finds parameters, 0 when it does not. Only the
bytes of `L.scratch` may change. p, q and the tape are public. -/
def contract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen _hs hsLen m =>
      let p := pAt L m ws
      let q := qAt L m ws
      L.size ≤ 8 * wsLen.toNat ∧ hsLen.toNat % L.pLen = 0 ∧
        p % 2 = 1 ∧ Spec.Dsa.bitLength p = 8 * L.pLen ∧ 0 < q ∧
        bytesAt m (ws + BitVec.ofNat 64 L.exponent) L.pLen = encodeBE L.pLen ((p - 1) / q))
    (post := fun ws wsLen hs hsLen m m' r =>
      let res := stage (pAt L m ws) (qAt L m ws) (candidates L.pLen (bytesAt m hs hsLen.toNat))
      r.toNat = (if res.isSome then 1 else 0) ∧ Keeps ws wsLen.toNat L.scratch m m' ∧
        ∀ a, res = some a →
          bytesAt m' (ws + BitVec.ofNat 64 L.packed) (2 * L.pLen + L.qLen) =
            encodeParams L.pLen L.qLen a)
    (stack := stack)
    (leak := some fun ws _wsLen hs hsLen m =>
      pAt L m ws :: qAt L m ws :: (bytesAt m hs hsLen.toNat).map (·.toNat))

end VG.Proof.Dsa.GeneratorStage
