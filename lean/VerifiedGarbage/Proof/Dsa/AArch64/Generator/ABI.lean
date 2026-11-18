module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Dsa.HelperLayout
public import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount

/-! ### `Dsa.GeneratorStageContract`, which this module and modules that import it used -/

section

/-!
# DSA's generator search and domain check at fixed offsets of a working space

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

A callable piece of DSA parameter generation:
`vg_dsa_generator_{bits}` runs the last stage of one seed of the
refillable-tape parameter search (`Spec.Dsa.seedCandidate`), once p and q
are found: FIPS 186-4 A.2.1's generator search `Spec.Dsa.generator p q hs`
over the h candidates of the `hs` tape, from its front, and then
`Spec.Dsa.parametersValid` of the resulting domain. Parameter generation
calls it for every p it accepts, whatever the hash it derives candidates
with, so that every hash backend's generator calls one copy of it.

p, q and the exponent (p − 1) / q are stored big-endian at fixed offsets
of a working space, as its `Layout` gives them. The function returns
`code + 4 * read`, where `read` is the octets of the candidates the search
read (`generatorCount`) and `code` is 1 when the search finds a g for which
the domain is valid, and then writes p ‖ q ‖ g (`Spec.Dsa.encodeParams`) at
the layout's `packed` offset; 2 when the domain it finds is invalid; and 3
when it finds no g. Only the bytes of the layout's `scratch` ranges may
change.

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
is the step of a seed's candidate that follows `primeFromSeed`. -/
def stage (p q : Nat) (hs : List Nat) : Option Params := do
  let g ← generator p q hs
  if parametersValid ⟨p, q, g⟩ then some ⟨p, q, g⟩ else none

/-- How the stage ends: 1 with valid parameters, 2 with a g whose domain is
invalid, 3 without a g. -/
def code (p q : Nat) (hs : List Nat) : Nat :=
  match generator p q hs with
  | none => 3
  | some g => if parametersValid ⟨p, q, g⟩ then 1 else 2

/-- The stage's return value: `code`, and the octets of the candidates the
search read. -/
def result (pLen p q : Nat) (hs : List Nat) : Nat :=
  code p q hs + 4 * (pLen * VG.Proof.Dsa.Generation.generatorCount p q hs)

/-- The working space and the h candidates. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("hs", .slice false .u8 "hs_len")]
  ret := some .u64

/-- For a working space of at least `L.size` bytes holding an odd p of
exactly `8 * L.pLen` bits, a positive q, and the exponent (p − 1) / q, and
a tape of `L.pLen`-byte h candidates: `result`, with p ‖ q ‖ g at
`L.packed` when `stage` finds parameters. Only the bytes of `L.scratch` may
change. p, q and the tape are public. -/
def contract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen _hs _hsLen m =>
      let p := pAt L m ws
      let q := qAt L m ws
      L.size ≤ 8 * wsLen.toNat ∧
        p % 2 = 1 ∧ Spec.Dsa.bitLength p = 8 * L.pLen ∧ 0 < q ∧
        bytesAt m (ws + BitVec.ofNat 64 L.exponent) L.pLen = encodeBE L.pLen ((p - 1) / q))
    (post := fun ws wsLen hs hsLen m m' r =>
      let res := stage (pAt L m ws) (qAt L m ws) (candidates L.pLen (bytesAt m hs hsLen.toNat))
      r = BitVec.ofNat 64 (result L.pLen (pAt L m ws) (qAt L m ws) (candidates L.pLen (bytesAt m hs hsLen.toNat))) ∧
        Keeps ws wsLen.toNat L.scratch m m' ∧
        ∀ a, res = some a →
          bytesAt m' (ws + BitVec.ofNat 64 L.packed) (2 * L.pLen + L.qLen) =
            encodeParams L.pLen L.qLen a)
    (stack := stack)
    (leak := some fun ws _wsLen hs hsLen m =>
      pAt L m ws :: qAt L m ws :: (bytesAt m hs hsLen.toNat).map (·.toNat))

end VG.Proof.Dsa.GeneratorStage

end

end

/-! # The generator stage's arguments, from its contract's precondition

The stage's contract asks for 288 bytes of stack: its 272-byte frame and
the 16 bytes below it, which the generation's frame layout (`Lay`) keeps
apart from the working space for the calls of the hash functions; the stage
makes no calls, and writes only its frame. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64

/-- The widths of p parameter generation produces. -/
def Supported (pLen : Nat) : Prop := pLen = 128 ∨ pLen = 256 ∨ pLen = 384

/-- The stack the stage's contract asks for. -/
abbrev stack : Nat := 288

/-- The stage's contract on AArch64. -/
abbrev contract (pLen : Nat) : Contract isa :=
  Proof.Dsa.GeneratorStage.contract (Impl.Dsa.AArch64.Generator.layout pLen) abi stack

/-- p, q and the exponent, in memory `m` of the working space `ws`. -/
abbrev pOf (pLen : Nat) (m : Mem) (ws : Addr) : Nat :=
  Proof.Dsa.GeneratorStage.pAt (Impl.Dsa.AArch64.Generator.layout pLen) m ws

abbrev qOf (pLen : Nat) (m : Mem) (ws : Addr) : Nat :=
  Proof.Dsa.GeneratorStage.qAt (Impl.Dsa.AArch64.Generator.layout pLen) m ws

structure StageABI (pLen : Nat) (s : State) : Prop where
  stackLower : stack ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩]
  wsTape : (⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  stackWs : (below s.sp stack : Region).Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩
  stackTape : (below s.sp stack : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  wsBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat * 8 ≤ 2 ^ 64
  tapeBound : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  size : Impl.Dsa.Generation.Layout.usedBytes pLen ≤ 8 * (s.gpr .x1).toNat
  odd : pOf pLen s.mem (s.gpr .x0) % 2 = 1
  bits : Spec.Dsa.bitLength (pOf pLen s.mem (s.gpr .x0)) = 8 * pLen
  qPos : 0 < qOf pLen s.mem (s.gpr .x0)
  exponent : Spec.Rsa.bytesAt s.mem (s.gpr .x0 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.exponent) pLen =
    Spec.Dsa.encodeBE pLen ((pOf pLen s.mem (s.gpr .x0) - 1) / qOf pLen s.mem (s.gpr .x0))

theorem stageABI_of {pLen : Nat} {s : State} (h : (contract pLen).pre s) : StageABI pLen s := by
  sig_pre [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.AArch64.Generator
