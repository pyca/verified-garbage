module

public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32

/-! # The public environment of parameter generation on i686

The arguments, as the search keeps them in the state words of `scratch`
(`Impl.Dsa.X86.Generation`), the stack pointer below the four saved
registers, and the facts about memory that every stage keeps: the tapes,
which nothing writes, and the state words that hold the arguments.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure Env where
  pLen : Nat
  qLen : Nat
  /-- `scratch`, and its bytes. -/
  base : Addr
  size : Nat
  out : Addr
  seeds : Addr
  seedsLen : Nat
  hs : Addr
  hsLen : Nat
  wit : Addr
  witLen : Nat
  /-- The stack pointer below the four saved registers. -/
  sp : BitVec 32
  /-- The trial-division table the probable-prime tests read. -/
  table : Addr
  /-- The tapes' bytes. -/
  seedT : List Byte
  hT : List Byte
  witT : List Byte

namespace Env
variable (E : Env)

def outLen : Nat := 2 * E.pLen + E.qLen
def scratchRegion : Region := ⟨E.base, E.size⟩
def outRegion : Region := ⟨E.out, E.outLen⟩
def seedsRegion : Region := ⟨E.seeds, E.seedsLen⟩
def hsRegion : Region := ⟨E.hs, E.hsLen⟩
def witRegion : Region := ⟨E.wit, E.witLen⟩
/-- The stack below the saved registers that the calls use. -/
def stackRegion : Region := below E.sp 160

def tableRegion : Region := ⟨E.table, 8192⟩

/-- The ranges `(offset, bytes)` of `scratch` and the stack that `m'` may
differ from `m` in. -/
def Chg (os : List (Nat × Nat)) (m m' : Mem) : Prop :=
  Frame ((os.map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion]) m m'

/-- Ranges of `scratch` apart from the state words that hold the arguments
`Base` keeps: `out`, and the `h` and witness tapes. -/
def Apart (os : List (Nat × Nat)) : Prop :=
  ∀ o ∈ os, o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ fOut ∨ (fOut + 4 ≤ o.1 ∧ o.1 + o.2 ≤ fHs) ∨ fWitLen + 4 ≤ o.1)

end Env

structure Env.Valid (E : Env) : Prop where
  lengths : Spec.Dsa.generationLengthsValid E.pLen E.qLen
  room : 512 * E.pLen + 8192 ≤ E.size
  scratchFit : E.base.toNat + E.size ≤ 2 ^ 32
  outFit : E.out.toNat + E.outLen ≤ 2 ^ 32
  seedsFit : E.seeds.toNat + E.seedsLen ≤ 2 ^ 32
  hsFit : E.hs.toNat + E.hsLen ≤ 2 ^ 32
  witFit : E.wit.toNat + E.witLen ≤ 2 ^ 32
  seedsWhole : E.seedsLen % E.qLen = 0
  hsWhole : E.hsLen % E.pLen = 0
  low : 160 ≤ E.sp.toNat
  stackScratch : E.sp.toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 160 ≤ E.sp.toNat
  outScratch : E.outRegion.Disjoint E.scratchRegion
  tapesFar : ∀ r ∈ [E.seedsRegion, E.hsRegion, E.witRegion],
    r.Disjoint E.scratchRegion ∧ r.Disjoint E.outRegion ∧ r.Disjoint E.stackRegion
  outStack : E.outRegion.Disjoint E.stackRegion
  scratchStack : E.scratchRegion.Disjoint E.stackRegion
  tableFit : E.table.toNat + 8192 ≤ 2 ^ 32
  ptrs : E.out.toNat < 2 ^ 32 ∧ E.seeds.toNat < 2 ^ 32 ∧ E.hs.toNat < 2 ^ 32 ∧ E.wit.toNat < 2 ^ 32
  lens : E.seedsLen < 2 ^ 32 ∧ E.hsLen < 2 ^ 32 ∧ E.witLen < 2 ^ 32
  tableFar : E.tableRegion.Disjoint E.scratchRegion ∧ E.tableRegion.Disjoint E.outRegion ∧
    E.tableRegion.Disjoint E.stackRegion

theorem Env.Valid.pLen_ge {E : Env} (v : E.Valid) : 128 ≤ E.pLen := by
  rcases v.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem Env.Valid.size_ge {E : Env} (v : E.Valid) : 73728 ≤ E.size := by
  have := v.pLen_ge; have := v.room; omega

/-- What every stage keeps: the working space in `edi`, the stack pointer,
the permissions, the table and the tapes, and the state words that hold the
arguments. -/
structure Base (E : Env) (s : State) : Prop where
  scr : Scr s E.base E.size
  sp : s.gpr .esp = E.sp
  tapes : E.seedsRegion ∈ s.rd ∧ E.hsRegion ∈ s.rd ∧ E.witRegion ∈ s.rd
  table : E.tableRegion ∈ s.rd
  out : E.outRegion ∈ s.wr
  syms : (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64 = E.table
  held : Abi.constsHeld s.mem (fun n => (s.syms n).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts
  seeds : Spec.Rsa.bytesAt s.mem E.seeds E.seedsLen = E.seedT
  hs : Spec.Rsa.bytesAt s.mem E.hs E.hsLen = E.hT
  wit : Spec.Rsa.bytesAt s.mem E.wit E.witLen = E.witT
  outW : s.mem.readW (off E.base fOut) 32 = E.out.setWidth 32
  hsW : s.mem.readW (off E.base fHs) 32 = E.hs.setWidth 32
  hsLenW : s.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 E.hsLen
  witW : s.mem.readW (off E.base fWit) 32 = E.wit.setWidth 32
  witLenW : s.mem.readW (off E.base fWitLen) 32 = BitVec.ofNat 32 E.witLen

end VG.Proof.Dsa.X86.Generation
