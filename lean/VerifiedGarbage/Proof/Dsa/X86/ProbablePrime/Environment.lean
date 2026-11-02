module

public import VerifiedGarbage.Impl.Dsa.X86.ProbablePrime
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # The public environment of DSA's probable-prime test on i686

The arguments, the stack pointer below the four saved registers, and the
trial-division table, with the facts about the memory that every stage of
the test keeps.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.ProbablePrime

/-- The sizes the test supports: a candidate of whole native words, at
least two of them, in at most 64 64-bit words. -/
structure Bits (bits : Nat) : Prop where
  low : 64 ≤ bits
  high : bits ≤ 4096
  whole : bits % 32 = 0

structure Environment where
  bits : Nat
  workspace : BitVec 32
  capacity : Nat
  rand : BitVec 32
  randLength : Nat
  used : BitVec 32
  table : BitVec 32
  /-- The stack pointer below the four saved registers. -/
  p : BitVec 32

def Environment.width (E : Environment) : Nat := VG.Impl.Dsa.X86.ProbablePrime.width E.bits
def Environment.words (E : Environment) : Nat := E.bits / 32
def Environment.base (E : Environment) : Addr := E.workspace.setWidth 64
def Environment.size (E : Environment) : Nat := 8 * E.capacity
def Environment.geometry (E : Environment) : Geometry := ⟨E.base, E.size, E.width⟩
def Environment.scratch (E : Environment) : Nat := scratchBytes E.width
def Environment.workspaceRegion (E : Environment) : Region := ⟨E.base, E.size⟩
def Environment.randRegion (E : Environment) : Region := ⟨E.rand.setWidth 64, E.randLength⟩
def Environment.usedRegion (E : Environment) : Region := ⟨E.used.setWidth 64, 8⟩
def Environment.tableRegion (E : Environment) : Region := ⟨E.table.setWidth 64, 8192⟩

/-- The candidate in memory `m`. -/
def Environment.candidate (E : Environment) (m : Mem) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off E.base E.scratch) (E.bits / 8))

structure Environment.Valid (E : Environment) : Prop where
  bits : Bits E.bits
  room : E.scratch + E.bits / 8 ≤ E.size
  workspaceFit : E.workspace.toNat + E.size ≤ 2 ^ 32
  randFit : E.rand.toNat + E.randLength ≤ 2 ^ 32
  randLengthFit : E.randLength < 2 ^ 32
  usedFit : E.used.toNat + 8 ≤ 2 ^ 32
  tableFit : E.table.toNat + 8192 ≤ 2 ^ 32
  low : 136 ≤ E.p.toNat
  argsFit : E.p.toNat + 40 ≤ 2 ^ 32
  workspaceStack : E.p.toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 136 ≤ E.p.toNat
  argsFar : (⟨(E.p + 20#32).setWidth 64, 20⟩ : Region).Disjoint E.workspaceRegion
  randWorkspace : E.randRegion.Disjoint E.workspaceRegion
  randUsed : E.randRegion.Disjoint E.usedRegion
  usedWorkspace : E.usedRegion.Disjoint E.workspaceRegion
  tableWorkspace : E.tableRegion.Disjoint E.workspaceRegion
  tableUsed : E.tableRegion.Disjoint E.usedRegion
  savedFar : ∀ r ∈ [E.workspaceRegion, E.randRegion, E.usedRegion, E.tableRegion],
    r.Disjoint ⟨E.p.setWidth 64, 16⟩
  stackFar : ∀ r ∈ [E.workspaceRegion, E.randRegion, E.usedRegion, E.tableRegion],
    r.Disjoint (below E.p 136)

/-- The bytes of the working space past the header and the arrays, which
the test never changes. -/
def Tail (E : Environment) (m m' : Mem) : Prop :=
  ∀ i, E.scratch ≤ i → i < E.size → m' (off E.base i) = m (off E.base i)

theorem Tail.refl (E : Environment) (m : Mem) : Tail E m m := fun _ _ _ => rfl

theorem Tail.trans {E : Environment} {a b c : Mem} (A : Tail E a b) (B : Tail E b c) : Tail E a c :=
  fun i lo hi => (B i lo hi).trans (A i lo hi)

/-- The memory every stage keeps: the tape, the table, the `used` output and
the candidate. -/
structure Memory (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop where
  usedWrite : Rt.Ws s (E.used.setWidth 64) 8
  randRead : InRegions (s.rd ++ s.wr) (E.rand.setWidth 64) E.randLength
  entropy : Spec.Rsa.bytesAt s.mem (E.rand.setWidth 64) E.randLength = entropy
  tableRead : InRegions (s.rd ++ s.wr) (E.table.setWidth 64) 8192
  table : ∀ i < 1024, s.mem.readW (off (E.table.setWidth 64) (8 * i)) 64 =
    BitVec.ofNat 64 (VG.Impl.RsaKeyGen.TrialTable32.entry i)
  symbol : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = E.table
  candidate : E.candidate s.mem = c

/-- What every stage keeps: the arguments the candidate code reads from the
header, and the memory. -/
structure Input (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop where
  scratch : Scr s E.base E.size
  stack : s.gpr .esp = E.p
  randPtr : s.mem.readW (off E.base 28) 32 = E.rand
  randLength : w32 s.mem E.base 32 = E.randLength
  capacity : w32 s.mem E.base 40 = E.capacity
  usedPtr : s.mem.readW (off E.base 44) 32 = E.used
  memory : Memory E c entropy s

/-- After the candidate's import: the candidate and the candidate minus one
in arrays 0 and 5, and no octet of the tape read yet. -/
structure Loaded (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop where
  input : Input E c entropy s
  value : val32 s.mem E.base (E.geometry.array 0) E.geometry.words = c
  minusOne : val32 s.mem E.base (E.geometry.array 5) E.geometry.words = c - 1
  count : w32 s.mem E.base 152 = 0

end VG.Proof.Dsa.X86.ProbablePrime
