module

public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Dsa.ParameterSearch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The public environment of parameter generation on i686

The arguments, as the search keeps them in the state words of `scratch`
(`Impl.Dsa.X86.Generation`), the stack pointer below the four saved
registers, and the facts about memory that every stage keeps: `rand`,
which nothing writes, and the state words that hold the arguments. A seed's
octets and its window of `h` candidates are parts of `rand`, at the offsets
`seedsOff` and `hsOff`: each stage reads them as the tapes of their own.
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
  /-- `used` and `state`. -/
  usedP : Addr
  stP : Addr
  /-- The seeds the search may still reject at its start, `state[0]`. -/
  k0 : Nat
  /-- The seeds' octets, at their offset in `rand`. -/
  seedsOff : Nat
  seedsLen : Nat
  /-- The `h` candidates' octets, at their offset in `rand`. -/
  hsOff : Nat
  hsLen : Nat
  /-- `rand`. -/
  wit : Addr
  witLen : Nat
  /-- The stack pointer below the four saved registers. -/
  sp : BitVec 32
  /-- The trial-division table the probable-prime tests read. -/
  table : Addr
  /-- `rand`'s bytes. -/
  witT : List Byte

namespace Env
variable (E : Env)

def outLen : Nat := 2 * E.pLen + E.qLen
def scratchRegion : Region := ⟨E.base, E.size⟩
def outRegion : Region := ⟨E.out, E.outLen⟩
def usedRegion : Region := ⟨E.usedP, 8⟩
def stRegion : Region := ⟨E.stP, 32⟩
/-- The seeds and the `h` candidates, in `rand`. -/
def seeds : Addr := E.wit + BitVec.ofNat 64 E.seedsOff
def hs : Addr := E.wit + BitVec.ofNat 64 E.hsOff
def seedT : List Byte := (E.witT.drop E.seedsOff).take E.seedsLen
def hT : List Byte := (E.witT.drop E.hsOff).take E.hsLen
def seedsRegion : Region := ⟨E.seeds, E.seedsLen⟩
def hsRegion : Region := ⟨E.hs, E.hsLen⟩
def witRegion : Region := ⟨E.wit, E.witLen⟩
/-- The stack below the saved registers that the calls use. -/
def stackRegion : Region := below E.sp 200

def tableRegion : Region := ⟨E.table, 8192⟩

/-- The seed of `qLen` octets at the cursor `c`. -/
def atSeed (c : Nat) : Env := { E with seedsOff := c, seedsLen := E.qLen }

/-- The window of `h` candidates at `u`: at most 128 of them. -/
def window (u : Nat) : Env := { E with hsOff := u, hsLen := min (E.witLen - u) (128 * E.pLen) }

/-- The ranges `(offset, bytes)` of `scratch` and the stack that `m'` may
differ from `m` in. -/
def Chg (os : List (Nat × Nat)) (m m' : Mem) : Prop :=
  Frame ((os.map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion]) m m'

/-- Ranges of `scratch` apart from the state words that hold the arguments
`Base` keeps: `out`, `used`, `state` and `rand`. -/
def Apart (os : List (Nat × Nat)) : Prop :=
  ∀ o ∈ os, o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ fOut ∨ (fOut + 4 ≤ o.1 ∧ o.1 + o.2 ≤ fUsedP) ∨ fWitLen + 4 ≤ o.1)

end Env

structure Env.Valid (E : Env) : Prop where
  lengths : Spec.Dsa.generationLengthsValid E.pLen E.qLen
  room : 512 * E.pLen + 8192 ≤ E.size
  scratchFit : E.base.toNat + E.size ≤ 2 ^ 32
  outFit : E.out.toNat + E.outLen ≤ 2 ^ 32
  witFit : E.wit.toNat + E.witLen ≤ 2 ^ 32
  seedsIn : E.seedsOff + E.seedsLen ≤ E.witLen
  hsIn : E.hsOff + E.hsLen ≤ E.witLen
  low : 200 ≤ E.sp.toNat
  stackScratch : E.sp.toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 200 ≤ E.sp.toNat
  outScratch : E.outRegion.Disjoint E.scratchRegion
  witFar : E.witRegion.Disjoint E.scratchRegion ∧ E.witRegion.Disjoint E.outRegion ∧
    E.witRegion.Disjoint E.stackRegion
  outStack : E.outRegion.Disjoint E.stackRegion
  scratchStack : E.scratchRegion.Disjoint E.stackRegion
  tableFit : E.table.toNat + 8192 ≤ 2 ^ 32
  outPtr : E.out.toNat < 2 ^ 32
  witPtr : E.wit.toNat < 2 ^ 32
  witLen32 : E.witLen < 2 ^ 32
  tableFar : E.tableRegion.Disjoint E.scratchRegion ∧ E.tableRegion.Disjoint E.outRegion ∧
    E.tableRegion.Disjoint E.stackRegion
  tableAligned : E.table.toNat % 64 = 0
  usedFit : E.usedP.toNat + 8 ≤ 2 ^ 32
  stFit : E.stP.toNat + 32 ≤ 2 ^ 32
  usedFar : ∀ r ∈ [E.scratchRegion, E.outRegion, E.stackRegion, E.stRegion, E.witRegion, E.tableRegion],
    E.usedRegion.Disjoint r
  stFar : ∀ r ∈ [E.scratchRegion, E.outRegion, E.stackRegion, E.witRegion, E.tableRegion], E.stRegion.Disjoint r
  k0le : E.k0 ≤ Spec.Dsa.parameterSeeds

namespace Env.Valid
variable {E : Env} (v : E.Valid)
include v

theorem seedsSub : E.seedsRegion.Sub E.witRegion := Offset.sub_base _ v.seedsIn

theorem hsSub : E.hsRegion.Sub E.witRegion := Offset.sub_base _ v.hsIn

theorem seedsNat : E.seeds.toNat = E.wit.toNat + E.seedsOff := by
  have := v.witFit; have := v.seedsIn
  rw [Env.seeds, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := E.seedsOff) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem hsNat : E.hs.toNat = E.wit.toNat + E.hsOff := by
  have := v.witFit; have := v.hsIn
  rw [Env.hs, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := E.hsOff) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem seedsFit : E.seeds.toNat + E.seedsLen ≤ 2 ^ 32 := by
  rw [v.seedsNat]; have := v.witFit; have := v.seedsIn; omega

theorem hsFit : E.hs.toNat + E.hsLen ≤ 2 ^ 32 := by
  rw [v.hsNat]; have := v.witFit; have := v.hsIn; omega

theorem tapesFar : ∀ r ∈ [E.seedsRegion, E.hsRegion, E.witRegion],
    r.Disjoint E.scratchRegion ∧ r.Disjoint E.outRegion ∧ r.Disjoint E.stackRegion := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have W := v.witFar
  rcases hr with rfl | rfl | rfl
  · exact ⟨W.1.sub_left v.seedsSub, W.2.1.sub_left v.seedsSub, W.2.2.sub_left v.seedsSub⟩
  · exact ⟨W.1.sub_left v.hsSub, W.2.1.sub_left v.hsSub, W.2.2.sub_left v.hsSub⟩
  · exact W

end Env.Valid

theorem Env.Valid.pLen_ge {E : Env} (v : E.Valid) : 128 ≤ E.pLen := by
  rcases v.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem Env.Valid.size_ge {E : Env} (v : E.Valid) : 73728 ≤ E.size := by
  have := v.pLen_ge; have := v.room; omega

theorem toNat_wide (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

/-- What every stage keeps: the working space in `edi`, the stack pointer,
the permissions, the table and `rand`, and the state words that hold the
arguments. -/
structure Base (E : Env) (s : State) : Prop where
  scr : Scr s E.base E.size
  sp : s.gpr .esp = E.sp
  tapes : E.witRegion ∈ s.rd
  table : E.tableRegion ∈ s.rd
  out : E.outRegion ∈ s.wr
  usedW : E.usedRegion ∈ s.wr
  stW : E.stRegion ∈ s.wr
  syms : (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64 = E.table
  held : Abi.constsHeld s.mem (fun n => (s.syms n).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts
  wit : Spec.Rsa.bytesAt s.mem E.wit E.witLen = E.witT
  outW : s.mem.readW (off E.base fOut) 32 = E.out.setWidth 32
  usedPW : s.mem.readW (off E.base fUsedP) 32 = E.usedP.setWidth 32
  stPW : s.mem.readW (off E.base fStP) 32 = E.stP.setWidth 32
  witW : s.mem.readW (off E.base fWit) 32 = E.wit.setWidth 32
  witLenW : s.mem.readW (off E.base fWitLen) 32 = BitVec.ofNat 32 E.witLen

/-- The bytes of a part of `rand`. -/
theorem Base.part {E : Env} {s : State} (B : Base E s) {o n : Nat} (h : o + n ≤ E.witLen) :
    Spec.Rsa.bytesAt s.mem (E.wit + BitVec.ofNat 64 o) n = (E.witT.drop o).take n := by
  rw [← B.wit]
  simp only [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [VG.Offset.add_add]

theorem Base.seeds {E : Env} {s : State} (B : Base E s) (v : E.Valid) :
    Spec.Rsa.bytesAt s.mem E.seeds E.seedsLen = E.seedT := B.part v.seedsIn

theorem Base.hs {E : Env} {s : State} (B : Base E s) (v : E.Valid) :
    Spec.Rsa.bytesAt s.mem E.hs E.hsLen = E.hT := B.part v.hsIn

end VG.Proof.Dsa.X86.Generation
