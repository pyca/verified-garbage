module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset

/-! # Public sieve geometry and the read-only candidate and divisor table -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen

structure Geometry where
  sp : BitVec 32
  candidate : BitVec 32
  table : BitVec 32
  w : Nat
  limit : Nat

def Geometry.candidateRegion (g : Geometry) : Region := ⟨g.candidate.setWidth 64, 8 * g.w⟩
def Geometry.tableRegion (g : Geometry) : Region := ⟨g.table.setWidth 64, 8192⟩
def Geometry.stackRegion (g : Geometry) : Region := ⟨g.sp.setWidth 64, 20⟩

def Geometry.cursor (g : Geometry) (i : Nat) : BitVec 32 := g.table + BitVec.ofNat 32 (8 * i)

def Geometry.ending (g : Geometry) : BitVec 32 := g.candidate + BitVec.ofNat 32 (8 * g.w)

structure Geometry.Valid (g : Geometry) : Prop where
  positive : 0 < g.w
  widthBound : g.w ≤ 128
  limitPositive : 0 < g.limit
  limitBound : g.limit ≤ 1024
  candidateFit : g.candidate.toNat + 8 * g.w ≤ 2 ^ 32
  tableFit : g.table.toNat + 8192 ≤ 2 ^ 32
  candidateFar : g.candidateRegion.Disjoint g.stackRegion
  tableFar : g.tableRegion.Disjoint g.stackRegion

structure Context (g : Geometry) (c : Nat) (s : State) : Prop where
  stack : StackContext g.sp s
  candidateRead : ∀ i < 2 * g.w, InRegions (s.rd ++ s.wr) (off (g.candidate.setWidth 64) (4 * i)) 4
  tableRead : ∀ i < 1024, ∀ d ∈ [0, 4], InRegions (s.rd ++ s.wr) (addr (g.cursor i) d) 4
  tableWords : ∀ i < 1024, s.mem.readW ((g.table.setWidth 64) + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i)
  candidateValue : val32 s.mem (g.candidate.setWidth 64) 0 (2 * g.w) = c

structure StateAt (g : Geometry) (c i q : Nat) (s : State) : Prop where
  context : Context g c s
  candidate : s.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate
  ending : s.mem.readW (off (g.sp.setWidth 64) 4) 32 = g.ending
  cursor : s.mem.readW (off (g.sp.setWidth 64) 8) 32 = g.cursor i
  count : s.mem.readW (off (g.sp.setWidth 64) 12) 32 = BitVec.ofNat 32 q

theorem Geometry.Valid.cursor_addr {g : Geometry} (v : g.Valid) {i : Nat} (index : i < 1024) :
    (g.cursor i).setWidth 64 = g.table.setWidth 64 + BitVec.ofNat 64 (8 * i) := by
  have bound := v.tableFit
  apply BitVec.eq_of_toNat_eq
  simp only [Geometry.cursor, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have table := g.table.isLt
  omega

theorem Geometry.Valid.cursor_fit {g : Geometry} (v : g.Valid) {i : Nat} (index : i < 1024) :
    (g.cursor i).toNat + 8 ≤ 2 ^ 32 := by
  have bound := v.tableFit
  simp only [Geometry.cursor, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega


theorem outsideStack_frame {g : Geometry} {m m' : Mem}
    (O : Outside (g.sp.setWidth 64) 0 20 m m') : Frame [g.stackRegion] m m' := by
  intro x outside
  have nc := outside _ (List.mem_singleton_self _)
  apply O
  right
  have bound : 20 ≤ ofs (g.sp.setWidth 64) x := by
    by_contra bad
    apply nc
    change ofs (g.sp.setWidth 64) x + 1 ≤ 20
    omega
  exact bound

theorem Context.keep {g : Geometry} (v : g.Valid) {c : Nat} {s t : State} (C : Context g c s)
    {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs)
    (F : Frame [g.stackRegion] s.mem t.mem) : Context g c t := by
  refine ⟨C.stack.keep K sp, ?_, ?_, ?_, ?_⟩
  · intro i bound
    rw [K.2.1, K.2.2]
    exact C.candidateRead i bound
  · intro i bound d mem
    rw [K.2.1, K.2.2]
    exact C.tableRead i bound d mem
  · intro i bound
    have read := F.readW (r := g.tableRegion) (w := 64)
      (Offset.contains_base _ (by omega : 8 * i + 8 ≤ 8192) (by omega))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.tableFar) (by decide)
    exact read.trans (C.tableWords i bound)
  · rw [← C.candidateValue]
    apply val32_congr
    intro i bound
    apply congrArg BitVec.toNat
    exact F.readW (r := g.candidateRegion) (w := 32)
      (Offset.contains_base _ (by omega) (by have := v.candidateFit; omega))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.candidateFar) (by decide)

end VG.Proof.RsaKeyGen.X86.Sieve
