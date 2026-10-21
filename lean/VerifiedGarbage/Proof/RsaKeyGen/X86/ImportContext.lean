module

public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Offset

/-! # Public bounds and exact memory footprint of a native-word import -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure Geometry where
  src : BitVec 32
  dst : BitVec 32
  count : Nat

def Geometry.sourceRegion (g : Geometry) : Region := ⟨g.src.setWidth 64, 4 * g.count⟩
def Geometry.destRegion (g : Geometry) : Region := ⟨g.dst.setWidth 64, 4 * g.count⟩
def Geometry.sourceAt (g : Geometry) (i : Nat) : Addr := off (g.src.setWidth 64) (4 * i)
def Geometry.destAt (g : Geometry) (i : Nat) : Addr := off (g.dst.setWidth 64) (4 * (g.count - 1 - i))
def Geometry.sourcePtr (g : Geometry) (i : Nat) : BitVec 32 := g.src + BitVec.ofNat 32 (4 * i)
def Geometry.destPtr (g : Geometry) (i : Nat) : BitVec 32 :=
  g.dst + BitVec.ofNat 32 (4 * (g.count - 1)) - BitVec.ofNat 32 (4 * i)

structure Context (g : Geometry) (s : State) : Prop where
  positive : 0 < g.count
  sourceFit : g.src.toNat + 4 * g.count ≤ 2 ^ 32
  destFit : g.dst.toNat + 4 * g.count ≤ 2 ^ 32
  readable : ∀ i < g.count, InRegions (s.rd ++ s.wr) (g.sourceAt i) 4
  writable : ∀ i < g.count, InRegions s.wr (g.destAt i) 4
  separate : g.sourceRegion.Disjoint g.destRegion

structure StateAt (g : Geometry) (s₀ : State) (i : Nat) (s : State) : Prop where
  index : i ≤ g.count
  source : s.gpr .esi = g.sourcePtr i
  destination : s.gpr .ebx = g.destPtr i
  count : s.gpr .ecx = BitVec.ofNat 32 (g.count - i)
  copied : ∀ j < i, s.mem.readW (g.destAt j) 32 = bswap (s₀.mem.readW (g.sourceAt j) 32)
  frame : Frame [g.destRegion] s₀.mem s.mem
  keeps : Keeps [.eax, .ebx, .esi, .ecx] s₀ s

theorem source_address {g : Geometry} {s : State} (C : Context g s) {i : Nat} (index : i < g.count) :
    addr (g.sourcePtr i) 0 = g.sourceAt i := by
  change addr (g.src + BitVec.ofNat 32 (4 * i)) 0 = _
  rw [show addr (g.src + BitVec.ofNat 32 (4 * i)) 0 = addr g.src (4 * i) by
    simp only [addr, BitVec.add_zero], addr_eq (by have := C.sourceFit; omega)]
  rfl

theorem dest_pointer {g : Geometry} {i : Nat} (index : i < g.count) :
    g.destPtr i = g.dst + BitVec.ofNat 32 (4 * (g.count - 1 - i)) := by
  unfold Geometry.destPtr
  apply BitVec.sub_eq_iff_eq_add.mpr
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

theorem dest_address {g : Geometry} {s : State} (C : Context g s) {i : Nat} (index : i < g.count) :
    addr (g.destPtr i) 0 = g.destAt i := by
  rw [dest_pointer index]
  change addr (g.dst + BitVec.ofNat 32 (4 * (g.count - 1 - i))) 0 = _
  rw [show addr (g.dst + BitVec.ofNat 32 (4 * (g.count - 1 - i))) 0 =
      addr g.dst (4 * (g.count - 1 - i)) by simp only [addr, BitVec.add_zero],
    addr_eq (by have := C.destFit; omega)]
  rfl

end VG.Proof.RsaKeyGen.X86.Import
