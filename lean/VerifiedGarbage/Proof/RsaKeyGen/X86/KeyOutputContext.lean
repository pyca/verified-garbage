module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public geometry for the seven masked RSA key outputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

structure OutputGeometry where
  base : Addr
  size : Nat
  n : Nat
  argument : Nat → BitVec 32

def OutputGeometry.pointer (g : OutputGeometry) (i : Nat) : BitVec 32 := g.argument (2 * i)
def OutputGeometry.length (g : OutputGeometry) (i : Nat) : Nat := (g.argument (2 * i + 1)).toNat
def OutputGeometry.region (g : OutputGeometry) (i : Nat) : Region := ⟨(g.pointer i).setWidth 64, g.length i⟩
def OutputGeometry.scratch (g : OutputGeometry) : Region := ⟨g.base, g.size⟩
def OutputGeometry.writes (g : OutputGeometry) : List Region := g.scratch :: (List.range 7).map g.region

structure OutputGeometry.Valid (g : OutputGeometry) : Prop where
  lengthPositive : ∀ i < 7, 0 < g.length i
  lengthBound : ∀ i < 7, g.length i ≤ 4 * g.n
  fit : ∀ i < 7, (g.pointer i).toNat + g.length i ≤ 2 ^ 32
  scratchApart : ∀ i < 7, g.scratch.Disjoint (g.region i)
  separate : ∀ i < 7, ∀ j < 7, i ≠ j → (g.region i).Disjoint (g.region j)

structure OutputInput (g : OutputGeometry) (s : State) : Prop where
  ws : Ws s g.base g.size g.n 32
  valid : g.Valid
  arguments : ∀ i < 14, s.mem.readW (off g.base (4 * i)) 32 = g.argument i
  writable : ∀ i < 7, InRegions s.wr (g.region i).base (g.region i).len

theorem OutputInput.after {g : OutputGeometry} {s t : State} {rs : List Reg}
    (h : OutputInput g s) (ws : Ws t g.base g.size g.n 32) (K : Keeps rs s t)
    (header : ∀ d, d + 4 ≤ hdr → slot t.mem g.base d = slot s.mem g.base d) : OutputInput g t := by
  refine ⟨ws, h.valid, ?_, ?_⟩
  · intro i hi
    apply BitVec.eq_of_toNat_eq
    exact (header (4 * i) (by unfold hdr; omega)).trans (congrArg BitVec.toNat (h.arguments i hi))
  · intro i hi
    rw [K.2.2]
    exact h.writable i hi

end VG.Proof.RsaKeyGen.X86.Key
