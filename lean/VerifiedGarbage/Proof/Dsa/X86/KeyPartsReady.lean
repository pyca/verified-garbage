module

public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyFrame
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Input and workspace components for key serialization -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallerBuffer.keyPart {s : State} {base out : Addr} {size len total : Nat} {p : Pointer}
    (B : CallerBuffer s base size p len) (positive : 0 < len)
    (apart : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨out, total⟩) :
    KeyPartReady s base out total (p, len) :=
  ⟨positive, B.fits, fun i hi => B.read i 1 (by omega_using [hi]), apart⟩

theorem localKeyPart {s : State} {base out : Addr} {size len total offset : Nat}
    (hs : Scr s base size) (positive : 0 < len) (fits : offset + len ≤ size)
    (apart : Region.Disjoint ⟨base, size⟩ ⟨out, total⟩) :
    KeyPartReady s base out total (.local offset, len) := by
  refine ⟨positive, ?_, ?_, ?_⟩
  · have nw := hs.nowrap
    change (s.gpr .edi + BitVec.ofNat 32 offset).toNat + len ≤ 2 ^ 32
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hs.edi_toNat,
      Nat.mod_eq_of_lt (by omega_using [positive, fits, nw] : offset < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [positive, fits, nw] : base.toNat + offset < 2 ^ 32)]
    omega_using [fits, nw]
  · intro i hi
    rw [local_pointer hs positive fits]
    change InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) 1
    rw [Offset.add_add]
    exact hs.read (by omega_using [fits, hi])
  · rw [local_pointer hs positive fits]
    exact apart.sub_left (Offset.sub_base base fits)

end VG.Proof.Dsa.X86
