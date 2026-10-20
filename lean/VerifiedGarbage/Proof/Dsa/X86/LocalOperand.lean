module

public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Persistent scratch buffers as arithmetic operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem local_pointer {s : State} {base : Addr} {size offset len : Nat}
    (hs : Scr s base size) (hlen : 0 < len) (hb : offset + len ≤ size) :
    (pointerValue base s (.local offset)).setWidth 64 = off base offset := by
  unfold pointerValue
  have H := addr_eq (x := s.gpr .edi) (k := offset) (by rw [hs.edi_toNat]; have := hs.nowrap; omega)
  rw [hs.edi] at H
  exact H

theorem localReady {s : State} {base : Addr} {size offset len n : Nat}
    (hs : Scr s base size) (hlen : 0 < len) (hb : offset + len ≤ size) (hfar : contextBytes n ≤ offset) :
    OperandReady s base n (.local offset) len := by
  have nw := hs.nowrap
  have ofit : offset < 2 ^ 32 := by omega
  have pfit : base.toNat + offset < 2 ^ 32 := by omega
  have ptr := local_pointer hs hlen hb
  constructor
  · constructor
    · change (s.gpr .edi + BitVec.ofNat 32 offset).toNat + len ≤ 2 ^ 32
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hs.edi_toNat, Nat.mod_eq_of_lt ofit, Nat.mod_eq_of_lt pfit]
      omega
    · intro d hd
      rw [ptr]
      change InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 offset + BitVec.ofNat 64 d) 4
      rw [Offset.add_add]
      exact hs.read (by omega)
  · rw [ptr]
    exact Offset.disjoint_base base hfar (by omega)

theorem local_bytes {s : State} {base : Addr} {size offset len : Nat}
    (hs : Scr s base size) (hlen : 0 < len) (hb : offset + len ≤ size) :
    Spec.Rsa.bytesAt s.mem ((pointerValue base s (.local offset)).setWidth 64) len =
      Spec.Rsa.bytesAt s.mem (off base offset) len := by rw [local_pointer hs hlen hb]

end VG.Proof.Dsa.X86
