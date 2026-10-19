module
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes

import VerifiedGarbage.Proof.Framework.Offset

/-! # The private wrapper's stack workspace, independent of its pointer registers -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Proof.Bignum.X86

structure Workspace (s : State) (base : BitVec 32) (size : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  writable : (⟨byteAddr base, size⟩ : Region) ∈ s.wr

theorem Workspace.congr {s t : State} {base : BitVec 32} {size : Nat}
    (h : Workspace s base size) (hw : t.wr = s.wr) : Workspace t base size :=
  ⟨h.nowrap, by rw [hw]; exact h.writable⟩

theorem Workspace.write {s : State} {base : BitVec 32} {size d n : Nat}
    (h : Workspace s base size) (hd : d + n ≤ size) :
    InRegions s.wr (byteAddr base + BitVec.ofNat 64 d) n :=
  ⟨_, h.writable, Offset.contains_base _ hd (by have := h.nowrap; omega)⟩

theorem Workspace.read {s : State} {base : BitVec 32} {size d n : Nat}
    (h : Workspace s base size) (hd : d + n ≤ size) :
    InRegions (s.rd ++ s.wr) (byteAddr base + BitVec.ofNat 64 d) n := by
  obtain ⟨R, hR, hsub⟩ := h.write hd
  exact ⟨R, List.mem_append_right _ hR, hsub⟩

end VG.Proof.Rsa.X86.PrivChecked
