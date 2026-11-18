module

public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Rsa.X86.PrivBytes`, which the modules that import this one used -/

section

/-! # Buffer geometry and immutable input bytes of checked public RSA -/

@[expose] public section

namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86

structure PublicBytes (p : BitVec 32) (k : Nat) (bs : List Byte) (s : State) : Prop where
  fits : p.toNat + k ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (byteAddr p) k
  bytes : Spec.Rsa.bytesAt s.mem (byteAddr p) k = bs

theorem PublicBytes.length {p : BitVec 32} {k : Nat} {bs : List Byte} {s : State}
    (h : PublicBytes p k bs s) : bs.length = k := by
  rw [← h.bytes]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem PublicBytes.byte {p : BitVec 32} {k : Nat} {bs : List Byte} {s : State}
    (h : PublicBytes p k bs s) (i : Nat) (hi : i < bs.length) :
    s.mem (byteAddr p + BitVec.ofNat 64 i) = bs[i] := by
  have hk : i < k := by rw [← h.length]; exact hi
  have hl : i < (Spec.Rsa.bytesAt s.mem (byteAddr p) k).length := by
    simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using hk
  have eq := congrArg (fun bs : List Byte => bs[i]?) h.bytes
  rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hi] at eq
  simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, Option.some.injEq] using eq

theorem PublicBytes.after_frame {p : BitVec 32} {k : Nat} {bs : List Byte} {s t : State}
    {regions : List Region} {rs : List Reg} (h : PublicBytes p k bs s)
    (frame : Frame regions s.mem t.mem) (rest : Keeps rs s t)
    (sep : ∀ r ∈ regions, (⟨byteAddr p, k⟩ : Region).Disjoint r) : PublicBytes p k bs t :=
  ⟨h.fits, by rw [rest.2.1, rest.2.2]; exact h.read,
    (rsa_bytes_frame frame (by have := h.fits; omega_using [this]) sep).trans h.bytes⟩

end VG.Proof.Rsa.X86.PrivChecked

end

end

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
  ⟨_, h.writable, Offset.contains_base _ hd (by have := h.nowrap; omega_using [hd, this])⟩

theorem Workspace.read {s : State} {base : BitVec 32} {size d n : Nat}
    (h : Workspace s base size) (hd : d + n ≤ size) :
    InRegions (s.rd ++ s.wr) (byteAddr base + BitVec.ofNat 64 d) n := by
  obtain ⟨R, hR, hsub⟩ := h.write hd
  exact ⟨R, List.mem_append_right _ hR, hsub⟩

end VG.Proof.Rsa.X86.PrivChecked
