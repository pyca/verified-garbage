module

public import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion

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
    (rsa_bytes_frame frame (by have := h.fits; omega) sep).trans h.bytes⟩

end VG.Proof.Rsa.X86.PrivChecked
