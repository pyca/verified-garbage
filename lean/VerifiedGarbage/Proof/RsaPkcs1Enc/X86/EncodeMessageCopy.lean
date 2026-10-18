module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeCopy
public import VerifiedGarbage.Proof.Bignum.Octets

/-! # Copy a message from a separate source after the encryption padding -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum VG.Proof.Bignum.X86 VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.X86
open VG.Proof.RsaPkcs1Sig (writeBytes_out bytesAt_take_succ)
open VG.Proof.RsaPkcs1Sig.X86
open VG.Proof.Cast5.X86 (wp_countdown)

structure MessageSource (s0 : State) (p : BitVec 32) (k n : Nat) : Prop where
  fit : p.toNat + n ≤ 2 ^ 32
  readable : ∀ i < n, InRegions (s0.rd ++ s0.wr) (byteAddr (p + BitVec.ofNat 32 i)) 1
  separate : ∀ i < n, ∀ j < k, byteAddr (p + BitVec.ofNat 32 i) ≠
    byteAddr (s0.gpr .edi + BitVec.ofNat 32 j)

theorem messageCopy_ok {s0 s : State} {p : BitVec 32} {k n : Nat} {acc : List Byte}
    (buf : Buf s0 k) (hk : k ≤ 1024) (input : MessageSource s0 p k n) (positive : 0 < n)
    (bound : acc.length + n ≤ k) (h : W s0 acc s) (source : s.gpr .esi = p)
    (count : s.gpr .ebp = BitVec.ofNat 32 n) :
    WP isa copyLoop s fun t => W s0 (acc ++ Spec.Rsa.bytesAt s0.mem (byteAddr p) n) t ∧
      t.gpr .ebx = s.gpr .ebx := by
  refine wp_countdown (cnt := .ebp) (by omega) positive
    (fun i t => W s0 (acc ++ (Spec.Rsa.bytesAt s0.mem (byteAddr p) n).take i) t ∧
      t.gpr .esi = p + BitVec.ofNat 32 i ∧ t.gpr .ebx = s.gpr .ebx) ?_
    (fun t ht => by
      rw [List.take_of_length_le (by rw [bytesAt_length])] at ht
      exact ⟨ht.1, ht.2.2⟩)
    ⟨by simpa using h, by rw [source]; simp, rfl⟩ count
  intro i hi t ⟨hw, hs, hb⟩ _
  have length : (acc ++ (Spec.Rsa.bytesAt s0.mem (byteAddr p) n).take i).length =
      acc.length + i := by
    simp only [List.length_append, List.length_take, bytesAt_length, Nat.min_eq_left (by omega : i ≤ n)]
  have readable : InRegions (t.rd ++ t.wr) (byteAddr (t.gpr .esi)) 1 := by
    rw [hs, hw.rest.2.1, hw.rest.2.2]
    exact input.readable i hi
  have writable : InRegions t.wr (byteAddr (t.gpr .edi)) 1 := by
    rw [hw.cursor, hw.rest.2.2, length]
    exact buf.writable (acc.length + i) (by omega)
  have original : t.mem (byteAddr (t.gpr .esi)) =
      s0.mem (byteAddr p + BitVec.ofNat 64 i) := by
    rw [hw.mem, hs, byteAddr_add (by have := input.fit; omega)]
    apply writeBytes_out _ _ _ _ k ?_ (by rw [length]; omega)
    intro j hj
    rw [← byteAddr_add (a := p) (by have := input.fit; omega),
      ← byteAddr_add (a := s0.gpr .edi) (by have := buf.fit; omega)]
    exact input.separate i hi j hj
  refine WP.mono (copyStep_ok t (byteAddr (t.gpr .esi)) (byteAddr (t.gpr .edi))
    (by change (t.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = _; simp only [BitVec.add_zero]; rfl)
    (by change (t.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = _; simp only [BitVec.add_zero]; rfl)
    readable writable) fun u ⟨mem, dst, src, cnt, zf, rest⟩ => ?_
  refine ⟨⟨⟨hw.rest.trans (rest.mono (by decide)), ?_, ?_⟩, ?_, ?_⟩, cnt, zf⟩
  · rw [mem, original, hw.mem, hw.cursor, byteAddr_add (by rw [length]; have := buf.fit; omega)]
    rw [bytesAt_take_succ _ _ hi, ← List.append_assoc, writeBytes_snoc _ _ _ _ (by rw [length]; omega)]
  · rw [dst, hw.cursor, BitVec.add_assoc]
    change s0.gpr .edi + (BitVec.ofNat 32 _ + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
    congr 2
    simp only [List.length_append, List.length_take, bytesAt_length,
      Nat.min_eq_left (by omega : i ≤ n), Nat.min_eq_left (by omega : i + 1 ≤ n)]
    omega
  · rw [src, hs, BitVec.add_assoc]
    change p + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]

  · exact (rest.1 .ebx (by decide)).trans hb

end VG.Proof.RsaPkcs1Enc.X86
