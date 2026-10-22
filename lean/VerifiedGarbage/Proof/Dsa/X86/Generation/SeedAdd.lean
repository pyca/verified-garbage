module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedByte
public import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Data.List.Induction

/-! # Wrapped seed addition reuses the shared big-endian carry identity -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Proof.Dsa.Generation

theorem seed_add (bs : List Byte) {s : State} {src dst : BitVec 32} {carry : Nat}
    (hlen : bs.length < 4096) (hc : carry < 2 ^ 31)
    (srcFit : src.toNat + bs.length ≤ 2 ^ 32) (dstFit : dst.toNat + bs.length ≤ 2 ^ 32)
    (source : s.gpr .esi = src) (dest : s.gpr .ebx = dst) (value : s.gpr .edx = BitVec.ofNat 32 carry)
    (read : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off (byteAddr src) i) 1)
    (write : ∀ i < bs.length, InRegions s.wr (off (byteAddr dst) i) 1)
    (bytes : ∀ i < bs.length, s.mem (off (byteAddr src) i) = bs.getD i 0)
    (separate : ∀ i < bs.length, ∀ j < bs.length, off (byteAddr src) i ≠ off (byteAddr dst) j) :
    WP isa (seedAdd bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr dst) bs.length = Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + carry) ∧
      (∀ a, (∀ i < bs.length, a ≠ off (byteAddr dst) i) → t.mem a = s.mem a) ∧ Keeps [.eax, .edx] s t := by
  induction bs using List.reverseRecOn generalizing s carry with
  | nil => exact WP.block_nil ⟨rfl, fun _ _ => rfl, Keeps.refl _ _⟩
  | append_singleton bs b ih =>
    simp only [List.length_append, List.length_singleton] at hlen srcFit dstFit read write bytes separate ⊢
    have hb : s.mem (off (byteAddr src) bs.length) = b := by simpa using bytes bs.length (by omega)
    refine WP.seq (WP.mono (seed_add_byte hc (by omega) (by omega) source dest value
      (read _ (by omega)) (write _ (by omega)) hb) ?_)
    rintro u ⟨carryU, memory, K⟩
    have readU : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off (byteAddr src) i) 1 := by
      intro i hi; rw [K.2.1, K.2.2]; exact read i (by omega)
    have writeU : ∀ i < bs.length, InRegions u.wr (off (byteAddr dst) i) 1 := by
      intro i hi; rw [K.2.2]; exact write i (by omega)
    have bytesU : ∀ i < bs.length, u.mem (off (byteAddr src) i) = bs.getD i 0 := by
      intro i hi
      rw [memory, WriteBytes.writeW8_apply, ite_eq_right (separate i (by omega) bs.length (by omega)), bytes i (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]
    have smallCarry : (b.toNat + carry) / 256 < 2 ^ 31 := by have := b.isLt; omega
    refine WP.mono (ih (by omega) smallCarry (by omega) (by omega)
      ((K.1 .esi (by decide)).trans source) ((K.1 .ebx (by decide)).trans dest) carryU readU writeU bytesU
      (fun i hi j hj => separate i (by omega) j (by omega))) ?_
    rintro t ⟨output, outside, L⟩
    refine ⟨?_, ?_, K.trans L⟩
    · have last : t.mem (off (byteAddr dst) bs.length) = BitVec.ofNat 8 (b.toNat + carry) := by
        rw [outside _ (fun i hi => Offset.add_ofNat_ne (byteAddr dst) (by omega) (by omega) (by omega)),
          memory, WriteBytes.writeW8_apply, ite_eq_left rfl]
      rw [seedAdd_snoc, bytesAt_append, output]
      simpa only [Spec.Rsa.bytesAt, List.range_one, List.map_cons, List.map_nil, off, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero] using congrArg (fun x => Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + (b.toNat + carry) / 256) ++ [x]) last
    · intro a ha
      rw [outside a (fun i hi => ha i (by omega)), memory, WriteBytes.writeW8_apply,
        ite_eq_right (ha bs.length (by omega))]

end VG.Proof.Dsa.X86.Generation
