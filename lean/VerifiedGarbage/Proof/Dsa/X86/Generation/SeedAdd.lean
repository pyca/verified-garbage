module
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import Mathlib.Data.List.Induction
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SeedAdd
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedByte

/-! # Wrapped addition across an entire seed -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum (bytesAt_length)
open VG.Proof.Dsa.Generation

theorem seedAdd_ok (bs : List Byte) {s : State} {rp op : BitVec 32} {carry : Nat}
    (hlen : bs.length < 2 ^ 31) (hc : carry < 2 ^ 24)
    (hrp : s.gpr .esi = rp) (hop : s.gpr .edi = op)
    (hrfit : rp.toNat + bs.length ≤ 2 ^ 32) (hofit : op.toNat + bs.length ≤ 2 ^ 32)
    (hcarry : s.gpr .eax = BitVec.ofNat 32 carry)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off (rp.setWidth 64) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off (op.setWidth 64) i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off (rp.setWidth 64) i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length, off (rp.setWidth 64) i ≠ off (op.setWidth 64) j) :
    WP isa (Impl.Dsa.X86.Generation.seedAdd bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem (op.setWidth 64) bs.length =
        Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + carry) ∧
      (∀ a, (∀ i < bs.length, a ≠ off (op.setWidth 64) i) → t.mem a = s.mem a) ∧ Keeps [.eax, .ecx] s t := by
  induction bs using List.reverseRecOn generalizing s carry with
  | nil => exact WP.block_nil ⟨rfl, fun _ _ => rfl, Keeps.refl _ _⟩
  | append_singleton bs b ih =>
    simp only [List.length_append, List.length_singleton] at hlen hrfit hofit hrd hwr hbytes hsep ⊢
    have hb : s.mem (off (rp.setWidth 64) bs.length) = b := by
      simpa using hbytes bs.length (by omega)
    refine WP.seq (WP.mono (seedAddByte_ok hc hrp hop (by omega) (by omega) hcarry (hrd _ (by omega)) (hwr _ (by omega)) hb)
      fun u ⟨hcu, hmu, ku⟩ => ?_)
    have hru : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off (rp.setWidth 64) i) 1 := by
      intro i hi
      rw [ku.2.1, ku.2.2]
      exact hrd i (by omega)
    have hwu : ∀ i < bs.length, InRegions u.wr (off (op.setWidth 64) i) 1 := by
      intro i hi
      rw [ku.2.2]
      exact hwr i (by omega)
    have hbu : ∀ i < bs.length, u.mem (off (rp.setWidth 64) i) = bs.getD i 0 := by
      intro i hi
      rw [hmu, WriteBytes.writeW8_apply, ite_eq_right (hsep i (by omega) bs.length (by omega)), hbytes i (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]
    have hcp : (b.toNat + carry) / 256 < 2 ^ 24 := by
      have := b.isLt
      omega
    refine WP.mono (ih (by omega) hcp ((ku.1 _ (by decide)).trans hrp)
      ((ku.1 _ (by decide)).trans hop) (by omega) (by omega) hcu hru hwu hbu
      (fun i hi j hj => hsep i (by omega) j (by omega))) fun t ⟨hout, hf, kt⟩ => ?_
    refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
    · rw [seedAdd_snoc]
      have hl : t.mem (off (op.setWidth 64) bs.length) = BitVec.ofNat 8 (b.toNat + carry) := by
        rw [hf _ (fun i hi => Offset.add_ofNat_ne (op.setWidth 64) (by omega) (by omega) (by omega)),
          hmu, WriteBytes.writeW8_apply, ite_eq_left rfl]
      apply List.ext_getElem
      · simp [bytesAt_length, encodeBE_length]
      · intro i hi hi'
        have hil : i < bs.length + 1 := by simpa only [bytesAt_length] using hi
        by_cases hib : i < bs.length
        · have he := congrArg (fun xs : List Byte => xs[i]?) hout
          simpa [Spec.Rsa.bytesAt, off, hib, List.getElem?_append, encodeBE_length] using he
        · have hie : i = bs.length := by omega
          subst i
          simpa [Spec.Rsa.bytesAt, off, List.getElem_append, encodeBE_length] using hl
    · intro a ha
      rw [hf a (fun i hi => ha i (by omega)), hmu, WriteBytes.writeW8_apply,
        ite_eq_right (ha bs.length (by omega))]

end VG.Proof.Dsa.X86.Generation
