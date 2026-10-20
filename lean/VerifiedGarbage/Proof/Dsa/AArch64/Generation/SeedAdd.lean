module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract

import Mathlib.Data.List.Induction
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedByte
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # Wrapped addition across an entire seed -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Dsa.Generation

theorem seedAdd_ok (bs : List Byte) {s : State} {rp op : Addr} {carry : Nat}
    (hlen : bs.length < 4096) (hc : carry < 2 ^ 32)
    (hrp : s.gpr .x1 = rp) (hop : s.gpr .x2 = op)
    (hcarry : s.gpr .x0 = BitVec.ofNat 64 carry)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length, off rp i ≠ off op j) :
    WP isa (Impl.Dsa.AArch64.Generation.seedAdd bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length =
        Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + carry) ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧ Keep [.x0, .x3] s t := by
  induction bs using List.reverseRecOn generalizing s carry with
  | nil =>
    refine WP.mono (WP.keep [.x0, .x3] (Q := fun t => t = s) (by brun) rfl rfl rfl) fun t ⟨rfl, hk⟩ => ?_
    exact ⟨rfl, fun _ _ => rfl, hk⟩
  | append_singleton bs b ih =>
    simp only [List.length_append, List.length_singleton] at hlen hrd hwr hbytes hsep ⊢
    have hb : s.mem (off rp bs.length) = b := by
      simpa using hbytes bs.length (by omega)
    refine WP.seq (WP.mono (seedAddByte_ok (by omega) hc hrp hop hcarry (hrd _ (by omega)) (hwr _ (by omega)) hb)
      fun u ⟨hcu, hmu, ku⟩ => ?_)
    have hru : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
      intro i hi
      rw [ku.rd, ku.wr]
      exact hrd i (by omega)
    have hwu : ∀ i < bs.length, InRegions u.wr (off op i) 1 := by
      intro i hi
      rw [ku.wr]
      exact hwr i (by omega)
    have hbu : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
      intro i hi
      rw [hmu, WriteBytes.writeW8_apply, ite_eq_right (hsep i (by omega) bs.length (by omega)), hbytes i (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]
    have hcp : (b.toNat + carry) / 256 < 2 ^ 32 := by
      have := b.isLt
      omega
    refine WP.mono (ih (by omega) hcp ((ku.gpr _ (by decide)).trans hrp)
      ((ku.gpr _ (by decide)).trans hop) hcu hru hwu hbu
      (fun i hi j hj => hsep i (by omega) j (by omega))) fun t ⟨hout, hf, kt⟩ => ?_
    refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
    · rw [seedAdd_snoc]
      have hl : t.mem (off op bs.length) = BitVec.ofNat 8 (b.toNat + carry) := by
        rw [hf _ (fun i hi => Offset.add_ofNat_ne op (by omega) (by omega) (by omega)),
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

end VG.Proof.Dsa.AArch64.Generation
