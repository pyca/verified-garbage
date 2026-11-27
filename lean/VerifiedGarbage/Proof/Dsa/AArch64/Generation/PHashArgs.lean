module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.ListSnoc
import VerifiedGarbage.Impl.Bignum.AArch64.Core
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Dsa.AArch64.Generation.SeedAdd`, which the modules that import this one used -/

section

/-! # Wrapped addition across an entire seed -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SeedByte.lean`, which only this module imported.
section

/-! # Carry propagation for one wrapped-seed byte -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

private theorem byte_add (c : Nat) (b : Byte) :
    BitVec.ofNat 64 c + b.setWidth 64 = BitVec.ofNat 64 (b.toNat + c) := by
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem seedAddByte_ok {s : State} {rp op : Addr} {i carry : Nat} {b : Byte}
    (hi : i < 4096) (hc : carry < 2 ^ 32) (hrp : s.gpr .x1 = rp) (hop : s.gpr .x2 = op)
    (hcarry : s.gpr .x0 = BitVec.ofNat 64 carry)
    (hrd : InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : InRegions s.wr (off op i) 1) (hb : s.mem (off rp i) = b) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedAddByte i)) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 ((b.toNat + carry) / 256) ∧
      t.mem = s.mem.writeW (off op i) (BitVec.ofNat 8 (b.toNat + carry)) ∧ Keep [.x0, .x3] s t := by
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun t =>
      t.gpr .x0 = BitVec.ofNat 64 ((b.toNat + carry) / 256) ∧
      t.mem = s.mem.writeW (off op i) (BitVec.ofNat 8 (b.toNat + carry))) ?_ rfl rfl rfl)
    fun _ ⟨⟨hv, hm⟩, hk⟩ => ⟨hv, hm, hk⟩
  simp only [off] at hrd hwr hb
  unfold Impl.Dsa.AArch64.Generation.seedAddByte
  brun [hrp, hop, hcarry, hrd, hwr, hb, read_one, hi,
    BitVec.setWidth_setWidth (x := b) (v := 32) (w := 64) (by decide), byte_add carry b]
  constructor
  · apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

end VG.Proof.Dsa.AArch64.Generation
end

end

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
  induction bs using VG.List.reverseRecOn generalizing s carry with
  | nil =>
    refine WP.mono (WP.keep [.x0, .x3] (Q := fun t => t = s) (by brun) rfl rfl rfl) fun t ⟨rfl, hk⟩ => ?_
    exact ⟨rfl, fun _ _ => rfl, hk⟩
  | append_singleton bs b ih =>
    simp only [List.length_append, List.length_singleton] at hlen hrd hwr hbytes hsep ⊢
    have hb : s.mem (off rp bs.length) = b := by
      simpa using hbytes bs.length (by omega_using [])
    refine WP.seq (WP.mono (seedAddByte_ok (by omega_using [hlen]) hc hrp hop hcarry (hrd _ (by omega_using [])) (hwr _ (by omega_using [])) hb)
      fun u ⟨hcu, hmu, ku⟩ => ?_)
    have hru : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
      intro i hi
      rw [ku.rd, ku.wr]
      exact hrd i (by omega_using [hi])
    have hwu : ∀ i < bs.length, InRegions u.wr (off op i) 1 := by
      intro i hi
      rw [ku.wr]
      exact hwr i (by omega_using [hi])
    have hbu : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
      intro i hi
      rw [hmu, WriteBytes.writeW8_apply, ite_eq_right (hsep i (by omega_using [hi]) bs.length (by omega_using [])), hbytes i (by omega_using [hi])]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]
    have hcp : (b.toNat + carry) / 256 < 2 ^ 32 := by
      have := b.isLt
      omega_using [hc]
    refine WP.mono (ih (by omega_using [hlen]) hcp ((ku.gpr _ (by decide)).trans hrp)
      ((ku.gpr _ (by decide)).trans hop) hcu hru hwu hbu
      (fun i hi j hj => hsep i (by omega_using [hi]) j (by omega_using [hj]))) fun t ⟨hout, hf, kt⟩ => ?_
    refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
    · rw [seedAdd_snoc]
      have hl : t.mem (off op bs.length) = BitVec.ofNat 8 (b.toNat + carry) := by
        rw [hf _ (fun i hi => Offset.add_ofNat_ne op (by omega_using [hlen]) (by omega_using [hlen, hi]) (by omega_using [hi])),
          hmu, WriteBytes.writeW8_apply, ite_eq_left rfl]
      apply List.ext_getElem
      · simp [bytesAt_length, encodeBE_length]
      · intro i hi hi'
        have hil : i < bs.length + 1 := by simpa only [bytesAt_length] using hi
        by_cases hib : i < bs.length
        · have he := congrArg (fun xs : List Byte => xs[i]?) hout
          simpa [Spec.Rsa.bytesAt, off, hib, List.getElem?_append, encodeBE_length] using he
        · have hie : i = bs.length := by omega_using [hil, hib]
          subst i
          simpa [Spec.Rsa.bytesAt, off, List.getElem_append, encodeBE_length] using hl
    · intro a ha
      rw [hf a (fun i hi => ha i (by omega_using [hi])), hmu, WriteBytes.writeW8_apply,
        ite_eq_right (ha bs.length (by omega_using []))]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! Prepare the wrapped seed, offset and digest-copy arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

theorem seedInputArgs_ok {s : State} {F S rp op : Addr} {offset j : Nat}
    (hj : j < 4096) (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (hrp : W 1 = rp) (hop : W 3 = op)
    (hoff : W 2 = BitVec.ofNat 64 offset) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedInputArgs j)) s fun t =>
      t.gpr .x1 = rp ∧ t.gpr .x2 = op ∧ t.gpr .x0 = BitVec.ofNat 64 (offset + j) ∧
      t.mem = s.mem ∧ Keep [.x1, .x2, .x0] s t := by
  refine WP.mono (WP.keep [.x1, .x2, .x0] (Q := fun t =>
    t.gpr .x1 = rp ∧ t.gpr .x2 = op ∧ t.gpr .x0 = BitVec.ofNat 64 (offset + j) ∧ t.mem = s.mem)
    ?_ rfl rfl rfl) fun _ ⟨⟨a, b, c, d⟩, hk⟩ => ⟨a, b, c, d, hk⟩
  have h1 : s.mem.readW (F + BitVec.ofNat 64 8) 64 = rp := (R.fr 1 (by decide)).trans hrp
  have h3 : s.mem.readW (F + BitVec.ofNat 64 24) 64 = op := (R.fr 3 (by decide)).trans hop
  have h2 : s.mem.readW (F + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 offset :=
    (R.fr 2 (by decide)).trans hoff
  unfold Impl.Dsa.AArch64.Generation.seedInputArgs
  brun [exec_ldrSp (off := 8) (by decide), exec_ldrSp (off := 24) (by decide),
    exec_ldrSp (off := 16) (by decide), L.sp, L.ld (d := 8) (n := 8) (by decide),
    L.ld (d := 24) (n := 8) (by decide), L.ld (d := 16) (n := 8) (by decide),
    h1, h2, h3, exec_addImm_x' hj, BitVec.ofNat_add]

theorem hashCopyArgs_ok {s : State} {F S op : Addr} {len count j : Nat}
    (hlen : len = 20 ∨ len = 32) (hcount : count ≤ 11)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (hop : W 4 = op) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.hashCopyArgs len count j)) s fun t =>
      t.gpr .x12 = off S oDig ∧ t.gpr .x2 = off op ((count - j) * len) ∧
      t.gpr .x9 = BitVec.ofNat 64 len ∧ t.mem = s.mem ∧ Keep [.x12, .x2, .x9] s t := by
  have hoff : (count - j) * len < 4096 := by rcases hlen with rfl | rfl <;> omega_using [hcount]
  have h4 : s.mem.readW (F + BitVec.ofNat 64 32) 64 = op := (R.fr 4 (by decide)).trans hop
  have hs : s.mem.readW (F + BitVec.ofNat 64 sScr) 64 = S := L.slot
  refine WP.mono (WP.keep [.x12, .x2, .x9] (Q := fun t =>
    t.gpr .x12 = off S oDig ∧ t.gpr .x2 = off op ((count - j) * len) ∧
    t.gpr .x9 = BitVec.ofNat 64 len ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨a, b, c, d⟩, hk⟩ => ⟨a, b, c, d, hk⟩
  unfold Impl.Dsa.AArch64.Generation.hashCopyArgs
  brun [exec_ldrSp (off := sScr) (by decide), exec_ldrSp (off := 32) (by decide),
    L.sp, L.ld (d := sScr) (n := 8) (by decide), L.ld (d := 32) (n := 8) (by decide),
    hs, h4, exec_addImm_x' hoff, off]
  rcases hlen with rfl | rfl <;> rfl

end VG.Proof.Dsa.AArch64.Generation
