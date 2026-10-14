module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! Source slices and the right-aligned nonce's memory frame. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_src_drop {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (h : Src s B Z p bs) (n : Nat) :
    Src s B Z (p + BitVec.ofNat 64 n) (bs.drop n) := by
  have he (i : Nat) : p + BitVec.ofNat 64 n + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (n + i) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [List.length_drop] at hi
    rw [he]
    exact h.rd (n + i) (by omega)
  · intro i hi
    rw [he, h.val (n + i) (by rw [List.length_drop] at hi; omega), List.getElem_drop]
  · intro i hi
    rw [List.length_drop] at hi
    rw [he]
    exact h.out (n + i) (by omega)

theorem random_src_take {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (h : Src s B Z p bs) (n : Nat) : Src s B Z p (bs.take n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [List.length_take] at hi
    exact h.rd i (by omega)
  · intro i hi
    rw [h.val i (by rw [List.length_take] at hi; omega), List.getElem_take]
  · intro i hi
    rw [List.length_take] at hi
    exact h.out i (by omega)

theorem random_nonce_addr (B : Addr) {l n : Nat} (hn : n ≤ l) :
    off B Random.oNonce + BitVec.ofNat 64 l - BitVec.ofNat 64 n = off B (200 + l - n) := by
  have he : BitVec.ofNat 64 (200 + l) - BitVec.ofNat 64 n = BitVec.ofNat 64 (200 + l - n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  change B + BitVec.ofNat 64 200 + BitVec.ofNat 64 l - BitVec.ofNat 64 n = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_neg_eq_sub, he]

theorem random_nonce_offset (B : Addr) {l n i : Nat} (hn : n ≤ l) (hl : l ≤ 32) (hi : i < n) :
    ofs B (off B (200 + l - n) + BitVec.ofNat 64 i) = 200 + l - n + i :=
  ofs_off B (by omega)

/-- A copy into the right-aligned candidate preserves everything outside
its exact byte range, hence all frame fields and external sources. -/
theorem random_copy_outside {m m' : Mem} {B : Addr} {l n : Nat}
    (hn : n ≤ l) (hl : l ≤ 32)
    (h : ∀ x, (∀ i < n, x ≠ off B (200 + l - n) + BitVec.ofNat 64 i) → m' x = m x) :
    Outside B (200 + l - n) n m m' := by
  intro x hx
  apply h x
  intro i hi he
  rw [he, random_nonce_offset B hn hl hi] at hx
  omega

end VG.Proof.Dsa.X86_64
