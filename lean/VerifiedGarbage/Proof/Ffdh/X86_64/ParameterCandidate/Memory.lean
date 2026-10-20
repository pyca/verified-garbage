module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.CrtFrame

/-! # FFDH parameter generation on x86-64: random-tape slices and frames -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate

theorem bytesAt_read (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    m (off p i) = (Spec.Rsa.bytesAt m p n)[i]'(by rw [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hi) := by
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, off]

theorem source_take {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
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

theorem source_drop {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (h : Src s B Z p bs) (n : Nat) : Src s B Z (off p n) (bs.drop n) := by
  have he (i : Nat) : off p n + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (n + i) := by
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
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

theorem apart_drop_right {op rp : Addr} {len rn : Nat} (h : Apart op len rp rn) (n : Nat) :
    Apart op len (off rp n) (rn - n) := by
  intro i hi j hj
  have he : off rp n + BitVec.ofNat 64 j = rp + BitVec.ofNat 64 (n + j) := by
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  rw [he]
  exact h i hi (n + j) (by omega)

/-- Outer-header writes do not touch any word of the following workspace. -/
theorem outer_words {O : Addr} {Z : Nat} {m m' : Mem} {rs : List (Nat × Nat)}
    (hf : Frm O rs m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ 256)
    (hz : 256 + Z ≤ 2 ^ 64) :
    ∀ d, d + 8 ≤ Z → word m' (off O 256) d = word m (off O 256) d := by
  intro d hd
  rw [word_off, word_off]
  apply hf.word_eq
  · intro r hr
    exact Or.inr (by have := hrs r hr; omega)
  · omega

/-- The exact three stores made when a sampled prefix is consumed. -/
def advanceMem (m : Mem) (O rp : Addr) (len left used : Nat) : Mem :=
  ((m.writeW (off O (8 * oRandPtr)) (off rp len)).writeW
    (off O (8 * oRandLeft)) (BitVec.ofNat 64 (left - len))).writeW
    (off O (8 * oUsed)) (BitVec.ofNat 64 (used + len))

theorem advanceMem_frame (m : Mem) (O rp : Addr) (len left used : Nat) :
    Frm O [(8 * oRandPtr, 24)] m (advanceMem m O rp len left used) := by
  have hf (m : Mem) (d : Nat) (v : BitVec 64) (h1 : 8 * oRandPtr ≤ d)
      (h2 : d + 8 ≤ 8 * oRandPtr + 24) : Frm O [(8 * oRandPtr, 24)] m (m.writeW (off O d) v) := by
    have hd : d + 8 ≤ 2 ^ 64 := by
      have hh : 8 * oRandPtr + 24 ≤ 2 ^ 64 := by decide
      omega
    exact Frm.of_outside ((writeW_outside m O (d := d) v hd).mono h1 h2) (by simp)
  unfold advanceMem
  exact (hf m (8 * oRandPtr) (off rp len) (by decide) (by decide)).trans
    ((hf _ (8 * oRandLeft) (BitVec.ofNat 64 (left - len)) (by decide) (by decide)).trans
      (hf _ (8 * oUsed) (BitVec.ofNat 64 (used + len)) (by decide) (by decide)))

theorem advanceMem_ptr (m : Mem) (O rp : Addr) (len left used : Nat) :
    word (advanceMem m O rp len left used) O (8 * oRandPtr) = off rp len := by
  unfold advanceMem
  rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
    hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

theorem advanceMem_left (m : Mem) (O rp : Addr) (len left used : Nat) :
    word (advanceMem m O rp len left used) O (8 * oRandLeft) = BitVec.ofNat 64 (left - len) := by
  unfold advanceMem
  rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

theorem advanceMem_used (m : Mem) (O rp : Addr) (len left used : Nat) :
    word (advanceMem m O rp len left used) O (8 * oUsed) = BitVec.ofNat 64 (used + len) := by
  unfold advanceMem
  exact word_writeW_self _ _ _ _

theorem advanceMem_saved (m : Mem) (O rp : Addr) (len left used : Nat) :
    ∀ j < 32, j ≠ 12 → j ≠ 13 → j ≠ 14 →
      word (advanceMem m O rp len left used) O (8 * j) = word m O (8 * j) := by
  intro j hj h12 h13 h14
  apply (advanceMem_frame m O rp len left used).word_eq
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    change 8 * j + 8 ≤ 96 ∨ 120 ≤ 8 * j
    omega_using [h12, h13, h14]
  · omega

end VG.Proof.Ffdh.X86_64.ParameterCandidate
