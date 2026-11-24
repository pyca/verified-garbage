module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Proof.X448.X86.Field
public import VerifiedGarbage.Spec.X448.Contract

import VerifiedGarbage.Proof.X448.X86.Decode
import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

/-!
# X448 on x86 (32-bit): the output buffer

Output stores cover exactly 56 bytes and preserve the disjoint working space.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- Writes to the output preserve a word in the disjoint working space. -/
theorem output_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : Outside p 0 n m m') (hn : n ≤ 56)
    (hd : d + 4 ≤ 8192) (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (Nat.le_trans (by omega_using [hn] : 0 + n ≤ 56) (hfar _ (by omega_using [hd, hi]))))

theorem packWord_ok {s : State} {base p : Addr} (hs : Scr s base) {i : Nat} (hi : i < 14)
    (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hw : InRegions s.wr (off p (4 * i)) 4) :
    WP isa (.block (packWord i)) s fun t =>
      t.mem = s.mem.writeW (off p (4 * i)) (word s.mem base (X2 + 4 * i)) ∧ Keeps [.eax] s t := by
  unfold packWord
  refine load_ok hs (by simp only [X2, slot]; omega_using [hi]) fun t ht => ?_
  refine wp_store (a := off p (4 * i)) (by
    change addr (t.gpr .esi) (4 * i) = _
    rw [ht.other .esi (by decide), addr_eq (by omega_using [hi, hfit]), hp]) (by rw [ht.wr]; exact hw)
    fun u hu => WP.block_nil ⟨?_, (ht.rest (by decide)).trans (hu.rest _)⟩
  rw [hu.mem, ht.mem, ht.gpr]

theorem output_ok {s : State} {base p : Addr} (hs : Scr s base)
    (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32) (hw : ∀ k < 14, InRegions s.wr (off p (4 * k)) 4)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    WP isa (.block ((List.range 14).flatMap packWord)) s fun t =>
      Spec.X448.bytesAt t.mem p 56 = VG.Proof.X25519.leBytes 56 (fe s.mem base X2) ∧
      Outside p 0 56 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, (t.mem.readW (off p (4 * i)) 32).toNat = limbs s.mem base X2 i) ∧
    Outside p 0 (4 * n) s.mem t.mem ∧ Keeps clob s t
  have st : ∀ n t, n < 14 → inv n t → WP isa (.block (packWord n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (packWord_ok (p := p) (hs.of_keeps tk (by decide)) hn (by rw [tk.1 _ (by decide)]; exact hp)
      (by rw [tk.1 _ (by decide)]; exact hfit)
      (by rw [tk.2.2]; exact hw _ hn)) fun u ⟨um, uk⟩ => ?_
    rw [output_word tm (by omega_using [hn]) (by simp only [X2, slot]; omega_using [hn]) hfar] at um
    refine ⟨?_, (tm.mono (by decide) (by omega_using [])).trans ?_, tk.trans (uk.mono (by decide))⟩
    · intro i hi
      show (word u.mem p (4 * i)).toNat = _
      have := word_write t.mem p (o := 0) (i := n) (j := i) (by omega_using [hn]) (by omega_using [hn, hi])
        (word s.mem base (X2 + 4 * n))
      rw [Nat.zero_add, Nat.zero_add] at this
      rw [um, this]
      by_cases h : i = n
      · rw [ite_eq_left h, h]
      · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
    · rw [um]; exact (writeW_outside _ _ _ (by omega_using [hn])).mono (by omega_using []) (by omega_using [])
  refine WP.mono (wp_range_flatMap (M := isa) (N := 14) inv st 14 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ => ⟨?_, tm, tk⟩
  have e : VG.Proof.X25519.leNum (Spec.X448.bytesAt t.mem p 56) = fe s.mem base X2 :=
    (bytes_num t.mem p 14).trans (Proof.X25519.X86.num_congr tf)
  have o := VG.Proof.X25519.bytesAt_leBytes t.mem p 56
  rw [← leNum_bytesAt_read, e] at o
  exact o

end VG.Proof.X448.X86
