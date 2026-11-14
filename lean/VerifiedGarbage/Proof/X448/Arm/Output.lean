module
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Proof.X448.Arm.Field
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.Arm.BitWrite
public import VerifiedGarbage.Proof.X448.Radix16Bytes
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.Arm.Iter
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `X448.Arm.Pack`, which only this module used -/

section

/-!
# X448 on ARMv7: encoding a limb

Two byte stores encode each 16-bit limb in little-endian order without
requiring output alignment.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_strb wp_mov op2_lsr)

def packMem (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) : Mem :=
  (m.writeW (off p (2 * i)) (v.setWidth 8)).writeW (off p (2 * i + 1)) ((v >>> 8).setWidth 8)

theorem packStep_ok {s : State} {base p : Addr} (hs : Scr s base) {i : Nat} (hi : i < 28)
    (hp : State.addr (s.gpr .r8) = p) (hfit : (s.gpr .r8).toNat + 56 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (off p (2 * i + j)) 1) :
    WP isa (.block (packLimb i)) s fun t =>
      t.mem = packMem s.mem p i (word s.mem base (X2 + 4 * i)) ∧ Keeps [.r3] s t := by
  have ea : ∀ j < 2, State.addr (s.gpr .r8 + BitVec.ofNat 32 (2 * i + j)) = off p (2 * i + j) := by
    intro j hj; rw [addr_add (by omega_using [hi, hfit, hj]), hp]
  unfold packLimb
  refine load_ok hs (by simp only [X2, slot]; omega_using [hi]) fun t ht => ?_
  refine wp_strb (a := off p (2 * i)) (by omega_using [hi]) (by rw [ht.other .r8 (by decide)]; exact ea 0 (by decide))
    (by rw [ht.wr]; exact hw 0 (by decide)) fun u hu => ?_
  refine wp_mov (op2_lsr (by decide)) fun v hv => ?_
  refine wp_strb (a := off p (2 * i + 1)) (by omega_using [hi]) (by rw [hv.other .r8 (by decide), hu.gpr, ht.other .r8 (by decide)]; exact ea 1 (by decide))
    (by rw [hv.wr, hu.wr, ht.wr]; exact hw 1 (by decide)) fun w hw' => WP.block_nil ⟨?_, ?_⟩
  · rw [hw'.mem, hv.mem, hu.mem, ht.mem, hv.gpr, hu.gpr, ht.gpr]; rfl
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest _).trans
      ((hv.rest (by decide)).trans (hw'.rest _))))

theorem packMem_decoded (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32)
    (hv : v.toNat < radix) : decoded (packMem m p i v) p i = v.toNat := by
  have hn : off p (2 * i) ≠ off p (2 * i + 1) := by
    rw [ne_eq, off_eq_iff p (by omega_using [hi]) (by omega_using [hi])]; omega_using []
  simp only [decoded, byteN, packMem, writeW8_apply, hn, ite_false, ite_true,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [radix] at hv
  omega_using [hv]

theorem packMem_outside (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32) :
    Outside p (2 * i) 2 m (packMem m p i v) := by
  intro x hx
  rw [packMem, writeW8_outside _ _ _ (by omega_using [hi]) (by omega_using [hx]),
    writeW8_outside _ _ _ (by omega_using [hi]) (by omega_using [hx])]

theorem packLimb_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    {i : Nat} (hi : i < 28) (hp : State.addr (s.gpr .r8) = p)
    (hfit : (s.gpr .r8).toNat + 56 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (off p (2 * i + j)) 1) :
    WP isa (.block (packLimb i)) s fun t =>
      decoded t.mem p i = limbs s.mem base X2 i ∧ Outside p (2 * i) 2 s.mem t.mem ∧ Keeps clob s t := by
  refine WP.mono (packStep_ok hs hi hp hfit hw) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, tk.mono ?_⟩
  · rw [tm]; exact packMem_decoded _ _ hi _ (hb i hi)
  · rw [tm]; exact packMem_outside _ _ hi _
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

end VG.Proof.X448.Arm

end

end


/-!
# X448 on ARMv7: the output buffer

Output stores cover exactly 56 bytes and preserve the disjoint working space.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

/-- Writes to the output preserve a word in the disjoint working space. -/
theorem output_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : Outside p 0 n m m') (hn : n ≤ 56)
    (hd : d + 4 ≤ 8192) (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (Nat.le_trans (by omega_using [hn] : 0 + n ≤ 56) (hfar _ (by omega_using [hd, hi]))))

theorem output_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    (hp : State.addr (s.gpr .r8) = p)
    (hfit : (s.gpr .r8).toNat + 56 ≤ 2 ^ 32) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    WP isa (.block ((List.range 28).flatMap packLimb)) s fun t =>
      Spec.X448.bytesAt t.mem p 56 = VG.Proof.X25519.leBytes 56 (fe s.mem base X2) ∧
      Outside p 0 56 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, decoded t.mem p i = limbs s.mem base X2 i) ∧ Outside p 0 (2 * n) s.mem t.mem ∧ Keeps clob s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (packLimb n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have eq : ∀ j < 28, limbs t.mem base X2 j = limbs s.mem base X2 j := by
      intro j hj
      exact congrArg BitVec.toNat (output_word tm (by omega_using [hn]) (by simp only [X2, slot]; omega_using [hj]) hfar)
    have tb : Bounded t.mem base X2 := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (packLimb_ok (p := p) (hs.of_keeps tk (by decide)) tb hn (by rw [tk.1 _ (by decide)]; exact hp)
      (by rw [tk.1 _ (by decide)]; exact hfit)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega_using [hn, hj]))) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, (tm.mono (by decide) (by omega_using [])).trans (um.mono (by omega_using []) (by omega_using [])), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans (eq n hn)
    · have byte : ∀ j < 2, u.mem (off p (2 * i + j)) = t.mem (off p (2 * i + j)) := by
        intro j hj
        exact um _ (Or.inl (by rw [ofs_off' p (by omega_using [hn, hi, hj])]; omega_using [hi, h, hj]))
      simp only [decoded, byteN]
      have b0 := byte 0 (by decide)
      have b1 := byte 1 (by decide)
      simp only [off, Nat.add_zero] at b0 b1
      rw [b0, b1]
      exact tf i (by omega_using [hi, h])
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ =>
    ⟨packed_bytes tf, tm, tk⟩

end VG.Proof.X448.Arm
