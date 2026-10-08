import VerifiedGarbage.Proof.Ed448.Arm.VerifyChecks
import VerifiedGarbage.Proof.Ed448.Arm.BaseEncode
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.Arm.ScalarNat
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.X448.Radix16Bytes

/-!
# Ed448 verification's equation on ARMv7: limbs from bytes, and `S < L`

`byteLimb_ok`: a limb of 56 bytes from two byte loads. `sCheck_ok`: the
twenty-eight limbs of `S`'s low 448 bits plus those of `2^448 - L` (scalar
reduction's `kLimb`), carried by X448's `pass`, carry out of 448 bits exactly
when they are at least `L`; with byte 56, `BAD |= 0` exactly when `S < L`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC TMP ld st pass)
open VG.Proof.X25519.Arm (wp_ldrb wp_dp wp_movw op2_lsl op2_reg)

/-- The number of 57 bytes: the limbs of the first 56 and the last byte. -/
theorem decodeLE_bytes57 (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) =
      valN (decoded m q) 28 + 256 ^ 56 * (m (q + BitVec.ofNat 64 56)).toNat := by
  rw [bytesAt_57 m q, Proof.Ed448.decodeLE_append, Proof.Ed448.decodeLE_eq, Proof.Ed448.decodeLE_eq,
    show (56 : Nat) = 2 * 28 from rfl, decoded_val m q 28, Proof.X448.length_bytesAt]
  simp only [Proof.X25519.leNum, Nat.mul_zero, Nat.add_zero]

theorem byteLimb_ok {s : State} {p : Reg} {src : Nat} {q : Addr}
    (hq : State.addr (s.gpr p) + BitVec.ofNat 64 src = q) (hsrc : src + 56 ≤ 4096)
    (hfit : (s.gpr p).toNat + src + 56 ≤ 2 ^ 32) (hp3 : p ≠ .r3) {i : Nat} (hi : i < 28)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block (byteLimb p src i)) s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 (decoded s.mem q i) ∧ t.mem = s.mem ∧ Keeps [.r3, .r4] s t := by
  have ea0 : State.addr (s.gpr p + BitVec.ofNat 32 (src + 2 * i)) = q + BitVec.ofNat 64 (2 * i) := by
    rw [addr_add (by omega), ← hq, Offset.add_add]
  have ea1 : State.addr (s.gpr p + BitVec.ofNat 32 (src + 2 * i + 1)) =
      q + BitVec.ofNat 64 (2 * i + 1) := by
    rw [addr_add (by omega), ← hq, Offset.add_add, Nat.add_assoc]
  unfold byteLimb
  refine wp_ldrb (off := src + 2 * i) (by omega) ea0 (hr _ (by omega)) fun s1 h1 => ?_
  refine wp_ldrb (off := src + 2 * i + 1) (a := q + BitVec.ofNat 64 (2 * i + 1)) (by omega) (by rw [h1.other p hp3]; exact ea1)
    (by rw [h1.rd, h1.wr]; exact hr _ (by omega)) fun s2 h2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 h3 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change s2.gpr .r3 + s2.gpr .r4 <<< 8 = _
    rw [h2.other .r3 (by decide), h1.gpr, h2.gpr, h1.mem]
    apply BitVec.eq_of_toNat_eq
    have b0 := (s.mem (q + BitVec.ofNat 64 (2 * i))).isLt
    have b1 := (s.mem (q + BitVec.ofNat 64 (2 * i + 1))).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, decoded, byteN]
    omega
  · rw [h3.mem, h2.mem, h1.mem]
  · exact rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide))))

theorem sLimb_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : State.addr (s.gpr .r12) + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .r12).toNat + 114 ≤ 2 ^ 32)
    {i : Nat} (hi : i < 28) (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block (sLimb i)) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (decoded s.mem q i + kLimb i)) ∧
        Keeps [.r3, .r4, .r2] s t := by
  unfold sLimb
  refine VG.Proof.X25519.Arm.WP.append (byteLimb_ok (src := 57) hq (by decide) (by omega) (by decide) hi hr)
    fun t ⟨t3, tm, tk⟩ => ?_
  have ht := hs.of_keeps tk (by decide)
  refine wp_movw fun u hu => ?_
  refine wp_dp (op2_reg _ _) fun v hv => ?_
  refine store_ok ((ht.of_upd hu (by decide) (by decide)).of_upd hv (by decide) (by decide))
    (by simp only [TMP]; omega) fun w hw => WP.block_nil ⟨?_, ?_⟩
  · rw [hw.mem, hv.mem, hu.mem, tm, hv.gpr]
    change s.mem.writeW _ (u.gpr .r3 + u.gpr .r2) = _
    rw [hu.other _ (by decide), t3, hu.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := decoded_lt s.mem q i
    have := kLimb_lt i
    simp only [radix] at *
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · exact (tk.mono (by decide)).trans (rest_keeps (ws := [.r3, .r4, .r2])
      ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest _))))

theorem sLimbs_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : State.addr (s.gpr .r12) + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .r12).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) :
    WP isa (.block ((List.range 28).flatMap sLimb)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = decoded s.mem q i + kLimb i) ∧
        Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3, .r4, .r2] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = decoded s.mem q i + kLimb i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3, .r4, .r2] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have byte : ∀ j < 56, t.mem (q + BitVec.ofNat 64 j) = s.mem (q + BitVec.ofNat 64 j) :=
    fun j hj => tm _ (Or.inr (by have := hd j hj; simp only [TMP]; omega))
  have eq : decoded t.mem q n = decoded s.mem q n := by
    simp only [decoded, byteN]; rw [byte _ (by omega), byte _ (by omega)]
  refine WP.mono (sLimb_ok (q := q) (hs.of_keeps tk (by decide)) (by rw [tk.1 _ (by decide)]; exact hq)
    (by rw [tk.1 _ (by decide)]; exact hfit) hn (by rw [tk.2.1, tk.2.2]; exact hr))
    fun u ⟨um, uk⟩ => ⟨fun i hi => ?_, tm.trans ?_, tk.trans uk⟩
  · rw [eq] at um
    change (word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · have := decoded_lt s.mem q n
      have := kLimb_lt n
      simp only [radix] at *
      rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [ite_eq_right h]; exact tf i (by omega)
  · rw [um]; exact (writeW_outside _ _ _ (by simp only [TMP]; omega)).mono (by omega) (by omega)

theorem valN_kLimb : valN kLimb 28 = 2 ^ 448 - Spec.Ed448.L := by decide +kernel

theorem radix_28 : radix ^ 28 = 2 ^ 448 := by decide +kernel

theorem sCheck_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : State.addr (s.gpr .r12) + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .r12).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) :
    WP isa (.block sCheck) s fun t =>
      BadUpd (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L) (s.gpr .r10) (t.gpr .r10) ∧
        Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3, .r4, .r2, .r5, .r10] s t := by
  unfold sCheck
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (sLimbs_ok hs hq hfit (fun j hj => hr j (by omega))
    (fun j hj => hd j (by omega))) fun t ⟨tf, tm, tk⟩ => ?_
  have ht := hs.of_keeps tk (by decide)
  have hf : ∀ i < 28, decoded s.mem q i + kLimb i ≤ 2 ^ 32 - radix := fun i _ => by
    have := decoded_lt s.mem q i; have := kLimb_lt i; simp only [radix] at *; omega
  refine VG.Proof.X25519.Arm.WP.append (pass_ok ht (o := TMP) (a := TMP) (by decide) (by decide)
    (Or.inl rfl) tf hf) fun u ⟨_, uc, um, uk⟩ => ?_
  have hu := ht.of_keeps uk (by decide)
  have r12 : u.gpr .r12 = s.gpr .r12 := by rw [uk.1 _ (by decide), tk.1 _ (by decide)]
  have b56 : u.mem (q + BitVec.ofNat 64 56) = s.mem (q + BitVec.ofNat 64 56) := by
    have := hd 56 (by decide)
    rw [um _ (Or.inr (by simp only [TMP]; omega)), tm _ (Or.inr (by simp only [TMP]; omega))]
  refine wp_ldrb (a := q + BitVec.ofNat 64 56) (by decide)
    (by rw [r12, addr_add (by omega), ← hq, Offset.add_add])
    (by rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr 56 (by decide)) fun v hv => ?_
  refine wp_dp (op2_reg _ _) fun w hw => ?_
  -- the carry and the check
  have cy := pass_eq (fun i => decoded s.mem q i + kLimb i) 28
  rw [valN_add, valN_kLimb, radix_28] at cy
  have dl : valN (digit fun i => decoded s.mem q i + kLimb i) 28 < 2 ^ 448 := by
    rw [← radix_28]; exact valN_lt (fun i _ => digit_lt _ i)
  have yl : valN (decoded s.mem q) 28 < 2 ^ 448 := by
    rw [← radix_28]; exact valN_lt (fun i _ => decoded_lt _ _ i)
  have hL : Spec.Ed448.L ≤ 2 ^ 448 := by decide +kernel
  have c1 : carry (fun i => decoded s.mem q i + kLimb i) 28 ≤ 1 := by
    generalize (2 : Nat) ^ 448 = M at *
    generalize carry (fun i => decoded s.mem q i + kLimb i) 28 = c at *
    rcases Nat.lt_or_ge c 2 with h | h
    · omega
    · have : M * 2 ≤ M * c := Nat.mul_le_mul_left M h
      omega
  have hchk := Proof.Ed448.sCheck_nat (b := (s.mem (q + BitVec.ofNat 64 56)).toNat) yl dl c1 cy
  rw [← decodeLE_bytes57] at hchk
  have e3 : w.gpr .r3 = (s.mem (q + BitVec.ofNat 64 56)).setWidth 32 |||
      BitVec.ofNat 32 (carry (fun i => decoded s.mem q i + kLimb i) 28) := by
    rw [hw.gpr]; change v.gpr .r3 ||| v.gpr .r5 = _
    rw [hv.gpr, hv.other _ (by decide), b56]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [uc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bt := (s.mem (q + BitVec.ofNat 64 56)).isLt
  refine WP.mono (orBad_ok (s := w) (P := Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L)
    ?_ ?_) fun x ⟨xb, xm, xk⟩ => ⟨?_, ?_, ?_⟩
  · rw [e3, BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.or_lt_two_pow (n := 16) (by omega) (by omega)
  · rw [e3, ← hchk]
    refine BitVec.or_eq_zero_iff.trans ?_
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := congrArg BitVec.toNat h2
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact this
      · have := congrArg BitVec.toNat h1
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at this
        exact this
    · rintro ⟨h1, h2⟩
      refine ⟨BitVec.eq_of_toNat_eq ?_, ?_⟩
      · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact h2
      · rw [h1]
  · have r10w : w.gpr .r10 = s.gpr .r10 := by
      rw [hw.other .r10 (by decide), hv.other .r10 (by decide), uk.1 .r10 (by decide),
        tk.1 .r10 (by decide)]
    rw [r10w] at xb
    exact xb
  · rw [xm, hw.mem, hv.mem]; exact tm.trans um
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans ((rest_keeps ((hv.rest (ws := [.r3, .r4, .r2, .r5, .r10])
      (by decide)).trans (hw.rest (by decide)))).trans (xk.mono ?_))) <;> decide

end VG.Proof.Ed448.Arm
