import VerifiedGarbage.Proof.Ed448.X86.VerifyChecks
import VerifiedGarbage.Proof.Ed448.X86.ScalarStep
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.X86.Decode

/-!
# Ed448 verification's equation on x86 (32-bit): limbs from bytes, and `S < L`

`byteLimb_ok`: a limb of 56 bytes from two byte loads. `sCheck_ok`: the
twenty-eight limbs of `S`'s low 448 bits plus those of `2^448 - L` (scalar
reduction's `kLimb`), carried by X448's `pass`, carry out of 448 bits exactly
when they are at least `L`; with byte 56, `BAD |= 0` exactly when `S < L`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC TMP ld st pass at_)

/-- The number of 57 bytes: the limbs of the first 56 and the last byte. -/
theorem decodeLE_bytes57 (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) =
      valN (decoded m q) 28 + 256 ^ 56 * (m (q + BitVec.ofNat 64 56)).toNat := by
  rw [Limbs16.bytesAt_57 m q, Proof.Ed448.decodeLE_append, Proof.Ed448.decodeLE_eq, Proof.Ed448.decodeLE_eq,
    show (56 : Nat) = 2 * 28 from rfl, decoded_val m q 28, Proof.X448.length_bytesAt]
  simp only [Proof.X25519.leNum, Nat.mul_zero, Nat.add_zero]

/-- The address of byte `src + j` at `esi`. -/
theorem ea_esi {s : State} {q : Addr} {src : Nat} (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 src = q)
    {j : Nat} (hfit : (s.gpr .esi).toNat + src + j < 2 ^ 32) :
    s.ea (at_ .esi (src + j)) = q + BitVec.ofNat 64 j := by
  change addr (s.gpr .esi) (src + j) = _
  rw [addr_eq (by omega), ← hq, Offset.add_add]

theorem byteLimb_ok {s : State} {q : Addr} {src : Nat}
    (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 src = q) (hfit : (s.gpr .esi).toNat + src + 56 ≤ 2 ^ 32)
    {i : Nat} (hi : i < 28) (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block (byteLimb src i)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decoded s.mem q i) ∧ t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  unfold byteLimb
  refine wp_load8 (a := q + BitVec.ofNat 64 (2 * i)) (ea_esi hq (by omega))
    (hr _ (by omega)) fun s1 h1 => ?_
  refine wp_load8 (a := q + BitVec.ofNat 64 (2 * i + 1))
    (by rw [show src + 2 * i + 1 = src + (2 * i + 1) by omega]
        exact ea_esi (by rw [h1.other .esi (by decide)]; exact hq) (by rw [h1.other .esi (by decide)]; omega))
    (by rw [h1.rd, h1.wr]; exact hr _ (by omega)) fun s2 h2 => ?_
  refine wp_shift (by decide) fun sr hrot => ?_
  refine wp_alu (by simp [plain]) rfl fun s3 h3 _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change sr.gpr .eax + sr.gpr .edx = _
    rw [hrot.other .eax (by decide), hrot.gpr]
    rw [h2.other .eax (by decide), h1.gpr, h2.gpr, h1.mem, byte_rotate]
    apply BitVec.eq_of_toNat_eq
    have h0 := (s.mem (q + BitVec.ofNat 64 (2 * i))).isLt
    have h1 := (s.mem (q + BitVec.ofNat 64 (2 * i + 1))).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, decoded, byteN]
    omega
  · rw [h3.mem, hrot.mem, h2.mem, h1.mem]
  · exact (h1.rest (by simp)).trans ((h2.rest (by simp)).trans ((hrot.rest (by simp)).trans
      (h3.rest (by simp))))

theorem sLimb_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32)
    {i : Nat} (hi : i < 28) (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block (sLimb i)) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (decoded s.mem q i + kLimb i)) ∧
        Keeps [.eax, .edx] s t := by
  unfold sLimb
  rw [WP.block_append_iff]
  refine WP.mono (byteLimb_ok hq (by omega) hi hr) fun t ⟨ta, tm, tk⟩ => ?_
  have ht := hs.of_keeps tk (by decide)
  refine wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  refine store_ok (ht.of_upd hu (by decide)) (by simp only [TMP]; omega) fun w hw =>
    WP.block_nil ⟨?_, tk.trans ((hu.rest (by simp)).trans (hw.rest _))⟩
  rw [hw.mem, hu.mem, tm, hu.gpr]
  change s.mem.writeW _ (t.gpr .eax + BitVec.ofNat 32 (kLimb i)) = _
  rw [ta]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := decoded_lt s.mem q i
  have := kLimb_lt i
  simp only [radix] at *
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sLimbs_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) :
    WP isa (.block ((List.range 28).flatMap sLimb)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = decoded s.mem q i + kLimb i) ∧
        Outside base TMP 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = decoded s.mem q i + kLimb i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t
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

theorem radix_28 : radix ^ 28 = 2 ^ 448 := by decide +kernel

theorem sCheck_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) :
    WP isa (.block sCheck) s fun t =>
      BadUpd (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L) (word s.mem base BAD)
        (word t.mem base BAD) ∧ Outside2 base TMP 112 BAD 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  unfold sCheck
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (sLimbs_ok hs hq hfit (fun j hj => hr j (by omega)) (fun j hj => hd j (by omega)))
    fun t ⟨tf, tm, tk⟩ => ?_
  have ht := hs.of_keeps tk (by decide)
  have hf : ∀ i < 28, decoded s.mem q i + kLimb i ≤ 2 ^ 32 - radix := fun i _ => by
    have := decoded_lt s.mem q i; have := kLimb_lt i; simp only [radix] at *; omega
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok ht (o := TMP) (a := TMP) (by decide) (by decide) (Or.inl rfl) tf hf)
    fun u ⟨_, uc, um, uk⟩ => ?_
  have hu := ht.of_keeps uk (by decide)
  have esi : u.gpr .esi = s.gpr .esi := by rw [uk.1 _ (by decide), tk.1 _ (by decide)]
  have b56 : u.mem (q + BitVec.ofNat 64 56) = s.mem (q + BitVec.ofNat 64 56) := by
    have := hd 56 (by decide)
    rw [um _ (Or.inr (by simp only [TMP]; omega)), tm _ (Or.inr (by simp only [TMP]; omega))]
  refine wp_load8 (a := q + BitVec.ofNat 64 56)
    (by rw [show (113 : Nat) = 57 + 56 from rfl]; exact ea_esi (by rw [esi]; exact hq) (by rw [esi]; omega))
    (by rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr 56 (by decide)) fun v hv => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl fun w hw _ => ?_
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
  have e3 : w.gpr .eax = (s.mem (q + BitVec.ofNat 64 56)).setWidth 32 |||
      BitVec.ofNat 32 (carry (fun i => decoded s.mem q i + kLimb i) 28) := by
    rw [hw.gpr]; change v.gpr .eax ||| v.gpr .ebx = _
    rw [hv.gpr, hv.other _ (by decide), b56]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [uc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bt := (s.mem (q + BitVec.ofNat 64 56)).isLt
  have hw' : Scr w base := (hu.of_upd hv (by decide)).of_upd hw (by decide)
  refine WP.mono (orBad_ok (s := w) hw' (by decide)
    (P := Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L) ?_ ?_)
    fun x ⟨xb, xm, xk⟩ => ⟨?_, ?_, ?_⟩
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
  · have bw : word w.mem base BAD = word s.mem base BAD := by
      rw [hw.mem, hv.mem, um.word (Or.inl (by simp only [BAD, TMP]; omega)) (by decide),
        tm.word (Or.inl (by simp only [BAD, TMP]; omega)) (by decide)]
    rw [bw] at xb
    exact xb
  · intro p h1 h2
    rw [xm p h2, hw.mem, hv.mem, um p h1, tm p h1]
  · exact (tk.mono (by simp)).trans ((uk.mono (by simp)).trans ((hv.rest (by simp)).trans
      ((hw.rest (by simp)).trans (xk.mono (by simp)))))

end VG.Proof.Ed448.X86
