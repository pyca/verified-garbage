import VerifiedGarbage.Proof.X448.Arm.BitWrite
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase

/-!
# Ed448 base-point multiplication on ARMv7: the scalar's bits

All 57 bytes of the scalar expanded into bytes `BITS + t` holding bit `t`, as
X448's `bits` expands its 56 (without its clamping): byte `t` is bit `t` of
the scalar (`baseBits_ok`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Impl.X448.Arm (BITS)
open VG.Spec.Ed448 (bytesAt decodeLE)

theorem baseBitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {b : BitVec 8} (ha : s.gpr .r3 = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (baseBitJ j)) s fun t =>
      t.mem = s.mem.writeW (off base (BITS + (8 * i + j)))
        (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧ Keeps [.r2] s t := by
  unfold baseBitJ
  refine VG.Proof.X25519.Arm.wp_mov (bitShift_eval s hj) fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  have ea : State.addr (u.gpr .r7 + BitVec.ofNat 32 (BITS + j)) = off base (BITS + (8 * i + j)) := by
    rw [hu.other .r7 (by decide), ht.other .r7 (by decide), hp,
      BitVec.add_assoc, ← BitVec.ofNat_add, hs.ea (by simp only [BITS]; omega)]
    congr 1; omega
  have wr := hs.write (d := BITS + (8 * i + j)) (n := 1) (by simp only [BITS]; omega)
  refine VG.Proof.X25519.Arm.wp_strb (by simp only [BITS]; omega) ea
    (by rw [hu.wr, ht.wr]; exact wr) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]
    change s.mem.writeW _ ((t.gpr .r2 &&& (1 : BitVec 32)).setWidth 8) = _
    rw [ht.gpr, ha, bit_byte b j hj]
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

/-- Expanding eight bits preserves each byte already written. -/
theorem baseByteBits_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {b : BitVec 8} (ha : s.gpr .r3 = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap baseBitJ)) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r2] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r2] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (baseBitJ n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (baseBitJ_ok (hs.of_keeps tk (by decide)) hi
      (by rw [tk.1 .r7 (by decide), tk.1 .r0 (by decide)]; exact hp)
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (BITS + (8 * i + j)) = off base (BITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

def baseBitHead : List Instr :=
  [.dp .add .r7 .r1 (.reg .r11), .ldrb .r3 .r7 0, .dp .add .r7 .r0 (.shifted .r11 .lsl 3)]

def baseBitTail : List Instr := [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 57)]

def baseBitRegs : List Reg := [.r3, .r2, .r11, .r7]

theorem baseBitHead_ok {s : State} {k : Addr} (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32) {i : Nat} (hi : i < 57)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block baseBitHead) s fun t =>
      t.gpr .r3 = (s.mem (off k i)).setWidth 32 ∧
      t.gpr .r7 = t.gpr .r0 + BitVec.ofNat 32 (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r7] s t := by
  unfold baseBitHead
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun t ht => ?_
  have ea : State.addr (t.gpr .r7 + BitVec.ofNat 32 0) = off k i := by
    rw [ht.gpr]; change State.addr (s.gpr .r1 + s.gpr .r11 + BitVec.ofNat 32 0) = _
    rw [BitVec.add_zero, hb, addr_add (by omega), hk]
  refine VG.Proof.X25519.Arm.wp_ldrb (by decide) ea (by rw [ht.rd, ht.wr]; exact hkr) fun u hu => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_lsl (by decide)) fun v hv =>
    WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hv.other .r3 (by decide), hu.gpr, ht.mem]
  · rw [hv.gpr, hv.other .r0 (by decide)]
    change u.gpr .r0 + u.gpr .r11 <<< 3 = _
    rw [hu.other .r11 (by decide), ht.other .r11 (by decide), hb]
    apply congrArg (u.gpr .r0 + ·)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  · exact hv.mem.trans (hu.mem.trans ht.mem)
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest (by decide))))

theorem baseBitTail_ok {s : State} {i : Nat} (hi : i < 57) (hb : s.gpr .r11 = BitVec.ofNat 32 i) :
    WP isa (.block baseBitTail) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 57) ∧
      t.mem = s.mem ∧ Keeps [.r11] s t := by
  have check : ∀ n < 57,
      ((BitVec.ofNat 32 n + (1 : BitVec 32) - (57 : BitVec 32)) == 0) = decide (n + 1 = 57) :=
    by decide +kernel
  unfold baseBitTail
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu hz =>
    WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hu.gpr, ht.gpr]; change s.gpr .r11 + BitVec.ofNat 32 1 = _
    rw [hb, ← BitVec.ofNat_add]
  · rw [hz, ht.gpr]; change ((s.gpr .r11 + 1 - 57) == 0) = _
    rw [hb]; exact check i hi
  · exact hu.mem.trans ht.mem
  · exact rest_keeps ((ht.rest (by decide)).trans (hu.rest _))

theorem baseBitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32) {i : Nat} (hi : i < 57)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block baseBitsBody) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 57) ∧ Keeps baseBitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (baseBitHead ++ (List.range 8).flatMap baseBitJ ++ baseBitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (baseBitHead_ok hk hfit hi hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (baseByteBits_ok (hs.of_keeps tk (by decide)) hi tp ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .r11 = BitVec.ofNat 32 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (baseBitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

/-- The bits loop's invariant, after `i` bytes. -/
structure BitsInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  r1 : State.addr (s.gpr .r1) = k
  fit : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  gpr : ∀ r, r ∉ baseBitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem baseBitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → BitsInv base k s₀ s i →
      WP isa (.loop (.block baseBitsBody) .ne) s fun s' => BitsInv base k s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block baseBitsBody) (c := .ne)
    (Q := fun s' => BitsInv base k s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ BitsInv base k s₀ s i) ?_ (57 - i) s
    ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (baseBitsBody_ok hb.scr hb.r1 hb.fit hi hb.r11 (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : BitsInv base k s₀ s' (i + 1) := by
    refine ⟨hb.scr.of_keeps ⟨g', rd', wr'⟩ (by decide),
      (by rw [g' _ (by decide)]; exact hb.r1),
      (by rw [g' _ (by decide)]; exact hb.fit), b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z']
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega
    exact .inl ⟨rfl, inv⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

/-- Bit `t` of the scalar is bit `t % 8` of its byte `t / 8`. -/
theorem scalar_bit (m : Mem) (p : Addr) {t : Nat} (ht : t < 456) :
    ((m (p + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1 =
      (decodeLE (bytesAt m p 57) >>> t) &&& 1 := by
  rw [Proof.Ed448.decodeLE_eq, Proof.X25519.leNum_bit, bytesAt_getD m p (by omega)]

/-- `baseBits`: byte `t` of `BITS` is bit `t` of the scalar, for `t < 456`. -/
theorem baseBits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa baseBits s fun s' =>
      (∀ r, r ∉ baseBitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base BITS 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem k 57) >>> t) &&& 1) := by
  unfold baseBits
  refine WP.seq (WP.mono (show WP isa (.block [.mov .r11 (.imm 0)]) s
      (fun s' => BitsInv base k s s' 0) by
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide))
      fun t ht => WP.block_nil ?_
    have keep : Keeps baseBitRegs s t := rest_keeps (ht.rest (by decide))
    exact ⟨hs.of_keeps keep (by decide), by rw [ht.other .r1 (by decide)]; exact hk,
      by rw [ht.other .r1 (by decide)]; exact hfit, ht.gpr, keep.1, keep.2.1, keep.2.2,
      ht.mem ▸ Outside.refl _ _ _ _, fun _ hi => by omega⟩) fun s₁ h₁ => ?_)
  refine WP.mono (baseBitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => ?_⟩
  rw [h₂.bits t (by omega), scalar_bit _ _ ht]

end VG.Proof.Ed448.Arm
