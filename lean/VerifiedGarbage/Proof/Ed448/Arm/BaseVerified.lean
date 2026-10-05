import VerifiedGarbage.Proof.X448.Arm.Verified
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.BaseBits`. -/
section

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
      VG.Proof.X448.Arm.Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r2] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    VG.Proof.X448.Arm.Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r2] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (baseBitJ n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.Ed448.Arm.baseBitJ_ok (hs.of_keeps tk (by decide)) hi
      (by rw [tk.1 .r7 (by decide), tk.1 .r0 (by decide)]; exact hp)
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, VG.Proof.X448.Arm.writeW8_apply]
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
    WP isa (.block VG.Proof.Ed448.Arm.baseBitHead) s fun t =>
      t.gpr .r3 = (s.mem (off k i)).setWidth 32 ∧
      t.gpr .r7 = t.gpr .r0 + BitVec.ofNat 32 (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r7] s t := by
  unfold VG.Proof.Ed448.Arm.baseBitHead
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
    WP isa (.block VG.Proof.Ed448.Arm.baseBitTail) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 57) ∧
      t.mem = s.mem ∧ Keeps [.r11] s t := by
  have check : ∀ n < 57,
      ((BitVec.ofNat 32 n + (1 : BitVec 32) - (57 : BitVec 32)) == 0) = decide (n + 1 = 57) :=
    by decide +kernel
  unfold VG.Proof.Ed448.Arm.baseBitTail
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
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 57) ∧ Keeps VG.Proof.Ed448.Arm.baseBitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      VG.Proof.X448.Arm.Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (VG.Proof.Ed448.Arm.baseBitHead ++ (List.range 8).flatMap baseBitJ ++ VG.Proof.Ed448.Arm.baseBitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.Arm.baseBitHead_ok hk hfit hi hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.Arm.baseByteBits_ok (hs.of_keeps tk (by decide)) hi tp ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .r11 = BitVec.ofNat 32 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (VG.Proof.Ed448.Arm.baseBitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
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
  gpr : ∀ r, r ∉ VG.Proof.Ed448.Arm.baseBitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X448.Arm.Outside base BITS 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem baseBitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → VG.Proof.Ed448.Arm.BitsInv base k s₀ s i →
      WP isa (.loop (.block baseBitsBody) .ne) s fun s' => VG.Proof.Ed448.Arm.BitsInv base k s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block baseBitsBody) (c := .ne)
    (Q := fun s' => VG.Proof.Ed448.Arm.BitsInv base k s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ VG.Proof.Ed448.Arm.BitsInv base k s₀ s i) ?_ (57 - i) s
    ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.Ed448.Arm.baseBitsBody_ok hb.scr hb.r1 hb.fit hi hb.r11 (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : VG.Proof.Ed448.Arm.BitsInv base k s₀ s' (i + 1) := by
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
  rw [Proof.Ed448.decodeLE_eq, Proof.X25519.leNum_bit, VG.Proof.Ed448.Arm.bytesAt_getD m p (by omega)]

/-- `baseBits`: byte `t` of `BITS` is bit `t` of the scalar, for `t < 456`. -/
theorem baseBits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa baseBits s fun s' =>
      (∀ r, r ∉ VG.Proof.Ed448.Arm.baseBitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X448.Arm.Outside base BITS 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem k 57) >>> t) &&& 1) := by
  unfold baseBits
  refine WP.seq (WP.mono (show WP isa (.block [.mov .r11 (.imm 0)]) s
      (fun s' => VG.Proof.Ed448.Arm.BitsInv base k s s' 0) by
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide))
      fun t ht => WP.block_nil ?_
    have keep : Keeps VG.Proof.Ed448.Arm.baseBitRegs s t := rest_keeps (ht.rest (by decide))
    exact ⟨hs.of_keeps keep (by decide), by rw [ht.other .r1 (by decide)]; exact hk,
      by rw [ht.other .r1 (by decide)]; exact hfit, ht.gpr, keep.1, keep.2.1, keep.2.2,
      ht.mem ▸ Outside.refl _ _ _ _, fun _ hi => by omega⟩) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.Ed448.Arm.baseBitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => ?_⟩
  rw [h₂.bits t (by omega), VG.Proof.Ed448.Arm.scalar_bit _ _ ht]

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.BaseEncode`. -/
section

/-!
# Ed448 base-point multiplication on ARMv7: the encoding

`baseEncode`: `Z` inverted into slot 21, `y = Y/Z` into slot 4 and
`x = X/Z` into slot 1; `x` fully reduced and its low bit kept in `r8`; `y`
copied into slot 1, fully reduced and written to the output's first 56
bytes, and the bit as the top bit of its 57th (RFC 8032 §5.2.2); then the
callee-saved registers restored (`baseEncode_ok`). The 57 bytes are
`encodePoint` of the point in slots 0–2 (`Proof.Ed448.encodePoint_code`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC ld saved)
open VG.Spec.Ed448 (bytesAt)

theorem invEnv_x0 (e : Env) : invEnv e 0 = e 0 := rfl

theorem bytesAt_57 (m : Mem) (q : Addr) :
    bytesAt m q 57 = Spec.X448.bytesAt m q 56 ++ [m (q + BitVec.ofNat 64 56)] := by
  simp only [bytesAt, Spec.X448.bytesAt, show 57 = 56 + 1 from rfl, List.range_succ, List.map_append,
    List.map_cons, List.map_nil]

/-- `r8 = 128 · (limb 0 of slot 1 mod 2)`. -/
theorem signBit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block signBit) s fun t =>
      (t.gpr .r8).toNat = 128 * (limbs s.mem base X2 0 % 2) ∧ t.mem = s.mem ∧ Keeps [.r8] s t := by
  unfold signBit
  refine load_ok hs (by decide) fun u hu => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun v hv => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsl (by decide)) fun t ht =>
    WP.block_nil ⟨?_, by rw [ht.mem, hv.mem, hu.mem], rest_keeps ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans (ht.rest (by decide))))⟩
  have h1 : (v.gpr .r8).toNat = limbs s.mem base X2 0 % 2 := by
    rw [hv.gpr]; change (u.gpr .r8 &&& 1#32).toNat = _
    rw [BitVec.toNat_and, show (1#32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hu.gpr]
    rfl
  rw [ht.gpr, VG.Proof.X25519.Arm.toNat_shl, h1, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The value of slot 1 mod 2 is its limb 0's. -/
theorem fe_mod2 (m : Mem) (base : Addr) : fe m base X2 % 2 = limbs m base X2 0 % 2 := by
  have h : ∀ n, VG.Proof.X448.Radix16.valN (limbs m base X2) (n + 1) % 2 = limbs m base X2 0 % 2 := by
    intro n
    induction n with
    | zero => simp [VG.Proof.X448.Radix16.valN]
    | succ n ih =>
      have e : (2 ^ 16) ^ (n + 1) * limbs m base X2 (n + 1) =
          2 * ((2 ^ 16) ^ n * 2 ^ 15 * limbs m base X2 (n + 1)) := by
        rw [Nat.pow_succ]; grind
      rw [VG.Proof.X448.Radix16.valN_succ, Nat.add_mod, ih, VG.Proof.X448.Radix16.radix, e, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
  exact h 27

theorem byte56_write (m : Mem) (q : Addr) (v : Byte) :
    (m.writeW (q + BitVec.ofNat 64 56) v) (q + BitVec.ofNat 64 56) = v := by
  simp [Mem.writeW, Mem.write]

theorem bytes56_write {m : Mem} {q : Addr} (v : Byte) :
    Spec.X448.bytesAt (m.writeW (q + BitVec.ofNat 64 56) v) q 56 = Spec.X448.bytesAt m q 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff _ q (by omega), Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

def encodeFields : List FieldOp := [.mul 4 1 21, .mul 1 0 21]

theorem encodeFields_impl :
    encodeFields.map FieldOp.impl = [.mul (slot 4) (slot 1) (slot 21), .mul X2 (slot 0) (slot 21)] := by
  decide +kernel

/-- A word of the working space is beyond the output. -/
theorem far57 {base q : Addr} (hd : (⟨q, 57⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 57 ≤ ofs q (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_
    (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs q (off base i) + 1 ≤ 57
  omega

/-- The registers the encoding may change. -/
def encRegs : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem baseEncode_ok {s : State} {base q : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hq : State.addr (s.gpr .r12) = q) (hfit : (s.gpr .r12).toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨q, 57⟩ : Region) ∈ s.wr) (hd : (⟨q, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {g : Reg → BitVec 32} (sv : VG.Proof.X448.Arm.Saved base g s.mem) :
    WP isa baseEncode s fun t =>
      bytesAt t.mem q 57 = Spec.Ed448.encodePoint ⟨E s.mem base 0, E s.mem base 1, E s.mem base 2⟩ ∧
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧ Keeps VG.Proof.Ed448.Arm.encRegs s t ∧
      Frame [⟨base, 8192⟩, ⟨q, 57⟩] s.mem t.mem := by
  have hfar56 : ∀ j < 8192, 56 ≤ ofs q (off base j) := fun j hj => Nat.le_trans (by decide) (VG.Proof.Ed448.Arm.far57 hd hj)
  have hw56 : ∀ j < 57, InRegions s.wr (off q j) 1 := fun j hj =>
    ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
  unfold baseEncode
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.invert_ok hs hb) fun s₁ ⟨k₁, b₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  rw [← VG.Proof.Ed448.Arm.encodeFields_impl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok hs₁ b₁ VG.Proof.Ed448.Arm.encodeFields) fun s₂ ⟨k₂, b₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have ex : E s₂.mem base 1 = E s.mem base 0 * Proof.X448.invert (E s.mem base 2) := by
    rw [e₂, e₁]
    simp only [applyOps, VG.Proof.Ed448.Arm.encodeFields, FieldOp.apply, VG.Proof.X448.Arm.opMul, Function.update_self]
    rw [Function.update_of_ne (show (21 : Index) ≠ 4 by decide),
      Function.update_of_ne (show (0 : Index) ≠ 4 by decide), VG.Proof.Ed448.Arm.invEnv_x0, invEnv_eval]
  have ey : E s₂.mem base 4 = E s.mem base 1 * Proof.X448.invert (E s.mem base 2) := by
    rw [e₂, e₁]
    simp only [applyOps, VG.Proof.Ed448.Arm.encodeFields, FieldOp.apply, VG.Proof.X448.Arm.opMul]
    rw [Function.update_of_ne (show (4 : Index) ≠ 1 by decide), Function.update_self, invEnv_x2,
      invEnv_eval]
  simp only [List.append_assoc]
  -- `x` fully reduced, and its bit.
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.X448.Arm.freeze_ok hs₂ (b₂ 1)) fun s₃ ⟨bx₃, vx₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.signBit_ok hs₃) fun s₄ ⟨r₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hx : (E s₂.mem base 1).val = fe s₂.mem base X2 % Spec.X448.P := Proof.X448.toFe_val _
  have bit : (s₄.gpr .r8).toNat = 128 * ((E s.mem base 0 * Proof.X448.invert (E s.mem base 2)).val % 2) := by
    rw [r₄, ← VG.Proof.Ed448.Arm.fe_mod2, vx₃, ← hx, ex]
  have E₄ : E s₄.mem base = E s₂.mem base := by
    rw [m₄, E_update (o := 1) m₃]
    funext i
    by_cases hi : i = 1
    · subst hi; rw [Function.update_self]
      change Proof.X448.toFe (fe s₃.mem base X2) = Proof.X448.toFe (fe s₂.mem base X2)
      rw [vx₃]; exact Proof.X448.toFe_mod _
    · rw [Function.update_of_ne hi]
  have b₄ : BoundedEnv s₄.mem base := m₄ ▸ bounded_update (o := 1) m₃ b₂ bx₃
  -- `y` into slot 1, fully reduced.
  refine VG.Proof.X25519.Arm.WP.append (copyE hs₄ b₄ 1 4) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_
  have hs₅ := k₅.scr hs₄
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.X448.Arm.freeze_ok hs₅ (b₅ 1)) fun s₆ ⟨by₆, vy₆, m₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have y₆ : fe s₆.mem base X2 = (E s.mem base 1 * Proof.X448.invert (E s.mem base 2)).val := by
    have hy : (E s₅.mem base 1).val = fe s₅.mem base X2 % Spec.X448.P := Proof.X448.toFe_val _
    have h5 : E s₅.mem base 1 = E s₄.mem base 4 := by
      rw [e₅]; exact Function.update_self _ _ _
    rw [vy₆, ← hy, h5, E₄, ey]
  -- The output.
  have r12₆ : s₆.gpr .r12 = s.gpr .r12 := by
    rw [k₆.1 _ (by decide), k₅.regs.1 _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide),
      k₂.regs.1 _ (by decide), k₁.regs.1 _ (by decide)]
  have wr₆ : s₆.wr = s.wr := by
    rw [k₆.2.2, k₅.regs.2.2, k₄.2.2, k₃.2.2, k₂.regs.2.2, k₁.regs.2.2]
  refine VG.Proof.X25519.Arm.WP.append (output_ok (p := q) hs₆ by₆ (by rw [r12₆]; exact hq)
    (by rw [r12₆]; omega) (fun j hj => by rw [wr₆]; exact hw56 j (by omega)) hfar56)
    fun s₇ ⟨v₇, o₇, k₇⟩ => ?_
  have r8₇ : s₇.gpr .r8 = s₄.gpr .r8 := by
    rw [k₇.1 _ (by decide), k₆.1 _ (by decide), k₅.regs.1 _ (by decide)]
  refine VG.Proof.X25519.Arm.wp_strb (a := q + BitVec.ofNat 64 56) (by decide)
    (by rw [k₇.1 _ (by decide), r12₆]; rw [VG.Arm.addr_add (by omega), hq])
    (by rw [k₇.2.2, wr₆]; exact hw56 56 (by decide)) fun s₈ u₈ => ?_
  -- The saved registers.
  have sv₂ : VG.Proof.X448.Arm.Saved base g s₂.mem := (sv.outside2 k₁.mem (by decide) (by decide)).outside2 k₂.mem
    (by decide) (by decide)
  have sv₄ : VG.Proof.X448.Arm.Saved base g s₄.mem := m₄ ▸ sv₂.field m₃ (by decide)
  have sv₆ : VG.Proof.X448.Arm.Saved base g s₆.mem := (sv₄.outside2 k₅.mem (by decide) (by decide)).field m₆ (by decide)
  have o₈ : VG.Proof.X448.Arm.Outside q 0 57 s₆.mem s₈.mem := by
    refine (o₇.mono (by decide) (by decide)).trans fun x hx => ?_
    rw [u₈.mem]
    exact writeW8_outside _ _ _ (d := 56) (by decide) (by omega)
  have w₈ : ∀ d, d + 4 ≤ 8192 → word s₈.mem base d = word s₆.mem base d := fun d hd4 =>
    Mem.readW_congr fun i hi => by
      rw [Offset.add_add]
      exact o₈ _ (Or.inr (VG.Proof.Ed448.Arm.far57 hd (i := d + i) (by omega)))
  have sv₈ : VG.Proof.X448.Arm.Saved base g s₈.mem := fun i hi => (w₈ _ (by omega)).trans (sv₆ i hi)
  have hs₈ : Scr s₈ base := hs₆.of_keeps (k₇.trans (rest_keeps (u₈.rest VG.Proof.X448.Arm.clob))) (by decide)
  refine WP.mono (VG.Proof.X448.Arm.restore_ok hs₈ sv₈) fun t ⟨rt, mt, kt⟩ => ?_
  refine ⟨?_, rt, ?_, ?_⟩
  · rw [mt, VG.Proof.Ed448.Arm.bytesAt_57, u₈.mem, VG.Proof.Ed448.Arm.bytes56_write, VG.Proof.Ed448.Arm.byte56_write, v₇, y₆, r8₇, Proof.Ed448.encodePoint_code]
    refine congrArg (fun b => _ ++ [b]) ?_
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, bit]
  · refine (k₁.regs.mono ?_).trans ((k₂.regs.mono ?_).trans ((k₃.mono ?_).trans ((k₄.mono ?_).trans
      ((k₅.regs.mono ?_).trans ((k₆.mono ?_).trans ((k₇.mono ?_).trans
      ((rest_keeps (u₈.rest VG.Proof.Ed448.Arm.encRegs)).trans (kt.mono ?_))))))))
    all_goals intro r hr; revert r; decide
  · have fw : VG.Proof.X448.Arm.Outside base 0 8192 s.mem s₆.mem :=
      (((((k₁.mem.whole (by decide) (by decide)).trans (k₂.mem.whole (by decide) (by decide))).trans
        (m₃.whole (by decide))).trans (by rw [m₄]; exact Outside.refl _ _ _ _)).trans
        (k₅.mem.whole (by decide) (by decide))).trans (m₆.whole (by decide))
    rw [mt]
    exact ((Outside.frame fw).mono (by simp)).trans ((Outside.frame o₈).mono (by simp))

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.BaseInit`. -/
section

/-!
# Ed448 base-point multiplication on ARMv7: the entry

The callee-saved registers saved (X448's `setupHead`) and every slot set to
its initial value (`initSlots_ok`): `R = (0 : 1 : 1)`, `Q` the base point, `d`,
and zero elsewhere, every limb below `2¹⁶`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot ACC st)

theorem initVal_lt (i : Nat) : initVal i < Spec.X448.P := by
  unfold initVal
  repeat (first | exact Fin.isLt _ | (split; exact Fin.isLt _) | split)
  decide +kernel

theorem initLimb_lt (i k : Nat) : initLimb i k < 65536 := Nat.mod_lt _ (by decide)

theorem valN_digits (v : Nat) : ∀ n, VG.Proof.X448.Radix16.valN (fun k => v / 2 ^ (16 * k) % 65536) n = v % VG.Proof.X448.Radix16.radix ^ n
  | 0 => by simp [VG.Proof.X448.Radix16.valN, Nat.mod_one]
  | n + 1 => by
    rw [VG.Proof.X448.Radix16.valN_succ, VG.Proof.Ed448.Arm.valN_digits v n, Nat.mod_pow_succ, VG.Proof.X448.Radix16.radix, ← Nat.pow_mul]

theorem initStep_ok {s : State} {base : Addr} (hs : Scr s base) (h4 : s.gpr .r4 = 0) {i k : Nat}
    (hi : i < 22) (hk : k < 28) :
    WP isa (.block (initStep i k)) s fun t =>
      t.mem = s.mem.writeW (off base (slot i + 4 * k)) (BitVec.ofNat 32 (initLimb i k)) ∧
        Keeps [.r3] s t := by
  have hsl : slot i + 4 * k + 4 ≤ 4096 := by simp only [slot]; omega
  unfold initStep
  split
  · rename_i h0
    refine store_ok hs (by omega) fun t ht => WP.block_nil ⟨?_, ⟨fun r _ => by rw [ht.gpr], ht.rd, ht.wr⟩⟩
    rw [ht.mem, h4, h0]; rfl
  · refine VG.Proof.X25519.Arm.wp_movw fun u hu => ?_
    refine store_ok (hs.of_upd hu (by decide) (by decide)) (by omega) fun t ht => WP.block_nil ⟨?_, ?_⟩
    · rw [ht.mem, hu.mem, hu.gpr]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (VG.Proof.Ed448.Arm.initLimb_lt i k)]
    · exact ⟨fun r hr => by rw [ht.gpr, hu.other r (fun h => hr (by simp [h]))], by rw [ht.rd, hu.rd],
        by rw [ht.wr, hu.wr]⟩

theorem initSlot_ok {s : State} {base : Addr} (hs : Scr s base) (h4 : s.gpr .r4 = 0) {i : Nat}
    (hi : i < 22) :
    WP isa (.block (initSlot i)) s fun t =>
      (∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        VG.Proof.X448.Arm.Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.r3] s t := by
  have hsl : slot i + 112 ≤ 4096 := by simp only [slot]; omega
  let inv := fun n (t : State) => (∀ k < n, limbs t.mem base (slot i) k = initLimb i k) ∧
    VG.Proof.X448.Arm.Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.r3] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (VG.Proof.Ed448.Arm.initStep_ok (hs.of_keeps tk (by decide)) ((tk.1 _ (by decide)).trans h4) hi hn)
    fun u ⟨um, uk⟩ => ⟨fun k hk => ?_, tm.trans ?_, tk.trans uk⟩
  · change (word u.mem base (slot i + 4 * k)).toNat = _
    rw [um, word_write t.mem base (by omega) (by omega)]
    by_cases h : k = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.Ed448.Arm.initLimb_lt i n; omega)]
    · rw [ite_eq_right h]; exact tf k (by omega)
  · rw [um]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block initSlots) s fun t =>
      (∀ i < 22, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        VG.Proof.X448.Arm.Outside base 64 2816 s.mem t.mem ∧ Keeps [.r3, .r4] s t := by
  unfold initSlots
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  have hsu := hs.of_upd hu (by decide) (by decide)
  have ku : Keeps [.r3, .r4] s u := rest_keeps (hu.rest (by decide))
  let inv := fun n (t : State) => (∀ i < n, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
    VG.Proof.X448.Arm.Outside base 64 2816 u.mem t.mem ∧ Keeps [.r3] u t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 22
    (by decide) u ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨tf, tm, tk⟩ => ⟨tf, by rw [← hu.mem]; exact tm, ku.trans (tk.mono (by simp))⟩
  refine WP.mono (VG.Proof.Ed448.Arm.initSlot_ok (hsu.of_keeps tk (by decide)) ((tk.1 _ (by decide)).trans hu.gpr) hn)
    fun v ⟨vf, vm, vk⟩ => ⟨fun i hi k hk => ?_, tm.trans (vm.mono (by simp only [slot]; omega)
      (by simp only [slot]; omega)), tk.trans vk⟩
  by_cases h : i = n
  · subst h; exact vf k hk
  · rw [vm.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) hk]
    exact tf i (by omega) k hk

/-- The slots' values. -/
theorem initSlots_E {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) (i : Index) :
    E m base i = Proof.X448.toFe (initVal i.val) := by
  simp only [E, F, fe]
  rw [VG.Proof.X448.Radix16.valN_congr (g := fun k => initVal i.val / 2 ^ (16 * k) % 65536) (h i.val i.isLt), VG.Proof.Ed448.Arm.valN_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans (VG.Proof.Ed448.Arm.initVal_lt _) (by decide +kernel))]

theorem initSlots_bounded {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) : BoundedEnv m base :=
  fun i k hk => by rw [h i.val i.isLt k hk]; exact VG.Proof.Ed448.Arm.initLimb_lt _ _

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.BaseLit`. -/
section

/-!
# Ed448 base-point multiplication on ARMv7: the code as a literal

The kernel checks the literal once.

The constant-time analysis, from the arguments alone, reads neither the
offsets of loads and stores nor the immediates of `movw`
(`Proof/Framework/Arm/TaintErase.lean`), so it checks the code without them,
`scalarBaseErased`: there the field operations on the working space's slots
are the same code, which its literal shares, and the kernel analyses each
once from the same taint rather than every copy.
-/

namespace VG

materialize_code Impl.Ed448.Arm.scalarBase

/-- `scalarBase` without its offsets. -/
def Proof.Ed448.Arm.scalarBaseErased : Prog Arm.isa := Arm.Code.eraseOff Impl.Ed448.Arm.scalarBase

materialize_code Proof.Ed448.Arm.scalarBaseErased

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.BaseStep`. -/
section

/-!
# Ed448 base-point multiplication on ARMv7: the loop over the bits

The doubling and addition programs run as X448's verified field operations
on the slots (`ops_ok`), and evaluate to `double` and the specification's
`pointAdd` (`baseEnv_r`): `Proof/Ed448/Ref.lean`'s `ladderStep`. One iteration (`baseStep_ok`) doubles `R`
(slots 0–2), adds `Q` (slots 8–10) into `T` (slots 3–5) and swaps `T` into
`R` with the mask of the bit; the loop (`baseLoop_ok`) leaves `R` as the
ladder over all 456 bits, `ladder k 456`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (double ladderStep ladder bitAt ladder_bit)
open VG.Impl.X448.Arm (BITS slot ACC)

/-! ## The field programs -/

def doubleFields : List FieldOp := [
  .add 12 0 1, .mul 12 12 12, .mul 13 0 0, .mul 14 1 1, .add 15 13 14, .mul 16 2 2,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul 0 18 17, .sub 19 13 14, .mul 1 15 19,
  .mul 2 15 17]

def addFields : List FieldOp := [
  .mul 12 2 10, .mul 13 12 12, .mul 14 0 8, .mul 15 1 9, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 8 9, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

theorem doubleFields_impl : doubleFields.map FieldOp.impl = VG.Impl.Ed448.Arm.doubleOps := by decide +kernel
theorem addFields_impl : addFields.map FieldOp.impl = VG.Impl.Ed448.Arm.addOps := by decide +kernel

/-- The point in slots `i`, `j`, `k`. -/
def pt (e : Env) (i j k : Index) : Spec.Ed448.Point := ⟨e i, e j, e k⟩

/-- The slots after an iteration, for the bit `sw`. -/
def baseEnv (sw : Bool) (e : Env) : Env :=
  opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw (applyOps VG.Proof.Ed448.Arm.addFields (applyOps VG.Proof.Ed448.Arm.doubleFields e))))

/-- The specification's addition, with `d` a parameter. -/
def addWith (dd : Spec.X448.Fe) (p q : Spec.Ed448.Point) : Spec.Ed448.Point :=
  let a := p.Z * q.Z
  let b := a * a
  let c := p.X * q.X
  let d' := p.Y * q.Y
  let e := dd * c * d'
  let f := b - e
  let g := b + e
  let h := (p.X + p.Y) * (q.X + q.Y)
  ⟨a * f * (h - c - d'), a * g * (d' - c), f * g⟩

theorem baseEnv_pt (sw : Bool) (e : Env) :
    VG.Proof.Ed448.Arm.pt (VG.Proof.Ed448.Arm.baseEnv sw e) 0 1 2 =
      if sw then VG.Proof.Ed448.Arm.addWith (e 11) (double (VG.Proof.Ed448.Arm.pt e 0 1 2)) (VG.Proof.Ed448.Arm.pt e 8 9 10) else double (VG.Proof.Ed448.Arm.pt e 0 1 2) := by
  cases sw <;> rfl

theorem baseEnv_r (sw : Bool) (e : Env) (hq : VG.Proof.Ed448.Arm.pt e 8 9 10 = Spec.Ed448.basePoint)
    (hd : e 11 = Spec.Ed448.d) :
    VG.Proof.Ed448.Arm.pt (VG.Proof.Ed448.Arm.baseEnv sw e) 0 1 2 = ladderStep sw (VG.Proof.Ed448.Arm.pt e 0 1 2) := by
  rw [VG.Proof.Ed448.Arm.baseEnv_pt, hq, hd]; rfl

theorem baseEnv_q (sw : Bool) (e : Env) : VG.Proof.Ed448.Arm.pt (VG.Proof.Ed448.Arm.baseEnv sw e) 8 9 10 = VG.Proof.Ed448.Arm.pt e 8 9 10 := by
  cases sw <;> rfl

theorem baseEnv_d (sw : Bool) (e : Env) : VG.Proof.Ed448.Arm.baseEnv sw e 11 = e 11 := by
  cases sw <;> rfl

/-! ## One iteration -/

theorem decR11_ok {s : State} {t : Nat}
    (hb : s.gpr .r11 = BitVec.ofNat 32 (t + 1)) :
    WP isa (.block [.dp .sub .r11 .r11 (.imm 1)]) s fun u =>
      u.gpr .r11 = BitVec.ofNat 32 t ∧ (∀ r, r ≠ .r11 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧
        u.rd = s.rd ∧ u.wr = s.wr :=
  VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => WP.block_nil
    ⟨by rw [hu.gpr]; change s.gpr .r11 - BitVec.ofNat 32 1 = _
        rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel], hu.other, hu.mem, hu.rd, hu.wr⟩

theorem mask_byte : ∀ b < 2, (0 : BitVec 32) - (BitVec.ofNat 8 b).setWidth 32 = mask (decide (b = 1)) := by
  decide

theorem baseMask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .r11 = BitVec.ofNat 32 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block baseMask) s fun u =>
      u.gpr .r5 = mask (decide (b = 1)) ∧ Keeps workRegs s u ∧ u.mem = s.mem := by
  have hB : BITS = 3072 := rfl
  unfold baseMask
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u1 v1 => ?_
  have ba : State.addr (u1.gpr .r7 + BitVec.ofNat 32 BITS) = off base (BITS + t) := by
    rw [v1.gpr]; change State.addr (s.gpr .r0 + s.gpr .r11 + BitVec.ofNat 32 BITS) = _
    rw [hb, Offset.add_add, Nat.add_comm t BITS]
    exact hs.ea (by omega)
  refine VG.Proof.X25519.Arm.wp_ldrb (by omega) ba
    (by rw [v1.rd, v1.wr]; exact hs.read (by omega)) fun u2 v2 => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u3 v3 => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u4 v4 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v4.gpr]; change u3.gpr .r5 - u3.gpr .r3 = _
    rw [v3.gpr, v3.other _ (by decide), v2.gpr, v1.mem, hbit]
    exact VG.Proof.Ed448.Arm.mask_byte b hb2
  · exact rest_keeps ((v1.rest (ws := workRegs) (by decide)).trans ((v2.rest (by decide)).trans
      ((v3.rest (by decide)).trans (v4.rest (by decide)))))
  · rw [v4.mem, v3.mem, v2.mem, v1.mem]

theorem baseSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base)
    {t : Nat} (ht : t < 456) (hb : s.gpr .r11 = BitVec.ofNat 32 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block baseSwap) s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      u.z = decide (t = 0) ∧
      E u.mem base = opSwap 2 5 (decide (b = 1)) (opSwap 1 4 (decide (b = 1))
        (opSwap 0 3 (decide (b = 1)) (E s.mem base))) := by
  unfold baseSwap
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.baseMask_ok hs ht hb hb2 hbit) fun u1 ⟨c1, k1, m1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have K1 : Keep base s u1 := ⟨k1, by rw [m1]; exact Outside2.refl _ _ _ _ _ _⟩
  refine VG.Proof.X25519.Arm.WP.append (cswapE hs1 (m1 ▸ hbd) 0 3 (by decide) c1) fun u2 ⟨k2, b2, c2, e2⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (cswapE (k2.scr hs1) b2 1 4 (by decide) (c2.trans c1)) fun u3 ⟨k3, b3, c3, e3⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (cswapE (k3.scr (k2.scr hs1)) b3 2 5 (by decide) (c3.trans (c2.trans c1)))
    fun u4 ⟨k4, b4, _, e4⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u5 v5 hz =>
    WP.block_nil ?_
  have K5 : Keep base u4 u5 := ⟨rest_keeps (v5.rest _), by rw [v5.mem]; exact Outside2.refl _ _ _ _ _ _⟩
  refine ⟨K1.trans (k2.trans (k3.trans (k4.trans K5))), v5.mem ▸ b4, ?_, by rw [v5.mem, e4, e3, e2, m1]⟩
  have r11 : u4.gpr .r11 = BitVec.ofNat 32 t := by
    rw [k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.regs.1 _ (by decide),
      k1.1 _ (by decide), hb]
  rw [hz, r11]
  change (BitVec.ofNat 32 t - BitVec.ofNat 32 0 == 0) = _
  rw [BitVec.sub_zero]
  exact VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)

/-- The loop's invariant, after the bits above `n` of `k`. -/
structure BaseInv (base : Addr) (k : Nat) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.r11 :: workRegs) s₀ s
  r11 : s.gpr .r11 = BitVec.ofNat 32 n
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  r : VG.Proof.Ed448.Arm.pt (E s.mem base) 0 1 2 = ladder k (456 - n)
  q : VG.Proof.Ed448.Arm.pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  d : E s.mem base 11 = Spec.Ed448.d

theorem bit_lt (k t : Nat) : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem baseStep_ok {s₀ s : State} {base : Addr} {k n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : VG.Proof.Ed448.Arm.BaseInv base k s₀ s (n + 1)) :
    WP isa baseStep s fun t => VG.Proof.Ed448.Arm.BaseInv base k s₀ t n ∧ t.z = decide (n = 0) := by
  have hs := hi.scr
  have hB : BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  have bitval : s.mem (off base (BITS + n)) = BitVec.ofNat 8 ((k >>> n) &&& 1) := by
    rw [hi.mem _ (by rw [ofs_off' base (by omega)]; omega) (by rw [ofs_off' base (by omega)]; omega)]
    exact hbits n hn
  unfold baseStep
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.decR11_ok hi.r11) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have K₁ : Keeps [.r11] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  have hs₁ := hs.of_keeps K₁ (by decide)
  rw [← VG.Proof.Ed448.Arm.doubleFields_impl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok hs₁ (m₁ ▸ hi.bounded) VG.Proof.Ed448.Arm.doubleFields) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  rw [← VG.Proof.Ed448.Arm.addFields_impl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok (k₂.scr hs₁) bb₂ VG.Proof.Ed448.Arm.addFields) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr (k₂.scr hs₁)
  have b₃ : s₃.gpr .r11 = BitVec.ofNat 32 n := by
    rw [k₃.regs.1 _ (by decide), k₂.regs.1 _ (by decide), b₁]
  have bit₃ : s₃.mem (off base (BITS + n)) = BitVec.ofNat 8 ((k >>> n) &&& 1) := by
    rw [(k₂.trans k₃).mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), m₁, bitval]
  refine WP.mono (VG.Proof.Ed448.Arm.baseSwap_ok hs₃ bb₃ (by omega) b₃ (VG.Proof.Ed448.Arm.bit_lt k n) bit₃) fun t ⟨k₄, bb₄, z₄, e₄⟩ => ?_
  have core := k₂.trans (k₃.trans k₄)
  have ee : E t.mem base = VG.Proof.Ed448.Arm.baseEnv (decide ((k >>> n) &&& 1 = 1)) (E s.mem base) := by
    rw [e₄, e₃, e₂, m₁]; rfl
  refine ⟨⟨core.scr hs₁, bb₄, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₄⟩
  · refine hi.regs.trans ⟨fun r hr => ?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    rw [core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), g₁ r (fun h => hr (by simp [h]))]
  · rw [core.regs.1 _ (by decide), b₁]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p hp hq, m₁]
  · rw [ee, VG.Proof.Ed448.Arm.baseEnv_r _ _ hi.q hi.d, hi.r, ladder_bit k hn]; rfl
  · rw [ee, VG.Proof.Ed448.Arm.baseEnv_q]; exact hi.q
  · rw [ee, VG.Proof.Ed448.Arm.baseEnv_d]; exact hi.d

theorem baseLoop_ok {s₀ s : State} {base : Addr} {k : Nat}
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : ∀ s', s'.gpr .r11 = BitVec.ofNat 32 456 → (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.Ed448.Arm.BaseInv base k s₀ s' 456) :
    WP isa baseLoop s fun s' => VG.Proof.Ed448.Arm.BaseInv base k s₀ s' 0 := by
  unfold baseLoop
  refine WP.seq (WP.mono (setCounter_ok s 456 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := baseStep) (c := .ne) (Q := fun s' => VG.Proof.Ed448.Arm.BaseInv base k s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VG.Proof.Ed448.Arm.BaseInv base k s₀ s m) ?_ 456 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.Ed448.Arm.baseStep_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.BaseMain`. -/
section

/-!
# Ed448 base-point multiplication on ARMv7: the whole function

`vg_ed448_scalar_base(out = r0, scalar = r1, scratch = r2)` computes the
encoding of the ladder over the scalar's bits (`scalarBase_ladder`): the
entry, the scalar's bits, the loop (`R` ends as `ladder k 456`), the
inversion of `Z` and the encoding. Every write is in the working space but
the result's, so the scalar is read unchanged; the callee-saved registers are
restored from the working space, and the return address is kept.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (ladder)
open VG.Impl.X448.Arm (slot BITS ACC saved)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The precondition of `vg_ed448_scalar_base`, by name. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 57⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 57⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_ws : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  scalar_ws : (⟨State.addr (s.gpr .r1), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 57 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far_ws {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega)
    (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem baseEntry_eq : baseEntry =
    ([.mov .r3 (.reg .r2)] : List Instr) ++ setupHead ++ initSlots := rfl

theorem scalarBase_ladder {s : State} (h : VG.Proof.Ed448.Arm.BasePre s) :
    WP isa scalarBase s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
        Spec.Ed448.encodePoint (ladder (decodeLE (bytesAt s.mem (State.addr (s.gpr .r1)) 57)) 456) := by
  obtain ⟨base, hbase⟩ : ∃ b, State.addr (s.gpr .r2) = b := ⟨_, rfl⟩
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [h.wr, ← hbase]; simp
  have kd : ∀ j < 57, 8192 ≤ ofs base (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) :=
    fun j hj => VG.Proof.Ed448.Arm.far_ws (hbase ▸ h.scalar_ws) hj (by decide)
  have kr : ∀ j < 57, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1 :=
    fun j hj => ⟨⟨State.addr (s.gpr .r1), 57⟩, by rw [h.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  unfold scalarBase
  rw [VG.Proof.Ed448.Arm.baseEntry_eq, List.append_assoc, List.singleton_append]
  -- The entry.
  refine WP.seq (VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun u hu => ?_)
  refine VG.Proof.X25519.Arm.WP.append (setupHead_ok (s := u) (base := base) (by rw [hu.gpr, hbase])
    (by rw [hu.wr]; exact hw₀) (by rw [hu.gpr]; exact h.f2)) fun v ⟨hsv, rv, svv, ov, kv⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.Arm.initSlots_ok hsv) fun w ⟨lw, ow, kw⟩ => ?_
  have hsw : Scr w base := hsv.of_keeps kw (by decide)
  have kuw : Keeps [.r3, .r12, .r0, .r6, .r4] s w :=
    (rest_keeps (hu.rest (by decide))).trans ((kv.mono (by decide)).trans (kw.mono (by decide)))
  have r1w : w.gpr .r1 = s.gpr .r1 := kuw.1 _ (by decide)
  have r12w : w.gpr .r12 = s.gpr .r0 := by
    rw [kw.1 _ (by decide), rv, hu.other _ (by decide)]
  have mw : ∀ x, 8192 ≤ ofs base x → w.mem x = s.mem x := fun x hx => by
    rw [ow x (Or.inr (by omega)), ov x (Or.inr (by omega)), hu.mem]
  have bw : bytesAt w.mem (State.addr (s.gpr .r1)) 57 = bytesAt s.mem (State.addr (s.gpr .r1)) 57 := by
    unfold bytesAt; exact List.map_congr_left fun j hj => mw _ (kd j (List.mem_range.mp hj))
  have sn : ∀ i < 8, saved[i]! ≠ .r3 := by decide
  have svw : VG.Proof.X448.Arm.Saved base s.gpr w.mem := by
    intro i hi
    rw [ow.word (by omega) (by omega), svv i hi]
    exact hu.other _ (sn i hi)
  -- The scalar's bits.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.baseBits_ok (k := State.addr (s.gpr .r1)) hsw (by rw [r1w])
    (by rw [r1w]; exact h.f1) (by rw [kuw.2.1, kuw.2.2]; exact kr) kd)
    fun x ⟨gx, rdx, wrx, ox, bitsx⟩ => ?_)
  have kx : Keeps VG.Proof.Ed448.Arm.baseBitRegs w x := ⟨gx, rdx, wrx⟩
  have hsx : Scr x base := hsw.of_keeps kx (by decide)
  have ex : ∀ i : Index, E x.mem base i = Proof.X448.toFe (initVal i.val) := by
    intro i
    rw [← VG.Proof.Ed448.Arm.initSlots_E lw i]
    simp only [E, F]
    rw [ox.fe (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega)]
  have bx : BoundedEnv x.mem base := by
    intro i j hj
    rw [ox.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj]
    exact VG.Proof.Ed448.Arm.initSlots_bounded lw i j hj
  rw [bw] at bitsx
  -- The loop.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.baseLoop_ok (s₀ := x) (s := x) bitsx (fun s' h1 h2 h3 h4 h5 => ?_))
    fun y hy => ?_)
  · have k' : Keeps (.r11 :: workRegs) x s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hsx.of_keeps k' (by decide), h3 ▸ bx, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_⟩
    · rw [h3]; simp only [VG.Proof.Ed448.Arm.pt, ex]
      rw [show ((0 : Index) : Nat) = 0 from rfl, show ((1 : Index) : Nat) = 1 from rfl,
        show ((2 : Index) : Nat) = 2 from rfl, show initVal 0 = Spec.Ed448.identity.X.val from rfl,
        show initVal 1 = Spec.Ed448.identity.Y.val from rfl,
        show initVal 2 = Spec.Ed448.identity.Z.val from rfl, Proof.X448.toFe_self,
        Proof.X448.toFe_self, Proof.X448.toFe_self]
      rfl
    · rw [h3]; simp only [VG.Proof.Ed448.Arm.pt, ex]
      rw [show ((8 : Index) : Nat) = 8 from rfl, show ((9 : Index) : Nat) = 9 from rfl,
        show ((10 : Index) : Nat) = 10 from rfl, show initVal 8 = Spec.Ed448.basePoint.X.val from rfl,
        show initVal 9 = Spec.Ed448.basePoint.Y.val from rfl,
        show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self,
        Proof.X448.toFe_self, Proof.X448.toFe_self]
    · rw [h3, ex]; exact Proof.X448.toFe_self _
  -- The encoding.
  have r12y : y.gpr .r12 = s.gpr .r0 := by
    rw [hy.regs.1 _ (by decide), gx _ (by decide), r12w]
  have wry : y.wr = s.wr := by rw [hy.regs.2.2, wrx, kuw.2.2]
  have svy : VG.Proof.X448.Arm.Saved base s.gpr y.mem :=
    (svw.outside ox (by decide)).outside2 hy.mem (by decide) (by decide)
  refine WP.mono (VG.Proof.Ed448.Arm.baseEncode_ok hy.scr hy.bounded (q := State.addr (s.gpr .r0)) (by rw [r12y])
    (by rw [r12y]; exact h.f0) (by rw [wry, h.wr]; simp) (hbase ▸ h.out_ws) svy)
    fun t ⟨bt, rt, kt, _⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt 0 (by decide)
    · exact rt 1 (by decide)
    · exact rt 2 (by decide)
    · exact rt 3 (by decide)
    · exact rt 4 (by decide)
    · exact rt 5 (by decide)
    · exact rt 6 (by decide)
    · exact rt 7 (by decide)
    · rw [kt.1 _ (by decide), hy.regs.1 _ (by decide), gx _ (by decide), kuw.1 _ (by decide)]
  · rw [bt]
    exact congrArg Spec.Ed448.encodePoint hy.r
end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.BaseVerified`. -/
section

/-!
# Ed448 base-point multiplication on ARMv7: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter), satisfiability,
and the shared contract of `Spec/`, given that the ladder the code computes
encodes as `[k]B` (`Proof.Ed448.BaseLadderOk`, proven with the group law in
`Proof/Ed448/Facts.lean`, which only the registration file imports).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm
open VG.Proof.Ed448 (BaseLadderOk decodeLE_below)

/-- `vg_ed448_scalar_base(out = r0, scalar = r1, scratch = r2)`. -/
def scalarBaseLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let scalar : Region := ⟨State.addr (s.gpr .r1), 57⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [scalar] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ scalar.Disjoint ws ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s t := Spec.Ed448.bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
  pub s t := s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧ s.sp = t.sp

theorem BasePre.of {s : State} (h : scalarBaseLocal.pre s) : VG.Proof.Ed448.Arm.BasePre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

def scalarBaseSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

theorem scalarBase_ok (hl : BaseLadderOk) (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Ed448.Arm.scalarBase_ladder (BasePre.of hs)
  refine ⟨t, s', he, ⟨h.1, Exec.sp he⟩, ?_⟩
  change Spec.Ed448.bytesAt s'.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul _ Spec.Ed448.basePoint)
  rw [h.2, hl _ (decodeLE_below (by simp [Spec.Ed448.bytesAt]))]

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine Taint.constantTime_eraseOff_of_eq (Taint.ofRegs [.r0, .r1, .r2]) (Taint.noBase_ofRegs _) ?_
    (c' := VG.Proof.Ed448.Arm.scalarBaseErased) rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, _⟩
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem scalarBase_verified (hl : BaseLadderOk) :
    Verified Arm.target scalarBase (Spec.Ed448.scalarBaseContract Arm.abi) :=
  Verified.of_correct (VG.Proof.Ed448.Arm.scalarBase_ok hl) VG.Proof.Ed448.Arm.scalarBase_ct (by
    sig_implies [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.scalarBaseLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [scalarBaseSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Ed448.Arm.scalarBaseSat)

end VG.Proof.Ed448.Arm

end
