module

public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.X448.Ladder
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.Arm.BitWrite
public import VerifiedGarbage.Proof.X448.Arm.Iter
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.X448.Arm.Field
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.X448.Arm.Env
import VerifiedGarbage.Proof.X448.Arm.Counters

/-! ### `X448.Arm.FinalSwap`, which the modules that import this one used -/

section

/-! ### `X448.Arm.Ladder`, which the modules that import this one used -/

section

/-!
# X448 on ARMv7: all 448 ladder iterations

A decreasing public counter connects the loop to the specification's
descending fold over scalar bits.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

variable {fv : Bool}

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → LInv base k u s₀ s n →
      WP isa (.loop (step fv) .ne) s fun s' => LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := step fv) (c := .ne)
    (Q := fun s' => LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_using [h1]⟩
  refine WP.mono (step_ok (by omega_using [h2]) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega_using [hm] : ¬m = 0), Bool.not_false], m, by omega_using [],
      by omega_using [hm], by omega_using [h2], hi'⟩

/-- The ladder: the counter set to 448, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : ∀ s', s'.gpr .r11 = BitVec.ofNat 32 448 → (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → LInv base k u s₀ s' 448) :
    WP isa (ladder fv) s fun s' => LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (setCounter_ok s 448 (by decide))
    fun s' ⟨h1, h2, h3, h4, h5⟩ => loop_ok hbits 448 s' (by omega_using []) (by omega_using []) (hi s' h1 h2 h3 h4 h5))

end VG.Proof.X448.Arm

end

end

/-!
# X448 on ARMv7: the final ladder swap

The last swap bit selects the coordinates that are converted back to affine
form.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm (wp_mov op2_imm wp_dp op2_reg)

theorem mask_of : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : word s.mem base SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block [ld .r2 SWAP, .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r2)]) s
      fun t => t.gpr .r5 = mask (decide (sw = 1)) ∧ t.mem = s.mem ∧ Keeps [.r2, .r5] s t := by
  refine load_ok hs (by decide) fun s1 h1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 h2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 h3 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change s2.gpr .r5 - s2.gpr .r2 = _
    rw [h2.gpr, h2.other .r2 (by decide), h1.gpr, hw]
    exact mask_of sw hsw
  · rw [h3.mem, h2.mem, h1.mem]
  · exact rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide))))

theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : word s.mem base SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block lastSwap) s fun t => Keep base s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = opSwap 2 4 (decide (sw = 1)) (opSwap 1 3 (decide (sw = 1)) (E s.mem base)) := by
  rw [lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : Keep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ Outside2.refl _ _ _ _ _ _⟩
  refine WP.mono (swaps_ok (kt.scr hs) (tm ▸ hb) tc) fun u ⟨ku, bu, eu⟩ =>
    ⟨kt.trans ku, bu, by rw [eu, tm]⟩

end VG.Proof.X448.Arm

end

end

/-! ### `X448.Arm.Clamp`, which only this module used -/

section

/-!
# X448 on ARMv7: clamping the scalar bits

Clear bits zero and one, and set bit 447, as RFC 7748 requires.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

def clamp : List Instr :=
  [.mov .r3 (.imm 0), .strb .r3 .r0 BITS, .strb .r3 .r0 (BITS + 1),
    .mov .r3 (.imm 1), .strb .r3 .r0 (BITS + 447)]

def clampMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (off base BITS) (0 : BitVec 8)).writeW (off base (BITS + 1))
    (0 : BitVec 8)).writeW (off base (BITS + 447)) (1 : BitVec 8)

theorem storeByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096) :
    WP isa (.block [.strb .r3 .r0 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) ((s.gpr .r3).setWidth 8) ∧ Keeps [] s t := by
  refine VG.Proof.X25519.Arm.wp_strb hd (hs.ea (by omega_using [hd])) (hs.write (by omega_using [hd]))
    fun t ht => WP.block_nil ⟨ht.mem, rest_keeps (ht.rest _)⟩

theorem putByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096)
    (v : BitVec 32) (hv : encodable v = true) :
    WP isa (.block [.mov .r3 (.imm v), .strb .r3 .r0 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (v.setWidth 8) ∧
      t.gpr .r3 = v ∧ Keeps [.r3] s t := by
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm hv) fun t ht => ?_
  refine WP.mono (storeByte_ok (hs.of_upd ht (by decide) (by decide)) hd) fun u ⟨um, uk⟩ => ?_
  exact ⟨by rw [um, ht.mem, ht.gpr], (uk.1 _ (by decide)).trans ht.gpr,
    (rest_keeps (ht.rest (by decide))).trans (uk.mono (by simp))⟩

theorem clamp_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block clamp) s fun t => t.mem = clampMem s.mem base ∧ Keeps [.r3] s t := by
  change WP isa (.block (([.mov .r3 (.imm 0), .strb .r3 .r0 BITS] : List Instr) ++
    ([.strb .r3 .r0 (BITS + 1)] : List Instr) ++
    [.mov .r3 (.imm 1), .strb .r3 .r0 (BITS + 447)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (putByte_ok hs (by decide : BITS < 4096) 0 (by decide)) fun t ⟨tm, tv, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeByte_ok (hs.of_keeps tk (by decide)) (by decide : BITS + 1 < 4096))
    fun u ⟨um, uk⟩ => ?_
  refine WP.mono (putByte_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (by decide : BITS + 447 < 4096) 1 (by decide)) fun v ⟨vm, _, vk⟩ => ?_
  refine ⟨?_, tk.trans ((uk.mono (by simp)).trans vk)⟩
  rw [vm, um, tv, tm]
  rfl

end VG.Proof.X448.Arm

end

end

/-! ### `X448.Arm.BitBody`, which only this module used -/

section

/-!
# X448 on ARMv7: one scalar byte

The public byte counter selects a scalar byte, expands it, and advances the
loop.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm (wp_dp wp_ldrb wp_cmp op2_reg op2_lsl op2_imm)

def bitHead : List Instr :=
  [.dp .add .r7 .r1 (.reg .r11), .ldrb .r3 .r7 0,
    .dp .add .r7 .r0 (.shifted .r11 .lsl 3)]

def bitTail : List Instr := [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 56)]

def bitRegs : List Reg := [.r3, .r2, .r11, .r7]

theorem bitHead_ok {s : State} {base k : Addr} (_hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32) {i : Nat} (hi : i < 56)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitHead) s fun t =>
      t.gpr .r3 = (s.mem (off k i)).setWidth 32 ∧
      t.gpr .r7 = t.gpr .r0 + BitVec.ofNat 32 (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r7] s t := by
  unfold bitHead
  refine wp_dp (op2_reg _ _) fun t ht => ?_
  have ea : State.addr (t.gpr .r7 + BitVec.ofNat 32 0) = off k i := by
    rw [ht.gpr]; change State.addr (s.gpr .r1 + s.gpr .r11 + BitVec.ofNat 32 0) = _
    rw [BitVec.add_zero, hb, addr_add (by omega_using [hfit, hi]), hk]
  refine wp_ldrb (by decide) ea (by rw [ht.rd, ht.wr]; exact hkr) fun u hu => ?_
  refine wp_dp (op2_lsl (by decide)) fun v hv => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hv.other .r3 (by decide), hu.gpr, ht.mem]
  · rw [hv.gpr, hv.other .r0 (by decide)]
    change u.gpr .r0 + u.gpr .r11 <<< 3 = _
    rw [hu.other .r11 (by decide), ht.other .r11 (by decide), hb]
    apply congrArg (u.gpr .r0 + ·)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using []
  · exact hv.mem.trans (hu.mem.trans ht.mem)
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest (by decide))))

theorem bitTail_ok {s : State} {i : Nat} (hi : i < 56) (hb : s.gpr .r11 = BitVec.ofNat 32 i) :
    WP isa (.block bitTail) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 56) ∧
      t.mem = s.mem ∧ Keeps [.r11] s t := by
  have check : ∀ n < 56,
      ((BitVec.ofNat 32 n + (1 : BitVec 32) - (56 : BitVec 32)) == 0) = decide (n + 1 = 56) :=
    by decide +kernel
  unfold bitTail
  refine wp_dp (op2_imm (by decide)) fun t ht => ?_
  refine wp_cmp (op2_imm (by decide)) fun u hu hz => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hu.gpr, ht.gpr]; change s.gpr .r11 + BitVec.ofNat 32 1 = _
    rw [hb, ← BitVec.ofNat_add]
  · rw [hz, ht.gpr]; change ((s.gpr .r11 + 1 - 56) == 0) = _
    rw [hb]; exact check i hi
  · exact hu.mem.trans ht.mem
  · exact rest_keeps ((ht.rest (by decide)).trans (hu.rest _))

theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32) {i : Nat} (hi : i < 56)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitsBody) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 56) ∧ Keeps bitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (bitHead ++ (List.range 8).flatMap bitJ ++ bitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (bitHead_ok hs hk hfit hi hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (byteBits_ok (hs.of_keeps tk (by decide)) hi tp ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .r11 = BitVec.ofNat 32 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (bitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

end VG.Proof.X448.Arm

end

end

/-!
# X448 on ARMv7: the scalar's decoded bits

The loop expands all 56 bytes before applying the RFC 7748 scalar clamp.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  r1 : State.addr (s.gpr .r1) = k
  fit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  gpr : ∀ r, r ∉ bitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 448 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 56, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 56 → BInv base k s₀ s i →
      WP isa (.loop (.block bitsBody) .ne) s fun s' => BInv base k s₀ s' 56 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .ne)
    (Q := fun s' => BInv base k s₀ s' 56)
    (fun m (s : State) => ∃ i, m = 56 - i ∧ i < 56 ∧ BInv base k s₀ s i) ?_ (56 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (bitsBody_ok hb.scr hb.r1 hb.fit hi hb.r11 (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega_using [this])
  have inv : BInv base k s₀ s' (i + 1) := by
    refine ⟨hb.scr.of_keeps ⟨g', rd', wr'⟩ (by decide),
      (by rw [g' _ (by decide)]; exact hb.r1),
      (by rw [g' _ (by decide)]; exact hb.fit), b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega_using []) (by omega_using [hi])),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [BITS]; omega_using [hi, ht])]; omega_using [h]), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega_using [ht])
      rw [show 8 * i + (t - 8 * i) = t by omega_using [h], hbyte] at e
      rw [e, show t / 8 = i by omega_using [ht, h], show t % 8 = t - 8 * i by omega_using [ht, h]]
  simp only [eval, z']
  rcases Nat.lt_or_ge (i + 1) 56 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega_using [h] : ¬i + 1 = 56), Bool.not_false],
      56 - (i + 1), by omega_using [hi], i + 1, rfl, h, inv⟩
  · obtain rfl : i = 55 := by omega_using [hi, h]
    exact .inl ⟨rfl, inv⟩

theorem getD_bytesAt (m : Mem) (k : Addr) {q : Nat} (hq : q < 56) :
    (Spec.X448.bytesAt m k 56).getD q 0 = m (k + BitVec.ofNat 64 q) := by
  simp only [Spec.X448.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some]

/-- `bits`: byte `t` of `BITS` is bit `t` of the decoded scalar, for `t < 448`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      (∀ r, r ∉ bitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base BITS 448 s.mem s'.mem ∧
      ∀ t < 448, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 (bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) t) := by
  rw [bits]
  refine WP.seq (WP.mono (show WP isa (.block [.mov .r11 (.imm 0)]) s
      (fun s' => BInv base k s s' 0) by
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide))
      fun t ht => WP.block_nil ?_
    have keep : Keeps bitRegs s t := rest_keeps (ht.rest (by decide))
    exact ⟨hs.of_keeps keep (by decide), by rw [ht.other .r1 (by decide)]; exact hk,
      by rw [ht.other .r1 (by decide)]; exact hfit, ht.gpr, keep.1, keep.2.1, keep.2.2,
      ht.mem ▸ Outside.refl _ _ _ _, fun _ hi => by omega⟩) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (bitsLoop_ok hkr hkd 0 s₁ (by omega_using []) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (clamp_ok h₂.scr) fun s₃ ⟨m₃, k₃⟩ => ?_
  refine ⟨fun r hr => ?_, k₃.2.1.trans h₂.rd, k₃.2.2.trans h₂.wr, fun x hx => ?_, fun t ht => ?_⟩
  · rw [k₃.1 r (by intro he; simp only [List.mem_singleton] at he; subst r; exact hr (by decide))]
    exact h₂.gpr r hr
  · rw [m₃, clampMem]
    have o : ∀ d, BITS ≤ d → d < BITS + 448 → ofs base x ≠ d := fun d h₁ h₂ h => by omega_using [hx, h₁, h₂, h]
    rw [writeW8_outside _ _ _ (by simp only [BITS]; omega_using []) (o (BITS + 447) (by omega_using []) (by omega_using [])),
      writeW8_outside _ _ _ (by simp only [BITS]; omega_using []) (o (BITS + 1) (by omega_using []) (by omega_using [])),
      writeW8_outside _ _ _ (by simp only [BITS]; omega_using []) (o BITS (by omega_using []) (by omega_using []))]
    exact h₂.mem x hx
  · rw [m₃, clampMem, scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega_arith) only [writeW8_apply, off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega_using [ht] : t = 0 ∨ t = 1 ∨ t = 447 ∨ (2 ≤ t ∧ t < 447)) with
      rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 447 by omega_using [h₄], show t ≠ 1 by omega_using [h₃], show t ≠ 0 by omega_using [h₃],
        show ¬t < 2 by omega_using [h₃], ite_false]
      rw [h₂.bits t (by omega_using [ht]), getD_bytesAt _ _ (by omega_using [ht])]

end VG.Proof.X448.Arm
