module

public import VerifiedGarbage.Proof.X448.AArch64.BitBody
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.X448.Ladder
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.AArch64.Iter

/-! ### `X448.AArch64.Clamp`, which only this module used -/

section

/-!
# X448 on AArch64: clamping the scalar bits

Clear bits zero and one, and set bit 447, as RFC 7748 requires.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def clamp : List Instr :=
  [.movz .x .x4 0 0, .strb .x4 .x3 BITS, .strb .x4 .x3 (BITS + 1),
    .movz .x .x4 1 0, .strb .x4 .x3 (BITS + 447)]

def clampMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (off base BITS) (0 : BitVec 8)).writeW (off base (BITS + 1))
    (0 : BitVec 8)).writeW (off base (BITS + 447)) (1 : BitVec 8)

theorem storeByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096) :
    WP isa (.block [.strb .x4 .x3 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) ((s.gpr .x4).setWidth 8) ∧ Keeps [] s t := by
  have w := hs.write (d := d) (n := 1) (by omega_using [hd])
  have enc : d % 1 = 0 ∧ d < 4096 := ⟨by omega_using [], hd⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, enc, and_self,
    hs.x3, State.store, w, State.read, ite_true, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun _ _ => rfl, rfl, rfl⟩
  rw [write1_eq]
  apply congrArg (s.mem.writeW (off base d))
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Size.bits]
  omega_using []

theorem putByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096)
    (v : BitVec 16) :
    WP isa (.block [.movz .x .x4 v 0, .strb .x4 .x3 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (v.setWidth 8) ∧
      t.gpr .x4 = v.setWidth 64 ∧ Keeps [.x4] s t := by
  change WP isa (.block (([.movz .x .x4 v 0] : List Instr) ++ [.strb .x4 .x3 d])) s _
  rw [WP.block_append_iff]
  have set : WP isa (.block [.movz .x .x4 v 0]) s fun t =>
      t.gpr .x4 = v.setWidth 64 ∧ t.mem = s.mem ∧ Keeps [.x4] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, rfl, fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr
  refine WP.mono set fun t ⟨tv, tm, tk⟩ => ?_
  refine WP.mono (storeByte_ok (hs.of_keeps tk (by decide)) hd) fun u ⟨um, uk⟩ => ?_
  refine ⟨?_, (uk.1 _ (by decide)).trans tv, tk.trans (uk.mono (by simp))⟩
  rw [um, tm, tv]
  apply congrArg (s.mem.writeW (off base d))
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt
  omega_using []

theorem clamp_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block clamp) s fun t => t.mem = clampMem s.mem base ∧ Keeps [.x4] s t := by
  change WP isa (.block (([.movz .x .x4 0 0, .strb .x4 .x3 BITS] : List Instr) ++
    ([.strb .x4 .x3 (BITS + 1)] : List Instr) ++
    [.movz .x .x4 1 0, .strb .x4 .x3 (BITS + 447)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (putByte_ok hs (by decide : BITS < 4096) 0) fun t ⟨tm, tv, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeByte_ok (hs.of_keeps tk (by decide)) (by decide : BITS + 1 < 4096))
    fun u ⟨um, uk⟩ => ?_
  refine WP.mono (putByte_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (by decide : BITS + 447 < 4096) 1) fun v ⟨vm, _, vk⟩ => ?_
  refine ⟨?_, tk.trans ((uk.mono (by simp)).trans vk)⟩
  rw [vm, um, tv, tm]
  rfl

end VG.Proof.X448.AArch64

end

end


/-!
# X448 on AArch64: the scalar's decoded bits

The loop expands all 56 bytes before applying the RFC 7748 scalar clamp.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Proof.X448

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  x1 : s.gpr .x1 = k
  x19 : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x8 = 1
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
      WP isa (.loop (.block bitsBody) (.nonzero .x .x11)) s fun s' => BInv base k s₀ s' 56 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .nonzero .x .x11)
    (Q := fun s' => BInv base k s₀ s' 56)
    (fun m (s : State) => ∃ i, m = 56 - i ∧ i < 56 ∧ BInv base k s₀ s i) ?_ (56 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (bitsBody_ok hb.scr hb.x1 hi hb.x19 hb.one (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', one', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega_using [this])
  have inv : BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.x3, (g' _ (by decide)).trans hb.scr.mask, wr' ▸ hb.scr.wr, hb.scr.nowrap⟩,
      (g' _ (by decide)).trans hb.x1, b', one', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega_using []) (by omega_using [hi])),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [BITS]; omega_using [hi, ht])]; omega_using [h]), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega_using [ht])
      rw [show 8 * i + (t - 8 * i) = t by omega_using [h], hbyte] at e
      rw [e, show t / 8 = i by omega_using [ht, h], show t % 8 = t - 8 * i by omega_using [ht, h]]
  simp only [eval, State.read, BitVec.setWidth_eq, bne, z']
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
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      (∀ r, r ∉ bitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base BITS 448 s.mem s'.mem ∧
      ∀ t < 448, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 (bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) t) := by
  rw [bits]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) s
      (fun s' => BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, ?_, hs.wr, hs.nowrap⟩, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
      Outside.refl _ _ _ _, fun t ht => absurd ht (by omega_using [])⟩
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.x3
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.mask
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hk
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]; rfl
    · rw [RegUpd.gpr_write_self]; rfl
    · have h19 : r ≠ .x19 := fun h => hr (by subst r; decide)
      have h8 : r ≠ .x8 := fun h => hr (by subst r; decide)
      simp only [RegUpd.gpr_write, h19, h8, ite_false]) fun s₁ h₁ => ?_)
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

end VG.Proof.X448.AArch64
