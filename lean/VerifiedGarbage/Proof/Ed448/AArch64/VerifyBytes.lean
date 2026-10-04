import VerifiedGarbage.Proof.Ed448.AArch64.VerifyChecks
import VerifiedGarbage.Proof.Ed448.Scalar

/-!
# Ed448 verification's equation on AArch64: checks of the encodings' bytes

`sCheck`: `S < L` for the 57 bytes at `x1 + 57` (`carryK` of `2^448 - L`, and
byte 56). `decodeY`: the 56 bytes of `y` as eight seven-byte chunks in a
slot, `y < p` (`carryK` of `2^224 + 1`), bits 448–454 zero, and the sign bit
in `x17`.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs workRegs)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Proof.X25519 (leNum)
open VG.Impl.X448.AArch64 (ld st slot)

theorem ldrb5_ok (s : State) {rp : Reg} {p : Addr} (hp : s.gpr rp = p) {o : Nat} (ho : o < 4096)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 o) 1) :
    WP isa (.block [.ldrb .x5 rp o]) s fun t =>
      t.gpr .x5 = (s.mem (p + BitVec.ofNat 64 o)).setWidth 64 ∧ t.mem = s.mem ∧ Keeps [.x5] s t := by
  have enc : o % 1 = 0 ∧ o < 4096 := ⟨Nat.mod_one _, ho⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, enc, and_self, hp, State.load, hr,
    VG.Proof.X448.AArch64.read1_eq, RegUpd.gpr_write, RegUpd.mem_write,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, Size.bits]
    have := (s.mem (p + BitVec.ofNat 64 o)).isLt
    omega
  · simp only [List.mem_singleton] at hr
    simp only [State.write, hr, ite_false]

theorem setWidth8_eq_zero (b : Byte) : b.setWidth 64 = 0 ↔ b.toNat = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at this
  · intro h; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide)), h]; rfl

theorem bytesAt_succ57 (m : Mem) (q : Addr) :
    Spec.Ed448.bytesAt m q 57 = Spec.X448.bytesAt m q 56 ++ [m (q + BitVec.ofNat 64 56)] := by
  simp only [Spec.Ed448.bytesAt, Spec.X448.bytesAt, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

/-- `sCheck`: `x20 |= c`, with `c = 0` exactly when the 57 bytes at `x1 + 57` are below `L`. -/
theorem sCheck_ok {s : State} {p : Addr} (hp : s.gpr .x1 = p)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (57 + j)) 1) :
    WP isa (.block sCheck) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (p + BitVec.ofNat 64 57) 57) <
        Spec.Ed448.L) ∧ t.gpr .x20 = s.gpr .x20 ||| c) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6, .x7, .x20] s t := by
  rw [sCheck]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (carryK_ok (rp := .x1) (o := 57) hp (by decide) (by decide)
    (fun j hj => hr j (by omega))) fun u ⟨u5, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (orBad_ok u) fun v ⟨v20, vm, vk⟩ => ?_
  rw [WP.block_append_iff]
  have pv : v.gpr .x1 = p := by rw [vk.1 _ (by decide), uk.1 _ (by decide)]; exact hp
  refine WP.mono (ldrb5_ok v pv (o := 113) (by decide) (by
    rw [vk.2.1, vk.2.2, uk.2.1, uk.2.2]; exact hr 56 (by decide))) fun w ⟨w5, wm, wk⟩ => ?_
  refine WP.mono (orBad_ok w) fun t ⟨t20, tm, tk⟩ => ?_
  generalize hy : leNum (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 57) 56) = y at u5
  have hyl : y < 2 ^ 448 := by
    rw [← hy]
    have := VG.Proof.X25519.leNum_lt (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 57) 56)
    rw [VG.Proof.X448.length_bytesAt] at this
    exact Nat.lt_of_lt_of_le this (Nat.le_of_eq (by decide +kernel))
  have hK : (2 ^ 448 - Spec.Ed448.L) % 2 ^ 448 = 2 ^ 448 - Spec.Ed448.L := by decide +kernel
  rw [hK] at u5
  have hb : v.mem (p + BitVec.ofNat 64 113) = s.mem (p + BitVec.ofNat 64 113) := by rw [vm, um]
  refine ⟨⟨u.gpr .x5 ||| w.gpr .x5, ?_, ?_⟩, ?_, ?_⟩
  · rw [VG.Proof.Ed448.AArch64.or_eq_zero64, w5, hb, setWidth8_eq_zero, bytesAt_succ57, decodeLE_append,
      Offset.add_add, VG.Proof.X448.length_bytesAt]
    rw [show Spec.Ed448.decodeLE [s.mem (p + BitVec.ofNat 64 (57 + 56))] = (s.mem (p + BitVec.ofNat 64 113)).toNat by
      simp [Spec.Ed448.decodeLE]]
    rw [show Spec.Ed448.decodeLE (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 57) 56) = y by
      rw [← hy, decodeLE_eq]]
    have h1 := Nat.mod_add_div (y + (2 ^ 448 - Spec.Ed448.L)) (2 ^ 448)
    have h2 := Nat.mod_lt (y + (2 ^ 448 - Spec.Ed448.L)) (Nat.two_pow_pos 448)
    have h3 : (y + (2 ^ 448 - Spec.Ed448.L)) / 2 ^ 448 ≤ 1 := by
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 448)]
      have := Nat.sub_le (2 ^ 448) Spec.Ed448.L
      omega
    have key := sCheck_nat (b := (s.mem (p + BitVec.ofNat 64 113)).toNat) hyl h2 h3 h1
    rw [← key]
    have hu : u.gpr .x5 = 0 ↔ (y + (2 ^ 448 - Spec.Ed448.L)) / 2 ^ 448 = 0 := by
      rw [← u5]
      exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hu]
  · rw [t20, wk.1 _ (by decide), v20, uk.1 _ (by decide), BitVec.or_assoc]
  · rw [tm, wm, vm, um]
  · exact (((uk.mono (by decide)).trans (vk.mono (by decide))).trans (wk.mono (by decide))).trans (tk.mono (by decide))

/-! ## `y` -/

theorem wide_chunks (m : Mem) (q : Addr) :
    ∀ n, VG.Proof.X448.Wide.valN (fun i => chunk7 m (q + BitVec.ofNat 64 (7 * i))) n =
      leNum (Spec.X448.bytesAt m q (7 * n))
  | 0 => rfl
  | n + 1 => by
    rw [VG.Proof.X448.Wide.valN_succ, wide_chunks m q n, leNum_chunks]
    congr 2
    rw [VG.Proof.X448.Wide.radix, ← Nat.pow_mul]

theorem byte56_val (b : Byte) :
    (b.setWidth 64 >>> 7) = BitVec.ofNat 64 (b.toNat / 128) ∧
      (b.setWidth 64 &&& BitVec.setWidth 64 (0x7f : BitVec 16)) = BitVec.ofNat 64 (b.toNat % 128) := by
  have hb := b.isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (BitVec.toNat (127 : BitVec 16)) % 2 ^ 64 = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : b.toNat % 2 ^ 7 < 2 ^ 64)]
    omega

/-- Byte 56: the sign bit into `x17`, and bits 448–454 into `x5`. -/
theorem byte56_ok (s : State) {rp : Reg} {p : Addr} (hp : s.gpr rp = p)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.ldrb .x5 rp 56, .lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0,
        .logic .and .x .x5 .x5 .x6] : List Instr)) s fun t =>
      t.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) ∧
      t.gpr .x5 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) ∧
      t.mem = s.mem ∧ Keeps [.x5, .x6, .x17] s t := by
  rw [show ([.ldrb .x5 rp 56, .lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0, .logic .and .x .x5 .x5 .x6] : List Instr) =
    [.ldrb .x5 rp 56] ++ [.lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0, .logic .and .x .x5 .x5 .x6] from rfl,
    WP.block_append_iff]
  refine WP.mono (ldrb5_ok s hp (o := 56) (by decide) hr) fun u ⟨u5, um, uk⟩ => ?_
  have bv := byte56_val (s.mem (p + BitVec.ofNat 64 56))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, Nat.reduceMul,
    Nat.reduceLT, ite_true, BitVec.shiftLeft_zero, BitVec.setWidth_eq, RegUpd.gpr_write, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left', u5]
  refine ⟨bv.1, bv.2, um, (fun r hr => ?_), uk.2.1, uk.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [State.write, hr.1, hr.2.1, hr.2.2, ite_false]
  exact uk.1 r (by simp only [List.mem_singleton]; exact hr.1)

/-- The chunks of `y` into slot `yo`. -/
theorem yStores_ok {s : State} {base : Addr} (hs : Scr s base) {rp : Reg} {p : Addr} (hp : s.gpr rp = p)
    (h4 : rp ≠ .x4) (h7 : rp ≠ .x7) (yo : Fin 22)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (.block ((List.range 8).flatMap (fun i => bytes7 rp (7 * i) ++ [st .x4 (slot yo.val + 8 * i)]))) s
      fun t => (∀ i < 8, (word t.mem base (slot yo.val + 8 * i)).toNat = chunk7 s.mem (p + BitVec.ofNat 64 (7 * i))) ∧
        Outside base (slot yo.val) 64 s.mem t.mem ∧ Keeps [.x4, .x7] s t := by
  have hy := yo.isLt
  let inv := fun n (t : State) =>
    (∀ i < n, (word t.mem base (slot yo.val + 8 * i)).toNat = chunk7 s.mem (p + BitVec.ofNat 64 (7 * i))) ∧
      Outside base (slot yo.val) 64 s.mem t.mem ∧ Keeps [.x4, .x7] s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (bytes7 rp (7 * n) ++ [st .x4 (slot yo.val + 8 * n)])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    have tp : t.gpr rp = p := by
      rw [tk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h7⟩)]; exact hp
    have hst : Scr t base := hs.of_keeps tk (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (bytes7_ok tp h4 h7 (o := 7 * n) (by omega) (fun j hj => by
      rw [tk.2.1, tk.2.2]; exact hr _ (by omega))) fun u ⟨u4, um, uk⟩ => ?_
    have hsu : Scr u base := hst.of_keeps uk (by decide)
    refine WP.mono (VG.Proof.X448.AArch64.store_ok hsu (d := slot yo.val + 8 * n) (by simp only [slot]; omega)
      (by simp only [slot]; omega) .x4) fun v ⟨vm, vk⟩ => ⟨fun i hi => ?_, ?_, (tk.trans uk).trans (vk.mono (by simp))⟩
    · rw [vm, VG.Proof.X448.AArch64.word_write_aligned _ _ (by simp only [slot]; omega) (by simp only [slot]; omega)
        (by simp only [slot]; omega) (by simp only [slot]; omega)]
      by_cases h : i = n
      · subst h
        rw [ite_eq_left rfl, u4]
        have hc : chunk7 t.mem (p + BitVec.ofNat 64 (7 * i)) = chunk7 s.mem (p + BitVec.ofNat 64 (7 * i)) := by
          apply congrArg leNum
          simp only [Spec.X448.bytesAt]
          refine List.map_congr_left fun j hj => ?_
          have hj := List.mem_range.mp hj
          rw [Offset.add_add]
          exact tm _ (Or.inr (by have := hfar (7 * i + j) (by omega); simp only [slot] at *; omega))
        exact hc
      · rw [ite_eq_right (by omega), um]; exact tv i (by omega)
    · intro x hx
      rw [vm, VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [slot]; omega) x (by omega), um]
      exact tm x hx
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), VG.Proof.X448.AArch64.Outside.refl _ _ _ _,
      VG.Proof.X448.AArch64.Keeps.refl _ _⟩

theorem P_add : Spec.X448.P + (2 ^ 224 + 1) = 2 ^ 448 := by decide +kernel

/-- `decodeY rp yo`: `y` (the first 56 bytes at `rp`) in slot `yo`, the sign bit in `x17`, and
`x20 |= c`, `c = 0` exactly when bits 448–454 are 0 and `y < p`. -/
theorem decodeY_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {rp : Reg}
    {p : Addr} (hp : s.gpr rp = p) (hrp : rp = .x0 ∨ rp = .x1) (yo : Fin 22)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (.block (decodeY rp yo.val)) s fun t =>
      E t.mem base yo = VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ∧
      t.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) ∧
      (∃ c : BitVec 64, (c = 0 ↔ (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
          Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ i : Fin 22, i ≠ yo → E t.mem base i = E s.mem base i) ∧ BoundedEnv t.mem base ∧
      Keeps [.x4, .x5, .x6, .x7, .x17, .x20] s t ∧ Outside base (slot yo.val) 64 s.mem t.mem := by
  have hy := yo.isLt
  have h4 : rp ≠ .x4 := by rcases hrp with rfl | rfl <;> decide
  have h5 : rp ≠ .x5 := by rcases hrp with rfl | rfl <;> decide
  have h6 : rp ≠ .x6 := by rcases hrp with rfl | rfl <;> decide
  have h7 : rp ≠ .x7 := by rcases hrp with rfl | rfl <;> decide
  rw [decodeY]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (yStores_ok hs hp h4 h7 yo (fun j hj => hr j (by omega)) (fun j hj => hfar j (by omega)))
    fun a ⟨av, am, ak⟩ => ?_
  have hin : ∀ j < 57, a.mem (p + BitVec.ofNat 64 j) = s.mem (p + BitVec.ofNat 64 j) := fun j hj =>
    am _ (Or.inr (by have := hfar j hj; simp only [slot] at *; omega))
  have ap : a.gpr rp = p := by
    rw [ak.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h7⟩)]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (carryK_ok (o := 0) ap ⟨h4, h5, h6, h7⟩ (by decide) (fun j hj => by
    rw [ak.2.1, ak.2.2, Nat.zero_add]; exact hr j (by omega))) fun u ⟨u5, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (orBad_ok u) fun v ⟨v20, vm, vk⟩ => ?_
  have vp : v.gpr rp = p := by
    rw [vk.1 _ (by simp only [List.mem_singleton]; rcases hrp with rfl | rfl <;> decide),
      uk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h5, h6, h7⟩)]
    exact ap
  rw [WP.block_append_iff]
  refine WP.mono (byte56_ok v vp (by
    rw [vk.2.1, vk.2.2, uk.2.1, uk.2.2, ak.2.1, ak.2.2]; exact hr 56 (by decide))) fun w ⟨w17, w5, wm, wk⟩ => ?_
  refine WP.mono (orBad_ok w) fun t ⟨t20, tm, tk⟩ => ?_
  have hb56 : v.mem (p + BitVec.ofNat 64 56) = s.mem (p + BitVec.ofNat 64 56) := by
    rw [vm, um]; exact hin 56 (by decide)
  have hy56 : leNum (Spec.X448.bytesAt a.mem (p + BitVec.ofNat 64 0) 56) =
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) := by
    rw [BitVec.add_zero, decodeLE_eq]
    apply congrArg leNum
    simp only [Spec.X448.bytesAt, Spec.Ed448.bytesAt]
    exact List.map_congr_left fun j hj => hin j (by have := List.mem_range.mp hj; omega)
  have tmem : t.mem = a.mem := by rw [tm, wm, vm, um]
  -- The value of slot `yo`.
  have ey : E t.mem base yo = VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) := by
    have w8 := wide_chunks s.mem p 8
    rw [show 7 * 8 = 56 from rfl] at w8
    rw [decodeLE_eq, show Spec.Ed448.bytesAt s.mem p 56 = Spec.X448.bytesAt s.mem p 56 from rfl, ← w8, tmem]
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr fun i hi => av i hi)
  refine ⟨ey, ?_, ⟨u.gpr .x5 ||| w.gpr .x5, ?_, ?_⟩, fun i hi => ?_, fun i j hj => ?_, ?_, ?_⟩
  · rw [tk.1 _ (by decide), w17, hb56]
  · rw [or_eq_zero64, w5, hb56]
    have hc : (u.gpr .x5).toNat = (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) + (2 ^ 224 + 1)) / 2 ^ 448 := by
      rw [u5, hy56, show ((2 : Nat) ^ 224 + 1) % 2 ^ 448 = 2 ^ 224 + 1 by decide +kernel]
    have hylt : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < 2 ^ 448 := by
      have := decodeLE_lt' (Spec.Ed448.bytesAt s.mem p 56)
      rw [show (Spec.Ed448.bytesAt s.mem p 56).length = 56 by simp [Spec.Ed448.bytesAt]] at this
      exact Nat.lt_of_lt_of_le this (Nat.le_of_eq (by decide +kernel))
    have hP := P_add
    generalize Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) = y at hc hylt ⊢
    generalize (2 : Nat) ^ 448 = M at hc hylt hP
    have e1 : u.gpr .x5 = 0 ↔ y < Spec.X448.P := by
      constructor
      · intro h
        rw [h] at hc
        have : (y + (2 ^ 224 + 1)) / M = 0 := hc.symm
        rw [Nat.div_eq_zero_iff_lt (by omega)] at this
        omega
      · intro h
        apply BitVec.eq_of_toNat_eq
        rw [hc, Nat.div_eq_of_lt (by omega)]; rfl
    have e2 : BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) = 0 ↔
        (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      · intro h; rw [h]; rfl
    rw [e1, e2, and_comm]
  · rw [t20, wk.1 _ (by decide), v20, uk.1 _ (by decide), ak.1 _ (by decide), BitVec.or_assoc]
  · rw [tmem]
    exact VG.Proof.X448.AArch64.Weak.E_outside am i
      (by have := VG.Proof.X448.AArch64.Weak.slot_sep hi; omega)
  · rw [tmem]
    by_cases h : i = yo
    · subst h
      change (word a.mem base (slot i.val + 8 * j)).toNat < _
      rw [av j hj]
      exact Nat.lt_of_lt_of_le (chunk7_lt _ _) (by decide)
    · have := VG.Proof.X448.AArch64.Weak.slot_sep h
      have hil := i.isLt
      change (word a.mem base (slot i.val + 8 * j)).toNat < _
      rw [am.word (by omega) (by simp only [slot]; omega)]
      exact hb i j hj
  · exact ((((ak.mono (by decide)).trans (uk.mono (by decide))).trans (vk.mono (by decide))).trans
      (wk.mono (by decide))).trans (tk.mono (by decide))
  · rw [tmem]; exact am

end VG.Proof.Ed448.AArch64
