import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
import VerifiedGarbage.Proof.Ed25519.Recode
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# The recoding's step on x86-64

`recodeStep` runs `Recode.step` on the scalar copied into the scratch (`Copied`): `recodeBits`
reads the bits from `rsi` (the bit) with a word load at its byte and conditional moves for the
shift within the byte, the carry is `r8`, and the digit's byte goes to the array `dst` (`dig`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519.Recode
open VG.Proof.X25519.X86_64 (off ofs Keeps)

/-- Byte `j` of the digits' array `dst` (0 for `k`, 1 for `S`). -/
abbrev dig (m : Mem) (base : Addr) (dst j : Nat) : Nat := (m (off base (2048 + 2 * j + dst))).toNat

/-- The scalar `X` copied at byte `src` of the scratch: the word at its byte `b < nb` holds
`X`'s bits from `8b`. -/
def Copied (m : Mem) (base : Addr) (src nb X : Nat) : Prop :=
  ∀ b < nb, (m.readW (off base (src + b)) 64).toNat = X / 2 ^ (8 * b) % 2 ^ 64

/-- The registers the recoding computes with. -/
def recRegs : List Reg := [.rax, .rbx, .rcx, .rdx, .rsi, .r8]

/-- What the recoding into the array `dst` may change: its registers, and the array's bytes. -/
structure RecKeep (base : Addr) (dst : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ recRegs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : ∀ x, (ofs base x < 2048 ∨ 3104 ≤ ofs base x ∨ ofs base x % 2 ≠ dst) → t.mem x = s.mem x

theorem RecKeep.refl (base : Addr) (dst : Nat) (s : State) : RecKeep base dst s s :=
  ⟨fun _ _ => rfl, rfl, rfl, fun _ _ => rfl⟩

theorem RecKeep.trans {base : Addr} {dst : Nat} {s t u : State} (h : RecKeep base dst s t)
    (k : RecKeep base dst t u) : RecKeep base dst s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    fun x hx => (k.mem x hx).trans (h.mem x hx)⟩

theorem RecKeep.of_keeps {base : Addr} {dst : Nat} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r ∈ recRegs) : RecKeep base dst s t :=
  ⟨fun r hr => h.1 r fun hm => hr (hrs r hm), h.2.2.1, h.2.2.2, fun x _ => by rw [h.2.1]⟩

theorem RecKeep.scratch {base : Addr} {dst : Nat} {s t : State} (h : RecKeep base dst s t)
    (hs : Scratch s base) : Scratch t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-! ## Reading the bits -/

/-- `rax` = the bit's byte, `rbx` = the word there, `rcx` = the bit within the byte. -/
theorem recodeLoad_ok {s : State} {base : Addr} (hs : Scratch s base) {src i : Nat}
    (hsrc : src + i / 8 + 8 ≤ 8192) (hr : s.gpr .rsi = BitVec.ofNat 64 i) (hi : i < 2 ^ 32) :
    WP isa (.block [.mov .rax (.reg .rsi), .shift .shr .rax 3,
      .mov .rbx (.mem { base := .rdi, index := some .rax, disp := (src : Int) }),
      .mov .rcx (.reg .rsi), .alu .and .rcx (.imm 7)]) s fun t =>
      t.gpr .rbx = s.mem.readW (off base (src + i / 8)) 64 ∧ t.gpr .rcx = BitVec.ofNat 64 (i % 8) ∧
      Keeps [.rax, .rbx, .rcx] s t := by
  have hshr : BitVec.ofNat 64 i >>> 3 = BitVec.ofNat 64 (i / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hea : base + BitVec.ofNat 64 (i / 8) * BitVec.ofNat 64 1 + BitVec.ofInt 64 (src : Int) =
      off base (src + i / 8) := by
    rw [BitVec.ofInt_natCast, BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]
  have hrg : InRegions (s.rd ++ s.wr) (off base (src + i / 8)) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hsrc (by omega)⟩
  have hand : BitVec.ofNat 64 i &&& (7 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (i % 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (7 : BitVec 32).signExtend 64 = BitVec.ofNat 64 7 from rfl,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 7 < 2 ^ 64 by decide),
      show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift, execAlu, State.load64,
    State.ea, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.mem_setReg,
    RegUpd.mem_setFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.wr_setReg, RegUpd.wr_setFlags,
    hr, hs.rdi, hshr, hea, hrg, hand, show 1 ≤ 3 ∧ 3 ≤ 63 by decide, and_self, reduceCtorEq,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A conditional shift: `rbx` shifted right by `k` if `rcx` has bit `k` set. -/
theorem condShift_ok (s : State) (k : Nat) (hk : 1 ≤ k ∧ k ≤ 63) :
    WP isa (.block [.mov .rdx (.reg .rbx), .shift .shr .rdx k,
      .alu .test .rcx (.imm (BitVec.ofNat 32 k)), .cmov .ne .rbx (.reg .rdx)]) s fun t =>
      t.gpr .rbx = (if (s.gpr .rcx &&& (BitVec.ofNat 32 k).signExtend 64 == 0) = true then s.gpr .rbx
        else s.gpr .rbx >>> k) ∧ t.gpr .rcx = s.gpr .rcx ∧ Keeps [.rbx, .rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift, execAlu, execCmov,
    eval, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    hk, and_self, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  cases hb : (s.gpr .rcx &&& (BitVec.ofNat 32 k).signExtend 64 == 0)
  · simp only [Bool.not_false, ite_true, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
      RegUpd.gpr_arithFlags, reduceCtorEq, ite_false, Bool.false_eq_true]
    refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, RegUpd.gpr_setReg,
      RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, reduceCtorEq]
    refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.2, ite_false]

/-- The three conditional shifts shift by the bit within the byte. -/
theorem condShifts (x : BitVec 64) {b : Nat} (hb : b < 8) :
    (let c (k : Nat) (y : BitVec 64) :=
      if (BitVec.ofNat 64 b &&& (BitVec.ofNat 32 k).signExtend 64 == 0) = true then y else y >>> k
     c 1 (c 2 (c 4 x))).toNat = x.toNat / 2 ^ b := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
    b = 5 ∨ b = 6 ∨ b = 7 := by omega
  all_goals
    simp only [BitVec.reduceSignExtend, BitVec.reduceAnd, BitVec.reduceBEq, ↓reduceIte, Bool.false_eq_true,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, Nat.pow_zero, Nat.div_one]
    try rfl

/-- The bits from `i`, as `recodeBits` reads them, modulo `2 ^ w`. -/
theorem bits_mod (X i w : Nat) (hw : w ≤ 56) :
    X / 2 ^ (8 * (i / 8)) % 2 ^ 64 / 2 ^ (i % 8) % 2 ^ w = X / 2 ^ i % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < w
  · simp only [hj, decide_true, Bool.true_and, show j + i % 8 < 64 by omega]
    congr 1
    omega
  · simp only [hj, decide_false, Bool.false_and]

theorem recodeBits_ok {s : State} {base : Addr} (hs : Scratch s base) {src nb X i : Nat}
    (hsrc : src + nb + 8 ≤ 8192) (hX : Copied s.mem base src nb X) (hi : i < 8 * nb)
    (hr : s.gpr .rsi = BitVec.ofNat 64 i) (hi32 : i < 2 ^ 32) :
    WP isa (.block (recodeBits src)) s fun t =>
      (t.gpr .rbx).toNat = X / 2 ^ (8 * (i / 8)) % 2 ^ 64 / 2 ^ (i % 8) ∧
      Keeps [.rax, .rbx, .rcx, .rdx] s t := by
  rw [show recodeBits src = [.mov .rax (.reg .rsi), .shift .shr .rax 3,
      .mov .rbx (.mem { base := .rdi, index := some .rax, disp := (src : Int) }),
      .mov .rcx (.reg .rsi), .alu .and .rcx (.imm 7)] ++
    ([.mov .rdx (.reg .rbx), .shift .shr .rdx 4, .alu .test .rcx (.imm (BitVec.ofNat 32 4)),
      .cmov .ne .rbx (.reg .rdx)] ++
    ([.mov .rdx (.reg .rbx), .shift .shr .rdx 2, .alu .test .rcx (.imm (BitVec.ofNat 32 2)),
      .cmov .ne .rbx (.reg .rdx)] ++
    [.mov .rdx (.reg .rbx), .shift .shr .rdx 1, .alu .test .rcx (.imm (BitVec.ofNat 32 1)),
      .cmov .ne .rbx (.reg .rdx)])) from rfl, WP.block_append_iff]
  refine WP.mono (recodeLoad_ok hs (by omega) hr hi32) fun a ⟨ab, ac, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (condShift_ok a 4 (by decide)) fun b ⟨bb, bc, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (condShift_ok b 2 (by decide)) fun c ⟨cb, cc, kc⟩ => ?_
  refine WP.mono (condShift_ok c 1 (by decide)) fun t ⟨tb, _, kt⟩ => ?_
  refine ⟨?_, (((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans
    (kt.mono (by decide))⟩
  rw [tb, cb, cc, bb, bc, ab, ac]
  rw [condShifts _ (Nat.mod_lt i (by decide)), hX (i / 8) (by omega)]

/-- ZF set if the bit `b` (bit 0 of `rbx`) equals the carry `c`. -/
theorem recodeTest_ok (s : State) {b c : Nat} (hb : (s.gpr .rbx).toNat % 2 = b) (hc1 : c ≤ 1)
    (hc : s.gpr .r8 = BitVec.ofNat 64 c) :
    WP isa (.block recodeTest) s fun t => t.zf = some (decide (b = c)) ∧ Keeps [.rax] s t := by
  have hb1 : b < 2 := by omega
  have hand : s.gpr .rbx &&& (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 b := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (by omega), show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact hb
  have hz : (BitVec.ofNat 64 b - BitVec.ofNat 64 c == 0) = decide (b = c) := by
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    all_goals obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
    all_goals decide
  rw [recodeTest]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, hand, hc, hz, reduceCtorEq,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem sext_small {n : Nat} (hn : n < 2 ^ 31) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]; omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem zext_small {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `rbx` = the window `W'` (the `w` bits) plus the carry `c`, CF set if that is below
`2 ^ (w - 1)`. -/
theorem recodeW_ok (s : State) {w W c : Nat} (hw : 1 ≤ w ∧ w ≤ 8)
    (hb : (s.gpr .rbx).toNat % 2 ^ w = W) (hc1 : c ≤ 1) (hc : s.gpr .r8 = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .and .rbx (.imm (BitVec.ofNat 32 (2 ^ w - 1))), .alu .add .rbx (.reg .r8),
      .alu .cmp .rbx (.imm (BitVec.ofNat 32 (2 ^ (w - 1))))]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (W + c) ∧ t.cf = some (decide (W + c < 2 ^ (w - 1))) ∧
        Keeps [.rbx] s t := by
  have h8 : 2 ^ w ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hw.2
  have h8' : 2 ^ (w - 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
  have hW : W < 2 ^ w := hb ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  have hand : s.gpr .rbx &&& (BitVec.ofNat 32 (2 ^ w - 1)).signExtend 64 = BitVec.ofNat 64 W := by
    apply BitVec.eq_of_toNat_eq
    rw [sext_small (by omega), BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 ^ w - 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega),
      Nat.and_two_pow_sub_one_eq_mod, hb]
  have hadd : BitVec.ofNat 64 W + BitVec.ofNat 64 c = BitVec.ofNat 64 (W + c) := by
    rw [BitVec.ofNat_add]
  have hcf : (BitVec.ofNat 64 (W + c)).toNat < ((BitVec.ofNat 32 (2 ^ (w - 1))).signExtend 64).toNat ↔
      W + c < 2 ^ (w - 1) := by
    rw [sext_small (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, hand, hc, hadd, hcf, reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- A negative digit's byte, `2 ^ w + 1 - W`, and the carry. -/
theorem recodeNeg_ok (s : State) {w W : Nat} (hw : w ≤ 8) (hW : W ≤ 2 ^ w + 1)
    (hb : s.gpr .rbx = BitVec.ofNat 64 W) :
    WP isa (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (2 ^ w + 1))), .alu .sub .rax (.reg .rbx),
      .mov .rbx (.reg .rax), .mov32 .r8 (.imm 1)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (2 ^ w + 1 - W) ∧ t.gpr .r8 = BitVec.ofNat 64 1 ∧
        Keeps [.rax, .rbx, .r8] s t := by
  have h8 : 2 ^ w ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hw
  have hsub : BitVec.ofNat 64 (2 ^ w + 1) - BitVec.ofNat 64 W = BitVec.ofNat 64 (2 ^ w + 1 - W) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 ^ w + 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 2 ^ w + 1 - W < 2 ^ 64 by omega)]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb, zext_small (show 2 ^ w + 1 < 2 ^ 32 by omega),
    hsub, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A positive digit: the carry cleared. -/
theorem recodePos_ok (s : State) :
    WP isa (.block [.mov32 .r8 (.imm 0)]) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 0 ∧ t.gpr .rbx = s.gpr .rbx ∧ Keeps [.r8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-! ## The digit's byte -/

/-- The digit's byte `u` to the array `dst` at the bit `i`, and the bit moved `w` on. -/
theorem recodeStore_ok {s : State} {base : Addr} (hs : Scratch s base) {i w dst u : Nat}
    (hi : i < 528) (hdst : dst < 2) (hw : w ≤ 8)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 i) (hb : s.gpr .rbx = BitVec.ofNat 64 u) :
    WP isa (.block [.mov .rax (.reg .rsi), .alu .add .rax (.reg .rax),
      .store8 { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) } .rbx,
      .alu .add .rsi (.imm (BitVec.ofNat 32 w))]) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (i + w) ∧
      t.mem = s.mem.writeW (off base (2048 + 2 * i + dst)) (BitVec.ofNat 8 u) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hea : base + (BitVec.ofNat 64 i + BitVec.ofNat 64 i) * BitVec.ofNat 64 1 +
      BitVec.ofInt 64 ((2048 + dst : Nat) : Int) = off base (2048 + 2 * i + dst) := by
    rw [BitVec.ofInt_natCast, BitVec.mul_one, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun n => off base n) (by omega)
  have hrg : InRegions s.wr (off base (2048 + 2 * i + dst)) 1 :=
    ⟨_, hs.wr, Offset.contains_base _ (show 2048 + 2 * i + dst + 1 ≤ 8192 by omega) (by omega)⟩
  have hw8 : (BitVec.ofNat 64 u).setWidth 8 = BitVec.ofNat 8 u := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.store8, State.ea,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, hrsi, hs.rdi, hb, hea, hrg, hw8, sext_small (show w < 2 ^ 31 by omega), reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.ofNat_add], trivial, fun r ha hs' => ?_, trivial, trivial⟩
  simp only [ha, hs', ite_false]

theorem dig_write {m : Mem} {base : Addr} {i dst u : Nat}
    (hi : i < 528) (hdst : dst < 2) (hu : u < 256) {j : Nat} (hj : j < 528) :
    dig (m.writeW (off base (2048 + 2 * i + dst)) (BitVec.ofNat 8 u)) base dst j =
      if j = i then u else dig m base dst j := by
  simp only [dig, VG.WriteBytes.writeW8_apply]
  by_cases h : j = i
  · subst h; simp only [ite_true, BitVec.toNat_ofNat]; omega
  · rw [ite_eq_right (Offset.add_ofNat_ne base (by omega) (by omega) (by omega)), ite_eq_right h]

theorem keep_write {m : Mem} {base : Addr} {i dst : Nat}
    (hi : i < 528) (hdst : dst < 2) (v : Byte) (x : Addr)
    (hx : ofs base x < 2048 ∨ 3104 ≤ ofs base x ∨ ofs base x % 2 ≠ dst) :
    m.writeW (off base (2048 + 2 * i + dst)) v x = m x := by
  rw [VG.WriteBytes.writeW8_apply, ite_eq_right]
  rintro rfl
  rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega)] at hx
  omega

theorem rsiInc_ok (s : State) {i : Nat} (hi : s.gpr .rsi = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .add .rsi (.imm 1)]) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (i + 1) ∧ Keeps [.rsi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, hi, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add],
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- One step of the recoding, from bit `i < 8 nb`: `Recode.step`. -/
theorem recodeStep_ok {s : State} {base : Addr} (hs : Scratch s base) {src nb X w dst : Nat}
    {st : St} (hw : 2 ≤ w ∧ w ≤ 8) (hdst : dst < 2) (hsrc : src + nb + 8 ≤ 8192)
    (hX : Copied s.mem base src nb X) (hi : st.i < 8 * nb) (hnb : 8 * nb ≤ 512) (hc1 : st.c ≤ 1)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 st.i) (hr8 : s.gpr .r8 = BitVec.ofNat 64 st.c)
    (hu : ∀ j < 528, dig s.mem base dst j = st.u j) :
    WP isa (recodeStep src w dst) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (step w X st).i ∧ t.gpr .r8 = BitVec.ofNat 64 (step w X st).c ∧
      (∀ j < 528, dig t.mem base dst j = (step w X st).u j) ∧ RecKeep base dst s t := by
  rw [recodeStep]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (recodeBits_ok hs hsrc hX hi hrsi (by omega)) fun a ⟨ab, ka⟩ => ?_
  have hbit : (a.gpr .rbx).toNat % 2 = X / 2 ^ st.i % 2 := by
    rw [ab]; exact bits_mod X st.i 1 (by decide)
  have hwin : (a.gpr .rbx).toNat % 2 ^ w = X / 2 ^ st.i % 2 ^ w := by
    rw [ab]; exact bits_mod X st.i w (by omega)
  refine WP.mono (recodeTest_ok a hbit hc1 (by rw [ka.1 _ (by decide)]; exact hr8)) fun b ⟨bz, kb⟩ => ?_
  have kab : Keeps recRegs s b := (ka.mono (by decide)).trans (kb.mono (by decide))
  have hbx : b.gpr .rbx = a.gpr .rbx := kb.1 _ (by decide)
  have hbrsi : b.gpr .rsi = s.gpr .rsi := (kb.1 _ (by decide)).trans (ka.1 _ (by decide))
  have hbr8 : b.gpr .r8 = s.gpr .r8 := (kb.1 _ (by decide)).trans (ka.1 _ (by decide))
  refine WP.ite (decide (X / 2 ^ st.i % 2 = st.c)) (by simp only [eval, bz]) (fun h => ?_) (fun h => ?_)
  · have heq : X / 2 ^ st.i % 2 = st.c := of_decide_eq_true h
    have hst : step w X st = ⟨st.i + 1, st.c, st.u⟩ := by unfold step; rw [ite_eq_left heq]
    rw [hst]
    refine WP.mono (rsiInc_ok b (i := st.i) (by rw [hbrsi]; exact hrsi)) fun t ⟨tr, kt⟩ => ?_
    have kbt := kab.trans (kt.mono (by decide))
    refine ⟨tr, by rw [kt.1 _ (by decide), hbr8]; exact hr8, fun j hj => ?_, RecKeep.of_keeps kbt (by decide)⟩
    rw [kbt.2.1]; exact hu j hj
  · have hne : ¬ X / 2 ^ st.i % 2 = st.c := by simpa using h
    have hlt : X / 2 ^ st.i % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [recodeWindow]
    refine WP.seq (WP.mono (recodeW_ok b (W := X / 2 ^ st.i % 2 ^ w) (by omega) (by rw [hbx]; exact hwin) hc1
      (by rw [hbr8]; exact hr8)) fun c ⟨cb, ccf, kc⟩ => ?_)
    have kbc := kab.trans (kc.mono (by decide))
    have hs' : Scratch c base := hs.of_keeps kbc (by decide)
    have crsi : c.gpr .rsi = BitVec.ofNat 64 st.i := by rw [kc.1 _ (by decide), hbrsi]; exact hrsi
    have h8 : 2 ^ w ≤ 256 := (Nat.pow_le_pow_right (by decide) hw.2 : 2 ^ w ≤ 2 ^ 8)
    have h8' : 2 ^ (w - 1) ≤ 256 := (Nat.pow_le_pow_right (by decide) (by omega) : 2 ^ (w - 1) ≤ 2 ^ 8)
    have h1 : 2 ≤ 2 ^ (w - 1) := (Nat.pow_le_pow_right (by decide) (by omega) : 2 ^ 1 ≤ 2 ^ (w - 1))
    refine WP.seq (WP.ite (decide (X / 2 ^ st.i % 2 ^ w + st.c < 2 ^ (w - 1))) (by simp only [eval, ccf])
      (fun hW => ?_) (fun hW => ?_))
    · have hW' : X / 2 ^ st.i % 2 ^ w + st.c < 2 ^ (w - 1) := of_decide_eq_true hW
      have hst : step w X st = ⟨st.i + w, 0, upd st.u st.i (X / 2 ^ st.i % 2 ^ w + st.c)⟩ := by
        unfold step; rw [ite_eq_right hne, ite_eq_left hW']
      rw [hst]
      refine WP.mono (recodePos_ok c) fun d ⟨d8, db, kd⟩ => ?_
      have kcd := kbc.trans (kd.mono (by decide))
      refine WP.mono (recodeStore_ok (hs'.of_keeps kd (by decide)) (i := st.i) (w := w)
        (u := X / 2 ^ st.i % 2 ^ w + st.c) (by omega) hdst
        (by omega) (by rw [kd.1 _ (by decide)]; exact crsi) (by rw [db]; exact cb)) fun t ⟨tr, tm, tg, trd, twr⟩ => ?_
      refine ⟨tr, by rw [tg _ (by decide) (by decide)]; exact d8, fun j hj => ?_, ?_⟩
      · rw [tm, dig_write (by omega) hdst (by omega) hj, kcd.2.1]
        by_cases hji : j = st.i
        · dsimp only; rw [ite_eq_left hji, hji, upd_self]
        · dsimp only; rw [ite_eq_right hji, upd_ne _ _ hji]; exact hu j hj
      · refine ⟨fun r hr => ?_, trd.trans kcd.2.2.1, twr.trans kcd.2.2.2, fun x hx => ?_⟩
        · rw [tg r (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide))]
          exact kcd.1 r hr
        · rw [tm, keep_write (by omega) hdst _ x hx, kcd.2.1]
    · have hW' : ¬ X / 2 ^ st.i % 2 ^ w + st.c < 2 ^ (w - 1) := by simpa using hW
      have hst : step w X st =
          ⟨st.i + w, 1, upd st.u st.i (2 ^ w + 1 - (X / 2 ^ st.i % 2 ^ w + st.c))⟩ := by
        unfold step; rw [ite_eq_right hne, ite_eq_right hW']
      rw [hst]
      refine WP.mono (recodeNeg_ok c hw.2 (by omega) cb) fun d ⟨db, d8, kd⟩ => ?_
      have kcd := kbc.trans (kd.mono (by decide))
      refine WP.mono (recodeStore_ok (hs'.of_keeps kd (by decide)) (i := st.i) (w := w) (by omega) hdst
        (by omega) (by rw [kd.1 _ (by decide)]; exact crsi) db) fun t ⟨tr, tm, tg, trd, twr⟩ => ?_
      refine ⟨tr, by rw [tg _ (by decide) (by decide)]; exact d8, fun j hj => ?_, ?_⟩
      · have hlt' : 2 ^ w + 1 - (X / 2 ^ st.i % 2 ^ w + st.c) < 256 := by omega
        rw [tm, dig_write (by omega) hdst hlt' hj, kcd.2.1]
        by_cases hji : j = st.i
        · dsimp only; rw [ite_eq_left hji, hji, upd_self]
        · dsimp only; rw [ite_eq_right hji, upd_ne _ _ hji]; exact hu j hj
      · refine ⟨fun r hr => ?_, trd.trans kcd.2.2.1, twr.trans kcd.2.2.2, fun x hx => ?_⟩
        · rw [tg r (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide))]
          exact kcd.1 r hr
        · rw [tm, keep_write (by omega) hdst _ x hx, kcd.2.1]

end VG.Proof.Ed25519.X86_64
