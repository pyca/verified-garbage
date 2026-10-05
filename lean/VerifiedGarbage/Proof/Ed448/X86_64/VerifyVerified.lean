import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.VerifyBits`. -/
section

/-!
# Ed448 verification's equation on x86-64: the bits of the scalars

`bitsAt o` stores bit `j` of byte `i` of the 57 bytes at `rsi` at byte
`o + 8i + j` of the working space: base-point multiplication's `bits`
(`BaseBits.lean`) at any offset `o`, for `S` and `k`.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr word off Outside ofs ofs_off' contains_sc
  ea_scalar bit_byte writeW8_apply writeW8_outside off_eq_iff inc_eq)

/-- Bit `j` of `rax` (a byte) into `[rdi + 8 rbx + o + j]`. -/
def bitJO (o j : Nat) : List Instr :=
  [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
    [.alu .and .rdx (.imm 1),
      .store8 { base := .rdi, index := some .rbx, scale := 8, disp := ((o + j : Nat) : Int) } .rdx]

theorem ea_bitAtO (s : State) (o j : Nat) :
    s.ea { base := .rdi, index := some .rbx, scale := 8, disp := ((o + j : Nat) : Int) } =
      s.gpr .rdi + s.gpr .rbx * BitVec.ofNat 64 8 + BitVec.ofNat 64 (o + j) := by
  simp only [State.ea, BitVec.ofInt_natCast]

theorem addr_bitO (base : Addr) (o i j : Nat) :
    base + BitVec.ofNat 64 i * BitVec.ofNat 64 8 + BitVec.ofNat 64 (o + j) =
      off base (o + (8 * i + j)) := by
  rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

variable {o : Nat} (ho : o + 456 ≤ 8192)

include ho in
theorem bitJO_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {b : BitVec 8} (ha : s.gpr .rax = b.setWidth 64)
    {j : Nat} (hj : j < 8) :
    WP isa (.block (VG.Proof.Ed448.X86_64.bitJO o j)) s fun s' =>
      (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base (o + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  have w : InRegions s.wr (off base (o + (8 * i + j))) 1 :=
    ⟨_, hs.wr, contains_sc (by omega)⟩
  have e := bit_byte b j hj
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [VG.Proof.Ed448.X86_64.bitJO, ite_true, List.nil_append, List.cons_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, VG.X86_64.readSrc, execAlu, State.store8, VG.Proof.Ed448.X86_64.ea_bitAtO, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg,
      RegUpd.mem_arithFlags, hs.rdi, hb, ha, VG.Proof.Ed448.X86_64.addr_bitO, w, ite_false, reduceCtorEq, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun r hr => ?_, rfl, by trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]; rfl
  · simp only [VG.Proof.Ed448.X86_64.bitJO, show ¬j = 0 by omega, ite_false, List.nil_append, List.cons_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, execShift, State.store8,
    VG.Proof.Ed448.X86_64.ea_bitAtO, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_setFlags, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
    RegUpd.mem_arithFlags, hs.rdi, hb, ha, VG.Proof.Ed448.X86_64.addr_bitO, w, show 1 ≤ j ∧ j ≤ 63 from ⟨hj0, by omega⟩,
    ite_true, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    and_self]
    refine ⟨fun r hr => ?_, rfl, by trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]

theorem bitsBodyAt_eq : bitsBodyAt o = ([.movzx8 .rax { base := .rsi, index := some .rbx }] : List Instr) ++
    (VG.Proof.Ed448.X86_64.bitJO o 0 ++ (VG.Proof.Ed448.X86_64.bitJO o 1 ++ (VG.Proof.Ed448.X86_64.bitJO o 2 ++ (VG.Proof.Ed448.X86_64.bitJO o 3 ++ (VG.Proof.Ed448.X86_64.bitJO o 4 ++ (VG.Proof.Ed448.X86_64.bitJO o 5 ++ (VG.Proof.Ed448.X86_64.bitJO o 6 ++ (VG.Proof.Ed448.X86_64.bitJO o 7 ++
      ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 57)] : List Instr))))))))) := rfl

include ho in
theorem bitsBodyAt_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .rsi = k)
    {i : Nat} (hi : i < 57) (hb : s.gpr .rbx = BitVec.ofNat 64 i)
    (hkr : InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 i) 1) :
    WP isa (.block (bitsBodyAt o)) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = 57)) ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ j < 8, s'.mem (off base (o + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (k + BitVec.ofNat 64 i)).toNat >>> j) &&& 1)) ∧
      Outside base (o + 8 * i) 8 s.mem s'.mem := by
  rw [VG.Proof.Ed448.X86_64.bitsBodyAt_eq, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movzx8 .rax { base := .rsi, index := some .rbx }]) s
      (fun s' => s'.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 ∧
        (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_scalar s hk hb, State.load8, hkr,
      ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s₀ ⟨a0, g0, m0, rd0, wr0⟩ => ?_
  have hs₀ : Scr s₀ base := ⟨(g0 _ (by decide)).trans hs.rdi, wr0 ▸ hs.wr, hs.nowrap⟩
  have hb₀ : s₀.gpr .rbx = BitVec.ofNat 64 i := (g0 _ (by decide)).trans hb
  have keep : ∀ {x y : State}, (∀ r, r ≠ .rdx → y.gpr r = x.gpr r) → y.rd = x.rd → y.wr = x.wr →
      Scr x base → x.gpr .rbx = BitVec.ofNat 64 i → x.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 →
      Scr y base ∧ y.gpr .rbx = BitVec.ofNat 64 i ∧ y.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 :=
    fun g _ wr hx hbx hax => ⟨⟨(g _ (by decide)).trans hx.rdi, wr ▸ hx.wr, hx.nowrap⟩,
      (g _ (by decide)).trans hbx, (g _ (by decide)).trans hax⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJO_ok ho hs₀ hi hb₀ a0 (j := 0) (by omega)) fun s₁ ⟨g1, rd1, wr1, m1⟩ => ?_
  obtain ⟨hs₁, hb₁, ha₁⟩ := keep g1 rd1 wr1 hs₀ hb₀ a0
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJO_ok ho hs₁ hi hb₁ ha₁ (j := 1) (by omega)) fun s₂ ⟨g2, rd2, wr2, m2⟩ => ?_
  obtain ⟨hs₂, hb₂, ha₂⟩ := keep g2 rd2 wr2 hs₁ hb₁ ha₁
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJO_ok ho hs₂ hi hb₂ ha₂ (j := 2) (by omega)) fun s₃ ⟨g3, rd3, wr3, m3⟩ => ?_
  obtain ⟨hs₃, hb₃, ha₃⟩ := keep g3 rd3 wr3 hs₂ hb₂ ha₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJO_ok ho hs₃ hi hb₃ ha₃ (j := 3) (by omega)) fun s₄ ⟨g4, rd4, wr4, m4⟩ => ?_
  obtain ⟨hs₄, hb₄, ha₄⟩ := keep g4 rd4 wr4 hs₃ hb₃ ha₃
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJO_ok ho hs₄ hi hb₄ ha₄ (j := 4) (by omega)) fun s₅ ⟨g5, rd5, wr5, m5⟩ => ?_
  obtain ⟨hs₅, hb₅, ha₅⟩ := keep g5 rd5 wr5 hs₄ hb₄ ha₄
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJO_ok ho hs₅ hi hb₅ ha₅ (j := 5) (by omega)) fun s₆ ⟨g6, rd6, wr6, m6⟩ => ?_
  obtain ⟨hs₆, hb₆, ha₆⟩ := keep g6 rd6 wr6 hs₅ hb₅ ha₅
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJO_ok ho hs₆ hi hb₆ ha₆ (j := 6) (by omega)) fun s₇ ⟨g7, rd7, wr7, m7⟩ => ?_
  obtain ⟨hs₇, hb₇, ha₇⟩ := keep g7 rd7 wr7 hs₆ hb₆ ha₆
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJO_ok ho hs₇ hi hb₇ ha₇ (j := 7) (by omega)) fun s₈ ⟨g8, rd8, wr8, m8⟩ => ?_
  obtain ⟨hs₈, hb₈, ha₈⟩ := keep g8 rd8 wr8 hs₇ hb₇ ha₇
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb₈, inc_eq,
    ite_true, RegUpd.zf_arithFlags, RegUpd.rd_arithFlags, RegUpd.rd_setReg, RegUpd.wr_arithFlags,
    RegUpd.wr_setReg, RegUpd.mem_arithFlags, RegUpd.mem_setReg, cmp57 i hi]
  have hm : s₀.mem = s.mem := m0
  refine ⟨trivial, trivial, fun r hr => ?_, ?_, ?_, fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ite_eq_right hr.2.2, g8 r hr.2.1, g7 r hr.2.1, g6 r hr.2.1, g5 r hr.2.1, g4 r hr.2.1, g3 r hr.2.1,
      g2 r hr.2.1, g1 r hr.2.1, g0 r hr.1]
  · rw [rd8, rd7, rd6, rd5, rd4, rd3, rd2, rd1, rd0]
  · rw [wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1, wr0]
  · rw [m8, m7, m6, m5, m4, m3, m2, m1]
    have ne : ∀ a b, a < 8 → b < 8 → a ≠ b →
        off base (o + (8 * i + a)) ≠ off base (o + (8 * i + b)) := by
      intro a b ha hb hab h
      rw [off_eq_iff base (by omega) (by omega)] at h
      omega
    have ne' : ∀ a b, a < 8 → b < 8 → a ≠ b →
        (off base (o + (8 * i + a)) = off base (o + (8 * i + b))) = False :=
      fun a b ha hb hab => eq_false (ne a b ha hb hab)
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [writeW8_apply, ite_true, ne', ite_false]
  · intro x hx
    have hd : ∀ j < 8, ofs base x ≠ o + (8 * i + j) := fun j hj h => by omega
    have hb : ∀ j < 8, o + (8 * i + j) < 2 ^ 64 := fun j hj => by omega
    rw [m8, m7, m6, m5, m4, m3, m2, m1, writeW8_outside _ _ _ (hb 7 (by omega)) (hd 7 (by omega)),
      writeW8_outside _ _ _ (hb 6 (by omega)) (hd 6 (by omega)),
      writeW8_outside _ _ _ (hb 5 (by omega)) (hd 5 (by omega)),
      writeW8_outside _ _ _ (hb 4 (by omega)) (hd 4 (by omega)),
      writeW8_outside _ _ _ (hb 3 (by omega)) (hd 3 (by omega)),
      writeW8_outside _ _ _ (hb 2 (by omega)) (hd 2 (by omega)),
      writeW8_outside _ _ _ (hb 1 (by omega)) (hd 1 (by omega)),
      writeW8_outside _ _ _ (hb 0 (by omega)) (hd 0 (by omega)), hm]

/-- `bitsAt`' loop invariant, after `i` bytes. -/
structure BInvO (o : Nat) (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  rsi : s.gpr .rsi = k
  rbx : s.gpr .rbx = BitVec.ofNat 64 i
  gpr : ∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base o 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (o + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

include ho in
theorem bitsLoopAt_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → VG.Proof.Ed448.X86_64.BInvO o base k s₀ s i →
      WP isa (.loop (.block (bitsBodyAt o)) .ne) s fun s' => VG.Proof.Ed448.X86_64.BInvO o base k s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block (bitsBodyAt o)) (c := .ne)
    (Q := fun s' => VG.Proof.Ed448.X86_64.BInvO o base k s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ VG.Proof.Ed448.X86_64.BInvO o base k s₀ s i) ?_ (57 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.bitsBodyAt_ok ho hb.scr hb.rsi hi hb.rbx (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', g', rd', wr', bits', o'⟩ => ?_
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; omega)
  have inv : VG.Proof.Ed448.X86_64.BInvO o base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.rdi, wr' ▸ hb.scr.wr, hb.scr.nowrap⟩,
      (g' _ (by decide)).trans hb.rsi, b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z', Option.map_some]
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega
    exact .inl ⟨rfl, inv⟩

include ho in
/-- `bits`: byte `t` of `o` is bit `t` of byte `t / 8` of the scalar, for
`t < 456`. -/
theorem bitsAt_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .rsi = k)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa (bitsAt o) s fun s' =>
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base o 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (o + t)) =
        BitVec.ofNat 8 (((s.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1) := by
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 0)]) s (fun s' =>
      VG.Proof.Ed448.X86_64.BInvO o base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left']
    refine ⟨⟨hs.rdi, hs.wr, hs.nowrap⟩, hk, rfl, fun r hr => ?_, rfl, rfl, Outside.refl _ _ _ _,
      fun t ht => absurd ht (by omega)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.2.2, ite_false]) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86_64.bitsLoopAt_ok ho hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_
  exact ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => h₂.bits t (by omega)⟩

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit`. -/
section

/-!
# Ed448 verification's equation on x86-64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse
them. The pieces come first, so that the whole function's literal calls theirs.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

materialize_code verifyRootLit := (root Impl.X448.X86_64.baseline 12 : Prog isa)
materialize_code verifyDecodeALit := (decode Impl.X448.X86_64.baseline 6 7 : Prog isa)
materialize_code verifyDecodeRLit := (decode Impl.X448.X86_64.baseline 8 9 : Prog isa)
materialize_code verifyDecodeAFullLit := (vdecodeA Impl.X448.X86_64.baseline : Prog isa)
materialize_code verifyLoopLit := (vloop Impl.X448.X86_64.baseline : Prog isa)
materialize_code verifyFinishLit := (vfinish Impl.X448.X86_64.baseline : Prog isa)

end VG.Proof.Ed448.X86_64

namespace VG

materialize_code Impl.Ed448.X86_64.verifyEquation

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.VerifyLocal`. -/
section

/-!
# Ed448 verification's equation on x86-64: the contract the proof is written against

The facts of `Spec.Ed448.verifyEquationContract` the proof uses, stated for
x86-64, in a module of their own: callers proven for any code meeting them
need not import the proof, and the group theory it imports.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64

/-- `vg_ed448_verify_equation(pk = rdi, signature = rsi, challenge = rdx, scratch = rcx) -> eax`. -/
def verifyEquationLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rsi, 114⟩, ⟨s.gpr .rdx, 57⟩] ∧
    s.wr = [⟨s.gpr .rcx, 8192⟩] ∧
    (⟨s.gpr .rdi, 57⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsi, 114⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rdx, 57⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .rax = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) then 1 else 0
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop`. -/
section

/-!
# Ed448 verification's equation on x86-64: `[S]B + [k](-A)`

One iteration of `vloop` (`vstep_ok`), for the bits `t` of `S` (at `BITS`)
and of `k` (at `KBITS`): `Q` doubled, then `B` (slots 8–10) added and
swapped in by the first bit, and `-A` (slots 6, 7 and 10) by the second. The
loop's invariant (`VInv`): `Q` is the reference ladder's point after the
bits above `n` (`Proof.Ed448.vladder`).
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk off contains_sc mask cswapE opSwap clob Outside)
open VG.Impl.X448.X86_64 (BITS slot cswap)

theorem ea_bitsAt {s : State} {base : Addr} (hr : s.gpr .rdi = base) {t : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (o : Nat) :
    s.ea { base := .rdi, index := some .rbx, disp := (o : Int) } = off base (o + t) := by
  simp only [State.ea, hr, hb, off, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm t o]

theorem maskAt_ok {s : State} {base : Addr} (hs : Scr s base) {o t : Nat} (ho : o + t < 8192)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (o + t)) = BitVec.ofNat 8 b) :
    WP isa (.block (maskAt o)) s fun s' =>
      s'.gpr .rcx = mask (decide (b = 1)) ∧ (∀ r, r ∉ [Reg.rdx, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s.rd ++ s.wr) (off base (o + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩
  apply WP.of_runBlock
  simp only [maskAt, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    State.load8, VG.Proof.Ed448.X86_64.ea_bitsAt hs.rdi hb, hin, hbit, ite_true, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨mask_bit b hb2, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

/-- The slots after a swap of `T` into `Q`. -/
def swapEnv (sw : Bool) (e : Env) : Env := opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw e))

/-- The slots after an iteration, for the bits `sw₁` (of `S`) and `sw₂` (of `k`). -/
def vstepEnv (sw₁ sw₂ : Bool) (e : Env) : Env :=
  VG.Proof.Ed448.X86_64.swapEnv sw₂ (evalOps (VG.Impl.Ed448.addAt 6 7) (VG.Proof.Ed448.X86_64.swapEnv sw₁ (evalOps (VG.Impl.Ed448.addAt 8 9) (evalOps (doubleAt 0 1 2) e))))

theorem pt_swap (sw : Bool) (e : Env) :
    pt (VG.Proof.Ed448.X86_64.swapEnv sw e) 0 1 2 = if sw then pt e 3 4 5 else pt e 0 1 2 := by
  cases sw <;> rfl

theorem swapEnv_keep (sw : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val) : VG.Proof.Ed448.X86_64.swapEnv sw e i = e i := by
  have h0 : i ≠ 0 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h1 : i ≠ 1 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h2 : i ≠ 2 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h3 : i ≠ 3 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h4 : i ≠ 4 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h5 : i ≠ 5 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  simp only [VG.Proof.Ed448.X86_64.swapEnv, opSwap, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]

theorem pt_congr {e e' : Env} {a b c : Index} (ha : e' a = e a) (hb : e' b = e b) (hc : e' c = e c) :
    pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]

theorem vstepEnv_keep (sw₁ sw₂ : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val ∧ i.val < 12) :
    VG.Proof.Ed448.X86_64.vstepEnv sw₁ sw₂ e i = e i := by
  rw [VG.Proof.Ed448.X86_64.vstepEnv, VG.Proof.Ed448.X86_64.swapEnv_keep _ _ _ hi.1, addAt_keep _ _ _ _ (Or.inr (Or.inl hi)), VG.Proof.Ed448.X86_64.swapEnv_keep _ _ _ hi.1,
    addAt_keep _ _ _ _ (Or.inr (Or.inl hi)), doubleAt_keep0 _ _ (Or.inl ⟨by omega, hi.2⟩)]

theorem vstepEnv_pt (sw₁ sw₂ : Bool) (e : Env) :
    pt (VG.Proof.Ed448.X86_64.vstepEnv sw₁ sw₂ e) 0 1 2 =
      let r₁ := Proof.Ed448.double (pt e 0 1 2)
      let r₂ := if sw₁ then addWith (e 11) r₁ (pt e 8 9 10) else r₁
      if sw₂ then addWith (e 11) r₂ (pt e 6 7 10) else r₂ := by
  -- the stages
  unfold VG.Proof.Ed448.X86_64.vstepEnv
  generalize he0 : evalOps (doubleAt 0 1 2) e = e0
  have p0 : pt e0 0 1 2 = Proof.Ed448.double (pt e 0 1 2) := by rw [← he0, doubleAt_eval0]
  have k0 : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, doubleAt_keep0 _ _ (Or.inl hi)]
  generalize he1 : evalOps (VG.Impl.Ed448.addAt 8 9) e0 = e1
  have p1 : pt e1 3 4 5 = addWith (e0 11) (pt e0 0 1 2) (pt e0 8 9 10) := by rw [← he1, addAt_eval8]
  have q1 : pt e1 0 1 2 = pt e0 0 1 2 :=
    VG.Proof.Ed448.X86_64.pt_congr (by rw [← he1, addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he1, addAt_keep _ _ _ _ (Or.inl (by decide))]) (by rw [← he1, addAt_keep _ _ _ _ (Or.inl (by decide))])
  have k1 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e1 i = e0 i := fun i hi => by
    rw [← he1, addAt_keep _ _ _ _ (Or.inr (Or.inl hi))]
  generalize he2 : VG.Proof.Ed448.X86_64.swapEnv sw₁ e1 = e2
  have p2 : pt e2 0 1 2 = if sw₁ then pt e1 3 4 5 else pt e1 0 1 2 := by rw [← he2, VG.Proof.Ed448.X86_64.pt_swap]
  have k2 : ∀ i : Index, 6 ≤ i.val → e2 i = e1 i := fun i hi => by rw [← he2, VG.Proof.Ed448.X86_64.swapEnv_keep _ _ _ hi]
  generalize he3 : evalOps (VG.Impl.Ed448.addAt 6 7) e2 = e3
  have p3 : pt e3 3 4 5 = addWith (e2 11) (pt e2 0 1 2) (pt e2 6 7 10) := by rw [← he3, addAt_eval6]
  have q3 : pt e3 0 1 2 = pt e2 0 1 2 :=
    VG.Proof.Ed448.X86_64.pt_congr (by rw [← he3, addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he3, addAt_keep _ _ _ _ (Or.inl (by decide))]) (by rw [← he3, addAt_keep _ _ _ _ (Or.inl (by decide))])
  have e11 : e2 11 = e 11 := by rw [k2 11 (by decide), k1 11 (by decide), k0 11 (by decide)]
  have e11' : e0 11 = e 11 := k0 11 (by decide)
  have b8 : pt e0 8 9 10 = pt e 8 9 10 :=
    VG.Proof.Ed448.X86_64.pt_congr (k0 8 (by decide)) (k0 9 (by decide)) (k0 10 (by decide))
  have a6 : pt e2 6 7 10 = pt e 6 7 10 :=
    VG.Proof.Ed448.X86_64.pt_congr (by rw [k2 6 (by decide), k1 6 (by decide), k0 6 (by decide)])
      (by rw [k2 7 (by decide), k1 7 (by decide), k0 7 (by decide)])
      (by rw [k2 10 (by decide), k1 10 (by decide), k0 10 (by decide)])
  rw [VG.Proof.Ed448.X86_64.pt_swap, p3, q3, p2, p1, q1, e11, e11', b8, a6, p0]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

/-- `T` swapped into `Q` by the mask `rcx`. -/
theorem swapT_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block swapT) s fun s' => Keep base s s' ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.Ed448.X86_64.swapEnv sw (VG.Proof.X448.X86_64.E s.mem base) := by
  rw [swapT, List.append_assoc, WP.block_append_iff]
  refine WP.mono (cswapE hs 0 3 (by decide) hc) fun s5 ⟨k5, c5, e5⟩ => ?_
  have hs5 := k5.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs5 1 4 (by decide) (c5.trans hc)) fun s6 ⟨k6, c6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  refine WP.mono (cswapE hs6 2 5 (by decide) (c6.trans (c5.trans hc))) fun s7 ⟨k7, _, e7⟩ => ?_
  exact ⟨(k5.trans k6).trans k7, by rw [e7, e6, e5]; rfl⟩

include hf in
/-- An iteration, for the bits `t` of `S` (`b₁`) and of `k` (`b₂`). -/
theorem vstep_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {b₁ b₂ : Nat} (hb₁ : b₁ < 2) (hb₂ : b₂ < 2)
    (hbit₁ : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b₁)
    (hbit₂ : s.mem (off base (KBITS + t)) = BitVec.ofNat 8 b₂) :
    WP isa (vstep fld) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.zf = some (decide (t = 0)) ∧
      (∀ r, r ∉ .rbx :: clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 64 1584 s.mem s'.mem ∧
      VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.Ed448.X86_64.vstepEnv (decide (b₁ = 1)) (decide (b₂ = 1)) (VG.Proof.X448.X86_64.E s.mem base) := by
  rw [vstep]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (dec_ok s hb) fun s1 ⟨b1, g1, m1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid0 hs1) fun s2 ⟨k2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf _ addAt_valid8 hs2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  have b3 : s3.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k3.gpr _ (by decide), k2.gpr _ (by decide)]; exact b1
  have hout : ∀ o, 2048 ≤ o → o + t < 8192 → Proof.X448.X86_64.ofs base (off base (o + t)) < 64 ∨
      64 + 1584 ≤ Proof.X448.X86_64.ofs base (off base (o + t)) := fun o h1 h2 =>
    Or.inr (by rw [Proof.X448.X86_64.ofs_off' base (by omega)]; omega)
  have hbit3 : s3.mem (off base (BITS + t)) = BitVec.ofNat 8 b₁ := by
    rw [k3.mem _ (hout BITS (by decide) (by simp only [BITS]; omega)),
      k2.mem _ (hout BITS (by decide) (by simp only [BITS]; omega)), m1, hbit₁]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.maskAt_ok hs3 (by simp only [BITS]; omega) b3 hb₁ hbit3) fun s4 ⟨c4, g4, m4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.swapT_ok hs4 c4) fun s5 ⟨k5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf _ addAt_valid6 hs5) fun s6 ⟨k6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  have b6 : s6.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k6.gpr _ (by decide), k5.gpr _ (by decide), g4 _ (by decide)]; exact b3
  have hbit6 : s6.mem (off base (KBITS + t)) = BitVec.ofNat 8 b₂ := by
    rw [k6.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)),
      k5.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)), m4,
      k3.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)),
      k2.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)), m1, hbit₂]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.maskAt_ok hs6 (by simp only [KBITS]; omega) b6 hb₂ hbit6) fun s7 ⟨c7, g7, m7, rd7, wr7⟩ => ?_
  have hs7 : Scr s7 base := ⟨(g7 _ (by decide)).trans hs6.rdi, wr7 ▸ hs6.wr, hs6.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.swapT_ok hs7 c7) fun s8 ⟨k8, e8⟩ => ?_
  have b8 : s8.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k8.gpr _ (by decide), g7 _ (by decide)]; exact b6
  refine WP.mono (testRbx_ok s8 t ht b8) fun s' ⟨z', g', m', rd', wr'⟩ => ?_
  refine ⟨(g' _).trans b8, z', fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    have hdc : r ∉ [Reg.rdx, .rcx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr.2 (h ▸ by decide), fun h => hr.2 (h ▸ by decide)⟩
    rw [g', k8.gpr r hr.2, g7 r hdc, k6.gpr r hr.2, k5.gpr r hr.2, g4 r hdc, k3.gpr r hr.2, k2.gpr r hr.2,
      g1 r hr.1]
  · rw [rd', k8.rd, rd7, k6.rd, k5.rd, rd4, k3.rd, k2.rd, rd1]
  · rw [wr', k8.wr, wr7, k6.wr, k5.wr, wr4, k3.wr, k2.wr, wr1]
  · rw [m', ← m1]
    exact ((((k2.mem.trans k3.mem).trans (by rw [m4]; exact Outside.refl _ _ _ _)).trans
      (k5.mem.trans k6.mem)).trans (by rw [m7]; exact Outside.refl _ _ _ _)).trans k8.mem
  · rw [m', e8, m7, e6, e5, m4, e3, e2, m1]
    rfl

/-- One bit of both scalars: the reference ladder's point after the bits above
`t`, then after bit `t`. -/
theorem vladder_step {e : Env} {S K t : Nat} {A : Spec.Ed448.Point} (ht : t < 456)
    (hr : pt e 0 1 2 = vladder S K A (456 - (t + 1)))
    (hq : pt e 8 9 10 = Spec.Ed448.basePoint) (ha : pt e 6 7 10 = A) (hd : e 11 = Spec.Ed448.d) :
    pt (VG.Proof.Ed448.X86_64.vstepEnv (decide ((S >>> t) &&& 1 = 1)) (decide ((K >>> t) &&& 1 = 1)) e) 0 1 2 =
      vladder S K A (456 - t) := by
  rw [VG.Proof.Ed448.X86_64.vstepEnv_pt, hd, hq, ha, hr, vladder_bit S K A ht]
  simp only [addWith_d]
  rfl

/-- The loop's invariant, after the bits above `n` of `S` and `k`, with `-A` the point `A`. -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 1584 s₀.mem s.mem
  q : pt (VG.Proof.X448.X86_64.E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  na : pt (VG.Proof.X448.X86_64.E s.mem base) 6 7 10 = A
  d : VG.Proof.X448.X86_64.E s.mem base 11 = Spec.Ed448.d
  rep : pt (VG.Proof.X448.X86_64.E s.mem base) 0 1 2 = vladder S K A (456 - n)

include hf in
theorem vloop_ok {s₀ : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbs : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1))
    (hbk : ∀ t < 456, s₀.mem (off base (KBITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 456 → VG.Proof.Ed448.X86_64.VInv base S K A s₀ n s →
      WP isa (.loop (vstep fld) .ne) s fun s' => VG.Proof.Ed448.X86_64.VInv base S K A s₀ 0 s' := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := fun s' => VG.Proof.Ed448.X86_64.VInv base S K A s₀ 0 s')
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VG.Proof.Ed448.X86_64.VInv base S K A s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hb1 : (S >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hb2 : (K >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hout : ∀ o, 2048 ≤ o → o + t < 8192 → Proof.X448.X86_64.ofs base (off base (o + t)) < 64 ∨
      64 + 1584 ≤ Proof.X448.X86_64.ofs base (off base (o + t)) := fun o h1 h2 =>
    Or.inr (by rw [Proof.X448.X86_64.ofs_off' base (by omega)]; omega)
  have hbit1 : s.mem (off base (BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1) := by
    rw [hi.mem _ (hout BITS (by decide) (by simp only [BITS]; omega))]
    exact hbs t (by omega)
  have hbit2 : s.mem (off base (KBITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1) := by
    rw [hi.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega))]
    exact hbk t (by omega)
  refine WP.mono (VG.Proof.Ed448.X86_64.vstep_ok hf hi.scr (by omega) hi.rbx hb1 hb2 hbit1 hbit2)
    fun s' ⟨b', z', g', rd', wr', o', e'⟩ => ?_
  have k' : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → VG.Proof.X448.X86_64.E s'.mem base i = VG.Proof.X448.X86_64.E s.mem base i := fun i hi => by
    rw [e', VG.Proof.Ed448.X86_64.vstepEnv_keep _ _ _ _ hi]
  have inv : VG.Proof.Ed448.X86_64.VInv base S K A s₀ t s' := by
    refine ⟨⟨(g' _ (by decide)).trans hi.scr.rdi, wr' ▸ hi.scr.wr, hi.scr.nowrap⟩, b',
      fun r hr => (g' r hr).trans (hi.gpr r hr), rd'.trans hi.rd, wr'.trans hi.wr,
      hi.mem.trans o', ?_, ?_, ?_, ?_⟩
    · rw [VG.Proof.Ed448.X86_64.pt_congr (k' 8 (by decide)) (k' 9 (by decide)) (k' 10 (by decide))]; exact hi.q
    · rw [VG.Proof.Ed448.X86_64.pt_congr (k' 6 (by decide)) (k' 7 (by decide)) (k' 10 (by decide))]; exact hi.na
    · rw [k' 11 (by decide)]; exact hi.d
    · rw [e']; exact VG.Proof.Ed448.X86_64.vladder_step (by omega) hi.rep hi.q hi.na hi.d
  simp only [eval, z', Option.map_some]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬t = 0), Bool.not_false], t, by omega,
      h, by omega, inv⟩

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain`. -/
section

/-!
# Ed448 verification's equation on x86-64: the whole function

The correctness of `vg_ed448_verify_equation` against the contract the proof
is written against (`verifyEquationLocal`, `VerifyLocal.lean`): `BAD` ends as the OR of
the checks of `S`, of decoding `A` and `R`, and of the comparison of `[4]Q`
with `[4]R`, for `Q` the reference ladder's `[S]B + [k](-A)` (`vladder`), which
decides the equation when `A` and `R` decode (`VerifyEqOk`, as decoding
`RecoverOk`, passed in by the registration files);
every write is in the working space, so the inputs are read unchanged, the
callee-saved registers are restored from it, and the return address is kept.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk word off Outside Outside2 ofs Saved clob
  writeW_outside word_writeW_self contains_sc E_outside)
open VG.Impl.X448.X86_64 (W w sc at_ slot BITS)

/-- One store of `r` at `[b + d]`, `b` the working space. -/
theorem store1_ok {s : State} {base : Addr} (b r : Reg) (hb : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.store (at_ b d) r] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions s.wr (base + BitVec.ofNat 64 d) 8 := ⟨_, hw, contains_sc hd⟩
  erun [hb, w]

/-- `rsi = [rdi + d]`. -/
theorem movRsi_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.mov .rsi (.mem (sc d))] : List Instr)) s fun t =>
      t.gpr .rsi = word s.mem base d ∧ (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 d) 8 := hs.read hd
  erun [hs.rdi, rb]
  exact fun r hr => by simp only [hr, ite_false]

/-- `[4]Q` and `[4]R`, doubling `Q` twice and then `R` twice. -/
def vcompare : List FOp := doubleAt 0 1 2 ++ doubleAt 0 1 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10

/-- The slots after `vcompare` and the first products: `[4]Q` and `[4]R`, `X_Q Z_R` and `X_R Z_Q`. -/
theorem compare_eval (e : Env) :
    pt (evalOps (VG.Proof.Ed448.X86_64.vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e) 0 1 2 =
      Proof.Ed448.double (Proof.Ed448.double (pt e 0 1 2)) ∧
    pt (evalOps (VG.Proof.Ed448.X86_64.vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e) 8 9 10 =
      Proof.Ed448.double (Proof.Ed448.double (pt e 8 9 10)) ∧
    evalOps (VG.Proof.Ed448.X86_64.vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 12 =
      evalOps (VG.Proof.Ed448.X86_64.vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 0 *
        evalOps (VG.Proof.Ed448.X86_64.vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 10 ∧
    evalOps (VG.Proof.Ed448.X86_64.vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 13 =
      evalOps (VG.Proof.Ed448.X86_64.vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 8 *
        evalOps (VG.Proof.Ed448.X86_64.vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 2 := by
  rw [evalOps_append]
  have h4 : ∀ (ec : Env) (i : Index), i.val < 3 ∨ (8 ≤ i.val ∧ i.val < 11) →
      evalOps [.mul 12 0 10, .mul 13 8 2] ec i = ec i := fun ec i hi =>
    evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl <;> simp only [fopDest] <;> omega
  have p12 : ∀ ec : Env, evalOps [.mul 12 0 10, .mul 13 8 2] ec 12 = ec 0 * ec 10 := fun _ => rfl
  have p13 : ∀ ec : Env, evalOps [.mul 12 0 10, .mul 13 8 2] ec 13 = ec 8 * ec 2 := fun _ => rfl
  simp only [VG.Proof.Ed448.X86_64.vcompare, evalOps_append]
  generalize h1 : evalOps (doubleAt 0 1 2) e = e1
  generalize h2 : evalOps (doubleAt 0 1 2) e1 = e2
  generalize h3 : evalOps (doubleAt 8 9 10) e2 = e3
  generalize h4' : evalOps (doubleAt 8 9 10) e3 = e4
  have q4 : pt e4 0 1 2 = Proof.Ed448.double (Proof.Ed448.double (pt e 0 1 2)) := by
    rw [VG.Proof.Ed448.X86_64.pt_congr (by rw [← h4', doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h4', doubleAt_keep8 _ _ (Or.inl (by decide))]) (by rw [← h4', doubleAt_keep8 _ _ (Or.inl (by decide))]),
      VG.Proof.Ed448.X86_64.pt_congr (by rw [← h3, doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h3, doubleAt_keep8 _ _ (Or.inl (by decide))]) (by rw [← h3, doubleAt_keep8 _ _ (Or.inl (by decide))]),
      ← h2, doubleAt_eval0, ← h1, doubleAt_eval0]
  have r4 : pt e4 8 9 10 = Proof.Ed448.double (Proof.Ed448.double (pt e 8 9 10)) := by
    rw [← h4', doubleAt_eval8, ← h3, doubleAt_eval8,
      VG.Proof.Ed448.X86_64.pt_congr (by rw [← h2, doubleAt_keep0 _ _ (Or.inl (by decide))])
      (by rw [← h2, doubleAt_keep0 _ _ (Or.inl (by decide))]) (by rw [← h2, doubleAt_keep0 _ _ (Or.inl (by decide))]),
      VG.Proof.Ed448.X86_64.pt_congr (by rw [← h1, doubleAt_keep0 _ _ (Or.inl (by decide))])
      (by rw [← h1, doubleAt_keep0 _ _ (Or.inl (by decide))]) (by rw [← h1, doubleAt_keep0 _ _ (Or.inl (by decide))])]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.Ed448.X86_64.pt_congr (h4 e4 0 (by decide)) (h4 e4 1 (by decide)) (h4 e4 2 (by decide)), q4]
  · rw [VG.Proof.Ed448.X86_64.pt_congr (h4 e4 8 (by decide)) (h4 e4 9 (by decide)) (h4 e4 10 (by decide)), r4]
  · rw [p12, h4 e4 0 (by decide), h4 e4 10 (by decide)]
  · rw [p13, h4 e4 8 (by decide), h4 e4 2 (by decide)]

/-- `rdx = [rdi + BAD]`, then `rdx = (rdx == 0)` into `rax`. -/
theorem result_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (([.mov .rdx (.mem (sc BAD))] : List Instr) ++ (isZero ++
      ([.mov .rax (.reg .rdx)] : List Instr)))) s fun t =>
      t.gpr .rax = (if word s.mem base BAD = 0 then 1 else 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 BAD) 8 := hs.read (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block ([.mov .rdx (.mem (sc BAD))] : List Instr)) s fun t =>
      t.gpr .rdx = word s.mem base BAD ∧ (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr by
    erun [hs.rdi, rb]
    exact fun r hr => by simp only [hr, ite_false]) fun s1 ⟨d1, g1, m1, rd1, wr1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s1) fun s2 ⟨d2, m2, g2, rd2, wr2⟩ => ?_
  refine WP.mono (show WP isa (.block ([.mov .rax (.reg .rdx)] : List Instr)) s2 fun t =>
      t.gpr .rax = s2.gpr .rdx ∧ (∀ r, r ≠ .rax → t.gpr r = s2.gpr r) ∧ t.mem = s2.mem ∧
        t.rd = s2.rd ∧ t.wr = s2.wr by
    erun
    exact fun r hr => by simp only [hr, ite_false]) fun t ⟨at', gt, mt, rdt, wrt⟩ => ?_
  refine ⟨by rw [at', d2, d1], fun r h1 h2 => by rw [gt r h1, g2 r h2, g1 r h2], by rw [mt, m2, m1],
    by rw [rdt, rd2, rd1], by rw [wrt, wr2, wr1]⟩

theorem zero_or64 (x : BitVec 64) : 0 ||| x = x := BitVec.zero_or

/-- `rsi = r9 + 57`. -/
theorem movR957_ok (s : State) :
    WP isa (.block ([.mov .rsi (.reg .r9), .alu .add .rsi (.imm 57)] : List Instr)) s fun t =>
      t.gpr .rsi = s.gpr .r9 + BitVec.ofNat 64 57 ∧ (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  exact ⟨rfl, fun r hr => by simp only [hr, ite_false]⟩

/-- `rax = 0`. -/
theorem movRax0_ok (s : State) :
    WP isa (.block ([.mov32 .rax (.imm 0)] : List Instr)) s fun t =>
      t.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  exact fun r hr => by simp only [hr, ite_false]

/-- The moves of the entry. -/
theorem movArgs_ok (s : State) :
    WP isa (.block ([.mov .r8 (.reg .rdi), .mov .r9 (.reg .rsi), .mov .rdi (.reg .rcx),
      .mov .rsi (.reg .rdx)] : List Instr)) s fun t =>
      t.gpr .r8 = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rsi ∧ t.gpr .rdi = s.gpr .rcx ∧
      t.gpr .rsi = s.gpr .rdx ∧ (∀ r, r ∉ [Reg.r8, .r9, .rdi, .rsi] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- What the entry leaves: the callee-saved registers saved, the pointers to `A` and the
signature in `r8` and `r9`, and the challenge's in `rsi`. -/
theorem ventry_ok {s : State} {base : Addr} (hbase : s.gpr .rcx = base)
    (hws : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block ventry) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ t.gpr .r8 = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rsi ∧
      t.gpr .rsi = s.gpr .rdx ∧ (∀ r, r ∉ [Reg.r8, .r9, .rdi, .rsi] → t.gpr r = s.gpr r) ∧
      Outside base 0 48 s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [ventry, WP.block_append_iff]
  refine WP.mono (saveAt_ok .rcx hbase hws) fun s1 ⟨g1, rd1, wr1, o1, sv1⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.X86_64.movArgs_ok s1) fun t ⟨r8t, r9t, dit, sit, gt, mt, rdt, wrt⟩ => ?_
  refine ⟨⟨by rw [dit, g1, hbase], by rw [wrt, wr1]; exact hws, hn⟩, by rw [mt]; exact sv1,
    by rw [r8t, g1], by rw [r9t, g1], by rw [sit, g1], fun r hr => by rw [gt r hr, g1], by rw [mt]; exact o1,
    by rw [rdt, rd1], by rw [wrt, wr1]⟩

/-- The bits of `k` at `KBITS` and of `S` at `BITS`, and `rsi` the address of `S`. -/
theorem vbits_ok {s : State} {base sig ch : Addr} (hs : Scr s base) (hch : s.gpr .rsi = ch)
    (hsig : s.gpr .r9 = sig)
    (hrs : ∀ q < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 q) 1)
    (hrc : ∀ q < 57, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 q) 1)
    (hfs : ∀ q < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 q))
    (hfc : ∀ q < 57, 8192 ≤ ofs base (ch + BitVec.ofNat 64 q)) :
    WP isa vbits s fun t =>
      (∀ n < 456, t.mem (off base (BITS + n)) = BitVec.ofNat 8
        ((Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (sig + BitVec.ofNat 64 57) 57) >>> n) &&& 1)) ∧
      (∀ n < 456, t.mem (off base (KBITS + n)) = BitVec.ofNat 8
        ((Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem ch 57) >>> n) &&& 1)) ∧
      t.gpr .rsi = sig + BitVec.ofNat 64 57 ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx, .rsi] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base BITS 968 s.mem t.mem := by
  rw [vbits]
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.bitsAt_ok (o := KBITS) (by decide) hs hch hrc hfc) fun s1 ⟨g1, rd1, wr1, o1, b1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.movR957_ok s1) fun s2 ⟨si2, g2, m2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  have hsig2 : s2.gpr .rsi = sig + BitVec.ofNat 64 57 := by rw [si2, g1 _ (by decide), hsig]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitsAt_ok (o := BITS) (by decide) hs2 hsig2
    (fun q hq => by rw [rd2, wr2, rd1, wr1]; exact hrs q hq) hfs) fun t ⟨gt, rdt, wrt, ot, bt⟩ => ?_
  have hm2 : ∀ x, 8192 ≤ ofs base x → s2.mem x = s.mem x := fun x hx => by
    rw [m2, o1 x (Or.inr (by simp only [KBITS]; omega))]
  have h3 : ∀ r, r ∉ [Reg.rax, .rdx, .rbx, .rsi] → r ∉ [Reg.rax, .rdx, .rbx] := fun r hr h =>
    hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h <;> simp only [h, true_or, or_true])
  refine ⟨fun n hn => ?_, fun n hn => ?_, by rw [gt _ (by decide), hsig2], fun r hr => ?_,
    by rw [rdt, rd2, rd1], by rw [wrt, wr2, wr1], fun x hx => ?_⟩
  · rw [bt n hn, hm2 _ (hfs _ (by omega)), scalar_bit s.mem _ hn]
  · have hlt : KBITS + n < 2 ^ 64 := by simp only [KBITS]; omega
    have hofs := VG.Proof.X448.X86_64.ofs_off' base hlt
    rw [ot _ (Or.inr (by rw [hofs]; simp only [BITS, KBITS]; omega)), m2, b1 n hn, scalar_bit s.mem _ hn]
  · have hsi : r ≠ .rsi := fun h => hr (by simp [h])
    rw [gt r (h3 r hr), g2 r hsi, g1 r (h3 r hr)]
  · simp only [BITS] at hx
    rw [ot x (by simp only [BITS]; omega), m2, o1 x (by simp only [KBITS]; omega)]

theorem vstart_eq : vstart = ([.store (sc PPK) .r8] : List Instr) ++ (([.store (sc PSIG) .r9] : List Instr) ++
    (([.mov32 .rax (.imm 0)] : List Instr) ++ (([.store (sc BAD) .rax] : List Instr) ++ sCheck))) := rfl

/-- The pointers to `A` and the signature saved, and `BAD` the check of `S < L`. -/
theorem vstart_ok {s : State} {base pk sig : Addr} (hs : Scr s base) (hpk : s.gpr .r8 = pk)
    (hsig : s.gpr .r9 = sig) (hp : s.gpr .rsi = sig + BitVec.ofNat 64 57)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 i)) :
    WP isa (.block vstart) s fun t =>
      word t.mem base PPK = pk ∧ word t.mem base PSIG = sig ∧
      (∃ c : BitVec 64, (c = 0 ↔ Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem
        (sig + BitVec.ofNat 64 57) 57) < Spec.Ed448.L) ∧ word t.mem base BAD = c) ∧
      (∀ r, r ∉ Reg.rax :: Reg.rdx :: W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base KC 1568 s.mem t.mem := by
  have O3 : ∀ {m : Mem} {d : Nat} (v : BitVec 64), d + 8 < 2 ^ 64 → Outside base d 8 m (m.writeW (off base d) v) :=
    fun v h => writeW_outside _ base v h
  rw [VG.Proof.Ed448.X86_64.vstart_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.store1_ok .rdi .r8 hs.rdi hs.wr (d := PPK) (by decide)) fun s1 ⟨m1, g1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨by rw [g1]; exact hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.store1_ok .rdi .r9 hs1.rdi hs1.wr (d := PSIG) (by decide)) fun s2 ⟨m2, g2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨by rw [g2]; exact hs1.rdi, wr2 ▸ hs1.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.movRax0_ok s2) fun s3 ⟨ax3, g3, m3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.store1_ok .rdi .rax hs3.rdi hs3.wr (d := BAD) (by decide)) fun s4 ⟨m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨by rw [g4]; exact hs3.rdi, wr4 ▸ hs3.wr, hs.nowrap⟩
  have hp4 : s4.gpr .rsi = sig + BitVec.ofNat 64 57 := by
    rw [g4, g3 _ (by decide), g2, g1, hp]
  have rr4 : s4.rd ++ s4.wr = s.rd ++ s.wr := by rw [rd4, wr4, rd3, wr3, rd2, wr2, rd1, wr1]
  have O4 : ∀ x, 8192 ≤ ofs base x → s4.mem x = s.mem x := fun x hx => by
    rw [m4, O3 _ (by decide) x (Or.inr (by simp only [BAD]; omega)), m3, m2,
      O3 _ (by decide) x (Or.inr (by simp only [PSIG]; omega)), m1,
      O3 _ (by decide) x (Or.inr (by simp only [PPK]; omega))]
  refine WP.mono (sCheck_ok hs4 hp4 (by rw [rr4]; exact hr8) (by rw [rr4]; exact hr56) hfar)
    fun t ⟨c, hc, bt, gt, rdt, wrt, ot⟩ => ?_
  have hbytes : Spec.Ed448.bytesAt s4.mem (sig + BitVec.ofNat 64 57) 57 =
      Spec.Ed448.bytesAt s.mem (sig + BitVec.ofNat 64 57) 57 := by
    simp only [Spec.Ed448.bytesAt]
    exact List.map_congr_left fun i hi => O4 _ (hfar i (List.mem_range.mp hi))
  have keepW : ∀ d, d + 8 ≤ BAD → KC + 56 ≤ d → word t.mem base d = word s4.mem base d := fun d h1 h2 =>
    ot.word (Or.inr h2) (Or.inl h1) (by simp only [BAD] at h1; omega)
  refine ⟨?_, ?_, ⟨c, by rw [hc, hbytes], ?_⟩, fun r hr => ?_, by rw [rdt, rd4, rd3, rd2, rd1],
    by rw [wrt, wr4, wr3, wr2, wr1], fun x hx => ?_⟩
  · rw [keepW PPK (by decide) (by decide), m4, (O3 _ (by decide)).word (Or.inl (by decide)) (by decide), m3,
      m2, (O3 _ (by decide)).word (Or.inl (by decide)) (by decide), m1, word_writeW_self, hpk]
  · rw [keepW PSIG (by decide) (by decide), m4, (O3 _ (by decide)).word (Or.inl (by decide)) (by decide), m3,
      m2, word_writeW_self, g1, hsig]
  · rw [bt, m4, word_writeW_self, ax3, VG.Proof.Ed448.X86_64.zero_or64]
  · rw [gt r hr, g4, g3 r (fun h => hr (h ▸ List.mem_cons_self)), g2, g1]
  · simp only [KC] at hx
    rw [ot x (by simp only [KC]; omega) (by simp only [BAD]; omega), m4,
      O3 _ (by decide) x (by simp only [BAD]; omega), m3, m2,
      O3 _ (by decide) x (by simp only [PSIG]; omega), m1,
      O3 _ (by decide) x (by simp only [PPK]; omega)]

theorem bytesAt_take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [Spec.Ed448.bytesAt]) fun i _ _ => ?_
  simp only [Spec.Ed448.bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 114).length = 57 + 57 := by
  simp [Spec.Ed448.bytesAt]

/-- Bytes far from the working space, after writes only to it. -/
theorem far_bytes {base p : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (by have := hf i (List.mem_range.mp hi); omega))

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : Saved base g s.mem) :
    WP isa (vfinish fld) s fun t =>
      t.gpr .rax = (if word s.mem base BAD = 0 ∧ Spec.Ed448.pointEqual
        (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)))
        (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      (∀ rd ∈ Impl.X448.X86_64.saved, t.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ .rbx :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  rw [vfinish]
  apply WP.seq
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid0 hs) fun sa ⟨ka, ea⟩ => ?_
  have hsa := ka.scr hs
  apply WP.seq
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid0 hsa) fun sb ⟨kb, eb⟩ => ?_
  have hsb := kb.scr hsa
  apply WP.seq
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid8 hsb) fun sc' ⟨kc, ec⟩ => ?_
  have hsc := kc.scr hsb
  apply WP.seq
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid8 hsc) fun sd ⟨kd, ed⟩ => ?_
  have hsd := kd.scr hsc
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf [.mul 12 0 10, .mul 13 8 2] (by decide) hsd) fun s1 ⟨k1', e1'⟩ => ?_
  have hs1 := k1'.scr hsd
  have k1 : Keep base s s1 := ((ka.trans kb).trans kc).trans (kd.trans k1')
  have e1 : E s1.mem base = evalOps (VG.Proof.Ed448.X86_64.vcompare ++ [.mul 12 0 10, .mul 13 8 2]) (E s.mem base) := by
    rw [e1', ed, ec, eb, ea]; simp only [VG.Proof.Ed448.X86_64.vcompare, evalOps_append]
  obtain ⟨q1, r1, x12, x13⟩ := VG.Proof.Ed448.X86_64.compare_eval (E s.mem base)
  rw [← e1] at q1 r1 x12 x13
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs1 12 13) fun s2 ⟨c4, hc4, b2, k2, _⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf [.mul 12 1 10, .mul 13 9 2] (by decide) hs2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs3 12 13) fun s4 ⟨c5, hc5, b4, k4, _⟩ => ?_
  have hs4 := k4.scr hs3
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff, List.append_assoc]
  refine WP.mono (VG.Proof.Ed448.X86_64.result_ok hs4) fun s5 ⟨a5, g5, m5, rd5, wr5⟩ => ?_
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide) (by decide)).trans hs4.rdi, wr5 ▸ hs4.wr, hs4.nowrap⟩
  have sv5 : Saved base g s5.mem := by
    rw [m5]
    exact ((((hsv.outside k1.mem (by decide)).outside k2.mem (by decide)).outside k3.mem (by decide)).outside
      k4.mem (by decide))
  refine WP.mono (Proof.X448.X86_64.restore_ok hs5 sv5) fun t ⟨rt, gt, mt, rdt, wrt⟩ => ?_
  -- the values
  have e2 : E s2.mem base = E s1.mem base := k2.E
  have y12 : E s3.mem base 12 = E s1.mem base 1 * E s1.mem base 10 := by rw [e3, e2]; rfl
  have y13 : E s3.mem base 13 = E s1.mem base 9 * E s1.mem base 2 := by rw [e3, e2]; rfl
  have hpe : Spec.Ed448.pointEqual (pt (E s1.mem base) 0 1 2) (pt (E s1.mem base) 8 9 10) = true ↔
      (E s1.mem base 0 * E s1.mem base 10 = E s1.mem base 8 * E s1.mem base 2 ∧
        E s1.mem base 1 * E s1.mem base 10 = E s1.mem base 9 * E s1.mem base 2) := by
    simp only [Spec.Ed448.pointEqual, pt, Bool.and_eq_true, beq_iff_eq]
  have hb : word s4.mem base BAD = word s.mem base BAD ||| c4 ||| c5 := by
    rw [b4, k3.mem.word (Or.inr (by decide)) (by decide), b2, k1.mem.word (Or.inr (by decide)) (by decide)]
  refine ⟨?_, rt, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hcond : (word s.mem base BAD ||| c4 ||| c5 = 0) ↔ (word s.mem base BAD = 0 ∧
        Spec.Ed448.pointEqual (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)))
          (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 8 9 10))) = true) := by
      rw [or_eq_zero64, or_eq_zero64, hc5, hc4, y12, y13, x12, x13, ← q1, ← r1, hpe, and_assoc]
    rw [gt _ (by decide), a5, hb]
    exact if_congr hcond rfl rfl
  · have hr' : r ∉ clob := fun h => hr (List.mem_cons_of_mem _ h)
    have s1' : ∀ x ∈ Reg.rax :: Reg.rdx :: Reg.r15 :: W, x ∈ clob := by decide
    rw [gt r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun h => hr (h ▸ List.mem_cons_self), fun h => hr' (h ▸ by decide), fun h => hr' (h ▸ by decide),
        fun h => hr' (h ▸ by decide), fun h => hr' (h ▸ by decide), fun h => hr' (h ▸ by decide)⟩),
      g5 r (fun h => hr' (h ▸ by decide)) (fun h => hr' (h ▸ by decide)), k4.gpr r (fun h => hr' (s1' r h)),
      k3.gpr r hr', k2.gpr r (fun h => hr' (s1' r h)), k1.gpr r hr']
  · rw [rdt, rd5, k4.rd, k3.rd, k2.rd, k1.rd]
  · rw [wrt, wr5, k4.wr, k3.wr, k2.wr, k1.wr]
  · intro x h1 h2
    rw [mt, m5, k4.mem x h2, k3.mem x h1, k2.mem x h2, k1.mem x h1]

include hf in
/-- `A` decoded and negated into slots 6, 7 and 10, `Q` the neutral point, `B` and `d`. -/
theorem vdecodeA_ok (hR : RecoverOk) {s : State} {base pk : Addr} (hs : Scr s base)
    (hpk : word s.mem base PPK = pk)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (pk + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (pk + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (pk + BitVec.ofNat 64 i)) :
    WP isa (vdecodeA fld) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem pk 57)).isSome) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem pk 57) = some a →
        pt (E t.mem base) 6 7 10 = negPoint a) ∧
      pt (E t.mem base) 0 1 2 = Spec.Ed448.identity ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d ∧
      (∀ r, r ∉ .rbx :: .rsi :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  rw [vdecodeA]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok hs) fun s1 ⟨p1, q1, d1, o1, g1, rd1, wr1, _⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.movRsi_ok hs1 (d := PPK) (by decide)) fun s2 ⟨si2, g2, m2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  have hp2 : s2.gpr .rsi = pk := by rw [si2, o1.word (Or.inr (by decide)) (by decide), hpk]
  have e2 : E s2.mem base = E s1.mem base := by rw [m2]
  have h10 : E s2.mem base 10 = 1 := by rw [e2]; exact (congrArg Spec.Ed448.Point.Z q1 :)
  have h11 : E s2.mem base 11 = Spec.Ed448.d := by rw [e2]; exact d1
  have rr2 : s2.rd = s.rd := by rw [rd2, rd1]
  have ww2 : s2.wr = s.wr := by rw [wr2, wr1]
  have hb2 : Spec.Ed448.bytesAt s2.mem pk 57 = Spec.Ed448.bytesAt s.mem pk 57 := by
    simp only [Spec.Ed448.bytesAt]
    exact List.map_congr_left fun i hi => by
      rw [m2, o1 _ (Or.inr (by have := hfar i (List.mem_range.mp hi); omega))]
  apply WP.seq
  refine WP.mono (decode_ok hf hR hs2 hp2 6 7 (Or.inl ⟨rfl, rfl⟩) h10 h11 (by rw [rr2, ww2]; exact hr8)
    (by rw [rr2, ww2]; exact hr56) hfar) fun s3 ⟨⟨c, hc, b3⟩, v3, k3, g3, rd3, wr3, o3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs2.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok hs3) fun s4 ⟨p4, q4, d4, o4, g4, rd4, wr4, k4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  refine WP.mono (fieldCode_ok hf [.sub 6 0 6] (by decide) hs4) fun t ⟨kt, et⟩ => ?_
  rw [hb2] at hc v3
  have keep : ∀ i : Index, i ≠ 6 → E t.mem base i = E s4.mem base i := fun i hi => by
    rw [et]; exact evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      subst hop; exact fun h => hi (Fin.ext (by simp only [fopDest] at h; omega))
  have t6 : E t.mem base 6 = E s4.mem base 0 - E s4.mem base 6 := by rw [et]; rfl
  refine ⟨⟨c, hc, ?_⟩, fun a ha => ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [kt.mem.word (Or.inr (by decide)) (by decide), o4.word (Or.inr (by decide)) (by decide), b3, m2,
      o1.word (Or.inr (by decide)) (by decide)]
  · obtain ⟨vx, vy, vz⟩ := v3 a ha
    have z0 : E s4.mem base 0 = 0 := (congrArg Spec.Ed448.Point.X p4 :)
    show (⟨E t.mem base 6, E t.mem base 7, E t.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
    rw [t6, keep 7 (by decide), keep 10 (by decide), z0, k4 6 (by decide) (by decide),
      k4 7 (by decide) (by decide), vx, vy, vz, show E s4.mem base 10 = 1 from (congrArg Spec.Ed448.Point.Z q4 :)]
  · rw [VG.Proof.Ed448.X86_64.pt_congr (keep 0 (by decide)) (keep 1 (by decide)) (keep 2 (by decide)), p4]
  · rw [VG.Proof.Ed448.X86_64.pt_congr (keep 8 (by decide)) (keep 9 (by decide)) (keep 10 (by decide)), q4]
  · rw [keep 11 (by decide), d4]
  · have hr' : r ∉ clob := fun h => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    have hW : r ∉ W := fun h => hr' (by
      have : ∀ x ∈ W, x ∈ clob := by decide
      exact this r h)
    rw [kt.gpr r hr', g4 r hW, g3 r (fun h => hr (by
      simp only [List.mem_cons] at h ⊢; rcases h with h | h <;> [exact Or.inl h; exact Or.inr (Or.inr h)])),
      g2 r (fun h => hr (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)), g1 r hW]
  · rw [kt.rd, rd4, rd3, rr2]
  · rw [kt.wr, wr4, wr3, ww2]
  · intro x h1 h2
    rw [kt.mem x h1, o4 x h1, o3 x h1 h2, m2, o1 x h1]

/-- Two stages' bound on what they write, as one range. -/
theorem wide {base : Addr} {m m' : Mem} (h : Outside2 base 64 1584 BAD 80 m m') :
    Outside base 64 1704 m m' :=
  h.outside (by decide) (by decide) (by decide) (by decide)

include hf in
theorem verifyEquation_correct (hR : RecoverOk) (hE : VerifyEqOk) {s : State}
    (hp : verifyEquationLocal.pre s) :
    WP isa (verifyEquationWith fld) s fun t => gprPreserved s t ∧ verifyEquationLocal.post s t := by
  obtain ⟨hr, hw, hdk, hds, hdc, hret, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rcx = b := ⟨_, rfl⟩
  rw [hbase] at hdk hds hdc hret hn hw
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have rpk : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdi, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have rsg : ∀ i n, i + n ≤ 114 → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rsi, 114⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 114) h (by omega)⟩
  have rch : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdx, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdi + BitVec.ofNat 64 i) := fun i hi => far hdk hi (by decide)
  have fsg : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => far hds (by omega) (by decide)
  have fs : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 57 + BitVec.ofNat 64 i) :=
    fun i hi => by rw [Offset.add_add]; exact far hds (by omega) (by decide)
  have fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdx + BitVec.ofNat 64 i) := fun i hi => far hdc hi (by decide)
  obtain ⟨S, hS⟩ : ∃ S, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 57) 57) = S :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) = K := ⟨_, rfl⟩
  rw [verifyEquationWith]
  -- The entry: the callee-saved registers saved, and the pointers.
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.ventry_ok hbase hws hn) fun s1 ⟨hs1, sv1, r81, r91, si1, g1, o1, rd1, wr1⟩ => ?_
  have rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [rd1, wr1]
  have O1 : Outside base 0 8192 s.mem s1.mem := o1.mono (by decide) (by decide)
  -- The bits of `k` and `S`.
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.vbits_ok (sig := s.gpr .rsi) (ch := s.gpr .rdx) hs1 si1 r91
    (fun q hq => by rw [rr1, Offset.add_add]; exact rsg _ _ (by omega))
    (fun q hq => by rw [rr1]; exact rch _ _ (by omega)) fs fch)
    fun s2 ⟨bs2, bk2, si2, g2, rd2, wr2, o2⟩ => ?_
  rw [VG.Proof.Ed448.X86_64.far_bytes O1 fs, hS] at bs2
  rw [VG.Proof.Ed448.X86_64.far_bytes O1 fch, hK] at bk2
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hn⟩
  have rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rd1, wr1]
  have O2 : Outside base 0 8192 s.mem s2.mem := O1.trans (o2.mono (by decide) (by decide))
  -- The pointers saved, and the check of `S`.
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.vstart_ok (pk := s.gpr .rdi) (sig := s.gpr .rsi) hs2 (by rw [g2 _ (by decide), r81]) (by rw [g2 _ (by decide), r91]) si2
    (fun i hi => by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega))
    (by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega)) fs)
    fun s3 ⟨pk3, sig3, ⟨c0, hc0, b3⟩, g3, rd3, wr3, o3⟩ => ?_
  rw [VG.Proof.Ed448.X86_64.far_bytes O2 fs, hS] at hc0
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hn⟩
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [rd3, wr3, rr2]
  have O3 : Outside base 0 8192 s.mem s3.mem := O2.trans (o3.mono (by decide) (by decide))
  -- `A`, decoded and negated, and the constants.
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.vdecodeA_ok hf hR hs3 pk3 (fun i hi => by rw [rr3]; exact rpk _ _ (by omega))
    (by rw [rr3]; exact rpk _ _ (by omega)) fpk)
    fun s4 ⟨⟨cA, hcA, b4⟩, na4, p4, q4, d4, g4, rd4, wr4, o4⟩ => ?_
  rw [VG.Proof.Ed448.X86_64.far_bytes O3 fpk] at hcA na4
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hn⟩
  have O4 : Outside base 0 8192 s.mem s4.mem := O3.trans ((VG.Proof.Ed448.X86_64.wide o4).mono (by decide) (by decide))
  -- The loop.
  apply WP.seq
  rw [vloop]
  apply WP.seq
  refine WP.mono (show WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 456))]) s4 _ from
    Proof.X448.X86_64.setRbx_ok s4 456 (by decide)) fun s5 ⟨rbx5, g5, m5, rd5, wr5⟩ => ?_
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide)).trans hs4.rdi, wr5 ▸ hs4.wr, hn⟩
  have bits5 : ∀ o : Nat, o + 456 ≤ 8192 → 2048 ≤ o → ∀ t < 456,
      s5.mem (off base (o + t)) = s2.mem (off base (o + t)) := fun o ho1 ho2 t ht => by
    have hofs := VG.Proof.X448.X86_64.ofs_off' base (d := o + t) (by omega)
    rw [m5, o4 _ (Or.inr (by rw [hofs]; omega)) (Or.inr (by rw [hofs]; simp only [BAD]; omega)),
      o3 _ (Or.inr (by rw [hofs]; simp only [KC]; omega))]
  have I5 : VG.Proof.Ed448.X86_64.VInv base S K (pt (E s5.mem base) 6 7 10) s5 456 s5 := by
    refine ⟨hs5, rbx5, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, ?_, rfl, ?_, ?_⟩
    · rw [m5]; exact q4
    · rw [m5]; exact d4
    · rw [Nat.sub_self, m5, p4]; rfl
  refine WP.mono (VG.Proof.Ed448.X86_64.vloop_ok hf (fun t ht => by rw [bits5 BITS (by decide) (by decide) t ht]; exact bs2 t ht)
    (fun t ht => by rw [bits5 KBITS (by decide) (by decide) t ht]; exact bk2 t ht)
    456 s5 (by decide) (by decide) I5) fun s6 I6 => ?_
  -- `R`, decoded.
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.movRsi_ok I6.scr (d := PSIG) (by decide)) fun s7 ⟨si7, g7, m7, rd7, wr7⟩ => ?_
  have hs7 : Scr s7 base := ⟨(g7 _ (by decide)).trans I6.scr.rdi, wr7 ▸ I6.scr.wr, hn⟩
  have hsig7 : s7.gpr .rsi = s.gpr .rsi := by
    rw [si7, I6.mem.word (by decide) (by decide), m5,
      o4.word (Or.inr (by decide)) (Or.inl (by decide)) (by decide), sig3]
  have O7 : Outside base 0 8192 s.mem s7.mem := by
    have h6 := I6.mem
    rw [m5] at h6
    rw [m7]
    exact O4.trans (h6.mono (by decide) (by decide))
  have rr7 : s7.rd ++ s7.wr = s.rd ++ s.wr := by
    rw [rd7, wr7, I6.rd, I6.wr, rd5, wr5, rd4, wr4, rr3]
  have h10 : E s7.mem base 10 = 1 := by
    rw [m7]; exact (congrArg Spec.Ed448.Point.Z I6.q :)
  have h11 : E s7.mem base 11 = Spec.Ed448.d := by rw [m7]; exact I6.d
  apply WP.seq
  refine WP.mono (decode_ok hf hR hs7 hsig7 8 9 (Or.inr ⟨rfl, rfl⟩) h10 h11
    (fun i hi => by rw [rr7]; exact rsg _ _ (by omega)) (by rw [rr7]; exact rsg _ _ (by omega)) fsg)
    fun s8 ⟨⟨cR, hcR, b8⟩, v8, k8, g8, rd8, wr8, o8⟩ => ?_
  rw [VG.Proof.Ed448.X86_64.far_bytes O7 fsg, ← VG.Proof.Ed448.X86_64.bytesAt_take57] at hcR v8
  have hs8 : Scr s8 base := ⟨(g8 _ (by decide)).trans hs7.rdi, wr8 ▸ hs7.wr, hn⟩
  have sv8 : Saved base s.gpr s8.mem := by
    have sv4 := ((sv1.outside o2 (by decide)).outside o3 (by decide)).outside (VG.Proof.Ed448.X86_64.wide o4) (by decide)
    have sv5 : Saved base s.gpr s5.mem := by rw [m5]; exact sv4
    have sv7 : Saved base s.gpr s7.mem := by rw [m7]; exact sv5.outside I6.mem (by decide)
    exact sv7.outside (VG.Proof.Ed448.X86_64.wide o8) (by decide)
  -- `[4]Q` and `[4]R` compared, and the result.
  refine WP.mono (VG.Proof.Ed448.X86_64.vfinish_ok hf hs8 sv8) fun t ⟨at', rt, gt, rdt, wrt, ot⟩ => ?_
  have hBAD : word s8.mem base BAD = c0 ||| cA ||| cR := by
    rw [b8, m7, I6.mem.word (by decide) (by decide), m5, b4, b3]
  have OT : Outside base 0 8192 s.mem t.mem :=
    (O7.trans ((VG.Proof.Ed448.X86_64.wide o8).mono (by decide) (by decide))).trans ((VG.Proof.Ed448.X86_64.wide ot).mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), g8 _ (by decide), g7 _ (by decide), I6.gpr _ (by decide), g5 _ (by decide),
        g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · exact (VG.Proof.Ed448.X86_64.Outside.frame OT).readW (r := ⟨s.gpr .rsp, 8⟩)
      (Region.contains_self _ _) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl; exact hret) (by decide)
  · show t.gpr .rax = _
    rw [at']
    refine if_congr ?_ rfl rfl
    rw [hBAD, or_eq_zero64, or_eq_zero64]
    cases ha : Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      refine ⟨fun h => absurd (hcA.mp h.1.1.2) (by rw [ha]; decide), fun h => absurd h (by decide)⟩
    | some a =>
      cases hR : Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hR)]
        refine ⟨fun h => absurd (hcR.mp h.1.2) (by rw [hR]; decide), fun h => absurd h (by decide)⟩
      | some r =>
        have cA0 : cA = 0 := hcA.mpr (by rw [ha]; rfl)
        have cR0 : cR = 0 := hcR.mpr (by rw [hR]; rfl)
        have hA : pt (E s5.mem base) 6 7 10 = negPoint a := by rw [m5]; exact na4 a ha
        have k80 : ∀ i : Index, i = 0 ∨ i = 1 ∨ i = 2 → E s8.mem base i = E s6.mem base i := by
          rintro i (rfl | rfl | rfl) <;>
            rw [k8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), m7]
        have hQ : pt (E s8.mem base) 0 1 2 = vladder (Spec.Ed448.decodeLE
            ((Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114).drop 57))
            (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57)) (negPoint a) 456 := by
          have := I6.rep
          rw [Nat.sub_zero, hA] at this
          rw [VG.Proof.Ed448.X86_64.bytesAt_drop57, hS, hK, VG.Proof.Ed448.X86_64.pt_congr (k80 0 (Or.inl rfl)) (k80 1 (Or.inr (Or.inl rfl)))
            (k80 2 (Or.inr (Or.inr rfl)))]
          exact this
        have hRR : pt (E s8.mem base) 8 9 10 = r := by
          obtain ⟨vx, vy, vz⟩ := v8 r hR
          show (⟨E s8.mem base 8, E s8.mem base 9, E s8.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [vx, vy, k8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h10, ← vz]
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (VG.Proof.Ed448.X86_64.bytesAt114_len _ _) (bytesAt57_len _ _) ha hR, ← hQ, ← hRR,
          Bool.and_eq_true, decide_eq_true_iff, VG.Proof.Ed448.X86_64.bytesAt_drop57, hS, cA0, cR0, hc0]
        exact ⟨fun h => ⟨h.1.1.1, h.2⟩, fun h => ⟨⟨⟨h.1, rfl⟩, rfl⟩, h.2⟩⟩

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified`. -/
section

/-!
# Ed448 verification's equation on x86-64: `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqOk`, which the registration
files pass in), constant time (by taint tracking: the only branches are on
the loop counters, and every address is an argument plus a constant or a
counter, or a pointer the code stored in the working space before any store
at a counter's offset could change it), and a concrete state satisfying the
signature's contract. The contract lets timing depend on the
inputs; the code's depends on the pointers alone.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

def verifyEquationSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩]

/-- The arguments are public; the working space is writable region 0, at `rcx`. -/
def verifyEquationτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx], flags := false, lens := [8192], bases := [(.rcx, 0, 0)] }

theorem verifyEquation_agree {s₁ s₂ : State} (h₁ : verifyEquationLocal.pre s₁)
    (h₂ : verifyEquationLocal.pre s₂) (hpub : verifyEquationLocal.pub s₁ s₂) :
    X86_64.Taint.Agree VG.Proof.Ed448.X86_64.verifyEquationτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3, p4⟩ := hpub
  have wf : ∀ s, verifyEquationLocal.pre s → X86_64.Taint.Wf VG.Proof.Ed448.X86_64.verifyEquationτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, d⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Ed448.X86_64.verifyEquationτ], by simp [hw], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Ed448.X86_64.verifyEquationτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Ed448.X86_64.verifyEquationτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p4]
  · intro sl h; simp [VG.Proof.Ed448.X86_64.verifyEquationτ] at h
  · intro sl h; simp [VG.Proof.Ed448.X86_64.verifyEquationτ] at h

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) (s : State)
    (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Ed448.X86_64.verifyEquation_correct Proof.X448.X86_64.baseline_ok hR hE hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := verifyEquation) (by lit_decide) he h.1, h.2⟩

/-! ## Constant time, with summaries

The constants stored in the working space are public, and the analysis keeps
them as public slots: some fifty, which every store of a secret and every
comparison of taints goes through. Nothing reads them as an address or a
condition: only the working space at `rdi` (region 0) and the pointers to `A`
and the signature saved there (`PPK`, `PSIG`) need to be public. The
decodings and the loop over the bits are analysed as summaries
(`taint_summary`) from that alone, so their analyses (and what follows them)
carry no constants, and the square root, the same code in both decodings, is
analysed once. -/

/-- What the code needs public after the entry, and the registers `rs` (the
encoding's address `rsi`, for a decoding). -/
def verifySumτ (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rdi]), flags := false, lens := [8192], bases := [(.rdi, 0, 0)],
    slots := [(0, PPK, 8), (0, PSIG, 8)] }

taint_summary verifyRootSum : taintS (VG.Proof.Ed448.X86_64.verifySumτ []) (root Impl.X448.X86_64.baseline 12)

taint_summary verifyDecodeASum : taintS (VG.Proof.Ed448.X86_64.verifySumτ [.rsi]) (decode Impl.X448.X86_64.baseline 6 7)
  using verifyRootSum
taint_summary verifyDecodeRSum : taintS (VG.Proof.Ed448.X86_64.verifySumτ [.rsi]) (decode Impl.X448.X86_64.baseline 8 9)
  using verifyRootSum
taint_summary verifyLoopSum : taintS (VG.Proof.Ed448.X86_64.verifySumτ []) (vloop Impl.X448.X86_64.baseline)

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check VG.Proof.Ed448.X86_64.verifyEquationτ verifyEquation h).isSome = true := by
    taint_decide_sum [verifyDecodeASum, verifyDecodeRSum, verifyLoopSum]
  exact VG.Taint.constantTime (A := taintS) VG.Proof.Ed448.X86_64.verifyEquationτ
    (fun _ _ h₁ h₂ hp => VG.Proof.Ed448.X86_64.verifyEquation_agree h₁ h₂ hp) hc

theorem verifyEquation_implies :
    verifyEquationLocal.Implies (Spec.Ed448.verifyEquationContract X86_64.abi) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, VG.Proof.Ed448.X86_64.verifyEquationLocal]
  post s t _ h := by
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs]
    have h' : t.gpr .rax = _ := h
    rw [h']
    generalize Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨sp, -, pk, sig, ch, base⟩ := h
    exact ⟨sp, pk, sig, ch, base⟩
  sat := by
    sig_implies_sat [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs] [verifyEquationSat] using VG.Proof.Ed448.X86_64.verifyEquationSat

theorem verifyEquation_verified (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) :
    Verified X86_64.target verifyEquation (Spec.Ed448.verifyEquationContract X86_64.abi) :=
  Verified.of_correct (VG.Proof.Ed448.X86_64.verifyEquation_ok hR hE) VG.Proof.Ed448.X86_64.verifyEquation_ct VG.Proof.Ed448.X86_64.verifyEquation_implies

end VG.Proof.Ed448.X86_64

end
