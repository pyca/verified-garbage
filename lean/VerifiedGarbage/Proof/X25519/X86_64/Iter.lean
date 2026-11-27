module

public import VerifiedGarbage.Proof.X25519.X86_64.Env
public import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Bits
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X25519 on x86-64: the ladder

What a ladder needs (`LPre`) and leaves (`LPost`), for `vg_x25519`'s and the
one with AVX512_IFMA (`Ifma/`), and the proof of `ladder`. A sequence of field
operations is run on the slots' values and on the list of the slots that are
known to be at most `2p` (`Run`); an iteration then takes the ladder's state
from the bits down to `t + 1` to the bits down to `t`, whichever way the bits
`t` and `t + 1` are (`iter_x2` … `iter_z3`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519
open VG.Spec.X25519 (Fe)

theorem cswap_fst (sw : Nat) (a b : Fe) :
    (Spec.X25519.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  by_cases h : sw = 1 <;> simp only [Spec.X25519.cswap, h, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]

theorem cswap_snd (sw : Nat) (a b : Fe) :
    (Spec.X25519.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  by_cases h : sw = 1 <;> simp only [Spec.X25519.cswap, h, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]

/-! ## The contract of a ladder -/

/-- What a ladder starts from: the scalar `k`'s bits, RFC 7748's initial
variables for `x₁ = u` with the `z` coordinates at most `2p`, `swap = 0`, and
that clamping cleared `k`'s low bits. -/
structure LPre (base : Addr) (k : Nat) (u : Fe) (s : State) : Prop where
  scr : Scr s base
  bits : ∀ t < 255, s.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)
  x1 : E s.mem base 2 = u
  x2 : E s.mem base 3 = 1
  z2 : E s.mem base 4 = 0
  x3 : E s.mem base 5 = u
  z3 : E s.mem base 6 = 1
  swap : word s.mem base SWAP = 0
  z2b : fe s.mem base 128 ≤ 2 * Spec.X25519.P
  z3b : fe s.mem base 192 ≤ 2 * Spec.X25519.P
  low : bit k 0 = 0 ∧ bit k 1 = 0 ∧ bit k 2 = 0

/-- What a ladder leaves: the point that `lastSwap` chooses is the one RFC
7748's last swap leaves. -/
structure LPost (base : Addr) (k : Nat) (u : Fe) (s₀ s : State) : Prop where
  scr : Scr s base
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 2152 s₀.mem s.mem
  res : ∃ sw, sw < 2 ∧ word s.mem base SWAP = BitVec.ofNat 64 sw ∧
    (Spec.X25519.cswap sw (E s.mem base 3) (E s.mem base 5)).1 =
      (Spec.X25519.cswap (ladderAfter k u 0).swap (ladderAfter k u 0).x2 (ladderAfter k u 0).x3).1 ∧
    (Spec.X25519.cswap sw (E s.mem base 4) (E s.mem base 6)).1 =
      (Spec.X25519.cswap (ladderAfter k u 0).swap (ladderAfter k u 0).z2 (ladderAfter k u 0).z3).1

/-- The ladder's whole final state is enough. -/
theorem LPost.of {base : Addr} {k : Nat} {u : Fe} {s₀ s : State} (scr : Scr s base)
    (gpr : ∀ r, r ∉ clob → r ≠ .rbx → s.gpr r = s₀.gpr r) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr)
    (mem : Outside base 64 2152 s₀.mem s.mem) (x2 : E s.mem base 3 = (ladderAfter k u 0).x2)
    (z2 : E s.mem base 4 = (ladderAfter k u 0).z2) (x3 : E s.mem base 5 = (ladderAfter k u 0).x3)
    (z3 : E s.mem base 6 = (ladderAfter k u 0).z3)
    (sw : word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u 0).swap) : LPost base k u s₀ s :=
  ⟨scr, gpr, rd, wr, mem, _, Nat.lt_succ_of_le (ladderAfter_swap_le k u (by decide)), sw,
    by rw [x2, x3], by rw [z2, z3]⟩

/-! ## The scalar's bits -/

theorem ea_bits (s : State) (d : Nat) {base : Addr} {n : Nat} (hr : s.gpr .rdi = base)
    (hb : s.gpr .rbx = BitVec.ofNat 64 n) :
    s.ea { base := .rdi, index := some .rbx, disp := ((BITS + d : Nat) : Int) } =
      off base (BITS + (d + n)) := by
  simp only [State.ea, hr, hb, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, off, BitVec.add_assoc,
    ← BitVec.ofNat_add]
  congr 2
  omega_arith

theorem dec_eq (n : Nat) :
    BitVec.ofNat 64 (n + 1) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 n := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add,
    BitVec.add_sub_cancel]

theorem ofNat_beq_zero {n : Nat} (hn : n < 255) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  revert n; decide +kernel

/-- The start of the iteration with AVX512_IFMA: `swap`'s mask, by the bit `t`. -/
def stepPre : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)]

theorem swapMask_eq : ∀ kt < 2, ∀ sw < 2, BitVec.setWidth 64 (0 : BitVec 32) -
    (BitVec.ofNat 64 sw ^^^ (BitVec.ofNat 8 kt).setWidth 64) = mask (decide (sw ^^^ kt = 1)) := by
  decide

theorem byte64 : ∀ kt < 2, (BitVec.ofNat 8 kt).setWidth 64 = BitVec.ofNat 64 kt := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 255)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hw : word s.mem base SWAP = BitVec.ofNat 64 sw0) :
    WP isa (.block stepPre) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rcx = mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [Reg.rbx, .rax, .rdx, .rcx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 64 kt) ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi := by
  have r1 : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega_using [ht])⟩
  have r2 : InRegions (s.rd ++ s.wr) (off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by decide)⟩
  have w2 : InRegions s.wr (off base SWAP) 8 := ⟨_, hs.wr, contains_sc (by decide)⟩
  have ea : ∀ s' : State, s'.gpr .rdi = base → s'.gpr .rbx = BitVec.ofNat 64 t →
      s'.ea { base := .rdi, index := some .rbx, disp := (BITS : Nat) } = off base (BITS + t) :=
    fun s' h1 h2 => by rw [← Nat.zero_add t]; exact ea_bits s' 0 h1 (by rw [h2])
  apply WP.of_runBlock
  simp (disch := (simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hs.rdi, hb, dec_eq, ite_true, ite_false, reduceCtorEq])) only
    [stepPre, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    ea, State.load8, State.load64, State.store64, ea_sc, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.mem_arithFlags, hs.rdi, hb, dec_eq, r1, r2, w2, hbit, hw, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, swapMask_eq kt hk sw0 hsw, fun r hr => ?_, trivial, trivial, ?_, rfl, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  · rw [byte64 kt hk]

theorem xorBits : ∀ a < 2, ∀ b < 2, ((BitVec.ofNat 8 a).setWidth 64 ^^^ (BitVec.ofNat 8 b).setWidth 64 ==
    (0 : BitVec 64)) = decide (a = b) := by decide

theorem bitsDiffer_ok {s : State} {base : Addr} (hs : Scr s base) {d n : Nat}
    (hn : d + n < 255) (hb : s.gpr .rbx = BitVec.ofNat 64 n) {a b : Nat} (ha : a < 2) (hb' : b < 2)
    (h0 : s.mem (off base (BITS + (d + n))) = BitVec.ofNat 8 a)
    (h1 : s.mem (off base (BITS + (d + n + 1))) = BitVec.ofNat 8 b) :
    WP isa (.block (bitsDiffer d)) s fun s' => s'.zf = some (decide (a = b)) ∧ Keeps [.rax, .rcx] s s' := by
  have r0 : InRegions (s.rd ++ s.wr) (off base (BITS + (d + n))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega_using [hn])⟩
  have r1 : InRegions (s.rd ++ s.wr) (off base (BITS + (d + n + 1))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega_using [hn])⟩
  have e1 : ∀ s' : State, s'.gpr .rdi = base → s'.gpr .rbx = BitVec.ofNat 64 n →
      s'.ea { base := .rdi, index := some .rbx, disp := ((BITS + d + 1 : Nat) : Int) } =
        off base (BITS + (d + n + 1)) := fun s' h1 h2 => by
    rw [show d + n + 1 = (d + 1) + n by omega_arith]; exact ea_bits s' (d + 1) h1 h2
  have e0 : ∀ s' : State, s'.gpr .rdi = base → s'.gpr .rbx = BitVec.ofNat 64 n →
      s'.ea { base := .rdi, index := some .rbx, disp := ((BITS + d : Nat) : Int) } =
        off base (BITS + (d + n)) := fun s' h1 h2 => ea_bits s' d h1 h2
  apply WP.of_runBlock
  simp (disch := (simp only [RegUpd.gpr_setReg, hs.rdi, hb, ite_false, reduceCtorEq])) only
    [bitsDiffer, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, e0, e1,
    State.load8, RegUpd.gpr_setReg, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, r0, r1, h0, h1, ite_true, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨xorBits a ha b hb', fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-! ## The selection -/

theorem choose1_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : x + 8 ≤ 4096)
    (hy : y + 8 ≤ 4096) (a : Reg) (ha : a ≠ .rdi) {z : Bool} (hz : s.zf = some z) :
    WP isa (.block ([.mov a (.mem (sc x)), .cmov .ne a (.mem (sc y))] : List Instr)) s fun s' =>
      s'.gpr a = (if z then word s.mem base x else word s.mem base y) ∧ s'.zf = some z ∧
      Keeps [a] s s' := by
  have hr : ∀ r, r ∉ [a] → r ≠ a := fun r hr => by simpa only [List.mem_singleton] using hr
  apply WP.of_runBlock
  cases z <;>
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execCmov, eval, State.load64,
      ea_sc, RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      hs.rdi, hz, ld_sc hs hx, ld_sc hs hy, ha.symm, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, fun r h => ?_, rfl, rfl, rfl⟩
    simp only [RegUpd.gpr_setReg, hr r h, ite_false]

theorem choose_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : Slot x) (hy : Slot y)
    {a b c d : Reg} (hd : [.rdi, a, b, c, d].Nodup) {z : Bool} (hz : s.zf = some z) :
    WP isa (.block (choose x y a b c d)) s fun s' =>
      val4 (s'.gpr a) (s'.gpr b) (s'.gpr c) (s'.gpr d) = (if z then fe s.mem base x else fe s.mem base y) ∧
      s'.zf = some z ∧ Keeps [a, b, c, d] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨na, nb, nc, nd⟩, ⟨ab, ac, ad⟩, ⟨bc, bd⟩, cd, -⟩ := hd
  rw [show choose x y a b c d = ([.mov a (.mem (sc x)), .cmov .ne a (.mem (sc y))] : List Instr) ++
    (([.mov b (.mem (sc (x + 8))), .cmov .ne b (.mem (sc (y + 8)))] : List Instr) ++
    (([.mov c (.mem (sc (x + 16))), .cmov .ne c (.mem (sc (y + 16)))] : List Instr) ++
    ([.mov d (.mem (sc (x + 24))), .cmov .ne d (.mem (sc (y + 24)))] : List Instr))) from rfl,
    WP.block_append_iff]
  refine WP.mono (choose1_ok hs (by omega) (by omega) a (Ne.symm na) hz) fun s₁ ⟨v₁, z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by simpa only [List.mem_singleton] using na)
  rw [WP.block_append_iff]
  refine WP.mono (choose1_ok hs₁ (by omega) (by omega) b (Ne.symm nb) z₁) fun s₂ ⟨v₂, z₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by simpa only [List.mem_singleton] using nb)
  rw [WP.block_append_iff]
  refine WP.mono (choose1_ok hs₂ (by omega) (by omega) c (Ne.symm nc) z₂) fun s₃ ⟨v₃, z₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by simpa only [List.mem_singleton] using nc)
  refine WP.mono (choose1_ok hs₃ (by omega) (by omega) d (Ne.symm nd) z₃) fun s₄ ⟨v₄, z₄, k₄⟩ => ?_
  have ne : ∀ {r q : Reg}, r ≠ q → r ∉ [q] := fun h => by simpa only [List.mem_singleton] using h
  refine ⟨?_, z₄, ?_⟩
  · rw [k₄.1 a (ne ad), k₃.1 a (ne ac), k₂.1 a (ne ab), k₄.1 b (ne bd), k₃.1 b (ne bc), k₄.1 c (ne cd),
      v₁, v₂, v₃, v₄, k₃.2.1, k₂.2.1, k₁.2.1]
    cases z <;> rfl
  · exact (k₁.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false]; grind)).trans
      ((k₂.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false]; grind)).trans
      ((k₃.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false]; grind)).trans
      (k₄.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false]; grind))))

/-- Two selections, by the same flag. -/
def opSel (o x x' p y y' : Fin 128) (z : Bool) (e : Env) : Env :=
  Fun.update (Fun.update e o (if z then e x else e x')) p (if z then e y else e y')

theorem choose2E {s : State} {base : Addr} (hs : Scr s base) (o x x' p y y' : Fin 128) (ho : LSlot o)
    (hp : LSlot p) (hop : o ≠ p) {z : Bool} (hz : s.zf = some z) :
    WP isa (.block (choose2 (32 * o.val) (32 * x.val) (32 * x'.val) (32 * p.val) (32 * y.val) (32 * y'.val))) s
      fun s' => Keep base s s' ∧ E s'.mem base = opSel o x x' p y y' z (E s.mem base) ∧
        (∀ i : Fin 128, i ≠ o → i ≠ p → fe s'.mem base (32 * i.val) = fe s.mem base (32 * i.val)) ∧
        fe s'.mem base (32 * p.val) =
          (if z then fe s.mem base (32 * y.val) else fe s.mem base (32 * y'.val)) := by
  have hne : o.val ≠ p.val := fun h => hop (Fin.ext h)
  simp only [choose2, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (choose_ok hs (by omega) (by omega) (by decide) hz) fun s₁ ⟨v₁, z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (choose_ok hs₁ (by omega) (by omega) (by decide) z₁) fun s₂ ⟨v₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok hs₂ (by omega)) fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_
  have hs₃ : Scr s₃ base := ⟨(g₃ _).trans hs₂.rdi, wr₃ ▸ hs₂.wr, hs.nowrap⟩
  refine WP.mono (stores_ok hs₃ (by omega) _ _ _ _) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_
  have o₃ : Outside base (32 * o.val) 32 s₂.mem s₃.mem := by
    rw [m₃]; exact st4_outside _ _ (by omega) _ _ _ _
  have o₄ : Outside base (32 * p.val) 32 s₃.mem s₄.mem := by
    rw [m₄]; exact st4_outside _ _ (by omega) _ _ _ _
  have m₂ : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
  rw [m₂] at o₃
  have f₃ : fe s₃.mem base (32 * o.val) =
      (if z then fe s.mem base (32 * x.val) else fe s.mem base (32 * x'.val)) := by
    rw [m₃, fe_st4 _ _ (by omega), ← v₁, k₂.1 .r8 (by decide), k₂.1 .r9 (by decide),
      k₂.1 .r10 (by decide), k₂.1 .r11 (by decide)]
  have f₄ : fe s₄.mem base (32 * p.val) =
      (if z then fe s.mem base (32 * y.val) else fe s.mem base (32 * y'.val)) := by
    rw [m₄, fe_st4 _ _ (by omega), g₃, g₃, g₃, g₃, v₂, k₁.2.1]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, (o₃.mono (by omega) (by omega)).trans
    (o₄.mono (by omega) (by omega))⟩, ?_, fun i hi hi' => ?_, f₄⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄, g₃, k₂.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; grind),
      k₁.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; grind)]
  · rw [rd₄, rd₃, k₂.2.2.1, k₁.2.2.1]
  · rw [wr₄, wr₃, k₂.2.2.2, k₁.2.2.2]
  · rw [E_update o₄, E_update o₃, opSel]
    simp only [F, f₃, f₄]
    cases z <;> rfl
  · have a : i.val ≠ o.val := fun h => hi (Fin.ext h)
    have b : i.val ≠ p.val := fun h => hi' (Fin.ext h)
    rw [o₄.fe (by omega) (by omega), o₃.fe (by omega) (by omega)]

/-! ## Sequences of operations -/

/-- The working space after some operations from `s₀`: the slots' values are
`e`, and those of `l` are at most `2p`. -/
structure Run (base : Addr) (s₀ s : State) (e : Env) (l : List (Fin 128)) : Prop where
  scr : Scr s base
  keep : Keep base s₀ s
  env : E s.mem base = e
  le : ∀ i ∈ l, fe s.mem base (32 * i.val) ≤ 2 * Spec.X25519.P

variable {base : Addr} {s₀ s : State} {e : Env} {l : List (Fin 128)} {fld : Field}

/-- The slots of `l` but `o`. -/
abbrev but (o : Fin 128) (l : List (Fin 128)) : List (Fin 128) := l.filter (· ≠ o)

theorem le_but (o : Fin 128) {m m' : Mem} (h : Outside base (32 * o.val) 32 m m')
    (hl : ∀ i ∈ l, fe m base (32 * i.val) ≤ 2 * Spec.X25519.P) :
    ∀ i ∈ but o l, fe m' base (32 * i.val) ≤ 2 * Spec.X25519.P := fun i hi => by
  obtain ⟨hi, hne⟩ := List.mem_filter.1 hi
  have : i.val ≠ o.val := fun h => of_decide_eq_true hne (Fin.ext h)
  rw [h.fe (by omega_arith) (by omega_arith)]; exact hl i hi

/-- A product. -/
theorem Run.mul (hf : FieldOk fld) (h : Run base s₀ s e l) (o a b : Fin 128) (ho : LSlot o)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Run base s₀ s' (opMul o a b e) (o :: but o l) → WP isa (.block rest) s' Q) :
    WP isa (.block (fld.mul (32 * o.val) (32 * a.val) (32 * b.val) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (mulEB hf h.scr o a b ho) fun s' ⟨K, e', m, hb⟩ => k s' ⟨K.scr h.scr, h.keep.trans K,
    by rw [e', h.env], fun i hi => ?_⟩
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hb
  · exact le_but o m h.le i hi

/-- A square. -/
theorem Run.sqr (hf : FieldOk fld) (h : Run base s₀ s e l) (o a : Fin 128) (ho : LSlot o)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Run base s₀ s' (opMul o a a e) (o :: but o l) → WP isa (.block rest) s' Q) :
    WP isa (.block (fld.sqr (32 * o.val) (32 * a.val) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (sqrEB hf h.scr o a ho) fun s' ⟨K, e', m, hb⟩ => k s' ⟨K.scr h.scr, h.keep.trans K,
    by rw [e', h.env], fun i hi => ?_⟩
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hb
  · exact le_but o m h.le i hi

/-- A sum, of which the second operand is at most `2p`. -/
theorem Run.add (h : Run base s₀ s e l) (o a b : Fin 128) (ho : LSlot o) (hb : b ∈ l)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Run base s₀ s' (opAdd o a b e) (but o l) → WP isa (.block rest) s' Q) :
    WP isa (.block (addCmov (32 * o.val) (32 * a.val) (32 * b.val) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  exact WP.mono (addCmovE h.scr o a b ho (.inr (h.le b hb))) fun s' ⟨K, e', m⟩ => k s' ⟨K.scr h.scr,
    h.keep.trans K, by rw [e', h.env], le_but o m h.le⟩

/-- A difference, of which the second operand is at most `2p`. -/
theorem Run.sub (h : Run base s₀ s e l) (o a b : Fin 128) (ho : LSlot o) (hb : b ∈ l)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Run base s₀ s' (opSub o a b e) (but o l) → WP isa (.block rest) s' Q) :
    WP isa (.block (subCmov (32 * o.val) (32 * a.val) (32 * b.val) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  exact WP.mono (subCmovE h.scr o a b ho (h.le b hb)) fun s' ⟨K, e', m⟩ => k s' ⟨K.scr h.scr,
    h.keep.trans K, by rw [e', h.env], le_but o m h.le⟩

/-- A multiply-add by `a24`. -/
theorem Run.a24 (hf : FieldOk fld) (h : Run base s₀ s e l) (o b a : Fin 128) (ho : LSlot o)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Run base s₀ s' (opA24Add o b a e) (but o l) → WP isa (.block rest) s' Q) :
    WP isa (.block (fld.a24add (32 * o.val) (32 * b.val) (32 * a.val) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  exact WP.mono (a24AddEB hf h.scr o b a ho) fun s' ⟨K, e', m⟩ => k s' ⟨K.scr h.scr,
    h.keep.trans K, by rw [e', h.env], le_but o m h.le⟩

/-! ## An iteration -/

/-- An iteration up to the selection. -/
def iter1 : List Instr :=
  subCmov (32 * 10) (32 * 5) (32 * 6) ++ (addCmov (32 * 7) (32 * 3) (32 * 4) ++
    (addCmov (32 * 9) (32 * 5) (32 * 6) ++ (subCmov (32 * 8) (32 * 3) (32 * 4) ++ [])))

/-- An iteration after the selection. -/
def iter2 (fld : Field) : List Instr :=
  fld.mul (32 * 10) (32 * 10) (32 * 7) ++ (fld.sqr (32 * 12) (32 * 12) ++ (fld.sqr (32 * 11) (32 * 11) ++
    (subCmov (32 * 7) (32 * 11) (32 * 12) ++ (fld.mul (32 * 9) (32 * 9) (32 * 8) ++
    (fld.a24add (32 * 8) (32 * 11) (32 * 7) ++ (subCmov (32 * 6) (32 * 10) (32 * 9) ++
    (fld.mul (32 * 3) (32 * 11) (32 * 12) ++ (addCmov (32 * 10) (32 * 10) (32 * 9) ++
    (fld.sqr (32 * 6) (32 * 6) ++ (fld.mul (32 * 4) (32 * 7) (32 * 8) ++ (fld.sqr (32 * 5) (32 * 10) ++
    (fld.mul (32 * 6) (32 * 2) (32 * 6) ++ []))))))))))))

theorem iter_eq (fld : Field) : iter fld = iter1 ++ (bitsDiffer 2 ++
    (choose2 (32 * 11) (32 * 7) (32 * 9) (32 * 12) (32 * 8) (32 * 10) ++ iter2 fld)) := by
  simp only [iter, iter1, iter2, List.append_assoc, List.append_nil]
  rfl

def env1 (e : Env) : Env := opSub 8 3 4 (opAdd 9 5 6 (opAdd 7 3 4 (opSub 10 5 6 e)))

def env2 (e : Env) : Env :=
  opMul 6 2 6 (opMul 5 10 10 (opMul 4 7 8 (opMul 6 6 6 (opAdd 10 10 9 (opMul 3 11 12
    (opSub 6 10 9 (opA24Add 8 11 7 (opMul 9 9 8 (opSub 7 11 12 (opMul 11 11 11 (opMul 12 12 12
    (opMul 10 10 7 e))))))))))))

/-- The slots after an iteration, when the bits are (`z`) or are not the same. -/
def envIter (z : Bool) (e : Env) : Env := env2 (opSel 11 7 9 12 8 10 z (env1 e))

theorem sq_neg (x y : Fe) : (x - y) * (x - y) = (y - x) * (y - x) := by grind

theorem mul_add_comm (a b c d : Fe) : d * a + c * b = b * c + a * d := by grind

theorem envIter_x2 (z : Bool) (e : Env) : envIter z e 3 =
    let a := if z then e 3 + e 4 else e 5 + e 6
    let b := if z then e 3 - e 4 else e 5 - e 6
    a * a * (b * b) := by
  simp only [envIter, env1, env2, opSel, opMul, opAdd, opSub, opA24Add,
    Fun.update_apply, Fin.reduceEq, ↓reduceIte]

theorem envIter_z2 (z : Bool) (e : Env) : envIter z e 4 =
    let a := if z then e 3 + e 4 else e 5 + e 6
    let b := if z then e 3 - e 4 else e 5 - e 6
    (a * a - b * b) * (a * a + Spec.X25519.a24 * (a * a - b * b)) := by
  simp only [envIter, env1, env2, opSel, opMul, opAdd, opSub, opA24Add,
    Fun.update_apply, Fin.reduceEq, ↓reduceIte]

theorem envIter_x3 (z : Bool) (e : Env) : envIter z e 5 =
    ((e 5 - e 6) * (e 3 + e 4) + (e 5 + e 6) * (e 3 - e 4)) *
      ((e 5 - e 6) * (e 3 + e 4) + (e 5 + e 6) * (e 3 - e 4)) := by
  simp only [envIter, env1, env2, opSel, opMul, opAdd, opSub, opA24Add,
    Fun.update_apply, Fin.reduceEq, ↓reduceIte]

theorem envIter_z3 (z : Bool) (e : Env) : envIter z e 6 =
    e 2 * (((e 5 - e 6) * (e 3 + e 4) - (e 5 + e 6) * (e 3 - e 4)) *
      ((e 5 - e 6) * (e 3 + e 4) - (e 5 + e 6) * (e 3 - e 4))) := by
  simp only [envIter, env1, env2, opSel, opMul, opAdd, opSub, opA24Add,
    Fun.update_apply, Fin.reduceEq, ↓reduceIte]

theorem envIter_x1 (z : Bool) (e : Env) : envIter z e 2 = e 2 := by
  simp only [envIter, env1, env2, opSel, opMul, opAdd, opSub, opA24Add,
    Fun.update_apply, Fin.reduceEq, ↓reduceIte]

/-- The ladder's variables are in their slots. -/
structure Holds (u : Fe) (e : Env) (st : Spec.X25519.Ladder) : Prop where
  x1 : e 2 = u
  x2 : e 3 = st.x2
  z2 : e 4 = st.z2
  x3 : e 5 = st.x3
  z3 : e 6 = st.z3

theorem xor_one : ∀ a < 2, ∀ b < 2, decide (a ^^^ b = 1) = !decide (b = a) := by decide

/-- An iteration does RFC 7748's: the swap by which its formulas start only
changes the sign of the difference that is squared. -/
theorem Holds.iter {k t : Nat} {u : Fe} {e : Env} {st : Spec.X25519.Ladder} (h : Holds u e st)
    (hsw : st.swap < 2) :
    Holds u (envIter (decide (bit k t = st.swap)) e) (Spec.X25519.ladderStep k u st t) := by
  have hx := xor_one st.swap hsw (bit k t) (Nat.lt_succ_of_le (bit_le k t))
  rw [ladderStep_eq]
  refine ⟨(envIter_x1 _ _).trans h.x1, ?_, ?_, ?_, ?_⟩
  · rw [envIter_x2]; simp only [cswap_fst, hx, h.x2, h.z2, h.x3, h.z3]
    cases decide (bit k t = st.swap) <;> rfl
  · rw [envIter_z2]; simp only [cswap_fst, hx, h.x2, h.z2, h.x3, h.z3]
    cases decide (bit k t = st.swap) <;> rfl
  · rw [envIter_x3]; simp only [cswap_fst, cswap_snd, hx, h.x2, h.z2, h.x3, h.z3]
    cases decide (bit k t = st.swap)
    · simp only [Bool.not_false, ite_true]; rw [mul_add_comm]
    · rfl
  · rw [envIter_z3]; simp only [cswap_fst, cswap_snd, hx, h.x1, h.x2, h.z2, h.x3, h.z3]
    cases decide (bit k t = st.swap)
    · simp only [Bool.not_false, ite_true]
      rw [sq_neg, Fin.mul_comm (st.x3 - st.z3), Fin.mul_comm (st.x3 + st.z3)]
    · rfl

theorem iter1_ok (h : Run base s₀ s e [4, 6]) :
    WP isa (.block iter1) s fun s' => Run base s₀ s' (env1 e) [4, 6] :=
  h.sub 10 5 6 (by decide) (by decide) fun _ h =>
  h.add 7 3 4 (by decide) (by decide) fun _ h =>
  h.add 9 5 6 (by decide) (by decide) fun _ h =>
  h.sub 8 3 4 (by decide) (by decide) fun _ h => WP.of_runBlock ⟨_, rfl, h⟩

theorem iter2_ok (hf : FieldOk fld) (h : Run base s₀ s e []) :
    WP isa (.block (iter2 fld)) s fun s' => Run base s₀ s' (env2 e) [4, 6] :=
  h.mul hf 10 10 7 (by decide) fun _ h =>
  h.sqr hf 12 12 (by decide) fun _ h =>
  h.sqr hf 11 11 (by decide) fun _ h =>
  h.sub 7 11 12 (by decide) (by decide) fun _ h =>
  h.mul hf 9 9 8 (by decide) fun _ h =>
  h.a24 hf 8 11 7 (by decide) fun _ h =>
  h.sub 6 10 9 (by decide) (by decide) fun _ h =>
  h.mul hf 3 11 12 (by decide) fun _ h =>
  h.add 10 10 9 (by decide) (by decide) fun _ h =>
  h.sqr hf 6 6 (by decide) fun _ h =>
  h.mul hf 4 7 8 (by decide) fun _ h =>
  h.sqr hf 5 10 (by decide) fun _ h =>
  h.mul hf 6 2 6 (by decide) fun _ h => WP.of_runBlock ⟨_, rfl, h.scr, h.keep, h.env, fun i hi =>
    h.le i (by revert i; decide)⟩

/-- A byte of `BITS` after operations on the slots. -/
theorem Keep.byte {s s' : State} (h : Keep base s s') {d : Nat} (hd : 640 ≤ d) (hd' : d < 4096) :
    s'.mem (off base d) = s.mem (off base d) :=
  h.mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith)

theorem Keeps.keep {rs : List Reg} {s s' : State} (h : Keeps rs s s') (hr : ∀ r ∈ rs, r ∈ clob) :
    Keep base s s' :=
  ⟨fun r h' => h.1 r fun h'' => h' (hr r h''), h.2.2.1, h.2.2.2, by rw [h.2.1]; exact Outside.refl _ _ _ _⟩

theorem iter_ok (hf : FieldOk fld) (h : Run base s₀ s e [4, 6]) {n : Nat} (hn : n < 253)
    (hb : s.gpr .rbx = BitVec.ofNat 64 n) {a b : Nat} (ha : a < 2) (hb' : b < 2)
    (h0 : s.mem (off base (BITS + (2 + n))) = BitVec.ofNat 8 a)
    (h1 : s.mem (off base (BITS + (2 + n + 1))) = BitVec.ofNat 8 b) :
    WP isa (.block (iter fld)) s fun s' => Run base s₀ s' (envIter (decide (a = b)) e) [4, 6] := by
  rw [iter_eq, WP.block_append_iff]
  refine WP.mono (iter1_ok ⟨h.scr, Keep.refl base s, h.env, h.le⟩) fun s₁ r₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bitsDiffer_ok r₁.scr (d := 2) (n := n) (by omega_using [hn])
    ((r₁.keep.gpr _ (by decide)).trans hb) ha hb'
    ((r₁.keep.byte (by simp only [BITS]; omega_using []) (by simp only [BITS]; omega_using [hn])).trans h0)
    ((r₁.keep.byte (by simp only [BITS]; omega_using []) (by simp only [BITS]; omega_using [hn])).trans h1))
    fun s₂ ⟨z₂, k₂⟩ => ?_
  have K₂ : Keep base s₁ s₂ := Keeps.keep k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (choose2E (K₂.scr r₁.scr) 11 7 9 12 8 10 (by decide) (by decide) (by decide) z₂)
    fun s₃ ⟨K₃, e₃, _, _⟩ => ?_
  refine iter2_ok hf ⟨K₃.scr (K₂.scr r₁.scr), (h.keep.trans r₁.keep).trans (K₂.trans K₃), ?_,
    fun i hi => absurd hi List.not_mem_nil⟩
  rw [e₃, k₂.2.1, r₁.env]

/-! ## The loop -/

theorem countDown_ok (s : State) {n : Nat} (hn : n < 255) (hb : s.gpr .rbx = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block countDown) s fun s' => s'.gpr .rbx = BitVec.ofNat 64 n ∧
      s'.zf = some (decide (n = 0)) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [countDown, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, hb, dec_eq,
    RegUpd.gpr_setReg_self, RegUpd.zf_setReg, RegUpd.zf_arithFlags, ofNat_beq_zero hn, Option.bind_some,
    Option.some.injEq, exists_eq_left', true_and]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- What both loops keep of the state before them. -/
structure Rest (base : Addr) (s₀ s : State) : Prop where
  scr : Scr s base
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 576 s₀.mem s.mem

theorem Rest.keep {s₀ s s' : State} (h : Rest base s₀ s) (k : Keep base s s') : Rest base s₀ s' :=
  ⟨k.scr h.scr, fun r hr hb => (k.gpr r hr).trans (h.gpr r hr hb), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem Rest.count {s₀ s s' : State} (h : Rest base s₀ s) (k : Keeps [.rbx] s s') : Rest base s₀ s' :=
  ⟨h.scr.of_keeps k (by decide), fun r hr hb => (k.1 r (by simpa only [List.mem_singleton] using hb)).trans
    (h.gpr r hr hb), k.2.2.1.trans h.rd, k.2.2.2.trans h.wr, by rw [k.2.1]; exact h.mem⟩

/-- The byte `t` of `BITS`, with bit 255 clear. -/
def kbit (k t : Nat) : Nat := if t = 255 then 0 else bit k t

theorem kbit_lt (k t : Nat) : kbit k t < 2 := by
  unfold kbit; split
  · decide
  · exact Nat.lt_succ_of_le (bit_le k t)

theorem swap_kbit (k : Nat) (u : Fe) {t : Nat} (ht : t ≤ 255) : (ladderAfter k u t).swap = kbit k t := by
  rcases Nat.lt_or_ge t 255 with h | h
  · rw [ladderAfter_step k u h, kbit, ite_eq_right (by omega_using [h])]; rfl
  · rw [show t = 255 by omega_using [ht, h]]; rfl

/-- The loop's invariant, with the counter `n`. -/
structure Inv (base : Addr) (k : Nat) (u : Fe) (s₀ s : State) (n : Nat) : Prop extends Rest base s₀ s where
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  holds : Holds u (E s.mem base) (ladderAfter k u (n + 3))
  le : ∀ i ∈ ([4, 6] : List (Fin 128)), fe s.mem base (32 * i.val) ≤ 2 * Spec.X25519.P

theorem Rest.byte {s₀ s : State} (h : Rest base s₀ s) {d : Nat} (hd : 640 ≤ d) (hd' : d < 4096) :
    s.mem (off base d) = s₀.mem (off base d) :=
  h.mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith)

theorem loopBody_ok (hf : FieldOk fld) {k : Nat} {u : Fe} {n : Nat} (hn : n < 252)
    (hbits : ∀ t < 256, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (kbit k t))
    (h : Inv base k u s₀ s (n + 1)) :
    WP isa (.block (iter fld ++ countDown)) s fun s' =>
      Inv base k u s₀ s' n ∧ s'.zf = some (decide (n = 0)) := by
  have B : ∀ t < 256, s.mem (off base (BITS + t)) = BitVec.ofNat 8 (kbit k t) := fun t ht =>
    (h.toRest.byte (by simp only [BITS]; omega_using []) (by simp only [BITS]; omega_using [ht])).trans (hbits t ht)
  rw [WP.block_append_iff]
  refine WP.mono (iter_ok hf (n := n + 1) ⟨h.scr, Keep.refl base s, rfl, h.le⟩ (by omega_using [hn]) h.rbx
    (kbit_lt k _) (kbit_lt k _) (B (2 + (n + 1)) (by omega_using [hn])) (B (2 + (n + 1) + 1) (by omega_using [hn]))) fun s₁ r₁ => ?_
  refine WP.mono (countDown_ok s₁ (n := n) (by omega_using [hn]) ((r₁.keep.gpr _ (by decide)).trans h.rbx))
    fun s₂ ⟨b₂, z₂, k₂⟩ => ⟨⟨(h.toRest.keep r₁.keep).count k₂, b₂, ?_, ?_⟩, z₂⟩
  · rw [k₂.2.1, r₁.env, ladderAfter_step k u (n := n + 3) (by omega_using [hn])]
    have := h.holds.iter (k := k) (t := n + 3) (by rw [swap_kbit k u (by omega_using [hn])]; exact kbit_lt k _)
    rw [swap_kbit k u (by omega_using [hn])] at this
    rw [show 2 + (n + 1) = n + 3 by omega_using [], show kbit k (n + 3) = bit k (n + 3) from
      ite_eq_right (by omega_using [hn])]
    exact this
  · rw [k₂.2.1]; exact r₁.le

theorem loop_ok (hf : FieldOk fld) {k : Nat} {u : Fe}
    (hbits : ∀ t < 256, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (kbit k t))
    {n : Nat} {s : State} (h1 : 1 ≤ n) (h2 : n ≤ 252) (hi : Inv base k u s₀ s n) :
    WP isa (.loop (.block (iter fld ++ countDown)) .ne) s fun s' => Inv base k u s₀ s' 0 := by
  refine WP.loop (M := isa) (body := .block (iter fld ++ countDown)) (c := .ne)
    (Q := fun s' => Inv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 252 ∧ Inv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_using [h1]⟩
  refine WP.mono (loopBody_ok hf (by omega_using [h2]) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega_using [hm] : ¬m = 0), Bool.not_false], m,
      by omega_using [], hm, by omega_using [h2], hi'⟩

/-! ## The doublings -/

/-- The point `(x, z)` doubled. -/
def dblX (x z : Fe) : Fe := (x + z) * (x + z) * ((x - z) * (x - z))

/-- The point `(x, z)` doubled. -/
def dblZ (x z : Fe) : Fe :=
  ((x + z) * (x + z) - (x - z) * (x - z)) *
    ((x + z) * (x + z) + Spec.X25519.a24 * ((x + z) * (x + z) - (x - z) * (x - z)))

def double' (fld : Field) : List Instr :=
  addCmov (32 * 7) (32 * 3) (32 * 4) ++ (subCmov (32 * 8) (32 * 3) (32 * 4) ++
    (fld.sqr (32 * 7) (32 * 7) ++ (fld.sqr (32 * 8) (32 * 8) ++ (subCmov (32 * 9) (32 * 7) (32 * 8) ++
    (fld.mul (32 * 3) (32 * 7) (32 * 8) ++ (fld.a24add (32 * 7) (32 * 7) (32 * 9) ++
    (fld.mul (32 * 4) (32 * 9) (32 * 7) ++ [])))))))

theorem double_eq (fld : Field) : double fld = double' fld := by
  simp only [double, double', List.append_assoc, List.append_nil]
  rfl

def envDouble (e : Env) : Env :=
  opMul 4 9 7 (opA24Add 7 7 9 (opMul 3 7 8 (opSub 9 7 8 (opMul 8 8 8 (opMul 7 7 7 (opSub 8 3 4
    (opAdd 7 3 4 e)))))))

theorem envDouble_x (e : Env) : envDouble e 3 = dblX (e 3) (e 4) := by
  simp only [envDouble, dblX, opMul, opAdd, opSub, opA24Add,
    Fun.update_apply, Fin.reduceEq, ↓reduceIte]

theorem envDouble_z (e : Env) : envDouble e 4 = dblZ (e 3) (e 4) := by
  simp only [envDouble, dblZ, opMul, opAdd, opSub, opA24Add,
    Fun.update_apply, Fin.reduceEq, ↓reduceIte]

theorem double_ok (hf : FieldOk fld) (h : Run base s₀ s e [4]) :
    WP isa (.block (double fld)) s fun s' => Run base s₀ s' (envDouble e) [4] := by
  rw [double_eq]
  exact h.add 7 3 4 (by decide) (by decide) fun _ h =>
    h.sub 8 3 4 (by decide) (by decide) fun _ h =>
    h.sqr hf 7 7 (by decide) fun _ h =>
    h.sqr hf 8 8 (by decide) fun _ h =>
    h.sub 9 7 8 (by decide) (by decide) fun _ h =>
    h.mul hf 3 7 8 (by decide) fun _ h =>
    h.a24 hf 7 7 9 (by decide) fun _ h =>
    h.mul hf 4 9 7 (by decide) fun _ h => WP.of_runBlock ⟨_, rfl, h.scr, h.keep, h.env, fun i hi =>
      h.le i (by revert i; decide)⟩

/-- `n` doublings of the point `(x, z)`. -/
def dblN (x z : Fe) : Nat → Fe × Fe
  | 0 => (x, z)
  | n + 1 => (dblX (dblN x z n).1 (dblN x z n).2, dblZ (dblN x z n).1 (dblN x z n).2)

/-- The doublings' invariant, with the counter `n`. -/
structure DInv (base : Addr) (x z : Fe) (s₀ s : State) (n : Nat) : Prop extends Rest base s₀ s where
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  x2 : E s.mem base 3 = (dblN x z (3 - n)).1
  z2 : E s.mem base 4 = (dblN x z (3 - n)).2
  le : fe s.mem base (32 * (4 : Fin 128).val) ≤ 2 * Spec.X25519.P

theorem doublings_ok (hf : FieldOk fld) {x z : Fe} {s : State} (hi : DInv base x z s₀ s 3) :
    WP isa (.loop (.block (double fld ++ countDown)) .ne) s fun s' => DInv base x z s₀ s' 0 := by
  refine WP.loop (M := isa) (body := .block (double fld ++ countDown)) (c := .ne)
    (Q := fun s' => DInv base x z s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 3 ∧ DInv base x z s₀ s m) ?_ 3 s ⟨by decide, by decide, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_using [h1]⟩
  rw [WP.block_append_iff]
  refine WP.mono (double_ok hf ⟨hi.scr, Keep.refl base s, rfl, fun i h => by
    rw [List.mem_singleton.1 h]; exact hi.le⟩) fun s₁ r₁ => ?_
  refine WP.mono (countDown_ok s₁ (n := m) (by omega_using [h2]) ((r₁.keep.gpr _ (by decide)).trans hi.rbx))
    fun s₂ ⟨b₂, z₂, k₂⟩ => ?_
  have e : 3 - m = 3 - (m + 1) + 1 := by omega_using [h2]
  have hi' : DInv base x z s₀ s₂ m := by
    refine ⟨(hi.toRest.keep r₁.keep).count k₂, b₂, ?_, ?_, ?_⟩
    · rw [k₂.2.1, r₁.env, envDouble_x, hi.x2, hi.z2, e]; rfl
    · rw [k₂.2.1, r₁.env, envDouble_z, hi.x2, hi.z2, e]; rfl
    · rw [k₂.2.1]; exact r₁.le _ (by decide)
  simp only [eval, z₂, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega_using [hm] : ¬m = 0), Bool.not_false], m,
      by omega_using [], hm, by omega_using [h2], hi'⟩

/-- An iteration for a bit that swaps nothing doubles `(x₂, z₂)`. -/
theorem step_same {k t : Nat} {u : Fe} {st : Spec.X25519.Ladder} (h : st.swap ^^^ bit k t = 0) :
    (Spec.X25519.ladderStep k u st t).x2 = dblX st.x2 st.z2 ∧
      (Spec.X25519.ladderStep k u st t).z2 = dblZ st.x2 st.z2 := by
  rw [ladderStep_eq, h]; exact ⟨rfl, rfl⟩

/-- The last three iterations double the point that bit 3 chooses, and leave no swap. -/
theorem ladderAfter_end {k : Nat} (u : Fe) (hl : bit k 0 = 0 ∧ bit k 1 = 0 ∧ bit k 2 = 0) :
    (ladderAfter k u 0).swap = 0 ∧
    (ladderAfter k u 0).x2 = (dblN (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).x2 (ladderAfter k u 3).x3).1
      (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).z2 (ladderAfter k u 3).z3).1 3).1 ∧
    (ladderAfter k u 0).z2 = (dblN (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).x2 (ladderAfter k u 3).x3).1
      (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).z2 (ladderAfter k u 3).z3).1 3).2 := by
  obtain ⟨h0, h1, h2⟩ := hl
  have s3 : (ladderAfter k u 3).swap = bit k 3 := swap_kbit k u (by decide)
  have s2 : (ladderAfter k u 2).swap = 0 := (swap_kbit k u (by decide)).trans h2
  have s1 : (ladderAfter k u 1).swap = 0 := (swap_kbit k u (by decide)).trans h1
  obtain ⟨x0, z0⟩ := step_same (k := k) (t := 0) (u := u) (st := ladderAfter k u 1) (by rw [s1, h0]; rfl)
  obtain ⟨x1, z1⟩ := step_same (k := k) (t := 1) (u := u) (st := ladderAfter k u 2) (by rw [s2, h1]; rfl)
  have x2 : (ladderAfter k u 2).x2 = dblX
      (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).x2 (ladderAfter k u 3).x3).1
      (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).z2 (ladderAfter k u 3).z3).1 := by
    rw [ladderAfter_step k u (n := 2) (by decide), ladderStep_eq, s3, h2, Nat.xor_zero]; rfl
  have z2 : (ladderAfter k u 2).z2 = dblZ
      (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).x2 (ladderAfter k u 3).x3).1
      (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).z2 (ladderAfter k u 3).z3).1 := by
    rw [ladderAfter_step k u (n := 2) (by decide), ladderStep_eq, s3, h2, Nat.xor_zero]; rfl
  rw [← ladderAfter_step k u (n := 1) (by decide), x2, z2] at x1 z1
  rw [← ladderAfter_step k u (n := 0) (by decide), x1, z1] at x0 z0
  exact ⟨(swap_kbit k u (by decide)).trans h0, x0, z0⟩

/-! ## The whole ladder -/

theorem movRbx_ok (s : State) (n : BitVec 32) :
    WP isa (.block ([.mov32 .rbx (.imm n)] : List Instr)) s fun s' =>
      s'.gpr .rbx = n.setWidth 64 ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem ladderStart_ok (hs : Scr s base) :
    WP isa (.block ladderStart) s fun s' => s'.gpr .rbx = BitVec.ofNat 64 252 ∧
      (∀ r, r ∉ clob → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base (BITS + 255)) (0 : BitVec 8) := by
  have w : InRegions s.wr (off base (BITS + 255)) 1 := ⟨_, hs.wr, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [ladderStart, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, State.store8, ea_sc, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.rd_setReg,
    RegUpd.mem_setReg, hs.rdi, w, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr hb => ?_, trivial, trivial, rfl⟩
  have : r ≠ .rax := fun h => hr (by rw [h]; decide)
  simp only [hb, this, ite_false]

theorem testBit : ∀ a < 2, ((BitVec.ofNat 8 a).setWidth 64 &&& (BitVec.ofNat 8 a).setWidth 64 ==
    (0 : BitVec 64)) = decide (a = 0) := by decide

theorem testBit_ok (hs : Scr s base) {d a : Nat} (hd : d < 4096) (ha : a < 2)
    (h : s.mem (off base d) = BitVec.ofNat 8 a) :
    WP isa (.block ([.movzx8 .rax (sc d), .alu .test .rax (.reg .rax)] : List Instr)) s fun s' =>
      s'.zf = some (decide (a = 0)) ∧ Keeps [.rax] s s' := by
  have r0 : InRegions (s.rd ++ s.wr) (off base d) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, ea_sc, hs.rdi,
    r0, h, RegUpd.gpr_setReg_self, RegUpd.zf_arithFlags, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨testBit a ha, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem ladderPoint_eq : ladderPoint =
    ([.movzx8 .rax (sc (BITS + 3)), .alu .test .rax (.reg .rax)] : List Instr) ++
    (choose2 (32 * 3) (32 * 3) (32 * 5) (32 * 4) (32 * 4) (32 * 6) ++ ([.mov32 .rbx (.imm 3)] : List Instr)) := by
  simp only [ladderPoint, List.append_assoc]
  rfl

theorem cswap_test : ∀ {a : Nat}, a < 2 → ∀ (x y : Fe),
    (if decide (a = 0) = true then x else y) = (Spec.X25519.cswap a x y).1 := by
  intro a ha x y
  rcases (by omega_using [ha] : a = 0 ∨ a = 1) with rfl | rfl <;> rfl

theorem ladderPoint_ok {k : Nat} {u : Fe} (hbits : s₀.mem (off base (BITS + 3)) = BitVec.ofNat 8 (bit k 3))
    (h : Inv base k u s₀ s 0) :
    WP isa (.block ladderPoint) s fun s' => DInv base
      (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).x2 (ladderAfter k u 3).x3).1
      (Spec.X25519.cswap (bit k 3) (ladderAfter k u 3).z2 (ladderAfter k u 3).z3).1 s₀ s' 3 := by
  have hk : bit k 3 < 2 := Nat.lt_succ_of_le (bit_le k 3)
  rw [ladderPoint_eq, WP.block_append_iff]
  refine WP.mono (testBit_ok h.scr (by decide) hk ((h.toRest.byte (by decide) (by decide)).trans hbits))
    fun s₁ ⟨z₁, k₁⟩ => ?_
  have K₁ : Keep base s s₁ := Keeps.keep k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (choose2E (K₁.scr h.scr) 3 3 5 4 4 6 (by decide) (by decide) (by decide) z₁)
    fun s₂ ⟨K₂, e₂, _, f₂⟩ => ?_
  refine WP.mono (movRbx_ok s₂ 3) fun s₃ ⟨b₃, k₃⟩ => ⟨(h.toRest.keep (K₁.trans K₂)).count k₃, b₃, ?_, ?_, ?_⟩
  · change _ = (Spec.X25519.cswap _ _ _).1
    rw [k₃.2.1, e₂, k₁.2.1, ← cswap_test hk, ← h.holds.x2, ← h.holds.x3]
    simp only [opSel, Fun.update_apply, Fin.reduceEq, ↓reduceIte]
  · change _ = (Spec.X25519.cswap _ _ _).1
    rw [k₃.2.1, e₂, k₁.2.1, ← cswap_test hk, ← h.holds.z2, ← h.holds.z3]
    simp only [opSel, Fun.update_apply, ↓reduceIte]
  · rw [k₃.2.1]
    refine Nat.le_trans (Nat.le_of_eq f₂) ?_
    rw [k₁.2.1]
    split
    · exact h.le 4 (by decide)
    · exact h.le 6 (by decide)

/-- The ladder. -/
theorem ladder_post (hf : FieldOk fld) {s : State} {base : Addr} {k : Nat} {u : Fe} (h : LPre base k u s) :
    WP isa (ladder fld) s (LPost base k u s) := by
  refine WP.seq (WP.mono (ladderStart_ok h.scr) fun s₁ ⟨b₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by decide) (by decide)).trans h.scr.rdi, wr₁ ▸ h.scr.wr, h.scr.nowrap⟩
  have o₁ : Outside base (BITS + 255) 1 s.mem s₁.mem := fun x hx => by
    rw [m₁]; exact writeW8_outside _ _ _ (by decide) (by omega_using [hx])
  have f₁ : ∀ d, d + 32 ≤ 1023 → fe s₁.mem base d = fe s.mem base d := fun d hd =>
    o₁.fe (Or.inl (by simp only [BITS]; omega_using [hd])) (by omega_using [hd])
  have e₁ : ∀ i : Fin 128, i.val < 24 → E s₁.mem base i = E s.mem base i := fun i hi => by
    simp only [E, F]; rw [f₁ _ (by omega_using [hi])]
  have bits₁ : ∀ t < 256, s₁.mem (off base (BITS + t)) = BitVec.ofNat 8 (kbit k t) := fun t ht => by
    rw [m₁, writeW8_apply]
    rcases Nat.lt_or_ge t 255 with h' | h'
    · rw [ite_eq_right fun c => absurd ((off_eq_iff base (by simp only [BITS]; omega_using [ht]) (by decide)).1 c)
        (by omega_using [h']), h.bits t h', kbit, ite_eq_right (by omega_using [h'])]
    · rw [show t = 255 by omega_using [ht, h'], ite_eq_left rfl]; rfl
  have inv : Inv base k u s₁ s₁ 252 := by
    refine ⟨⟨hs₁, fun _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩, b₁, ⟨?_, ?_, ?_, ?_, ?_⟩, fun i hi => ?_⟩
    · rw [e₁ 2 (by decide)]; exact h.x1
    · rw [e₁ 3 (by decide)]; exact h.x2
    · rw [e₁ 4 (by decide)]; exact h.z2
    · rw [e₁ 5 (by decide)]; exact h.x3
    · rw [e₁ 6 (by decide)]; exact h.z3
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rw [f₁ _ (by decide)]; exact h.z2b
      · rw [f₁ _ (by decide)]; exact h.z3b
  refine WP.seq (WP.mono (loop_ok hf bits₁ (by decide) (by decide) inv) fun s₂ i₂ => ?_)
  refine WP.seq (WP.mono (ladderPoint_ok ((bits₁ 3 (by decide)).trans rfl) i₂) fun s₃ d₃ => ?_)
  refine WP.mono (doublings_ok hf d₃) fun s₄ d₄ => ?_
  obtain ⟨sw, x, z⟩ := ladderAfter_end u h.low
  have hw : word s₄.mem base SWAP = BitVec.ofNat 64 0 := by
    rw [d₄.mem.word (by decide) (by decide), o₁.word (by decide) (by decide)]; exact h.swap
  refine ⟨d₄.scr, fun r hr hb => (d₄.gpr r hr hb).trans (g₁ r hr hb), d₄.rd.trans rd₁, d₄.wr.trans wr₁,
    (o₁.mono (by decide) (by decide)).trans (d₄.mem.mono (by decide) (by decide)), 0, by decide, hw, ?_, ?_⟩
  · rw [sw, x]; exact d₄.x2
  · rw [sw, z]; exact d₄.z2

end VG.Proof.X25519.X86_64
