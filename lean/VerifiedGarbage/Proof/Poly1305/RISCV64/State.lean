module

import VerifiedGarbage.Proof.Poly1305.RISCV64.Reduce
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Poly1305.RISCV64.Absorb

/-!
# Poly1305 on RISC-V: the state

The regions of the state (as on PPC64LE, `Proof/Poly1305/PPC64LE/Setup.lean`),
the key and the accumulator as numbers, and the code that reads and writes
them a byte at a time: `setup_ok` (the clamped `r` and the accumulator on
entry), `storeH_ok`, `addS_ok` and `storeTag_ok`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The address `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (off base d) n := Offset.contains_base base h hd

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (Offset.sep p h (by omega) (by omega)) (by decide)

/-! ## The regions of the state -/

section
variable (st : Addr)
/-- The accumulator. -/
abbrev hR : Region := ⟨st, 24⟩
/-- The key. -/
abbrev kR : Region := ⟨off st 24, 32⟩
/-- The buffer and the rest. -/
abbrev wR : Region := ⟨off st 56, 72⟩
/-- The whole state. -/
abbrev sR : Region := ⟨st, 128⟩
end

theorem sub_sR (st : Addr) {d n : Nat} (h : d + n ≤ 128) : Region.Sub ⟨off st d, n⟩ (sR st) :=
  Offset.sub_base st h

theorem kR_disjoint (st : Addr) : ∀ r ∈ [hR st, wR st], (kR st).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint_base st (by decide) (by decide)
  · exact Offset.disjoint st (by decide) (by decide) (by decide)

/-- The key is unchanged by writes to the accumulator and the working space. -/
theorem key_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') :
    bytesAt m' (off st 24) 32 = bytesAt m (off st 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := kR st) (kR_disjoint st) (by simp only [Nat.reducePow, Nat.reduceLeDiff])
    (List.mem_range.mp hi)

/-- A word of the key, unchanged by writes to the accumulator and the working space. -/
theorem key_word {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') {d : Nat}
    (h₁ : 24 ≤ d) (h₂ : d + 8 ≤ 56) : m'.readW (off st d) 64 = m.readW (off st d) 64 := by
  refine hf.readW (r := ⟨off st d, 8⟩) (a := off st d) (w := 64) (Region.contains_self _ _) ?_
    (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base st (n := 8) (k := 24) (by omega) (by omega)
  · exact Offset.disjoint st (n := 8) (e := 56) (k := 72) (by omega) (by omega) (by omega)

/-! ## The accumulator and the key as numbers -/

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- The accumulator stored in the state. -/
theorem leNum_acc (m : Mem) (st : Addr) :
    leNum (bytesAt m st 24) = word m st 0 + 2 ^ 64 * word m st 8 + 2 ^ 128 * word m st 16 := by
  rw [Poly1305.leNum_bytesAt_24, word, add_ofNat_zero]
  rfl

theorem key_take (m : Mem) (st : Addr) :
    (bytesAt m (off st 24) 32).take 16 = bytesAt m (off st 24) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add,
    List.take_left' (Poly1305.length_bytesAt _ _ _)]

theorem key_drop (m : Mem) (st : Addr) :
    ((bytesAt m (off st 24) 32).drop 16).take 16 = bytesAt m (off st 40) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add,
    List.drop_left' (Poly1305.length_bytesAt _ _ _),
    List.take_of_length_le (by rw [Poly1305.length_bytesAt])]
  congr 1
  simp only [off]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem leNum_key (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = word m p 0 + 2 ^ 64 * word m p 8 := by
  rw [Poly1305.leNum_bytesAt_16, word, add_ofNat_zero]
  rfl

theorem off_24 (p : Addr) : off p 24 = p + 24 := rfl

theorem off_off (p : Addr) (d e : Nat) : off (off p d) e = off p (d + e) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The clamping mask of `r1`. -/
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

/-- The clamped `r` of the key in the state. -/
abbrev Rk (m : Mem) (st : Addr) : Nat :=
  (m.readW (off st 24) 64 &&& M0).toNat + 2 ^ 64 * (m.readW (off st 32) 64 &&& M1).toNat

theorem clamp_key (m : Mem) (st : Addr) :
    clamp (leNum ((bytesAt m (off st 24) 32).take 16)) = Rk m st := by
  rw [key_take, leNum_key, word, word, off, add_ofNat_zero, BitVec.add_assoc, ← BitVec.ofNat_add,
    Poly1305.clamp_words]
  rfl

/-! ## The state on entry -/

section
variable (s₀ : State)
/-- The state, on entry. -/
abbrev st : Addr := s₀.gpr .a0
/-- The clamped `r`. -/
abbrev Rn : Nat := Rk s₀.mem (st s₀)
/-- The accumulator on entry. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem (st s₀) 24)
end

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem A0_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) : A0 s₀ < P := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2] at this
  exact this

theorem repr_key {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    bytesAt s₀.mem (off (st s₀) 24) 32 = key := h.2.1

theorem repr_acc {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    accumulate (Rn s₀) msg = A0 s₀ := by
  rw [A0, h.2.2, ← repr_key h, clamp_key]

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

/-! ## Storing the accumulator -/

/-- The words of `h` stored. -/
def storeHm (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) : Mem :=
  ((m.writeW (off st 0) w0).writeW (off st 8) w1).writeW (off st 16) w2

theorem storeHm_frame {st : Addr} {r : Region} {m m' : Mem} (hf : Frame [hR st, r] m m')
    (w0 w1 w2 : BitVec 64) : Frame [hR st, r] m (storeHm m' st w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd =>
    contains_off hd (by omega)
  exact ((hf.writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))

theorem storeHm_acc (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) :
    leNum (bytesAt (storeHm m st w0 w1 w2) st 24) = w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat := by
  rw [leNum_acc]
  simp only [word, storeHm]
  rw [show st + BitVec.ofNat 64 0 = off st 0 from rfl, show st + BitVec.ofNat 64 8 = off st 8 from rfl,
    show st + BitVec.ofNat 64 16 = off st 16 from rfl,
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide),
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
    Mem.readW_writeW_self64]

theorem in_st {s : State} {p : Addr} (hw : sR p ∈ s.wr) {d n : Nat} (h : d + n ≤ 128) :
    InRegions s.wr (p + BitVec.ofNat 64 d) n :=
  ⟨_, hw, contains_off h (by omega)⟩

theorem in_st' {s : State} {p : Addr} (hw : sR p ∈ s.rd ++ s.wr) {d n : Nat} (h : d + n ≤ 128) :
    InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 d) n :=
  ⟨_, hw, contains_off h (by omega)⟩

/-- The state plus a multiple of 8 is 8-byte aligned. -/
theorem st_al8 {p : Addr} (ha : p.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) :
    (p + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega

theorem storeH_ok (s : State) (hw : sR (s.gpr .a0) ∈ s.wr) (ha : (s.gpr .a0).toNat % 8 = 0) :
    WP isa (.block storeH) s fun s' =>
      s'.mem = storeHm s.mem (s.gpr .a0) (s.gpr H0) (s.gpr H1) (s.gpr H2) ∧
      (∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [storeH]
  refine VG.RISCV64.Steps.wp_sd (a := off (s.gpr .a0) 0) (by decide) rfl (st_al8 ha (by decide))
    (in_st hw (by decide)) fun s₁ g₁ => ?_
  refine VG.RISCV64.Steps.wp_sd (a := off (s.gpr .a0) 8) (by decide) (by rw [g₁.gpr])
    (st_al8 ha (by decide)) (by rw [g₁.wr]; exact in_st hw (by decide)) fun s₂ g₂ => ?_
  refine VG.RISCV64.Steps.wp_sd (a := off (s.gpr .a0) 16) (by decide) (by rw [g₂.gpr, g₁.gpr])
    (st_al8 ha (by decide)) (by rw [g₂.wr, g₁.wr]; exact in_st hw (by decide)) fun s₃ g₃ =>
    WP.block_nil ⟨?_, fun r _ _ => by rw [g₃.gpr, g₂.gpr, g₁.gpr], by rw [g₃.rd, g₂.rd, g₁.rd],
      by rw [g₃.wr, g₂.wr, g₁.wr], by rw [g₃.sp, g₂.sp, g₁.sp]⟩
  rw [g₃.mem, g₂.mem, g₁.mem, g₂.gpr, g₁.gpr]
  rfl

/-! ## Loading the state -/

/-- A doubleword of the state at `a0`, loaded into `d`. -/
theorem ldSt_ok (s : State) (d : Reg) {off : Nat} (ho : off + 8 ≤ 128) (hw : sR (s.gpr .a0) ∈ s.rd ++ s.wr)
    (ha : (s.gpr .a0).toNat % 8 = 0) (h8 : off % 8 = 0 := by decide) :
    WP isa (.block [.load .d d .a0 off]) s fun s' =>
      Words64.Upd3 s s' d T1 T2 (s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 off) 64) :=
  VG.RISCV64.Steps.wp_ld (by omega) rfl (st_al8 ha h8) (in_st' hw ho) fun s' u =>
    WP.block_nil ⟨u.gpr, fun r h _ _ => u.other r h, u.mem, u.rd, u.wr, u.sp⟩

theorem upd3_regs {s s' : State} {d t₁ t₂ : Reg} {v : BitVec 64} (h : Words64.Upd3 s s' d t₁ t₂ v) :
    Keeps [d, t₁, t₂] s s' :=
  ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact h.other r hr.1 hr.2.1 hr.2.2, h.mem, h.rd, h.wr, h.sp⟩

theorem M0_M1 : M0 &&& BitVec.ofInt 64 (-4) = M1 := by decide

theorem key0_lt (k : BitVec 64) : (k &&& M0).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem key1_lt (k : BitVec 64) : (k &&& M1).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem key1_mod (k : BitVec 64) : (k &&& M1).toNat % 4 = 0 := by
  rw [BitVec.toNat_and, show (4 : Nat) = 2 ^ 2 from rfl,
    ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show M1.toNat &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

theorem s1_toNat (k : BitVec 64) :
    (((k &&& M1) >>> 2) + (k &&& M1)).toNat = 5 * ((k &&& M1).toNat / 4) := by
  have h1 := key1_lt k
  have h2 := key1_mod k
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega_using [h1, h2]

/-- The clamping and `s1`. -/
def clampI : List Instr :=
  [.logic .and R0 R0 T1, .logicImm .and T1 T1 (-4), .logic .and R1 R1 T1, .shift .srl .d S1 R1 2,
    .add S1 S1 R1]

theorem clampI_ok (s : State) :
    WP isa (.block clampI) s fun s' =>
      s'.gpr R0 = s.gpr R0 &&& s.gpr T1 ∧ s'.gpr R1 = s.gpr R1 &&& (s.gpr T1 &&& BitVec.ofInt 64 (-4)) ∧
      s'.gpr S1 = ((s.gpr R1 &&& (s.gpr T1 &&& BitVec.ofInt 64 (-4))) >>> 2) +
        (s.gpr R1 &&& (s.gpr T1 &&& BitVec.ofInt 64 (-4))) ∧
      Keeps [R0, T1, R1, S1] s s' := by
  apply WP.of_runBlock
  simp only [clampI, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_logicImm (show imm12 (-4) by decide), exec_shift_d (show 2 < 64 by decide), exec_add,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · exact (((((Keeps.refl _ s).write _ (by decide)).write _ (by decide)).write _
      (by decide)).write _ (by decide)).write _ (by decide)

theorem setup_eq : setup =
    ([.load .d R0 .a0 24] : List Instr) ++ (([.load .d R1 .a0 32] : List Instr) ++
    (Impl.Words64.RISCV64.movImm64 T1 T2 M0 ++ (clampI ++
    (([.load .d H0 .a0 0] : List Instr) ++ (([.load .d H1 .a0 8] : List Instr) ++
      ([.load .d H2 .a0 16] : List Instr)))))) := by
  simp only [setup, clampI, List.append_assoc, List.cons_append, List.nil_append]

/-- The registers `setup` writes. -/
abbrev setupRegs : List Reg := [R0, T1, T2, R1, S1, H0, H1, H2]

theorem setup_ok (s : State) (hw : sR (s.gpr .a0) ∈ s.rd ++ s.wr) (ha : (s.gpr .a0).toNat % 8 = 0) :
    WP isa (.block setup) s fun s' =>
      Keys (Rk s.mem (s.gpr .a0)) s' ∧ (A0 s < P → hv s' = A0 s ∧ Bounds s') ∧
      Keeps setupRegs s s' := by
  rw [setup_eq]
  refine WP.block_append (WP.mono (ldSt_ok s R0 (by decide) hw ha) fun s₁ u₁ => ?_)
  have k₁ := upd3_regs u₁
  have a₁ : s₁.gpr .a0 = s.gpr .a0 := k₁.gpr'
  have hw₁ : sR (s₁.gpr .a0) ∈ s₁.rd ++ s₁.wr := by rw [a₁, k₁.2.2.1, k₁.2.2.2.1]; exact hw
  refine WP.block_append (WP.mono (ldSt_ok s₁ R1 (by decide) hw₁ (by rw [a₁]; exact ha)) fun s₂ u₂ => ?_)
  have k₂ := k₁.trans (upd3_regs u₂)
  refine WP.block_append (WP.mono (Words64.movImm64_ok (d := T1) (tmp := T2) (s := s₂) (by decide) M0)
    fun s₃ ⟨t₃, o₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  have k₃ : Keeps [T1, T2] s₂ s₃ := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact o₃ r hr.1 hr.2, m₃, rd₃, wr₃, sp₃⟩
  refine WP.block_append (WP.mono (clampI_ok s₃) fun s₄ ⟨c₀, c₁, c₂, k₄⟩ => ?_)
  have k₁₄ := (k₂.trans k₃).trans k₄
  have a₄ : s₄.gpr .a0 = s.gpr .a0 := k₁₄.gpr'
  have hw₄ : sR (s₄.gpr .a0) ∈ s₄.rd ++ s₄.wr := by rw [a₄, k₁₄.2.2.1, k₁₄.2.2.2.1]; exact hw
  refine WP.block_append (WP.mono (ldSt_ok s₄ H0 (by decide) hw₄ (by rw [a₄]; exact ha)) fun s₅ u₅ => ?_)
  have k₅ := upd3_regs u₅
  have hw₅ : sR (s₅.gpr .a0) ∈ s₅.rd ++ s₅.wr := by
    rw [k₅.gpr' (r := .a0), k₅.2.2.1, k₅.2.2.2.1]; exact hw₄
  refine WP.block_append (WP.mono (ldSt_ok s₅ H1 (by decide) hw₅
    (by rw [k₅.gpr' (r := .a0), a₄]; exact ha)) fun s₆ u₆ => ?_)
  have k₆ := upd3_regs u₆
  have hw₆ : sR (s₆.gpr .a0) ∈ s₆.rd ++ s₆.wr := by
    rw [k₆.gpr' (r := .a0), k₆.2.2.1, k₆.2.2.2.1]; exact hw₅
  refine WP.mono (ldSt_ok s₆ H2 (by decide) hw₆
    (by rw [k₆.gpr' (r := .a0), k₅.gpr' (r := .a0), a₄]; exact ha)) fun s₇ u₇ => ?_
  have k₇ := upd3_regs u₇
  have k₅₇ := (k₅.trans k₆).trans k₇
  have K := k₁₄.trans k₅₇
  -- The memory and the base are those on entry.
  have mm : ∀ {t : State}, t.mem = s.mem → t.gpr .a0 = s.gpr .a0 → ∀ d,
      t.mem.readW (t.gpr .a0 + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 d) 64 :=
    fun hm ha _ => by rw [hm, ha]
  have r0 : s₇.gpr R0 = s.mem.readW (off (s.gpr .a0) 24) 64 &&& M0 := by
    rw [k₅₇.gpr' (r := R0), c₀, k₃.gpr' (r := R0), t₃, (upd3_regs u₂).gpr' (r := R0), u₁.gpr]
  have r1 : s₇.gpr R1 = s.mem.readW (off (s.gpr .a0) 32) 64 &&& M1 := by
    rw [k₅₇.gpr' (r := R1), c₁, k₃.gpr' (r := R1), t₃, u₂.gpr, M0_M1, mm k₁.2.1 a₁]
  have s1 : s₇.gpr S1 = ((s.mem.readW (off (s.gpr .a0) 32) 64 &&& M1) >>> 2) +
      (s.mem.readW (off (s.gpr .a0) 32) 64 &&& M1) := by
    rw [k₅₇.gpr' (r := S1), c₂, k₃.gpr' (r := R1), t₃, u₂.gpr, M0_M1, mm k₁.2.1 a₁]
  refine ⟨⟨(s₇.gpr R1).toNat / 4, ?_, ?_, ?_, ?_, ?_⟩, fun hA => ?_, K.mono⟩
  · rw [r0]; exact key0_lt _
  · have e := key1_mod (s.mem.readW (off (s.gpr .a0) 32) 64)
    rw [← r1] at e
    omega_using [e]
  · have e := key1_lt (s.mem.readW (off (s.gpr .a0) 32) 64)
    rw [← r1] at e
    omega_using [e]
  · rw [s1, s1_toNat, r1]
  · rw [r0, r1]
  · have m₄ : s₄.mem = s.mem := k₁₄.2.1
    have h0 : s₇.gpr H0 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 0) 64 := by
      rw [((upd3_regs u₆).trans k₇).gpr' (r := H0), u₅.gpr, mm m₄ a₄]
    have h1 : s₇.gpr H1 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 8) 64 := by
      rw [k₇.gpr' (r := H1), u₆.gpr, mm (k₅.2.1.trans m₄) (k₅.gpr'.trans a₄)]
    have h2 : s₇.gpr H2 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 16) 64 := by
      rw [u₇.gpr, mm ((k₅.trans (upd3_regs u₆)).2.1.trans m₄)
        ((k₅.trans (upd3_regs u₆)).gpr'.trans a₄)]
    have e : hv s₇ = A0 s := by
      simp only [hv, val3, h0, h1, h2, A0, st, leNum_acc, word]
    refine ⟨e, ?_⟩
    have a0 := (s₇.gpr H0).isLt
    have a1 := (s₇.gpr H1).isLt
    simp only [Bounds, hv, val3, P] at e hA ⊢
    omega_using [e, hA, a0, a1]

/-! ## The tag -/

theorem addS_eq : addS = ([.load .d X0 .a0 40] : List Instr) ++
    (([.load .d X1 .a0 48] : List Instr) ++ Impl.Words.RISCV64.add2 H0 H1 X0 X1) := by
  simp only [addS, List.cons_append, List.nil_append]

theorem addS_ok (s : State) (hw : sR (s.gpr .a0) ∈ s.rd ++ s.wr) (ha : (s.gpr .a0).toNat % 8 = 0) :
    WP isa (.block addS) s fun s' =>
      (s'.gpr H0).toNat + 2 ^ 64 * (s'.gpr H1).toNat =
        ((s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat +
          (word s.mem (s.gpr .a0) 40 + 2 ^ 64 * word s.mem (s.gpr .a0) 48)) % 2 ^ 128 ∧
      Keeps [X0, T1, T2, X1, T1, T2, H0, H1, X0] s s' := by
  rw [addS_eq]
  refine WP.block_append (WP.mono (ldSt_ok s X0 (by decide) hw ha) fun s₁ u₁ => ?_)
  have k₁ := upd3_regs u₁
  have hw₁ : sR (s₁.gpr .a0) ∈ s₁.rd ++ s₁.wr := by
    rw [k₁.gpr' (r := .a0), k₁.2.2.1, k₁.2.2.2.1]; exact hw
  refine WP.block_append (WP.mono (ldSt_ok s₁ X1 (by decide) hw₁
    (by rw [k₁.gpr' (r := .a0)]; exact ha)) fun s₂ u₂ => ?_)
  have k₂ := upd3_regs u₂
  refine WP.mono add2_ok fun s₃ ⟨e₃, k₃⟩ => ⟨?_, (k₁.trans k₂).trans k₃⟩
  rw [e₃, (k₁.trans k₂).gpr' (r := H0), (k₁.trans k₂).gpr' (r := H1),
    k₂.gpr' (r := X0), u₁.gpr, u₂.gpr, k₁.2.1, k₁.gpr' (r := .a0)]

/-- The tag. -/
abbrev outR (p : Addr) : Region := ⟨p, 16⟩

theorem storeTag_ok (s : State) (ho : outR (s.gpr .a2) ∈ s.wr) :
    WP isa (.block storeTag) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr .a2) (s.gpr H0)).writeW
        (s.gpr .a2 + BitVec.ofNat 64 8) (s.gpr H1) := by
  rw [storeTag]
  refine WP.block_append (WP.mono (Words64.storeLE64_ok (v := H0) (n := .a2) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨_, ho, contains_off (by decide) (by decide)⟩) fun s₁ ⟨g₁, m₁, r₁, w₁, p₁⟩ => ?_)
  have a₁ : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide)
  have i₁ : InRegions s₁.wr (s₁.gpr .a2 + BitVec.ofNat 64 8) 8 := by
    rw [w₁, a₁]; exact ⟨_, ho, contains_off (by decide) (by decide)⟩
  refine WP.mono (Words64.storeLE64_ok (v := H1) (n := .a2) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) i₁)
    fun s₂ ⟨_, m₂, _, _, _⟩ => ?_
  rw [m₂, m₁, a₁, g₁ _ (by decide) (by decide), add_ofNat_zero]

/-- The tag stored: the low 128 bits of `x`. -/
theorem tag_bytes (m : Mem) (p : Addr) (h0 h1 : BitVec 64) (x : Nat)
    (hx : h0.toNat + 2 ^ 64 * h1.toNat = x % 2 ^ 128) :
    bytesAt ((m.writeW p h0).writeW (p + BitVec.ofNat 64 8) h1) p 16 =
      Spec.Poly1305.leBytes 16 x := by
  have q0 : ((m.writeW p h0).writeW (p + BitVec.ofNat 64 8) h1).readW p 64 = h0 := by
    rw [Mem.readW_writeW_sep (Offset.sep_base p (n := 8) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  have q1 : ((m.writeW p h0).writeW (p + BitVec.ofNat 64 8) h1).readW
      (p + BitVec.ofNat 64 8) 64 = h1 := Mem.readW_writeW_self64 _ _ _
  have a0 := h0.isLt; have a1 := h1.isLt
  refine Poly1305.bytesAt_leBytes_16 _ _ _ ?_ ?_
  · rw [q0]; omega_using [hx, a0, a1]
  · rw [q1]; omega_using [hx, a0, a1]

end VG.Proof.Poly1305.RISCV64
