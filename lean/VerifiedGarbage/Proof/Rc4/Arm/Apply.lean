module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Rc4.Update
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rc4.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rc4.Identity
public import VerifiedGarbage.Proof.Rc4.Schedule
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Rc4.Dword
public import VerifiedGarbage.Proof.Rc4.Scan32
public import VerifiedGarbage.Impl.Rc4.Arm
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.TCB.Arm.Isa

/-! ### `Rc4.Arm.Init`, which this module and modules that import it used -/

section

/-! ### `Rc4.Arm.Replace`, which this module and modules that import it used -/

section

/-! ### `Rc4.Arm.Lookup`, which this module and modules that import it used -/

section

/-! ### `Rc4.Arm.Run`, which this module and modules that import it used -/

section

/-!
# RC4 on ARMv7: running blocks

`arun [facts]` runs a block symbolically (`runBlock_cons`, `runStep_some`,
the semantics of the instructions the code uses, reading through the
writes with `RegUpd`), keeping the flag and memory updates folded.
`Keep rs s s'` says that `s'` has the registers of `s` but for `rs`, and its
regions and stack pointer; `WP.keep` proves it of a block none of whose
instructions writes another register.
-/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Proof.Rc4

/-! ## Registers kept -/

def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂)
    (h₂ : Keep rs' s₂ s₃) : Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Whether every instruction of `is` writes only registers of `rs`. -/
def writesOnly (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => (dsts i).all rs.contains

theorem WP.keep {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa (.block is) s Q) (hc : writesOnly rs is = true) :
    WP isa (.block is) s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  have he' := Exec.block_iff.mp he
  obtain ⟨r, w, p, -⟩ := execBlock_regions he'
  exact ⟨t, s', he, hq, fun r' hr => execBlock_gpr (fun i hi =>
    clobbers_eq_false_of_contains (List.all_eq_true.mp hc i hi) hr) he', r, w, p⟩

/-! ## Symbolic execution -/

theorem gpr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
theorem mem_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
theorem rd_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
theorem wr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
theorem sp_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl
theorem z_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0#32) := rfl
theorem c_subFlags (s : State) (x y : BitVec 32) :
    (subFlags s x y).c = decide (y.toNat ≤ x.toNat) := rfl

/-- `s` with the memory `m`: what a store leaves, kept folded. -/
def withMem (s : State) (m : Mem) : State := { s with mem := m }

theorem store32_eq (s : State) (a : Addr) (x : BitVec 32) :
    s.store32 a x = if InRegions s.wr a 4 then some (withMem s (s.mem.writeW a x)) else none := rfl
theorem store8_eq (s : State) (a : Addr) (x : BitVec 8) :
    s.store8 a x = if InRegions s.wr a 1 then some (withMem s (s.mem.writeW a x)) else none := rfl
theorem sp_store (s : State) (m : Mem) : (withMem s m).sp = s.sp := rfl
theorem gpr_store (s : State) (m : Mem) : (withMem s m).gpr = s.gpr := rfl
theorem rd_store (s : State) (m : Mem) : (withMem s m).rd = s.rd := rfl
theorem wr_store (s : State) (m : Mem) : (withMem s m).wr = s.wr := rfl
theorem mem_store (s : State) (m : Mem) : (withMem s m).mem = m := rfl
theorem z_store (s : State) (m : Mem) : (withMem s m).z = s.z := rfl
theorem c_store (s : State) (m : Mem) : (withMem s m).c = s.c := rfl

/-- The carry `adc` adds, as a number (rewritten before the flag inside it,
so that the `if` never depends on a rewritten instance). -/
theorem ite_carry (b : Bool) : (if b = true then (1 : BitVec 32) else 0) = BitVec.ofNat 32 b.toNat := by
  cases b <;> rfl

/-- An immediate below 256 is encodable (rotation 0); closes the encoding
checks of the literal operands in `arun`. -/
theorem encodable_of_lt {v : BitVec 32} (h : v.toNat < 256) : encodable v = true :=
  List.any_eq_true.2 ⟨0, by simp, by
    have h0 : v.rotateLeft (2 * 0) = v := by ext i; simp
    simpa only [h0, decide_eq_true_eq] using h⟩

/-- 256, the one immediate of the code that needs a rotation. -/
theorem encodable_256 : encodable (256#32) = true := by decide

/-- Runs a block of the RC4 code. -/
syntax "arun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| arun) => `(tactic| arun [])
  | `(tactic| arun [$ls,*]) => `(tactic| plain_simp_names (
                       apply WP.of_runBlock
                       set_option linter.unusedSimpArgs false in
                       simp (disch := decide) only [runBlock_cons, runStep_some, runBlock_nil, exec,
                         encodable_of_lt, encodable_256,
                         Op2.eval, imm, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, z_setReg, c_setReg,
                         gpr_subFlags, mem_subFlags, rd_subFlags, wr_subFlags, sp_subFlags, z_subFlags, c_subFlags,
                         State.load32, store32_eq, State.load8, store8_eq, sp_store, gpr_store, rd_store, wr_store,
                         mem_store, z_store, c_store, ↓ite_carry, ite_true, ite_false, ↓reduceIte, reduceCtorEq,
                         Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, Option.map_some,
                         Option.some.injEq, exists_eq_left', List.cons_append, List.nil_append, and_true, true_and,
                         $ls,*]))

/-- Closes a conjunction of reflexive equations. -/
macro "conj_rfl" : tactic => `(tactic| repeat' (first | exact rfl | refine ⟨?_, ?_⟩))

/-! ## Values -/

theorem ones_eq : ((0xFFFF : BitVec 16) ++
    (((0xFFFF : BitVec 16).setWidth 32).extractLsb' 0 16) : BitVec 32) = BitVec.allOnes 32 := by
  decide

/-- The mask `adc d, ones, #0` leaves after a comparison that set the carry to `c`. -/
theorem adc_mask (c : Bool) (y : BitVec 32) :
    (BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 c.toNat) &&& y =
      if c = true then 0 else y := by
  cases c
  · rw [show BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 false.toNat =
      BitVec.allOnes 32 by decide, BitVec.allOnes_and]
    rfl
  · rw [show BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 true.toNat = 0 by decide]
    exact BitVec.zero_and

theorem adc_mask' (c : Bool) (y : BitVec 32) :
    y &&& (BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 c.toNat) =
      if c = true then 0 else y := by
  rw [BitVec.and_comm, adc_mask]

/-- The address of byte `i` of the table at `P`. -/
theorem idx_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) (i : Byte) :
    State.addr (P + i.setWidth 32 + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 i.toNat := by
  rw [BitVec.add_zero, byte32]
  exact addr_add (by have := i.isLt; omega_using [hP])

/-- The branch conditions. -/
theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

theorem region_in {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) :
    InRegions (rs ++ ws) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.Rc4.Arm

end

end

/-! # RC4 on ARMv7: the table lookup, by rows of two words -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Proof.Rc4

/-! ## The values the code makes -/

/-- Bit `k` of `x`, as `bit` leaves it. -/
def bitv (x : BitVec 32) (k : Nat) : BitVec 32 := (x <<< (31 - k)) >>> 31

/-- A step of the one-hot word: `o` shifted left by `n` if `b` is 1. -/
def ohs (o b : BitVec 32) (n : Nat) : BitVec 32 := (o <<< n - o) * b + o

/-- What `oneHot` leaves for the index `x`. -/
def ohv (x : BitVec 32) : BitVec 32 :=
  ohs (ohs (ohs (ohs (bitv x 3 + BitVec.ofNat 32 1) (bitv x (3 + 1)) (2 ^ 1)) (bitv x (3 + 2)) (2 ^ 2))
    (bitv x (3 + 3)) (2 ^ 3)) (bitv x (3 + 4)) (2 ^ 4)

/-- What `deltaWord` multiplies a byte by to move it to the index's byte of a
word: `2 ^ (8 (x % 4))`. -/
def mlv (x : BitVec 32) : BitVec 32 :=
  (bitv x 0 <<< 8 - bitv x 0 + BitVec.ofNat 32 1) * (bitv x 1 <<< 16 - bitv x 1 + BitVec.ofNat 32 1)

/-- `W` shifted right by `n` if `b` is 1. -/
def cshr (W : BitVec 32) (n : Nat) (b : BitVec 32) : BitVec 32 := (W >>> n - W) * b + W

/-- What `pickByte` leaves of the word `W` for the index `x`. -/
def pickv (W x : BitVec 32) : BitVec 32 :=
  cshr (cshr W 8 (bitv x 0)) 16 (bitv x 1) &&& BitVec.ofNat 32 255

/-- What `deltaWord` leaves: the word `W` with a byte replaced by `a`, minus `W`. -/
def deltav (W a x : BitVec 32) : BitVec 32 := ((W &&& ~~~(mlv x <<< 8 - mlv x)) ||| (a * mlv x)) - W

/-- The selector of row `r` for the index's row `h`. -/
def selv (h r : Nat) : BitVec 32 := if h = r then BitVec.ofNat 32 1 else BitVec.ofNat 32 0

theorem selv_self (h : Nat) : selv h h = BitVec.ofNat 32 1 := by
  unfold selv; rw [ite_eq_left rfl]

theorem selv_ne {h r : Nat} (e : h ≠ r) : selv h r = BitVec.ofNat 32 0 := by
  unfold selv; rw [ite_eq_right e]

/-- The values for an index `32 a + b`: its low three bits, the multiplier
of its byte and its row's one-hot word. -/
theorem idx_split : ∀ a < 8, ∀ b < 32,
    bitv (BitVec.ofNat 32 (32 * a + b)) 0 = BitVec.ofNat 32 ((32 * a + b) % 2) ∧
    bitv (BitVec.ofNat 32 (32 * a + b)) 1 = BitVec.ofNat 32 ((32 * a + b) / 2 % 2) ∧
    bitv (BitVec.ofNat 32 (32 * a + b)) 2 = BitVec.ofNat 32 ((32 * a + b) / 4 % 2) ∧
    mlv (BitVec.ofNat 32 (32 * a + b)) = BitVec.ofNat 32 (2 ^ (8 * ((32 * a + b) % 4))) ∧
    ohv (BitVec.ofNat 32 (32 * a + b)) = BitVec.ofNat 32 (2 ^ ((32 * a + b) / 8)) := by decide

theorem idx_vals {n : Nat} (h : n < 256) :
    bitv (BitVec.ofNat 32 n) 0 = BitVec.ofNat 32 (n % 2) ∧
    bitv (BitVec.ofNat 32 n) 1 = BitVec.ofNat 32 (n / 2 % 2) ∧
    bitv (BitVec.ofNat 32 n) 2 = BitVec.ofNat 32 (n / 4 % 2) ∧
    mlv (BitVec.ofNat 32 n) = BitVec.ofNat 32 (2 ^ (8 * (n % 4))) ∧
    ohv (BitVec.ofNat 32 n) = BitVec.ofNat 32 (2 ^ (n / 8)) := by
  have := idx_split (n / 32) (by omega_using [h]) (n % 32) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

/-- The selector `rowSel` makes of the one-hot word of row `h`. -/
theorem sel_low : ∀ h < 32, ∀ r < 31, (BitVec.ofNat 32 (2 ^ h) <<< (31 - r)) >>> 31 = selv h r := by decide

theorem sel_top : ∀ h < 32, BitVec.ofNat 32 (2 ^ h) >>> 31 = selv h 31 := by decide

/-- 255 at byte `L` of a word, from the byte's multiplier. -/
theorem lane_val : ∀ L < 4, (BitVec.ofNat 32 (2 ^ (8 * L)) <<< 8) - BitVec.ofNat 32 (2 ^ (8 * L)) =
    BitVec.ofNat 32 255 <<< (8 * L) := by decide

theorem cshr_eq (W : BitVec 32) (k : Nat) {b : Nat} (hb : b < 2) :
    cshr W k (BitVec.ofNat 32 b) = W >>> (k * b) := by
  unfold cshr
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega_using [hb]
  · rw [BitVec.mul_zero, BitVec.zero_add, Nat.mul_zero, BitVec.ushiftRight_zero]
  · rw [BitVec.mul_one, BitVec.sub_add_cancel, Nat.mul_one]

theorem pickv_eq (W : BitVec 32) {n : Nat} (h : n < 256) :
    pickv W (BitVec.ofNat 32 n) = (W >>> (8 * (n % 4))) &&& BitVec.ofNat 32 255 := by
  obtain ⟨v0, v1, -⟩ := idx_vals h
  unfold pickv
  rw [v0, v1, cshr_eq _ _ (Nat.mod_lt _ (by decide)), cshr_eq _ _ (Nat.mod_lt _ (by decide)),
    ← BitVec.shiftRight_add, show 8 * (n % 2) + 16 * (n / 2 % 2) = 8 * (n % 4) by omega_using []]

/-- A sum of the rows' words times their selectors is the word of the
index's row, once its row is passed. -/
theorem acc_succ (f : Nat → BitVec 32) (h k : Nat) :
    f k * selv h k + (if h < k then f h else BitVec.ofNat 32 0) =
      if h < k + 1 then f h else BitVec.ofNat 32 0 := by
  rcases Nat.lt_trichotomy h k with hl | rfl | hg
  · rw [selv_ne (Nat.ne_of_lt hl), ite_eq_left hl, ite_eq_left (Nat.lt_succ_of_lt hl), BitVec.mul_zero,
      BitVec.zero_add]
  · rw [selv_self, ite_eq_right (Nat.lt_irrefl _), ite_eq_left (Nat.lt_succ_self _), BitVec.mul_one,
      BitVec.add_zero]
  · rw [selv_ne (Nat.ne_of_gt hg), ite_eq_right (by omega_using [hg]), ite_eq_right (by omega_using [hg]),
      BitVec.mul_zero, BitVec.add_zero]

/-- The word of the index's column, of the two of its row. -/
theorem gather_col (m : Mem) (p : Addr) (n : Nat) :
    (m.readW (p + BitVec.ofNat 64 (8 * (n / 8) + 4)) 32 - m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 32) *
      BitVec.ofNat 32 (n / 4 % 2) + m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * (n / 4))) 32 := by
  rcases Nat.mod_two_eq_zero_or_one (n / 4) with e | e
  · rw [e, BitVec.mul_zero, BitVec.zero_add, show 8 * (n / 8) = 4 * (n / 4) by omega_using [e]]
  · rw [e, BitVec.mul_one, BitVec.sub_add_cancel, show 8 * (n / 8) + 4 = 4 * (n / 4) by omega_using [e]]

/-- The address of a word of the table at `P`, which does not wrap around. -/
theorem off_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) {d : Nat} (hd : d < 256) :
    State.addr (P + BitVec.ofNat 32 d) = State.addr P + BitVec.ofNat 64 d :=
  addr_add (by omega_using [hP, hd])

/-- A register that has its value again is kept. -/
theorem Keep.restore {rs : List Reg} {s s' : State} {a : Reg} (h : Keep (a :: rs) s s')
    (ha : s'.gpr a = s.gpr a) : Keep rs s s' :=
  ⟨fun r hr => by
    by_cases e : r = a
    · rw [e, ha]
    · exact h.1 r fun hm => (List.mem_cons.mp hm).elim e hr, h.2⟩

/-! ## The one-hot word and the selectors -/

theorem oneHot_ok (s : State) :
    WP isa (.block oneHot) s fun t => t.gpr .r10 = ohv (s.gpr .r6) ∧ t.mem = s.mem := by
  unfold oneHot ohStep bit
  arun [Nat.reduceSub, Nat.reduceAdd, Nat.reducePow]
  rfl

theorem ones_ok (s : State) :
    WP isa (.block ones) s fun t => t.gpr .r10 = BitVec.allOnes 32 ∧ t.mem = s.mem := by
  unfold ones
  arun [ones_eq]

theorem rowSel_ok (s : State) {d : Reg} (hd : d = .r11 ∨ d = .r9) {h r : Nat} (hh : h < 32) (hr : r < 32)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (2 ^ h)) :
    WP isa (.block (rowSel d r)) s fun t => (t.gpr d = selv h r ∧ t.mem = s.mem) ∧ Keep [d] s t := by
  unfold rowSel
  by_cases h31 : r = 31
  · rw [ite_eq_left h31, h31]
    rcases hd with rfl | rfl
    · refine WP.keep [.r11] ?_ rfl
      arun [h10]
      exact sel_top h hh
    · refine WP.keep [.r9] ?_ rfl
      arun [h10]
      exact sel_top h hh
  · rw [ite_eq_right h31]
    have hs : 1 ≤ 31 - r ∧ 31 - r ≤ 31 := by omega_using [hr, h31]
    have hr' : r < 31 := by omega_using [hr, h31]
    unfold bit
    rcases hd with rfl | rfl
    · refine WP.keep [.r11] ?_ rfl
      arun [h10, hs]
      exact sel_low h hh r hr'
    · refine WP.keep [.r9] ?_ rfl
      arun [h10, hs]
      exact sel_low h hh r hr'

/-! ## Visiting the rows -/

theorem gather_row (s : State) {h r : Nat} (hh : h < 32) (hr : r < 32)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (2 ^ h)) (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hrd : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12)) 256) :
    WP isa (.block (gatherRow r)) s fun t =>
      t.gpr .r7 = s.mem.readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (8 * r)) 32 * selv h r + s.gpr .r7 ∧
      t.gpr .r8 =
        s.mem.readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (8 * r + 4)) 32 * selv h r + s.gpr .r8 ∧
      t.mem = s.mem ∧ Keep [.r7, .r8, .r9, .r11] s t := by
  unfold gatherRow
  rw [WP.block_append_iff]
  refine WP.mono (rowSel_ok s (.inl rfl) hh hr h10) fun t ⟨⟨t11, tm⟩, tk⟩ => ?_
  have t12 : t.gpr .r12 = s.gpr .r12 := tk.gpr (by decide)
  have ho0 : 8 * r < 4096 := by omega_using [hr]
  have ho1 : 8 * r + 4 < 4096 := by omega_using [hr]
  have a0 := off_addr hfit (d := 8 * r) (by omega_using [hr])
  have a1 := off_addr hfit (d := 8 * r + 4) (by omega_using [hr])
  have hq0 : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r12 + BitVec.ofNat 32 (8 * r))) 4 := by
    rw [tk.2.1, tk.2.2.1, t12, a0]
    exact region_offset _ _ _ _ _ (by omega_using [hr]) (by omega_using [hr]) hrd
  have hq1 : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r12 + BitVec.ofNat 32 (8 * r + 4))) 4 := by
    rw [tk.2.1, tk.2.2.1, t12, a1]
    exact region_offset _ _ _ _ _ (by omega_using [hr]) (by omega_using [hr]) hrd
  refine WP.mono (WP.keep [.r7, .r8, .r9] (Q := fun u =>
      u.gpr .r7 = t.mem.readW (State.addr (t.gpr .r12 + BitVec.ofNat 32 (8 * r))) 32 * selv h r + t.gpr .r7 ∧
      u.gpr .r8 = t.mem.readW (State.addr (t.gpr .r12 + BitVec.ofNat 32 (8 * r + 4))) 32 * selv h r + t.gpr .r8 ∧
      u.mem = t.mem) ?_ rfl) fun u ⟨⟨u7, u8, um⟩, uk⟩ => ?_
  · arun [t11, ho0, ho1, hq0, hq1]
  · refine ⟨?_, ?_, um.trans tm, (tk.trans uk).mono (by decide)⟩
    · rw [u7, tm, t12, a0, tk.gpr (r := .r7) (by decide)]
    · rw [u8, tm, t12, a1, tk.gpr (r := .r8) (by decide)]

/-- After `k` rows: the two words of the index's row `h`, once passed. -/
def GInv (s₀ : State) (h k : Nat) (t : State) : Prop :=
  t.gpr .r7 = (if h < k then s₀.mem.readW (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 (8 * h)) 32
    else BitVec.ofNat 32 0) ∧
  t.gpr .r8 = (if h < k then s₀.mem.readW (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 (8 * h + 4)) 32
    else BitVec.ofNat 32 0) ∧
  t.gpr .r10 = BitVec.ofNat 32 (2 ^ h) ∧ t.mem = s₀.mem ∧ Keep [.r7, .r8, .r9, .r10, .r11] s₀ t

theorem gather_rows (s₀ : State) {h : Nat} (hh : h < 32) (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hrd : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r12)) 256) :
    ∀ n ≤ 32, ∀ s, GInv s₀ h 0 s →
      WP isa (.block ((List.range n).flatMap gatherRow)) s (GInv s₀ h n) := by
  intro n hn
  induction n with
  | zero => intro s hs; exact WP.block_nil hs
  | succ n ih =>
    intro s hs
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) s hs) fun t ⟨t7, t8, t10, tm, tk⟩ => ?_
    have t12 : t.gpr .r12 = s₀.gpr .r12 := tk.gpr (by decide)
    refine WP.mono (gather_row t hh (by omega_using [hn]) t10 (by rw [t12]; exact hfit)
      (by rw [tk.2.1, tk.2.2.1, t12]; exact hrd)) fun u ⟨u7, u8, um, uk⟩ => ?_
    refine ⟨?_, ?_, (uk.gpr (by decide)).trans t10, um.trans tm, (tk.trans uk).mono (by decide)⟩
    · rw [u7, t7, tm, t12]
      exact acc_succ (fun r => s₀.mem.readW (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 (8 * r)) 32) h n
    · rw [u8, t8, tm, t12]
      exact acc_succ (fun r => s₀.mem.readW (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 (8 * r + 4)) 32) h n

/-- What a lookup or replacement needs: the index, all ones, and the table. -/
structure TableEnv (s : State) (idx : Byte) : Prop where
  idx : s.gpr .r6 = idx.setWidth 32
  ones : s.gpr .r10 = BitVec.allOnes 32
  fit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32
  table : InRegions s.wr (State.addr (s.gpr .r12)) 256

theorem TableEnv.read {s : State} {idx : Byte} (h : TableEnv s idx) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12)) 256 := region_in h.table

/-- The word that holds the index's byte, and the one-hot word of its row. -/
theorem gatherWord_ok (s : State) (idx : Byte) (h : TableEnv s idx) :
    WP isa (.block gatherWord) s fun t =>
      t.gpr .r7 = s.mem.readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * (idx.toNat / 4))) 32 ∧
      t.gpr .r10 = BitVec.ofNat 32 (2 ^ (idx.toNat / 8)) ∧ t.mem = s.mem ∧
      Keep [.r7, .r8, .r9, .r10, .r11] s t := by
  have hn := idx.isLt
  obtain ⟨-, -, v2, -, vo⟩ := idx_vals hn
  have hh : idx.toNat / 8 < 32 := by omega_using [hn]
  simp only [gatherWord, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r9, .r10, .r11] (oneHot_ok s) (by decide)) fun t ⟨⟨t10, tm⟩, tk⟩ => ?_
  rw [h.idx, byte32, vo] at t10
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.mov .r7 (imm 0), .mov .r8 (imm 0)]) t fun u =>
      u.gpr .r7 = BitVec.ofNat 32 0 ∧ u.gpr .r8 = BitVec.ofNat 32 0 ∧ u.mem = t.mem := by
    arun
  refine WP.mono (WP.keep [.r7, .r8] h0 (by decide)) fun u ⟨⟨u7, u8, um⟩, uk⟩ => ?_
  have hu : GInv s (idx.toNat / 8) 0 u :=
    ⟨by rw [u7, ite_eq_right (Nat.not_lt_zero _)], by rw [u8, ite_eq_right (Nat.not_lt_zero _)],
      (uk.gpr (by decide)).trans t10, um.trans tm, (tk.trans uk).mono (by decide)⟩
  rw [WP.block_append_iff]
  refine WP.mono (gather_rows s hh h.fit h.read 32 (Nat.le_refl _) u hu) fun v ⟨v7, v8, v10, vm, vk⟩ => ?_
  rw [ite_eq_left hh] at v7 v8
  have h1 : WP isa (.block (bit .r11 .r6 2 ++
      ([.dp .sub .r8 .r8 (.reg .r7), .mla .r7 .r8 .r11 .r7] : List Instr))) v fun w =>
      w.gpr .r7 = (v.gpr .r8 - v.gpr .r7) * bitv (v.gpr .r6) 2 + v.gpr .r7 ∧ w.mem = v.mem := by
    unfold bit
    arun [Nat.reduceSub, Nat.reduceAdd, Nat.reducePow]
    rfl
  refine WP.mono (WP.keep [.r7, .r8, .r11] h1 (by decide)) fun w ⟨⟨w7, wm⟩, wk⟩ => ?_
  refine ⟨?_, (wk.gpr (by decide)).trans v10, wm.trans vm, (vk.trans wk).mono (by decide)⟩
  rw [w7, v7, v8, vk.gpr (r := .r6) (by decide), h.idx, byte32, v2]
  exact gather_col _ _ _

/-! ## The byte of the word -/

theorem pickByte_ok (s : State) :
    WP isa (.block pickByte) s fun t => t.gpr .r7 = pickv (s.gpr .r7) (s.gpr .r6) ∧ t.mem = s.mem := by
  unfold pickByte bit
  arun [Nat.reduceSub, Nat.reduceAdd, Nat.reducePow]
  rfl

/-! ## The lookup -/

theorem lookup_core (s : State) (idx : Byte) (h : TableEnv s idx) :
    WP isa (.block lookup) s fun t =>
      (t.gpr .r7 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
        t.mem = s.mem) ∧ Keep [.r7, .r8, .r9, .r11] s t := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (gatherWord_ok s idx h) fun t ⟨t7, _, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r7, .r9, .r11] (pickByte_ok t) (by decide)) fun u ⟨⟨u7, um⟩, uk⟩ => ?_
  refine WP.mono (WP.keep [.r10] (ones_ok u) (by decide)) fun w ⟨⟨w10, wm⟩, wk⟩ => ?_
  refine ⟨⟨?_, wm.trans (um.trans tm)⟩, Keep.restore (a := .r10) (((tk.trans uk).trans wk).mono (by decide))
    (w10.trans h.ones.symm)⟩
  rw [wk.gpr (r := .r7) (by decide), u7, t7, tk.gpr (r := .r6) (by decide), h.idx, byte32, pickv_eq _ hn,
    dword_byte _ _ (Nat.mod_lt _ (by decide)), row_lane32]

end VG.Proof.Rc4.Arm

end

end

/-! # RC4 on ARMv7: replacing a secret-indexed byte of the table -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Proof.Rc4

/-! ## The word with its byte replaced -/

/-- The word `W` with its byte `L`, which is `b`, replaced by `a`. -/
theorem newWord (W : BitVec 32) (a b : BitVec 8) {L : Nat} (hb : b = W.extractLsb' (8 * L) 8) :
    (W &&& ~~~(BitVec.ofNat 32 255 <<< (8 * L))) ||| (a.setWidth 32 * BitVec.ofNat 32 (2 ^ (8 * L))) =
      W ^^^ ((b ^^^ a).setWidth 32) <<< (8 * L) := by
  rw [show BitVec.ofNat 32 (2 ^ (8 * L)) = BitVec.twoPow 32 (8 * L) from
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, BitVec.toNat_twoPow]), BitVec.mul_twoPow_eq_shiftLeft, hb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h255 : ∀ j, (BitVec.ofNat 32 255).getLsbD j = decide (j < 8) := fun j => by
    change Nat.testBit 255 j = decide (j < 8)
    exact Nat.testBit_two_pow_sub_one 8 j
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', h255, hi, decide_true, Bool.true_and]
  by_cases h1 : i < 8 * L
  · simp only [decide_eq_true h1, Bool.not_true, Bool.false_and, Bool.and_true, Bool.or_false, Bool.xor_false,
      Bool.not_false]
  · have h3 : i - 8 * L < 32 := by omega_using [hi]
    by_cases h2 : i - 8 * L < 8
    · simp only [decide_eq_false h1, decide_eq_true h2, decide_eq_true h3, Bool.not_false, Bool.true_and,
        Bool.not_true, Bool.and_false, Bool.false_or, show 8 * L + (i - 8 * L) = i by omega_using [h1]]
      cases W.getLsbD i <;> cases a.getLsbD (i - 8 * L) <;> rfl
    · simp only [decide_eq_false h1, decide_eq_false h2, Bool.not_false, Bool.false_and, Bool.and_true,
        BitVec.getLsbD_of_ge a _ (Nat.le_of_not_lt h2), Bool.and_false, Bool.or_false, Bool.xor_false]

theorem deltav_eq (W : BitVec 32) (a b : BitVec 8) {n : Nat} (h : n < 256)
    (hb : b = W.extractLsb' (8 * (n % 4)) 8) :
    deltav W (a.setWidth 32) (BitVec.ofNat 32 n) = (W ^^^ ((b ^^^ a).setWidth 32) <<< (8 * (n % 4))) - W := by
  obtain ⟨-, -, -, vm, -⟩ := idx_vals h
  unfold deltav
  rw [vm, lane_val _ (Nat.mod_lt _ (by decide)), newWord W a b hb]

theorem loadI_ok (s : State) (ii : Byte) (h4 : s.gpr .r4 = ii.setWidth 32)
    (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12)) 256) :
    WP isa (.block loadI) s fun t =>
      t.gpr .r11 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      Keep [.r9, .r11] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + ii.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [idx_addr hfit ii]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hr
  refine WP.mono (WP.keep (Q := fun t =>
      t.gpr .r11 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      t.mem = s.mem) [.r9, .r11] ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold loadI
  arun [h4, hi]
  rw [idx_addr hfit ii]

theorem deltaWord_ok (s : State) (ii : Byte) (h4 : s.gpr .r4 = ii.setWidth 32)
    (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hrd : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12)) 256) :
    WP isa (.block deltaWord) s fun t =>
      t.gpr .r8 = deltav (s.gpr .r7)
        ((s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)).setWidth 32) (s.gpr .r6) ∧
      t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + ii.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [idx_addr hfit ii]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hrd
  unfold deltaWord loadI bit
  arun [h4, hi, Nat.reduceSub, Nat.reduceAdd, Nat.reducePow]
  rw [idx_addr hfit ii]
  rfl

theorem splitDelta_ok (s : State) :
    WP isa (.block splitDelta) s fun t =>
      t.gpr .r11 = s.gpr .r8 * bitv (s.gpr .r6) 2 ∧
      t.gpr .r8 = s.gpr .r8 - s.gpr .r8 * bitv (s.gpr .r6) 2 ∧ t.mem = s.mem := by
  unfold splitDelta bit
  arun [Nat.reduceSub, Nat.reduceAdd, Nat.reducePow]
  exact ⟨rfl, rfl⟩

/-! ## Storing back every word -/

/-- Storing the word read: nothing changes. -/
theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, show 32 / 8 = 4 from rfl]
  split
  · rename_i h
    rw [← Mem.readW_byte m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl

/-- The word at `a` plus `d`. -/
def addW (m : Mem) (a : Addr) (d : BitVec 32) : Mem := m.writeW a (d + m.readW a 32)

theorem addW_zero (m : Mem) (a : Addr) : addW m a (BitVec.ofNat 32 0) = m := by
  unfold addW
  rw [BitVec.zero_add, writeW_readW]

/-- The two words of row `r` plus `d0` and `d1`. -/
def scatRow (m : Mem) (p : Addr) (r : Nat) (d0 d1 : BitVec 32) : Mem :=
  addW (addW m (p + BitVec.ofNat 64 (8 * r)) d0) (p + BitVec.ofNat 64 (8 * r + 4)) d1

/-- The memory after `k` rows: row `h` changed, once passed. -/
def scat (m : Mem) (p : Addr) (h : Nat) (d0 d1 : BitVec 32) (k : Nat) : Mem :=
  if h < k then scatRow m p h d0 d1 else m

theorem scat_succ (m : Mem) (p : Addr) (h : Nat) (d0 d1 : BitVec 32) (k : Nat) :
    scatRow (scat m p h d0 d1 k) p k (d0 * selv h k) (d1 * selv h k) = scat m p h d0 d1 (k + 1) := by
  unfold scat
  rcases Nat.lt_trichotomy h k with hl | rfl | hg
  · rw [selv_ne (Nat.ne_of_lt hl), ite_eq_left hl, ite_eq_left (Nat.lt_succ_of_lt hl), BitVec.mul_zero,
      BitVec.mul_zero]
    unfold scatRow
    rw [addW_zero, addW_zero]
  · rw [selv_self, ite_eq_right (Nat.lt_irrefl _), ite_eq_left (Nat.lt_succ_self _), BitVec.mul_one,
      BitVec.mul_one]
  · rw [selv_ne (Nat.ne_of_gt hg), ite_eq_right (by omega_using [hg]), ite_eq_right (by omega_using [hg]),
      BitVec.mul_zero, BitVec.mul_zero]
    unfold scatRow
    rw [addW_zero, addW_zero]

/-- The difference to the index's column changes its word alone. -/
theorem scatRow_col (m : Mem) (p : Addr) (n : Nat) (d : BitVec 32) :
    scatRow m p (n / 8) (d - d * BitVec.ofNat 32 (n / 4 % 2)) (d * BitVec.ofNat 32 (n / 4 % 2)) =
      addW m (p + BitVec.ofNat 64 (4 * (n / 4))) d := by
  unfold scatRow
  rcases Nat.mod_two_eq_zero_or_one (n / 4) with e | e
  · rw [e, BitVec.mul_zero, BitVec.sub_zero, addW_zero, show 8 * (n / 8) = 4 * (n / 4) by omega_using [e]]
  · rw [e, BitVec.mul_one, BitVec.sub_self, addW_zero, show 8 * (n / 8) + 4 = 4 * (n / 4) by omega_using [e]]

theorem scatter_row (s : State) {h r : Nat} (hh : h < 32) (hr : r < 32)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (2 ^ h)) (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hwr : InRegions s.wr (State.addr (s.gpr .r12)) 256) :
    WP isa (.block (scatterRow r)) s fun t =>
      t.mem = scatRow s.mem (State.addr (s.gpr .r12)) r (s.gpr .r8 * selv h r) (s.gpr .r11 * selv h r) ∧
      Keep [.r6, .r9] s t := by
  unfold scatterRow
  rw [WP.block_append_iff]
  refine WP.mono (rowSel_ok s (.inr rfl) hh hr h10) fun t ⟨⟨t9, tm⟩, tk⟩ => ?_
  have t12 : t.gpr .r12 = s.gpr .r12 := tk.gpr (by decide)
  have ho0 : 8 * r < 4096 := by omega_using [hr]
  have ho1 : 8 * r + 4 < 4096 := by omega_using [hr]
  have a0 := off_addr hfit (d := 8 * r) (by omega_using [hr])
  have a1 := off_addr hfit (d := 8 * r + 4) (by omega_using [hr])
  have hw0 : InRegions t.wr (State.addr (t.gpr .r12 + BitVec.ofNat 32 (8 * r))) 4 := by
    rw [tk.2.2.1, t12, a0]
    exact region_offset _ _ _ _ _ (by omega_using [hr]) (by omega_using [hr]) hwr
  have hw1 : InRegions t.wr (State.addr (t.gpr .r12 + BitVec.ofNat 32 (8 * r + 4))) 4 := by
    rw [tk.2.2.1, t12, a1]
    exact region_offset _ _ _ _ _ (by omega_using [hr]) (by omega_using [hr]) hwr
  have hq0 := region_in (rs := t.rd) hw0
  have hq1 := region_in (rs := t.rd) hw1
  refine WP.mono (WP.keep [.r6] (Q := fun u =>
      u.mem = scatRow t.mem (State.addr (t.gpr .r12)) r (t.gpr .r8 * selv h r) (t.gpr .r11 * selv h r))
      ?_ rfl) fun u ⟨um, uk⟩ => ?_
  · arun [t9, ho0, ho1, hq0, hq1, hw0, hw1]
    rw [t12, a0, a1]
    rfl
  · refine ⟨?_, (tk.trans uk).mono (by decide)⟩
    rw [um, tm, t12, tk.gpr (r := .r8) (by decide), tk.gpr (r := .r11) (by decide)]

theorem scatter_rows (s₀ : State) {h : Nat} (hh : h < 32) (d0 d1 : BitVec 32)
    (h8 : s₀.gpr .r8 = d0) (h11 : s₀.gpr .r11 = d1) (h10 : s₀.gpr .r10 = BitVec.ofNat 32 (2 ^ h))
    (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32) (hwr : InRegions s₀.wr (State.addr (s₀.gpr .r12)) 256) :
    ∀ n ≤ 32, ∀ s, s.mem = s₀.mem → Keep [.r6, .r9] s₀ s →
      WP isa (.block ((List.range n).flatMap scatterRow)) s fun t =>
        t.mem = scat s₀.mem (State.addr (s₀.gpr .r12)) h d0 d1 n ∧ Keep [.r6, .r9] s₀ t := by
  intro n hn
  induction n with
  | zero =>
    intro s hm hk
    refine WP.block_nil ⟨?_, hk⟩
    rw [hm]; unfold scat; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s hm hk
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) s hm hk) fun t ⟨tm, tk⟩ => ?_
    have t12 : t.gpr .r12 = s₀.gpr .r12 := tk.gpr (by decide)
    refine WP.mono (scatter_row t hh (by omega_using [hn]) ((tk.gpr (by decide)).trans h10)
      (by rw [t12]; exact hfit) (by rw [tk.2.2.1, t12]; exact hwr)) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, (tk.trans uk).mono (by decide)⟩
    rw [um, tm, t12, tk.gpr (r := .r8) (by decide), tk.gpr (r := .r11) (by decide), h8, h11, scat_succ]

/-! ## The replacement -/

theorem replace_core (s : State) (idx ii : Byte) (h : TableEnv s idx)
    (h4 : s.gpr .r4 = ii.setWidth 32) :
    WP isa (.block replace) s fun t =>
      t.gpr .r7 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
      t.mem = s.mem.write (State.addr (s.gpr .r12) + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)) ∧
      Keep [.r6, .r7, .r8, .r9, .r11] s t := by
  have hn := idx.isLt
  obtain ⟨-, -, v2, -, -⟩ := idx_vals hn
  have hh : idx.toNat / 8 < 32 := by omega_using [hn]
  have hL : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  let p := State.addr (s.gpr .r12)
  let W := s.mem.readW (p + BitVec.ofNat 64 (4 * (idx.toNat / 4))) 32
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let a := s.mem (p + BitVec.ofNat 64 ii.toNat)
  have hb : b = W.extractLsb' (8 * (idx.toNat % 4)) 8 := by
    rw [← Mem.readW_byte _ _ hL, row_lane32]
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (gatherWord_ok s idx h) fun t ⟨t7, t10, tm, tk⟩ => ?_
  have t12 : t.gpr .r12 = s.gpr .r12 := tk.gpr (by decide)
  have t6 : t.gpr .r6 = BitVec.ofNat 32 idx.toNat := by rw [tk.gpr (by decide), h.idx, byte32]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .r9, .r11] (deltaWord_ok t ii ((tk.gpr (by decide)).trans h4)
    (by rw [t12]; exact h.fit) (by rw [tk.2.1, tk.2.2.1, t12]; exact h.read)) (by decide))
    fun u ⟨⟨u8, um⟩, uk⟩ => ?_
  rw [t7, tm, t12, t6, deltav_eq W a b hn hb] at u8
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r7, .r9, .r11] (pickByte_ok u) (by decide)) fun v ⟨⟨v7, vm⟩, vk⟩ => ?_
  rw [uk.gpr (r := .r7) (by decide), t7, uk.gpr (r := .r6) (by decide), t6, pickv_eq _ hn, dword_byte _ _ hL,
    row_lane32] at v7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .r9, .r11] (splitDelta_ok v) (by decide)) fun w ⟨⟨w11, w8, wm⟩, wk⟩ => ?_
  rw [vk.gpr (r := .r8) (by decide), u8, vk.gpr (r := .r6) (by decide), uk.gpr (r := .r6) (by decide), t6,
    v2] at w11 w8
  have k₁ : Keep [.r7, .r8, .r9, .r10, .r11] s w := (((tk.trans uk).trans vk).trans wk).mono (by decide)
  have w12 : w.gpr .r12 = s.gpr .r12 := k₁.gpr (by decide)
  have w10 : w.gpr .r10 = BitVec.ofNat 32 (2 ^ (idx.toNat / 8)) := by
    rw [wk.gpr (by decide), vk.gpr (by decide), uk.gpr (by decide), t10]
  have wms : w.mem = s.mem := wm.trans (vm.trans (um.trans tm))
  rw [WP.block_append_iff]
  refine WP.mono (scatter_rows w hh _ _ w8 w11 w10 (by rw [w12]; exact h.fit)
    (by rw [k₁.2.2.1, w12]; exact h.table) 32 (Nat.le_refl _) w rfl (Keep.refl _ _)) fun x ⟨xm, xk⟩ => ?_
  refine WP.mono (WP.keep [.r10] (ones_ok x) (by decide)) fun y ⟨⟨y10, ym⟩, yk⟩ => ?_
  refine ⟨?_, ?_, Keep.restore (a := .r10) (((k₁.trans xk).trans yk).mono (by decide)) (y10.trans h.ones.symm)⟩
  · rw [yk.gpr (r := .r7) (by decide), xk.gpr (r := .r7) (by decide), wk.gpr (r := .r7) (by decide), v7]
  · rw [ym, xm, wms, w12]
    unfold scat
    rw [ite_eq_left hh, scatRow_col]
    unfold addW
    rw [BitVec.sub_add_cancel, writeW_byte32, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.Arm

end

end

/-! ### `Rc4.Arm.Schedule`, which only this module used -/

section

/-! # RC4 on ARMv7: key scheduling -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- The address of byte `r` of the table at `P`. -/
theorem idx_addr' {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) {r : Nat} (hr : r < 256) :
    State.addr (P + BitVec.ofNat 32 r + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 r := by
  rw [BitVec.add_zero]
  exact addr_add (by omega_using [hP, hr])

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem (State.addr (s₀.gpr .r12)) r ∧ Keep [.r4, .r9] s₀ s ∧
    s.gpr .r4 = BitVec.ofNat 32 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr (State.addr (s₀.gpr .r12)) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.z = (BitVec.ofNat 32 r + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32) := by
  obtain ⟨hm, hk, h4⟩ := h
  obtain h12 : s.gpr .r12 = s₀.gpr .r12 := hk.gpr (by decide)
  obtain hw : InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 r + BitVec.ofNat 32 0)) 1 := by
    rw [h12, idx_addr' hfit hr, hk.2.2.1]
    exact region_offset _ _ _ _ _ (by omega_using [hr]) (by omega_using [hr]) hp
  obtain hadd : BitVec.ofNat 32 r + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
    rw [← BitVec.ofNat_add]
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = identityMem s₀.mem (State.addr (s₀.gpr .r12)) (r + 1) ∧
      t.gpr .r4 = BitVec.ofNat 32 (r + 1) ∧
      t.z = (BitVec.ofNat 32 r + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32)) [.r4, .r9] ?_
    (by decide)) fun t ⟨⟨tm, t4, tz⟩, tk⟩ => ⟨⟨tm, (hk.trans tk).mono (by decide), t4⟩, tz⟩
  unfold identityStep
  arun [h4, hw, hadd]
  rw [h12, idx_addr' hfit hr, hm, writeW_byte8, ofNat_low32, identityMem_store _ _ _ hr]

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr (State.addr (s₀.gpr .r12)) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) .ne) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t hj hfit hp ht) fun u ⟨hu, hz⟩ => ?_
  obtain hadd : BitVec.ofNat 32 j + BitVec.ofNat 32 1 = BitVec.ofNat 32 (j + 1) := by
    rw [← BitVec.ofNat_add]
  rw [hadd] at hz
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [eval_ne, hz, hend]
    rfl
  · right
    obtain hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega_using [hj, hend, h']
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    rw [eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

/-! ## One round -/

/-- What the key schedule keeps throughout: the table at `P`, the key at `K`
(`Lk` bytes), all ones. -/
structure ScheduleEnv (s : State) (P K Lk : BitVec 32) : Prop where
  p : s.gpr .r12 = P
  k : s.gpr .r0 = K
  l : s.gpr .r1 = Lk
  ones : s.gpr .r10 = BitVec.allOnes 32
  len : 1 ≤ Lk.toNat ∧ Lk.toNat ≤ 256
  fit : P.toNat + 256 ≤ 2 ^ 32
  table : InRegions s.wr (State.addr P) 256
  key : InRegions (s.rd ++ s.wr) (State.addr K) Lk.toNat
  keyFit : K.toNat + Lk.toNat ≤ 2 ^ 32
  keySep : Mem.Sep (State.addr K) Lk.toNat (State.addr P) 256

theorem ScheduleEnv.keep {s t : State} {P K Lk : BitVec 32} (h : ScheduleEnv s P K Lk)
    {rs : List Reg} (hk : Keep rs s t) (hrs : ∀ r ∈ rs, r ≠ .r12 ∧ r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r10) :
    ScheduleEnv t P K Lk :=
  { h with
    p := (hk.gpr fun hm => (hrs _ hm).1 rfl).trans h.p
    k := (hk.gpr fun hm => (hrs _ hm).2.1 rfl).trans h.k
    l := (hk.gpr fun hm => (hrs _ hm).2.2.1 rfl).trans h.l
    ones := (hk.gpr fun hm => (hrs _ hm).2.2.2 rfl).trans h.ones
    table := by rw [hk.2.2.1]; exact h.table
    key := by rw [hk.2.1, hk.2.2.1]; exact h.key }

theorem ScheduleEnv.tableEnv {s : State} {P K Lk : BitVec 32} (h : ScheduleEnv s P K Lk)
    {idx : Byte} (h6 : s.gpr .r6 = idx.setWidth 32) : TableEnv s idx :=
  ⟨h6, h.ones, by rw [h.p]; exact h.fit, by rw [h.p]; exact h.table⟩

theorem schedule_before (s : State) (i j : Byte) {P K Lk : BitVec 32} {o : Nat}
    (he : ScheduleEnv s P K Lk) (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 o) (ho : o < Lk.toNat) :
    WP isa (.block (loadI ++ ([.dp .add .r5 .r5 (.reg .r11), .dp .add .r9 .r0 (.reg .r2),
      .ldrb .r9 .r9 0, .dp .add .r5 .r5 (.reg .r9), .dp .and .r5 .r5 (imm 255),
      .mov .r6 (.reg .r5)] : List Instr))) s
      fun t => t.gpr .r5 = (j + s.mem (State.addr P + BitVec.ofNat 64 i.toNat) +
          s.mem (State.addr K + BitVec.ofNat 64 o)).setWidth 32 ∧ t.gpr .r6 = t.gpr .r5 ∧
        Keep [.r5, .r6, .r9, .r11] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok s i h4 (by rw [he.p]; exact he.fit) (by rw [he.p]; exact region_in he.table))
    fun t ⟨t11, tk, tm⟩ => ?_
  rw [he.p] at t11
  obtain t5 : t.gpr .r5 = j.setWidth 32 := (tk.gpr (by decide)).trans h5
  obtain t0 : t.gpr .r0 = K := (tk.gpr (by decide)).trans he.k
  obtain t2 : t.gpr .r2 = BitVec.ofNat 32 o := (tk.gpr (by decide)).trans h2
  obtain hka : State.addr (K + BitVec.ofNat 32 o + BitVec.ofNat 32 0) =
      State.addr K + BitVec.ofNat 64 o := by
    rw [BitVec.add_zero]
    exact addr_add (by have := he.keyFit; omega_using [ho, this])
  obtain hk : InRegions (t.rd ++ t.wr) (State.addr (K + BitVec.ofNat 32 o + BitVec.ofNat 32 0)) 1 := by
    rw [hka, tk.2.1, tk.2.2.1]
    exact region_offset _ _ _ _ _ (by have := he.keyFit; omega_using [ho]) (by omega_using [ho]) he.key
  refine WP.mono (WP.keep (Q := fun u => u.gpr .r5 = (j + s.mem (State.addr P +
      BitVec.ofNat 64 i.toNat) + s.mem (State.addr K + BitVec.ofNat 64 o)).setWidth 32 ∧
      u.gpr .r6 = u.gpr .r5 ∧ u.mem = s.mem) [.r5, .r6, .r9] ?_ (by decide))
    fun u ⟨⟨u5, u6, um⟩, uk⟩ => ⟨u5, u6, (tk.trans uk).mono (by decide), um⟩
  arun [t5, t11, t0, t2, hk, tm]
  rw [hka, byte_add3_32]

/-- The key offset after `cmp`, `adc` and `and`. -/
theorem next_off (x L : BitVec 32) :
    x &&& (BitVec.allOnes 32 + BitVec.ofNat 32 0 +
      BitVec.ofNat 32 (decide (L.toNat ≤ x.toNat)).toNat) =
      if x.toNat < L.toNat then x else 0#32 := by
  rw [adc_mask']
  by_cases h : x.toNat < L.toNat
  · rw [ite_eq_right (by simp only [decide_eq_true_eq]; omega_using [h]), ite_eq_left h]
  · rw [ite_eq_left (by simp only [decide_eq_true_eq]; omega_using [h]), ite_eq_right h]
    rfl

theorem schedule_after (s : State) (i b : Byte) {P K Lk : BitVec 32}
    (he : ScheduleEnv s P K Lk) (h4 : s.gpr .r4 = i.setWidth 32) (h7 : s.gpr .r7 = b.setWidth 32) :
    WP isa (.block [.dp .add .r2 .r2 (imm 1), .cmp .r2 (.reg .r1), .adc .r9 .r10 (imm 0),
      .dp .and .r2 .r2 (.reg .r9), .dp .add .r9 .r12 (.reg .r4), .strb .r7 .r9 0,
      .dp .add .r4 .r4 (imm 1), .cmp .r4 (imm 256)]) s fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r2 = (if (s.gpr .r2 + BitVec.ofNat 32 1).toNat < Lk.toNat then
        s.gpr .r2 + BitVec.ofNat 32 1 else 0#32) ∧
      t.gpr .r4 = i.setWidth 32 + BitVec.ofNat 32 1 ∧
      t.z = (i.setWidth 32 + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32) ∧
      Keep [.r2, .r4, .r9] s t := by
  obtain hw : InRegions s.wr (State.addr (P + i.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [idx_addr he.fit i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_using []) (by have := i.isLt; omega_using []) he.table
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r2 = (if (s.gpr .r2 + BitVec.ofNat 32 1).toNat < Lk.toNat then
        s.gpr .r2 + BitVec.ofNat 32 1 else 0#32) ∧
      t.gpr .r4 = i.setWidth 32 + BitVec.ofNat 32 1 ∧
      t.z = (i.setWidth 32 + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32)) [.r2, .r4, .r9] ?_
    (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  arun [he.p, he.l, he.ones, h4, h7, hw]
  rw [idx_addr he.fit i, writeW_byte8, low_byte32, next_off]
  conj_rfl

/-- One key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte) {P K Lk : BitVec 32} {o : Nat}
    (he : ScheduleEnv s P K Lk) (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 o) (ho : o < Lk.toNat) :
    let p := State.addr P
    let a := s.mem (p + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (State.addr K + BitVec.ofNat 64 o)
    let b := s.mem (p + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write
        (p + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r2 = (if (BitVec.ofNat 32 o + BitVec.ofNat 32 1).toNat < Lk.toNat then
        BitVec.ofNat 32 o + BitVec.ofNat 32 1 else 0#32) ∧
      t.gpr .r5 = jj.setWidth 32 ∧ t.gpr .r4 = i.setWidth 32 + BitVec.ofNat 32 1 ∧
      t.z = (i.setWidth 32 + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32) ∧
      Keep [.r2, .r4, .r5, .r6, .r7, .r8, .r9, .r11] s t := by
  intro p a jj b
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (schedule_before s i j he h4 h5 h2 ho) fun t ⟨t5, t6, tk, tm⟩ => ?_
  obtain het := he.keep tk (by decide)
  refine WP.mono (replace_core t jj i (het.tableEnv (t6.trans t5)) ((tk.gpr (by decide)).trans h4))
    fun u ⟨u7, um, uk⟩ => ?_
  rw [tm, het.p] at u7 um
  obtain heu := het.keep uk (by decide)
  refine WP.mono (schedule_after u i b heu ((uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans h4))
    u7) fun v ⟨vm, v2, v4, vz, vk⟩ => ?_
  refine ⟨by rw [vm, um], ?_, (vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t5), v4, vz,
    ((tk.trans uk).trans vk).mono (by decide)⟩
  rw [v2, (uk.gpr (by decide) : u.gpr .r2 = t.gpr .r2), (tk.gpr (by decide) : t.gpr .r2 = s.gpr .r2), h2]

/-- The key bytes, at `K` (32-bit), `Lk` of them. -/
def keyOf (m : Mem) (K Lk : BitVec 32) : List Byte := bytesAt m (State.addr K) Lk.toNat

structure ScheduleInv (s₀ : State) (P K Lk : BitVec 32) (r : Nat) (s : State) : Prop where
  frame : TableFrame (State.addr P) s₀.mem s.mem
  table : (contextAt s.mem (State.addr P)).table = (schedulePrefix (keyOf s₀.mem K Lk) r).1
  j : s.gpr .r5 = (schedulePrefix (keyOf s₀.mem K Lk) r).2.setWidth 32
  i : s.gpr .r4 = BitVec.ofNat 32 r
  off : s.gpr .r2 = BitVec.ofNat 32 (r % Lk.toNat)
  keep : Keep [.r2, .r4, .r5, .r6, .r7, .r8, .r9, .r11] s₀ s

theorem schedule_inv_step (s₀ s : State) {P K Lk : BitVec 32} {r : Nat} (hr : r < 256)
    (he₀ : ScheduleEnv s₀ P K Lk) (h : ScheduleInv s₀ P K Lk r s) :
    WP isa (.block scheduleStep) s fun t => ScheduleInv s₀ P K Lk (r + 1) t ∧
      t.z = (BitVec.ofNat 32 (r + 1) - BitVec.ofNat 32 256 == 0#32) := by
  let key := keyOf s₀.mem K Lk
  let st := schedulePrefix key r
  have hlen := he₀.len
  obtain he := he₀.keep h.keep (by decide)
  obtain hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  obtain hi : s.gpr .r4 = (BitVec.ofNat 8 r).setWidth 32 := by
    rw [h.i, byte32, hrt]
  obtain hmod := Nat.mod_lt r (show 0 < Lk.toNat by omega_using [hlen])
  obtain hkeybyte : s.mem (State.addr K + BitVec.ofNat 64 (r % Lk.toNat)) =
      key.getD (r % key.length) 0 := by
    obtain hsep := he₀.keySep (State.addr K + BitVec.ofNat 64 (r % Lk.toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hmod])]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyOf]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  obtain htablebyte : s.mem (State.addr P + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    obtain hg := table_get s.mem (State.addr P) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (schedule_step s _ _ he hi h.j h.off hmod)
    fun t ⟨tm, t2, t5, t4, tz, tk⟩ => ?_
  obtain hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  obtain hcast : (BitVec.ofNat 8 r).setWidth 32 + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
    rw [byte32, hrt, ← BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (h.keep.trans tk).mono (by decide)⟩, ?_⟩
  · rw [tm]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, table_swap, h.table, hnext, hrt]
    rw [htablebyte, hkeybyte]
  · rw [t5, hrt, htablebyte, hkeybyte, hnext]
  · rw [t4, hcast]
  · rw [t2]
    exact key_next32 r _ (by omega_using [hlen]) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) {P K Lk : BitVec 32} {r : Nat} (hr : r < 256)
    (he₀ : ScheduleEnv s₀ P K Lk) (h : ScheduleInv s₀ P K Lk r s) :
    WP isa (.loop (.block scheduleStep) .ne) s (ScheduleInv s₀ P K Lk 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ P K Lk j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t hj he₀ ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [eval_ne, hz, hend]
    rfl
  · right
    obtain hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega_using [hj, hend, h']
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    rw [eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

end VG.Proof.Rc4.Arm

end

end


/-! # RC4 on ARMv7: checked initialization -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-! ## Our caller's registers -/

theorem saved_slots : Spill.Slots 0 32 saved := by decide

theorem saved_restorable : Spill.Restorable .r3 saved := by decide

/-- The registers `saved` lists. -/
theorem saved_regs : saved.map Prod.fst = [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := rfl

/-- Saving the registers in `scratch` at `S`. -/
theorem save_ok (s : State) (hfit : (s.gpr .r3).toNat + 64 ≤ 2 ^ 32)
    (hw : InRegions s.wr (State.addr (s.gpr .r3)) 64) :
    WP isa (.block save) s fun t =>
      t.mem = Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (Spill.save_block_ok saved_slots (by omega_arith) fun d _ hd =>
    region_offset _ _ _ _ _ (by omega_arith) (by omega_arith) hw) (by decide)) fun t ⟨h, hk⟩ => ⟨h.2.2.2, hk⟩

/-- What saving changes: the first 32 bytes of `scratch`. -/
theorem save_frame (m : Mem) (S : Addr) (g : Reg → BitVec 32) :
    Frame [⟨S, 64⟩] m (Spill.saveMem m S g saved) :=
  Spill.saveMem_frame _ _ _ (by decide) _ (by decide)

/-- The saved registers survive writes to the table. -/
theorem saved_after {m m' : Mem} {S P : Addr} {g : Reg → BitVec 32}
    (h : Spill.Saved m S g saved) (hf : Frame [⟨P, 258⟩] m m')
    (hd : Region.Disjoint ⟨P, 258⟩ ⟨S, 64⟩) : Spill.Saved m' S g saved := by
  refine h.frame saved_slots hf fun r hr => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  exact (hd.symm.sub_left (by
    rw [BitVec.add_zero]
    exact Region.sub_prefix (by decide)))

/-- Restoring them. -/
theorem restore_ok (s : State) {g : Reg → BitVec 32} (hfit : (s.gpr .r3).toNat + 64 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3)) 64)
    (hs : Spill.Saved s.mem (State.addr (s.gpr .r3)) g saved) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ saved.map Prod.fst, t.gpr r = g r) ∧
      Keep [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧ t.mem = s.mem := by
  refine WP.mono (Spill.restore_block_ok saved_slots saved_restorable (by omega_arith)
    (fun d _ hd => region_offset _ _ _ _ _ (by omega_arith) (by omega_arith) hr) hs)
    fun t ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨fun r hr => Spill.restored_reg h₁ hr,
      ⟨fun r hr => h₂ r (by rw [saved_regs]; exact hr), h₄, h₅, h₆⟩, h₃⟩

/-! ## Initialization -/

theorem init_finish (s : State) {P : BitVec 32} (h12 : s.gpr .r12 = P)
    (hfit : P.toNat + 258 ≤ 2 ^ 32) (hp : InRegions s.wr (State.addr P) 258) :
    WP isa (.block [.mov .r9 (imm 0), .strb .r9 .r12 256, .strb .r9 .r12 257]) s
      fun t => t.mem = (s.mem.write (State.addr P + 256#64) 1 0#8).write
          (State.addr P + 257#64) 1 0#8 ∧ Keep [.r9] s t := by
  obtain a256 : State.addr (P + BitVec.ofNat 32 256) = State.addr P + 256#64 := addr_add (by omega_arith)
  obtain a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega_arith)
  obtain h256 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 256)) 1 := by
    rw [a256]; exact region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact region_offset _ _ _ 257 1 (by decide) (by decide) hp
  refine WP.mono (WP.keep (Q := fun t => t.mem = (s.mem.write (State.addr P + 256#64) 1 0#8).write
      (State.addr P + 257#64) 1 0#8) [.r9] ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h, hk⟩
  arun [h12, h256, h257]
  rw [a256, a257, writeW_byte8, writeW_byte8]
  rfl

theorem init_valid (s : State) (hs : initC.pre s)
    (hlen : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) :
    WP isa initValid s fun t => t.gpr .r0 = 0#32 ∧
      contextAt t.mem (State.addr (s.gpr .r2)) =
        { table := keySchedule (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat),
          i := 0, j := 0 } ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  obtain ⟨hrd, hwr, kc, ks, cs, kfit, cfit, sfit⟩ := hs
  generalize hP : s.gpr .r2 = P at hwr kc cs cfit ⊢
  generalize hK : s.gpr .r0 = K at hrd kc ks kfit ⊢
  generalize hL : s.gpr .r1 = Lk at hrd kc ks kfit hlen ⊢
  generalize hS : s.gpr .r3 = Sc at hwr ks cs sfit
  obtain hctx : InRegions s.wr (State.addr P) 258 := ⟨_, by rw [hwr]; exact List.mem_cons_self,
    Region.contains_self _ _⟩
  obtain hscr : InRegions s.wr (State.addr Sc) 64 := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  obtain htab : InRegions s.wr (State.addr P) 256 := by
    obtain h' := region_offset _ _ _ 0 256 (by decide) (by decide) hctx
    simpa only [BitVec.add_zero] using h'
  unfold initValid
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s (by rw [hS]; exact sfit) (by rw [hS]; exact hscr))
    fun a ⟨ham, hak⟩ => ?_
  rw [hS] at ham
  obtain haf : Frame [⟨State.addr Sc, 64⟩] s.mem a.mem := by rw [ham]; exact save_frame _ _ _
  obtain hb : WP isa (.block [.mov .r12 (.reg .r2), .mov .r4 (imm 0)]) a fun b =>
      b.gpr .r12 = P ∧ b.gpr .r4 = 0#32 ∧ b.mem = a.mem := by
    arun [hak.gpr (r := .r2) (by decide), hP]
  refine WP.mono (WP.keep [.r12, .r4] hb (by decide)) fun b ⟨⟨hb12, hb4, hbm⟩, hbk⟩ => ?_
  obtain kb : Keep [.r12, .r4] s b := (hak.trans hbk).mono (by decide)
  obtain hpb : InRegions b.wr (State.addr (b.gpr .r12)) 256 := by rw [kb.2.2.1, hb12]; exact htab
  obtain hfit : (b.gpr .r12).toNat + 256 ≤ 2 ^ 32 := by rw [hb12]; omega_arith
  obtain hib : IdentityInv b 0 b := ⟨by rw [identityMem_zero], Keep.refl _ _, hb4⟩
  refine WP.seq (WP.mono (identity_loop b b (by decide) hfit hpb hib) fun c hc => ?_)
  obtain ⟨hcm, hck, _⟩ := hc
  obtain hd : WP isa (.block (([.mov .r4 (imm 0), .mov .r2 (imm 0), .mov .r5 (imm 0)] : List Instr) ++
      ones)) c fun d => d.gpr .r4 = 0#32 ∧ d.gpr .r2 = 0#32 ∧ d.gpr .r5 = 0#32 ∧
        d.gpr .r10 = BitVec.allOnes 32 ∧ d.mem = c.mem := by
    unfold ones
    arun [ones_eq]
  refine WP.seq (WP.mono (WP.keep [.r4, .r2, .r5, .r10] hd (by decide))
    fun d ⟨⟨hd4, hd2, hd5, hd10, hdm⟩, hdk⟩ => ?_)
  obtain kd : Keep [.r4, .r2, .r5, .r10, .r9, .r12] s d :=
    ((kb.trans (hck.trans hdk)).mono (by decide))
  obtain hd12 : d.gpr .r12 = P := ((hck.trans hdk).gpr (by decide)).trans hb12
  obtain hdmem : d.mem = identityMem a.mem (State.addr P) 256 := by rw [hdm, hcm, hbm, hb12]
  -- The key is untouched by the saves and the identity permutation.
  obtain hkey : keyOf d.mem K Lk = bytesAt s.mem (State.addr K) Lk.toNat := by
    unfold keyOf bytesAt
    apply List.map_congr_left
    intro k hk
    obtain hk' := List.mem_range.mp hk
    obtain hin : (⟨State.addr K, Lk.toNat⟩ : Region).Contains (State.addr K + BitVec.ofNat 64 k) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [hdmem, identityMem_frame _ _ _ (by decide) _ fun hl =>
      kc _ hin (by simp only [Region.Contains] at hl ⊢; omega_arith)]
    exact haf _ fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ks _ hin
  obtain hen : ScheduleEnv d P K Lk :=
    { p := hd12
      k := (kd.gpr (by decide)).trans hK
      l := (kd.gpr (by decide)).trans hL
      ones := hd10
      len := hlen
      fit := by omega_arith
      table := by rw [kd.2.2.1]; exact htab
      key := by
        rw [kd.2.1, kd.2.2.1, hrd]
        exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
      keyFit := kfit
      keySep := fun x h₁ h₂ => kc x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega_arith) }
  obtain hid : ScheduleInv d P K Lk 0 d := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, Keep.refl _ _⟩
    · rw [hdmem, identityMem_table, schedule_zero]
    · rw [hd5]; rfl
    · rw [hd4]
    · rw [hd2, Nat.zero_mod]
  refine WP.seq (WP.mono (schedule_loop d d (by decide) hen hid) fun e he => ?_)
  obtain ke : Keep [.r4, .r2, .r5, .r10, .r9, .r12, .r6, .r7, .r8, .r11] s e :=
    (kd.trans he.keep).mono (by decide)
  obtain he12 : e.gpr .r12 = P := (he.keep.gpr (by decide)).trans hd12
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (init_finish e he12 cfit (by rw [ke.2.2.1]; exact hctx)) fun f ⟨hfm, hfk⟩ => ?_
  obtain kf : Keep [.r4, .r2, .r5, .r10, .r9, .r12, .r6, .r7, .r8, .r11] s f :=
    (ke.trans hfk).mono (by decide)
  obtain hctxf : Frame [⟨State.addr P, 258⟩] a.mem f.mem := by
    rw [hfm]
    refine frame_finish ?_ _ _
    obtain h1 := frame_of_table he.frame
    obtain h0 := frame_of_table (identityMem_frame a.mem (State.addr P) 256 (by decide))
    rw [hdmem] at h1
    exact h0.trans h1
  obtain hf3 : f.gpr .r3 = Sc := (kf.gpr (by decide)).trans hS
  obtain hsaved : Spill.Saved f.mem (State.addr (f.gpr .r3)) s.gpr saved := by
    rw [hf3]
    refine saved_after ?_ hctxf cs
    rw [ham]
    exact Spill.saveMem_saved _ _ _ _ saved_slots
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok f (by rw [hf3]; exact sfit)
    (by rw [kf.2.1, kf.2.2.1, hf3]; exact region_in hscr) hsaved)
    fun g ⟨hgr, hgk, hgm⟩ => ?_
  obtain h0 : WP isa (.block [.mov .r0 (imm 0)]) g fun t => t.gpr .r0 = 0#32 ∧ t.mem = g.mem := by
    arun
  refine WP.mono (WP.keep [.r0] h0 (by decide)) fun t ⟨⟨t0, tm⟩, tk⟩ => ?_
  refine ⟨t0, ?_, ?_, tk.2.2.2.trans (hgk.2.2.2.trans kf.2.2.2)⟩
  · have ht := he.table
    rw [tm, hgm, hfm, context_finish, ht, ← keySchedule_eq, hkey]
    rfl
  · intro r hr
    rw [tk.gpr (by simp only [preserved] at hr; revert hr; revert r; decide)]
    by_cases hs : r ∈ saved.map Prod.fst
    · exact hgr r hs
    · rw [hgk.gpr (by rw [← saved_regs]; exact hs)]
      have : r = .lr := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [saved_regs] at hs
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs ⊢
      subst this
      exact kf.gpr (by decide)

/-- `(len - 1) >> 8` is zero iff `len` is in `1..=256`. -/
theorem valid_len (L : BitVec 32) :
    ((L - BitVec.ofNat 32 1) >>> 8 - BitVec.ofNat 32 0 == 0#32) =
      decide (1 ≤ L.toNat ∧ L.toNat ≤ 256) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, BitVec.sub_zero,
    ← BitVec.toNat_inj, BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
  have := L.isLt
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega_arith

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State) (hs : initC.pre s) :
    WP isa VG.Impl.Rc4.Arm.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) with
      | .ok ctx => t.gpr .r0 = 0#32 ∧ contextAt t.mem (State.addr (s.gpr .r2)) = ctx
      | .error .invalidKeyLength => t.gpr .r0 = 1#32) ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  obtain hcheck : WP isa (.block [.dp .sub .r12 .r1 (imm 1), .mov .r12 (.shifted .r12 .lsr 8),
      .cmp .r12 (imm 0)]) s fun t => t.mem = s.mem ∧
      t.z = decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) := by
    arun
    exact valid_len _
  unfold VG.Impl.Rc4.Arm.init
  refine WP.seq (WP.mono (WP.keep [.r12] hcheck (by decide)) fun t ⟨⟨htm, htz⟩, htk⟩ => ?_)
  obtain htp : initC.pre t := by
    obtain ⟨hrd, hwr, h⟩ := hs
    refine ⟨?_, ?_, ?_⟩ <;> simp only [htk.2.1, htk.2.2.1, htk.gpr (r := .r0) (by decide),
      htk.gpr (r := .r1) (by decide), htk.gpr (r := .r2) (by decide),
      htk.gpr (r := .r3) (by decide)] <;> with_reducible assumption
  have hreg (r : Reg) (hr : r ≠ .r12) : t.gpr r = s.gpr r := htk.gpr (by simpa using hr)
  refine WP.ite (!t.z) rfl (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) := by
      intro hg; rw [htz, decide_eq_true hg] at hn; exact absurd hn (by decide)
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    obtain h1 : WP isa (.block [.mov .r0 (imm 1)]) t fun u => u.gpr .r0 = 1#32 := by
      arun
    refine WP.mono (WP.keep [.r0] h1 (by decide)) fun u ⟨hu, huk⟩ => ⟨hu, ?_, ?_⟩
    · intro r hr
      have : r ≠ .r0 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [huk.gpr (by simpa using this.1), hreg r this.2]
    · exact huk.2.2.2.trans htk.2.2.2
  · have hg : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256 := by
      by_contra hg; rw [htz, decide_eq_false hg] at hy; exact absurd hy (by decide)
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    refine WP.mono (init_valid t htp (by rw [hreg .r1 (by decide)]; exact hg))
      fun u ⟨hu0, huc, hup, husp⟩ => ?_
    rw [hreg .r0 (by decide), hreg .r1 (by decide), hreg .r2 (by decide), htm] at huc
    refine ⟨⟨hu0, huc⟩, fun r hr => ?_, husp.trans htk.2.2.2⟩
    rw [hup r hr]
    refine hreg r ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Rc4.Arm

end

end

/-! ### `Rc4.Arm.ApplyLoop`, which only this module used -/

section

/-! ### `Rc4.Arm.ApplyStep`, which only this module used -/

section

/-! # RC4 on ARMv7: one PRGA step -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- What a step of the stream function keeps: the table at `P`, the `L`
bytes of data at `D`, all ones. -/
structure StepEnv (s : State) (P D L : BitVec 32) : Prop where
  p : s.gpr .r12 = P
  d : s.gpr .r1 = D
  l : s.gpr .r2 = L
  ones : s.gpr .r10 = BitVec.allOnes 32
  pfit : P.toNat + 258 ≤ 2 ^ 32
  dfit : D.toNat + L.toNat ≤ 2 ^ 32
  table : InRegions s.wr (State.addr P) 256
  data : InRegions s.wr (State.addr D) L.toNat
  sTD : Mem.Sep (State.addr P) 256 (State.addr D) L.toNat

/-- The registers a step writes. -/
abbrev stepRegs : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r11]

theorem StepEnv.keep {s t : State} {P D L : BitVec 32} (h : StepEnv s P D L) {rs : List Reg}
    (hk : Keep rs s t) (hrs : ∀ r ∈ rs, r ≠ .r12 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r10) :
    StepEnv t P D L :=
  { h with
    p := (hk.gpr fun hm => (hrs _ hm).1 rfl).trans h.p
    d := (hk.gpr fun hm => (hrs _ hm).2.1 rfl).trans h.d
    l := (hk.gpr fun hm => (hrs _ hm).2.2.1 rfl).trans h.l
    ones := (hk.gpr fun hm => (hrs _ hm).2.2.2 rfl).trans h.ones
    table := by rw [hk.2.2.1]; exact h.table
    data := by rw [hk.2.2.1]; exact h.data }

theorem StepEnv.tableEnv {s : State} {P D L : BitVec 32} (h : StepEnv s P D L)
    {idx : Byte} (h6 : s.gpr .r6 = idx.setWidth 32) : TableEnv s idx :=
  ⟨h6, h.ones, by rw [h.p]; have := h.pfit; omega_using [this], by rw [h.p]; exact h.table⟩

theorem apply_before (s : State) (i j : Byte) {P D L : BitVec 32} (he : StepEnv s P D L)
    (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32) :
    WP isa (.block (([.dp .add .r4 .r4 (imm 1), .dp .and .r4 .r4 (imm 255)] : List Instr) ++ loadI ++
      ([.dp .add .r5 .r5 (.reg .r11), .dp .and .r5 .r5 (imm 255), .mov .r6 (.reg .r5)] :
        List Instr))) s fun t =>
      t.gpr .r4 = (i + 1#8).setWidth 32 ∧
      t.gpr .r5 = (j + s.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧
      t.gpr .r6 = t.gpr .r5 ∧ Keep [.r4, .r5, .r6, .r9, .r11] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain h1 : WP isa (.block [.dp .add .r4 .r4 (imm 1), .dp .and .r4 .r4 (imm 255)]) s fun t =>
      t.gpr .r4 = (i + 1#8).setWidth 32 ∧ t.mem = s.mem := by
    arun [h4, byte_inc32]
  refine WP.mono (WP.keep [.r4] h1 (by decide)) fun t ⟨⟨t4, tm⟩, tk⟩ => ?_
  obtain het := he.keep tk (by decide)
  refine WP.mono (loadI_ok t (i + 1#8) t4 (by rw [het.p]; have := he.pfit; omega_using [this])
    (by rw [het.p]; exact region_in het.table)) fun u ⟨u11, uk, um⟩ => ?_
  rw [het.p, tm] at u11
  obtain u5 : u.gpr .r5 = j.setWidth 32 :=
    (uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans h5)
  obtain h2 : WP isa (.block [.dp .add .r5 .r5 (.reg .r11), .dp .and .r5 .r5 (imm 255),
      .mov .r6 (.reg .r5)]) u fun v =>
      v.gpr .r5 = (j + s.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧
      v.gpr .r6 = v.gpr .r5 ∧ v.mem = u.mem := by
    arun [u5, u11, byte_add32]
  refine WP.mono (WP.keep [.r5, .r6] h2 (by decide)) fun v ⟨⟨v5, v6, vm⟩, vk⟩ => ?_
  exact ⟨(vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t4), v5, v6,
    ((tk.trans uk).trans vk).mono (by decide), vm.trans (um.trans tm)⟩

theorem apply_middle (s : State) (ii a b : Byte) {P : BitVec 32} (h12 : s.gpr .r12 = P)
    (hfit : P.toNat + 256 ≤ 2 ^ 32) (h4 : s.gpr .r4 = ii.setWidth 32)
    (h7 : s.gpr .r7 = b.setWidth 32) (h11 : s.gpr .r11 = a.setWidth 32)
    (hw : InRegions s.wr (State.addr P + BitVec.ofNat 64 ii.toNat) 1) :
    WP isa (.block [.dp .add .r9 .r12 (.reg .r4), .strb .r7 .r9 0, .dp .add .r6 .r7 (.reg .r11),
      .dp .and .r6 .r6 (imm 255)]) s fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r6 = (a + b).setWidth 32 ∧ Keep [.r6, .r9] s t := by
  obtain hw' : InRegions s.wr (State.addr (P + ii.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [idx_addr hfit ii]; exact hw
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r6 = (a + b).setWidth 32) [.r6, .r9] ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  arun [h12, h4, h7, h11, hw', byte_add32]
  rw [idx_addr hfit ii, writeW_byte8, low_byte32, BitVec.add_comm b a]
  exact ⟨rfl, rfl⟩

theorem apply_after (s : State) (k : Byte) {D L : BitVec 32} {n : Nat}
    (h1 : s.gpr .r1 = D) (h2 : s.gpr .r2 = L) (h0 : s.gpr .r0 = BitVec.ofNat 32 n)
    (h7 : s.gpr .r7 = k.setWidth 32) (hfit : D.toNat + n < 2 ^ 32)
    (hd : InRegions s.wr (State.addr D + BitVec.ofNat 64 n) 1) :
    WP isa (.block [.dp .add .r9 .r1 (.reg .r0), .ldrb .r11 .r9 0, .dp .eor .r11 .r11 (.reg .r7),
      .strb .r11 .r9 0, .dp .add .r0 .r0 (imm 1), .cmp .r0 (.reg .r2)]) s fun t =>
      t.mem = s.mem.write (State.addr D + BitVec.ofNat 64 n) 1
          (s.mem (State.addr D + BitVec.ofNat 64 n) ^^^ k) ∧
        t.gpr .r0 = BitVec.ofNat 32 (n + 1) ∧
        t.z = (BitVec.ofNat 32 (n + 1) - L == 0#32) ∧ Keep [.r0, .r9, .r11] s t := by
  obtain hdn : State.addr (D + BitVec.ofNat 32 n + BitVec.ofNat 32 0) =
      State.addr D + BitVec.ofNat 64 n := by
    rw [BitVec.add_zero]
    exact addr_add hfit
  obtain hw : InRegions s.wr (State.addr (D + BitVec.ofNat 32 n + BitVec.ofNat 32 0)) 1 := by
    rw [hdn]; exact hd
  obtain hr := region_in (rs := s.rd) hw
  obtain hadd : BitVec.ofNat 32 n + BitVec.ofNat 32 1 = BitVec.ofNat 32 (n + 1) := by
    rw [← BitVec.ofNat_add]
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (State.addr D + BitVec.ofNat 64 n) 1
          (s.mem (State.addr D + BitVec.ofNat 64 n) ^^^ k) ∧
        t.gpr .r0 = BitVec.ofNat 32 (n + 1) ∧
        t.z = (BitVec.ofNat 32 (n + 1) - L == 0#32)) [.r0, .r9, .r11] ?_ (by decide))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2, hk⟩
  arun [h1, h2, h0, h7, hw, hr, hadd]
  rw [hdn, writeW_byte8, low_xor32]

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte) {P D L : BitVec 32} {n : Nat}
    (he : StepEnv s P D L) (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 n) (hn : n < L.toNat) :
    let p := State.addr P
    let ii := i + 1#8
    let a := s.mem (p + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (p + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write
      (p + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (p + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = swapped.write (State.addr D + BitVec.ofNat 64 n) 1
        (swapped (State.addr D + BitVec.ofNat 64 n) ^^^ k) ∧
      t.gpr .r4 = ii.setWidth 32 ∧ t.gpr .r5 = jj.setWidth 32 ∧
      t.gpr .r0 = BitVec.ofNat 32 (n + 1) ∧
      t.z = (BitVec.ofNat 32 (n + 1) - L == 0#32) ∧ Keep stepRegs s t := by
  intro p ii a jj b swapped k
  obtain hfit : P.toNat + 256 ≤ 2 ^ 32 := by have := he.pfit; omega_using [this]
  simp only [applyStep, List.append_assoc]
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (apply_before s i j he h4 h5) fun t ⟨t4, t5, t6, tk, tm⟩ => ?_
  obtain het := he.keep tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (replace_core t jj ii (het.tableEnv (t6.trans t5)) t4) fun u ⟨u7, um, uk⟩ => ?_
  rw [tm, het.p] at u7 um
  obtain heu := het.keep uk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok u ii ((uk.gpr (by decide)).trans t4) (by rw [heu.p]; exact hfit)
    (by rw [heu.p]; exact region_in heu.table)) fun v ⟨v11, vk, vm⟩ => ?_
  obtain ha : u.mem (p + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, write_byte]
    split <;> rfl
  rw [heu.p, ha] at v11
  obtain hev := heu.keep vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (apply_middle v ii a b hev.p hfit
    ((vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t4))
    ((vk.gpr (by decide)).trans u7) v11
    (by rw [vk.2.2.1, uk.2.2.1, tk.2.2.1]
        exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using [])
          he.table)) fun w ⟨wm, w6, wk⟩ => ?_
  rw [vm, um] at wm
  have hw : w.mem = swapped := wm
  obtain hew := hev.keep wk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (lookup_core w (a + b) (hew.tableEnv w6)) fun x ⟨⟨x7, xm⟩, xk⟩ => ?_
  rw [hew.p, hw] at x7
  obtain hex := hew.keep xk (by decide)
  obtain ktx := ((uk.trans vk).trans wk).trans xk
  obtain x4 : x.gpr .r4 = ii.setWidth 32 := (ktx.gpr (by decide)).trans t4
  obtain x5 : x.gpr .r5 = jj.setWidth 32 := (ktx.gpr (by decide)).trans t5
  obtain x0 : x.gpr .r0 = BitVec.ofNat 32 n := (ktx.gpr (by decide)).trans ((tk.gpr (by decide)).trans h0)
  refine WP.mono (apply_after x k hex.d hex.l x0 x7 (by have := he.dfit; omega_using [hn, this])
    (by rw [xk.2.2.1, wk.2.2.1, vk.2.2.1, uk.2.2.1, tk.2.2.1]
        exact region_offset _ _ _ _ _ (by have := he.dfit; omega_using [hn]) (by omega_using [hn]) he.data))
    fun y ⟨ym, y0, yz, yk⟩ => ?_
  exact ⟨by rw [ym, xm, hw], (yk.gpr (by decide)).trans x4, (yk.gpr (by decide)).trans x5, y0, yz,
    (((tk.trans ktx).trans yk)).mono (by decide)⟩

end VG.Proof.Rc4.Arm

end

end


/-! # RC4 on ARMv7: the stream loop -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- The context and output after the first `k` data bytes, from memory `m`. -/
def upd (m : Mem) (P D : BitVec 32) (k : Nat) : Context × List Byte :=
  update (contextAt m (State.addr P)) (bytesAt m (State.addr D) k)

theorem upd_succ (m : Mem) (P D : BitVec 32) (k : Nat) :
    upd m P D (k + 1) = ((step (upd m P D k).1).1, (upd m P D k).2 ++
      [m (State.addr D + BitVec.ofNat 64 k) ^^^ (step (upd m P D k).1).2]) := by
  unfold upd
  rw [bytes_snoc, update_snoc]

/-- What the stream loop writes: the table and the data. -/
def loopRegions (P D L : BitVec 32) : List Region :=
  [⟨State.addr P, 256⟩, ⟨State.addr D, L.toNat⟩]

/-- The stream loop after `k` bytes, from the state `b` it started in; `m₀`
is the memory on entry, which differs from `b`'s only outside the context
and the data. -/
structure LoopInv (m₀ : Mem) (P D L : BitVec 32) (b : State) (k : Nat) (t : State) : Prop where
  le : k ≤ L.toNat
  table : (contextAt t.mem (State.addr P)).table = (upd m₀ P D k).1.table
  i : t.gpr .r4 = (upd m₀ P D k).1.i.setWidth 32
  j : t.gpr .r5 = (upd m₀ P D k).1.j.setWidth 32
  data : bytesAt t.mem (State.addr D) k = (upd m₀ P D k).2
  tail : ∀ x, k ≤ x → x < L.toNat →
    t.mem (State.addr D + BitVec.ofNat 64 x) = m₀ (State.addr D + BitVec.ofNat 64 x)
  frame : Frame (loopRegions P D L) b.mem t.mem
  count : t.gpr .r0 = BitVec.ofNat 32 k
  keep : Keep stepRegs b t

/-- A byte outside the table and the data byte an iteration writes. -/
theorem step_other {m : Mem} {p d x : Addr} {ii jj : Byte} {w : Byte}
    (hT : ¬ (x - p).toNat < 256) (hD : x ≠ d) :
    (((m.write (p + BitVec.ofNat 64 jj.toNat) 1 (m (p + BitVec.ofNat 64 ii.toNat))).write
      (p + BitVec.ofNat 64 ii.toNat) 1 (m (p + BitVec.ofNat 64 jj.toNat))).write d 1 w) x =
      m x := by
  rw [write_byte, ite_eq_right hD]
  exact swap_frame m p ii jj x hT

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (t : State) (i j : Byte) {P D L : BitVec 32} {k : Nat}
    (he : StepEnv t P D L) (h4 : t.gpr .r4 = i.setWidth 32) (h5 : t.gpr .r5 = j.setWidth 32)
    (h0 : t.gpr .r0 = BitVec.ofNat 32 k) (hk : k < L.toNat) :
    let next := step { table := (contextAt t.mem (State.addr P)).table, i, j }
    WP isa (.block applyStep) t fun u =>
      (contextAt u.mem (State.addr P)).table = next.1.table ∧
      u.gpr .r4 = next.1.i.setWidth 32 ∧ u.gpr .r5 = next.1.j.setWidth 32 ∧
      u.mem (State.addr D + BitVec.ofNat 64 k) =
        t.mem (State.addr D + BitVec.ofNat 64 k) ^^^ next.2 ∧
      (∀ x, ¬ (x - State.addr P).toNat < 256 → x ≠ State.addr D + BitVec.ofNat 64 k →
        u.mem x = t.mem x) ∧
      Frame (loopRegions P D L) t.mem u.mem ∧
      u.gpr .r0 = BitVec.ofNat 32 (k + 1) ∧
      u.z = (BitVec.ofNat 32 (k + 1) - L == 0#32) ∧ Keep stepRegs t u := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step t i j he h4 h5 h0 hk)
    fun u ⟨hum, hu4, hu5, hu0, huz, huk⟩ => ?_
  obtain hdk : ¬ (State.addr D + BitVec.ofNat 64 k - State.addr P).toNat < 256 := by
    obtain hin : (State.addr D + BitVec.ofNat 64 k - State.addr D).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk])]
      exact hk
    exact fun h => he.sTD _ h hin
  obtain hTD : Mem.Sep (State.addr P) 256 (State.addr D + BitVec.ofNat 64 k) 1 :=
    sep_offset_right he.sTD (by omega_using [hk]) (by omega_using [hk])
  refine ⟨?_, hu4, hu5, ?_, ?_, ?_, hu0, huz, huk⟩
  · rw [hum, table_write_sep _ _ _ _ hTD, table_swap]
  · rw [hum, write_byte, ite_eq_left rfl, swap_frame _ _ _ _ _ hdk]
    obtain ht := table_swap t.mem (State.addr P) (i + 1#8)
      (j + t.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · intro x hT hD
    rw [hum]
    exact step_other hT hD
  · rw [hum]
    have hP : (⟨State.addr P, 256⟩ : Region) ∈ loopRegions P D L := List.mem_cons_self
    obtain hD : (⟨State.addr D, L.toNat⟩ : Region) ∈ loopRegions P D L :=
      List.mem_cons_of_mem _ List.mem_cons_self
    refine Frame.write ?_ hD _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
    refine Frame.write ?_ hP _ (Offset.contains_base _ (by omega_using []) (by omega_using []))
    exact Frame.write (Frame.refl _ _) hP _ (Offset.contains_base _ (by omega_using []) (by omega_using []))

theorem loop_step (m₀ : Mem) {P D L : BitVec 32} (b : State) (hb : StepEnv b P D L) {k : Nat}
    (hk : k < L.toNat) (t : State) (ht : LoopInv m₀ P D L b k t) :
    WP isa (.block applyStep) t fun u => LoopInv m₀ P D L b (k + 1) u ∧
      u.z = (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  obtain he := hb.keep ht.keep (by decide)
  obtain hsD : ∀ x, x < L.toNat →
      ¬ (State.addr D + BitVec.ofNat 64 x - State.addr P).toNat < 256 := by
    intro x hx
    obtain hin : (State.addr D + BitVec.ofNat 64 x - State.addr D).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hx])]
      exact hx
    exact fun h => hb.sTD _ h hin
  obtain hctx : (⟨(contextAt t.mem (State.addr P)).table, (upd m₀ P D k).1.i,
      (upd m₀ P D k).1.j⟩ : Context) = (upd m₀ P D k).1 := context_ext ht.table rfl rfl
  obtain hst := apply_step_table t (upd m₀ P D k).1.i (upd m₀ P D k).1.j he ht.i ht.j ht.count hk
  rw [hctx] at hst
  refine WP.mono hst fun u ⟨htab, hui, huj, hbyte, hother, hfr, hu0, huz, huk⟩ => ⟨?_, huz⟩
  obtain hkeep : ∀ x, x < L.toNat → x ≠ k →
      u.mem (State.addr D + BitVec.ofNat 64 x) = t.mem (State.addr D + BitVec.ofNat 64 x) :=
    fun x hx hne => hother _ (hsD x hx) (data_ne hx hk hne)
  refine
    { le := hk
      table := by rw [upd_succ]; exact htab
      i := by rw [upd_succ]; exact hui
      j := by rw [upd_succ]; exact huj
      data := ?_
      tail := fun x hx hxL => by
        rw [hkeep x hxL (by omega_using [hx])]
        exact ht.tail x (by omega_using [hx]) hxL
      frame := ht.frame.trans hfr
      count := hu0
      keep := (ht.keep.trans huk).mono (by decide) }
  rw [bytes_snoc, upd_succ, hbyte, ht.tail k (Nat.le_refl _) hk, ← ht.data]
  refine congrArg (· ++ _) ?_
  exact bytes_frame _ _ _ _ fun x hx => hkeep x (by omega_using [hk, hx]) (by omega_using [hx])

theorem apply_loop (m₀ : Mem) {P D L : BitVec 32} (b : State) (hb : StepEnv b P D L) {k : Nat}
    (hk : k < L.toNat) (t : State) (ht : LoopInv m₀ P D L b k t) :
    WP isa (.loop (.block applyStep) .ne) t (LoopInv m₀ P D L b L.toNat) := by
  refine WP.loop (M := isa)
    (fun rem u => ∃ j, j < L.toNat ∧ rem = L.toNat - j ∧ LoopInv m₀ P D L b j u)
    ?_ (L.toNat - k) t ⟨k, hk, rfl, ht⟩
  intro rem u ⟨j, hj, hrem, hu⟩
  refine WP.mono (loop_step m₀ b hb hj u hu) fun v ⟨hv, hz⟩ => ?_
  by_cases hend : j + 1 = L.toNat
  · left
    refine ⟨?_, hend ▸ hv⟩
    rw [hend, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self] at hz
    rw [eval_ne, hz]
    rfl
  · right
    have hL := L.isLt
    obtain hnz : BitVec.ofNat 32 (j + 1) - L ≠ 0#32 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega_using [hj, hend, h']
    refine ⟨?_, L.toNat - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hv⟩
    rw [eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

end VG.Proof.Rc4.Arm

end

end


/-! # RC4 on ARMv7: the stream function -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

theorem apply_entry (s : State) (hs : applyC.pre s) :
    WP isa (.block entry) s fun a => a.mem = s.mem ∧ Keep [.r12] s a ∧
      a.gpr .r12 = (contextAt s.mem (State.addr (s.gpr .r0))).i.setWidth 32 ∧
      a.z = (s.gpr .r2 - BitVec.ofNat 32 0 == 0#32) := by
  obtain ⟨_, hwr, _, _, _, cfit, _, _⟩ := hs
  obtain a256 : State.addr (s.gpr .r0 + BitVec.ofNat 32 256) = State.addr (s.gpr .r0) + 256#64 :=
    addr_add (a := s.gpr .r0) (k := 256) (by omega_using [cfit])
  obtain r256 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 256)) 1 := by
    rw [a256]
    refine region_in (region_offset _ _ 258 256 1 (by decide) (by decide) ?_)
    exact ⟨_, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  refine WP.mono (WP.keep (Q := fun a => a.mem = s.mem ∧
      a.gpr .r12 = (contextAt s.mem (State.addr (s.gpr .r0))).i.setWidth 32 ∧
      a.z = (s.gpr .r2 - BitVec.ofNat 32 0 == 0#32)) [.r12] ?_ (by decide))
    fun a ⟨h, hk⟩ => ⟨h.1, hk, h.2.1, h.2.2⟩
  unfold entry
  arun [r256]
  rw [a256]
  conj_rfl

theorem apply_start (b : State) {P : BitVec 32} (h0 : b.gpr .r0 = P)
    (hfit : P.toNat + 258 ≤ 2 ^ 32) (h257 : InRegions (b.rd ++ b.wr) (State.addr P + 257#64) 1) :
    WP isa (.block start) b fun c => c.mem = b.mem ∧ Keep [.r4, .r12, .r5, .r0, .r10] b c ∧
      c.gpr .r4 = b.gpr .r12 ∧ c.gpr .r12 = P ∧
      c.gpr .r5 = (b.mem (State.addr P + 257#64)).setWidth 32 ∧ c.gpr .r0 = 0#32 ∧
      c.gpr .r10 = BitVec.allOnes 32 := by
  obtain a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega_using [hfit])
  obtain r257 : InRegions (b.rd ++ b.wr) (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact h257
  refine WP.mono (WP.keep (Q := fun c => c.mem = b.mem ∧ c.gpr .r4 = b.gpr .r12 ∧
      c.gpr .r12 = P ∧ c.gpr .r5 = (b.mem (State.addr P + 257#64)).setWidth 32 ∧
      c.gpr .r0 = 0#32 ∧ c.gpr .r10 = BitVec.allOnes 32) [.r4, .r12, .r5, .r0, .r10] ?_
    (by decide)) fun c ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold start ones
  arun [h0, r257, ones_eq]
  rw [a257]
  conj_rfl

theorem apply_finish (d : State) (i j : Byte) {P : BitVec 32} (hfit : P.toNat + 258 ≤ 2 ^ 32)
    (h4 : d.gpr .r4 = i.setWidth 32) (h5 : d.gpr .r5 = j.setWidth 32) (h12 : d.gpr .r12 = P)
    (hw : InRegions d.wr (State.addr P) 258) :
    WP isa (.block finish) d fun e =>
      e.mem = (d.mem.write (State.addr P + 256#64) 1 i).write (State.addr P + 257#64) 1 j ∧
      Keep [] d e := by
  obtain a256 : State.addr (P + BitVec.ofNat 32 256) = State.addr P + 256#64 := addr_add (by omega_using [hfit])
  obtain a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega_using [hfit])
  obtain h256 : InRegions d.wr (State.addr (P + BitVec.ofNat 32 256)) 1 := by
    rw [a256]; exact region_offset _ _ _ 256 1 (by decide) (by decide) hw
  obtain h257 : InRegions d.wr (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact region_offset _ _ _ 257 1 (by decide) (by decide) hw
  refine WP.mono (WP.keep (Q := fun e =>
      e.mem = (d.mem.write (State.addr P + 256#64) 1 i).write (State.addr P + 257#64) 1 j)
    [] ?_ (by decide)) fun e ⟨h, hk⟩ => ⟨h, hk⟩
  unfold finish
  arun [h4, h5, h12, h256, h257]
  rw [a256, a257, writeW_byte8, writeW_byte8, low_byte32, low_byte32]

/-- The full stream function, including empty input. -/
theorem apply_ok (s : State) (hs : applyC.pre s) :
    WP isa VG.Impl.Rc4.Arm.apply s fun t => applyC.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  have hs' := hs
  obtain ⟨hrd, hwr, cd, cs, ds, cfit, dfit, sfit⟩ := hs'
  unfold applyC
  dsimp only
  generalize hP : s.gpr .r0 = P at hwr cd cs cfit ⊢
  generalize hD : s.gpr .r1 = D at hwr cd ds dfit ⊢
  generalize hL : s.gpr .r2 = L at hwr cd ds dfit ⊢
  generalize hS : s.gpr .r3 = Sc at hwr cs ds sfit
  obtain hctx : InRegions s.wr (State.addr P) 258 := ⟨_, by rw [hwr]; exact List.mem_cons_self,
    Region.contains_self _ _⟩
  obtain hdat : InRegions s.wr (State.addr D) L.toNat := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  obtain hscr : InRegions s.wr (State.addr Sc) 64 := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    Region.contains_self _ _⟩
  have hpres (t : State) (rs : List Reg) (hk : Keep rs s t) (hr : ∀ r ∈ preserved, r ∉ rs) :
      ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r h => hk.gpr (hr r h)
  unfold VG.Impl.Rc4.Arm.apply
  refine WP.seq (WP.mono (apply_entry s hs) fun a ⟨ham, hak, ha12, haz⟩ => ?_)
  rw [hP] at ha12
  rw [hL, BitVec.sub_zero] at haz
  refine WP.ite a.z (eval_eq a) (fun hz => ?_) (fun hnz => ?_)
  · have hL0 : L = 0#32 := by rw [haz, beq_iff_eq] at hz; exact hz
    refine WP.block_nil ⟨?_, hpres a _ hak (by decide), hak.2.2.2⟩
    rw [ham, hL0]
    exact ⟨rfl, rfl⟩
  obtain hL0 : L.toNat ≠ 0 := fun h => by
    have : L = 0#32 := BitVec.eq_of_toNat_eq h
    rw [haz, this] at hnz
    exact absurd hnz (by decide)
  refine WP.seq ?_
  obtain ha3 : a.gpr .r3 = Sc := (hak.gpr (by decide)).trans hS
  rw [WP.block_append_iff]
  refine WP.mono (save_ok a (by rw [ha3]; exact sfit) (by rw [hak.2.2.1, ha3]; exact hscr))
    fun b ⟨hbm, hbk⟩ => ?_
  rw [ha3] at hbm
  obtain ka : Keep [.r12] s b := (hak.trans hbk).mono (by decide)
  obtain hsave : Frame [⟨State.addr Sc, 64⟩] s.mem b.mem := by
    rw [hbm, ham]; exact save_frame _ _ _
  obtain hctxb : contextAt b.mem (State.addr P) = contextAt s.mem (State.addr P) :=
    contextAt_frame hsave fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cs
  obtain r257 : InRegions (b.rd ++ b.wr) (State.addr P + 257#64) 1 := by
    rw [ka.2.1, ka.2.2.1]
    exact region_in (region_offset _ _ _ 257 1 (by decide) (by decide) hctx)
  refine WP.mono (apply_start b ((ka.gpr (by decide)).trans hP) cfit r257)
    fun c ⟨hcm, hck, hc4, hc12, hc5, hc0, hc10⟩ => ?_
  obtain kc : Keep [.r12, .r4, .r5, .r0, .r10] s c := (ka.trans hck).mono (by decide)
  obtain hec : StepEnv c P D L :=
    { p := hc12
      d := (kc.gpr (by decide)).trans hD
      l := (kc.gpr (by decide)).trans hL
      ones := hc10
      pfit := cfit
      dfit := dfit
      table := by
        rw [kc.2.2.1]
        obtain h' := region_offset _ _ _ 0 256 (by decide) (by decide) hctx
        simpa only [BitVec.add_zero] using h'
      data := by rw [kc.2.2.1]; exact hdat
      sTD := sep_of_sub cd (contains_prefix _ (by decide)) (contains_prefix _ (Nat.le_refl _)) }
  obtain hinv : LoopInv s.mem P D L c 0 c := by
    have hu0 : upd s.mem P D 0 = (contextAt s.mem (State.addr P), []) := rfl
    refine
      { le := Nat.zero_le _
        table := by rw [hu0, hcm, hctxb]
        i := by
          rw [hu0, hc4, (hbk.gpr (by decide) : b.gpr .r12 = a.gpr .r12), ha12]
        j := by
          rw [hu0, hc5, ← hctxb]
          rfl
        data := by rw [hu0]; rfl
        tail := fun x _ hx => by
          rw [hcm]
          exact hsave.bytes (R := ⟨State.addr D, L.toNat⟩) (fun r hr => by
            simp only [List.mem_singleton] at hr
            subst hr
            exact ds) (show L.toNat ≤ 2 ^ 64 by have := L.isLt; omega_using []) hx
        frame := Frame.refl _ _
        count := hc0
        keep := Keep.refl _ _ }
  refine WP.seq (WP.mono (apply_loop s.mem c hec (Nat.pos_of_ne_zero hL0) c hinv)
    fun d hd => ?_)
  obtain kd : Keep (([.r12, .r4, .r5, .r0, .r10] : List Reg) ++ stepRegs) s d := kc.trans hd.keep
  rw [WP.block_append_iff]
  refine WP.mono (apply_finish d (upd s.mem P D L.toNat).1.i (upd s.mem P D L.toNat).1.j cfit
    hd.i hd.j ((hd.keep.gpr (by decide)).trans hc12) (by rw [kd.2.2.1]; exact hctx))
    fun e ⟨hem, hek⟩ => ?_
  obtain hce : Frame [⟨State.addr P, 258⟩, ⟨State.addr D, L.toNat⟩] b.mem e.mem := by
    have hc258 : (⟨State.addr P, 258⟩ : Region) ∈
        [⟨State.addr P, 258⟩, ⟨State.addr D, L.toNat⟩] := List.mem_cons_self
    rw [hem]
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    obtain hbd : Frame (loopRegions P D L) b.mem d.mem := by rw [← hcm]; exact hd.frame
    refine hbd.sub fun r hr => ?_
    simp only [loopRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
  obtain ke : Keep (([.r12, .r4, .r5, .r0, .r10] : List Reg) ++ stepRegs) s e :=
    (kd.trans hek).mono (by decide)
  obtain he3 : e.gpr .r3 = Sc := (ke.gpr (by decide)).trans hS
  obtain hsaved : Spill.Saved e.mem (State.addr (e.gpr .r3)) a.gpr saved := by
    rw [he3]
    obtain h0 : Spill.Saved b.mem (State.addr Sc) a.gpr saved := by
      rw [hbm]
      exact Spill.saveMem_saved _ _ _ _ saved_slots
    refine h0.frame saved_slots hce fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [BitVec.add_zero]
    rcases hr with rfl | rfl
    · exact (cs.symm.sub_left (Region.sub_prefix (by decide)))
    · exact (ds.symm.sub_left (Region.sub_prefix (by decide)))
  refine WP.mono (restore_ok e (by rw [he3]; exact sfit)
    (by rw [ke.2.1, ke.2.2.1, he3]; exact region_in hscr) hsaved)
    fun g ⟨hgr, hgk, hgm⟩ => ?_
  have hDP (o : Nat) (ho : o < 258) :
      Mem.Sep (State.addr D) L.toNat (State.addr P + BitVec.ofNat 64 o) 1 :=
    sep_of_sub cd.symm (contains_prefix _ (Nat.le_refl _))
      (Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho]))
  obtain hLn : L.toNat < 2 ^ 64 := by have := L.isLt; omega_using []
  refine ⟨⟨?_, ?_⟩, fun r hr => ?_, hgk.2.2.2.trans ke.2.2.2⟩
  · rw [hgm, hem, context_finish]
    exact context_ext hd.table rfl rfl
  · rw [hgm, hem, bytes_write_sep _ _ _ _ _ hLn (hDP 257 (by decide)),
      bytes_write_sep _ _ _ _ _ hLn (hDP 256 (by decide))]
    exact hd.data
  · by_cases hs : r ∈ saved.map Prod.fst
    · rw [hgr r hs]
      exact hak.gpr (by rw [saved_regs] at hs; revert hs; revert r; decide)
    · rw [hgk.gpr (by rw [← saved_regs]; exact hs)]
      have : r = .lr := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [saved_regs] at hs
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs ⊢
      subst this
      exact ke.gpr (by decide)

end VG.Proof.Rc4.Arm
