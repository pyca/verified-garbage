import VerifiedGarbage.Impl.Rc4.Arm
import VerifiedGarbage.Proof.Rc4.Update
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Run`. -/
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

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Proof.Rc4

/-! ## Registers kept -/

def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : VG.Proof.Rc4.Arm.Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Rc4.Arm.Keep rs s₁ s₂)
    (h₂ : VG.Proof.Rc4.Arm.Keep rs' s₂ s₃) : VG.Proof.Rc4.Arm.Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Rc4.Arm.Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Rc4.Arm.Keep rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keep.refl (rs : List Reg) (s : State) : VG.Proof.Rc4.Arm.Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Whether every instruction of `is` writes only registers of `rs`. -/
def writesOnly (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => match dstOf i with
    | some r => rs.contains r
    | none => true

theorem WP.keep {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa (.block is) s Q) (hc : VG.Proof.Rc4.Arm.writesOnly rs is = true) :
    WP isa (.block is) s fun s' => Q s' ∧ VG.Proof.Rc4.Arm.Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  have he' := Exec.block_iff.mp he
  obtain ⟨r, w, p, -⟩ := execBlock_regions he'
  refine ⟨t, s', he, hq, fun r' hr => execBlock_gpr (fun i hi e => hr ?_) he', r, w, p⟩
  have := List.all_eq_true.mp hc i hi
  simp only [e, List.contains_iff_mem] at this
  exact this

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
    s.store32 a x = if InRegions s.wr a 4 then some (VG.Proof.Rc4.Arm.withMem s (s.mem.writeW a x)) else none := rfl
theorem store8_eq (s : State) (a : Addr) (x : BitVec 8) :
    s.store8 a x = if InRegions s.wr a 1 then some (VG.Proof.Rc4.Arm.withMem s (s.mem.writeW a x)) else none := rfl
theorem sp_store (s : State) (m : Mem) : (VG.Proof.Rc4.Arm.withMem s m).sp = s.sp := rfl
theorem gpr_store (s : State) (m : Mem) : (VG.Proof.Rc4.Arm.withMem s m).gpr = s.gpr := rfl
theorem rd_store (s : State) (m : Mem) : (VG.Proof.Rc4.Arm.withMem s m).rd = s.rd := rfl
theorem wr_store (s : State) (m : Mem) : (VG.Proof.Rc4.Arm.withMem s m).wr = s.wr := rfl
theorem mem_store (s : State) (m : Mem) : (VG.Proof.Rc4.Arm.withMem s m).mem = m := rfl
theorem z_store (s : State) (m : Mem) : (VG.Proof.Rc4.Arm.withMem s m).z = s.z := rfl
theorem c_store (s : State) (m : Mem) : (VG.Proof.Rc4.Arm.withMem s m).c = s.c := rfl

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

theorem encodable_lt {n : Nat} (h : n < 256) : encodable (BitVec.ofNat 32 n) = true :=
  VG.Proof.Rc4.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega)

/-- 256, the one immediate of the code that needs a rotation. -/
theorem encodable_256 : encodable (256#32) = true := by decide

/-- Runs a block of the RC4 code. -/
syntax "arun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| arun) => `(tactic| arun [])
  | `(tactic| arun [$ls,*]) => `(tactic| (
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
  rw [BitVec.and_comm, VG.Proof.Rc4.Arm.adc_mask]

/-- The address of word `k` of the table at `P`, which does not wrap around. -/
theorem row_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) {k : Nat} (hk : k < 64) :
    State.addr (P + BitVec.ofNat 32 (4 * k)) = State.addr P + BitVec.ofNat 64 (4 * k) :=
  addr_add (by omega)

/-- The address of byte `i` of the table at `P`. -/
theorem idx_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) (i : Byte) :
    State.addr (P + i.setWidth 32 + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 i.toNat := by
  rw [BitVec.add_zero, byte32]
  exact addr_add (by have := i.isLt; omega)

/-- The branch conditions. -/
theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

theorem region_in {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) :
    InRegions (rs ++ ws) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Lookup`. -/
section

/-! # RC4 on ARMv7: the table lookup, a word at a time -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Proof.Rc4

/-- The mask `cmp x, #n` and `adc d, ones, #0` leave, applied to `y`: all
ones if `x < n`. -/
theorem cmp_mask (x : BitVec 32) {n : Nat} (hn : n < 2 ^ 32) {P : Prop} [Decidable P]
    (h : x.toNat < n ↔ P) (y : BitVec 32) :
    (BitVec.allOnes 32 + BitVec.ofNat 32 0 +
      BitVec.ofNat 32 (decide ((BitVec.ofNat 32 n).toNat ≤ x.toNat)).toNat) &&& y =
      if P then y else 0 := by
  rw [VG.Proof.Rc4.Arm.adc_mask, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  by_cases hp : P
  · rw [ite_eq_right (by simp only [decide_eq_true_eq]; have := h.mpr hp; omega), ite_eq_left hp]
  · rw [ite_eq_left (by simp only [decide_eq_true_eq]; have := mt h.mp hp; omega),
      ite_eq_right hp]

/-- The mask `rowMask` leaves. -/
theorem row_mask (idx : Byte) {k : Nat} (hk : k < 64) (y : BitVec 32) :
    (BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 (decide ((BitVec.ofNat 32 4).toNat ≤
      (idx.setWidth 32 ^^^ BitVec.ofNat 32 (4 * k)).toNat)).toNat) &&& y =
      if idx.toNat / 4 = k then y else 0 :=
  VG.Proof.Rc4.Arm.cmp_mask _ (by decide) (row_hit32 idx hk) y

/-- The mask `laneMask` leaves. -/
theorem lane_mask (idx : Byte) {j : Nat} (hj : j < 4) (y : BitVec 32) :
    (BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 (decide ((BitVec.ofNat 32 1).toNat ≤
      ((idx.setWidth 32 &&& BitVec.ofNat 32 3) ^^^ BitVec.ofNat 32 j).toNat)).toNat) &&& y = if idx.toNat % 4 = j then y else 0 :=
  VG.Proof.Rc4.Arm.cmp_mask _ (by decide) (lane_hit32 idx hj) y

/-! ## Visiting the words -/

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 64)
    (h6 : s.gpr .r6 = idx.setWidth 32) (h10 : s.gpr .r10 = BitVec.allOnes 32)
    (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .r8 = s.gpr .r8 |||
        (if idx.toNat / 4 = k then s.mem.readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k)) 32
          else 0) ∧ t.mem = s.mem := by
  have he : encodable (BitVec.ofNat 32 (4 * k)) = true := VG.Proof.Rc4.Arm.encodable_lt (by omega)
  have ho : 4 * k < 4096 := by omega
  rw [← VG.Proof.Rc4.Arm.row_addr hfit hk] at hr
  unfold gatherStep rowMask
  arun [h6, h10, he, ho, hr]
  rw [VG.Proof.Rc4.Arm.row_addr hfit hk, VG.Proof.Rc4.Arm.row_mask idx hk]

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .r8 = gather s₀.mem (State.addr (s₀.gpr .r12)) idx.toNat k ∧ t.gpr .r6 = s₀.gpr .r6 ∧
    t.gpr .r10 = s₀.gpr .r10 ∧ t.gpr .r12 = s₀.gpr .r12 ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧
    t.wr = s₀.wr

theorem gather_steps (s₀ : State) (idx : Byte) (h6 : s₀.gpr .r6 = idx.setWidth 32)
    (h10 : s₀.gpr .r10 = BitVec.allOnes 32) (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r12)) 256) :
    ∀ n ≤ 64, ∀ s, VG.Proof.Rc4.Arm.GInv s₀ idx 0 s →
      WP isa (.block ((List.range n).flatMap gatherStep)) s (VG.Proof.Rc4.Arm.GInv s₀ idx n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h8, h6', h10', h12, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r12) + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [hrd, hwr, h12]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hr
    refine WP.mono (WP.keep [.r8, .r9, .r11]
      (VG.Proof.Rc4.Arm.gather_step t idx (by omega) (h6'.trans h6) (h10'.trans h10) (by rw [h12]; exact hfit) hq)
      rfl) fun u ⟨⟨u8, um⟩, uk⟩ => ?_
    refine ⟨?_, (uk.gpr (by decide)).trans h6', (uk.gpr (by decide)).trans h10',
      (uk.gpr (by decide)).trans h12, um.trans hm, uk.2.1.trans hrd, uk.2.2.1.trans hwr⟩
    rw [u8, h8, h12, hm, gather_succ]

/-! ## Picking the byte of the word -/

theorem pick_step (s : State) (idx : Byte) {j : Nat} (hj : j < 4)
    (h6 : s.gpr .r6 = idx.setWidth 32) (h10 : s.gpr .r10 = BitVec.allOnes 32) :
    WP isa (.block (pickStep j)) s fun t =>
      t.gpr .r7 = s.gpr .r7 ||| (if idx.toNat % 4 = j then s.gpr .r8 else 0) ∧
      t.gpr .r8 = s.gpr .r8 >>> 8 ∧ t.mem = s.mem := by
  have he : encodable (BitVec.ofNat 32 j) = true := VG.Proof.Rc4.Arm.encodable_lt (by omega)
  unfold pickStep laneMask
  arun [h6, h10, he]
  rw [VG.Proof.Rc4.Arm.lane_mask idx hj]

def PInv (s₀ : State) (q : BitVec 32) (L j : Nat) (t : State) : Prop :=
  t.gpr .r7 = pick q L j ∧ t.gpr .r8 = q >>> (8 * j) ∧ t.gpr .r6 = s₀.gpr .r6 ∧
    t.gpr .r10 = s₀.gpr .r10 ∧ t.mem = s₀.mem

theorem pick_steps (s₀ : State) (idx : Byte) (q : BitVec 32) (h6 : s₀.gpr .r6 = idx.setWidth 32)
    (h10 : s₀.gpr .r10 = BitVec.allOnes 32) :
    ∀ n ≤ 4, ∀ s, VG.Proof.Rc4.Arm.PInv s₀ q (idx.toNat % 4) 0 s →
      WP isa (.block ((List.range n).flatMap pickStep)) s (VG.Proof.Rc4.Arm.PInv s₀ q (idx.toNat % 4) n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h7, h8, h6', h10', hm⟩ := ht
    refine WP.mono (WP.keep [.r7, .r8, .r9]
      (VG.Proof.Rc4.Arm.pick_step t idx (by omega) (h6'.trans h6) (h10'.trans h10)) rfl)
      fun u ⟨⟨u7, u8, um⟩, uk⟩ => ?_
    refine ⟨?_, ?_, (uk.gpr (by decide)).trans h6', (uk.gpr (by decide)).trans h10', um.trans hm⟩
    · rw [u7, h7, h8, pick_succ]
    · rw [u8, h8, shr_byte32]

/-! ## The lookup -/

/-- What a lookup or replacement needs: the index, all ones, and the table. -/
structure TableEnv (s : State) (idx : Byte) : Prop where
  idx : s.gpr .r6 = idx.setWidth 32
  ones : s.gpr .r10 = BitVec.allOnes 32
  fit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32
  table : InRegions s.wr (State.addr (s.gpr .r12)) 256

theorem TableEnv.read {s : State} {idx : Byte} (h : VG.Proof.Rc4.Arm.TableEnv s idx) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12)) 256 := VG.Proof.Rc4.Arm.region_in h.table

theorem lookup_core (s : State) (idx : Byte) (h : VG.Proof.Rc4.Arm.TableEnv s idx) :
    WP isa (.block lookup) s fun t =>
      t.gpr .r7 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
      t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.mov .r8 (imm 0)]) s (VG.Proof.Rc4.Arm.GInv s idx 0) := by
    arun [VG.Proof.Rc4.Arm.GInv, gather, Nat.not_lt_zero, BitVec.ofNat_eq_ofNat]
  refine WP.mono h0 fun t ht => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.gather_steps s idx h.idx h.ones h.fit h.read 64 (by decide) t ht)
    fun u hu => ?_
  obtain ⟨u8, u6, u10, _, um, _, _⟩ := hu
  let q := s.mem.readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * (idx.toNat / 4))) 32
  have hq : u.gpr .r8 = q := by
    rw [u8]; unfold gather; rw [ite_eq_left (by omega)]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.mov .r7 (imm 0)]) u (VG.Proof.Rc4.Arm.PInv s q (idx.toNat % 4) 0) := by
    arun [VG.Proof.Rc4.Arm.PInv, pick, hq, u6, u10, um, Nat.mul_zero, BitVec.ushiftRight_zero, Nat.not_lt_zero,
      BitVec.ofNat_eq_ofNat]
  refine WP.mono h1 fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.pick_steps s idx q h.idx h.ones 4 (by decide) v hv) fun w hw => ?_
  obtain ⟨w7, _, _, _, wm⟩ := hw
  have hL : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  arun [w7, wm]
  unfold pick
  rw [ite_eq_left hL, dword_byte _ _ hL, row_lane32]

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Replace`. -/
section

/-! # RC4 on ARMv7: replacing a secret-indexed byte of the table -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Proof.Rc4

/-! ## Moving the difference to the byte's lane -/

theorem spread_step (s : State) (idx c : Byte) {j : Nat} (hj : j < 4)
    (h6 : s.gpr .r6 = idx.setWidth 32) (h10 : s.gpr .r10 = BitVec.allOnes 32)
    (h7 : s.gpr .r7 = c.setWidth 32) (h8 : s.gpr .r8 = spread c (idx.toNat % 4) (j + 1)) :
    WP isa (.block (spreadStep j)) s fun t =>
      t.gpr .r8 = spread c (idx.toNat % 4) j ∧ t.mem = s.mem := by
  have he : encodable (BitVec.ofNat 32 j) = true := VG.Proof.Rc4.Arm.encodable_lt (by omega)
  unfold spreadStep laneMask
  arun [h6, h10, h7, h8, he]
  rw [VG.Proof.Rc4.Arm.lane_mask idx hj, spread_succ c (Nat.mod_lt _ (by decide))]

theorem spread_steps (s₀ : State) (idx c : Byte) (h6 : s₀.gpr .r6 = idx.setWidth 32)
    (h10 : s₀.gpr .r10 = BitVec.allOnes 32) (h7 : s₀.gpr .r7 = c.setWidth 32) :
    ∀ n ≤ 4, ∀ s, s.gpr .r8 = spread c (idx.toNat % 4) n → VG.Proof.Rc4.Arm.Keep [.r8, .r9] s₀ s →
      s.mem = s₀.mem →
      WP isa (.block ((List.range n).reverse.flatMap spreadStep)) s fun t =>
        t.gpr .r8 = spread c (idx.toNat % 4) 0 ∧ VG.Proof.Rc4.Arm.Keep [.r8, .r9] s₀ t ∧ t.mem = s₀.mem := by
  intro n hn
  induction n with
  | zero => intro s h8 hk hm; exact WP.block_nil ⟨h8, hk, hm⟩
  | succ n ih =>
    intro s h8 hk hm
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (WP.keep [.r8, .r9] (VG.Proof.Rc4.Arm.spread_step s idx c (by omega)
      ((hk.gpr (by decide)).trans h6) ((hk.gpr (by decide)).trans h10)
      ((hk.gpr (by decide)).trans h7) h8) rfl) fun t ⟨⟨t8, tm⟩, tk⟩ => ?_
    exact ih (by omega) t t8 ((hk.trans tk).mono (by decide)) (tm.trans hm)

theorem lanesDown_eq : lanesDown = (List.range 4).reverse := rfl

/-! ## Storing back every word -/

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 64)
    (h6 : s.gpr .r6 = idx.setWidth 32) (h10 : s.gpr .r10 = BitVec.allOnes 32)
    (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k))
        ((if idx.toNat / 4 = k then s.gpr .r8 else 0) ^^^
          s.mem.readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k)) 32) := by
  have he : encodable (BitVec.ofNat 32 (4 * k)) = true := VG.Proof.Rc4.Arm.encodable_lt (by omega)
  have ho : 4 * k < 4096 := by omega
  have hr := VG.Proof.Rc4.Arm.region_in (rs := s.rd) hw
  rw [← VG.Proof.Rc4.Arm.row_addr hfit hk] at hw hr
  unfold scatterStep rowMask
  arun [h6, h10, he, ho, hr, hw]
  rw [VG.Proof.Rc4.Arm.row_addr hfit hk, VG.Proof.Rc4.Arm.row_mask idx hk]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 32) (h : VG.Proof.Rc4.Arm.TableEnv s₀ idx) :
    ∀ n ≤ 64, ∀ s, s.gpr .r8 = d → VG.Proof.Rc4.Arm.Keep [.r9, .r11] s₀ s → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem (State.addr (s₀.gpr .r12)) idx.toNat d n ∧ t.gpr .r8 = d ∧
        VG.Proof.Rc4.Arm.Keep [.r9, .r11] s₀ t := by
  intro n hn
  induction n with
  | zero =>
    intro s h8 hk hm
    refine WP.block_nil ⟨?_, h8, hk⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s h8 hk hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h8 hk hm) fun t ⟨tm, t8, tk⟩ => ?_
    have t12 : t.gpr .r12 = s₀.gpr .r12 := tk.gpr (by decide)
    have hq : InRegions t.wr (State.addr (t.gpr .r12) + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [tk.2.2.1, t12]
      exact region_offset _ _ _ _ _ (by omega) (by omega) h.table
    refine WP.mono (WP.keep [.r9, .r11] (VG.Proof.Rc4.Arm.scatter_step t idx (by omega)
      ((tk.gpr (by decide)).trans h.idx) ((tk.gpr (by decide)).trans h.ones)
      (by rw [t12]; exact h.fit) hq) rfl) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, (uk.gpr (by decide)).trans t8, (tk.trans uk).mono (by decide)⟩
    rw [um, tm, t8, t12, scatter_succ]

/-! ## The replacement -/

theorem loadI_ok (s : State) (ii : Byte) (h4 : s.gpr .r4 = ii.setWidth 32)
    (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12)) 256) :
    WP isa (.block loadI) s fun t =>
      t.gpr .r11 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      VG.Proof.Rc4.Arm.Keep [.r9, .r11] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + ii.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [VG.Proof.Rc4.Arm.idx_addr hfit ii]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hr
  refine WP.mono (WP.keep (Q := fun t =>
      t.gpr .r11 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      t.mem = s.mem) [.r9, .r11] ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold loadI
  arun [h4, hi]
  rw [VG.Proof.Rc4.Arm.idx_addr hfit ii]

theorem replace_core (s : State) (idx ii : Byte) (h : VG.Proof.Rc4.Arm.TableEnv s idx)
    (h4 : s.gpr .r4 = ii.setWidth 32) :
    WP isa (.block replace) s fun t =>
      t.gpr .r7 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
      t.mem = s.mem.write (State.addr (s.gpr .r12) + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)) ∧
      VG.Proof.Rc4.Arm.Keep [.r7, .r8, .r9, .r11] s t := by
  have hn := idx.isLt
  let p := State.addr (s.gpr .r12)
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r7, .r8, .r9, .r11] (VG.Proof.Rc4.Arm.lookup_core s idx h) (by decide +kernel))
    fun t ⟨⟨t7, tm⟩, tk⟩ => ?_
  have t12 : t.gpr .r12 = s.gpr .r12 := tk.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.loadI_ok t ii ((tk.gpr (by decide)).trans h4) (by rw [t12]; exact h.fit)
    (by rw [tk.2.1, tk.2.2.1, t12]; exact h.read)) fun t' ⟨t'11, t'k, t'm⟩ => ?_
  rw [t12, tm] at t'11
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.dp .eor .r7 .r7 (.reg .r11), .mov .r8 (imm 0)]) t' fun u =>
      u.gpr .r7 = (b ^^^ v).setWidth 32 ∧ u.gpr .r8 = 0 ∧ u.mem = s.mem := by
    have t'7 : t'.gpr .r7 = b.setWidth 32 := (t'k.gpr (by decide)).trans t7
    arun [t'7, t'11, t'm, tm, BitVec.ofNat_eq_ofNat]
    rw [xor_byte32]
  refine WP.mono (WP.keep [.r7, .r8] h1 (by decide)) fun u ⟨⟨u7, u8, um⟩, uk⟩ => ?_
  have k₁ : VG.Proof.Rc4.Arm.Keep [.r7, .r8, .r9, .r11] s u := ((tk.trans t'k).trans uk).mono (by decide)
  rw [WP.block_append_iff]
  have hsp := VG.Proof.Rc4.Arm.spread_steps u idx (b ^^^ v) ((k₁.gpr (by decide)).trans h.idx)
    ((k₁.gpr (by decide)).trans h.ones) u7 4 (by decide) u
    (by rw [u8]; unfold spread; rw [ite_eq_right (by omega)]) (Keep.refl _ _) rfl
  rw [← VG.Proof.Rc4.Arm.lanesDown_eq] at hsp
  refine WP.mono hsp fun w ⟨w8, wk, wm⟩ => ?_
  have w11 : w.gpr .r11 = v.setWidth 32 :=
    (wk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t'11)
  have w7 : w.gpr .r7 = (b ^^^ v).setWidth 32 := (wk.gpr (by decide)).trans u7
  rw [WP.block_append_iff]
  have h2 : WP isa (.block [.dp .eor .r7 .r7 (.reg .r11)]) w fun x =>
      x.gpr .r7 = b.setWidth 32 ∧ x.mem = s.mem := by
    arun [w7, w11, wm, um]
    rw [xor_byte32, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono (WP.keep [.r7] h2 (by decide)) fun x ⟨⟨x7, xm⟩, xk⟩ => ?_
  have k₂ : VG.Proof.Rc4.Arm.Keep [.r7, .r8, .r9, .r11] s x := ((k₁.trans wk).trans xk).mono (by decide)
  have x12 : x.gpr .r12 = s.gpr .r12 := k₂.gpr (by decide)
  have hx : VG.Proof.Rc4.Arm.TableEnv x idx := ⟨(k₂.gpr (by decide)).trans h.idx, (k₂.gpr (by decide)).trans h.ones,
    by rw [x12]; exact h.fit, by rw [k₂.2.2.1, x12]; exact h.table⟩
  have x8 : x.gpr .r8 = spread (b ^^^ v) (idx.toNat % 4) 0 := (xk.gpr (by decide)).trans w8
  refine WP.mono (VG.Proof.Rc4.Arm.scatter_steps x idx _ hx 64 (by decide) x x8 (Keep.refl _ _) rfl)
    fun y ⟨ym, _, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans x7, ?_, (k₂.trans yk).mono (by decide)⟩
  rw [ym, xm, x12]
  unfold scatter spread
  rw [ite_eq_left (by omega), ite_eq_left (Nat.zero_le _), Nat.sub_zero, writeW_byte32,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.ApplyStep`. -/
section

/-! # RC4 on ARMv7: one PRGA step -/

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

theorem StepEnv.keep {s t : State} {P D L : BitVec 32} (h : VG.Proof.Rc4.Arm.StepEnv s P D L) {rs : List Reg}
    (hk : VG.Proof.Rc4.Arm.Keep rs s t) (hrs : ∀ r ∈ rs, r ≠ .r12 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r10) :
    VG.Proof.Rc4.Arm.StepEnv t P D L :=
  { h with
    p := (hk.gpr fun hm => (hrs _ hm).1 rfl).trans h.p
    d := (hk.gpr fun hm => (hrs _ hm).2.1 rfl).trans h.d
    l := (hk.gpr fun hm => (hrs _ hm).2.2.1 rfl).trans h.l
    ones := (hk.gpr fun hm => (hrs _ hm).2.2.2 rfl).trans h.ones
    table := by rw [hk.2.2.1]; exact h.table
    data := by rw [hk.2.2.1]; exact h.data }

theorem StepEnv.tableEnv {s : State} {P D L : BitVec 32} (h : VG.Proof.Rc4.Arm.StepEnv s P D L)
    {idx : Byte} (h6 : s.gpr .r6 = idx.setWidth 32) : VG.Proof.Rc4.Arm.TableEnv s idx :=
  ⟨h6, h.ones, by rw [h.p]; have := h.pfit; omega, by rw [h.p]; exact h.table⟩

theorem apply_before (s : State) (i j : Byte) {P D L : BitVec 32} (he : VG.Proof.Rc4.Arm.StepEnv s P D L)
    (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32) :
    WP isa (.block (([.dp .add .r4 .r4 (imm 1), .dp .and .r4 .r4 (imm 255)] : List Instr) ++ loadI ++
      ([.dp .add .r5 .r5 (.reg .r11), .dp .and .r5 .r5 (imm 255), .mov .r6 (.reg .r5)] :
        List Instr))) s fun t =>
      t.gpr .r4 = (i + 1#8).setWidth 32 ∧
      t.gpr .r5 = (j + s.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧
      t.gpr .r6 = t.gpr .r5 ∧ VG.Proof.Rc4.Arm.Keep [.r4, .r5, .r6, .r9, .r11] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  have h1 : WP isa (.block [.dp .add .r4 .r4 (imm 1), .dp .and .r4 .r4 (imm 255)]) s fun t =>
      t.gpr .r4 = (i + 1#8).setWidth 32 ∧ t.mem = s.mem := by
    arun [h4, byte_inc32]
  refine WP.mono (WP.keep [.r4] h1 (by decide)) fun t ⟨⟨t4, tm⟩, tk⟩ => ?_
  have het := he.keep tk (by decide)
  refine WP.mono (VG.Proof.Rc4.Arm.loadI_ok t (i + 1#8) t4 (by rw [het.p]; have := he.pfit; omega)
    (by rw [het.p]; exact VG.Proof.Rc4.Arm.region_in het.table)) fun u ⟨u11, uk, um⟩ => ?_
  rw [het.p, tm] at u11
  have u5 : u.gpr .r5 = j.setWidth 32 :=
    (uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans h5)
  have h2 : WP isa (.block [.dp .add .r5 .r5 (.reg .r11), .dp .and .r5 .r5 (imm 255),
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
      t.gpr .r6 = (a + b).setWidth 32 ∧ VG.Proof.Rc4.Arm.Keep [.r6, .r9] s t := by
  have hw' : InRegions s.wr (State.addr (P + ii.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [VG.Proof.Rc4.Arm.idx_addr hfit ii]; exact hw
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r6 = (a + b).setWidth 32) [.r6, .r9] ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  arun [h12, h4, h7, h11, hw', byte_add32]
  rw [VG.Proof.Rc4.Arm.idx_addr hfit ii, writeW_byte8, low_byte32, BitVec.add_comm b a]
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
        t.z = (BitVec.ofNat 32 (n + 1) - L == 0#32) ∧ VG.Proof.Rc4.Arm.Keep [.r0, .r9, .r11] s t := by
  have hdn : State.addr (D + BitVec.ofNat 32 n + BitVec.ofNat 32 0) =
      State.addr D + BitVec.ofNat 64 n := by
    rw [BitVec.add_zero]
    exact addr_add hfit
  have hw : InRegions s.wr (State.addr (D + BitVec.ofNat 32 n + BitVec.ofNat 32 0)) 1 := by
    rw [hdn]; exact hd
  have hr := VG.Proof.Rc4.Arm.region_in (rs := s.rd) hw
  have hadd : BitVec.ofNat 32 n + BitVec.ofNat 32 1 = BitVec.ofNat 32 (n + 1) := by
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
    (he : VG.Proof.Rc4.Arm.StepEnv s P D L) (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32)
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
      t.z = (BitVec.ofNat 32 (n + 1) - L == 0#32) ∧ VG.Proof.Rc4.Arm.Keep VG.Proof.Rc4.Arm.stepRegs s t := by
  intro p ii a jj b swapped k
  have hfit : P.toNat + 256 ≤ 2 ^ 32 := by have := he.pfit; omega
  simp only [applyStep, List.append_assoc]
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.apply_before s i j he h4 h5) fun t ⟨t4, t5, t6, tk, tm⟩ => ?_
  have het := he.keep tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.replace_core t jj ii (het.tableEnv (t6.trans t5)) t4) fun u ⟨u7, um, uk⟩ => ?_
  rw [tm, het.p] at u7 um
  have heu := het.keep uk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.loadI_ok u ii ((uk.gpr (by decide)).trans t4) (by rw [heu.p]; exact hfit)
    (by rw [heu.p]; exact VG.Proof.Rc4.Arm.region_in heu.table)) fun v ⟨v11, vk, vm⟩ => ?_
  have ha : u.mem (p + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, write_byte]
    split <;> rfl
  rw [heu.p, ha] at v11
  have hev := heu.keep vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.apply_middle v ii a b hev.p hfit
    ((vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t4))
    ((vk.gpr (by decide)).trans u7) v11
    (by rw [vk.2.2.1, uk.2.2.1, tk.2.2.1]
        exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega)
          he.table)) fun w ⟨wm, w6, wk⟩ => ?_
  rw [vm, um] at wm
  have hw : w.mem = swapped := wm
  have hew := hev.keep wk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r7, .r8, .r9, .r11] (VG.Proof.Rc4.Arm.lookup_core w (a + b) (hew.tableEnv w6))
    (by decide +kernel)) fun x ⟨⟨x7, xm⟩, xk⟩ => ?_
  rw [hew.p, hw] at x7
  have hex := hew.keep xk (by decide)
  have ktx := ((uk.trans vk).trans wk).trans xk
  have x4 : x.gpr .r4 = ii.setWidth 32 := (ktx.gpr (by decide)).trans t4
  have x5 : x.gpr .r5 = jj.setWidth 32 := (ktx.gpr (by decide)).trans t5
  have x0 : x.gpr .r0 = BitVec.ofNat 32 n := (ktx.gpr (by decide)).trans ((tk.gpr (by decide)).trans h0)
  refine WP.mono (VG.Proof.Rc4.Arm.apply_after x k hex.d hex.l x0 x7 (by have := he.dfit; omega)
    (by rw [xk.2.2.1, wk.2.2.1, vk.2.2.1, uk.2.2.1, tk.2.2.1]
        exact region_offset _ _ _ _ _ (by have := he.dfit; omega) (by omega) he.data))
    fun y ⟨ym, y0, yz, yk⟩ => ?_
  exact ⟨by rw [ym, xm, hw], (yk.gpr (by decide)).trans x4, (yk.gpr (by decide)).trans x5, y0, yz,
    (((tk.trans ktx).trans yk)).mono (by decide)⟩

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.ApplyLoop`. -/
section

/-! # RC4 on ARMv7: the stream loop -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- The context and output after the first `k` data bytes, from memory `m`. -/
def upd (m : Mem) (P D : BitVec 32) (k : Nat) : Context × List Byte :=
  update (contextAt m (State.addr P)) (bytesAt m (State.addr D) k)

theorem upd_succ (m : Mem) (P D : BitVec 32) (k : Nat) :
    VG.Proof.Rc4.Arm.upd m P D (k + 1) = ((VG.Spec.Rc4.step (VG.Proof.Rc4.Arm.upd m P D k).1).1, (VG.Proof.Rc4.Arm.upd m P D k).2 ++
      [m (State.addr D + BitVec.ofNat 64 k) ^^^ (VG.Spec.Rc4.step (VG.Proof.Rc4.Arm.upd m P D k).1).2]) := by
  unfold VG.Proof.Rc4.Arm.upd
  rw [bytes_snoc, update_snoc]

/-- What the stream loop writes: the table and the data. -/
def loopRegions (P D L : BitVec 32) : List Region :=
  [⟨State.addr P, 256⟩, ⟨State.addr D, L.toNat⟩]

/-- The stream loop after `k` bytes, from the state `b` it started in; `m₀`
is the memory on entry, which differs from `b`'s only outside the context
and the data. -/
structure LoopInv (m₀ : Mem) (P D L : BitVec 32) (b : State) (k : Nat) (t : State) : Prop where
  le : k ≤ L.toNat
  table : (contextAt t.mem (State.addr P)).table = (VG.Proof.Rc4.Arm.upd m₀ P D k).1.table
  i : t.gpr .r4 = (VG.Proof.Rc4.Arm.upd m₀ P D k).1.i.setWidth 32
  j : t.gpr .r5 = (VG.Proof.Rc4.Arm.upd m₀ P D k).1.j.setWidth 32
  data : bytesAt t.mem (State.addr D) k = (VG.Proof.Rc4.Arm.upd m₀ P D k).2
  tail : ∀ x, k ≤ x → x < L.toNat →
    t.mem (State.addr D + BitVec.ofNat 64 x) = m₀ (State.addr D + BitVec.ofNat 64 x)
  frame : Frame (VG.Proof.Rc4.Arm.loopRegions P D L) b.mem t.mem
  count : t.gpr .r0 = BitVec.ofNat 32 k
  keep : VG.Proof.Rc4.Arm.Keep VG.Proof.Rc4.Arm.stepRegs b t

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
    (he : VG.Proof.Rc4.Arm.StepEnv t P D L) (h4 : t.gpr .r4 = i.setWidth 32) (h5 : t.gpr .r5 = j.setWidth 32)
    (h0 : t.gpr .r0 = BitVec.ofNat 32 k) (hk : k < L.toNat) :
    let next := VG.Spec.Rc4.step { table := (contextAt t.mem (State.addr P)).table, i, j }
    WP isa (.block applyStep) t fun u =>
      (contextAt u.mem (State.addr P)).table = next.1.table ∧
      u.gpr .r4 = next.1.i.setWidth 32 ∧ u.gpr .r5 = next.1.j.setWidth 32 ∧
      u.mem (State.addr D + BitVec.ofNat 64 k) =
        t.mem (State.addr D + BitVec.ofNat 64 k) ^^^ next.2 ∧
      (∀ x, ¬ (x - State.addr P).toNat < 256 → x ≠ State.addr D + BitVec.ofNat 64 k →
        u.mem x = t.mem x) ∧
      Frame (VG.Proof.Rc4.Arm.loopRegions P D L) t.mem u.mem ∧
      u.gpr .r0 = BitVec.ofNat 32 (k + 1) ∧
      u.z = (BitVec.ofNat 32 (k + 1) - L == 0#32) ∧ VG.Proof.Rc4.Arm.Keep VG.Proof.Rc4.Arm.stepRegs t u := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (VG.Proof.Rc4.Arm.apply_step t i j he h4 h5 h0 hk)
    fun u ⟨hum, hu4, hu5, hu0, huz, huk⟩ => ?_
  have hdk : ¬ (State.addr D + BitVec.ofNat 64 k - State.addr P).toNat < 256 := by
    have hin : (State.addr D + BitVec.ofNat 64 k - State.addr D).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hk
    exact fun h => he.sTD _ h hin
  have hTD : Mem.Sep (State.addr P) 256 (State.addr D + BitVec.ofNat 64 k) 1 :=
    sep_offset_right he.sTD (by omega) (by omega)
  refine ⟨?_, hu4, hu5, ?_, ?_, ?_, hu0, huz, huk⟩
  · rw [hum, table_write_sep _ _ _ _ hTD, table_swap]
  · rw [hum, write_byte, ite_eq_left rfl, swap_frame _ _ _ _ _ hdk]
    have ht := table_swap t.mem (State.addr P) (i + 1#8)
      (j + t.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · intro x hT hD
    rw [hum]
    exact VG.Proof.Rc4.Arm.step_other hT hD
  · rw [hum]
    have hP : (⟨State.addr P, 256⟩ : Region) ∈ VG.Proof.Rc4.Arm.loopRegions P D L := List.mem_cons_self
    have hD : (⟨State.addr D, L.toNat⟩ : Region) ∈ VG.Proof.Rc4.Arm.loopRegions P D L :=
      List.mem_cons_of_mem _ List.mem_cons_self
    refine Frame.write ?_ hD _ (Offset.contains_base _ (by omega) (by omega))
    refine Frame.write ?_ hP _ (Offset.contains_base _ (by omega) (by omega))
    exact Frame.write (Frame.refl _ _) hP _ (Offset.contains_base _ (by omega) (by omega))

theorem loop_step (m₀ : Mem) {P D L : BitVec 32} (b : State) (hb : VG.Proof.Rc4.Arm.StepEnv b P D L) {k : Nat}
    (hk : k < L.toNat) (t : State) (ht : VG.Proof.Rc4.Arm.LoopInv m₀ P D L b k t) :
    WP isa (.block applyStep) t fun u => VG.Proof.Rc4.Arm.LoopInv m₀ P D L b (k + 1) u ∧
      u.z = (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  have he := hb.keep ht.keep (by decide)
  have hsD : ∀ x, x < L.toNat →
      ¬ (State.addr D + BitVec.ofNat 64 x - State.addr P).toNat < 256 := by
    intro x hx
    have hin : (State.addr D + BitVec.ofNat 64 x - State.addr D).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hx
    exact fun h => hb.sTD _ h hin
  have hctx : (⟨(contextAt t.mem (State.addr P)).table, (VG.Proof.Rc4.Arm.upd m₀ P D k).1.i,
      (VG.Proof.Rc4.Arm.upd m₀ P D k).1.j⟩ : Context) = (VG.Proof.Rc4.Arm.upd m₀ P D k).1 := context_ext ht.table rfl rfl
  have hst := VG.Proof.Rc4.Arm.apply_step_table t (VG.Proof.Rc4.Arm.upd m₀ P D k).1.i (VG.Proof.Rc4.Arm.upd m₀ P D k).1.j he ht.i ht.j ht.count hk
  rw [hctx] at hst
  refine WP.mono hst fun u ⟨htab, hui, huj, hbyte, hother, hfr, hu0, huz, huk⟩ => ⟨?_, huz⟩
  have hkeep : ∀ x, x < L.toNat → x ≠ k →
      u.mem (State.addr D + BitVec.ofNat 64 x) = t.mem (State.addr D + BitVec.ofNat 64 x) :=
    fun x hx hne => hother _ (hsD x hx) (data_ne hx hk hne)
  refine
    { le := hk
      table := by rw [VG.Proof.Rc4.Arm.upd_succ]; exact htab
      i := by rw [VG.Proof.Rc4.Arm.upd_succ]; exact hui
      j := by rw [VG.Proof.Rc4.Arm.upd_succ]; exact huj
      data := ?_
      tail := fun x hx hxL => by
        rw [hkeep x hxL (by omega)]
        exact ht.tail x (by omega) hxL
      frame := ht.frame.trans hfr
      count := hu0
      keep := (ht.keep.trans huk).mono (by decide) }
  rw [bytes_snoc, VG.Proof.Rc4.Arm.upd_succ, hbyte, ht.tail k (Nat.le_refl _) hk, ← ht.data]
  refine congrArg (· ++ _) ?_
  exact bytes_frame _ _ _ _ fun x hx => hkeep x (by omega) (by omega)

theorem apply_loop (m₀ : Mem) {P D L : BitVec 32} (b : State) (hb : VG.Proof.Rc4.Arm.StepEnv b P D L) {k : Nat}
    (hk : k < L.toNat) (t : State) (ht : VG.Proof.Rc4.Arm.LoopInv m₀ P D L b k t) :
    WP isa (.loop (.block applyStep) .ne) t (VG.Proof.Rc4.Arm.LoopInv m₀ P D L b L.toNat) := by
  refine WP.loop (M := isa)
    (fun rem u => ∃ j, j < L.toNat ∧ rem = L.toNat - j ∧ VG.Proof.Rc4.Arm.LoopInv m₀ P D L b j u)
    ?_ (L.toNat - k) t ⟨k, hk, rfl, ht⟩
  intro rem u ⟨j, hj, hrem, hu⟩
  refine WP.mono (VG.Proof.Rc4.Arm.loop_step m₀ b hb hj u hu) fun v ⟨hv, hz⟩ => ?_
  by_cases hend : j + 1 = L.toNat
  · left
    refine ⟨?_, hend ▸ hv⟩
    rw [hend, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self] at hz
    rw [VG.Proof.Rc4.Arm.eval_ne, hz]
    rfl
  · right
    have hL := L.isLt
    have hnz : BitVec.ofNat 32 (j + 1) - L ≠ 0#32 := by
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega
    refine ⟨?_, L.toNat - (j + 1), by omega, j + 1, by omega, rfl, hv⟩
    rw [VG.Proof.Rc4.Arm.eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Schedule`. -/
section

/-! # RC4 on ARMv7: key scheduling -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- The address of byte `r` of the table at `P`. -/
theorem idx_addr' {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) {r : Nat} (hr : r < 256) :
    State.addr (P + BitVec.ofNat 32 r + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 r := by
  rw [BitVec.add_zero]
  exact addr_add (by omega)

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem (State.addr (s₀.gpr .r12)) r ∧ VG.Proof.Rc4.Arm.Keep [.r4, .r9] s₀ s ∧
    s.gpr .r4 = BitVec.ofNat 32 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr (State.addr (s₀.gpr .r12)) 256) (h : VG.Proof.Rc4.Arm.IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => VG.Proof.Rc4.Arm.IdentityInv s₀ (r + 1) t ∧
      t.z = (BitVec.ofNat 32 r + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32) := by
  obtain ⟨hm, hk, h4⟩ := h
  have h12 : s.gpr .r12 = s₀.gpr .r12 := hk.gpr (by decide)
  have hw : InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 r + BitVec.ofNat 32 0)) 1 := by
    rw [h12, VG.Proof.Rc4.Arm.idx_addr' hfit hr, hk.2.2.1]
    exact region_offset _ _ _ _ _ (by omega) (by omega) hp
  have hadd : BitVec.ofNat 32 r + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
    rw [← BitVec.ofNat_add]
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = identityMem s₀.mem (State.addr (s₀.gpr .r12)) (r + 1) ∧
      t.gpr .r4 = BitVec.ofNat 32 (r + 1) ∧
      t.z = (BitVec.ofNat 32 r + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32)) [.r4, .r9] ?_
    (by decide)) fun t ⟨⟨tm, t4, tz⟩, tk⟩ => ⟨⟨tm, (hk.trans tk).mono (by decide), t4⟩, tz⟩
  unfold identityStep
  arun [h4, hw, hadd]
  rw [h12, VG.Proof.Rc4.Arm.idx_addr' hfit hr, hm, writeW_byte8, ofNat_low32, identityMem_store _ _ _ hr]

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr (State.addr (s₀.gpr .r12)) 256) (h : VG.Proof.Rc4.Arm.IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) .ne) s (VG.Proof.Rc4.Arm.IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ VG.Proof.Rc4.Arm.IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (VG.Proof.Rc4.Arm.identity_step s₀ t hj hfit hp ht) fun u ⟨hu, hz⟩ => ?_
  have hadd : BitVec.ofNat 32 j + BitVec.ofNat 32 1 = BitVec.ofNat 32 (j + 1) := by
    rw [← BitVec.ofNat_add]
  rw [hadd] at hz
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [VG.Proof.Rc4.Arm.eval_ne, hz, hend]
    rfl
  · right
    have hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    rw [VG.Proof.Rc4.Arm.eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
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

theorem ScheduleEnv.keep {s t : State} {P K Lk : BitVec 32} (h : VG.Proof.Rc4.Arm.ScheduleEnv s P K Lk)
    {rs : List Reg} (hk : VG.Proof.Rc4.Arm.Keep rs s t) (hrs : ∀ r ∈ rs, r ≠ .r12 ∧ r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r10) :
    VG.Proof.Rc4.Arm.ScheduleEnv t P K Lk :=
  { h with
    p := (hk.gpr fun hm => (hrs _ hm).1 rfl).trans h.p
    k := (hk.gpr fun hm => (hrs _ hm).2.1 rfl).trans h.k
    l := (hk.gpr fun hm => (hrs _ hm).2.2.1 rfl).trans h.l
    ones := (hk.gpr fun hm => (hrs _ hm).2.2.2 rfl).trans h.ones
    table := by rw [hk.2.2.1]; exact h.table
    key := by rw [hk.2.1, hk.2.2.1]; exact h.key }

theorem ScheduleEnv.tableEnv {s : State} {P K Lk : BitVec 32} (h : VG.Proof.Rc4.Arm.ScheduleEnv s P K Lk)
    {idx : Byte} (h6 : s.gpr .r6 = idx.setWidth 32) : VG.Proof.Rc4.Arm.TableEnv s idx :=
  ⟨h6, h.ones, by rw [h.p]; exact h.fit, by rw [h.p]; exact h.table⟩

theorem schedule_before (s : State) (i j : Byte) {P K Lk : BitVec 32} {o : Nat}
    (he : VG.Proof.Rc4.Arm.ScheduleEnv s P K Lk) (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 o) (ho : o < Lk.toNat) :
    WP isa (.block (loadI ++ ([.dp .add .r5 .r5 (.reg .r11), .dp .add .r9 .r0 (.reg .r2),
      .ldrb .r9 .r9 0, .dp .add .r5 .r5 (.reg .r9), .dp .and .r5 .r5 (imm 255),
      .mov .r6 (.reg .r5)] : List Instr))) s
      fun t => t.gpr .r5 = (j + s.mem (State.addr P + BitVec.ofNat 64 i.toNat) +
          s.mem (State.addr K + BitVec.ofNat 64 o)).setWidth 32 ∧ t.gpr .r6 = t.gpr .r5 ∧
        VG.Proof.Rc4.Arm.Keep [.r5, .r6, .r9, .r11] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.loadI_ok s i h4 (by rw [he.p]; exact he.fit) (by rw [he.p]; exact VG.Proof.Rc4.Arm.region_in he.table))
    fun t ⟨t11, tk, tm⟩ => ?_
  rw [he.p] at t11
  have t5 : t.gpr .r5 = j.setWidth 32 := (tk.gpr (by decide)).trans h5
  have t0 : t.gpr .r0 = K := (tk.gpr (by decide)).trans he.k
  have t2 : t.gpr .r2 = BitVec.ofNat 32 o := (tk.gpr (by decide)).trans h2
  have hka : State.addr (K + BitVec.ofNat 32 o + BitVec.ofNat 32 0) =
      State.addr K + BitVec.ofNat 64 o := by
    rw [BitVec.add_zero]
    exact addr_add (by have := he.keyFit; omega)
  have hk : InRegions (t.rd ++ t.wr) (State.addr (K + BitVec.ofNat 32 o + BitVec.ofNat 32 0)) 1 := by
    rw [hka, tk.2.1, tk.2.2.1]
    exact region_offset _ _ _ _ _ (by have := he.keyFit; omega) (by omega) he.key
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
  rw [VG.Proof.Rc4.Arm.adc_mask']
  by_cases h : x.toNat < L.toNat
  · rw [ite_eq_right (by simp only [decide_eq_true_eq]; omega), ite_eq_left h]
  · rw [ite_eq_left (by simp only [decide_eq_true_eq]; omega), ite_eq_right h]
    rfl

theorem schedule_after (s : State) (i b : Byte) {P K Lk : BitVec 32}
    (he : VG.Proof.Rc4.Arm.ScheduleEnv s P K Lk) (h4 : s.gpr .r4 = i.setWidth 32) (h7 : s.gpr .r7 = b.setWidth 32) :
    WP isa (.block [.dp .add .r2 .r2 (imm 1), .cmp .r2 (.reg .r1), .adc .r9 .r10 (imm 0),
      .dp .and .r2 .r2 (.reg .r9), .dp .add .r9 .r12 (.reg .r4), .strb .r7 .r9 0,
      .dp .add .r4 .r4 (imm 1), .cmp .r4 (imm 256)]) s fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r2 = (if (s.gpr .r2 + BitVec.ofNat 32 1).toNat < Lk.toNat then
        s.gpr .r2 + BitVec.ofNat 32 1 else 0#32) ∧
      t.gpr .r4 = i.setWidth 32 + BitVec.ofNat 32 1 ∧
      t.z = (i.setWidth 32 + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32) ∧
      VG.Proof.Rc4.Arm.Keep [.r2, .r4, .r9] s t := by
  have hw : InRegions s.wr (State.addr (P + i.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [VG.Proof.Rc4.Arm.idx_addr he.fit i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega) (by have := i.isLt; omega) he.table
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r2 = (if (s.gpr .r2 + BitVec.ofNat 32 1).toNat < Lk.toNat then
        s.gpr .r2 + BitVec.ofNat 32 1 else 0#32) ∧
      t.gpr .r4 = i.setWidth 32 + BitVec.ofNat 32 1 ∧
      t.z = (i.setWidth 32 + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32)) [.r2, .r4, .r9] ?_
    (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  arun [he.p, he.l, he.ones, h4, h7, hw]
  rw [VG.Proof.Rc4.Arm.idx_addr he.fit i, writeW_byte8, low_byte32, VG.Proof.Rc4.Arm.next_off]
  conj_rfl

/-- One key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte) {P K Lk : BitVec 32} {o : Nat}
    (he : VG.Proof.Rc4.Arm.ScheduleEnv s P K Lk) (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32)
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
      VG.Proof.Rc4.Arm.Keep [.r2, .r4, .r5, .r6, .r7, .r8, .r9, .r11] s t := by
  intro p a jj b
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.schedule_before s i j he h4 h5 h2 ho) fun t ⟨t5, t6, tk, tm⟩ => ?_
  have het := he.keep tk (by decide)
  refine WP.mono (VG.Proof.Rc4.Arm.replace_core t jj i (het.tableEnv (t6.trans t5)) ((tk.gpr (by decide)).trans h4))
    fun u ⟨u7, um, uk⟩ => ?_
  rw [tm, het.p] at u7 um
  have heu := het.keep uk (by decide)
  refine WP.mono (VG.Proof.Rc4.Arm.schedule_after u i b heu ((uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans h4))
    u7) fun v ⟨vm, v2, v4, vz, vk⟩ => ?_
  refine ⟨by rw [vm, um], ?_, (vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t5), v4, vz,
    ((tk.trans uk).trans vk).mono (by decide)⟩
  rw [v2, (uk.gpr (by decide) : u.gpr .r2 = t.gpr .r2), (tk.gpr (by decide) : t.gpr .r2 = s.gpr .r2), h2]

/-- The key bytes, at `K` (32-bit), `Lk` of them. -/
def keyOf (m : Mem) (K Lk : BitVec 32) : List Byte := bytesAt m (State.addr K) Lk.toNat

structure ScheduleInv (s₀ : State) (P K Lk : BitVec 32) (r : Nat) (s : State) : Prop where
  frame : TableFrame (State.addr P) s₀.mem s.mem
  table : (contextAt s.mem (State.addr P)).table = (schedulePrefix (VG.Proof.Rc4.Arm.keyOf s₀.mem K Lk) r).1
  j : s.gpr .r5 = (schedulePrefix (VG.Proof.Rc4.Arm.keyOf s₀.mem K Lk) r).2.setWidth 32
  i : s.gpr .r4 = BitVec.ofNat 32 r
  off : s.gpr .r2 = BitVec.ofNat 32 (r % Lk.toNat)
  keep : VG.Proof.Rc4.Arm.Keep [.r2, .r4, .r5, .r6, .r7, .r8, .r9, .r11] s₀ s

theorem schedule_inv_step (s₀ s : State) {P K Lk : BitVec 32} {r : Nat} (hr : r < 256)
    (he₀ : VG.Proof.Rc4.Arm.ScheduleEnv s₀ P K Lk) (h : VG.Proof.Rc4.Arm.ScheduleInv s₀ P K Lk r s) :
    WP isa (.block scheduleStep) s fun t => VG.Proof.Rc4.Arm.ScheduleInv s₀ P K Lk (r + 1) t ∧
      t.z = (BitVec.ofNat 32 (r + 1) - BitVec.ofNat 32 256 == 0#32) := by
  let key := VG.Proof.Rc4.Arm.keyOf s₀.mem K Lk
  let st := schedulePrefix key r
  have hlen := he₀.len
  have he := he₀.keep h.keep (by decide)
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .r4 = (BitVec.ofNat 8 r).setWidth 32 := by
    rw [h.i, byte32, hrt]
  have hmod := Nat.mod_lt r (show 0 < Lk.toNat by omega)
  have hkeybyte : s.mem (State.addr K + BitVec.ofNat 64 (r % Lk.toNat)) =
      key.getD (r % key.length) 0 := by
    have hsep := he₀.keySep (State.addr K + BitVec.ofNat 64 (r % Lk.toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, VG.Proof.Rc4.Arm.keyOf]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem (State.addr P + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    have hg := table_get s.mem (State.addr P) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (VG.Proof.Rc4.Arm.schedule_step s _ _ he hi h.j h.off hmod)
    fun t ⟨tm, t2, t5, t4, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 32 + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
    rw [byte32, hrt, ← BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (h.keep.trans tk).mono (by decide)⟩, ?_⟩
  · rw [tm]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, table_swap, h.table, hnext, hrt]
    rw [htablebyte, hkeybyte]
  · rw [t5, hrt, htablebyte, hkeybyte, hnext]
  · rw [t4, hcast]
  · rw [t2]
    exact key_next32 r _ (by omega) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) {P K Lk : BitVec 32} {r : Nat} (hr : r < 256)
    (he₀ : VG.Proof.Rc4.Arm.ScheduleEnv s₀ P K Lk) (h : VG.Proof.Rc4.Arm.ScheduleInv s₀ P K Lk r s) :
    WP isa (.loop (.block scheduleStep) .ne) s (VG.Proof.Rc4.Arm.ScheduleInv s₀ P K Lk 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ VG.Proof.Rc4.Arm.ScheduleInv s₀ P K Lk j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (VG.Proof.Rc4.Arm.schedule_inv_step s₀ t hj he₀ ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [VG.Proof.Rc4.Arm.eval_ne, hz, hend]
    rfl
  · right
    have hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    rw [VG.Proof.Rc4.Arm.eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Contract`. -/
section

/-!
# RC4 on ARMv7: the contracts the proofs use

`Proof.Rc4.initScratchContract` and `Proof.Rc4.applyScratchContract` spelled
out for ARMv7: every argument is in a register, and no stack is used.
-/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Spec.Rc4

def initC : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let ctx : Region := ⟨State.addr (s.gpr .r2), 258⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 64⟩
    s.rd = [key] ∧ s.wr = [ctx, scratch] ∧ key.Disjoint ctx ∧ key.Disjoint scratch ∧
      ctx.Disjoint scratch ∧ (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 258 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 64 ≤ 2 ^ 32
  post s s' :=
    match VG.Spec.Rc4.init (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) with
    | .ok c => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        contextAt s'.mem (State.addr (s.gpr .r2)) = c
    | .error .invalidKeyLength => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

def applyC : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 258⟩
    let data : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 64⟩
    s.rd = [] ∧ s.wr = [ctx, data, scratch] ∧ ctx.Disjoint data ∧ ctx.Disjoint scratch ∧
      data.Disjoint scratch ∧ (s.gpr .r0).toNat + 258 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 64 ≤ 2 ^ 32
  post s s' :=
    let result := update (contextAt s.mem (State.addr (s.gpr .r0)))
      (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
    contextAt s'.mem (State.addr (s.gpr .r0)) = result.1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat = result.2
  pub s₁ s₂ := (s₁.sp = s₂.sp ∧
      [(contextAt s₁.mem (State.addr (s₁.gpr .r0))).i.toNat] =
        [(contextAt s₂.mem (State.addr (s₂.gpr .r0))).i.toNat]) ∧
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

/-- `init(0x1000, 1, 0x2000, 0x3000)`. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩, ⟨0x3000, 64⟩]

/-- `apply(0x1000, 0x2000, 1, 0x3000)`. -/
def applySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 1 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩, ⟨0x3000, 64⟩]

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Init`. -/
section

/-! # RC4 on ARMv7: checked initialization -/

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
      t.mem = Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved ∧ VG.Proof.Rc4.Arm.Keep [] s t := by
  refine WP.mono (WP.keep [] (Spill.save_block_ok VG.Proof.Rc4.Arm.saved_slots (by omega) fun d _ hd =>
    region_offset _ _ _ _ _ (by omega) (by omega) hw) (by decide)) fun t ⟨h, hk⟩ => ⟨h.2.2.2, hk⟩

/-- What saving changes: the first 32 bytes of `scratch`. -/
theorem save_frame (m : Mem) (S : Addr) (g : Reg → BitVec 32) :
    Frame [⟨S, 64⟩] m (Spill.saveMem m S g saved) :=
  Spill.saveMem_frame _ _ _ (by decide) _ (by decide)

/-- The saved registers survive writes to the table. -/
theorem saved_after {m m' : Mem} {S P : Addr} {g : Reg → BitVec 32}
    (h : Spill.Saved m S g saved) (hf : Frame [⟨P, 258⟩] m m')
    (hd : Region.Disjoint ⟨P, 258⟩ ⟨S, 64⟩) : Spill.Saved m' S g saved := by
  refine h.frame VG.Proof.Rc4.Arm.saved_slots hf fun r hr => ?_
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
      VG.Proof.Rc4.Arm.Keep [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧ t.mem = s.mem := by
  refine WP.mono (Spill.restore_block_ok VG.Proof.Rc4.Arm.saved_slots VG.Proof.Rc4.Arm.saved_restorable (by omega)
    (fun d _ hd => region_offset _ _ _ _ _ (by omega) (by omega) hr) hs)
    fun t ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨fun r hr => Spill.restored_reg h₁ hr,
      ⟨fun r hr => h₂ r (by rw [VG.Proof.Rc4.Arm.saved_regs]; exact hr), h₄, h₅, h₆⟩, h₃⟩

/-! ## Initialization -/

theorem init_finish (s : State) {P : BitVec 32} (h12 : s.gpr .r12 = P)
    (hfit : P.toNat + 258 ≤ 2 ^ 32) (hp : InRegions s.wr (State.addr P) 258) :
    WP isa (.block [.mov .r9 (imm 0), .strb .r9 .r12 256, .strb .r9 .r12 257]) s
      fun t => t.mem = (s.mem.write (State.addr P + 256#64) 1 0#8).write
          (State.addr P + 257#64) 1 0#8 ∧ VG.Proof.Rc4.Arm.Keep [.r9] s t := by
  have a256 : State.addr (P + BitVec.ofNat 32 256) = State.addr P + 256#64 := addr_add (by omega)
  have a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega)
  have h256 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 256)) 1 := by
    rw [a256]; exact region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 257)) 1 := by
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
  have hctx : InRegions s.wr (State.addr P) 258 := ⟨_, by rw [hwr]; exact List.mem_cons_self,
    Region.contains_self _ _⟩
  have hscr : InRegions s.wr (State.addr Sc) 64 := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  have htab : InRegions s.wr (State.addr P) 256 := by
    have h' := region_offset _ _ _ 0 256 (by decide) (by decide) hctx
    simpa only [BitVec.add_zero] using h'
  unfold initValid
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.save_ok s (by rw [hS]; exact sfit) (by rw [hS]; exact hscr))
    fun a ⟨ham, hak⟩ => ?_
  rw [hS] at ham
  have haf : Frame [⟨State.addr Sc, 64⟩] s.mem a.mem := by rw [ham]; exact VG.Proof.Rc4.Arm.save_frame _ _ _
  have hb : WP isa (.block [.mov .r12 (.reg .r2), .mov .r4 (imm 0)]) a fun b =>
      b.gpr .r12 = P ∧ b.gpr .r4 = 0#32 ∧ b.mem = a.mem := by
    arun [hak.gpr (r := .r2) (by decide), hP]
  refine WP.mono (WP.keep [.r12, .r4] hb (by decide)) fun b ⟨⟨hb12, hb4, hbm⟩, hbk⟩ => ?_
  have kb : VG.Proof.Rc4.Arm.Keep [.r12, .r4] s b := (hak.trans hbk).mono (by decide)
  have hpb : InRegions b.wr (State.addr (b.gpr .r12)) 256 := by rw [kb.2.2.1, hb12]; exact htab
  have hfit : (b.gpr .r12).toNat + 256 ≤ 2 ^ 32 := by rw [hb12]; omega
  have hib : VG.Proof.Rc4.Arm.IdentityInv b 0 b := ⟨by rw [identityMem_zero], Keep.refl _ _, hb4⟩
  refine WP.seq (WP.mono (VG.Proof.Rc4.Arm.identity_loop b b (by decide) hfit hpb hib) fun c hc => ?_)
  obtain ⟨hcm, hck, _⟩ := hc
  have hd : WP isa (.block (([.mov .r4 (imm 0), .mov .r2 (imm 0), .mov .r5 (imm 0)] : List Instr) ++
      ones)) c fun d => d.gpr .r4 = 0#32 ∧ d.gpr .r2 = 0#32 ∧ d.gpr .r5 = 0#32 ∧
        d.gpr .r10 = BitVec.allOnes 32 ∧ d.mem = c.mem := by
    unfold ones
    arun [VG.Proof.Rc4.Arm.ones_eq]
  refine WP.seq (WP.mono (WP.keep [.r4, .r2, .r5, .r10] hd (by decide))
    fun d ⟨⟨hd4, hd2, hd5, hd10, hdm⟩, hdk⟩ => ?_)
  have kd : VG.Proof.Rc4.Arm.Keep [.r4, .r2, .r5, .r10, .r9, .r12] s d :=
    ((kb.trans (hck.trans hdk)).mono (by decide))
  have hd12 : d.gpr .r12 = P := ((hck.trans hdk).gpr (by decide)).trans hb12
  have hdmem : d.mem = identityMem a.mem (State.addr P) 256 := by rw [hdm, hcm, hbm, hb12]
  -- The key is untouched by the saves and the identity permutation.
  have hkey : VG.Proof.Rc4.Arm.keyOf d.mem K Lk = bytesAt s.mem (State.addr K) Lk.toNat := by
    unfold VG.Proof.Rc4.Arm.keyOf bytesAt
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    have hin : (⟨State.addr K, Lk.toNat⟩ : Region).Contains (State.addr K + BitVec.ofNat 64 k) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    rw [hdmem, identityMem_frame _ _ _ (by decide) _ fun hl =>
      kc _ hin (by simp only [Region.Contains] at hl ⊢; omega)]
    exact haf _ fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ks _ hin
  have hen : VG.Proof.Rc4.Arm.ScheduleEnv d P K Lk :=
    { p := hd12
      k := (kd.gpr (by decide)).trans hK
      l := (kd.gpr (by decide)).trans hL
      ones := hd10
      len := hlen
      fit := by omega
      table := by rw [kd.2.2.1]; exact htab
      key := by
        rw [kd.2.1, kd.2.2.1, hrd]
        exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
      keyFit := kfit
      keySep := fun x h₁ h₂ => kc x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega) }
  have hid : VG.Proof.Rc4.Arm.ScheduleInv d P K Lk 0 d := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, Keep.refl _ _⟩
    · rw [hdmem, identityMem_table, schedule_zero]
    · rw [hd5]; rfl
    · rw [hd4]
    · rw [hd2, Nat.zero_mod]
  refine WP.seq (WP.mono (VG.Proof.Rc4.Arm.schedule_loop d d (by decide) hen hid) fun e he => ?_)
  have ke : VG.Proof.Rc4.Arm.Keep [.r4, .r2, .r5, .r10, .r9, .r12, .r6, .r7, .r8, .r11] s e :=
    (kd.trans he.keep).mono (by decide)
  have he12 : e.gpr .r12 = P := (he.keep.gpr (by decide)).trans hd12
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.init_finish e he12 cfit (by rw [ke.2.2.1]; exact hctx)) fun f ⟨hfm, hfk⟩ => ?_
  have kf : VG.Proof.Rc4.Arm.Keep [.r4, .r2, .r5, .r10, .r9, .r12, .r6, .r7, .r8, .r11] s f :=
    (ke.trans hfk).mono (by decide)
  have hctxf : Frame [⟨State.addr P, 258⟩] a.mem f.mem := by
    rw [hfm]
    refine frame_finish ?_ _ _
    have h1 := frame_of_table he.frame
    have h0 := frame_of_table (identityMem_frame a.mem (State.addr P) 256 (by decide))
    rw [hdmem] at h1
    exact h0.trans h1
  have hf3 : f.gpr .r3 = Sc := (kf.gpr (by decide)).trans hS
  have hsaved : Spill.Saved f.mem (State.addr (f.gpr .r3)) s.gpr saved := by
    rw [hf3]
    refine VG.Proof.Rc4.Arm.saved_after ?_ hctxf cs
    rw [ham]
    exact Spill.saveMem_saved _ _ _ _ VG.Proof.Rc4.Arm.saved_slots
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.restore_ok f (by rw [hf3]; exact sfit)
    (by rw [kf.2.1, kf.2.2.1, hf3]; exact VG.Proof.Rc4.Arm.region_in hscr) hsaved)
    fun g ⟨hgr, hgk, hgm⟩ => ?_
  have h0 : WP isa (.block [.mov .r0 (imm 0)]) g fun t => t.gpr .r0 = 0#32 ∧ t.mem = g.mem := by
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
    · rw [hgk.gpr (by rw [← VG.Proof.Rc4.Arm.saved_regs]; exact hs)]
      have : r = .lr := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [VG.Proof.Rc4.Arm.saved_regs] at hs
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
  omega

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State) (hs : initC.pre s) :
    WP isa VG.Impl.Rc4.Arm.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) with
      | .ok ctx => t.gpr .r0 = 0#32 ∧ contextAt t.mem (State.addr (s.gpr .r2)) = ctx
      | .error .invalidKeyLength => t.gpr .r0 = 1#32) ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  have hcheck : WP isa (.block [.dp .sub .r12 .r1 (imm 1), .mov .r12 (.shifted .r12 .lsr 8),
      .cmp .r12 (imm 0)]) s fun t => t.mem = s.mem ∧
      t.z = decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) := by
    arun
    exact VG.Proof.Rc4.Arm.valid_len _
  unfold VG.Impl.Rc4.Arm.init
  refine WP.seq (WP.mono (WP.keep [.r12] hcheck (by decide)) fun t ⟨⟨htm, htz⟩, htk⟩ => ?_)
  have htp : initC.pre t := by
    obtain ⟨hrd, hwr, h⟩ := hs
    refine ⟨?_, ?_, ?_⟩ <;> simp only [htk.2.1, htk.2.2.1, htk.gpr (r := .r0) (by decide),
      htk.gpr (r := .r1) (by decide), htk.gpr (r := .r2) (by decide),
      htk.gpr (r := .r3) (by decide)] <;> with_reducible assumption
  have hreg (r : Reg) (hr : r ≠ .r12) : t.gpr r = s.gpr r := htk.gpr (by simpa using hr)
  refine WP.ite (!t.z) rfl (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) := by
      intro hg; rw [htz, decide_eq_true hg] at hn; exact absurd hn (by decide)
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    have h1 : WP isa (.block [.mov .r0 (imm 1)]) t fun u => u.gpr .r0 = 1#32 := by
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
    refine WP.mono (VG.Proof.Rc4.Arm.init_valid t htp (by rw [hreg .r1 (by decide)]; exact hg))
      fun u ⟨hu0, huc, hup, husp⟩ => ?_
    rw [hreg .r0 (by decide), hreg .r1 (by decide), hreg .r2 (by decide), htm] at huc
    refine ⟨⟨hu0, huc⟩, fun r hr => ?_, husp.trans htk.2.2.2⟩
    rw [hup r hr]
    refine hreg r ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Apply`. -/
section

/-! # RC4 on ARMv7: the stream function -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

theorem apply_entry (s : State) (hs : applyC.pre s) :
    WP isa (.block entry) s fun a => a.mem = s.mem ∧ VG.Proof.Rc4.Arm.Keep [.r12] s a ∧
      a.gpr .r12 = (contextAt s.mem (State.addr (s.gpr .r0))).i.setWidth 32 ∧
      a.z = (s.gpr .r2 - BitVec.ofNat 32 0 == 0#32) := by
  obtain ⟨_, hwr, _, _, _, cfit, _, _⟩ := hs
  have a256 : State.addr (s.gpr .r0 + BitVec.ofNat 32 256) = State.addr (s.gpr .r0) + 256#64 :=
    addr_add (a := s.gpr .r0) (k := 256) (by omega)
  have r256 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 256)) 1 := by
    rw [a256]
    refine VG.Proof.Rc4.Arm.region_in (region_offset _ _ 258 256 1 (by decide) (by decide) ?_)
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
    WP isa (.block start) b fun c => c.mem = b.mem ∧ VG.Proof.Rc4.Arm.Keep [.r4, .r12, .r5, .r0, .r10] b c ∧
      c.gpr .r4 = b.gpr .r12 ∧ c.gpr .r12 = P ∧
      c.gpr .r5 = (b.mem (State.addr P + 257#64)).setWidth 32 ∧ c.gpr .r0 = 0#32 ∧
      c.gpr .r10 = BitVec.allOnes 32 := by
  have a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega)
  have r257 : InRegions (b.rd ++ b.wr) (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact h257
  refine WP.mono (WP.keep (Q := fun c => c.mem = b.mem ∧ c.gpr .r4 = b.gpr .r12 ∧
      c.gpr .r12 = P ∧ c.gpr .r5 = (b.mem (State.addr P + 257#64)).setWidth 32 ∧
      c.gpr .r0 = 0#32 ∧ c.gpr .r10 = BitVec.allOnes 32) [.r4, .r12, .r5, .r0, .r10] ?_
    (by decide)) fun c ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold start ones
  arun [h0, r257, VG.Proof.Rc4.Arm.ones_eq]
  rw [a257]
  conj_rfl

theorem apply_finish (d : State) (i j : Byte) {P : BitVec 32} (hfit : P.toNat + 258 ≤ 2 ^ 32)
    (h4 : d.gpr .r4 = i.setWidth 32) (h5 : d.gpr .r5 = j.setWidth 32) (h12 : d.gpr .r12 = P)
    (hw : InRegions d.wr (State.addr P) 258) :
    WP isa (.block finish) d fun e =>
      e.mem = (d.mem.write (State.addr P + 256#64) 1 i).write (State.addr P + 257#64) 1 j ∧
      VG.Proof.Rc4.Arm.Keep [] d e := by
  have a256 : State.addr (P + BitVec.ofNat 32 256) = State.addr P + 256#64 := addr_add (by omega)
  have a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega)
  have h256 : InRegions d.wr (State.addr (P + BitVec.ofNat 32 256)) 1 := by
    rw [a256]; exact region_offset _ _ _ 256 1 (by decide) (by decide) hw
  have h257 : InRegions d.wr (State.addr (P + BitVec.ofNat 32 257)) 1 := by
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
  unfold VG.Proof.Rc4.Arm.applyC
  dsimp only
  generalize hP : s.gpr .r0 = P at hwr cd cs cfit ⊢
  generalize hD : s.gpr .r1 = D at hwr cd ds dfit ⊢
  generalize hL : s.gpr .r2 = L at hwr cd ds dfit ⊢
  generalize hS : s.gpr .r3 = Sc at hwr cs ds sfit
  have hctx : InRegions s.wr (State.addr P) 258 := ⟨_, by rw [hwr]; exact List.mem_cons_self,
    Region.contains_self _ _⟩
  have hdat : InRegions s.wr (State.addr D) L.toNat := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  have hscr : InRegions s.wr (State.addr Sc) 64 := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    Region.contains_self _ _⟩
  have hpres (t : State) (rs : List Reg) (hk : VG.Proof.Rc4.Arm.Keep rs s t) (hr : ∀ r ∈ preserved, r ∉ rs) :
      ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r h => hk.gpr (hr r h)
  unfold VG.Impl.Rc4.Arm.apply
  refine WP.seq (WP.mono (VG.Proof.Rc4.Arm.apply_entry s hs) fun a ⟨ham, hak, ha12, haz⟩ => ?_)
  rw [hP] at ha12
  rw [hL, BitVec.sub_zero] at haz
  refine WP.ite a.z (VG.Proof.Rc4.Arm.eval_eq a) (fun hz => ?_) (fun hnz => ?_)
  · have hL0 : L = 0#32 := by rw [haz, beq_iff_eq] at hz; exact hz
    refine WP.block_nil ⟨?_, hpres a _ hak (by decide), hak.2.2.2⟩
    rw [ham, hL0]
    exact ⟨rfl, rfl⟩
  have hL0 : L.toNat ≠ 0 := fun h => by
    have : L = 0#32 := BitVec.eq_of_toNat_eq h
    rw [haz, this] at hnz
    exact absurd hnz (by decide)
  refine WP.seq ?_
  have ha3 : a.gpr .r3 = Sc := (hak.gpr (by decide)).trans hS
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.save_ok a (by rw [ha3]; exact sfit) (by rw [hak.2.2.1, ha3]; exact hscr))
    fun b ⟨hbm, hbk⟩ => ?_
  rw [ha3] at hbm
  have ka : VG.Proof.Rc4.Arm.Keep [.r12] s b := (hak.trans hbk).mono (by decide)
  have hsave : Frame [⟨State.addr Sc, 64⟩] s.mem b.mem := by
    rw [hbm, ham]; exact VG.Proof.Rc4.Arm.save_frame _ _ _
  have hctxb : contextAt b.mem (State.addr P) = contextAt s.mem (State.addr P) :=
    contextAt_frame hsave fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cs
  have r257 : InRegions (b.rd ++ b.wr) (State.addr P + 257#64) 1 := by
    rw [ka.2.1, ka.2.2.1]
    exact VG.Proof.Rc4.Arm.region_in (region_offset _ _ _ 257 1 (by decide) (by decide) hctx)
  refine WP.mono (VG.Proof.Rc4.Arm.apply_start b ((ka.gpr (by decide)).trans hP) cfit r257)
    fun c ⟨hcm, hck, hc4, hc12, hc5, hc0, hc10⟩ => ?_
  have kc : VG.Proof.Rc4.Arm.Keep [.r12, .r4, .r5, .r0, .r10] s c := (ka.trans hck).mono (by decide)
  have hec : VG.Proof.Rc4.Arm.StepEnv c P D L :=
    { p := hc12
      d := (kc.gpr (by decide)).trans hD
      l := (kc.gpr (by decide)).trans hL
      ones := hc10
      pfit := cfit
      dfit := dfit
      table := by
        rw [kc.2.2.1]
        have h' := region_offset _ _ _ 0 256 (by decide) (by decide) hctx
        simpa only [BitVec.add_zero] using h'
      data := by rw [kc.2.2.1]; exact hdat
      sTD := sep_of_sub cd (contains_prefix _ (by decide)) (contains_prefix _ (Nat.le_refl _)) }
  have hinv : VG.Proof.Rc4.Arm.LoopInv s.mem P D L c 0 c := by
    have hu0 : VG.Proof.Rc4.Arm.upd s.mem P D 0 = (contextAt s.mem (State.addr P), []) := rfl
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
            exact ds) (show L.toNat ≤ 2 ^ 64 by have := L.isLt; omega) hx
        frame := Frame.refl _ _
        count := hc0
        keep := Keep.refl _ _ }
  refine WP.seq (WP.mono (VG.Proof.Rc4.Arm.apply_loop s.mem c hec (Nat.pos_of_ne_zero hL0) c hinv)
    fun d hd => ?_)
  have kd : VG.Proof.Rc4.Arm.Keep (([.r12, .r4, .r5, .r0, .r10] : List Reg) ++ VG.Proof.Rc4.Arm.stepRegs) s d := kc.trans hd.keep
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.Arm.apply_finish d (VG.Proof.Rc4.Arm.upd s.mem P D L.toNat).1.i (VG.Proof.Rc4.Arm.upd s.mem P D L.toNat).1.j cfit
    hd.i hd.j ((hd.keep.gpr (by decide)).trans hc12) (by rw [kd.2.2.1]; exact hctx))
    fun e ⟨hem, hek⟩ => ?_
  have hce : Frame [⟨State.addr P, 258⟩, ⟨State.addr D, L.toNat⟩] b.mem e.mem := by
    have hc258 : (⟨State.addr P, 258⟩ : Region) ∈
        [⟨State.addr P, 258⟩, ⟨State.addr D, L.toNat⟩] := List.mem_cons_self
    rw [hem]
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    have hbd : Frame (VG.Proof.Rc4.Arm.loopRegions P D L) b.mem d.mem := by rw [← hcm]; exact hd.frame
    refine hbd.sub fun r hr => ?_
    simp only [VG.Proof.Rc4.Arm.loopRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
  have ke : VG.Proof.Rc4.Arm.Keep (([.r12, .r4, .r5, .r0, .r10] : List Reg) ++ VG.Proof.Rc4.Arm.stepRegs) s e :=
    (kd.trans hek).mono (by decide)
  have he3 : e.gpr .r3 = Sc := (ke.gpr (by decide)).trans hS
  have hsaved : Spill.Saved e.mem (State.addr (e.gpr .r3)) a.gpr saved := by
    rw [he3]
    have h0 : Spill.Saved b.mem (State.addr Sc) a.gpr saved := by
      rw [hbm]
      exact Spill.saveMem_saved _ _ _ _ VG.Proof.Rc4.Arm.saved_slots
    refine h0.frame VG.Proof.Rc4.Arm.saved_slots hce fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [BitVec.add_zero]
    rcases hr with rfl | rfl
    · exact (cs.symm.sub_left (Region.sub_prefix (by decide)))
    · exact (ds.symm.sub_left (Region.sub_prefix (by decide)))
  refine WP.mono (VG.Proof.Rc4.Arm.restore_ok e (by rw [he3]; exact sfit)
    (by rw [ke.2.1, ke.2.2.1, he3]; exact VG.Proof.Rc4.Arm.region_in hscr) hsaved)
    fun g ⟨hgr, hgk, hgm⟩ => ?_
  have hDP (o : Nat) (ho : o < 258) :
      Mem.Sep (State.addr D) L.toNat (State.addr P + BitVec.ofNat 64 o) 1 :=
    sep_of_sub cd.symm (contains_prefix _ (Nat.le_refl _))
      (Offset.contains_base _ (by omega) (by omega))
  have hLn : L.toNat < 2 ^ 64 := by have := L.isLt; omega
  refine ⟨⟨?_, ?_⟩, fun r hr => ?_, hgk.2.2.2.trans ke.2.2.2⟩
  · rw [hgm, hem, context_finish]
    exact context_ext hd.table rfl rfl
  · rw [hgm, hem, bytes_write_sep _ _ _ _ _ hLn (hDP 257 (by decide)),
      bytes_write_sep _ _ _ _ _ hLn (hDP 256 (by decide))]
    exact hd.data
  · by_cases hs : r ∈ saved.map Prod.fst
    · rw [hgr r hs]
      exact hak.gpr (by rw [VG.Proof.Rc4.Arm.saved_regs] at hs; revert hs; revert r; decide)
    · rw [hgk.gpr (by rw [← VG.Proof.Rc4.Arm.saved_regs]; exact hs)]
      have : r = .lr := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [VG.Proof.Rc4.Arm.saved_regs] at hs
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs ⊢
      subst this
      exact ke.gpr (by decide)

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Lit`. -/
section

/-! Literal code keeps unrolled table scans cheap for kernel-evaluated audits. -/
namespace VG.Impl.Rc4.Arm
materialize_value lookup
materialize_value replace
materialize_value scheduleStep
materialize_value applyStep
materialize_code VG.Impl.Rc4.Arm.init
materialize_code apply
end VG.Impl.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.ConstantTime`. -/
section

/-! # RC4 on ARMv7: constant time

Initialization is checked by the taint analysis alone. The stream function
first loads the PRGA index `i` from the context, which the analysis takes
for secret: the contract lets it leak, so the proof makes it public by hand
(`entry_ct`) and the analysis checks the rest.
-/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

theorem init_ct : ConstantTime isa initC.pre initC.pub VG.Impl.Rc4.Arm.init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ ⟨_, h0, h1, h2, h3⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption)
    (by taint_decide)

/-- The taint after `entry`, with `i` in `r12`. -/
def loopTaint : VG.Arm.Taint.T := Taint.ofRegs [.r0, .r1, .r2, .r3, .r12]

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem entry_ct : RelCT isa (fun a b => applyC.pre a ∧ applyC.pre b ∧ applyC.pub a b)
    (.block entry) fun a b => VG.Arm.Taint.Agree VG.Proof.Rc4.Arm.loopTaint a b ∧ a.z = b.z := by
  intro a b tr tr' a' b' ⟨hpa, hpb, ⟨_, hi⟩, h0, h1, h2, h3⟩ ea eb
  obtain ⟨htrace, -⟩ := RelCT.taint (A := taint) (P := fun a b => VG.Arm.Taint.Agree
    (Taint.ofRegs [.r0, .r1, .r2, .r3]) a b) (Taint.ofRegs [.r0, .r1, .r2, .r3]) (fun _ _ h => h)
    (by taint_decide) a b tr tr' a' b' (Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ea eb
  obtain ⟨_, u, eu, -, hak, ha12, haz⟩ := VG.Proof.Rc4.Arm.apply_entry a hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, -, hbk, hb12, hbz⟩ := VG.Proof.Rc4.Arm.apply_entry b hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  have hi' : (contextAt a.mem (State.addr (a.gpr .r0))).i =
      (contextAt b.mem (State.addr (b.gpr .r0))).i :=
    BitVec.eq_of_toNat_eq (List.cons.inj hi).1
  refine ⟨htrace, Taint.agree_ofRegs fun r hr => ?_, by rw [haz, hbz, h2]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hak.gpr (by decide), hbk.gpr (by decide), h0]
  · rw [hak.gpr (by decide), hbk.gpr (by decide), h1]
  · rw [hak.gpr (by decide), hbk.gpr (by decide), h2]
  · rw [hak.gpr (by decide), hbk.gpr (by decide), h3]
  · rw [ha12, hb12, hi']

theorem nil_ct {P : State → State → Prop} : RelCT isa P (.block []) fun _ _ => True := by
  intro _ _ _ _ _ _ _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  exact ⟨e₁.2.symm.trans e₂.2, trivial⟩

theorem apply_ct : ConstantTime isa applyC.pre applyC.pub VG.Impl.Rc4.Arm.apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold VG.Impl.Rc4.Arm.apply
  refine RelCT.seq VG.Proof.Rc4.Arm.entry_ct (RelCT.ite ?_ VG.Proof.Rc4.Arm.nil_ct ?_)
  · intro a b ⟨_, hz⟩
    rw [VG.Proof.Rc4.Arm.eval_eq, VG.Proof.Rc4.Arm.eval_eq, hz]
  · exact RelCT.taint (A := taint) VG.Proof.Rc4.Arm.loopTaint (fun _ _ h => h.1.1) (by taint_decide)

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Verified`. -/
section

/-! # RC4 on ARMv7: `Verified` -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

theorem init_correct (s : State) (hs : initC.pre s) :
    ∃ t s', Exec isa VG.Impl.Rc4.Arm.init s t s' ∧ abiPreserved s s' ∧ initC.post s s' := by
  obtain ⟨t, s', he, hpost, hpres, hsp⟩ := VG.Proof.Rc4.Arm.init_ok s hs
  refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
  unfold VG.Proof.Rc4.Arm.initC
  dsimp only
  revert hpost
  cases Spec.Rc4.init (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) with
  | ok c => intro hpost; exact ⟨by rw [ret_low, hpost.1]; rfl, hpost.2⟩
  | error e => cases e; intro hpost; rw [ret_low, hpost]; rfl

theorem apply_correct (s : State) (hs : applyC.pre s) :
    ∃ t s', Exec isa VG.Impl.Rc4.Arm.apply s t s' ∧ abiPreserved s s' ∧ applyC.post s s' := by
  obtain ⟨t, s', he, hpost, hpres, hsp⟩ := VG.Proof.Rc4.Arm.apply_ok s hs
  exact ⟨t, s', he, ⟨hpres, hsp⟩, hpost⟩

theorem init_verified : Verified target VG.Impl.Rc4.Arm.init (initScratchContract abi) := by
  refine Verified.of_correct VG.Proof.Rc4.Arm.init_correct VG.Proof.Rc4.Arm.init_ct ?_
  sig_implies [initScratchContract, initScratchSig, initPost, abi, argRegs, Arm.reduceClassify,
    Arm.Loc.val, VG.Proof.Rc4.Arm.initC, State.addr] [initSat] using VG.Proof.Rc4.Arm.initSat

theorem apply_verified : Verified target VG.Impl.Rc4.Arm.apply (applyScratchContract abi) := by
  refine Verified.of_correct VG.Proof.Rc4.Arm.apply_correct VG.Proof.Rc4.Arm.apply_ct ?_
  sig_implies [applyScratchContract, applyScratchSig, applyPost, applyLeak, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, VG.Proof.Rc4.Arm.applyC, State.addr] [applySat] using VG.Proof.Rc4.Arm.applySat

end VG.Proof.Rc4.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Arm.Frame`. -/
section

/-!
# RC4 on ARMv7, with the working space on the stack

The working space of `vg_rc4_init` and `vg_rc4_apply`, where they keep our
caller's `r4`–`r11`, was their fourth argument, in `r3`: they run their code,
proved with it as an argument (`Verified.lean`), in a frame of 64 bytes that
is the working space and which they zero after the code
(`Verified.regScratchWiped`). The code uses no other stack. The frame passes
`vg_rc4_apply`'s arguments in the same registers and memory, so its leak, the
context's `i`, is the code's.
-/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm

/-- A state satisfying `vg_rc4_init`'s precondition: a 1-byte key at
`0x1000` and the context at `0x2000`. -/
def initFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Rc4.initContract Arm.abi 64).pre s := by
  implies_sat [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initFrameSat] using VG.Proof.Rc4.Arm.initFrameSat

/-- A state satisfying `vg_rc4_apply`'s precondition: the context at
`0x1000` and 1 byte of data at `0x2000`. -/
def applyFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩]

theorem applyFrameSat_pre : ∃ s, (Spec.Rc4.applyContract Arm.abi 64).pre s := by
  implies_sat [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost,
    Spec.Rc4.applyLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [applyFrameSat] using VG.Proof.Rc4.Arm.applyFrameSat

theorem init_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.init)
      (Spec.Rc4.initContract Arm.abi 64) :=
  Arm.Verified.regScratchWiped (sig := Spec.Rc4.initSig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.initPost Arm.abi.ptrBits) (wa := true) (stack := 0)
    VG.Proof.Rc4.Arm.init_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.Rc4.initPostOut_local _) VG.Proof.Rc4.Arm.initFrameSat_pre

theorem apply_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.apply)
      (Spec.Rc4.applyContract Arm.abi 64) :=
  Arm.Verified.regScratchWiped (sig := Spec.Rc4.applySig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.applyPost Arm.abi.ptrBits) (wa := true) (stack := 0)
    (leak := some (Spec.Rc4.applyLeak Arm.abi.ptrBits))
    VG.Proof.Rc4.Arm.apply_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.Rc4.applyPostOut_local _) VG.Proof.Rc4.Arm.applyFrameSat_pre

end VG.Proof.Rc4.Arm

end
