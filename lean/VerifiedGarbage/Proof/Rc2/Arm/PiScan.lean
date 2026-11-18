module
public import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
public import VerifiedGarbage.Proof.Rc2.Arm.Lookup

import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.PiLit

/-!
# RC2 on ARMv7: the lookups in PITABLE

`piLookup` visits the 256 bytes of the static `VG_RC2_PITABLE` as 32 rows of
two words, and leaves in `r12` PITABLE's byte at the low byte of `r12`
(`piLookup_ok`), given the table at the static's address (`PiAt`). Each
row's words are multiplied by a bit that is 1 exactly when the index is one
of the row's eight entries (`rowBit`) and added to their columns' registers,
which then hold the two words of the index's row (`piRows_ok`); the index's
word of the two, and its byte of that word, are then chosen by bits of the
index (`pick_shift`).
-/

@[expose] public section

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm

/-- PITABLE at the 32-bit address `T`: readable, within the address space,
and holding PITABLE's bytes. -/
structure PiTab (T : BitVec 32) (s : State) : Prop where
  fit : T.toNat + 256 ≤ 2 ^ 32
  rd : (⟨State.addr T, 256⟩ : Region) ∈ s.rd
  held : ∀ i < 256, s.mem (State.addr T + BitVec.ofNat 64 i) = Spec.Rc2.piTable.getD i 0

/-- `PiTab`, at the address of `VG_RC2_PITABLE` in `s`. -/
structure PiAt (T : BitVec 32) (s : State) : Prop extends PiTab T s where
  syms : s.syms Impl.Rc2.piSym = T

theorem PiTab.keep {T : BitVec 32} {rs : List Reg} {s s' : State} (h : PiTab T s) (k : Keep rs s s') :
    PiTab T s' := ⟨h.fit, by rw [k.rd]; exact h.rd, by rw [k.mem]; exact h.held⟩

/-- The registers a lookup writes. -/
def piRegs : List Reg := [.r12, .r3, .r9, .r10, .r11, .lr]

/-- The registers the rows of a lookup write. -/
def piRowRegs : List Reg := [.r3, .r9, .r10, .r11]

/-- A row: each column's register gains the row's word of the column times
the row's bit. -/
theorem piRow_ok (s : State) {n r : Nat} (hn : n < 256) (hr : r < 32)
    (h12 : s.gpr .r12 = BitVec.ofNat 32 n)
    (hin0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 (8 * r))) 4)
    (hin1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 (8 * r + 4))) 4) :
    ∃ s', runBlock isa (piRow r) s = some s' ∧
      s'.gpr .r9 = s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 (8 * r))) 32 *
        (if n / 8 = r then 1 else 0 : BitVec 32) + s.gpr .r9 ∧
      s'.gpr .r10 = s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 (8 * r + 4))) 32 *
        (if n / 8 = r then 1 else 0 : BitVec 32) + s.gpr .r10 ∧
      Keep piRowRegs s s' := by
  have er := encodable_row hr
  have ho0 : 8 * r < 4096 := by omega_arith
  have ho1 : 8 * r + 4 < 4096 := by omega_arith
  have bit := rowBit hn hr
  refine ⟨_, by
    simp only [piRow, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, State.load32,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, hin0, hin1, er, encodable_imm, ho0, ho1,
      Nat.reduceLeDiff, and_self, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [h12, bit]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [h12, bit]
  · constructor
    · intro q hq
      simp only [piRowRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      obtain ⟨h3, h9, h10, h11⟩ := hq
      simp only [gpr_setReg, h3, h9, h10, h11, ite_false]
    · rfl
    · rfl
    · rfl

/-- The word at offset `d` of row `r` of the table at `T` in the memory `m`. -/
def tw (m : Mem) (T : BitVec 32) (d r : Nat) : BitVec 32 := m.readW (State.addr T + BitVec.ofNat 64 (8 * r + d)) 32

/-- The state of the lookup from `s₀` with the rows before `k` visited. -/
structure PiScanAt (s₀ : State) (T : BitVec 32) (n k : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = BitVec.ofNat 32 n
  lr : s.gpr .lr = T
  r9 : s.gpr .r9 = if n / 8 < k then tw s₀.mem T 0 (n / 8) else 0
  r10 : s.gpr .r10 = if n / 8 < k then tw s₀.mem T 4 (n / 8) else 0
  keep : Keep piRowRegs s₀ s

theorem piRows_ok {s₀ : State} {T : BitVec 32} {n : Nat} (hn : n < 256) (hT : PiTab T s₀) :
    ∀ k ≤ 32, ∀ s, PiScanAt s₀ T n 0 s →
      WP isa (.block ((List.range k).flatMap piRow)) s (PiScanAt s₀ T n k) := by
  intro k hk
  induction k with
  | zero => intro s hs; exact WP.block_nil hs
  | succ k ih =>
    intro s hs
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith) s hs) fun t ht => ?_
    have fit := hT.fit
    have ea : ∀ d < 8, State.addr (t.gpr .lr + BitVec.ofNat 32 (8 * k + d)) =
        State.addr T + BitVec.ofNat 64 (8 * k + d) := fun d hd => by
      rw [ht.lr, addr_add (k := 8 * k + d) (by omega_arith)]
    have hin : ∀ d ≤ 4, InRegions (t.rd ++ t.wr) (State.addr (t.gpr .lr + BitVec.ofNat 32 (8 * k + d))) 4 :=
      fun d hd => by
        rw [ht.keep.rd, ht.keep.wr, ea d (by omega_arith)]
        exact ⟨_, List.mem_append_left _ hT.rd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    obtain ⟨u, run, u9, u10, uk⟩ := piRow_ok t (r := k) hn (by omega_arith) ht.r12 (hin 0 (by decide))
      (hin 4 (by decide))
    refine WP.of_runBlock ⟨u, run, ?_, ?_, ?_, ?_, ht.keep.trans uk⟩
    · rw [uk.reg .r12 (by decide), ht.r12]
    · rw [uk.reg .lr (by decide), ht.lr]
    · have e0 := ea 0 (by decide)
      rw [Nat.add_zero] at e0
      rw [u9, ht.r9, ht.keep.mem, e0]
      exact acc_step (tw s₀.mem T 0) (n / 8) k
    · rw [u10, ht.r10, ht.keep.mem, ea 4 (by decide)]
      exact acc_step (tw s₀.mem T 4) (n / 8) k

/-- The two conditional shifts: by `8 (n % 4)`. -/
theorem pick_shift (W : BitVec 32) (n : Nat) :
    (if n / 2 % 2 = 1 then (if n % 2 = 1 then W >>> 8 else W) >>> 16 else (if n % 2 = 1 then W >>> 8 else W)) =
      W >>> (8 * (n % 4)) := by
  have h4 : n % 4 = n % 2 + 2 * (n / 2 % 2) := by omega_arith
  rw [h4]
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h0 <;> rcases Nat.mod_two_eq_zero_or_one (n / 2) with h1 | h1 <;>
    rw [h0, h1]
  · exact (BitVec.ushiftRight_zero W).symm
  · rfl
  · rfl
  · exact (BitVec.shiftRight_add W 8 16).symm

/-- The low byte of `w >>> k`. -/
theorem shift_and_255 (w : BitVec 32) (k : Nat) : w >>> k &&& 255 = (w.extractLsb' k 8).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    show (255 : BitVec 32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

/-- A byte, as a word. -/
theorem byte_ofNat (x : Byte) : x.setWidth 32 = BitVec.ofNat 32 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The lookup: `r12 := PITABLE[r12 & 255]`; only `piRegs` are written. -/
theorem piLookup_ok (s : State) {T : BitVec 32} (hT : PiAt T s) :
    WP isa piLookup s (fun s' =>
      s'.gpr .r12 = (Spec.Rc2.pi ((s.gpr .r12).setWidth 8)).setWidth 32 ∧ Keep piRegs s s') := by
  obtain ⟨x, hx⟩ : ∃ x, (s.gpr .r12).setWidth 8 = x := ⟨_, rfl⟩
  have hn := x.isLt
  obtain ⟨b2, b1, b0⟩ := idxBits hn
  rw [hx]
  unfold piLookup
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun s₁ => PiScanAt s₁ T x.toNat 0 s₁ ∧ Keep piRegs s s₁) (WP.of_runBlock ⟨_, by
      simp only [mask, imm, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
        Op2.eval, Option.map_some, Nat.reduceLeDiff, Nat.reduceSub, and_self, ite_true]
      rfl, ?_⟩) fun s₁ ⟨h₁, k₁⟩ => ?_
  · refine ⟨⟨?_, ?_, ?_, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩, ?_⟩
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
      rw [maskBits _ 8 (by decide), hx, byte_ofNat]
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true, syms_setReg]
      exact hT.syms
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
      rw [ite_eq_right (Nat.not_lt_zero _)]; rfl
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
      rw [ite_eq_right (Nat.not_lt_zero _)]; rfl
    · constructor
      · intro r hr
        simp only [piRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h12, _, h9, h10, _, hl⟩ := hr
        simp only [gpr_setReg, h12, h9, h10, hl, ite_false]
      · rfl
      · rfl
      · rfl
  have hT₁ : PiTab T s₁ := hT.toPiTab.keep k₁
  rw [WP.block_append_iff]
  refine WP.mono (piRows_ok hn hT₁ 32 (Nat.le_refl _) s₁ h₁) fun v hv => ?_
  have e255 : encodable (255 : BitVec 32) = true := by decide
  refine WP.of_runBlock ⟨_, by
    simp only [piSelect, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      encodable_imm, e255, Nat.reduceLeDiff, and_self, ite_true]
    rfl, ?_, ?_⟩
  · have hq : x.toNat / 8 < 32 := by omega_arith
    have hk : x.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
    simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [hv.r12, hv.r9, hv.r10, ite_eq_left hq, ite_eq_left hq, b2, b1, b0, sub_select, sub_select, sub_select,
      pick_shift, shift_and_255]
    refine congrArg (BitVec.setWidth 32) ?_
    have hw : (if x.toNat / 4 % 2 = 1 then tw s₁.mem T 4 (x.toNat / 8) else tw s₁.mem T 0 (x.toNat / 8)) =
        s₁.mem.readW (State.addr T + BitVec.ofNat 64 (4 * (x.toNat / 4))) 32 := by
      unfold tw
      by_cases hc : x.toNat / 4 % 2 = 1
      · rw [ite_eq_left hc, show 8 * (x.toNat / 8) + 4 = 4 * (x.toNat / 4) by omega_arith]
      · rw [ite_eq_right hc, show 8 * (x.toNat / 8) + 0 = 4 * (x.toNat / 4) by omega_arith]
    rw [hw, ← Mem.readW_byte _ _ hk, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, hT₁.held _ hn]
    rfl
  · refine (k₁.trans (hv.keep.weaken (by
      intro r hr; simp only [piRowRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h <;> subst h <;> decide))).trans ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [piRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h12, h3, h9, h10, _, _⟩ := hr
    simp only [gpr_setReg, h12, h3, h9, h10, ite_false]

end VG.Proof.Rc2.Arm
