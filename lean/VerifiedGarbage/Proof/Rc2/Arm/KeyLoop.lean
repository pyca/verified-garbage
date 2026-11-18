module

public import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
public import VerifiedGarbage.Proof.Rc2.Arm.Lookup
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Rc2.PiLit

/-! ### `Rc2.Arm.PiScan`, which this module and modules that import it used -/

section

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

end

end

@[expose] public section

section

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

/-- A block keeps the addresses of statics. -/
theorem runBlock_syms {is : List Instr} {s s' : State} (h : runBlock isa is s = some s') :
    s'.syms = s.syms := by
  induction is generalizing s with
  | nil => rw [runBlock_nil, Option.some.injEq] at h; rw [h]
  | cons i is ih =>
    rw [runBlock_cons] at h
    cases he : exec i s with
    | none => rw [he, runStep, Option.bind_none] at h; cases h
    | some s₁ => rw [he, runStep_some] at h; exact (ih h).trans (exec_syms he)

/-- The table, after a block that keeps memory and regions. -/
theorem PiAt.run {T : BitVec 32} {rs : List Reg} {is : List Instr} {s s' : State} (h : PiAt T s)
    (run : runBlock isa is s = some s') (k : Keep rs s s') : PiAt T s' :=
  ⟨h.toPiTab.keep k, by rw [runBlock_syms run]; exact h.syms⟩

theorem fillKey_ok (s : State) {T : BitVec 32} (hT : PiAt T s)
    (readLo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + s.gpr .r0 - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - s.gpr .r5))) 1)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    WP isa fillKey s (fun s' =>
      s'.gpr .r0 = s.gpr .r0 + 1 ∧
      zeroFlag s' = some ((s.gpr .r0 + 1 - 128) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0))
          (Spec.Rc2.pi (s.mem (State.addr (s.gpr .r6 + s.gpr .r0 - 1)) +
          s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - s.gpr .r5)))))} s') := by
  rw [fillKey]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := fillInput_ok s readLo readHi
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  apply WP.seq
  apply WP.mono (piLookup_ok s₁ (hT.run run₁ keep₁))
  intro s₂ h₂
  have k₁ : Keep keyTemps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have k₂ : Keep keyTemps s₁ s₂ := h₂.2.weaken (by
    intro r hr
    simp only [piRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h <;> subst r <;> decide)
  have keep := k₁.trans k₂
  have ptr := keep.reg .r6 (by decide)
  have index := (keep₁.reg .r0 (by decide)).trans rfl
  have index₂ : s₂.gpr .r0 = s.gpr .r0 := (h₂.2.reg .r0 (by decide)).trans index
  have write₂ : InRegions s₂.wr (State.addr (s₂.gpr .r6 + s₂.gpr .r0)) 1 := by
    rw [keep.wr, ptr, index₂]; exact writable
  obtain ⟨s₃, run₃, out₃, flag₃, keep₃⟩ := fillOutput_ok s₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [out₃, index₂], by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact (keep₃.reg r hr).trans (keep.reg r hr)
  · rw [keep₃.mem, keep.mem, ptr, index₂, h₂.1, out₁]
    simp [BitVec.setWidth_add]
  · exact keep₃.rd.trans keep.rd
  · exact keep₃.wr.trans keep.wr

theorem piStore_ok (s : State) {T : BitVec 32} (hT : PiAt T s)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    WP isa (.seq piLookup (.block storeKey)) s (fun s' =>
      s'.gpr .r0 = s.gpr .r0 ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0)) (Spec.Rc2.pi ((s.gpr .r12).setWidth 8))} s') := by
  apply WP.seq
  apply WP.mono (piLookup_ok s hT)
  intro s₁ h₁
  have ptr := h₁.2.reg .r6 (by decide)
  have index := h₁.2.reg .r0 (by decide)
  have valid : InRegions s₁.wr (State.addr (s₁.gpr .r6 + s₁.gpr .r0)) 1 := by
    rw [h₁.2.wr, ptr, index]; exact writable
  obtain ⟨s₂, run₂, index₂, keep₂⟩ := storeByte_ok s₁ valid
  refine WP.of_runBlock ⟨s₂, run₂, index₂.trans index, ?_⟩
  constructor
  · intro r hr
    rw [keep₂.reg r (by intro hm; simp only [List.mem_singleton] at hm; subst r; exact hr (by decide))]
    exact h₁.2.reg r (fun hm => hr (by
      simp only [piRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h <;> subst r <;> decide))
  · rw [keep₂.mem, h₁.2.mem, ptr, index, h₁.1]
    simp
  · exact keep₂.rd.trans h₁.2.rd
  · exact keep₂.wr.trans h₁.2.wr

theorem reduceKey_ok (s : State) {T : BitVec 32} (hT : PiAt T s)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + s.gpr .r0)) 1)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    WP isa reduceKey s (fun s' => s'.gpr .r0 = s.gpr .r0 ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0))
          (Spec.Rc2.pi (s.mem (State.addr (s.gpr .r6 + s.gpr .r0)) &&& (s.gpr .r2).setWidth 8))} s') := by
  rw [reduceKey]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := reduceInput_ok s readable
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ptr := keep₁.reg .r6 (by decide)
  have index := keep₁.reg .r0 (by decide)
  have valid : InRegions s₁.wr (State.addr (s₁.gpr .r6 + s₁.gpr .r0)) 1 := by
    rw [keep₁.wr, ptr, index]; exact writable
  apply WP.mono (piStore_ok s₁ (hT.run run₁ keep₁) valid)
  intro s₂ h₂
  refine ⟨h₂.1.trans index, ?_⟩
  constructor
  · intro r hr
    exact (h₂.2.reg r hr).trans (keep₁.reg r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h <;> subst r <;> exact hr (by decide)))
  · rw [h₂.2.mem, keep₁.mem, ptr, index, out₁]
    simp
  · exact h₂.2.rd.trans keep₁.rd
  · exact h₂.2.wr.trans keep₁.wr

theorem descendKey_ok (s : State) {T : BitVec 32} (hT : PiAt T s)
    (readLo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - 1 + s.gpr .r1))) 1)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + (s.gpr .r0 - 1))) 1) :
    WP isa descendKey s (fun s' =>
      s'.gpr .r0 = s.gpr .r0 - 1 ∧ zeroFlag s' = some ((s.gpr .r0 - 1) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (State.addr (s.gpr .r6 + (s.gpr .r0 - 1)))
          (Spec.Rc2.pi (s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - 1) + 1)) ^^^
            s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - 1 + s.gpr .r1)))))} s') := by
  rw [descendKey]
  obtain ⟨s₁, run₁, index₁, out₁, keep₁⟩ := descendInput_ok s readLo readHi
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ptr := keep₁.reg .r6 (by decide)
  have valid : InRegions s₁.wr (State.addr (s₁.gpr .r6 + s₁.gpr .r0)) 1 := by
    rw [keep₁.wr, ptr, index₁]; exact writable
  refine WP.seq (WP.mono (WP.seq_iff.mp (piStore_ok s₁ (hT.run run₁ keep₁) valid)) fun t ht => ?_)
  rw [WP.block_append_iff]
  refine WP.mono ht fun s₂ h₂ => ?_
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpZero_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have index₂ := h₂.1.trans index₁
  refine ⟨(keep₃.reg .r0 (by decide)).trans index₂, by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact ((keep₃.reg r (by simp)).trans (h₂.2.reg r hr)).trans (keep₁.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h <;> subst r <;> decide)))
  · rw [keep₃.mem, h₂.2.mem, keep₁.mem, ptr, index₁, out₁]
    simp
  · exact keep₃.rd.trans (h₂.2.rd.trans keep₁.rd)
  · exact keep₃.wr.trans (h₂.2.wr.trans keep₁.wr)


end VG.Proof.Rc2.Arm

end

/-! # A bounded loop rule and frame invariant for key expansion -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem forwardLoop (body : Prog isa) (I : Nat → State → Prop) (stop : Nat)
    (step : ∀ i < stop, ∀ s, I i s → WP isa body s (fun s' =>
      I (i + 1) s' ∧ zeroFlag s' = some (decide (i + 1 = stop))))
    (i : Nat) (hi : i < stop) (s : State) (hs : I i s) :
    WP isa (.loop body .ne) s (I stop) := by
  let Inv (n : Nat) (s : State) := ∃ i, i < stop ∧ stop - i = n ∧ I i s
  refine WP.loop (M := isa) Inv ?_ (stop - i) s ⟨i, hi, rfl, hs⟩
  intro n s ⟨j, hj, hn, hI⟩
  apply WP.mono (step j hj s hI)
  intro s' h'
  by_cases he : j + 1 = stop
  · left
    constructor
    · simp only [eval_nonzero, h'.2, he, decide_true, Option.map_some, Bool.not_true]
    · rw [he] at h'
      exact h'.1
  · right
    constructor
    · simp only [eval_nonzero, h'.2, he, decide_false, Option.map_some, Bool.not_false]
    · exact ⟨stop - (j + 1), by omega_using [hj, hn], j + 1, by omega_using [hj, he], rfl, h'.1⟩

/-- Across a key-expansion loop only the six temporaries and the schedule
buffer change. The key, scratch saves, and return address are separate. -/
structure KeyFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ keyTemps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨State.addr (s₀.gpr .r6), 128⟩] s₀.mem s.mem
  syms : s.syms = s₀.syms

theorem KeyFrame.refl (s : State) : KeyFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩

theorem KeyFrame.trans {s₀ s₁ s₂ : State} (h₁ : KeyFrame s₀ s₁) (h₂ : KeyFrame s₁ s₂) :
    KeyFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_, h₂.syms.trans h₁.syms⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .r6 (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem KeyFrame.step {s₀ s s' : State} (h : KeyFrame s₀ s) (i : Nat) (hi : i < 128)
    (b : Byte) (keep : Keep keyTemps {s with mem := s.mem.writeW (State.addr (s₀.gpr .r6) + BitVec.ofNat 64 i) b} s')
    (hsy : s'.syms = s.syms) : KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_, hsy.trans h.syms⟩
  rw [keep.mem]
  exact h.mem.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))

theorem KeyFrame.keep {s₀ s s' : State} (h : KeyFrame s₀ s) (keep : Keep keyTemps s s')
    (hsy : s'.syms = s.syms) : KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_, hsy.trans h.syms⟩
  rw [keep.mem]; exact h.mem

/-- The table, after a key-expansion loop, which writes only the schedule. -/
theorem PiAt.frame {T : BitVec 32} {s₀ s : State} (h : PiAt T s₀) (f : KeyFrame s₀ s)
    (sep : (⟨State.addr T, 256⟩ : Region).Disjoint ⟨State.addr (s₀.gpr .r6), 128⟩) : PiAt T s := by
  refine ⟨⟨h.fit, by rw [f.rd]; exact h.rd, fun i hi => ?_⟩, by rw [f.syms]; exact h.syms⟩
  rw [f.mem.bytes (R := ⟨State.addr T, 256⟩) (by simpa using sep) (by simp) hi]
  exact h.held i hi

theorem counter_add (i : Nat) : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by
  rw [BitVec.ofNat_add]
  rfl

theorem counter_eq (i n : Nat) (hi : i < 2 ^ 32) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 32 i - BitVec.ofNat 32 n) == 0#32) = decide (i = n) := by
  have he : (BitVec.ofNat 32 i - BitVec.ofNat 32 n = 0#32) ↔ i = n := by bv_omega
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using he

theorem counter_sub (i : Nat) (hi : 1 ≤ i) :
    BitVec.ofNat 32 i - 1 = BitVec.ofNat 32 (i - 1) :=
  Offset.ofNat_sub_ofNat hi

end VG.Proof.Rc2.Arm
