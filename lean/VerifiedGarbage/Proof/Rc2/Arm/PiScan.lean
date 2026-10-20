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
# RC2 on ARMv7: the scan of PITABLE

`piLookup` visits the 256 bytes of the static `VG_RC2_PITABLE`, in order,
one word of four entries at a time, and leaves in `r12` PITABLE's byte at the
low byte of `r12` (`piLookup_ok`), given the table at the static's address
(`PiAt`). Each word is kept under a mask that is all ones exactly when the
index is one of its entries, and 0 otherwise (`maskWord`); the index's byte
of the word kept is then selected with masks (`select_eq`).
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

/-- The registers the loop of a lookup writes. -/
def piLoopRegs : List Reg := [.r3, .r9, .r10, .r11, .lr]

theorem and_zero32 (v : BitVec 32) : v &&& 0 = 0 := BitVec.eq_of_getLsbD_eq (by simp)

theorem or_zero32 (v : BitVec 32) : v ||| 0 = v := BitVec.eq_of_getLsbD_eq (by simp)

/-- `c ^^^ d = 0` only for `c = d`. -/
theorem nat_eq_of_xor_eq_zero {c d : Nat} (h : c ^^^ d = 0) : c = d := by
  have := congrArg (· ^^^ d) h
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at this
  exact this

/-- The mask of a word of four entries, from `4 j`, keeps it exactly when
the index `x` is one of its entries. -/
theorem maskWord (x : Byte) {j : Nat} (hj : j < 64) :
    ((x.setWidth 32 ^^^ BitVec.ofNat 32 (4 * j)) - 4) >>> 8 |||
        ((x.setWidth 32 ^^^ BitVec.ofNat 32 (4 * j)) - 4) >>> 8 <<< 8 =
      if x.toNat / 4 = j then BitVec.allOnes 32 else 0 := by
  have hx : (x.setWidth 32).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  obtain ⟨z, hz⟩ : ∃ z, x.setWidth 32 ^^^ BitVec.ofNat 32 (4 * j) = z := ⟨_, rfl⟩
  have hzt : z.toNat = x.toNat ^^^ (4 * j) := by
    rw [← hz, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hx]
  have hzl : z.toNat < 256 := by
    rw [hzt]; exact Nat.xor_lt_two_pow (n := 8) x.isLt (by omega)
  have hdiv : z.toNat / 4 = x.toNat / 4 ^^^ j := by
    have e : z.toNat / 2 ^ 2 = x.toNat / 2 ^ 2 ^^^ (4 * j) / 2 ^ 2 := by
      rw [hzt]; exact Nat.xor_div_two_pow
    rw [show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_div_cancel_left j (by decide)] at e
    exact e
  have key : z.toNat < 4 ↔ x.toNat / 4 = j := by
    constructor
    · intro h; exact nat_eq_of_xor_eq_zero (by rw [← hdiv]; omega)
    · intro h; rw [h, Nat.xor_self] at hdiv; omega
  rw [hz]
  by_cases h : x.toNat / 4 = j
  · rw [ite_eq_left h]
    have hz4 := key.mpr h
    have hy : (z - 4) >>> 8 = (0x00FFFFFF : BitVec 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow,
        show (4 : BitVec 32).toNat = 4 from rfl, show (0x00FFFFFF : BitVec 32).toNat = 16777215 from rfl]
      omega
    rw [hy]
    decide
  · rw [ite_eq_right h]
    have hz4 : 4 ≤ z.toNat := Nat.le_of_not_lt fun h' => h (key.mp h')
    have hy : (z - 4) >>> 8 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow,
        show (4 : BitVec 32).toNat = 4 from rfl, show (0 : BitVec 32).toNat = 0 from rfl]
      omega
    rw [hy]
    decide

/-- Four entries: `r3` gains their word iff the index is one of them; on to
the next four. -/
theorem piBody_ok (s : State) (x : Byte) {j : Nat} (hj : j < 64)
    (h12 : s.gpr .r12 = x.setWidth 32) (h9 : s.gpr .r9 = BitVec.ofNat 32 (4 * j))
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4) :
    ∃ s', runBlock isa piBody s = some s' ∧
      s'.gpr .r3 = s.gpr .r3 ||| (if x.toNat / 4 = j then
        s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 else 0) ∧
      s'.gpr .r9 = BitVec.ofNat 32 (4 * (j + 1)) ∧ s'.gpr .lr = s.gpr .lr + 4 ∧
      s'.z = (BitVec.ofNat 32 (4 * j) - 252 == 0) ∧ Keep piLoopRegs s s' := by
  have e4 : encodable (4 : BitVec 32) = true := by decide
  have e252 : encodable (252 : BitVec 32) = true := by decide
  refine ⟨_, by
    simp only [piBody, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, State.load32,
      hin, e4, e252, Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_subFlags, reduceCtorEq, ite_true, ite_false]
    rw [h12, h9, maskWord x hj]
    split
    · rw [BitVec.and_allOnes]
    · rw [and_zero32]
  · simp only [gpr_setReg, gpr_subFlags, reduceCtorEq, ite_true, ite_false]
    rw [h9, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add,
      show 4 * j + 4 = 4 * (j + 1) by omega]
  · simp only [gpr_setReg, gpr_subFlags, reduceCtorEq, ite_true, ite_false]
  · simp only [z_setReg, gpr_setReg, reduceCtorEq, ite_false]
    rw [h9]; rfl
  · constructor
    · intro r hr
      simp only [piLoopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h3, h9', h10, h11, hl⟩ := hr
      simp only [gpr_setReg, gpr_subFlags, h3, h9', h10, h11, hl, ite_false]
    · rfl
    · rfl
    · rfl

/-- Word `q` of the table at `T` in the memory `m`: entries `4 q … 4 q + 3`. -/
def tw (m : Mem) (T : BitVec 32) (q : Nat) : BitVec 32 := m.readW (State.addr T + BitVec.ofNat 64 (4 * q)) 32

/-- The value of the scan once words `0 … j - 1` are visited. -/
def wAcc (m : Mem) (T : BitVec 32) (x : Byte) (j : Nat) : BitVec 32 :=
  if x.toNat / 4 < j then tw m T (x.toNat / 4) else 0

theorem wAcc_succ (m : Mem) (T : BitVec 32) (x : Byte) {j : Nat} :
    (wAcc m T x j ||| if x.toNat / 4 = j then tw m T j else 0) = wAcc m T x (j + 1) := by
  unfold wAcc
  by_cases h : x.toNat / 4 = j
  · rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_left (by omega), ← h]
    exact BitVec.eq_of_getLsbD_eq (by simp)
  · rw [ite_eq_right h, or_zero32]
    by_cases h2 : x.toNat / 4 < j
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- The state of the scan from `s₀` with words `0 … j - 1` visited. -/
structure PiScanAt (s₀ : State) (T : BitVec 32) (x : Byte) (j : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = x.setWidth 32
  r9 : s.gpr .r9 = BitVec.ofNat 32 (4 * j)
  lr : s.gpr .lr = T + BitVec.ofNat 32 (4 * j)
  r3 : s.gpr .r3 = wAcc s₀.mem T x j
  keep : Keep piLoopRegs s₀ s

theorem piScan_step {s₀ s : State} {T : BitVec 32} {x : Byte} {j : Nat} (hj : j < 64)
    (hT : PiTab T s₀) (h : PiScanAt s₀ T x j s) :
    WP isa (.block piBody) s fun t => PiScanAt s₀ T x (j + 1) t ∧ t.z = decide (j = 63) := by
  have fit := hT.fit
  have ea : State.addr (s.gpr .lr + BitVec.ofNat 32 0) = State.addr T + BitVec.ofNat 64 (4 * j) := by
    rw [h.lr, BitVec.add_zero, addr_add (by omega)]
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4 := by
    rw [h.keep.rd, h.keep.wr, ea]
    exact ⟨_, List.mem_append_left _ hT.rd, Offset.contains_base _ (by omega) (by omega)⟩
  have hw : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 = tw s₀.mem T j := by
    rw [ea, h.keep.mem]; rfl
  obtain ⟨t, run, t3, t9, tl, tz, tk⟩ := piBody_ok s x hj h.r12 h.r9 hin
  refine WP.of_runBlock ⟨t, run, ⟨?_, t9, ?_, ?_, h.keep.trans tk⟩, ?_⟩
  · rw [tk.reg .r12 (by decide), h.r12]
  · rw [tl, h.lr, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add,
      show 4 * j + 4 = 4 * (j + 1) by omega]
  · rw [t3, h.r3, hw, wAcc_succ]
  · rw [tz]
    by_cases he : j = 63
    · subst he; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 (4 * j) - 252 ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        simp at this; omega
      simpa using this

/-- `0x00ffffff` keeps the low byte. -/
theorem m24_and (v : BitVec 32) : ((0x00FFFFFF : BitVec 32) &&& v) &&& 255 = v &&& 255 := by
  have hf : ∀ i < 32, (255 : BitVec 32).getLsbD i = true → (0x00FFFFFF : BitVec 32).getLsbD i = true := by
    decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  cases h : (255 : BitVec 32).getLsbD i
  · simp only [Bool.and_false]
  · simp only [hf i hi h, Bool.true_and]

/-- The selection: byte `k` of `w`, for `k` the index's low two bits. -/
theorem select_eq (w : BitVec 32) {k : Nat} (hk : k < 4) :
    ((((BitVec.ofNat 32 k - 1) >>> 8 &&& w) ||| (((BitVec.ofNat 32 k ^^^ 1) - 1) >>> 8 &&& w >>> 8)) |||
        (((BitVec.ofNat 32 k ^^^ 2) - 1) >>> 8 &&& w >>> 16) |||
        (((BitVec.ofNat 32 k ^^^ 3) - 1) >>> 8 &&& w >>> 24)) &&& 255 = w >>> (8 * k) &&& 255 := by
  have hm : ∀ a < 4,
      (BitVec.ofNat 32 a - 1) >>> 8 = (if a = 0 then 0x00FFFFFF else 0#32) ∧
      ((BitVec.ofNat 32 a ^^^ 1) - 1) >>> 8 = (if a = 1 then 0x00FFFFFF else 0#32) ∧
      ((BitVec.ofNat 32 a ^^^ 2) - 1) >>> 8 = (if a = 2 then 0x00FFFFFF else 0#32) ∧
      ((BitVec.ofNat 32 a ^^^ 3) - 1) >>> 8 = (if a = 3 then 0x00FFFFFF else 0#32) := by
    decide
  obtain ⟨h0, h1, h2, h3⟩ := hm k hk
  rw [h0, h1, h2, h3]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceEqDiff, ite_true, ite_false, BitVec.zero_and, BitVec.or_zero, BitVec.zero_or,
      Nat.reduceMul, BitVec.ushiftRight_zero, m24_and]

/-- The low byte of `w >>> k`. -/
theorem shift_and_255 (w : BitVec 32) (k : Nat) : w >>> k &&& 255 = (w.extractLsb' k 8).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    show (255 : BitVec 32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

/-- The index's low two bits. -/
theorem low2 (x : Byte) : x.setWidth 32 &&& 3 = BitVec.ofNat 32 (x.toNat % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega),
    show (3 : BitVec 32).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The lookup: `r12 := PITABLE[r12 & 255]`; only `piRegs` are written. -/
theorem piLookup_ok (s : State) {T : BitVec 32} (hT : PiAt T s) :
    WP isa piLookup s (fun s' =>
      s'.gpr .r12 = (Spec.Rc2.pi ((s.gpr .r12).setWidth 8)).setWidth 32 ∧ Keep piRegs s s') := by
  obtain ⟨x, hx⟩ : ∃ x, (s.gpr .r12).setWidth 8 = x := ⟨_, rfl⟩
  rw [hx]
  unfold piLookup
  refine WP.seq (WP.mono (Q := fun s₁ => PiScanAt s₁ T x 0 s₁ ∧ Keep piRegs s s₁) ?_ fun s₁ ⟨h₁, k₁⟩ => ?_)
  · refine WP.of_runBlock ⟨_, by
      simp only [mask, imm, List.cons_append, List.nil_append, runBlock_cons, exec, Op2.eval,
        Nat.reduceLeDiff, Nat.reduceSub, and_self, ite_true]
      rfl, ?_⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩, ?_⟩
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
      rw [maskBits _ 8 (by decide), hx]
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true, syms_setReg]
      rw [hT.syms]; exact (BitVec.add_zero T).symm
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
    · constructor
      · intro r hr
        simp only [piRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h12, h3, h9, _, _, hl⟩ := hr
        simp only [gpr_setReg, h12, h3, h9, hl, ite_false]
      · rfl
      · rfl
      · rfl
  have hT₁ : PiTab T s₁ := hT.toPiTab.keep k₁
  have loop : WP isa (.loop (.block piBody) .ne) s₁ (PiScanAt s₁ T x 64) := by
    refine WP.loop (M := isa) (fun n (v : State) => ∃ j, n = 64 - j ∧ j < 64 ∧ PiScanAt s₁ T x j v)
      ?_ 64 s₁ ⟨0, rfl, by decide, h₁⟩
    rintro n v ⟨j, rfl, hj, hv⟩
    refine WP.mono (piScan_step hj hT₁ hv) fun w ⟨hw, wz⟩ => ?_
    by_cases he : j = 63
    · subst he
      exact .inl ⟨by show some (!w.z) = _; rw [wz]; rfl, hw⟩
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, 64 - (j + 1), by omega, j + 1, rfl,
        by omega, hw⟩
  have e1 : encodable (1 : BitVec 32) = true := by decide
  have e2 : encodable (2 : BitVec 32) = true := by decide
  have e3 : encodable (3 : BitVec 32) = true := by decide
  have e255 : encodable (255 : BitVec 32) = true := by decide
  refine WP.seq (WP.mono loop fun v hv => WP.of_runBlock ⟨_, by
    simp only [piSelect, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      e1, e2, e3, e255, Nat.reduceLeDiff, and_self, ite_true]
    rfl, ?_⟩)
  have hq : x.toNat / 4 < 64 := by have := x.isLt; omega
  have hk : x.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  refine ⟨?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [hv.r12, hv.r3, low2, select_eq _ hk, shift_and_255, wAcc, ite_eq_left hq, tw]
    refine congrArg (BitVec.setWidth 32) ?_
    have fit := hT.fit
    rw [← Mem.readW_byte _ _ hk, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, hT₁.held _ x.isLt]
    rfl
  · have k₂ : Keep piRegs s₁ v := hv.keep.weaken (by
      intro r hr; simp only [piLoopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h <;> subst h <;> decide)
    refine (k₁.trans k₂).trans ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [piRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h12, h3, h9, h10, h11, hl⟩ := hr
    simp only [gpr_setReg, h12, h10, hl, ite_false]

end VG.Proof.Rc2.Arm
