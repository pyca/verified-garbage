module

public import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
public import VerifiedGarbage.Proof.Rc2.Table
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RC2 on ARMv7: the scan of PITABLE

`piLookup` visits the 256 bytes of the static `VG_RC2_PITABLE`, in order,
and leaves in `r12` PITABLE's byte at the low byte of `r12` (`piLookup_ok`),
given the table at the static's address (`PiAt`). Each entry's byte is kept
under a mask that is `0x00ffffff` exactly when the index is the entry's
number, and 0 otherwise (`maskByte`).
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

theorem byte_and_mask : ∀ b : Byte, b.setWidth 32 &&& ((0 : BitVec 32) - 1) >>> 8 = b.setWidth 32 := by
  decide +kernel

/-- The mask of an entry keeps the byte `b` exactly when the index `x` is
the entry's number `j`. -/
theorem maskByte (b x : Byte) {j : Nat} (hj : j < 256) :
    b.setWidth 32 &&& ((x.setWidth 32 ^^^ BitVec.ofNat 32 j) - 1) >>> 8 =
      if x.toNat = j then b.setWidth 32 else 0 := by
  have hx : (x.setWidth 32).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  by_cases h : x.toNat = j
  · have e : x.setWidth 32 = BitVec.ofNat 32 j :=
      BitVec.eq_of_toNat_eq (by rw [hx, BitVec.toNat_ofNat, h]; omega)
    rw [ite_eq_left h, e, BitVec.xor_self]
    exact byte_and_mask b
  · rw [ite_eq_right h]
    obtain ⟨z, hz⟩ : ∃ z, x.setWidth 32 ^^^ BitVec.ofNat 32 j = z := ⟨_, rfl⟩
    have hzl : z.toNat < 256 := by
      rw [← hz, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hx]
      exact Nat.xor_lt_two_pow (n := 8) x.isLt hj
    have hz0 : z ≠ 0 := fun e => h (by
      rw [e] at hz
      have := congrArg (· ^^^ BitVec.ofNat 32 j) hz
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      have := congrArg BitVec.toNat this
      simp [hx] at this
      omega)
    have hz1 : z.toNat ≠ 0 := fun e => hz0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    rw [hz]
    have hs : (z - 1) >>> 8 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow,
        show (1 : BitVec 32).toNat = 1 from rfl, show (0 : BitVec 32).toNat = 0 from rfl]
      omega
    rw [hs, and_zero32]

/-- One entry: `r3` gains the entry's byte iff the index is `j`; on to the
next entry. -/
theorem piBody_ok (s : State) (x : Byte) {j : Nat} (hj : j < 256)
    (h12 : s.gpr .r12 = x.setWidth 32) (h9 : s.gpr .r9 = BitVec.ofNat 32 j)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 1) :
    ∃ s', runBlock isa piBody s = some s' ∧
      s'.gpr .r3 = s.gpr .r3 ||| (if x.toNat = j then
        (s.mem (State.addr (s.gpr .lr + BitVec.ofNat 32 0))).setWidth 32 else 0) ∧
      s'.gpr .r9 = BitVec.ofNat 32 (j + 1) ∧ s'.gpr .lr = s.gpr .lr + 1 ∧
      s'.z = (BitVec.ofNat 32 j - 255 == 0) ∧ Keep piLoopRegs s s' := by
  have e1 : encodable (1 : BitVec 32) = true := by decide
  have e255 : encodable (255 : BitVec 32) = true := by decide
  refine ⟨_, by
    simp only [piBody, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, State.load8,
      hin, e1, e255, Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_subFlags, reduceCtorEq, ite_true, ite_false]
    rw [h12, h9, maskByte _ x hj]
  · simp only [gpr_setReg, gpr_subFlags, reduceCtorEq, ite_true, ite_false]
    rw [h9, BitVec.ofNat_add]; rfl
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

/-- The value of the lookup once entries `0 … j - 1` are visited. -/
def piAcc (x : Byte) (j : Nat) : BitVec 32 :=
  if x.toNat < j then (Spec.Rc2.pi x).setWidth 32 else 0

/-- The state of the scan from `s₀` with entries `0 … j - 1` visited. -/
structure PiScanAt (s₀ : State) (T : BitVec 32) (x : Byte) (j : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = x.setWidth 32
  r9 : s.gpr .r9 = BitVec.ofNat 32 j
  lr : s.gpr .lr = T + BitVec.ofNat 32 j
  r3 : s.gpr .r3 = piAcc x j
  keep : Keep piLoopRegs s₀ s

theorem piAcc_succ (x : Byte) {j : Nat} :
    (piAcc x j ||| if x.toNat = j then (Spec.Rc2.piTable.getD j 0).setWidth 32 else 0) = piAcc x (j + 1) := by
  unfold piAcc
  by_cases h : x.toNat = j
  · rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_left (by omega), ← h]
    exact BitVec.eq_of_getLsbD_eq (by simp [Spec.Rc2.pi])
  · rw [ite_eq_right h, or_zero32]
    by_cases h2 : x.toNat < j
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem piScan_step {s₀ s : State} {T : BitVec 32} {x : Byte} {j : Nat} (hj : j < 256)
    (hT : PiTab T s₀) (h : PiScanAt s₀ T x j s) :
    WP isa (.block piBody) s fun t => PiScanAt s₀ T x (j + 1) t ∧ t.z = decide (j = 255) := by
  have fit := hT.fit
  have ea : State.addr (s.gpr .lr + BitVec.ofNat 32 0) = State.addr T + BitVec.ofNat 64 j := by
    rw [h.lr, BitVec.add_zero, addr_add (by omega)]
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 1 := by
    rw [h.keep.rd, h.keep.wr, ea]
    exact ⟨_, List.mem_append_left _ hT.rd, Offset.contains_base _ (by omega) (by omega)⟩
  have hb : s.mem (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) = Spec.Rc2.piTable.getD j 0 := by
    rw [ea, h.keep.mem]; exact hT.held j hj
  obtain ⟨t, run, t3, t9, tl, tz, tk⟩ := piBody_ok s x hj h.r12 h.r9 hin
  refine WP.of_runBlock ⟨t, run, ⟨?_, t9, ?_, ?_, h.keep.trans tk⟩, ?_⟩
  · rw [tk.reg .r12 (by decide), h.r12]
  · rw [tl, h.lr, BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  · rw [t3, h.r3, hb, piAcc_succ]
  · rw [tz]
    by_cases he : j = 255
    · subst he; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 j - 255 ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        simp at this; omega
      simpa using this

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
  have loop : WP isa (.loop (.block piBody) .ne) s₁ (PiScanAt s₁ T x 256) := by
    refine WP.loop (M := isa) (fun n (v : State) => ∃ j, n = 256 - j ∧ j < 256 ∧ PiScanAt s₁ T x j v)
      ?_ 256 s₁ ⟨0, rfl, by decide, h₁⟩
    rintro n v ⟨j, rfl, hj, hv⟩
    refine WP.mono (piScan_step hj hT₁ hv) fun w ⟨hw, wz⟩ => ?_
    by_cases he : j = 255
    · subst he
      exact .inl ⟨by show some (!w.z) = _; rw [wz]; rfl, hw⟩
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, 256 - (j + 1), by omega, j + 1, rfl,
        by omega, hw⟩
  refine WP.seq (WP.mono loop fun v hv => WP.of_runBlock ⟨v.setReg .r12 (v.gpr .r3), by
    simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some], ?_⟩)
  refine ⟨?_, ?_⟩
  · rw [gpr_setReg_self, hv.r3, piAcc, ite_eq_left x.isLt]
  · have k₂ : Keep piRegs s₁ v := hv.keep.weaken (by
      intro r hr; simp only [piLoopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h <;> subst h <;> decide)
    refine (k₁.trans k₂).trans ⟨fun r hr => gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self)),
      mem_setReg _ _ _, rd_setReg _ _ _, wr_setReg _ _ _⟩

end VG.Proof.Rc2.Arm
