import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Rc2.Arm.Block
import VerifiedGarbage.Impl.Rc2.Arm.Lookup
import VerifiedGarbage.Proof.Rc2.Word32
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Rc2.PiLit
import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Lookup`. -/
section

/-! # Correctness of baseline Arm RC2 lookup steps -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

/-- A register-only block preserves memory, regions, and other GPRs. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : VG.Proof.Rc2.Arm.Keep rs s s') (h' : VG.Proof.Rc2.Arm.Keep rs s' s'') : VG.Proof.Rc2.Arm.Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem byte_imm (b : Byte) : (BitVec.ofNat 16 b.toNat).setWidth 32 = b.setWidth 32 := by
  simp

theorem index_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 i).setWidth 32 = (BitVec.ofNat 8 i).setWidth 32 := by
  have h : BitVec.ofNat 16 i = (BitVec.ofNat 8 i).setWidth 16 := by bv_omega
  rw [h]; simp

theorem piStep_ok (s : State) (x : Byte) (hx : s.gpr .r12 = x.setWidth 32)
    (i : Nat) (hi : i < 256) :
    ∃ s', runBlock isa (piStep i) s = some s' ∧
      s'.gpr .r3 = s.gpr .r3 |||
        (if x.toNat = i then (Spec.Rc2.piTable.getD i 0).setWidth 32 else 0) ∧
      VG.Proof.Rc2.Arm.Keep [.r3, .r10, .r11] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [piStep, selectMask, imm, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, gpr_setReg,
      ite_true, ite_false]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [hx, VG.Proof.Rc2.Arm.index_imm i hi, VG.Proof.Rc2.Arm.byte_imm]
    simp only [BitVec.setWidth_zero]
    change s.gpr .r3 |||
      ((0 - (((x.setWidth 32 ^^^ (BitVec.ofNat 8 i).setWidth 32) - 1) >>> 31)) &&&
        (Spec.Rc2.piTable.getD i 0).setWidth 32) = _
    rw [VG.Proof.Rc2.Word32.selectMask_eq]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.allOnes_and]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]


theorem piSteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 256)
    (s : State) (x : Byte) (hx : s.gpr .r12 = x.setWidth 32) :
    WP isa (.block (is.flatMap piStep)) s (fun s' =>
      s'.gpr .r3 = s.gpr .r3 |||
        (if x.toNat ∈ is then (Spec.Rc2.piTable.getD x.toNat 0).setWidth 32 else 0) ∧
      VG.Proof.Rc2.Arm.Keep [.r3, .r10, .r11] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.Arm.piStep_ok s x hx i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .r12 (by decide)).trans hx
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ hx₁)
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁]
    by_cases h : x.toNat = i
    · subst i
      by_cases hm : x.toNat ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x.toNat ∈ is <;> simp [h, hm]

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Rc2.Arm.Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Rc2.Arm.Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem maskBits (x : BitVec 32) (n : Nat) (hn : n ≤ 32) :
    x <<< (32 - n) >>> (32 - n) = (x.setWidth n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  have ha : 32 - n + i < 32 ↔ i < n := by omega
  have hb : ¬32 - n + i < 32 - n := by omega
  simp only [ha, hb, hi, decide_true, decide_false, Bool.not_false,
    Bool.and_true, Bool.true_and, Nat.add_sub_cancel_left]

theorem piStart_ok (s : State) :
    ∃ s', runBlock isa (mask .r12 8 ++ [imm .r3 0]) s = some s' ∧
      s'.gpr .r12 = ((s.gpr .r12).setWidth 8).setWidth 32 ∧ s'.gpr .r3 = 0 ∧
      VG.Proof.Rc2.Arm.Keep [.r12, .r3, .r10, .r11] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [mask, imm, List.cons_append, List.nil_append, runBlock_cons,
      exec, Op2.eval]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
    exact VG.Proof.Rc2.Arm.maskBits _ 8 (by decide)
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.1, ite_false]
    · rfl
    · rfl
    · rfl

theorem piLookup_ok (s : State) :
    WP isa (.block piLookup) s (fun s' =>
      s'.gpr .r12 = (Spec.Rc2.pi ((s.gpr .r12).setWidth 8)).setWidth 32 ∧
      VG.Proof.Rc2.Arm.Keep [.r12, .r3, .r10, .r11] s s') := by
  rw [piLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := VG.Proof.Rc2.Arm.piStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.Arm.piSteps_ok (List.range 256) (fun i hi => List.mem_range.mp hi)
    s₁ ((s.gpr .r12).setWidth 8) input₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .r3 = (Spec.Rc2.pi ((s.gpr .r12).setWidth 8)).setWidth 32 := by
    rw [h₂.1, zero₁]
    simp only [List.mem_range]
    rw [ite_eq_left ((s.gpr .r12).setWidth 8).isLt]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .r12 (s₂.gpr .r3), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, ]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : VG.Proof.Rc2.Arm.Keep [.r12, .r3, .r10, .r11] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _



theorem keyStep_ok (s : State) (x : Byte) (hx : s.gpr .r12 = x.setWidth 32)
    (i : Nat) (hi : i < 64)
    (hlo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i))) 1)
    (hhi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i + 1))) 1) :
    ∃ s', runBlock isa (keyStep i) s = some s' ∧
      s'.gpr .r3 = s.gpr .r3 |||
        (if x.toNat = i then
          ((s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i)))).setWidth 16 |||
            (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i + 1)))).setWidth 16 <<< 8).setWidth 32
          else 0) ∧
      VG.Proof.Rc2.Arm.Keep [.r3, .r8, .r9, .r10, .r11] s s' := by
  have hloOff : 2 * i < 4096 := by omega
  have hhiOff : 2 * i + 1 < 4096 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [keyStep, selectMask, loadKey, imm,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.load8,
      Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg,
      wr_setReg,  hloOff, hhiOff, hlo, hhi, ite_true, ite_false]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [hx, VG.Proof.Rc2.Arm.index_imm i (by omega)]
    change s.gpr .r3 |||
      (((s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i)))).setWidth 32 |||
        ((s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i + 1)))).setWidth 32).rotateRight 24) &&&
        (0 - (((x.setWidth 32 ^^^ (BitVec.ofNat 8 i).setWidth 32) - 1) >>> 31))) = _
    rw [VG.Proof.Rc2.Word32.selectMask_eq, VG.Proof.Rc2.Word32.joinBytes]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.and_allOnes]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

theorem keySteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 64)
    (s : State) (x : Byte) (hx : s.gpr .r12 = x.setWidth 32)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 i)) 1) :
    WP isa (.block (is.flatMap keyStep)) s (fun s' =>
      s'.gpr .r3 = s.gpr .r3 |||
        (if x.toNat ∈ is then
          ((s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * x.toNat)))).setWidth 16 |||
            (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * x.toNat + 1)))).setWidth 16 <<< 8).setWidth 32
          else 0) ∧ VG.Proof.Rc2.Arm.Keep [.r3, .r8, .r9, .r10, .r11] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have bound := hi i (by simp)
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.Arm.keyStep_ok s x hx i bound
      (readable (2 * i) (by omega)) (readable (2 * i + 1) (by omega))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .r12 (by decide)).trans hx
    have ptr₁ := keep₁.reg .r0 (by decide)
    have read₁ : ∀ j < 128,
        InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 j)) 1 := by
      rw [keep₁.rd, keep₁.wr, ptr₁]
      exact readable
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ hx₁ read₁)
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁, keep₁.mem, ptr₁]
    by_cases h : x.toNat = i
    · subst i
      by_cases hm : x.toNat ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x.toNat ∈ is <;> simp [h, hm]


theorem keyStart_ok (s : State) :
    ∃ s', runBlock isa (mask .r12 6 ++ [imm .r3 0]) s = some s' ∧
      s'.gpr .r12 = ((s.gpr .r12).setWidth 6).setWidth 32 ∧ s'.gpr .r3 = 0 ∧
      VG.Proof.Rc2.Arm.Keep [.r12, .r3, .r8, .r9, .r10, .r11] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [mask, imm, List.cons_append, List.nil_append, runBlock_cons,
      exec, Op2.eval]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
    exact VG.Proof.Rc2.Arm.maskBits _ 6 (by decide)
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.1, ite_false]
    · rfl
    · rfl
    · rfl

theorem scheduleAt_getD (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    (Spec.Rc2.scheduleAt m p).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.scheduleAt, Vector.getD, hi]

theorem keyLookup_ok (s : State) (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 i)) 1) :
    WP isa (.block keyLookup) s (fun s' =>
      s'.gpr .r12 = ((Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD
        ((s.gpr .r12).setWidth 6).toNat 0).setWidth 32 ∧
      VG.Proof.Rc2.Arm.Keep [.r12, .r3, .r8, .r9, .r10, .r11] s s') := by
  rw [keyLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := VG.Proof.Rc2.Arm.keyStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ := keep₁.reg .r0 (by decide)
  have read₁ : ∀ i < 128,
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 i)) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]
    exact readable
  have inputByte : s₁.gpr .r12 = (((s.gpr .r12).setWidth 6).setWidth 8).setWidth 32 := by
    rw [input₁]; simp
  apply WP.mono (VG.Proof.Rc2.Arm.keySteps_ok (List.range 64) (fun i hi => List.mem_range.mp hi)
    s₁ (((s.gpr .r12).setWidth 6).setWidth 8) inputByte read₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .r3 = ((Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD
      ((s.gpr .r12).setWidth 6).toNat 0).setWidth 32 := by
    rw [h₂.1, zero₁, keep₁.mem, ptr₁]
    simp only [List.mem_range, BitVec.toNat_setWidth]
    have bound := ((s.gpr .r12).setWidth 6).isLt
    simp only [BitVec.toNat_setWidth] at bound
    rw [Nat.mod_eq_of_lt (show (s.gpr .r12).toNat % 64 < 256 by omega),
      ite_eq_left bound, VG.Proof.Rc2.Arm.scheduleAt_getD _ _ _ bound]
    rw [addr_add (by omega_using [fit, bound]), addr_add (by omega_using [fit, bound])]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .r12 (s₂.gpr .r3), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : VG.Proof.Rc2.Arm.Keep [.r12, .r3, .r8, .r9, .r10, .r11] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _

end VG.Proof.Rc2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Rounds`. -/
section

/-! # RC2 mixing and mashing in Arm registers -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

/-- State words never alias the temporaries or argument registers. -/
theorem wordReg_separate (i : Nat) :
    wordReg i ≠ .r12 ∧ wordReg i ≠ .r3 ∧ wordReg i ≠ .r2 ∧ wordReg i ≠ .r0 ∧
    wordReg i ≠ .r1 ∧ wordReg i ≠ .r8 ∧ wordReg i ≠ .r9 ∧
    wordReg i ≠ .r10 ∧ wordReg i ≠ .r11 := by
  have h : ∀ j < 4,
      wordReg j ≠ .r12 ∧ wordReg j ≠ .r3 ∧ wordReg j ≠ .r2 ∧ wordReg j ≠ .r0 ∧
      wordReg j ≠ .r1 ∧ wordReg j ≠ .r8 ∧ wordReg j ≠ .r9 ∧
      wordReg j ≠ .r10 ∧ wordReg j ≠ .r11 := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_injective : ∀ i < 4, ∀ j < 4, wordReg i = wordReg j ↔ i = j := by decide

theorem rotation_bounds (i : Nat) : 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by
  have h : ∀ j < 4, 1 ≤ Spec.Rc2.rotation j ∧ Spec.Rc2.rotation j < 16 := by decide
  simpa only [Spec.Rc2.rotation, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem rotate16_ok (s : State) (r : Reg) (hr : r ≠ .r12)
    (x : BitVec 16) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ∃ s', runBlock isa (rotate16 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧ VG.Proof.Rc2.Arm.Keep [r, .r12] s s' := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega
  have hright : 1 ≤ 16 - n ∧ 16 - n ≤ 31 := by omega
  refine ⟨_, by
    simp only [rotate16, mask, rr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, and_self, Nat.reduceSub, hleft, hright, show 1 ≤ 16 ∧ 16 ≤ 31 by decide, ite_true, hr, Ne.symm hr,
       gpr_setReg,
      ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, ite_true,
      hr, ite_false]
    rw [hx]
    rw [VG.Proof.Rc2.Arm.maskBits _ 16 (by decide), ← VG.Proof.Rc2.Word32.maskWord]
    exact VG.Proof.Rc2.Word32.rotateWord x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

theorem mixInputs_ok (s : State) (i j : Nat) (hj : j < 64)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    ∃ s', runBlock isa (mixInputs j i) s = some s' ∧
      s'.gpr .r10 = (s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
        (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))) ∧
      s'.gpr .r8 = ((Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD j 0).setWidth 32 ∧
      VG.Proof.Rc2.Arm.Keep [.r8, .r9, .r10, .r11] s s' := by
  have h₁ := VG.Proof.Rc2.Arm.wordReg_separate (i + 1)
  have h₂ := VG.Proof.Rc2.Arm.wordReg_separate (i + 2)
  have h₃ := VG.Proof.Rc2.Arm.wordReg_separate (i + 3)
  have lo := readable (2 * j) (by omega)
  have hi := readable (2 * j + 1) (by omega)
  have loOff : 2 * j < 4096 := by omega
  have hiOff : 2 * j + 1 < 4096 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [mixInputs, loadKey, imm,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.load8,
      Option.map_some,
       gpr_setReg,
      mem_setReg, rd_setReg,
      wr_setReg, loOff, hiOff, lo, hi, ite_true, ite_false,
      h₁.2.2.2.2.2.2.2.1, h₁.2.2.2.2.2.2.2.2,
      h₃.2.2.2.2.2.2.2.1, h₃.2.2.2.2.2.2.2.2]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true,
      ite_false]
    simp only [BitVec.setWidth_zero]
    have comp (x : BitVec 32) : 0#32 - x - 1 = ~~~x := by bv_omega
    rw [comp]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [VG.Proof.Rc2.Word32.joinBytes, VG.Proof.Rc2.Arm.scheduleAt_getD _ _ _ hj]
    rw [addr_add (by omega_using [fit, hj]), addr_add (by omega_using [fit, hj])]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

/-- Current RC2 words in the four dedicated registers. -/
def Words (s : State) (v : Spec.Rc2.State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 32

def temps : List Reg := [.r12, .r3, .r8, .r9, .r10, .r11]
def roundWrites : List Reg := VG.Proof.Rc2.Arm.temps ++ [.r4, .r5, .r6, .r7]

theorem wordReg_not_temps (i : Nat) : wordReg i ∉ VG.Proof.Rc2.Arm.temps := by
  have h := VG.Proof.Rc2.Arm.wordReg_separate i
  simp only [VG.Proof.Rc2.Arm.temps, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem wordReg_mem_roundWrites (i : Nat) : wordReg i ∈ VG.Proof.Rc2.Arm.roundWrites := by
  have h : ∀ j < 4, wordReg j ∈ VG.Proof.Rc2.Arm.roundWrites := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by
  simp [Vector.getD, hi]

theorem Words.update {s s' : State} {v : Spec.Rc2.State} (h : VG.Proof.Rc2.Arm.Words s v)
    (i : Nat) (hi : i < 4) (x : BitVec 16)
    (out : s'.gpr (wordReg i) = x.setWidth 32)
    (keep : VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s') : VG.Proof.Rc2.Arm.Words s' (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j
    simpa [Vector.getD, hi] using out
  · have hr : wordReg j ∉ wordReg i :: VG.Proof.Rc2.Arm.temps := by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => he ((VG.Proof.Rc2.Arm.wordReg_injective j hj i hi).mp e), VG.Proof.Rc2.Arm.wordReg_not_temps j⟩
    rw [keep.reg _ hr, h j hj]
    rw [VG.Proof.Rc2.Arm.vector_getD _ j hj, VG.Proof.Rc2.Arm.vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

theorem Words.preserve {s s' : State} {v : Spec.Rc2.State} (h : VG.Proof.Rc2.Arm.Words s v)
    (keep : VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.temps s s') : VG.Proof.Rc2.Arm.Words s' v := by
  intro i hi
  exact (keep.reg _ (VG.Proof.Rc2.Arm.wordReg_not_temps i)).trans (h i hi)

theorem Keep.round {s s' : State} {i : Nat}
    (h : VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s') : VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s' :=
  h.weaken (by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with he | hm
    · subst r; exact VG.Proof.Rc2.Arm.wordReg_mem_roundWrites i
    · exact List.mem_append_left _ hm)


theorem addInputs_ok (s : State) (r : Reg) (h6 : r ≠ .r10) :
    ∃ s', runBlock isa (addInputs r) s = some s' ∧
      s'.gpr r = (s.gpr r + s.gpr .r8 + s.gpr .r10) &&& 65535 ∧ VG.Proof.Rc2.Arm.Keep [r] s s' := by
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, and_self, addInputs, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      gpr_setReg, Ne.symm h6]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
    rw [VG.Proof.Rc2.Arm.maskBits _ 16 (by decide), VG.Proof.Rc2.Word32.maskWord]
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem subInputs_ok (s : State) (r : Reg) (h6 : r ≠ .r10) :
    ∃ s', runBlock isa (subInputs r) s = some s' ∧
      s'.gpr r = (s.gpr r - s.gpr .r8 - s.gpr .r10) &&& 65535 ∧ VG.Proof.Rc2.Arm.Keep [r] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [subInputs, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      gpr_setReg, Ne.symm h6, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
    rw [VG.Proof.Rc2.Arm.maskBits _ 16 (by decide), VG.Proof.Rc2.Word32.maskWord]
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem mix_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block (mix j i)) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' (Spec.Rc2.mix (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j i v) ∧
      VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s') := by
  rw [mix, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, composite₁, key₁, keep₁⟩ := VG.Proof.Rc2.Arm.mixInputs_ok s i j hj fit readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have sep := VG.Proof.Rc2.Arm.wordReg_separate i
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := VG.Proof.Rc2.Arm.addInputs_ok s₁ (wordReg i)
    sep.2.2.2.2.2.2.2.1
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  let x := v.getD i 0 + (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD j 0 +
    (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) +
    (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)
  have wordmod (j : Nat) : wordReg j = wordReg (j % 4) := by simp [wordReg]
  have value₂ : s₂.gpr (wordReg i) = x.setWidth 32 := by
    rw [out₂, key₁, composite₁, keep₁.reg (wordReg i) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
        sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩), hv i hi,
      wordmod (i + 3), wordmod (i + 2), wordmod (i + 1),
      hv _ (Nat.mod_lt _ (by decide)), hv _ (Nat.mod_lt _ (by decide)),
      hv _ (Nat.mod_lt _ (by decide))]
    exact VG.Proof.Rc2.Word32.mixWord _ _ _ _ _
  have hn := VG.Proof.Rc2.Arm.rotation_bounds i
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.Arm.rotate16_ok s₂ (wordReg i) sep.1 x value₂ _ hn.1 hn.2
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₁ : VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s₁ := keep₁.weaken (by
    intro r hr
    apply List.mem_cons_of_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have k₂ : VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s₁ s₂ := keep₂.weaken (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact List.mem_cons_self)
  have k₃ : VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s₂ s₃ := keep₃.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h
    · subst r; exact List.mem_cons_self
    · subst r; exact List.mem_cons_of_mem _ (by decide))
  have keep := (k₁.trans k₂).trans k₃
  exact ⟨hv.update i hi (x.rotateLeft _) out₃ keep, keep⟩

theorem wordReg_mod (i : Nat) : wordReg i = wordReg (i % 4) := by simp [wordReg]

theorem wordReg_offset_ne (i : Nat) (hi : i < 4) (d : Nat) (hd : 1 ≤ d) (hd' : d < 4) :
    wordReg (i + d) ≠ wordReg i := by
  rw [VG.Proof.Rc2.Arm.wordReg_mod (i + d)]
  intro he
  have := (VG.Proof.Rc2.Arm.wordReg_injective _ (Nat.mod_lt _ (by decide)) i hi).mp he
  omega

theorem keep_inputs {s s' : State} (h : VG.Proof.Rc2.Arm.Keep [.r8, .r9, .r10, .r11] s s') (i : Nat) :
    VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s' := h.weaken (by
  intro r hr
  apply List.mem_cons_of_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> subst r <;> decide)

theorem keep_rotate {i : Nat} {s s' : State} (h : VG.Proof.Rc2.Arm.Keep [wordReg i, .r12] s s') :
    VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · subst r; exact List.mem_cons_self
  · subst r; exact List.mem_cons_of_mem _ (by decide))

theorem keep_word {i : Nat} {s s' : State} (h : VG.Proof.Rc2.Arm.Keep [wordReg i] s s') :
    VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r; exact List.mem_cons_self)

theorem reverseMix_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block (reverseMix j i)) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j i v) ∧
      VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s') := by
  rw [reverseMix, List.append_assoc, WP.block_append_iff]
  have sep := VG.Proof.Rc2.Arm.wordReg_separate i
  have hn := VG.Proof.Rc2.Arm.rotation_bounds i
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.Arm.rotate16_ok s (wordReg i) sep.1 (v.getD i 0)
    (hv i hi) (16 - Spec.Rc2.rotation i) (by omega) (by omega)
  rw [VG.Proof.Rc2.Word32.rotateLeft_reverse _ _ hn.1 hn.2] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ : s₁.gpr .r0 = s.gpr .r0 := keep₁.reg _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm sep.2.2.2.1, by decide⟩)
  have read₁ : ∀ k < 128,
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 k)) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable
  obtain ⟨s₂, run₂, composite₂, key₂, keep₂⟩ := VG.Proof.Rc2.Arm.mixInputs_ok s₁ i j hj (by rw [ptr₁]; exact fit) read₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.Arm.subInputs_ok s₂ (wordReg i) sep.2.2.2.2.2.2.2.1
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have other (d : Nat) (hd : 1 ≤ d) (hd' : d < 4) :
      s₁.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 32 := by
    rw [keep₁.reg _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨VG.Proof.Rc2.Arm.wordReg_offset_ne i hi d hd hd', (VG.Proof.Rc2.Arm.wordReg_separate _).1⟩),
      VG.Proof.Rc2.Arm.wordReg_mod (i + d)]
    exact hv _ (Nat.mod_lt _ (by decide))
  have keptWord := keep₂.reg (wordReg i) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
      sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩)
  have value₃ : s₃.gpr (wordReg i) =
      ((v.getD i 0).rotateRight (Spec.Rc2.rotation i) -
        (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD j 0 -
        (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) -
        (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)).setWidth 32 := by
    rw [out₃, keptWord, out₁, key₂, composite₂, keep₁.mem, ptr₁,
      other 3 (by decide) (by decide), other 2 (by decide) (by decide),
      other 1 (by decide) (by decide)]
    exact VG.Proof.Rc2.Word32.reverseMixWord _ _ _ _ _
  have keep := ((VG.Proof.Rc2.Arm.keep_rotate keep₁).trans (VG.Proof.Rc2.Arm.keep_inputs keep₂ i)).trans (VG.Proof.Rc2.Arm.keep_word keep₃)
  exact ⟨hv.update i hi _ value₃ keep, keep⟩

theorem adjust_ok (s : State) (r : Reg) (sub : Bool) :
    ∃ s', runBlock isa (adjust sub r) s = some s' ∧
      s'.gpr r = (if sub then s.gpr r - s.gpr .r12 else s.gpr r + s.gpr .r12) &&& 65535 ∧
      VG.Proof.Rc2.Arm.Keep [r] s s' := by
  cases sub <;> refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, and_self, adjust, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, gpr_setReg]
    rfl, ?_⟩
  all_goals
    constructor
    · simp only [gpr_setReg_self, Bool.false_eq_true,
        ite_false, ite_true]
      rw [VG.Proof.Rc2.Arm.maskBits _ 16 (by decide), VG.Proof.Rc2.Word32.maskWord]
    · constructor
      · intro r' hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, hr, ite_false]
      · rfl
      · rfl
      · rfl

theorem indexWord (x : BitVec 16) :
    ((x.setWidth 32).setWidth 6).toNat = (x &&& 63).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  change x.toNat % 4294967296 % 64 = x.toNat &&& (2 ^ 6 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show x.toNat < 4294967296 by have := x.isLt; omega)]

def mashSpec (direction : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match direction with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem mash_ok (direction : Spec.Rc2.Direction) (s : State)
    (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v) (i : Nat) (hi : i < 4)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block (mash direction i)) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' (VG.Proof.Rc2.Arm.mashSpec direction (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) i v) ∧
      VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s') := by
  rw [mash, List.append_assoc, WP.block_append_iff]
  let s₁ := s.setReg .r12 (s.gpr (wordReg (i + 3)))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.temps s s₁ := by
    constructor
    · intro r hr
      exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _
  have ptr₁ := keep₁.reg .r0 (by decide)
  have read₁ : ∀ k < 128,
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 k)) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable
  apply WP.mono (VG.Proof.Rc2.Arm.keyLookup_ok s₁ (by rw [ptr₁]; exact fit) read₁)
  intro s₂ h₂
  let k := Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))
  let key := k.getD ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0
  have out₂ : s₂.gpr .r12 = key.setWidth 32 := by
    rw [h₂.1, keep₁.mem, ptr₁]
    change (k.getD (((s.gpr (wordReg (i + 3))).setWidth 6).toNat) 0).setWidth 32 = _
    rw [VG.Proof.Rc2.Arm.wordReg_mod (i + 3), hv _ (Nat.mod_lt _ (by decide)), VG.Proof.Rc2.Arm.indexWord]
  have keep₂ : VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.temps s₁ s₂ := h₂.2
  have value₂ := ((hv.preserve keep₁).preserve keep₂) i hi
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.Arm.adjust_ok s₂ (wordReg i) (direction == .decrypt)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep : VG.Proof.Rc2.Arm.Keep (wordReg i :: VG.Proof.Rc2.Arm.temps) s s₃ :=
    ((keep₁.trans keep₂).weaken (fun _ hr => List.mem_cons_of_mem _ hr)).trans (VG.Proof.Rc2.Arm.keep_word keep₃)
  have out₃' : s₃.gpr (wordReg i) =
      (if direction == .decrypt then v.getD i 0 - key else v.getD i 0 + key).setWidth 32 := by
    rw [out₃, value₂, out₂]
    cases direction <;>
      simp [VG.Proof.Rc2.Word32.maskWord_lit, BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]
  constructor
  · cases direction <;> exact hv.update i hi _ out₃' keep
  · exact keep

end VG.Proof.Rc2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Save`. -/
section

section

/-! # Composition of RC2's sixteen rounds -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem foldWords_ok (code : Nat → List Instr)
    (step : Spec.Rc2.Schedule → Nat → Spec.Rc2.State → Spec.Rc2.State) (is : List Nat)
    (correct : ∀ i ∈ is, ∀ (s : State) (v : Spec.Rc2.State), VG.Proof.Rc2.Arm.Words s v → (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 →
      (∀ j < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 j)) 1) →
      WP isa (.block (code i)) s (fun s' =>
        VG.Proof.Rc2.Arm.Words s' (step (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) i v) ∧ VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s'))
    (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ j < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 j)) 1) :
    WP isa (.block (is.flatMap code)) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' (is.foldl (fun v i => step (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) i v) v) ∧
      VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s') := by
  induction is generalizing s v with
  | nil =>
    apply WP.block_nil
    exact ⟨hv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (correct i (by simp) s v hv fit readable)
    intro s₁ h₁
    have ptr₁ := h₁.2.reg .r0 (by decide)
    have read₁ : ∀ j < 128,
        InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 j)) 1 := by
      rw [h₁.2.rd, h₁.2.wr, ptr₁]; exact readable
    apply WP.mono (ih (fun j hj => correct j (List.mem_cons_of_mem _ hj)) s₁ _ h₁.1 (by rw [ptr₁]; exact fit) read₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₁.2.mem, ptr₁] at h₂
    exact h₂.1

theorem mixRound_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (j : Nat) (hj : j < 16)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block ((List.range 4).flatMap (fun i => mix (4 * j + i) i))) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' (Spec.Rc2.mixRound (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) ∧
      VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s') := by
  apply VG.Proof.Rc2.Arm.foldWords_ok (step := fun k i v => Spec.Rc2.mix k (4 * j + i) i v) _ _ _ s v hv fit readable
  intro i hi s v hv fit readable
  have bound := List.mem_range.mp hi
  apply WP.mono (VG.Proof.Rc2.Arm.mix_ok s v hv i (4 * j + i) bound (by omega) fit readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

theorem reverseMixRound_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (j : Nat) (hj : j < 16)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block ([3, 2, 1, 0].flatMap (fun i => reverseMix (4 * j + i) i))) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' (Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) ∧
      VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s') := by
  apply VG.Proof.Rc2.Arm.foldWords_ok (step := fun k i v => Spec.Rc2.reverseMix k (4 * j + i) i v) _ _ _ s v hv fit readable
  intro i hi s v hv fit readable
  have bound : i < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  apply WP.mono (VG.Proof.Rc2.Arm.reverseMix_ok s v hv i (4 * j + i) bound (by omega) fit readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def order (d : Spec.Rc2.Direction) : List Nat :=
  match d with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

theorem mashRound_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block ((VG.Proof.Rc2.Arm.order d).flatMap (mash d))) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' (VG.Proof.Rc2.Arm.mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) v) ∧
      VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s') := by
  have he (k : Spec.Rc2.Schedule) : VG.Proof.Rc2.Arm.mashRoundSpec d k v =
      (VG.Proof.Rc2.Arm.order d).foldl (fun v i => VG.Proof.Rc2.Arm.mashSpec d k i v) v := by cases d <;> rfl
  simp only [he]
  apply VG.Proof.Rc2.Arm.foldWords_ok (step := fun k i v => VG.Proof.Rc2.Arm.mashSpec d k i v) _ _ _ s v hv fit readable
  intro i hi s v hv fit readable
  have bound : i < 4 := by
    cases d with
    | encrypt => exact List.mem_range.mp hi
    | decrypt =>
      simp only [VG.Proof.Rc2.Arm.order, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
  apply WP.mono (VG.Proof.Rc2.Arm.mash_ok d s v hv i bound fit readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  let v := match d with
    | .encrypt => Spec.Rc2.mixRound k j v
    | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v
  if j = 4 ∨ j = 10 then VG.Proof.Rc2.Arm.mashRoundSpec d k v else v

theorem round_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (j : Nat) (hj : j < 16)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block (VG.Impl.Rc2.Arm.round d j)) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' (VG.Proof.Rc2.Arm.roundSpec d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) ∧
      VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s') := by
  have finish (s₁ : State) (v₁ : Spec.Rc2.State) (h₁ : VG.Proof.Rc2.Arm.Words s₁ v₁ ∧ VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s₁) :
      WP isa (.block (if j = 4 ∨ j = 10 then (VG.Proof.Rc2.Arm.order d).flatMap (mash d) else [])) s₁ (fun s₂ =>
        VG.Proof.Rc2.Arm.Words s₂ (if j = 4 ∨ j = 10 then VG.Proof.Rc2.Arm.mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) v₁
          else v₁) ∧ VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s₂) := by
    by_cases h : j = 4 ∨ j = 10
    · rw [ite_eq_left h]
      have ptr₁ := h₁.2.reg .r0 (by decide)
      have read₁ : ∀ k < 128,
          InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 k)) 1 := by
        rw [h₁.2.rd, h₁.2.wr, ptr₁]; exact readable
      apply WP.mono (VG.Proof.Rc2.Arm.mashRound_ok d s₁ v₁ h₁.1 (by rw [ptr₁]; exact fit) read₁)
      intro s₂ h₂
      rw [h₁.2.mem, ptr₁] at h₂
      exact ⟨by simpa only [ite_eq_left h] using h₂.1, h₁.2.trans h₂.2⟩
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by simpa only [ite_eq_right h] using h₁.1, h₁.2⟩
  cases d with
  | encrypt =>
    rw [VG.Impl.Rc2.Arm.round, WP.block_append_iff]
    apply WP.mono (VG.Proof.Rc2.Arm.mixRound_ok s v hv j hj fit readable)
    intro s₁ h₁
    exact finish s₁ _ h₁
  | decrypt =>
    rw [VG.Impl.Rc2.Arm.round, WP.block_append_iff]
    apply WP.mono (VG.Proof.Rc2.Arm.reverseMixRound_ok s v hv (15 - j) (by omega) fit readable)
    intro s₁ h₁
    exact finish s₁ _ h₁

theorem rounds_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block ((List.range 16).flatMap (VG.Impl.Rc2.Arm.round d))) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' ((List.range 16).foldl (fun v j => VG.Proof.Rc2.Arm.roundSpec d
        (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) v) ∧ VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s') := by
  apply VG.Proof.Rc2.Arm.foldWords_ok (step := fun k j v => VG.Proof.Rc2.Arm.roundSpec d k j v) _ _ _ s v hv fit readable
  intro j hj s v hv fit readable
  exact VG.Proof.Rc2.Arm.round_ok d s v hv j (List.mem_range.mp hj) fit readable

end VG.Proof.Rc2.Arm

end

section

section

/-! # Byte loads and stores for RC2 on ARMv7 -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm

theorem decode_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m p)).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  rw [Spec.Rc2.decodeBlock, getD_ofFn _ i hi]
  change ((Spec.Rc2.blockAt m p).getD (2 * i) 0).setWidth 16 |||
    ((Spec.Rc2.blockAt m p).getD (2 * i + 1) 0).setWidth 16 <<< 8 = _
  rw [Spec.Rc2.blockAt, getD_ofFn _ _ (by omega), getD_ofFn _ _ (by omega)]

theorem loadWord_ok (s : State) (i : Nat) (hi : i < 4)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa (loadWord i) s = some s' ∧
      s'.gpr (wordReg i) =
        ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).getD i 0).setWidth 32 ∧
      VG.Proof.Rc2.Arm.Keep [wordReg i, .r12] s s' := by
  have sep := VG.Proof.Rc2.Arm.wordReg_separate i
  have lo := readable (2 * i) (by omega)
  have high := readable (2 * i + 1) (by omega)
  have a := addr_add (a := s.gpr .r1) (k := 2 * i) (by omega)
  have b := addr_add (a := s.gpr .r1) (k := 2 * i + 1) (by omega)
  have loOff : 2 * i < 4096 := by omega
  have hiOff : 2 * i + 1 < 4096 := by omega
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reduceLeDiff, and_self, loadWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.load8, loOff, hiOff, a, b, lo, high,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      Ne.symm sep.2.2.2.2.1, sep.1]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, sep.1, ite_false, ite_true]
    rw [VG.Proof.Rc2.Arm.decode_word _ _ i hi]
    exact Word32.joinBytes_shift _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem loadWords_ok (is : List Nat) (hi : ∀ i ∈ is, i < 4) (s : State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block (is.flatMap loadWord)) s (fun s' =>
      (∀ i ∈ is, s'.gpr (wordReg i) =
        ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).getD i 0).setWidth 32) ∧
      VG.Proof.Rc2.Arm.Keep (is.map wordReg ++ ([.r12] : List Reg)) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.Arm.loadWord_ok s i (hi i (by simp)) fit readable
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have ptr₁ := keep₁.reg .r1 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Ne.symm (VG.Proof.Rc2.Arm.wordReg_separate i).2.2.2.2.1, by decide⟩)
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁
      (by rw [ptr₁]; exact fit) (by rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable))
    intro s₂ h₂
    constructor
    · intro j hj
      rw [List.mem_cons] at hj
      by_cases hm : j ∈ is
      · rw [h₂.1 j hm, keep₁.mem, ptr₁]
      · have he : j = i := hj.resolve_right hm
        subst j
        rw [h₂.2.reg _ (by
          simp only [List.mem_append, List.mem_singleton, not_or]
          refine ⟨?_, (VG.Proof.Rc2.Arm.wordReg_separate i).1⟩
          intro hm'
          obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
          have je := (VG.Proof.Rc2.Arm.wordReg_injective j (hi j (List.mem_cons_of_mem _ hj)) i (hi i (by simp))).mp he
          exact hm (je ▸ hj)), out₁]
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h
        · subst r; simp
        · subst r; simp
      · exact List.mem_cons_of_mem _ hr

theorem blockLoad_ok (s : State) (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block blockLoad) s (fun s' =>
      VG.Proof.Rc2.Arm.Words s' (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))) ∧
      VG.Proof.Rc2.Arm.Keep VG.Proof.Rc2.Arm.roundWrites s s') := by
  apply WP.mono (VG.Proof.Rc2.Arm.loadWords_ok (List.range 4) (fun i hi => List.mem_range.mp hi) s fit readable)
  intro s' h
  refine ⟨fun i hi => h.1 i (List.mem_range.mpr hi), h.2.weaken ?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, _, he⟩ := List.mem_map.mp hr
    subst r; exact VG.Proof.Rc2.Arm.wordReg_mem_roundWrites i
  · simp only [List.mem_singleton] at hr
    subst r; decide

end VG.Proof.Rc2.Arm

end

/-! # Writing the four RC2 words as little-endian bytes -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.WriteBytes VG.Proof.Rc2.Word32

theorem storeWord_ok (s : State) (i : Nat) (hi : i < 4) (v : BitVec 16)
    (value : s.gpr (wordReg i) = v.setWidth 32)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa (storeWord i) s = some s' ∧
      VG.Proof.Rc2.Arm.Keep [.r12] {s with
        mem := (s.mem.writeW (State.addr (s.gpr .r1) + BitVec.ofNat 64 (2 * i)) (v.setWidth 8)).writeW
          (State.addr (s.gpr .r1) + BitVec.ofNat 64 (2 * i + 1)) ((v >>> 8).setWidth 8)} s' := by
  have sep := VG.Proof.Rc2.Arm.wordReg_separate i
  have lo := writable (2 * i) (by omega)
  have high := writable (2 * i + 1) (by omega)
  have a := addr_add (a := s.gpr .r1) (k := 2 * i) (by omega)
  have b := addr_add (a := s.gpr .r1) (k := 2 * i + 1) (by omega)
  have loOff : 2 * i < 4096 := by omega
  have hiOff : 2 * i + 1 < 4096 := by omega
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, storeWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.store8, loOff, hiOff, a, b, lo, high,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    exact gpr_setReg_of_ne _ _ hr
  · rw [value]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    have byte : ((v.setWidth 32) >>> 8).setWidth 8 = (v >>> 8).setWidth 8 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj,
        show 8 + j < 32 by omega, decide_true, Bool.true_and]
    rw [byte]
  · rfl
  · rfl

theorem storeWords_ok (n : Nat) (hn : n ≤ 4) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block ((List.range n).flatMap storeWord)) s (fun s' =>
      VG.Proof.Rc2.Arm.Keep [.r12] {s with mem := writeBytes s.mem (State.addr (s.gpr .r1)) (outputBytes v n)} s') := by
  induction n generalizing s with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ _ => rfl, (writeBytes_nil s.mem (State.addr (s.gpr .r1))).symm, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    apply WP.mono (ih (by omega) s hv fit writable)
    intro s₁ keep₁
    have ptr₁ := keep₁.reg .r1 (by decide)
    have val₁ : s₁.gpr (wordReg n) = (v.getD n 0).setWidth 32 :=
      (keep₁.reg _ (by simpa using (VG.Proof.Rc2.Arm.wordReg_separate n).1)).trans (hv n (by omega))
    obtain ⟨s₂, run₂, keep₂⟩ := VG.Proof.Rc2.Arm.storeWord_ok s₁ n (by omega) _ val₁
      (by rw [ptr₁]; exact fit) (by rw [keep₁.wr, ptr₁]; exact writable)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    refine ⟨fun r hr => (keep₂.reg r hr).trans (keep₁.reg r hr), ?_,
      keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
    rw [keep₂.mem, keep₁.mem, ptr₁, outputBytes_write _ _ _ n (by omega)]

theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.Arm.Words s v)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block blockStore) s (fun s' =>
      VG.Proof.Rc2.Arm.Keep [.r12] {s with mem := s.mem.writeW (State.addr (s.gpr .r1)) (pack v)} s') := by
  apply WP.mono (VG.Proof.Rc2.Arm.storeWords_ok 4 (by decide) s v hv fit writable)
  intro s' h
  rw [outputBytes_pack] at h
  exact h

end VG.Proof.Rc2.Arm

end

section

namespace VG.Proof.Rc2.Arm

open VG VG.Arm

theorem exec_ldr (s : State) (t n : Reg) (off : Nat) (ho : off < 4096)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.ldr t n off) s =
      some (s.setReg t (s.mem.readW (State.addr (s.gpr n) + BitVec.ofNat 64 off) 32)) := by
  simp only [exec, ho, ite_true, State.load32, addr_add fit, h, Option.map_some]

theorem exec_str (s : State) (t n : Reg) (off : Nat) (ho : off < 4096)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions s.wr (State.addr (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.str t n off) s =
      some {s with mem := s.mem.writeW (State.addr (s.gpr n) + BitVec.ofNat 64 off) (s.gpr t)} := by
  simp only [exec, ho, ite_true, State.store32, addr_add fit, h]

end VG.Proof.Rc2.Arm

end

/-! # Where RC2 (and TDEA) save their callee-saved registers in scratch

The `i`th register of a list at byte `4 * i`; the saving and restoring are
`VG.Arm.Spill`'s. -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm

/-- Each register of `regs`, the `i`th at byte `4 * i`. -/
def slotsOf (regs : List Reg) : List (Reg × Nat) := regs.zipIdx.map fun (r, i) => (r, 4 * i)

end VG.Proof.Rc2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Lit`. -/
section

namespace VG.Impl.Rc2.Arm

open VG.Arm

/-- `piStep`, reading PITABLE from its packed table (`Rc2.piTable_getD`). -/
def piStepLit (i : Nat) : List Instr :=
  selectMask i ++
    ([imm .r10 (BitVec.ofNat 8 (VG.Rc2.piNat i)).toNat,
      .dp .and .r11 .r11 (.reg .r10), .dp .orr .r3 .r3 (.reg .r11)] : List Instr)

/-- `piLookup`, reading PITABLE from its packed table. -/
def piLookupLit : List Instr :=
  mask .r12 8 ++ [imm .r3 0] ++ (List.range 256).flatMap VG.Impl.Rc2.Arm.piStepLit ++ [rr .r12 .r3]

materialize_value VG.Impl.Rc2.Arm.piLookupLit

/-- The literal of `piLookup`, evaluated through the packed PITABLE. -/
noncomputable abbrev piLookup.lit : List Instr := piLookupLit.lit

theorem piLookup.lit_eq : piLookup = piLookup.lit := by
  have : piStep = VG.Impl.Rc2.Arm.piStepLit := by
    funext i; simp only [piStep, VG.Impl.Rc2.Arm.piStepLit, VG.Rc2.piTable_getD]
  refine Eq.trans ?_ piLookupLit.lit_eq
  simp only [piLookup, VG.Impl.Rc2.Arm.piLookupLit, this]

materialize_value keyLookup

materialize_code encryptBlock
materialize_code decryptBlock

materialize_code expandKey

end VG.Impl.Rc2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.ConstantTime`. -/
section

/-! # Constant-time RC2 block operations -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem encryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (VG.Proof.Rc2.Arm.PublicRegs [.r0, .r1, .r2]) encryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem decryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (VG.Proof.Rc2.Arm.PublicRegs [.r0, .r1, .r2]) decryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

end VG.Proof.Rc2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Block`. -/
section

/-! # Verified RC2 block encryption and decryption -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem blockSave_eq : blockSave = (VG.Proof.Rc2.Arm.slotsOf blockSaved).map (fun p => Instr.str p.1 .r2 p.2) := rfl

theorem blockRestore_eq : blockRestore = (VG.Proof.Rc2.Arm.slotsOf blockSaved).map (fun p => Instr.ldr p.1 .r2 p.2) := rfl

theorem blockSlots_ok : Spill.Slots 0 32 (VG.Proof.Rc2.Arm.slotsOf blockSaved) := by decide

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 256⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 256 ≤ 2 ^ 32
  post s s' := Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) =
    VG.Proof.Rc2.Arm.cipher d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))
  pub := VG.Proof.Rc2.Arm.PublicRegs [.r0, .r1, .r2]

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    VG.Proof.Rc2.Arm.cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => VG.Proof.Rc2.Arm.roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.Arm.blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (VG.Proof.Rc2.Arm.blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep, keyFit, dataFit, scratchFit⟩ := hs
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff, VG.Proof.Rc2.Arm.blockSave_eq]
  apply WP.mono (Spill.save_block_ok VG.Proof.Rc2.Arm.blockSlots_ok (by omega) fun d _ hd => by
    rw [hwr]; exact ⟨⟨State.addr (s.gpr .r2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
  intro s₁ h₁
  have scratchFrame : Frame [⟨State.addr (s.gpr .r2), 256⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2]
    exact Spill.saveMem_frame _ _ _ (by decide) _ (by decide)
  have input₁ : Spec.Rc2.blockAt s₁.mem (State.addr (s₁.gpr .r1)) = Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)) := by
    rw [h₁.1]
    exact blockAt_frame scratchFrame _ (by simpa using dataSep)
  have schedule₁ : Spec.Rc2.scheduleAt s₁.mem (State.addr (s₁.gpr .r0)) =
      Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
    rw [h₁.1]
    exact scheduleAt_frame scratchFrame _ (by simpa using keySep)
  have dataRead₁ : ∀ i < 8,
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r1) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.Arm.blockLoad_ok s₁ (by rw [h₁.1]; exact dataFit) dataRead₁)
  intro s₂ h₂
  have keyPtr₂ : s₂.gpr .r0 = s.gpr .r0 := (h₂.2.reg .r0 (by decide)).trans (congrFun h₁.1 .r0)
  have read₂ : ∀ i < 128, InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r0 + BitVec.ofNat 32 i)) 1 := by
    intro i hi
    rw [h₂.2.rd, h₂.2.wr, keyPtr₂, h₁.2.1, h₁.2.2.1, hrd, hwr, addr_add (by omega)]
    exact ⟨⟨State.addr (s.gpr .r0), 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.Arm.rounds_ok d s₂ _ h₂.1 (by rw [keyPtr₂]; exact keyFit) read₂)
  intro s₃ h₃
  have keep₂₃ := h₂.2.trans h₃.2
  have ptr₃ : s₃.gpr .r1 = s.gpr .r1 := (keep₂₃.reg .r1 (by decide)).trans (congrFun h₁.1 .r1)
  have writable₃ : ∀ i < 8, InRegions s₃.wr (State.addr (s₃.gpr .r1) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [keep₂₃.wr, h₁.2.2.1, hwr, ptr₃]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  let v := (List.range 16).foldl (fun v j => VG.Proof.Rc2.Arm.roundSpec d
    (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1))))
  have words₃ : VG.Proof.Rc2.Arm.Words s₃ v := by
    rw [h₂.2.mem, h₂.2.reg .r0 (by decide), schedule₁, input₁] at h₃
    exact h₃.1
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.Arm.blockStore_ok s₃ v words₃ (by rw [ptr₃]; exact dataFit) writable₃)
  intro s₄ h₄
  have mem₄ : s₄.mem = s₁.mem.writeW (State.addr (s.gpr .r1)) (pack v) := by rw [h₄.mem, keep₂₃.mem, ptr₃]
  have rd₄ : s₄.rd = s.rd := h₄.rd.trans (keep₂₃.rd.trans h₁.2.1)
  have wr₄ : s₄.wr = s.wr := h₄.wr.trans (keep₂₃.wr.trans h₁.2.2.1)
  have regs₄ (r : Reg) (hr : r ∉ VG.Proof.Rc2.Arm.roundWrites) : s₄.gpr r = s.gpr r := by
    rw [h₄.reg r (by
      simp only [List.mem_singleton]
      intro he; subst r; exact hr (by decide)), keep₂₃.reg r hr, h₁.1]
  have saved₄ : Spill.Saved s₄.mem (State.addr (s₄.gpr .r2)) s.gpr (VG.Proof.Rc2.Arm.slotsOf blockSaved) := by
    intro p hp
    have bound := blockSlots_ok.bound hp
    rw [mem₄, regs₄ .r2 (by decide), Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Region.contains_self _ _))
      (by decide), h₁.2.2.2]
    exact Spill.saveMem_saved _ _ _ _ VG.Proof.Rc2.Arm.blockSlots_ok p hp
  rw [VG.Proof.Rc2.Arm.blockRestore_eq]
  apply WP.mono (Spill.restore_block_ok VG.Proof.Rc2.Arm.blockSlots_ok (by decide) (by rw [regs₄ .r2 (by decide)]; omega)
    (fun d _ hd => by
      rw [rd₄, wr₄, regs₄ .r2 (by decide), hrd, hwr]
      exact ⟨⟨State.addr (s.gpr .r2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩) saved₄)
  intro s₅ h₅
  have finalMem : s₅.mem = s₁.mem.writeW (State.addr (s.gpr .r1)) (pack v) := h₅.2.2.1.trans mem₄
  constructor
  · intro r hr
    by_cases hm : r ∈ (VG.Proof.Rc2.Arm.slotsOf blockSaved).map Prod.fst
    · exact Spill.restored_reg h₅.1 hm
    · rw [h₅.2.1 _ hm]
      have covered : ∀ r ∈ preserved,
          r ∈ (VG.Proof.Rc2.Arm.slotsOf blockSaved).map Prod.fst ∨ r ∉ VG.Proof.Rc2.Arm.roundWrites := by decide
      exact regs₄ r ((covered r hr).resolve_left hm)
  · change Spec.Rc2.blockAt s₅.mem (State.addr (s.gpr .r1)) = _
    rw [finalMem, blockAt_write64, VG.Proof.Rc2.Arm.cipher_rounds]

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]

theorem encrypt_correct (s : State) (hs : (VG.Proof.Rc2.Arm.blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.Arm.blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.Arm.block_correct .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (VG.Proof.Rc2.Arm.blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.Arm.blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.Arm.block_correct .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem publicRegs_three (s₁ s₂ : State) : VG.Proof.Rc2.Arm.PublicRegs [.r0, .r1, .r2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 := by
  simp [VG.Proof.Rc2.Arm.PublicRegs]

theorem encrypt_verified :
    Verified target encryptBlock (Spec.Rc2.encryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.Rc2.Arm.encrypt_correct (VG.Proof.Rc2.Arm.encryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val,
    VG.Proof.Rc2.Arm.blockContract, VG.Proof.Rc2.Arm.publicRegs_three, VG.Proof.Rc2.Arm.cipher, State.addr] [satState] using VG.Proof.Rc2.Arm.satState

theorem decrypt_verified :
    Verified target decryptBlock (Spec.Rc2.decryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.Rc2.Arm.decrypt_correct (VG.Proof.Rc2.Arm.decryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val,
    VG.Proof.Rc2.Arm.blockContract, VG.Proof.Rc2.Arm.publicRegs_three, VG.Proof.Rc2.Arm.cipher, State.addr] [satState] using VG.Proof.Rc2.Arm.satState

end VG.Proof.Rc2.Arm

end
