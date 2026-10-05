import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Impl.Rc2.X86_64.Block
import VerifiedGarbage.Impl.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.Rc2.X86_64.Sse2Lookup
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Rc2.RestoreMemory
import VerifiedGarbage.Impl.Rc2.X86_64.Sse2KeyLookup
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Rc2.PiLit
import VerifiedGarbage.Impl.Rc2.X86_64.ExpandKey
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Lookup`. -/
section

/-! # Correctness of baseline x86-64 RC2 lookup steps -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

/-- A register-only block preserves memory, regions, and other GPRs. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem byte_imm (b : Byte) : (b.setWidth 32).signExtend 64 = b.setWidth 64 := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp
  · simp [BitVec.msb_setWidth]

theorem index_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 32 i).signExtend 64 = (BitVec.ofNat 8 i).setWidth 64 := by
  have h : BitVec.ofNat 32 i = (BitVec.ofNat 8 i).setWidth 32 := by bv_omega
  rw [h, byte_imm]

/-- SUB followed by SBB of a register from itself selects equality. -/
theorem borrowMask_eq (x y : BitVec 8) :
    (0 - (BitVec.ofBool ((x.setWidth 64 ^^^ y.setWidth 64).toNat < 1)).setWidth 64 : BitVec 64) =
      if x = y then BitVec.allOnes 64 else 0 := by
  have he : ((x.setWidth 64 ^^^ y.setWidth 64).toNat < 1) ↔ x = y := by
    rw [Nat.lt_one_iff]
    have hz : (x.setWidth 64 ^^^ y.setWidth 64).toNat = 0 ↔
        x.setWidth 64 ^^^ y.setWidth 64 = 0#64 := by
      constructor
      · intro h
        apply BitVec.eq_of_toNat_eq
        exact h
      · intro h; rw [h]; rfl
    rw [hz, BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have h' := congrArg (BitVec.setWidth 8) h
      simpa using h'
    · exact congrArg (BitVec.setWidth 64)
  by_cases h : x = y
  · rw [ite_eq_left h]
    have hb : decide ((x.setWidth 64 ^^^ y.setWidth 64).toNat < 1) = true := by
      exact decide_eq_true (he.mpr h)
    rw [hb]
    decide
  · rw [ite_eq_right h]
    have hb : decide ((x.setWidth 64 ^^^ y.setWidth 64).toNat < 1) = false := by
      exact decide_eq_false (mt he.mp h)
    rw [hb]
    decide

theorem piStep_ok (s : State) (x : Byte) (hx : s.gpr .rax = x.setWidth 64)
    (i : Nat) (hi : i < 256) :
    ∃ s', runBlock isa (piStep i) s = some s' ∧
      s'.gpr .rcx = s.gpr .rcx |||
        (if x.toNat = i then (Spec.Rc2.piTable.getD i 0).setWidth 64 else 0) ∧
      Keep [.rcx, .r10, .r11] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, BitVec.reduceSignExtend, piStep, selectMask, rr, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags,
      ]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    simp only [BitVec.sub_self]
    rw [hx, index_imm i hi, byte_imm]
    change s.gpr .rcx |||
      ((0 - (BitVec.ofBool ((x.setWidth 64 ^^^ (BitVec.ofNat 8 i).setWidth 64).toNat < 1)).setWidth 64) &&&
        (Spec.Rc2.piTable.getD i 0).setWidth 64) = _
    rw [borrowMask_eq]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.allOnes_and]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem piSteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 256)
    (s : State) (x : Byte) (hx : s.gpr .rax = x.setWidth 64) :
    WP isa (.block (is.flatMap piStep)) s (fun s' =>
      s'.gpr .rcx = s.gpr .rcx |||
        (if x.toNat ∈ is then (Spec.Rc2.piTable.getD x.toNat 0).setWidth 64 else 0) ∧
      Keep [.rcx, .r10, .r11] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := piStep_ok s x hx i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .rax (by decide)).trans hx
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ hx₁)
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁]
    by_cases h : x.toNat = i
    · subst i
      by_cases hm : x.toNat ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x.toNat ∈ is <;> simp [h, hm]

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem piStart_ok (s : State) :
    ∃ s', runBlock isa [.alu .and .rax (.imm 255), imm .rcx 0] s = some s' ∧
      s'.gpr .rax = ((s.gpr .rax).setWidth 8).setWidth 64 ∧ s'.gpr .rcx = 0 ∧
      Keep [.rax, .rcx, .r10, .r11] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact maskByte _
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _

theorem piLookup_ok (s : State) :
    WP isa (.block piLookup) s (fun s' =>
      s'.gpr .rax = (Spec.Rc2.pi ((s.gpr .rax).setWidth 8)).setWidth 64 ∧
      Keep [.rax, .rcx, .r10, .r11] s s') := by
  rw [piLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := piStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piSteps_ok (List.range 256) (fun i hi => List.mem_range.mp hi)
    s₁ ((s.gpr .rax).setWidth 8) input₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .rcx = (Spec.Rc2.pi ((s.gpr .rax).setWidth 8)).setWidth 64 := by
    rw [h₂.1, zero₁]
    simp only [List.mem_range]
    rw [ite_eq_left ((s.gpr .rax).setWidth 8).isLt]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .rax (s₂.gpr .rcx), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.rax, .rcx, .r10, .r11] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (Int.ofNat i) = BitVec.ofNat 64 i := by
  rfl

theorem keyStep_ok (s : State) (x : Byte) (hx : s.gpr .rax = x.setWidth 64)
    (i : Nat) (hi : i < 64)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (2 * i + 1)) 1) :
    ∃ s', runBlock isa (keyStep i) s = some s' ∧
      s'.gpr .rcx = s.gpr .rcx |||
        (if x.toNat = i then
          ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
            (s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8).setWidth 64
          else 0) ∧
      Keep [.rcx, .r8, .r9, .r10, .r11] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, BitVec.reduceSignExtend, keyStep, selectMask, loadKey, rr, memOp,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, State.load8, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags, gpr_setFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
      wr_setReg, wr_arithFlags, hlo, hhi]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    simp only [BitVec.sub_self]
    rw [hx, index_imm i (by omega)]
    change s.gpr .rcx |||
      (((s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * i))).setWidth 64 |||
        ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * i + 1))).setWidth 64).rotateRight 56) &&&
        (0 - (BitVec.ofBool ((x.setWidth 64 ^^^ (BitVec.ofNat 8 i).setWidth 64).toNat < 1)).setWidth 64)) = _
    rw [borrowMask_eq, joinBytes]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.and_allOnes]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem keySteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 64)
    (s : State) (x : Byte) (hx : s.gpr .rax = x.setWidth 64)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1) :
    WP isa (.block (is.flatMap keyStep)) s (fun s' =>
      s'.gpr .rcx = s.gpr .rcx |||
        (if x.toNat ∈ is then
          ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * x.toNat))).setWidth 16 |||
            (s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * x.toNat + 1))).setWidth 16 <<< 8).setWidth 64
          else 0) ∧ Keep [.rcx, .r8, .r9, .r10, .r11] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have bound := hi i (by simp)
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := keyStep_ok s x hx i bound
      (readable (2 * i) (by omega)) (readable (2 * i + 1) (by omega))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .rax (by decide)).trans hx
    have ptr₁ := keep₁.reg .rdi (by decide)
    have read₁ : ∀ j < 128,
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 j) 1 := by
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

theorem maskIndex (x : BitVec 64) :
    x &&& 63 = (x.setWidth 6).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 6 - 1) = x.toNat % 64 % 18446744073709551616
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem keyStart_ok (s : State) :
    ∃ s', runBlock isa [.alu .and .rax (.imm 63), imm .rcx 0] s = some s' ∧
      s'.gpr .rax = ((s.gpr .rax).setWidth 6).setWidth 64 ∧ s'.gpr .rcx = 0 ∧
      Keep [.rax, .rcx, .r8, .r9, .r10, .r11] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact maskIndex _
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _

theorem scheduleAt_getD (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    (Spec.Rc2.scheduleAt m p).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.scheduleAt, Vector.getD, hi]

theorem keyLookup_ok (s : State)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1) :
    WP isa (.block keyLookup) s (fun s' =>
      s'.gpr .rax = ((Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD
        ((s.gpr .rax).setWidth 6).toNat 0).setWidth 64 ∧
      Keep [.rax, .rcx, .r8, .r9, .r10, .r11] s s') := by
  rw [keyLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := keyStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ := keep₁.reg .rdi (by decide)
  have read₁ : ∀ i < 128,
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]
    exact readable
  have inputByte : s₁.gpr .rax = (((s.gpr .rax).setWidth 6).setWidth 8).setWidth 64 := by
    rw [input₁]; simp
  apply WP.mono (keySteps_ok (List.range 64) (fun i hi => List.mem_range.mp hi)
    s₁ (((s.gpr .rax).setWidth 6).setWidth 8) inputByte read₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .rcx = ((Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD
      ((s.gpr .rax).setWidth 6).toNat 0).setWidth 64 := by
    rw [h₂.1, zero₁, keep₁.mem, ptr₁]
    simp only [List.mem_range, BitVec.toNat_setWidth]
    have bound := ((s.gpr .rax).setWidth 6).isLt
    simp only [BitVec.toNat_setWidth] at bound
    rw [Nat.mod_eq_of_lt (show (s.gpr .rax).toNat % 64 < 256 by omega),
      ite_eq_left bound, scheduleAt_getD _ _ _ bound]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .rax (s₂.gpr .rcx), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.rax, .rcx, .r8, .r9, .r10, .r11] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _

end VG.Proof.Rc2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Sse2Vector`. -/
section

section

section

/-! # Word-sized equality masks for SSE2 RC2 scans -/

namespace VG.Proof.Rc2.X86_64.Sse2

private theorem shift_mask (v : BitVec 16) (hb : v.toNat < 256)
    (hn : v.toNat ≠ 0) : (v - 1).sshiftRight 15 = 0 := by
  have hv : (v - 1).toNat = v.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by bv_omega)]
    rfl
  have hs : (v - 1).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hv]
    omega
  rw [BitVec.sshiftRight_eq_of_msb_false hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, hv]
  rw [Nat.shiftRight_eq_div_pow, show (0 : BitVec 16).toNat = 0 by decide]
  change (v.toNat - 1) / 32768 = 0
  omega

theorem mask_eq (x y : VG.Byte) :
    ((x.setWidth 16 ^^^ y.setWidth 16) - 1).sshiftRight 15 =
      if x = y then BitVec.allOnes 16 else 0 := by
  have hb : (x.setWidth 16 ^^^ y.setWidth 16).toNat < 256 := by
    rw [← BitVec.setWidth_xor]
    simp only [BitVec.toNat_setWidth]
    have h := (x ^^^ y).isLt
    omega
  by_cases h : x = y
  · subst y
    rw [BitVec.xor_self, ite_eq_left rfl]
    decide
  · have hn : x.setWidth 16 ^^^ y.setWidth 16 ≠ 0#16 := by
      intro hz
      have he := BitVec.xor_eq_zero_iff.mp hz
      have he' := congrArg (BitVec.setWidth 8) he
      exact h (by simpa using he')
    have hn' : (x.setWidth 16 ^^^ y.setWidth 16).toNat ≠ 0 := by
      intro hz
      exact hn (BitVec.eq_of_toNat_eq hz)
    rw [ite_eq_right h]
    exact shift_mask _ hb hn'

end VG.Proof.Rc2.X86_64.Sse2

end

/-! # Register-only SSE2 RC2 lookup steps -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd

structure KeepX (regs : List Reg) (xregs : List XReg) (s s' : State) : Prop where
  keep : Keep regs s s'
  xmm : ∀ r, r ∉ xregs → s'.xmm r = s.xmm r

theorem KeepX.trans {rs : List Reg} {xs : List XReg} {s s' s'' : State}
    (h : KeepX rs xs s s') (h' : KeepX rs xs s' s'') : KeepX rs xs s s'' :=
  ⟨h.keep.trans h'.keep, fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

theorem loadConst_ok (s : State) (dst : XReg) (hd : dst ≠ .xmm5) (v : BitVec 128) :
    ∃ s', runBlock isa (Impl.Rc2.X86_64.Sse2.loadConst dst v) s = some s' ∧
      s'.xmm dst = v ∧ KeepX [.r10] [dst, .xmm5] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.X86_64.Sse2.loadConst, runBlock_cons, runStep_some,
      runBlock_nil, exec, XOp.exec, gpr_setReg,
      gpr_setXmm, xmm_setReg, xmm_setXmm_self, xmm_setXmm_of_ne _ _ hd]
    rfl, ?_⟩
  constructor
  · simp only [xmm_setXmm_self]
    exact movq_const v
  · constructor
    · constructor
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [gpr_setXmm, gpr_setReg_of_ne _ _ hr]
      · simp only [mem_setXmm, mem_setReg]
      · simp only [rd_setXmm, rd_setReg]
      · simp only [wr_setXmm, wr_setReg]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2, xmm_setReg]

def selectValue (a b c v : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pand
    (XShiftOp.eval .psraw (XBinOp.eval .psubw (a ^^^ b) c) 15) v

theorem select_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Sse2.select s = some s' ∧
      s'.xmm .xmm1 = s.xmm .xmm1 |||
        selectValue (s.xmm .xmm0) (s.xmm .xmm2) (s.xmm .xmm6) (s.xmm .xmm4) ∧
      s'.xmm .xmm2 = XBinOp.eval .paddw (s.xmm .xmm2) (s.xmm .xmm7) ∧
      KeepX [] [.xmm3, .xmm1, .xmm2] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, not_false_eq_true, Impl.Rc2.X86_64.Sse2.select,
      runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
      xmm_setXmm_self, xmm_setXmm_of_ne]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [reduceCtorEq, not_false_eq_true, selectValue, xmm_setXmm_self,
      xmm_setXmm_of_ne, XBinOp.eval]
  · exact xmm_setXmm_self _ _ _
  · constructor
    · constructor
      · intro r _; simp only [gpr_setXmm]
      · simp only [mem_setXmm]
      · simp only [rd_setXmm]
      · simp only [wr_setXmm]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2.1,
        xmm_setXmm_of_ne _ _ hr.2.2]

theorem selectValue_word (a b v : BitVec 128) (x y : Byte) (i : Nat) (hi : i < 8)
    (ha : word a i = x.setWidth 16) (hb : word b i = y.setWidth 16) :
    word (selectValue a b Impl.Rc2.X86_64.Sse2.ones v) i =
      if x = y then word v i else 0 := by
  rw [selectValue, word_pand, word_psraw _ _ hi, word_psubw _ _ hi]
  rw [show (15 : BitVec 8).toNat = 15 by decide, Nat.min_eq_left (by decide)]
  rw [show word (a ^^^ b) i = word a i ^^^ word b i from word_pxor a b]
  rw [Impl.Rc2.X86_64.Sse2.ones, word_ofWords _ hi, ha, hb, mask_eq]
  by_cases h : x = y
  · rw [ite_eq_left h, ite_eq_left h, BitVec.allOnes_and]
  · rw [ite_eq_right h, ite_eq_right h]
    change 0#16 &&& word v i = 0#16
    exact BitVec.zero_and

end VG.Proof.Rc2.X86_64.Sse2

end

/-! # Word-wise SSE2 lookup invariants -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64

theorem word_por (a b : BitVec 128) (i : Nat) :
    word (a ||| b) i = word a i ||| word b i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_or, decide_eq_true hj, Bool.true_and]

def broadcast (x : Byte) : BitVec 128 := ofWords fun _ => x.setWidth 16

theorem broadcast_word (x : Byte) (i : Nat) (hi : i < 8) :
    word (shufDwords (XBinOp.eval .punpcklwd
      (0#64 ++ x.setWidth 64) (0#64 ++ x.setWidth 64)) 0) i = x.setWidth 16 := by
  have hd : dword (XBinOp.eval .punpcklwd
      (0#64 ++ x.setWidth 64) (0#64 ++ x.setWidth 64)) 0 =
      x.setWidth 16 ++ x.setWidth 16 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [dword, XBinOp.eval, ofWords, word, BitVec.getLsbD_extractLsb',
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
      Nat.zero_add, ite_true, ite_false, decide_eq_true hj, Bool.true_and]
    repeat rw [BitVec.getLsbD_append]
    by_cases h : j < 16 <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, BitVec.getLsbD_extractLsb',
        Nat.zero_add, decide_eq_true, Bool.true_and]
    all_goals rw [BitVec.getLsbD_append]
    all_goals simp (disch := omega) only [ite_eq_left, BitVec.getLsbD_setWidth,
      decide_eq_true, Bool.true_and]
  rw [shufDwords]
  change word (ofDwords
    (dword _ 0) (dword _ 0) (dword _ 0) (dword _ 0)) i = _
  rw [hd]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [word_eq_dword _ hi] <;>
    simp (disch := decide) only [Nat.reduceDiv, Nat.reduceMod,
      dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      Nat.reduceMul, Nat.reduceSub, BitVec.extractLsb'_append_eq_of_add_le,
      BitVec.extractLsb'_append_eq_of_le, BitVec.extractLsb'_eq_self]


def acc (f : Nat → BitVec 16) (x n : Nat) : BitVec 128 :=
  ofWords fun j => if x < 8 * n ∧ x % 8 = j then f x else 0#16

theorem acc_zero (f : Nat → BitVec 16) (x : Nat) : acc f x 0 = 0#128 := by
  apply ext_word
  intro j hj
  rw [acc, word_ofWords _ hj]
  simp [word]

theorem indices_next (n : Nat) :
    XBinOp.eval .paddw (Impl.Rc2.X86_64.Sse2.indices n)
      Impl.Rc2.X86_64.Sse2.eights = Impl.Rc2.X86_64.Sse2.indices (n + 1) := by
  apply ext_word
  intro j hj
  rw [word_paddw _ _ hj]
  simp only [Impl.Rc2.X86_64.Sse2.indices, Impl.Rc2.X86_64.Sse2.eights, word_ofWords _ hj]
  change BitVec.ofNat 16 (8 * n + j) + BitVec.ofNat 16 8 = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem acc_step (f : Nat → BitVec 16) (x : Byte) (n : Nat) (hn : n < 32)
    (v : BitVec 128) (hv : ∀ j < 8, word v j = f (8 * n + j)) :
    acc f x.toNat n ||| selectValue (broadcast x)
      (Impl.Rc2.X86_64.Sse2.indices n) Impl.Rc2.X86_64.Sse2.ones v =
    acc f x.toNat (n + 1) := by
  apply ext_word
  intro j hj
  rw [word_por, selectValue_word _ _ _ x (BitVec.ofNat 8 (8 * n + j)) j hj
    (word_ofWords _ hj) (by
      rw [Impl.Rc2.X86_64.Sse2.indices, word_ofWords _ hj]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega)]
  simp only [acc, word_ofWords _ hj, hv j hj]
  have he : (x = BitVec.ofNat 8 (8 * n + j)) ↔ x.toNat = 8 * n + j := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases h : x.toNat = 8 * n + j
  · rw [ite_eq_left (he.mpr h), ite_eq_right (by omega), ite_eq_left (by omega), h]
    exact BitVec.zero_or
  · rw [ite_eq_right (mt he.mp h)]
    change (if x.toNat < 8 * n ∧ x.toNat % 8 = j then f x.toNat else 0#16) ||| 0#16 = _
    rw [BitVec.or_zero]
    have heq : (x.toNat < 8 * n ∧ x.toNat % 8 = j) ↔
        (x.toNat < 8 * (n + 1) ∧ x.toNat % 8 = j) := by omega
    simp only [heq]

def reduceValue (v : BitVec 128) : BitVec 128 :=
  let a := v ||| (v >>> 64)
  let b := a ||| (a >>> 32)
  b ||| (b >>> 16)

theorem reduceValue_word (v : BitVec 128) :
    word (reduceValue v) 0 =
      word v 0 ||| word v 1 ||| word v 2 ||| word v 3 |||
      word v 4 ||| word v 5 ||| word v 6 ||| word v 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [reduceValue, getLsbD_word, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    decide_eq_true hj, Bool.true_and, Nat.mul_zero, Nat.zero_add]
  simp only [Nat.reduceMul]
  simp only [Nat.add_assoc, Nat.add_comm, Bool.or_comm, Bool.or_left_comm]

theorem reduce_acc (f : Nat → BitVec 16) (x n : Nat) :
    word (reduceValue (acc f x n)) 0 = if x < 8 * n then f x else 0#16 := by
  rw [reduceValue_word]
  simp only [acc, word_ofWords _ (by decide : 0 < 8), word_ofWords _ (by decide : 1 < 8),
    word_ofWords _ (by decide : 2 < 8), word_ofWords _ (by decide : 3 < 8),
    word_ofWords _ (by decide : 4 < 8), word_ofWords _ (by decide : 5 < 8),
    word_ofWords _ (by decide : 6 < 8), word_ofWords _ (by decide : 7 < 8)]
  by_cases h : x < 8 * n
  · rw [ite_eq_left h]
    rcases (by omega : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
      x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7) with
      hm | hm | hm | hm | hm | hm | hm | hm <;>
      simp only [h, hm, Nat.reduceEqDiff, ite_true, ite_false, true_and, and_false,
        BitVec.or_zero, BitVec.zero_or]
  · simp only [h, false_and, ite_false, BitVec.or_zero]


end VG.Proof.Rc2.X86_64.Sse2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Block`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish`. -/
section

/-! # Reducing a scan and restoring its temporary memory -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem reduceOr_ok (s : State) :
    ∃ s', runBlock isa Sse2.reduceOr s = some s' ∧
      s'.xmm .xmm1 = reduceValue (s.xmm .xmm1) ∧
      KeepX [] [.xmm1, .xmm3] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, not_false_eq_true, Sse2.reduceOr, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne]
    rfl, ?_⟩
  constructor
  · simp only [xmm_setXmm_self,
      XBinOp.eval, XShiftOp.eval]
    rfl
  · constructor
    · constructor
      · intro r _; simp only [gpr_setXmm]
      · simp only [mem_setXmm]
      · simp only [rd_setXmm]
      · simp only [wr_setXmm]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2]

theorem read64_word (m : Mem) (p : Addr) :
    (m.readW p 64).setWidth 16 = m.readW p 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true hj, decide_eq_true (by omega : j < 64), Bool.true_and]
  rw [VG.X86_64.getLsbD_read _ _ (by omega), VG.X86_64.getLsbD_read _ _ (by omega)]

theorem stored_word (m : Mem) (p : Addr) (v : BitVec 128) :
    (m.writeW p v).readW p 64 &&& 65535 = (word v 0).setWidth 64 := by
  rw [maskWord, VG.Proof.Rc2.X86_64.Sse2.read64_word]
  have he := readW_writeW128_16 m p v (j := 0) (by decide)
  change (m.writeW p v).readW (p + 0#64) 16 = word v 0 at he
  rw [BitVec.add_zero] at he
  rw [he]

theorem finishTail_ok (s : State) (scratch : Reg) (hs : scratch ≠ .rax)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr scratch + BitVec.ofNat 64 64) 8)
    (hwrite : InRegions s.wr (s.gpr scratch + BitVec.ofNat 64 64) 16)
    (hrestore : s.xmm .xmm8 = s.mem.readW (s.gpr scratch + BitVec.ofNat 64 64) 128) :
    ∃ s', runBlock isa
      [.movdquStore (memOp scratch 64) .xmm1, .mov .rax (.mem (memOp scratch 64)),
       .alu .and .rax (.imm 65535), .movdquStore (memOp scratch 64) .xmm8] s = some s' ∧
      s'.gpr .rax = (word (s.xmm .xmm1) 0).setWidth 64 ∧ Keep [.rax] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc,
      State.store128, State.load64, State.ea, memOp, offset_nat, gpr_setReg_of_ne _ _ hs,
      gpr_arithFlags, gpr_setReg_self, xmm_setReg, xmm_arithFlags,
      wr_setReg, wr_arithFlags, hread, hwrite, ite_true, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
    change (s.mem.writeW _ (s.xmm .xmm1)).readW _ 64 &&&
      (65535#32).signExtend 64 = _
    rw [show (65535#32).signExtend 64 = (65535 : BitVec 64) by decide]
    exact VG.Proof.Rc2.X86_64.Sse2.stored_word _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [gpr_setReg_of_ne _ _ hr, gpr_arithFlags]
    · simp only [mem_setReg, mem_arithFlags, hrestore]
      exact restore128 _ _ _
    · simp only [rd_setReg, rd_arithFlags]
    · rfl


end VG.Proof.Rc2.X86_64.Sse2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Save`. -/
section

section

section

section

section

/-! # Initialization of SSE2 RC2 schedule lookup state -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem keyStart_ok (s : State) (scratch : Reg)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr scratch + BitVec.ofNat 64 64) 16) :
    ∃ s', runBlock isa (Sse2.start scratch 63) s = some s' ∧
      s'.xmm .xmm0 = broadcast (((s.gpr .rax).setWidth 6).setWidth 8) ∧
      s'.xmm .xmm1 = 0#128 ∧ s'.xmm .xmm2 = Sse2.indices 0 ∧
      s'.xmm .xmm6 = Sse2.ones ∧ s'.xmm .xmm7 = Sse2.eights ∧
      s'.xmm .xmm8 = s.mem.readW (s.gpr scratch + BitVec.ofNat 64 64) 128 ∧
      Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Sse2.start, Sse2.loadConst,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc, XOp.exec,
      State.load128, State.ea, memOp, offset_nat, hread, ite_true, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_setXmm, gpr_arithFlags,
      xmm_setReg, xmm_setXmm_self, xmm_setXmm_of_ne]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg]
    rw [show (63#32).signExtend 64 = (63 : BitVec 64) by decide, maskIndex]
    apply ext_word
    intro i hi
    rw [broadcast, word_ofWords _ hi]
    simpa using broadcast_word (((s.gpr .rax).setWidth 6).setWidth 8) i hi
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg,
      XBinOp.eval, BitVec.xor_self]
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg]
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg]
  · simp only [xmm_setXmm_self]
    exact movq_const _
  · simp (config := {decide := true}) only [xmm_setXmm_of_ne, xmm_setReg,
      xmm_arithFlags, xmm_setXmm_self]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setXmm, gpr_setReg_of_ne _ _ hr.1, gpr_setReg_of_ne _ _ hr.2, gpr_arithFlags]
    · simp only [mem_setXmm, mem_setReg, mem_arithFlags]
    · simp only [rd_setXmm, rd_setReg, rd_arithFlags]
    · simp only [wr_setXmm, wr_setReg, wr_arithFlags]

end VG.Proof.Rc2.X86_64.Sse2

end

/-! # Composing eight-candidate schedule scans -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

structure KeyScanInv (f : Nat → BitVec 16) (x : Byte) (n : Nat) (s : State) : Prop where
  input : s.xmm .xmm0 = broadcast x
  acc : s.xmm .xmm1 = Sse2.acc f x.toNat n
  indices : s.xmm .xmm2 = Impl.Rc2.X86_64.Sse2.indices n
  ones : s.xmm .xmm6 = Impl.Rc2.X86_64.Sse2.ones
  eights : s.xmm .xmm7 = Impl.Rc2.X86_64.Sse2.eights

theorem keyLoad_ok (s : State) (n : Nat)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * n)) 16) :
    ∃ s', runBlock isa [.movdquLoad .xmm4 (memOp .rdi (16 * n))] s = some s' ∧
      s'.xmm .xmm4 = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * n)) 128 ∧
      KeepX [] [.xmm4] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128,
      State.ea, memOp, offset_nat, hread, ite_true, Option.map_some]
    rfl, ?_⟩
  constructor
  · exact xmm_setXmm_self _ _ _
  · constructor
    · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      exact xmm_setXmm_of_ne _ _ hr

theorem keyStep_ok (s : State) (f : Nat → BitVec 16) (x : Byte) (n : Nat) (hn : n < 8)
    (hinv : VG.Proof.Rc2.X86_64.Sse2.KeyScanInv f x n s)
    (hf : ∀ i < 64, f i = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * n)) 16) :
    WP isa (.block (Impl.Rc2.X86_64.Sse2.keyStep n)) s (fun s' =>
      VG.Proof.Rc2.X86_64.Sse2.KeyScanInv f x (n + 1) s' ∧ Keep [] s s' ∧ s'.xmm .xmm8 = s.xmm .xmm8) := by
  rw [Impl.Rc2.X86_64.Sse2.keyStep, WP.block_append_iff]
  obtain ⟨s₁, run₁, val₁, keep₁⟩ := VG.Proof.Rc2.X86_64.Sse2.keyLoad_ok s n hread
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, val₂, idx₂, keep₂⟩ := select_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine ⟨?_, keep₁.keep.trans keep₂.keep, ?_⟩
  · constructor
    · rw [keep₂.xmm .xmm0 (by decide), keep₁.xmm .xmm0 (by decide)]
      exact hinv.input
    · rw [val₂, keep₁.xmm .xmm1 (by decide), keep₁.xmm .xmm0 (by decide),
        keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm6 (by decide), val₁,
        hinv.acc, hinv.input, hinv.indices, hinv.ones]
      apply acc_step f x n (by omega)
      intro j hj
      rw [word_readW _ _ hj, hf (8 * n + j) (by omega)]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (fun d => s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 d) 16) (by omega)
    · rw [idx₂, keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm7 (by decide),
        hinv.indices, hinv.eights]
      exact indices_next n
    · rw [keep₂.xmm .xmm6 (by decide), keep₁.xmm .xmm6 (by decide)]
      exact hinv.ones
    · rw [keep₂.xmm .xmm7 (by decide), keep₁.xmm .xmm7 (by decide)]
      exact hinv.eights
  · rw [keep₂.xmm .xmm8 (by decide), keep₁.xmm .xmm8 (by decide)]

theorem keySteps_ok (count n : Nat) (hbound : n + count ≤ 8)
    (s : State) (f : Nat → BitVec 16) (x : Byte) (hinv : VG.Proof.Rc2.X86_64.Sse2.KeyScanInv f x n s)
    (hf : ∀ i < 64, f i = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16)
    (hread : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block ((List.range' n count).flatMap Impl.Rc2.X86_64.Sse2.keyStep)) s
      (fun s' => VG.Proof.Rc2.X86_64.Sse2.KeyScanInv f x (n + count) s' ∧ Keep [] s s' ∧
        s'.xmm .xmm8 = s.xmm .xmm8) := by
  induction count generalizing n s with
  | zero =>
    apply WP.block_nil
    exact ⟨hinv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl⟩
  | succ count ih =>
    rw [List.range'_succ, List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (VG.Proof.Rc2.X86_64.Sse2.keyStep_ok s f x n (by omega) hinv hf (hread n (by omega)))
    intro s₁ h₁
    have hf₁ : ∀ i < 64, f i = s₁.mem.readW (s₁.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16 := by
      rw [h₁.2.1.mem, h₁.2.1.reg .rdi (by simp)]; exact hf
    have hr₁ : ∀ i < 8, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16 := by
      rw [h₁.2.1.rd, h₁.2.1.wr, h₁.2.1.reg .rdi (by simp)]; exact hread
    apply WP.mono (ih (n + 1) (by omega) s₁ h₁.1 hf₁ hr₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.1.trans h₂.2.1, h₂.2.2.trans h₁.2.2⟩
    have he : n + 1 + count = n + (count + 1) := by omega
    exact he ▸ h₂.1

end VG.Proof.Rc2.X86_64.Sse2

end

/-! # Verified constant-time SSE2 schedule lookup -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem schedule_readWord (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    m.readW (p + BitVec.ofNat 64 (2 * i)) 16 = (Spec.Rc2.scheduleAt m p).getD i 0 := by
  rw [scheduleAt_getD _ _ _ hi]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Mem.readW, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, decide_eq_true hj, Bool.true_and]
  rw [VG.X86_64.getLsbD_read _ _ (by omega)]
  by_cases h : j < 8
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, Bool.or_false,
      Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, BitVec.add_zero]
  · have hj' : j - 8 < 8 := by omega
    simp only [h, decide_false, Bool.not_false]
    have hdiv : j / 8 = 1 := by omega
    have hmod : j % 8 = j - 8 := by omega
    rw [hdiv, hmod]
    have hp : p + BitVec.ofNat 64 (2 * i) + BitVec.ofNat 64 1 =
        p + BitVec.ofNat 64 (2 * i + 1) := by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [hp]
    simp (disch := omega) only [BitVec.getLsbD_of_ge, decide_eq_true,
      Bool.true_and, Bool.false_or]

theorem keyLookup_ok (s : State)
    (hread : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16)
    (hwrite : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 64) 16) :
    WP isa (.block Impl.Rc2.X86_64.Sse2.keyLookup) s (fun s' =>
      s'.gpr .rax = ((Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD
        ((s.gpr .rax).setWidth 6).toNat 0).setWidth 64 ∧
      Keep [.rax, .rcx, .r8, .r9, .r10, .r11] s s') := by
  have hsread : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 64) 16 := by
    obtain ⟨r, hr, hc⟩ := hwrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [Impl.Rc2.X86_64.Sse2.keyLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, idx₁, ones₁, eights₁, saved₁, keep₁⟩ := VG.Proof.Rc2.X86_64.Sse2.keyStart_ok s .rdx hsread
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff, List.range_eq_range']
  let x : Byte := ((s.gpr .rax).setWidth 6).setWidth 8
  let f (i : Nat) := s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16
  have inv₁ : VG.Proof.Rc2.X86_64.Sse2.KeyScanInv f x 0 s₁ :=
    ⟨input₁, zero₁.trans (acc_zero _ _).symm, idx₁, ones₁, eights₁⟩
  have hf₁ : ∀ i < 64, f i = s₁.mem.readW (s₁.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16 := by
    rw [keep₁.mem, keep₁.reg .rdi (by decide)]
    intro _ _; rfl
  have hr₁ : ∀ i < 8, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [keep₁.rd, keep₁.wr, keep₁.reg .rdi (by decide)]; exact hread
  apply WP.mono (VG.Proof.Rc2.X86_64.Sse2.keySteps_ok 8 0 (by decide) s₁ f x inv₁ hf₁ hr₁)
  intro s₂ h₂
  rw [Impl.Rc2.X86_64.Sse2.finish, WP.block_append_iff]
  obtain ⟨s₃, run₃, reduced₃, keep₃⟩ := VG.Proof.Rc2.X86_64.Sse2.reduceOr_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep₂ : Keep [.rax, .r10] s₁ s₂ := h₂.2.1.weaken (by simp)
  have keep₃' : Keep [.rax, .r10] s₂ s₃ := keep₃.keep.weaken (by simp)
  have kept : Keep [.rax, .r10] s s₃ := (keep₁.trans keep₂).trans keep₃'
  have ptr : s₃.gpr .rdx = s.gpr .rdx := kept.reg .rdx (by decide)
  have wr₃ : InRegions s₃.wr (s₃.gpr .rdx + BitVec.ofNat 64 64) 16 := by
    rw [kept.wr, ptr]; exact hwrite
  have rd₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .rdx + BitVec.ofNat 64 64) 8 := by
    rw [kept.rd, kept.wr, ptr]
    obtain ⟨r, hr, hc⟩ := hsread
    exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega⟩
  have saved₃ : s₃.xmm .xmm8 = s₃.mem.readW (s₃.gpr .rdx + BitVec.ofNat 64 64) 128 := by
    rw [keep₃.xmm .xmm8 (by decide), h₂.2.2, saved₁, kept.mem, ptr]
  obtain ⟨s₄, run₄, out₄, keep₄⟩ := VG.Proof.Rc2.X86_64.Sse2.finishTail_ok s₃ .rdx (by decide) rd₃ wr₃ saved₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · have xb : x.toNat < 64 := by
      simp only [x, BitVec.toNat_setWidth]
      have h := ((s.gpr .rax).setWidth 6).isLt
      simp only [BitVec.toNat_setWidth] at h
      omega
    have xe : x.toNat = ((s.gpr .rax).setWidth 6).toNat := by
      simp only [x, BitVec.toNat_setWidth]
      have h := ((s.gpr .rax).setWidth 6).isLt
      simp only [BitVec.toNat_setWidth] at h
      omega
    rw [out₄, reduced₃, h₂.1.acc, reduce_acc, ite_eq_left xb]
    dsimp only [f]
    rw [VG.Proof.Rc2.X86_64.Sse2.schedule_readWord _ _ _ xb, xe]
  · exact (kept.trans (keep₄.weaken (by simp))).weaken (by simp)

end VG.Proof.Rc2.X86_64.Sse2

end

section

/-! # Existing contract permissions used by vector schedule scans -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64

structure ScanMemory (s : State) : Prop where
  bytes : ∀ i < 128, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1
  vectors : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16
  scratch : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 64) 16

instance (s : State) : CoeFun (VG.Proof.Rc2.X86_64.ScanMemory s)
    (fun _ => ∀ i, i < 128 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1) where
  coe := fun h => h.bytes

theorem ScanMemory.keep {s s' : State} {rs : List Reg} (h : VG.Proof.Rc2.X86_64.ScanMemory s)
    (keep : Keep rs s s') (hk : .rdi ∉ rs) (hs : .rdx ∉ rs) : VG.Proof.Rc2.X86_64.ScanMemory s' := by
  constructor
  · rw [keep.rd, keep.wr, keep.reg .rdi hk]
    exact h.bytes
  · rw [keep.rd, keep.wr, keep.reg .rdi hk]
    exact h.vectors
  · rw [keep.wr, keep.reg .rdx hs]
    exact h.scratch

end VG.Proof.Rc2.X86_64

end

/-! # RC2 mixing and mashing in x86-64 registers -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

/-- State words never alias the temporaries or argument registers. -/
theorem wordReg_separate (i : Nat) :
    wordReg i ≠ .rax ∧ wordReg i ≠ .rcx ∧ wordReg i ≠ .rdx ∧ wordReg i ≠ .rdi ∧
    wordReg i ≠ .rsi ∧ wordReg i ≠ .r8 ∧ wordReg i ≠ .r9 ∧
    wordReg i ≠ .r10 ∧ wordReg i ≠ .r11 := by
  have h : ∀ j < 4,
      wordReg j ≠ .rax ∧ wordReg j ≠ .rcx ∧ wordReg j ≠ .rdx ∧ wordReg j ≠ .rdi ∧
      wordReg j ≠ .rsi ∧ wordReg j ≠ .r8 ∧ wordReg j ≠ .r9 ∧
      wordReg j ≠ .r10 ∧ wordReg j ≠ .r11 := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_injective : ∀ i < 4, ∀ j < 4, wordReg i = wordReg j ↔ i = j := by decide

theorem rotation_bounds (i : Nat) : 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by
  have h : ∀ j < 4, 1 ≤ Spec.Rc2.rotation j ∧ Spec.Rc2.rotation j < 16 := by decide
  simpa only [Spec.Rc2.rotation, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem rotate16_ok (s : State) (r : Reg) (hr : r ≠ .rax)
    (x : BitVec 16) (hx : s.gpr r = x.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ∃ s', runBlock isa (rotate16 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 64 ∧ Keep [r, .rax] s s' := by
  have hleft : 1 ≤ 64 - n ∧ 64 - n ≤ 63 := by omega
  have hright : 1 ≤ 16 - n ∧ 16 - n ≤ 63 := by omega
  refine ⟨_, by
    simp only [rotate16, rr, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, execShift, VG.X86_64.readSrc, hleft, hright, and_self, ite_true, hr, Ne.symm hr,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_setFlags, gpr_arithFlags,
      ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      hr, ite_false]
    rw [hx]
    exact rotateWord x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem mixInputs_ok (s : State) (i j : Nat) (hj : j < 64)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) :
    ∃ s', runBlock isa (mixInputs j i) s = some s' ∧
      s'.gpr .r10 = (s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
        (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))) ∧
      s'.gpr .r8 = ((Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD j 0).setWidth 64 ∧
      Keep [.r8, .r9, .r10, .r11] s s' := by
  have h₁ := VG.Proof.Rc2.X86_64.wordReg_separate (i + 1)
  have h₂ := VG.Proof.Rc2.X86_64.wordReg_separate (i + 2)
  have h₃ := VG.Proof.Rc2.X86_64.wordReg_separate (i + 3)
  have lo := readable (2 * j) (by omega)
  have hi := readable (2 * j + 1) (by omega)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reducePow, and_self, mixInputs, loadKey, rr, memOp,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, VG.X86_64.readSrc, State.load8, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
      wr_setReg, wr_arithFlags, lo, hi,
      h₁.2.2.2.2.2.2.2.1, h₁.2.2.2.2.2.2.2.2,
      h₂.2.2.2.2.2.2.2.1, h₃.2.2.2.2.2.2.2.1]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true,
      ite_false]
    change _ + ((_ ^^^ BitVec.allOnes 64) &&& _) = _
    rw [BitVec.xor_allOnes]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [joinBytes, scheduleAt_getD _ _ _ hj]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

/-- Current RC2 words in the four dedicated registers. -/
def Words (s : State) (v : Spec.Rc2.State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 64

def temps : List Reg := [.rax, .rcx, .r8, .r9, .r10, .r11]
def roundWrites : List Reg := VG.Proof.Rc2.X86_64.temps ++ [.r12, .r13, .r14, .r15]

theorem wordReg_not_temps (i : Nat) : wordReg i ∉ VG.Proof.Rc2.X86_64.temps := by
  have h := VG.Proof.Rc2.X86_64.wordReg_separate i
  simp only [VG.Proof.Rc2.X86_64.temps, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem wordReg_mem_roundWrites (i : Nat) : wordReg i ∈ VG.Proof.Rc2.X86_64.roundWrites := by
  have h : ∀ j < 4, wordReg j ∈ VG.Proof.Rc2.X86_64.roundWrites := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by
  simp [Vector.getD, hi]

theorem Words.update {s s' : State} {v : Spec.Rc2.State} (h : VG.Proof.Rc2.X86_64.Words s v)
    (i : Nat) (hi : i < 4) (x : BitVec 16)
    (out : s'.gpr (wordReg i) = x.setWidth 64)
    (keep : Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s') : VG.Proof.Rc2.X86_64.Words s' (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j
    simpa [Vector.getD, hi] using out
  · have hr : wordReg j ∉ wordReg i :: VG.Proof.Rc2.X86_64.temps := by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => he ((VG.Proof.Rc2.X86_64.wordReg_injective j hj i hi).mp e), VG.Proof.Rc2.X86_64.wordReg_not_temps j⟩
    rw [keep.reg _ hr, h j hj]
    rw [VG.Proof.Rc2.X86_64.vector_getD _ j hj, VG.Proof.Rc2.X86_64.vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

theorem Words.preserve {s s' : State} {v : Spec.Rc2.State} (h : VG.Proof.Rc2.X86_64.Words s v)
    (keep : Keep VG.Proof.Rc2.X86_64.temps s s') : VG.Proof.Rc2.X86_64.Words s' v := by
  intro i hi
  exact (keep.reg _ (VG.Proof.Rc2.X86_64.wordReg_not_temps i)).trans (h i hi)

theorem Keep.round {s s' : State} {i : Nat}
    (h : Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s') : Keep VG.Proof.Rc2.X86_64.roundWrites s s' :=
  h.weaken (by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with he | hm
    · subst r; exact VG.Proof.Rc2.X86_64.wordReg_mem_roundWrites i
    · exact List.mem_append_left _ hm)

theorem addInputs_ok (s : State) (r : Reg) (h10 : r ≠ .r10) :
    ∃ s', runBlock isa [.alu .add r (.reg .r8), .alu .add r (.reg .r10),
      .alu .and r (.imm 65535)] s = some s' ∧
      s'.gpr r = (s.gpr r + s.gpr .r8 + s.gpr .r10) &&& 65535 ∧ Keep [r] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags,
      Ne.symm h10, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem subInputs_ok (s : State) (r : Reg) (h10 : r ≠ .r10) :
    ∃ s', runBlock isa [.alu .sub r (.reg .r8), .alu .sub r (.reg .r10),
      .alu .and r (.imm 65535)] s = some s' ∧
      s'.gpr r = (s.gpr r - s.gpr .r8 - s.gpr .r10) &&& 65535 ∧ Keep [r] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags,
      Ne.symm h10, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem mix_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) :
    WP isa (.block (mix j i)) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' (Spec.Rc2.mix (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j i v) ∧
      Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s') := by
  rw [mix, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, composite₁, key₁, keep₁⟩ := VG.Proof.Rc2.X86_64.mixInputs_ok s i j hj readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have sep := VG.Proof.Rc2.X86_64.wordReg_separate i
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := VG.Proof.Rc2.X86_64.addInputs_ok s₁ (wordReg i)
    sep.2.2.2.2.2.2.2.1
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  let x := v.getD i 0 + (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD j 0 +
    (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) +
    (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)
  have wordmod (j : Nat) : wordReg j = wordReg (j % 4) := by simp [wordReg]
  have value₂ : s₂.gpr (wordReg i) = x.setWidth 64 := by
    rw [out₂, key₁, composite₁, keep₁.reg (wordReg i) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
        sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩), hv i hi,
      wordmod (i + 3), wordmod (i + 2), wordmod (i + 1),
      hv _ (Nat.mod_lt _ (by decide)), hv _ (Nat.mod_lt _ (by decide)),
      hv _ (Nat.mod_lt _ (by decide))]
    exact mixWord _ _ _ _ _
  have hn := VG.Proof.Rc2.X86_64.rotation_bounds i
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.X86_64.rotate16_ok s₂ (wordReg i) sep.1 x value₂ _ hn.1 hn.2
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₁ : Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s₁ := keep₁.weaken (by
    intro r hr
    apply List.mem_cons_of_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have k₂ : Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s₁ s₂ := keep₂.weaken (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact List.mem_cons_self)
  have k₃ : Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s₂ s₃ := keep₃.weaken (by
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
  rw [VG.Proof.Rc2.X86_64.wordReg_mod (i + d)]
  intro he
  have := (VG.Proof.Rc2.X86_64.wordReg_injective _ (Nat.mod_lt _ (by decide)) i hi).mp he
  omega

theorem keep_inputs {s s' : State} (h : Keep [.r8, .r9, .r10, .r11] s s') (i : Nat) :
    Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s' := h.weaken (by
  intro r hr
  apply List.mem_cons_of_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> subst r <;> decide)

theorem keep_rotate {i : Nat} {s s' : State} (h : Keep [wordReg i, .rax] s s') :
    Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · subst r; exact List.mem_cons_self
  · subst r; exact List.mem_cons_of_mem _ (by decide))

theorem keep_word {i : Nat} {s s' : State} (h : Keep [wordReg i] s s') :
    Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r; exact List.mem_cons_self)

theorem reverseMix_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) :
    WP isa (.block (reverseMix j i)) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j i v) ∧
      Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s') := by
  rw [reverseMix, List.append_assoc, WP.block_append_iff]
  have sep := VG.Proof.Rc2.X86_64.wordReg_separate i
  have hn := VG.Proof.Rc2.X86_64.rotation_bounds i
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86_64.rotate16_ok s (wordReg i) sep.1 (v.getD i 0)
    (hv i hi) (16 - Spec.Rc2.rotation i) (by omega) (by omega)
  rw [rotateLeft_reverse _ _ hn.1 hn.2] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ : s₁.gpr .rdi = s.gpr .rdi := keep₁.reg _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm sep.2.2.2.1, by decide⟩)
  have read₁ : ∀ k < 128,
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 k) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable
  obtain ⟨s₂, run₂, composite₂, key₂, keep₂⟩ := VG.Proof.Rc2.X86_64.mixInputs_ok s₁ i j hj read₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.X86_64.subInputs_ok s₂ (wordReg i) sep.2.2.2.2.2.2.2.1
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have other (d : Nat) (hd : 1 ≤ d) (hd' : d < 4) :
      s₁.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 64 := by
    rw [keep₁.reg _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨VG.Proof.Rc2.X86_64.wordReg_offset_ne i hi d hd hd', (VG.Proof.Rc2.X86_64.wordReg_separate _).1⟩),
      VG.Proof.Rc2.X86_64.wordReg_mod (i + d)]
    exact hv _ (Nat.mod_lt _ (by decide))
  have keptWord := keep₂.reg (wordReg i) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
      sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩)
  have value₃ : s₃.gpr (wordReg i) =
      ((v.getD i 0).rotateRight (Spec.Rc2.rotation i) -
        (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD j 0 -
        (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) -
        (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)).setWidth 64 := by
    rw [out₃, keptWord, out₁, key₂, composite₂, keep₁.mem, ptr₁,
      other 3 (by decide) (by decide), other 2 (by decide) (by decide),
      other 1 (by decide) (by decide)]
    exact reverseMixWord _ _ _ _ _
  have keep := ((VG.Proof.Rc2.X86_64.keep_rotate keep₁).trans (VG.Proof.Rc2.X86_64.keep_inputs keep₂ i)).trans (VG.Proof.Rc2.X86_64.keep_word keep₃)
  exact ⟨hv.update i hi _ value₃ keep, keep⟩

theorem adjust_ok (s : State) (r : Reg) (subtract : Bool) :
    ∃ s', runBlock isa [.alu (if subtract then .sub else .add) r (.reg .rax),
      .alu .and r (.imm 65535)] s = some s' ∧
      s'.gpr r = (if subtract then s.gpr r - s.gpr .rax else s.gpr r + s.gpr .rax) &&& 65535 ∧
      Keep [r] s s' := by
  cases subtract <;>
    refine ⟨_, by
      simp only [Bool.false_eq_true, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, VG.X86_64.readSrc, Option.bind_some, gpr_setReg,
        ↓reduceIte]
      rfl, ?_⟩
  all_goals
    constructor
    · exact gpr_setReg_self _ _ _
    · constructor
      · intro r' hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
      · simp only [mem_setReg, mem_arithFlags]
      · simp only [rd_setReg, rd_arithFlags]
      · simp only [wr_setReg, wr_arithFlags]

theorem indexWord (x : BitVec 16) :
    ((x.setWidth 64).setWidth 6).toNat = (x &&& 63).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  change x.toNat % 18446744073709551616 % 64 = x.toNat &&& (2 ^ 6 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show x.toNat < 18446744073709551616 by have := x.isLt; omega)]

def mashSpec (direction : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match direction with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem mash_ok (direction : Spec.Rc2.Direction) (s : State)
    (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v) (i : Nat) (hi : i < 4)
    (readable : VG.Proof.Rc2.X86_64.ScanMemory s) :
    WP isa (.block (mash direction i)) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' (VG.Proof.Rc2.X86_64.mashSpec direction (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) i v) ∧
      Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s') := by
  rw [mash, List.append_assoc, WP.block_append_iff]
  let s₁ := s.setReg .rax (s.gpr (wordReg (i + 3)))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, Option.map_some]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : Keep VG.Proof.Rc2.X86_64.temps s s₁ := by
    constructor
    · intro r hr
      exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _
  have ptr₁ := keep₁.reg .rdi (by decide)
  have read₁ : VG.Proof.Rc2.X86_64.ScanMemory s₁ := readable.keep keep₁ (by decide) (by decide)
  apply WP.mono (Sse2.keyLookup_ok s₁ read₁.vectors read₁.scratch)
  intro s₂ h₂
  let k := Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)
  let key := k.getD ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0
  have out₂ : s₂.gpr .rax = key.setWidth 64 := by
    rw [h₂.1, keep₁.mem, ptr₁]
    change (k.getD (((s.gpr (wordReg (i + 3))).setWidth 6).toNat) 0).setWidth 64 = _
    rw [VG.Proof.Rc2.X86_64.wordReg_mod (i + 3), hv _ (Nat.mod_lt _ (by decide)), VG.Proof.Rc2.X86_64.indexWord]
  have keep₂ : Keep VG.Proof.Rc2.X86_64.temps s₁ s₂ := h₂.2
  have value₂ := ((hv.preserve keep₁).preserve keep₂) i hi
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.X86_64.adjust_ok s₂ (wordReg i) (direction == .decrypt)
  have code_eq : (if (direction == .decrypt) = true then AluOp.sub else .add) =
      (if direction = .encrypt then .add else .sub) := by cases direction <;> rfl
  rw [code_eq] at run₃
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep : Keep (wordReg i :: VG.Proof.Rc2.X86_64.temps) s s₃ :=
    ((keep₁.trans keep₂).weaken (fun _ hr => List.mem_cons_of_mem _ hr)).trans (VG.Proof.Rc2.X86_64.keep_word keep₃)
  have out₃' : s₃.gpr (wordReg i) =
      (if direction == .decrypt then v.getD i 0 - key else v.getD i 0 + key).setWidth 64 := by
    rw [out₃, value₂, out₂]
    cases direction <;>
      simp [maskWord_lit, BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]
  constructor
  · cases direction <;> exact hv.update i hi _ out₃' keep
  · exact keep

end VG.Proof.Rc2.X86_64

end

section

section

/-! # Composition of RC2's sixteen rounds -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem foldWords_ok (code : Nat → List Instr)
    (step : Spec.Rc2.Schedule → Nat → Spec.Rc2.State → Spec.Rc2.State) (is : List Nat)
    (correct : ∀ i ∈ is, ∀ (s : State) (v : Spec.Rc2.State), VG.Proof.Rc2.X86_64.Words s v →
      (VG.Proof.Rc2.X86_64.ScanMemory s) →
      WP isa (.block (code i)) s (fun s' =>
        VG.Proof.Rc2.X86_64.Words s' (step (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) i v) ∧ Keep VG.Proof.Rc2.X86_64.roundWrites s s'))
    (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v)
    (readable : VG.Proof.Rc2.X86_64.ScanMemory s) :
    WP isa (.block (is.flatMap code)) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' (is.foldl (fun v i => step (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) i v) v) ∧
      Keep VG.Proof.Rc2.X86_64.roundWrites s s') := by
  induction is generalizing s v with
  | nil =>
    apply WP.block_nil
    exact ⟨hv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (correct i (by simp) s v hv readable)
    intro s₁ h₁
    have ptr₁ := h₁.2.reg .rdi (by decide)
    have read₁ : VG.Proof.Rc2.X86_64.ScanMemory s₁ := readable.keep h₁.2 (by decide) (by decide)
    apply WP.mono (ih (fun j hj => correct j (List.mem_cons_of_mem _ hj)) s₁ _ h₁.1 read₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₁.2.mem, ptr₁] at h₂
    exact h₂.1

theorem mixRound_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v)
    (j : Nat) (hj : j < 16)
    (readable : VG.Proof.Rc2.X86_64.ScanMemory s) :
    WP isa (.block ((List.range 4).flatMap (fun i => mix (4 * j + i) i))) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' (Spec.Rc2.mixRound (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) ∧
      Keep VG.Proof.Rc2.X86_64.roundWrites s s') := by
  apply VG.Proof.Rc2.X86_64.foldWords_ok (step := fun k i v => Spec.Rc2.mix k (4 * j + i) i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound := List.mem_range.mp hi
  apply WP.mono (VG.Proof.Rc2.X86_64.mix_ok s v hv i (4 * j + i) bound (by omega) readable.bytes)
  exact fun _ h => ⟨h.1, h.2.round⟩

theorem reverseMixRound_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v)
    (j : Nat) (hj : j < 16)
    (readable : VG.Proof.Rc2.X86_64.ScanMemory s) :
    WP isa (.block ([3, 2, 1, 0].flatMap (fun i => reverseMix (4 * j + i) i))) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' (Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) ∧
      Keep VG.Proof.Rc2.X86_64.roundWrites s s') := by
  apply VG.Proof.Rc2.X86_64.foldWords_ok (step := fun k i v => Spec.Rc2.reverseMix k (4 * j + i) i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound : i < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  apply WP.mono (VG.Proof.Rc2.X86_64.reverseMix_ok s v hv i (4 * j + i) bound (by omega) readable.bytes)
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

theorem mashRound_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v)
    (readable : VG.Proof.Rc2.X86_64.ScanMemory s) :
    WP isa (.block ((VG.Proof.Rc2.X86_64.order d).flatMap (mash d))) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' (VG.Proof.Rc2.X86_64.mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) v) ∧
      Keep VG.Proof.Rc2.X86_64.roundWrites s s') := by
  have he (k : Spec.Rc2.Schedule) : VG.Proof.Rc2.X86_64.mashRoundSpec d k v =
      (VG.Proof.Rc2.X86_64.order d).foldl (fun v i => VG.Proof.Rc2.X86_64.mashSpec d k i v) v := by cases d <;> rfl
  simp only [he]
  apply VG.Proof.Rc2.X86_64.foldWords_ok (step := fun k i v => VG.Proof.Rc2.X86_64.mashSpec d k i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound : i < 4 := by
    cases d with
    | encrypt => exact List.mem_range.mp hi
    | decrypt =>
      simp only [VG.Proof.Rc2.X86_64.order, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
  apply WP.mono (VG.Proof.Rc2.X86_64.mash_ok d s v hv i bound readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  let v := match d with
    | .encrypt => Spec.Rc2.mixRound k j v
    | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v
  if j = 4 ∨ j = 10 then VG.Proof.Rc2.X86_64.mashRoundSpec d k v else v

theorem round_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v)
    (j : Nat) (hj : j < 16)
    (readable : VG.Proof.Rc2.X86_64.ScanMemory s) :
    WP isa (.block (VG.Impl.Rc2.X86_64.round d j)) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' (VG.Proof.Rc2.X86_64.roundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) ∧
      Keep VG.Proof.Rc2.X86_64.roundWrites s s') := by
  have finish (s₁ : State) (v₁ : Spec.Rc2.State) (h₁ : VG.Proof.Rc2.X86_64.Words s₁ v₁ ∧ Keep VG.Proof.Rc2.X86_64.roundWrites s s₁) :
      WP isa (.block (if j = 4 ∨ j = 10 then (VG.Proof.Rc2.X86_64.order d).flatMap (mash d) else [])) s₁ (fun s₂ =>
        VG.Proof.Rc2.X86_64.Words s₂ (if j = 4 ∨ j = 10 then VG.Proof.Rc2.X86_64.mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) v₁
          else v₁) ∧ Keep VG.Proof.Rc2.X86_64.roundWrites s s₂) := by
    by_cases h : j = 4 ∨ j = 10
    · rw [ite_eq_left h]
      have ptr₁ := h₁.2.reg .rdi (by decide)
      have read₁ : VG.Proof.Rc2.X86_64.ScanMemory s₁ := readable.keep h₁.2 (by decide) (by decide)
      apply WP.mono (VG.Proof.Rc2.X86_64.mashRound_ok d s₁ v₁ h₁.1 read₁)
      intro s₂ h₂
      rw [h₁.2.mem, ptr₁] at h₂
      exact ⟨by simpa only [ite_eq_left h] using h₂.1, h₁.2.trans h₂.2⟩
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by simpa only [ite_eq_right h] using h₁.1, h₁.2⟩
  cases d with
  | encrypt =>
    rw [VG.Impl.Rc2.X86_64.round, WP.block_append_iff]
    apply WP.mono (VG.Proof.Rc2.X86_64.mixRound_ok s v hv j hj readable)
    intro s₁ h₁
    exact finish s₁ _ h₁
  | decrypt =>
    rw [VG.Impl.Rc2.X86_64.round, WP.block_append_iff]
    apply WP.mono (VG.Proof.Rc2.X86_64.reverseMixRound_ok s v hv (15 - j) (by omega) readable)
    intro s₁ h₁
    exact finish s₁ _ h₁

theorem rounds_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v)
    (readable : VG.Proof.Rc2.X86_64.ScanMemory s) :
    WP isa (.block ((List.range 16).flatMap (VG.Impl.Rc2.X86_64.round d))) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' ((List.range 16).foldl (fun v j => VG.Proof.Rc2.X86_64.roundSpec d
        (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) v) ∧ Keep VG.Proof.Rc2.X86_64.roundWrites s s') := by
  apply VG.Proof.Rc2.X86_64.foldWords_ok (step := fun k j v => VG.Proof.Rc2.X86_64.roundSpec d k j v) _ _ _ s v hv readable
  intro j hj s v hv readable
  exact VG.Proof.Rc2.X86_64.round_ok d s v hv j (List.mem_range.mp hj) readable

end VG.Proof.Rc2.X86_64

end

/-! # Loading and storing RC2 blocks -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem unpackWord_ok (s : State) (i : Nat) (hi : i < 4) :
    ∃ s', runBlock isa (unpackWord i) s = some s' ∧
      s'.gpr (wordReg i) = (((s.gpr .rax) >>> (16 * i)).setWidth 16).setWidth 64 ∧
      Keep [wordReg i] s s' := by
  by_cases hz : i = 0
  · subst i
    refine ⟨_, by
      simp only [unpackWord, rr, ite_true, List.append_nil, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc,
        Option.map_some, Option.bind_some, gpr_setReg, ite_true]
      rfl, ?_⟩
    constructor
    · simp only [gpr_setReg_self, Nat.mul_zero, BitVec.ushiftRight_zero]
      exact maskWord _
    · constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
      · simp only [mem_setReg, mem_arithFlags]
      · simp only [rd_setReg, rd_arithFlags]
      · simp only [wr_setReg, wr_arithFlags]
  · have hn : 1 ≤ 16 * i ∧ 16 * i ≤ 63 := by omega
    refine ⟨_, by
      simp only [unpackWord, rr, hz, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, VG.X86_64.readSrc,
        Option.map_some, Option.bind_some, gpr_setReg, gpr_setFlags, hn, and_self, ite_true]
      rfl, ?_⟩
    constructor
    · rw [gpr_setReg_self]
      exact maskWord _
    · constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, ite_false]
      · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
      · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
      · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem unpackWords_ok (is : List Nat) (hi : ∀ i ∈ is, i < 4) (s : State) :
    WP isa (.block (is.flatMap unpackWord)) s (fun s' =>
      (∀ i ∈ is, s'.gpr (wordReg i) = (((s.gpr .rax) >>> (16 * i)).setWidth 16).setWidth 64) ∧
      Keep (is.map wordReg) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86_64.unpackWord_ok s i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁)
    intro s₂ h₂
    have input₁ := keep₁.reg .rax (by
      simp only [List.mem_singleton]
      exact Ne.symm (VG.Proof.Rc2.X86_64.wordReg_separate i).1)
    constructor
    · intro j hj
      rw [List.mem_cons] at hj
      by_cases hm : j ∈ is
      · rw [h₂.1 j hm, input₁]
      · have he : j = i := hj.resolve_right hm
        subst j
        rw [h₂.2.reg _ (by
          intro hm'
          obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
          have je := (VG.Proof.Rc2.X86_64.wordReg_injective j (hi j (List.mem_cons_of_mem _ hj)) i (hi i (by simp))).mp he
          exact hm (je ▸ hj)), out₁]
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_singleton] at hr
        subst r; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hr

theorem blockLoad_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) :
    WP isa (.block blockLoad) s (fun s' =>
      VG.Proof.Rc2.X86_64.Words s' (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .rsi))) ∧
      Keep VG.Proof.Rc2.X86_64.roundWrites s s') := by
  rw [blockLoad, WP.block_append_iff]
  let s₁ := s.setReg .rax (s.mem.readW (s.gpr .rsi) 64)
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
      State.load64, State.ea, offset_nat, BitVec.add_zero, readable, ite_true,
      Option.map_some]
    rfl
  apply WP.mono (VG.Proof.Rc2.X86_64.unpackWords_ok (List.range 4) (fun i hi => List.mem_range.mp hi) s₁)
  intro s₂ h₂
  constructor
  · intro i hi
    rw [h₂.1 i (List.mem_range.mpr hi), decode_read64 _ _ i hi]
    rfl
  · have keep₁ : Keep VG.Proof.Rc2.X86_64.roundWrites s s₁ := by
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ (by decide)))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _
    apply keep₁.trans
    exact h₂.2.weaken (by
      intro r hr
      obtain ⟨i, _, he⟩ := List.mem_map.mp hr
      subst r; exact VG.Proof.Rc2.X86_64.wordReg_mem_roundWrites i)

theorem packWord_ok (s : State) (i : Nat) (hi : 1 ≤ i) (hi' : i < 4) :
    ∃ s', runBlock isa (packWord i) s = some s' ∧
      s'.gpr .rax = s.gpr .rax ||| (s.gpr (wordReg i)).rotateRight (64 - 16 * i) ∧
      Keep [.rax, .rcx] s s' := by
  have hn : 1 ≤ 64 - 16 * i ∧ 64 - 16 * i ≤ 63 := by omega
  refine ⟨_, by
    simp only [packWord, rr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      execShift, VG.X86_64.readSrc, Option.map_some, Option.bind_some, gpr_setReg, gpr_setFlags,
      hn, and_self, reduceCtorEq, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem packWords_ok (is : List Nat) (hi : ∀ i ∈ is, 1 ≤ i ∧ i < 4)
    (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v) :
    WP isa (.block (is.flatMap packWord)) s (fun s' =>
      s'.gpr .rax = is.foldl (fun acc i => acc |||
        ((v.getD i 0).setWidth 64).rotateRight (64 - 16 * i)) (s.gpr .rax) ∧
      Keep [.rax, .rcx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have bound := hi i (by simp)
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86_64.packWord_ok s i bound.1 bound.2
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have keepTemps : Keep VG.Proof.Rc2.X86_64.temps s s₁ := keep₁.weaken (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h <;> subst r <;> decide)
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ (hv.preserve keepTemps))
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁, hv i bound.2]
    rfl

/-- The block store changes exactly the data word, plus two caller-saved
registers; it leaves all memory-access permissions unchanged. -/
theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86_64.Words s v)
    (writable : InRegions s.wr (s.gpr .rsi) 8) :
    WP isa (.block blockStore) s (fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi) (pack v) ∧
      (∀ r, r ∉ [.rax, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr) := by
  rw [blockStore, List.append_assoc, WP.block_append_iff]
  let s₁ := s.setReg .rax (s.gpr (wordReg 0))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, Option.map_some]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : Keep [.rax, .rcx] s s₁ := by
    constructor
    · intro r hr
      exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _
  have keepTemps : Keep VG.Proof.Rc2.X86_64.temps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h <;> subst r <;> decide)
  apply WP.mono (VG.Proof.Rc2.X86_64.packWords_ok [1, 2, 3] (by decide) s₁ v (hv.preserve keepTemps))
  intro s₂ h₂
  have keep := keep₁.trans h₂.2
  have ptr₂ := keep.reg .rsi (by decide)
  have out₂ : s₂.gpr .rax = pack v := by
    rw [h₂.1]
    change ((s.gpr (wordReg 0) ||| ((v.getD 1 0).setWidth 64).rotateRight 48) |||
      ((v.getD 2 0).setWidth 64).rotateRight 32) |||
      ((v.getD 3 0).setWidth 64).rotateRight 16 = _
    rw [hv 0 (by decide)]
    exact (pack_eq v).symm
  refine WP.of_runBlock ⟨{s₂ with mem := s₂.mem.writeW (s₂.gpr .rsi) (s₂.gpr .rax)}, ?_, ?_⟩
  · have valid : InRegions s₂.wr (s₂.gpr .rsi) 8 := by rw [keep.wr, ptr₂]; exact writable
    simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
      State.ea, offset_nat, BitVec.add_zero, valid, ite_true]
  · exact ⟨by rw [keep.mem, ptr₂, out₂], keep.reg, keep.rd, keep.wr⟩

end VG.Proof.Rc2.X86_64

end

/-! # Saving and restoring RC2's callee-saved registers in scratch -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

def saveMem (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) : Mem :=
  (List.range n).foldl (fun m i => m.writeW (p + BitVec.ofNat 64 (8 * i)) (v i)) m

theorem saveMem_succ (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) :
    VG.Proof.Rc2.X86_64.saveMem m p v (n + 1) = (VG.Proof.Rc2.X86_64.saveMem m p v n).writeW (p + BitVec.ofNat 64 (8 * n)) (v n) := by
  simp only [VG.Proof.Rc2.X86_64.saveMem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem saveMem_read (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) (hn : n ≤ 64)
    (i : Nat) (hi : i < n) : (VG.Proof.Rc2.X86_64.saveMem m p v n).readW (p + BitVec.ofNat 64 (8 * i)) 64 = v i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [VG.Proof.Rc2.X86_64.saveMem_succ]
    by_cases he : i = n
    · subst i; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem saveMem_frame (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) (hn : n ≤ 64) :
    Frame [⟨p, 8 * n⟩] m (VG.Proof.Rc2.X86_64.saveMem m p v n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    rw [VG.Proof.Rc2.X86_64.saveMem_succ]
    have prev : Frame [⟨p, 8 * (n + 1)⟩] m (VG.Proof.Rc2.X86_64.saveMem m p v n) := by
      apply (ih (by omega)).sub
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      refine ⟨⟨p, 8 * (n + 1)⟩, List.mem_cons_self, ?_⟩
      intro x hx
      change (x - p).toNat + 1 ≤ 8 * n at hx
      change (x - p).toNat + 1 ≤ 8 * (n + 1)
      omega
    exact prev.writeW List.mem_cons_self _ (Offset.contains_base p (by omega) (by omega))

def saveCode (base : Reg) (regs : Nat → Reg) (n : Nat) : List Instr :=
  (List.range n).map fun i => .store (memOp base (8 * i)) (regs i)

theorem saveCode_ok (s : State) (base : Reg) (regs : Nat → Reg) (n : Nat)
    (writable : ∀ i < n, InRegions s.wr (s.gpr base + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (VG.Proof.Rc2.X86_64.saveCode base regs n)) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.Proof.Rc2.X86_64.saveMem s.mem (s.gpr base) (fun i => s.gpr (regs i)) n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [VG.Proof.Rc2.X86_64.saveCode, List.range_succ, List.map_append, List.map_cons, List.map_nil, WP.block_append_iff]
    apply WP.mono (ih (fun i hi => writable i (by omega)))
    intro s₁ h₁
    have valid := writable n (by omega)
    have valid₁ : InRegions s₁.wr (s₁.gpr base + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.1, h₁.2.2.1]; exact valid
    refine WP.of_runBlock ⟨{s₁ with mem := s₁.mem.writeW (s₁.gpr base + BitVec.ofNat 64 (8 * n)) (s₁.gpr (regs n))}, ?_, ?_⟩
    · simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
        State.ea, offset_nat, valid₁, ite_true]
    · exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, by rw [h₁.2.2.2, h₁.1, VG.Proof.Rc2.X86_64.saveMem_succ]⟩

def restoreCode (base : Reg) (regs : Nat → Reg) (is : List Nat) : List Instr :=
  is.map fun i => .mov (regs i) (.mem (memOp base (8 * i)))

theorem restoreCode_ok (s : State) (base : Reg) (regs : Nat → Reg) (is : List Nat)
    (values : Reg → BitVec 64)
    (separate : ∀ i ∈ is, regs i ≠ base)
    (readable : ∀ i ∈ is, InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 (8 * i)) 8)
    (stored : ∀ i ∈ is, s.mem.readW (s.gpr base + BitVec.ofNat 64 (8 * i)) 64 = values (regs i)) :
    WP isa (.block (VG.Proof.Rc2.X86_64.restoreCode base regs is)) s (fun s' =>
      (∀ r ∈ is.map regs, s'.gpr r = values r) ∧ Keep (is.map regs) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    change WP isa (.block (([.mov (regs i) (.mem (memOp base (8 * i)))] : List Instr) ++ VG.Proof.Rc2.X86_64.restoreCode base regs is)) s _
    rw [WP.block_append_iff]
    let s₁ := s.setReg (regs i) (values (regs i))
    have hi : i ∈ i :: is := List.mem_cons_self
    refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
    · simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, State.load64,
        State.ea, offset_nat, readable i hi, ite_true, Option.map_some, stored i hi]
      rfl
    have keep₁ : Keep [regs i] s s₁ := by
      constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        exact gpr_setReg_of_ne _ _ hr
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _
    have ptr₁ := keep₁.reg base (by
      simp only [List.mem_singleton]; exact Ne.symm (separate i hi))
    have read₁ : ∀ j ∈ is,
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr base + BitVec.ofNat 64 (8 * j)) 8 := by
      rw [keep₁.rd, keep₁.wr, ptr₁]
      exact fun j hj => readable j (List.mem_cons_of_mem _ hj)
    have stored₁ : ∀ j ∈ is,
        s₁.mem.readW (s₁.gpr base + BitVec.ofNat 64 (8 * j)) 64 = values (regs j) := by
      rw [keep₁.mem, ptr₁]
      exact fun j hj => stored j (List.mem_cons_of_mem _ hj)
    apply WP.mono (ih s₁ (fun j hj => separate j (List.mem_cons_of_mem _ hj)) read₁ stored₁)
    intro s₂ h₂
    constructor
    · intro r hr
      simp only [List.map_cons, List.mem_cons] at hr
      by_cases hm : r ∈ is.map regs
      · exact h₂.1 r hm
      · have he := hr.resolve_right hm
        subst r
        rw [h₂.2.reg _ hm]
        exact gpr_setReg_self _ _ _
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_singleton] at hr
        subst r; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hr

theorem saveMem_frame_le (m : Mem) (p : Addr) (v : Nat → BitVec 64)
    (n capacity : Nat) (hn : n ≤ capacity) (hc : capacity ≤ 64) :
    Frame [⟨p, 8 * capacity⟩] m (VG.Proof.Rc2.X86_64.saveMem m p v n) := by
  apply (VG.Proof.Rc2.X86_64.saveMem_frame m p v n (by omega)).sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  refine ⟨⟨p, 8 * capacity⟩, List.mem_cons_self, ?_⟩
  intro x hx
  change (x - p).toNat + 1 ≤ 8 * n at hx
  change (x - p).toNat + 1 ≤ 8 * capacity
  omega

end VG.Proof.Rc2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Lit`. -/
section

/-! # Literal RC2 programs for kernel-evaluated checks -/

namespace VG.Impl.Rc2.X86_64.Sse2

open VG.X86_64 VG.Impl.Rc2.X86_64

/-- `piValues`, reading PITABLE from its packed table (`Rc2.piTable_getD`). -/
def piValuesLit (n : Nat) : BitVec 128 :=
  ofWords fun j => (BitVec.ofNat 8 (VG.Rc2.piNat (8 * n + j))).setWidth 16

/-- `piStep`, reading PITABLE from its packed table. -/
def piStepLit (n : Nat) : List Instr := loadConst .xmm4 (VG.Impl.Rc2.X86_64.Sse2.piValuesLit n) ++ select

/-- `piLookup`, reading PITABLE from its packed table. -/
def piLookupLit : List Instr :=
  start .r8 255 ++ (List.range 32).flatMap VG.Impl.Rc2.X86_64.Sse2.piStepLit ++ finish .r8

materialize_value VG.Impl.Rc2.X86_64.Sse2.piLookupLit

/-- The literal of `piLookup`, evaluated through the packed PITABLE. -/
noncomputable abbrev piLookup.lit : List Instr := piLookupLit.lit

theorem piLookup.lit_eq : piLookup = piLookup.lit := by
  have : piStep = VG.Impl.Rc2.X86_64.Sse2.piStepLit := by
    funext n; simp only [piStep, VG.Impl.Rc2.X86_64.Sse2.piStepLit, piValues, VG.Impl.Rc2.X86_64.Sse2.piValuesLit, VG.Rc2.piTable_getD]
  refine Eq.trans ?_ piLookupLit.lit_eq
  simp only [piLookup, VG.Impl.Rc2.X86_64.Sse2.piLookupLit, this]

end VG.Impl.Rc2.X86_64.Sse2

namespace VG

materialize_code Impl.Rc2.X86_64.encryptBlock
materialize_code Impl.Rc2.X86_64.decryptBlock
materialize_code Impl.Rc2.X86_64.expandKey

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.ConstantTime`. -/
section

/-! # Constant-time RC2 block and key-expansion programs -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem encryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (VG.Proof.Rc2.X86_64.PublicRegs [.rdi, .rsi, .rdx]) encryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

theorem decryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (VG.Proof.Rc2.X86_64.PublicRegs [.rdi, .rsi, .rdx]) decryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (VG.Proof.Rc2.X86_64.PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8]) expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

end VG.Proof.Rc2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Block`. -/
section

/-! # Verified RC2 block encryption and decryption -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rsi, 8⟩
    let scratch : Region := ⟨s.gpr .rdx, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .rsi) =
    VG.Proof.Rc2.X86_64.cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))
  pub := VG.Proof.Rc2.X86_64.PublicRegs [.rdi, .rsi, .rdx]

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    VG.Proof.Rc2.X86_64.cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => VG.Proof.Rc2.X86_64.roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86_64.blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => gprPreserved s s' ∧ (VG.Proof.Rc2.X86_64.blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep, retData, retScratch⟩ := hs
  have writes : ∀ i < 4, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86_64.saveCode_ok s .rdx wordReg 4 writes)
  intro s₁ h₁
  have scratchFrame : Frame [⟨s.gpr .rdx, 256⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_frame_le _ _ _ 4 32 (by decide) (by decide)
  have input₁ : Spec.Rc2.blockAt s₁.mem (s₁.gpr .rsi) = Spec.Rc2.blockAt s.mem (s.gpr .rsi) := by
    rw [h₁.1]
    exact blockAt_frame scratchFrame _ (by simpa using dataSep)
  have schedule₁ : Spec.Rc2.scheduleAt s₁.mem (s₁.gpr .rdi) =
      Spec.Rc2.scheduleAt s.mem (s.gpr .rdi) := by
    rw [h₁.1]
    exact scheduleAt_frame scratchFrame _ (by simpa using keySep)
  have dataRead₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsi) 8 := by
    rw [h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86_64.blockLoad_ok s₁ dataRead₁)
  intro s₂ h₂
  have read₂ : ∀ i < 128, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rdi + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [h₂.2.rd, h₂.2.wr, h₂.2.reg .rdi (by decide), h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨s.gpr .rdi, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have scans₂ : VG.Proof.Rc2.X86_64.ScanMemory s₂ := by
    refine ⟨read₂, ?_, ?_⟩
    · intro i hi
      rw [h₂.2.rd, h₂.2.wr, h₂.2.reg .rdi (by decide), h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
      exact ⟨⟨s.gpr .rdi, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [h₂.2.wr, h₂.2.reg .rdx (by decide), h₁.1, h₁.2.2.1, hwr]
      exact ⟨⟨s.gpr .rdx, 256⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86_64.rounds_ok d s₂ _ h₂.1 scans₂)
  intro s₃ h₃
  have keep₂₃ := h₂.2.trans h₃.2
  have ptr₃ : s₃.gpr .rsi = s.gpr .rsi := (keep₂₃.reg .rsi (by decide)).trans (congrFun h₁.1 .rsi)
  have writable₃ : InRegions s₃.wr (s₃.gpr .rsi) 8 := by
    rw [keep₂₃.wr, h₁.2.2.1, hwr, ptr₃]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  let v := (List.range 16).foldl (fun v j => VG.Proof.Rc2.X86_64.roundSpec d
    (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .rsi)))
  have words₃ : VG.Proof.Rc2.X86_64.Words s₃ v := by
    rw [h₂.2.mem, h₂.2.reg .rdi (by decide), schedule₁, input₁] at h₃
    exact h₃.1
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86_64.blockStore_ok s₃ v words₃ writable₃)
  intro s₄ h₄
  have mem₄ : s₄.mem = s₁.mem.writeW (s.gpr .rsi) (pack v) := by rw [h₄.1, keep₂₃.mem, ptr₃]
  have rd₄ : s₄.rd = s.rd := h₄.2.2.1.trans (keep₂₃.rd.trans h₁.2.1)
  have wr₄ : s₄.wr = s.wr := h₄.2.2.2.trans (keep₂₃.wr.trans h₁.2.2.1)
  have regs₄ (r : Reg) (hr : r ∉ VG.Proof.Rc2.X86_64.roundWrites) : s₄.gpr r = s.gpr r := by
    rw [h₄.2.1 r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he <;> subst r <;> exact hr (by decide)), keep₂₃.reg r hr, h₁.1]
  have scratchRead₄ : ∀ i ∈ List.range 4,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, regs₄ .rdx (by decide), hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .rdx, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have saved₄ : ∀ i ∈ List.range 4,
      s₄.mem.readW (s₄.gpr .rdx + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (wordReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [mem₄, regs₄ .rdx (by decide), Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Region.contains_self _ _))
      (by decide), h₁.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_read _ _ _ 4 (by decide) i bound
  apply WP.mono (VG.Proof.Rc2.X86_64.restoreCode_ok s₄ .rdx wordReg (List.range 4) s.gpr
    (fun i _ => (VG.Proof.Rc2.X86_64.wordReg_separate i).2.2.1) scratchRead₄ saved₄)
  intro s₅ h₅
  have finalMem : s₅.mem = s₁.mem.writeW (s.gpr .rsi) (pack v) := h₅.2.mem.trans mem₄
  constructor
  · constructor
    · intro r hr
      by_cases hm : r ∈ (List.range 4).map wordReg
      · exact h₅.1 r hm
      · rw [h₅.2.reg _ hm]
        have covered : ∀ r ∈ calleeSaved,
            r ∈ (List.range 4).map wordReg ∨ r ∉ VG.Proof.Rc2.X86_64.roundWrites := by decide
        exact regs₄ r ((covered r hr).resolve_left hm)
    · have frame₄ : Frame [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 256⟩] s.mem s₅.mem := by
        rw [finalMem]
        exact (scratchFrame.mono (fun _ hr => List.mem_cons_of_mem _ hr)).writeW
          List.mem_cons_self _ (Region.contains_self _ _)
      exact frame₄.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h
          · subst r; exact retData
          · subst r; exact retScratch)
        (by decide)
  · change Spec.Rc2.blockAt s₅.mem (s.gpr .rsi) = _
    rw [finalMem, blockAt_write64, VG.Proof.Rc2.X86_64.cipher_rounds]

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]

theorem encrypt_correct (s : State) (hs : (VG.Proof.Rc2.X86_64.blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.X86_64.blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.X86_64.block_correct .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (VG.Proof.Rc2.X86_64.blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.X86_64.blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.X86_64.block_correct .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem publicRegs_three (s₁ s₂ : State) : VG.Proof.Rc2.X86_64.PublicRegs [.rdi, .rsi, .rdx] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx := by
  simp [VG.Proof.Rc2.X86_64.PublicRegs]

theorem encrypt_verified :
    Verified target encryptBlock (Spec.Rc2.encryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.Rc2.X86_64.encrypt_correct (VG.Proof.Rc2.X86_64.encryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argRegs,
    VG.Proof.Rc2.X86_64.blockContract, VG.Proof.Rc2.X86_64.publicRegs_three, VG.Proof.Rc2.X86_64.cipher] [satState] using VG.Proof.Rc2.X86_64.satState

theorem decrypt_verified :
    Verified target decryptBlock (Spec.Rc2.decryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.Rc2.X86_64.decrypt_correct (VG.Proof.Rc2.X86_64.decryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argRegs,
    VG.Proof.Rc2.X86_64.blockContract, VG.Proof.Rc2.X86_64.publicRegs_three, VG.Proof.Rc2.X86_64.cipher] [satState] using VG.Proof.Rc2.X86_64.satState

end VG.Proof.Rc2.X86_64

end

end
