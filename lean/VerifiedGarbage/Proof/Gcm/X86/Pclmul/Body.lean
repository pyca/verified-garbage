import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Invariant
import VerifiedGarbage.Proof.Framework.X86.Wp

section

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre hP yP dP nBlk hR yR)
open VG.Impl.Gcm.X86.Pclmul (argOp at_)

theorem Env.arithFlags {s₀ s : State} (h : Env s₀ s) (v : BitVec 32) (c o : Bool) :
    Env s₀ (arithFlags s v c o) :=
  ⟨(mem_arithFlags s v c o).trans h.mem, (rd_arithFlags s v c o).trans h.rd,
    (wr_arithFlags s v c o).trans h.wr,
    fun r hr => by rw [gpr_arithFlags]; exact h.saved r hr⟩

theorem movArg_ok {s₀ s : State} (hp : GPre s₀) (he : Env s₀ s)
    (i : Nat) (hi : i < 5) (d : Reg) (hd : d ∉ calleeSaved) :
    WP isa (.block [.mov d (.mem (argOp i))]) s fun s' =>
      s'.gpr d = arg s₀ i ∧ Env s₀ s' ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm := by
  refine WP.of_runBlock ⟨s.setReg d (arg s₀ i), ?_, ?_⟩
  · rw [runBlock_cons, movArg_exec hp hi he.sp he.mem he.rd he.wr,
      runStep_some, runBlock_nil]
  · exact ⟨gpr_setReg_self _ _ _, he.setReg d _ hd,
      fun r hr => gpr_setReg_of_ne _ _ hr, rfl⟩

theorem test_ok (s : State) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun s' =>
      s'.zf = some (s.gpr .eax == 0) ∧ Env s s' ∧
      s'.gpr = s.gpr ∧ s'.xmm = s.xmm := by
  refine WP.of_runBlock ⟨arithFlags s (s.gpr .eax) false false, ?_, ?_⟩
  · simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some,
      BitVec.and_self, runStep_some, runBlock_nil]
  · exact ⟨rfl, (Env.refl s).arithFlags _ _ _, rfl, rfl⟩

theorem h_read {s : State} (hp : GPre s) :
    InRegions (s.rd ++ s.wr) ((hP s).setWidth 64) 16 := by
  refine ⟨hR s, ?_, Region.contains_self _ _⟩
  simp only [hp.rd, List.mem_append, List.mem_cons, true_or]

theorem y_read {s : State} (hp : GPre s) :
    InRegions (s.rd ++ s.wr) ((yP s).setWidth 64) 16 := by
  refine ⟨yR s, ?_, Region.contains_self _ _⟩
  simp only [hp.wr, List.mem_append, List.mem_cons, or_true, true_or]

theorem Env.trans {s₀ s s' : State} (h : Env s₀ s) (h' : Env s s') : Env s₀ s' :=
  ⟨h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.saved r hr).trans (h.saved r hr)⟩

theorem prologue_ok (s₀ : State) (hp : GPre s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.prologue) s₀ fun s =>
      Inv s₀ 0 s ∧ s.zf = some (decide (nBlk s₀ = 0)) := by
  simp only [Impl.Gcm.X86.Pclmul.prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 Impl.Gcm.X86.Pclmul.revMask s₀ (by decide))
    fun s₁ ⟨rev₁, f₁⟩ => ?_
  have e₁ := (Env.refl s₀).of_setup f₁
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 Impl.Gcm.X86.Pclmul.poly s₁ (by decide))
    fun s₂ ⟨poly₂, f₂⟩ => ?_
  have e₂ := e₁.of_setup f₂
  have rev₂ : s₂.xmm .xmm0 = VG.Proof.Gcm.X86.revMask := by
    rw [f₂.xmm _ (by decide), rev₁]; rfl
  rw [show ([.mov .eax (.mem (argOp 0)), .movdquLoad .xmm7 (at_ .eax 0),
      .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) =
      ([.mov .eax (.mem (argOp 0))] : List Instr) ++
      [.movdquLoad .xmm7 (at_ .eax 0), .xop (.bin .pshufb .xmm7 .xmm0)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₂ 0 (by decide) .eax (by decide))
    fun s₃ ⟨ptr₃, e₃, _, x₃⟩ => ?_
  have hread₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.ea (at_ .eax 0)) 16 := by
    simp only [State.ea, at_, ptr₃, BitVec.add_zero, e₃.rd, e₃.wr]
    exact h_read hp
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .eax 0 s₃ (by decide) (by rw [x₃]; exact rev₂) hread₃)
    fun s₄ ⟨hash₄, f₄⟩ => ?_
  have e₄ := e₃.of_only f₄
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₄) fun s₅ ⟨hash₅, f₅⟩ => ?_
  have e₅ := e₄.of_setup f₅
  have rev₅ : s₅.xmm .xmm0 = VG.Proof.Gcm.X86.revMask := by
    rw [f₅.xmm _ (by decide), f₄.xmm _ (by decide), x₃]; exact rev₂
  have poly₅ : s₅.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₅.xmm _ (by decide), f₄.xmm _ (by decide), x₃]; exact poly₂
  have hash₅' : x * φ (s₅.xmm .xmm3) = φ (H s₀) := by
    rw [hash₅, hash₄, e₃.mem]
    simp only [State.ea, at_, ptr₃, BitVec.add_zero]
  change WP isa (.block (([.mov .ecx (.mem (argOp 1))] : List Instr) ++
    [.movdquLoad .xmm2 (at_ .ecx 0), .xop (.bin .pshufb .xmm2 .xmm0),
      .mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 3)), .alu .test .eax (.reg .eax)])) s₅ _
  rw [WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₅ 1 (by decide) .ecx (by decide))
    fun s₆ ⟨ptr₆, e₆, _, x₆⟩ => ?_
  have yread₆ : InRegions (s₆.rd ++ s₆.wr) (s₆.ea (at_ .ecx 0)) 16 := by
    simp only [State.ea, at_, ptr₆, BitVec.add_zero, e₆.rd, e₆.wr]
    exact y_read hp
  change WP isa (.block (([.movdquLoad .xmm2 (at_ .ecx 0),
    .xop (.bin .pshufb .xmm2 .xmm0)] : List Instr) ++
    [.mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 3)), .alu .test .eax (.reg .eax)])) s₆ _
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm2 .ecx 0 s₆ (by decide) (by rw [x₆]; exact rev₅) yread₆)
    fun s₇ ⟨acc₇, f₇⟩ => ?_
  have e₇ := e₆.of_only f₇
  change WP isa (.block (([.mov .edx (.mem (argOp 2))] : List Instr) ++
    [.mov .eax (.mem (argOp 3)), .alu .test .eax (.reg .eax)])) s₇ _
  rw [WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₇ 2 (by decide) .edx (by decide))
    fun s₈ ⟨ptr₈, e₈, regs₈, x₈⟩ => ?_
  change WP isa (.block (([.mov .eax (.mem (argOp 3))] : List Instr) ++
    [.alu .test .eax (.reg .eax)])) s₈ _
  rw [WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₈ 3 (by decide) .eax (by decide))
    fun s₉ ⟨count₉, e₉, regs₉, x₉⟩ => ?_
  refine WP.mono (test_ok s₉) fun s ⟨zf, ef, regs, xs⟩ => ?_
  constructor
  · refine ⟨e₉.trans ef, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regs, count₉, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [regs, regs₉ _ (by decide), ptr₈, Nat.mul_zero, BitVec.add_zero]
    · rw [regs, regs₉ _ (by decide), regs₈ _ (by decide), f₇.gpr, ptr₆]
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact rev₅
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact poly₅
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact hash₅'
    · rw [xs, x₉, x₈, acc₇, e₆.mem]
      simp only [State.ea, at_, ptr₆, BitVec.add_zero,
        Y, Proof.Gcm.ghashFrom_blocksAt_zero]
  · rw [zf, count₉]
    exact congrArg some (by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Wp.ofNat_beq_zero (arg s₀ 3).isLt)

end VG.Proof.Gcm.X86.Pclmul

end

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre dP nBlk dR)
open VG.Impl.Gcm.X86.Pclmul (at_)

theorem data_read {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s)
    (hb : i < nBlk s₀) :
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edx 0)) 16 := by
  have hf := hp.fD
  have he : s.ea (at_ .edx 0) = (dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    simp only [State.ea, at_, hi.data, BitVec.add_zero]
    exact addr_eq (by omega)
  rw [he, hi.env.rd, hi.env.wr, hp.rd]
  refine ⟨dR s₀, ?_, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [List.mem_append, List.mem_cons, or_true, true_or]

theorem xor_ok (s : State) :
    WP isa (.block [.xop (.bin .pxor .xmm2 .xmm7)]) s fun s' =>
      s'.xmm .xmm2 = s.xmm .xmm2 ^^^ s.xmm .xmm7 ∧ Only [.xmm2] s s' := by
  refine WP.of_runBlock ⟨s.setXmm .xmm2 (s.xmm .xmm2 ^^^ s.xmm .xmm7), ?_, ?_⟩
  · simp only [runBlock_cons, exec, XOp.exec, XBinOp.eval, runStep_some, runBlock_nil]
  · refine ⟨xmm_setXmm_self _ _ _, gpr_setXmm _ _ _, mem_setXmm _ _ _,
      rd_setXmm _ _ _, wr_setXmm _ _ _, ?_⟩
    intro r hr
    exact xmm_setXmm_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem advance_ok (s : State) :
    WP isa (.block [.alu .add .edx (.imm 16), .alu .sub .eax (.imm 1)]) s fun s' =>
      s'.gpr .eax = s.gpr .eax - 1 ∧ s'.gpr .edx = s.gpr .edx + 16 ∧
      s'.zf = some (s.gpr .eax - 1 == 0) ∧ Env s s' ∧
      s'.gpr .ecx = s.gpr .ecx ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, rfl, ?_, True.intro, rfl⟩
  exact (((Env.refl s).arithFlags _ _ _).setReg .edx _ (by decide)).arithFlags _ _ _ |>.setReg .eax _ (by decide)

theorem body_ok {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s)
    (hb : i < nBlk s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.body) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (i + 1) = 0)) := by
  simp only [Impl.Gcm.X86.Pclmul.body, List.append_assoc]
  rw [show ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0),
    .xop (.bin .pxor .xmm2 .xmm7)] : List Instr) =
    ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) ++
    [.xop (.bin .pxor .xmm2 .xmm7)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .edx 0 s (by decide) hi.rev (data_read hp hi hb))
    fun s₁ ⟨input₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (xor_ok s₁) fun s₂ ⟨acc₂, f₂⟩ => ?_
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  have poly₂ : s₂.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.poly
  refine WP.mono (mul_ok s₂ poly₂) fun s₃ ⟨mul₃, f₃⟩ => ?_
  have env₃ := ((hi.env.of_only f₁).of_only f₂).of_only f₃
  have acc₃ : s₃.xmm .xmm2 = Y s₀ (i + 1) := by
    apply φ_inj
    have hin : s₁.xmm .xmm7 = Spec.Gcm.blockAt s₀.mem
        ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) := by
      rw [input₁, hi.env.mem]
      refine congrArg (Spec.Gcm.blockAt _) ?_
      simp only [State.ea, at_, hi.data, BitVec.add_zero]
      exact addr_eq (by have hf := hp.fD; omega)
    rw [mul₃, acc₂, hin, f₁.xmm _ (by decide), hi.acc]
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]
    rw [mul_assoc, mul_left_comm x, hi.hash]
    rw [show Y s₀ (i + 1) = Spec.Gcm.mul (Y s₀ i ^^^ Spec.Gcm.blockAt s₀.mem
      ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i))) (H s₀) from
      Proof.Gcm.ghashFrom_blocksAt_succ _ _ _ _ _, φ_mul]
  refine WP.mono (advance_ok s₃) fun s₄ ⟨count₄, data₄, zf₄, ef₄, out₄, xmm₄⟩ => ?_
  have regs₃ : s₃.gpr = s.gpr := f₃.gpr.trans (f₂.gpr.trans f₁.gpr)
  have bound : nBlk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have count : s₃.gpr .eax - 1 = BitVec.ofNat 32 (nBlk s₀ - (i + 1)) := by
    rw [regs₃, hi.count, Wp.ofNat_pred (by omega), Nat.sub_sub]
  constructor
  · refine ⟨env₃.trans ef₄, by omega, count₄.trans count, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [data₄, regs₃, hi.data, BitVec.add_assoc]
      change dP s₀ + (BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 16) = _
      rw [← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega]
    · rw [out₄, regs₃]; exact hi.out
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.rev
    · rw [xmm₄, f₃.xmm _ (by decide)]; exact poly₂
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.hash
    · rw [xmm₄]; exact acc₃
  · rw [zf₄, count, Wp.ofNat_beq_zero (by omega)]

end VG.Proof.Gcm.X86.Pclmul
