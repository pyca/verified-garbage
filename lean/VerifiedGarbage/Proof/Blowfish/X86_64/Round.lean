import VerifiedGarbage.Proof.Blowfish.X86_64.F
import VerifiedGarbage.Proof.Blowfish.Feistel

/-!
# The rounds

`round_run`: one round on the halves in the low doublewords of `xL` and
`xR`, the P-array entry at `rax`; `cipher_run`: the sixteen and the last
swap undone, `feistel` of the halves.
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

theorem ord_true : ord true = id := rfl
theorem ord_false : ord false = (17 - ·) := rfl

/-- What the rounds need: the lookups', and the P-array readable. -/
structure CipherEnv (sch : Reg) (S : Addr) (s : State) : Prop where
  look : LookEnv sch S s
  neA : sch ≠ Reg.rax
  ne10 : sch ≠ Reg.r10
  rdP : ∀ i < 18, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (4096 + 4 * i)) 4

/-- The vector registers the rounds write. -/
def cXRegs : List XReg := xL :: xR :: fXRegs

/-- After `i` rounds. -/
structure CInv (sch : Reg) (S : Addr) (up : Bool) (s₀ : State) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  rax : u.gpr .rax = BitVec.ofNat 64 (4 * ord up i)
  r10 : u.gpr .r10 = BitVec.ofNat 64 (16 - i)
  halves : (dword (u.xmm xL) 0, dword (u.xmm xR) 0) =
    iter (scheduleAt s₀.mem S) (ord up) i (dword (s₀.xmm xL) 0, dword (s₀.xmm xR) 0)
  xmm : ∀ d, d ∉ cXRegs → u.xmm d = s₀.xmm d
  gpr : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → u.gpr g = s₀.gpr g
  upd : Upd s₀ u

theorem exec_mov32_mem {s : State} {d : Reg} {m : MemOp} (h : InRegions (s.rd ++ s.wr) (s.ea m) 4) :
    exec (.mov32 d (.mem m)) s = some (s.setReg32 d (s.mem.readW (s.ea m) 32)) := by
  simp only [exec, readSrc32, State.load32, h, ite_true, Option.map_some]

theorem dword_movq (s : State) (r : Reg) (v : BitVec 32) (h : s.gpr r = v.setWidth 64) :
    dword ((0 : BitVec 64) ++ s.gpr r) 0 = v := by
  rw [h]; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_dword, BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and, Nat.mul_zero, Nat.zero_add,
    itT _ _ (show i < 64 by omega), BitVec.getLsbD_setWidth, decide_eq_true (show i < 64 by omega), Bool.true_and]

theorem runBlock_append_x {a b : List Instr} {s s₁ : State} (h : runBlock isa a s = some s₁) :
    runBlock isa (a ++ b) s = runBlock isa b s₁ := by
  rw [runBlock_append, h]; rfl

theorem ord_lt (up : Bool) {m : Nat} (hm : m < 18) : ord up m < 18 := by
  cases up <;> simp only [ord, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem ea_p (t : State) (sch : Reg) (S : Addr) (n : Nat) (h1 : t.gpr sch = S)
    (h2 : t.gpr .rax = BitVec.ofNat 64 n) :
    t.ea { base := sch, index := some .rax, disp := Int.ofNat pOff } = S + BitVec.ofNat 64 (4096 + n) := by
  simp only [State.ea, h1, h2, BitVec.mul_one, Rc2.X86_64.offset_nat, pOff]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]

theorem add_imm_run (t : State) (d : Reg) (v : BitVec 32) :
    ∃ t', exec (.alu .add d (.imm v)) t = some t' ∧ t'.gpr d = t.gpr d + v.signExtend 64 ∧
      (∀ g, g ≠ d → t'.gpr g = t.gpr g) ∧ t'.xmm = t.xmm ∧ Upd t t' := by
  refine ⟨_, rfl, ?_, fun g hg => ?_, rfl, rfl⟩
  · simp only [gpr_setReg_self]
  · simp only [gpr_setReg_of_ne _ _ hg, gpr_arithFlags]

theorem sub_imm_run (t : State) (d : Reg) (v : BitVec 32) :
    ∃ t', exec (.alu .sub d (.imm v)) t = some t' ∧ t'.gpr d = t.gpr d - v.signExtend 64 ∧
      t'.zf = some (t.gpr d - v.signExtend 64 == 0) ∧
      (∀ g, g ≠ d → t'.gpr g = t.gpr g) ∧ t'.xmm = t.xmm ∧ Upd t t' := by
  refine ⟨_, rfl, ?_, rfl, fun g hg => ?_, rfl, rfl⟩
  · simp only [gpr_setReg_self]
  · simp only [gpr_setReg_of_ne _ _ hg, gpr_arithFlags]

theorem Upd.refl (t : State) : Upd t t := state_eta t

theorem Upd.of_xmm {t t' : State} (h : t' = { t with xmm := t'.xmm }) : Upd t t' := by
  unfold Upd; rw [h]

/-- The end of a round. -/
theorem roundTail_run (t : State) (up : Bool) :
    ∃ t', runBlock isa [bin .pxor xR fReg, bin .movdqa tmp xL, bin .movdqa xL xR, bin .movdqa xR tmp,
        if up then .alu .add .rax (.imm 4) else .alu .sub .rax (.imm 4), .alu .sub .r10 (.imm 1)] t = some t' ∧
      t'.xmm xL = t.xmm xR ^^^ t.xmm fReg ∧ t'.xmm xR = t.xmm xL ∧
      (∀ d, d ≠ xL → d ≠ xR → d ≠ tmp → t'.xmm d = t.xmm d) ∧
      t'.gpr .rax = (if up then t.gpr .rax + 4 else t.gpr .rax - 4) ∧ t'.gpr .r10 = t.gpr .r10 - 1 ∧
      t'.zf = some (t.gpr .r10 - 1 == 0) ∧ (∀ g, g ≠ .rax → g ≠ .r10 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  let ops : List XOp := [.bin .pxor xR fReg, .bin .movdqa tmp xL, .bin .movdqa xL xR, .bin .movdqa xR tmp]
  let t₁ := ops.foldl (fun t op => op.exec t) t
  have r₁ : runBlock isa (ops.map .xop) t = some t₁ := runXops ops t
  have x₁ : t₁.xmm xL = t.xmm xR ^^^ t.xmm fReg ∧ t₁.xmm xR = t.xmm xL ∧
      ∀ d, d ≠ xL → d ≠ xR → d ≠ tmp → t₁.xmm d = t.xmm d := by
    refine ⟨?_, ?_, fun d h1 h2 h3 => ?_⟩
    · simp (disch := decide) only [t₁, ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, eval_movdqa]
      rfl
    · simp (disch := decide) only [t₁, ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, eval_movdqa]
    · simp only [t₁, ops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2,
        xmm_setXmm_of_ne _ _ h3]
  have g₁ : t₁.gpr = t.gpr := by simp only [t₁, ops, List.foldl, XOp.exec, gpr_setXmm]
  have u₁ : Upd t t₁ := Upd.of_xmm (by simp only [t₁, ops, List.foldl, XOp.exec, State.setXmm])
  have hA : ∃ t₂, exec (if up then .alu .add .rax (.imm 4) else .alu .sub .rax (.imm 4)) t₁ = some t₂ ∧
      t₂.gpr .rax = (if up then t.gpr .rax + 4 else t.gpr .rax - 4) ∧ (∀ g, g ≠ .rax → t₂.gpr g = t₁.gpr g) ∧
      t₂.xmm = t₁.xmm ∧ Upd t₁ t₂ := by
    cases up
    · obtain ⟨t₂, e, h1, -, h2, h3, h4⟩ := sub_imm_run t₁ .rax 4
      exact ⟨t₂, e, by rw [h1, g₁]; rfl, h2, h3, h4⟩
    · obtain ⟨t₂, e, h1, h2, h3, h4⟩ := add_imm_run t₁ .rax 4
      exact ⟨t₂, e, by rw [h1, g₁]; rfl, h2, h3, h4⟩
  obtain ⟨t₂, e₂, a₂, g₂, x₂, u₂⟩ := hA
  obtain ⟨t₃, e₃, a₃, z₃, g₃, x₃, u₃⟩ := sub_imm_run t₂ .r10 1
  have h10 : t₂.gpr .r10 = t.gpr .r10 := by rw [g₂ _ (by decide), g₁]
  refine ⟨t₃, ?_, by rw [x₃, x₂]; exact x₁.1, by rw [x₃, x₂]; exact x₁.2.1,
    fun d h1 h2 h3 => by rw [x₃, x₂]; exact x₁.2.2 d h1 h2 h3, by rw [g₃ _ (by decide), a₂],
    by rw [a₃, h10]; rfl, by rw [z₃, h10]; rfl, fun g h1 h2 => by rw [g₃ _ h2, g₂ _ h1, g₁],
    Upd.trans u₃ (Upd.trans u₂ u₁)⟩
  show runBlock isa (ops.map .xop ++ [_, _]) t = _
  rw [runBlock_append_x r₁, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]

theorem ord_next (up : Bool) {m : Nat} (hm : m < 16) :
    (if up then BitVec.ofNat 64 (4 * ord up m) + 4 else BitVec.ofNat 64 (4 * ord up m) - 4) =
      BitVec.ofNat 64 (4 * ord up (m + 1)) := by
  cases up <;> simp only [ord, Bool.false_eq_true, ite_false, ite_true] <;>
    apply BitVec.eq_of_toNat_eq <;> simp <;> omega

theorem round_step {sch : Reg} {S : Addr} {up : Bool} {s₀ : State} (E : CipherEnv sch S s₀) {i : Nat}
    (hi : i < 16) {u : State} (I : CInv sch S up s₀ i u) :
    WP isa (round sch up) u (fun u' => CInv sch S up s₀ (i + 1) u' ∧
      u'.zf = some (BitVec.ofNat 64 (16 - (i + 1)) == 0)) := by
  have hrd : u.rd = s₀.rd := by rw [I.upd]
  have hwr : u.wr = s₀.wr := by rw [I.upd]
  have hm : u.mem = s₀.mem := by rw [I.upd]
  have hsch : u.gpr sch = S := by
    rw [I.gpr _ E.neA (E.look.ne8) E.look.ne9 E.ne10 E.look.ne11]; exact E.look.hsch
  have ea := ea_p u sch S _ hsch I.rax
  have hR : InRegions (u.rd ++ u.wr) (u.ea { base := sch, index := some .rax, disp := Int.ofNat pOff }) 4 := by
    rw [ea, hrd, hwr]; exact E.rdP _ (ord_lt up (by omega))
  let P := u.mem.readW (u.ea { base := sch, index := some .rax, disp := Int.ofNat pOff }) 32
  have hP : P = pEntry (scheduleAt s₀.mem S) (ord up i) := by
    rw [pEntry_read _ _ (ord_lt up (by omega))]; simp only [P, ea, hm]
  let u₁ := u.setReg32 .r11 P
  let u₂ := (XOp.movq tmp .r11).exec u₁
  let u₃ := (XOp.bin .pxor xL tmp).exec u₂
  rw [round]
  apply WP.seq
  refine WP.of_runBlock ⟨u₃, ?_, ?_⟩
  · rw [loadP, List.cons_append, runBlock_cons, exec_mov32_mem hR, runStep_some]
    exact runXops [XOp.movq tmp .r11, XOp.bin .pxor xL tmp] u₁
  have x₃ : dword (u₃.xmm xL) 0 = dword (u.xmm xL) 0 ^^^ P := by
    simp (disch := decide) only [u₃, u₂, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, XBinOp.eval]
    rw [dword_xor, dword_movq _ _ P (by simp only [u₁, State.setReg32, gpr_setReg_self])]
    rfl
  have k₃ : ∀ d, d ≠ xL → d ≠ tmp → u₃.xmm d = u.xmm d := fun d h1 h2 => by
    simp only [u₃, u₂, u₁, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2, State.setReg32, xmm_setReg]
  have g₃ : ∀ g, g ≠ .r11 → u₃.gpr g = u.gpr g := fun g h => by
    simp only [u₃, u₂, u₁, XOp.exec, gpr_setXmm, State.setReg32, gpr_setReg_of_ne _ _ h]
  have up₃ : Upd u u₃ := by
    unfold Upd; simp only [u₃, u₂, u₁, XOp.exec, State.setXmm, State.setReg32, State.setReg]
  have LE : LookEnv sch S u₃ := by
    refine ⟨by rw [g₃ _ E.look.ne11, hsch], E.look.ne8, E.look.ne9, E.look.ne11, fun off h => ?_, ?_, ?_, ?_⟩
    · rw [show u₃.rd = s₀.rd by rw [up₃, hrd], show u₃.wr = s₀.wr by rw [up₃, hwr]]; exact E.look.rd off h
    · rw [k₃ _ (by decide) (by decide), I.xmm _ (by decide), E.look.ones]
    · rw [k₃ _ (by decide) (by decide), I.xmm _ (by decide), E.look.sixteen]
    · rw [k₃ _ (by decide) (by decide), I.xmm _ (by decide), E.look.low]
  apply WP.seq
  refine WP.mono (f_run LE) fun u₄ ⟨hf, O⟩ => ?_
  obtain ⟨u₅, r₅, xl₅, xr₅, k₅, rax₅, r10₅, z₅, g₅, up₅⟩ := roundTail_run u₄ up
  refine WP.of_runBlock ⟨u₅, r₅, ⟨by omega, ?_, ?_, ?_, fun d hd => ?_, fun g h1 h2 h3 h4 h5 => ?_, ?_⟩, ?_⟩
  · rw [rax₅, O.gpr _ (by decide) (by decide) (by decide), g₃ _ (by decide), I.rax, ord_next up hi]
  · rw [r10₅, O.gpr _ (by decide) (by decide) (by decide), g₃ _ (by decide), I.r10]
    apply BitVec.eq_of_toNat_eq; simp; omega
  · rw [iter_succ, ← I.halves, xl₅, xr₅, dword_xor, hf, O.xmm xR (by decide), O.xmm xL (by decide),
      k₃ xR (by decide) (by decide), show u₃.mem = s₀.mem by rw [up₃, hm], x₃, hP]
    simp only [roundStep]
    rw [BitVec.xor_comm]
  · have h1 : d ≠ xL := fun e => hd (by rw [e]; decide)
    have h2 : d ≠ xR := fun e => hd (by rw [e]; decide)
    have h3 : d ≠ tmp := fun e => hd (by rw [e]; decide)
    have hf' : d ∉ fXRegs := fun h => hd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    rw [k₅ _ h1 h2 h3, O.xmm _ hf', k₃ _ h1 h3, I.xmm _ hd]
  · rw [g₅ _ h1 h4, O.gpr _ h2 h3 h5, g₃ _ h5, I.gpr _ h1 h2 h3 h4 h5]
  · exact Upd.trans up₅ (Upd.trans O.eq (Upd.trans up₃ I.upd))
  · rw [z₅, O.gpr _ (by decide) (by decide) (by decide), g₃ _ (by decide), I.r10,
      show BitVec.ofNat 64 (16 - i) - 1 = BitVec.ofNat 64 (16 - (i + 1)) from by
        apply BitVec.eq_of_toNat_eq; simp; omega]


/-- Only the rounds' registers and the flags change. -/
structure COnly (s s' : State) : Prop where
  xmm : ∀ d, d ∉ cXRegs → s'.xmm d = s.xmm d
  gpr : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g
  upd : Upd s s'

/-- The P-array entry `i` into `tmp`, XORed into `d`. -/
theorem xorP_run {sch : Reg} {S : Addr} {s₀ : State} (E : CipherEnv sch S s₀) {t : State} (O : COnly s₀ t)
    {i : Nat} (hi : i < 18) {d : XReg} (hd : d ≠ tmp) :
    ∃ t', runBlock isa [.mov32 .r11 (.mem (mem sch (pOff + 4 * i))), .xop (.movq tmp .r11), bin .pxor d tmp] t =
        some t' ∧
      dword (t'.xmm d) 0 = dword (t.xmm d) 0 ^^^ pEntry (scheduleAt s₀.mem S) i ∧
      (∀ e, e ≠ d → e ≠ tmp → t'.xmm e = t.xmm e) ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  have hsch : t.gpr sch = S := by
    rw [O.gpr _ E.neA E.look.ne8 E.look.ne9 E.ne10 E.look.ne11]; exact E.look.hsch
  have ea : t.ea (mem sch (pOff + 4 * i)) = S + BitVec.ofNat 64 (4096 + 4 * i) := by
    simp only [State.ea, mem, hsch, Rc2.X86_64.offset_nat, pOff]
  have hR : InRegions (t.rd ++ t.wr) (t.ea (mem sch (pOff + 4 * i))) 4 := by
    rw [ea, show t.rd = s₀.rd by rw [O.upd], show t.wr = s₀.wr by rw [O.upd]]; exact E.rdP i hi
  let P := t.mem.readW (t.ea (mem sch (pOff + 4 * i))) 32
  let t₁ := t.setReg32 .r11 P
  let t₂ := (XOp.movq tmp .r11).exec t₁
  let t₃ := (XOp.bin .pxor d tmp).exec t₂
  refine ⟨t₃, ?_, ?_, fun e h1 h2 => ?_, fun g h => ?_, ?_⟩
  · rw [runBlock_cons, exec_mov32_mem hR, runStep_some]
    exact runXops [XOp.movq tmp .r11, XOp.bin .pxor d tmp] t₁
  · simp only [t₃, t₂, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne _ _ hd, XBinOp.eval]
    rw [dword_xor, dword_movq _ _ P (by simp only [t₁, State.setReg32, gpr_setReg_self]), pEntry_read _ _ hi]
    simp only [P, ea, show t.mem = s₀.mem by rw [O.upd]]
    rfl
  · simp only [t₃, t₂, t₁, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2, State.setReg32, xmm_setReg]
  · simp only [t₃, t₂, t₁, XOp.exec, gpr_setXmm, State.setReg32, gpr_setReg_of_ne _ _ h]
  · unfold Upd; simp only [t₃, t₂, t₁, XOp.exec, State.setXmm, State.setReg32, State.setReg]

theorem cipher_run {sch : Reg} {S : Addr} {s : State} (E : CipherEnv sch S s) (up : Bool) :
    WP isa (cipher sch up) s (fun s' =>
      dword (s'.xmm xR) 0 = (feistel (scheduleAt s.mem S) (ord up) (dword (s.xmm xL) 0) (dword (s.xmm xR) 0)).1 ∧
      dword (s'.xmm xL) 0 = (feistel (scheduleAt s.mem S) (ord up) (dword (s.xmm xL) 0) (dword (s.xmm xR) 0)).2 ∧
      COnly s s') := by
  rw [cipher]
  apply WP.seq
  let u₀ := (s.setReg32 .rax (if up then 0 else 68)).setReg32 .r10 16
  have I0 : CInv sch S up s 0 u₀ := by
    refine ⟨by omega, ?_, ?_, rfl, fun d _ => rfl, fun g h1 _ _ h4 _ => ?_, ?_⟩
    · simp only [u₀, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.rax ≠ Reg.r10 by decide), gpr_setReg_self]
      cases up <;> rfl
    · simp only [u₀, State.setReg32, gpr_setReg_self]; rfl
    · simp only [u₀, State.setReg32, gpr_setReg_of_ne _ _ h4, gpr_setReg_of_ne _ _ h1]
    · unfold Upd; simp only [u₀, State.setReg32, State.setReg]
  refine WP.of_runBlock ⟨u₀, ?_, ?_⟩
  · rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil]
  apply WP.seq
  refine WP.mono (WP.loop (M := isa) (Q := CInv sch S up s 16)
    (fun m u => ∃ i, i < 16 ∧ m = 16 - i ∧ CInv sch S up s i u) ?_ 16 u₀ ⟨0, by omega, rfl, I0⟩)
    fun v Iv => ?_
  · intro m u ⟨i, hi, hm, I⟩
    refine WP.mono (round_step E hi I) fun u' ⟨I', zu⟩ => ?_
    have ev : isa.eval .ne u' = some (!(BitVec.ofNat 64 (16 - (i + 1)) == 0)) := by
      show u'.zf.map (!·) = _; rw [zu]; rfl
    by_cases h : i + 1 = 16
    · left; exact ⟨by rw [ev, h]; rfl, h ▸ I'⟩
    · right
      have nz : BitVec.ofNat 64 (16 - (i + 1)) ≠ 0 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
      exact ⟨by rw [ev, show (BitVec.ofNat 64 (16 - (i + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
        16 - (i + 1), by omega, i + 1, by omega, rfl, I'⟩
  have Ov : COnly s v := ⟨Iv.xmm, Iv.gpr, Iv.upd⟩
  obtain ⟨w₁, r₁, x₁, k₁, g₁, u₁⟩ := xorP_run E Ov (i := ord up 16) (ord_lt up (by decide)) (d := xL) (by decide)
  have O₁ : COnly s w₁ := ⟨fun d hd => by
      rw [k₁ _ (fun e => hd (by rw [e]; decide)) (fun e => hd (by rw [e]; decide)), Iv.xmm d hd],
    fun g h1 h2 h3 h4 h5 => by rw [g₁ _ h5, Iv.gpr _ h1 h2 h3 h4 h5], Upd.trans u₁ Iv.upd⟩
  obtain ⟨w₂, r₂, x₂, k₂, g₂, u₂⟩ := xorP_run E O₁ (i := ord up 17) (ord_lt up (by decide)) (d := xR) (by decide)
  refine WP.of_runBlock ⟨w₂, ?_, ?_, ?_, ?_⟩
  · have e1 : pOff + 4 * (if up then 16 else 1) = pOff + 4 * ord up 16 := by cases up <;> rfl
    have e2 : pOff + 4 * (if up then 17 else 0) = pOff + 4 * ord up 17 := by cases up <;> rfl
    rw [e1, e2]
    exact cat_run r₁ r₂
  · rw [x₂, k₁ _ (by decide) (by decide), feistel_eq, ← Iv.halves]
  · rw [k₂ _ (by decide) (by decide), x₁, feistel_eq, ← Iv.halves]
  · exact ⟨fun d hd => by
      rw [k₂ _ (fun e => hd (by rw [e]; decide)) (fun e => hd (by rw [e]; decide)), O₁.xmm d hd],
    fun g h1 h2 h3 h4 h5 => by rw [g₂ _ h5, O₁.gpr _ h1 h2 h3 h4 h5], Upd.trans u₂ O₁.upd⟩


end VG.Proof.Blowfish.X86_64
