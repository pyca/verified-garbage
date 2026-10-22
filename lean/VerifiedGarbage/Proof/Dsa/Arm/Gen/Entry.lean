module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Steps
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the entry

`entry_vp`: from the frame just allocated, the callee-saved registers, `out`
and its length, the first seed, all seeds left, the witnesses, `scratch`,
nothing read and `fStatus` = 0 in the frame (`GI` with `eV`, `eLS`), `r2`
(`p_len`) kept.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Arm.FrameStack
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_str wp_mov op2_imm)
open VG.Proof.Rsa.Arm.Recover (VP)

/-! ## Words written at offsets of a base -/

/-- `m` with the words `l` written at offsets of `B`, the last first. -/
def wmem (m : Mem) (B : Addr) : List (Nat × BitVec 32) → Mem
  | [] => m
  | (o, v) :: l => (wmem m B l).writeW (B + BitVec.ofNat 64 o) v

theorem wmem_head (m : Mem) (B : Addr) (o : Nat) (v : BitVec 32) (l : List (Nat × BitVec 32)) :
    (wmem m B ((o, v) :: l)).readW (B + BitVec.ofNat 64 o) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

theorem wmem_cons_sep (m : Mem) (B : Addr) {o d : Nat} (v : BitVec 32) (l : List (Nat × BitVec 32))
    (h : d + 4 ≤ o ∨ o + 4 ≤ d) (ho : o + 4 ≤ 4096) (hd : d + 4 ≤ 4096) :
    (wmem m B ((o, v) :: l)).readW (B + BitVec.ofNat 64 d) 32 = (wmem m B l).readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep B h (by omega) (by omega)) (by decide)

theorem wmem_sep (m : Mem) (B : Addr) {d : Nat} (hd : d + 4 ≤ 4096) :
    ∀ l : List (Nat × BitVec 32), (∀ q ∈ l, (d + 4 ≤ q.1 ∨ q.1 + 4 ≤ d) ∧ q.1 + 4 ≤ 4096) →
      (wmem m B l).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32
  | [], _ => rfl
  | (o, v) :: l, h => by
    have := h (o, v) List.mem_cons_self
    rw [wmem_cons_sep m B v l this.1 this.2 hd]
    exact wmem_sep m B hd l fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem wmem_frame (m : Mem) (B : Addr) {R : Region} (hR : ∀ o < 128, o % 4 = 0 → R.Contains (B + BitVec.ofNat 64 o) 4) :
    ∀ l : List (Nat × BitVec 32), (∀ q ∈ l, q.1 < 128 ∧ q.1 % 4 = 0) → Frame [R] m (wmem m B l)
  | [], _ => Frame.refl _ _
  | (o, v) :: l, h => by
    have := h (o, v) List.mem_cons_self
    exact (wmem_frame m B hR l fun q hq => h q (List.mem_cons_of_mem _ hq)).writeW List.mem_cons_self _
      (hR o this.1 this.2)

/-! ## The entry's frame words -/

/-- The variable frame words the entry writes. -/
abbrev eLS : List Nat := [fStatus, fUsed, fSeedLeft, fSeed]

/-- Their values. -/
def eV (G : GP) : Nat → BitVec 32 := fun o =>
  if o = fSeed then G.seeds else if o = fSeedLeft then BitVec.ofNat 32 G.seedsLen else 0

theorem eV_fStatus (G : GP) : eV G fStatus = 0 := by simp [eV, fStatus, fSeed, fSeedLeft]
theorem eV_fUsed (G : GP) : eV G fUsed = 0 := by simp [eV, fUsed, fSeed, fSeedLeft]
theorem eV_fSeedLeft (G : GP) : eV G fSeedLeft = BitVec.ofNat 32 G.seedsLen := by simp [eV, fSeed, fSeedLeft]
theorem eV_fSeed (G : GP) : eV G fSeed = G.seeds := by simp [eV]

/-- The words after the saved registers. -/
def eWords (σ : State) : List (Nat × BitVec 32) :=
  [(fStatus, 0), (fUsed, 0), (fScratch, stackArg σ 6), (fWitLen, stackArg σ 5), (fWit, stackArg σ 4),
    (fSeedLeft, stackArg σ 1), (fSeed, stackArg σ 0), (fOutLen, σ.gpr .r1), (fOut, σ.gpr .r0)]

/-- During the entry: the frame allocated, `r12` its base, memory changed in the frame alone. -/
structure EI (σ : State) (s : State) : Prop where
  sp : s.sp = (mkG σ).sp
  rd : s.rd = σ.rd
  wr : s.wr = (mkG σ).rFrame :: σ.wr
  r12 : s.gpr .r12 = (mkG σ).sp
  frame : Frame [(mkG σ).rFrame] σ.mem s.mem

section
variable {σ s : State} {rest : List Instr} {Q : State → Prop}

theorem CIn.spN (h : CIn σ) : (mkG σ).sp.toNat = σ.sp.toNat - F := by
  have := h.spLo; show (σ.sp - BitVec.ofNat 32 F).toNat = _
  exact sub_toNat' (by simp only [F]; omega)

theorem EI.st (h : EI σ s) (hpre : CIn σ) {o : Nat} (ho : o + 4 ≤ F) (r : Reg)
    (k : ∀ t, Mupd s t (s.mem.writeW (State.addr (mkG σ).sp + BitVec.ofNat 64 o) (s.gpr r)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r12 o :: rest)) s Q := by
  have := hpre.spN; have := hpre.spLo; have := hpre.spHi
  exact wp_str (by simp only [F] at ho; omega) (by rw [h.r12]; exact addr_add (by simp only [F] at *; omega))
    ⟨(mkG σ).rFrame, by rw [h.wr]; exact List.mem_cons_self, Offset.contains_base _ ho (by simp only [F] at *; omega)⟩ k

theorem EI.of_st (h : EI σ s) (hpre : CIn σ) {o : Nat} (ho : o + 4 ≤ F) {t : State} {v : BitVec 32}
    (m : Mupd s t (s.mem.writeW (State.addr (mkG σ).sp + BitVec.ofNat 64 o) v)) : EI σ t := by
  have := hpre.spN; have := hpre.spLo; have := hpre.spHi
  exact ⟨m.sp.trans h.sp, m.rd.trans h.rd, m.wr.trans h.wr, by rw [m.gpr]; exact h.r12, by
    rw [m.mem]; exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ ho (by simp only [F] at *; omega))⟩

theorem EI.of_upd (h : EI σ s) {t : State} {r : Reg} {v : BitVec 32} (u : Upd s t r v) (hr : r ≠ .r12) : EI σ t :=
  ⟨u.sp.trans h.sp, u.rd.trans h.rd, u.wr.trans h.wr, (u.other _ (Ne.symm hr)).trans h.r12, u.mem ▸ h.frame⟩

/-- `ldr r, [sp, #arg i]`: the stack argument `i`. -/
theorem EI.ldArg (h : EI σ s) (hpre : CIn σ) {i : Nat} (hi : i < 8) (r : Reg)
    (k : ∀ t, Upd s t r (stackArg σ i) → WP isa (.block rest) t Q) :
    WP isa (.block (.ldrSp r (arg i) :: rest)) s Q := by
  have := hpre.spLo; have := hpre.spHi
  have ha : State.addr (s.sp + BitVec.ofNat 32 (arg i)) = State.addr (σ.sp + BitVec.ofNat 32 (4 * i)) := by
    rw [h.sp, show (mkG σ).sp = σ.sp - BitVec.ofNat 32 F from rfl, show arg i = F + 4 * i from rfl,
      BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have sub : Region.Sub ⟨State.addr (σ.sp + BitVec.ofNat 32 (4 * i)), 4⟩ (mkG σ).rArgs := by
    show Region.Sub _ ⟨State.addr (σ.sp + BitVec.ofNat 32 (4 * 0)), 32⟩
    rw [Nat.mul_zero, BitVec.add_zero, addr_add (by omega)]
    exact Offset.sub_base _ (by omega)
  have con : (mkG σ).rArgs.Contains (State.addr (σ.sp + BitVec.ofNat 32 (4 * i))) 4 := by
    show Region.Contains ⟨State.addr (σ.sp + BitVec.ofNat 32 (4 * 0)), 32⟩ _ _
    rw [Nat.mul_zero, BitVec.add_zero, addr_add (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)
  refine VG.Proof.Bignum.Arm.wp_loadStack (by simp only [arg, F]; omega) ha
    ⟨(mkG σ).rArgs, List.mem_append_left _ (by
      rw [h.rd, hpre.rd]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))), con⟩
    fun t u => k t ?_
  have e : s.mem.readW (State.addr (σ.sp + BitVec.ofNat 32 (4 * i))) 32 = stackArg σ i :=
    h.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have fs : Region.Sub (mkG σ).rFrame (rStack σ) := by
        show Region.Sub ⟨State.addr (σ.sp - BitVec.ofNat 32 F), F⟩ _
        rw [addr_sub' (by simp only [F]; omega)]
        exact Offset.sub_below _ (by simp only [F]; omega) (by simp only [F]; omega)
      exact (hpre.fA.sub_left fs).symm.sub_left sub) (by decide)
  rwa [e] at u

end

theorem saved_ne12 : ∀ p ∈ VG.Impl.Dsa.Arm.Generation.saved, p.1 ≠ .r12 := by decide

/-- The entry, from the frame just allocated. -/
theorem entry_ok {σ : State} (hpre : CIn σ) :
    WP isa (.block entry) (allocated F σ) fun t =>
      GI (mkG σ) σ (eV (mkG σ)) eLS t ∧ t.gpr .r2 = σ.gpr .r2 := by
  have spN := hpre.spN; have spLo := hpre.spLo; have spHi := hpre.spHi
  -- The frame's words are in the frame.
  have inF : ∀ o, o + 4 ≤ F → (mkG σ).rFrame.Contains (State.addr (mkG σ).sp + BitVec.ofNat 64 o) 4 :=
    fun o ho => Offset.contains_base _ ho (by simp only [F] at *; omega)
  unfold entry
  rw [List.singleton_append,
    show VG.Impl.Dsa.Arm.Generation.saved.map (fun (r, o) => Instr.str r .r12 o) =
      VG.Impl.Dsa.Arm.Generation.saved.map (fun p => Instr.str p.1 .r12 p.2) from rfl]
  refine VG.Proof.Bignum.Arm.wp_stackAddr (r := .r12) (d := 0) (by decide) fun u₁ h0 => ?_
  have e1 : EI σ u₁ := ⟨h0.sp, h0.rd, h0.wr, by rw [h0.gpr, BitVec.add_zero]; rfl, by rw [h0.mem]; exact Frame.refl _ _⟩
  refine Spill.saveList_ok _ _ _ (fun p hp => by
      have := saved_ok p hp
      refine ⟨by omega, by rw [e1.r12, spN]; simp only [F] at *; omega, ⟨(mkG σ).rFrame, by rw [e1.wr]; exact List.mem_cons_self, by
        rw [e1.r12]; exact inF p.2 (by simp only [F]; omega)⟩⟩)
    fun u₂ gp₂ rd₂ wr₂ sp₂ mm₂ => ?_
  have mem₂ : u₂.mem = Spill.saveMem σ.mem (State.addr (mkG σ).sp) σ.gpr VG.Impl.Dsa.Arm.Generation.saved := by
    rw [mm₂, e1.r12, h0.mem]
    exact Spill.saveMem_congr _ _ _ fun p hp => h0.other _ (saved_ne12 p hp)
  have e2 : EI σ u₂ := ⟨sp₂.trans e1.sp, rd₂.trans e1.rd, wr₂.trans e1.wr, by rw [gp₂]; exact e1.r12, by
    rw [mem₂]; exact Spill.saveMem_frame_of _ _ List.mem_cons_self _ _ fun p hp =>
      inF p.2 (by have := saved_ok p hp; simp only [F]; omega)⟩
  have g₂ : ∀ r, r ≠ .r12 → u₂.gpr r = σ.gpr r := fun r hr => by rw [gp₂]; exact h0.other _ hr
  refine e2.st hpre (o := fOut) (by decide) .r0 fun u₃ m₃ => ?_
  have e3 := e2.of_st hpre (by decide) m₃
  refine e3.st hpre (o := fOutLen) (by decide) .r1 fun u₄ m₄ => ?_
  have e4 := e3.of_st hpre (by decide) m₄
  refine e4.ldArg hpre (i := 0) (by decide) .r1 fun u₅ v₅ => ?_
  have e5 := e4.of_upd v₅ (by decide)
  refine e5.st hpre (o := fSeed) (by decide) .r1 fun u₆ m₆ => ?_
  have e6 := e5.of_st hpre (by decide) m₆
  refine e6.ldArg hpre (i := 1) (by decide) .r1 fun u₇ v₇ => ?_
  have e7 := e6.of_upd v₇ (by decide)
  refine e7.st hpre (o := fSeedLeft) (by decide) .r1 fun u₈ m₈ => ?_
  have e8 := e7.of_st hpre (by decide) m₈
  refine e8.ldArg hpre (i := 4) (by decide) .r1 fun u₉ v₉ => ?_
  have e9 := e8.of_upd v₉ (by decide)
  refine e9.st hpre (o := fWit) (by decide) .r1 fun u₁₀ m₁₀ => ?_
  have e10 := e9.of_st hpre (by decide) m₁₀
  refine e10.ldArg hpre (i := 5) (by decide) .r1 fun u₁₁ v₁₁ => ?_
  have e11 := e10.of_upd v₁₁ (by decide)
  refine e11.st hpre (o := fWitLen) (by decide) .r1 fun u₁₂ m₁₂ => ?_
  have e12 := e11.of_st hpre (by decide) m₁₂
  refine e12.ldArg hpre (i := 6) (by decide) .r1 fun u₁₃ v₁₃ => ?_
  have e13 := e12.of_upd v₁₃ (by decide)
  refine e13.st hpre (o := fScratch) (by decide) .r1 fun u₁₄ m₁₄ => ?_
  have e14 := e13.of_st hpre (by decide) m₁₄
  refine wp_mov (d := .r1) (op2_imm (by decide)) fun u₁₅ v₁₅ => ?_
  have e15 := e14.of_upd v₁₅ (by decide)
  refine e15.st hpre (o := fUsed) (by decide) .r1 fun u₁₆ m₁₆ => ?_
  have e16 := e15.of_st hpre (by decide) m₁₆
  refine e16.st hpre (o := fStatus) (by decide) .r1 fun u₁₇ m₁₇ => WP.block_nil ?_
  have e17 := e16.of_st hpre (by decide) m₁₇
  -- The frame's words.
  have hmem : u₁₇.mem = wmem u₂.mem (State.addr (mkG σ).sp) (eWords σ) := by
    rw [m₁₇.mem, m₁₆.mem, v₁₅.mem, m₁₄.mem, v₁₃.mem, m₁₂.mem, v₁₁.mem, m₁₀.mem, v₉.mem, m₈.mem, v₇.mem, m₆.mem,
      v₅.mem, m₄.mem, m₃.mem, m₁₆.gpr, v₁₅.gpr, v₁₃.gpr, v₁₁.gpr, v₉.gpr, v₇.gpr, v₅.gpr, m₃.gpr,
      g₂ _ (by decide), g₂ _ (by decide)]
    rfl
  have rd : ∀ d, d + 4 ≤ F → d % 4 = 0 → fw u₁₇.mem (mkG σ) d = (wmem u₂.mem (State.addr (mkG σ).sp) (eWords σ)).readW
      (State.addr (mkG σ).sp + BitVec.ofNat 64 d) 32 := fun d _ _ => by rw [hmem]
  refine ⟨⟨hpre, rfl, e17.sp, e17.rd, e17.wr, fun p hp => ?_, fun p hp => ?_, fun o ho => ?_, fun o ho => ?_,
    e17.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp⟩, ?_⟩
  · -- The saved registers.
    have hb := saved_ok p hp
    show u₁₇.mem.readW _ 32 = _
    rw [hmem, wmem_sep _ _ (by omega) _ fun q hq => ?_, mem₂]
    · exact Spill.saveMem_saved (lo := 0) (hi := 36) _ _ _ _ (by decide) p hp
    · simp only [eWords, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨Or.inl (Nat.le_trans hb.1 (by dsimp only; decide)), by dsimp only; decide⟩
  · simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
    show u₁₇.mem.readW _ 32 = _
    rw [hmem]
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [eWords, wmem_cons_sep, wmem_head]
    · rfl
    · show σ.gpr .r1 = BitVec.ofNat 32 (σ.gpr .r1).toNat
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rfl
    · rfl
    · show stackArg σ 5 = BitVec.ofNat 32 (stackArg σ 5).toNat
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [eLS, List.mem_cons, List.not_mem_nil, or_false] at ho
    show u₁₇.mem.readW _ 32 = _
    rw [hmem]
    rcases ho with rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [eWords, wmem_cons_sep, wmem_head]
    · rw [eV_fStatus]
    · rw [eV_fUsed]
    · rw [eV_fSeedLeft]; show stackArg σ 1 = BitVec.ofNat 32 (stackArg σ 1).toNat
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [eV_fSeed]; rfl
  · simp only [eLS, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> exact varOk_of (by decide)
  · rw [m₁₇.gpr, m₁₆.gpr, v₁₅.other _ (by decide), m₁₄.gpr, v₁₃.other _ (by decide), m₁₂.gpr,
      v₁₁.other _ (by decide), m₁₀.gpr, v₉.other _ (by decide), m₈.gpr, v₇.other _ (by decide), m₆.gpr,
      v₅.other _ (by decide), m₄.gpr, m₃.gpr, g₂ _ (by decide)]

end VG.Proof.Dsa.Arm.Gen
