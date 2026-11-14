module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Base
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter search on RISC-V: a state of the search

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Frame.lean`). `GI G STK σ V LS s`: a
state of the search for the call from `σ` (with the parameters `G`, and
`STK` bytes of stack for the functions we call): `s6` holds `scratch`, whose
header holds our caller's callee-saved registers, our return address, the
fixed words (`fixedWords`) and the words of `LS` holding `V`; the regions
are the call's, and memory changed only in `scratch` and the stack below the
stack pointer. Loads of header words (`GI.ldV`), stores into its variable
words (`GI.stF`), and steps that keep a search state: those that change
registers alone (`GI.of_keep`) or memory in `scratch` past the header
(`GI.of_scr`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The header's end: the state, then the saved registers. -/
def hEnd : Nat := fSave + 8 * 12

/-- The header word at `o`. -/
abbrev fw (m : Mem) (G : GP) (o : Nat) : BitVec 64 := m.readW (G.scr + BitVec.ofNat 64 o) 64

/-- The fixed header words: `out`, the tape, `used`, `state` and `scratch_len`. -/
def fixedWords (G : GP) : List (Nat × BitVec 64) :=
  [(fOut, G.out), (fWit, G.rand), (fWitLen, BitVec.ofNat 64 G.randLen), (fUsedArg, G.used), (fState, G.state),
    (fScrLen, BitVec.ofNat 64 G.scrLen)]

/-- A variable header word: before the saved registers, apart from the return
address and the fixed words. -/
abbrev VarOk (G : GP) (o : Nat) : Prop := o + 8 ≤ fSave ∧ o % 8 = 0 ∧ o ≠ fRA ∧ ∀ p ∈ fixedWords G, o ≠ p.1

/-- `V` with the word at `o` := `v`. -/
def upd (V : Nat → BitVec 64) (o : Nat) (v : BitVec 64) : Nat → BitVec 64 := fun o' => if o' = o then v else V o'

@[simp] theorem upd_self (V : Nat → BitVec 64) (o : Nat) (v : BitVec 64) : upd V o v o = v := by simp [upd]
theorem upd_ne (V : Nat → BitVec 64) {o o' : Nat} (v : BitVec 64) (h : o' ≠ o) : upd V o v o' = V o' := by
  simp [upd, h]

/-- A state of the search. -/
structure GI (G : GP) (STK : Nat) (σ : State) (V : Nat → BitVec 64) (LS : List Nat) (s : State) : Prop where
  pre : CIn STK σ
  hG : mkG σ = G
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  s6 : s.gpr .s6 = G.scr
  saved : ∀ i < 12, fw s.mem G (fSave + 8 * i) = σ.gpr (saved.getD i .s0)
  ra : fw s.mem G fRA = σ.gpr .ra
  fixed : ∀ p ∈ fixedWords G, fw s.mem G p.1 = p.2
  slots : ∀ o ∈ LS, fw s.mem G o = V o
  ls : ∀ o ∈ LS, VarOk G o
  frame : Frame [G.rScr, rBelow σ STK] σ.mem s.mem

/-- A run keeps the stack pointer. -/
theorem WP.sp_eq {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s fun t => t.sp = s.sp → Q t) :
    WP isa c s Q := by
  obtain ⟨tr, s', he, hq⟩ := h; exact ⟨tr, s', he, hq (Exec.sp he)⟩

section
variable {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}

theorem GI.scrFit (h : GI G STK σ V LS s) : G.scr.toNat + G.scrLen * 8 ≤ 2 ^ 64 := by
  have := h.pre.nC; rw [← h.hG]; exact this

theorem GI.scrAl (h : GI G STK σ V LS s) : G.scr.toNat % 8 = 0 := by
  have := h.pre.alC; rw [← h.hG]; exact this

theorem GI.lens (h : GI G STK σ V LS s) : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by
  have := h.pre.lens; rw [h.hG] at this
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this
  omega

/-- `scratch`'s size. -/
theorem GI.scrBig (h : GI G STK σ V LS s) : 8 * (64 * G.pLen + 1024) ≤ G.scrLen * 8 := by
  have := h.pre.scrLen
  rw [h.hG] at this
  simp only [Spec.Dsa.generationScratchWords] at this
  omega

/-- Byte `o` of `scratch`. -/
abbrev GP.sa (G : GP) (o : Nat) : Addr := G.scr + BitVec.ofNat 64 o
/-- The `n` bytes at byte `o` of `scratch`. -/
abbrev GP.rs (G : GP) (o n : Nat) : Region := ⟨G.sa o, n⟩

/-- A range of `scratch` is writable. -/
theorem sw (G : GP) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) : Region.Sub (G.rs o n) G.rScr :=
  Offset.sub_base _ ho

theorem GI.inScr (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) (hn : 0 < n := by decide) :
    InRegions s.wr (G.sa o) n := by
  have := h.scrFit
  refine ⟨G.rScr, ?_, Offset.contains_base _ ho (by omega)⟩
  rw [h.wr, h.pre.wr, h.hG]; simp

theorem GI.inRdWr (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) (hn : 0 < n := by decide) :
    InRegions (s.rd ++ s.wr) (G.sa o) n := by
  obtain ⟨r, hr, hc⟩ := h.inScr ho hn
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- A word of `scratch` at an offset that is a multiple of 8 is aligned. -/
theorem GI.al8 (h : GI G STK σ V LS s) {o : Nat} (ho : o % 8 = 0) (hon : o + 8 ≤ G.scrLen * 8) :
    (G.sa o).toNat % 8 = 0 := by
  have f := h.scrFit; have a := h.scrAl
  have e : (G.sa o).toNat = G.scr.toNat + o := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e]; omega

/-- Ranges of `scratch` apart by their offsets are disjoint. -/
theorem GI.sdisj (h : GI G STK σ V LS s) {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o)
    (h1 : o + n ≤ G.scrLen * 8) (h2 : o' + n' ≤ G.scrLen * 8) :
    (G.rs o n).Disjoint (G.rs o' n') := by
  have := h.scrFit
  exact Offset.disjoint _ hs (by omega) (by omega)

/-- `scratch` is apart from the stack below the stack pointer. -/
theorem GI.scr_below (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) :
    (G.rs o n).Disjoint (rBelow σ STK) := by
  have := h.pre.bC; rw [h.hG] at this
  exact this.symm.sub_left (sw G ho)

theorem GI.hEnd_le (h : GI G STK σ V LS s) : hEnd ≤ G.scrLen * 8 := by
  have := h.scrBig; simp only [hEnd, fSave]; omega

/-- A header word's value. -/
theorem GI.fixedV (h : GI G STK σ V LS s) {o : Nat} {v : BitVec 64} (hp : (o, v) ∈ fixedWords G) :
    fw s.mem G o = v := h.fixed (o, v) hp

theorem GI.slotV (h : GI G STK σ V LS s) {o : Nat} (ho : o ∈ LS) : fw s.mem G o = V o := h.slots o ho

/-- `ld t, o(s6)` of a header word whose value `v` is known. -/
theorem GI.ldV (h : GI G STK σ V LS s) {o : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) {v : BitVec 64}
    (hv : fw s.mem G o = v) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t v → WP isa (.block rest) s' Q) : WP isa (.block (ld t o :: rest)) s Q := by
  have := h.hEnd_le
  refine wp_ld (by simp only [hEnd, fSave] at ho; omega) (by rw [h.s6]) (h.al8 h8 (by omega))
    (h.inRdWr (by omega)) fun s' u => k s' (by rw [← hv]; exact u)

/-- A state of the search through a step that changes registers other than
`s6` alone. -/
theorem GI.of_keep {t : State} {ws : List Reg} (h : GI G STK σ V LS s) (r : Keep ws s t) (m : t.mem = s.mem)
    (sp : t.sp = s.sp) (h6 : .s6 ∉ ws := by decide) : GI G STK σ V LS t :=
  ⟨h.pre, h.hG, sp.trans h.sp, r.2.1.trans h.rd, r.2.2.trans h.wr, (r.gpr h6).trans h.s6,
    by rw [m]; exact h.saved, by rw [m]; exact h.ra, by rw [m]; exact h.fixed, by rw [m]; exact h.slots,
    h.ls, by rw [m]; exact h.frame⟩

theorem GI.of_upd {t : State} {r : Reg} {v : BitVec 64} (h : GI G STK σ V LS s) (u : Upd s t r v)
    (h6 : r ≠ .s6) : GI G STK σ V LS t :=
  h.of_keep (ws := [r]) ⟨fun r' hr' => u.other r' (by simpa using hr'), u.rd, u.wr⟩ u.mem u.sp
    (by simpa using h6.symm)

/-- A header word keeps its value through writes outside the header. -/
theorem fw_frame {G : GP} {m m' : Mem} {rs : List Region} (f : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, (G.rs o 8).Disjoint r) : fw m' G o = fw m G o :=
  f.readW (r := G.rs o 8) (Region.contains_self _ _) hd (by decide)

theorem fixed_ok (G : GP) : ∀ p ∈ fixedWords G, p.1 + 8 ≤ fSave ∧ p.1 % 8 = 0 := by
  intro p hp
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

/-- A state of the search through a step that writes `scratch` past the
header and the stack below the stack pointer. -/
theorem GI.of_scr {t : State} {ws : List Reg} (h : GI G STK σ V LS s) (r : Keep ws s t) (sp : t.sp = s.sp)
    {o n : Nat} (ho : hEnd ≤ o) (hon : o + n ≤ G.scrLen * 8)
    (f : Frame [G.rs o n, rBelow σ STK] s.mem t.mem) (h6 : .s6 ∉ ws := by decide) : GI G STK σ V LS t := by
  have big := h.hEnd_le
  have hd : ∀ p, p + 8 ≤ hEnd → ∀ r ∈ [G.rs o n, rBelow σ STK], (G.rs p 8).Disjoint r := fun p hp r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.sdisj (.inl (by omega)) (by omega) hon
    · exact h.scr_below (by omega)
  refine ⟨h.pre, h.hG, sp.trans h.sp, r.2.1.trans h.rd, r.2.2.trans h.wr, (r.gpr h6).trans h.s6,
    fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, h.ls, h.frame.trans (f.sub fun x hx => ?_)⟩
  · rw [fw_frame f (hd _ (by simp only [hEnd]; omega))]; exact h.saved i hi
  · rw [fw_frame f (hd _ (by decide))]; exact h.ra
  · rw [fw_frame f (hd _ (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega))]; exact h.fixed p hp
  · rw [fw_frame f (hd _ (by have := (h.ls p hp).1; simp only [hEnd]; omega))]; exact h.slots p hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨G.rScr, List.mem_cons_self, sw G hon⟩
    · exact ⟨rBelow σ STK, by simp, fun _ h => h⟩

/-- `sd r, o(s6)` of a variable header word. -/
theorem GI.stF (h : GI G STK σ V LS s) {o : Nat} (hv : VarOk G o) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, GI G STK σ (upd V o (s.gpr r)) (o :: LS) t → Mupd s t (s.mem.writeW (G.sa o) (s.gpr r)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (st r o :: rest)) s Q := by
  obtain ⟨oS, o8, oRA, ofix⟩ := hv
  have big := h.hEnd_le
  have fit := h.scrFit
  refine wp_sd (by simp only [fSave] at oS; omega) (by rw [h.s6]) (h.al8 o8 (by simp only [hEnd] at big; omega))
    (h.inScr (by simp only [hEnd] at big; omega)) fun t m => k t ?_ m
  have mt : t.mem = s.mem.writeW (G.sa o) (s.gpr r) := m.mem
  have sep : ∀ {p : Nat}, p % 8 = 0 → p ≠ o → p + 8 ≤ hEnd → fw t.mem G p = fw s.mem G p := fun hp hne hpE => by
    show t.mem.readW _ 64 = s.mem.readW _ 64
    rw [mt]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by simp only [hEnd] at *; omega)
      (by simp only [hEnd, fSave] at *; omega)) (by decide)
  refine ⟨h.pre, h.hG, by rw [m.sp, h.sp], by rw [m.rd, h.rd], by rw [m.wr, h.wr],
    by rw [m.gpr, h.s6], fun i hi => ?_, ?_, fun p hp => ?_, fun o' ho' => ?_, fun o' ho' => ?_, ?_⟩
  · rw [sep (by simp only [fSave]; omega) (by simp only [fSave] at *; omega) (by simp only [hEnd]; omega)]
    exact h.saved i hi
  · rw [sep (by decide) (Ne.symm oRA) (by decide)]; exact h.ra
  · obtain ⟨b1, b2⟩ := fixed_ok G p hp
    exact (sep b2 (fun e => ofix p hp e.symm) (by simp only [hEnd]; omega)).trans (h.fixed p hp)
  · by_cases he : o' = o
    · subst he; show t.mem.readW _ 64 = _; rw [mt, Mem.readW_writeW_self64, upd_self]
    · have ho'' := (List.mem_cons.mp ho').resolve_left he
      obtain ⟨l1, l2, _, _⟩ := h.ls o' ho''
      rw [sep l2 he (by simp only [hEnd]; omega), upd_ne _ _ he]; exact h.slots o' ho''
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ⟨oS, o8, oRA, ofix⟩
    · exact h.ls o' ho'
  · rw [mt]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by simp only [hEnd] at big; omega)
      (by simp only [fSave] at oS; omega))

end

end VG.Proof.Dsa.RISCV64.PSearch
