module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Base
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: a state of the search

`GI G STK σ V LS s`: a state of the search for the call from `σ` (with the
parameters `G`, and `STK` bytes of stack for the functions we call): `r28`
holds `scratch`, whose header holds our caller's registers, our return
address, the fixed words (`fixedWords`) and the words of `LS` holding `V`;
the regions are the call's, and memory changed only in `scratch` and the
stack below the stack pointer. Loads of header words (`GI.ldV`), stores into
its variable words (`GI.stF`), and steps that keep a search state: those that
change registers alone (`GI.of_keep`) or memory in `scratch` past the header
(`GI.of_scr`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- The header's end: the state, then the saved registers. -/
def hEnd : Nat := fSave + 8 * 19

/-- The header word at `o`. -/
abbrev fw (m : Mem) (G : GP) (o : Nat) : BitVec 64 := m.readW (G.scr + BitVec.ofNat 64 o) 64

/-- The fixed header words: `out`, the witnesses and `hs`. -/
def fixedWords (G : GP) : List (Nat × BitVec 64) :=
  [(fOut, G.out), (fWit, G.wit), (fWitLen, BitVec.ofNat 64 G.witLen), (fHs, G.hs),
    (fHsLen, BitVec.ofNat 64 G.hsLen)]

/-- A variable header word: before the saved registers, apart from the return
address and the fixed words. -/
abbrev VarOk (G : GP) (o : Nat) : Prop := o + 8 ≤ fSave ∧ o % 8 = 0 ∧ o ≠ fLR ∧ ∀ p ∈ fixedWords G, o ≠ p.1

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
  r28 : s.gpr .r28 = G.scr
  saved : ∀ i < 19, fw s.mem G (fSave + 8 * i) = σ.gpr (saved.getD i .r14)
  lr : fw s.mem G fLR = σ.lr
  fixed : ∀ p ∈ fixedWords G, fw s.mem G p.1 = p.2
  slots : ∀ o ∈ LS, fw s.mem G o = V o
  ls : ∀ o ∈ LS, VarOk G o
  frame : Frame [G.rScr, rBelow σ STK] σ.mem s.mem

/-- A run keeps the stack pointer. -/
theorem WP.sp_eq {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s fun t => t.sp = s.sp → Q t) :
    WP isa c s Q := by
  obtain ⟨tr, s', he, hq⟩ := h; exact ⟨tr, s', he, hq (Exec.sp he)⟩

/-- `std t, off(n)`, with the stack pointer and the link register kept. -/
theorem wp_std' {s : State} {is : List Instr} {Q : State → Prop} {t n : Reg} {off : Nat} {a : Addr}
    (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → s'.sp = s.sp → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

section
variable {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}

theorem GI.scrFit (h : GI G STK σ V LS s) : G.scr.toNat + G.scrLen * 8 ≤ 2 ^ 64 := by
  have := h.pre.nC; rw [← h.hG]; exact this

theorem GI.lens (h : GI G STK σ V LS s) :
    (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32) := by
  rw [← h.hG]; exact h.pre.lens

/-- `scratch`'s size. -/
theorem GI.scrBig (h : GI G STK σ V LS s) : 8 * (64 * G.pLen + 1024) ≤ G.scrLen * 8 := by
  have := h.pre.scrLen
  have e1 : (σ.gpr .r5).toNat = G.pLen := by rw [← h.hG]; rfl
  have e2 : (stackArg σ 3).toNat = G.scrLen := by rw [← h.hG]; rfl
  rw [e1, e2] at this
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

/-- `ld t, o(r28)` of a header word whose value `v` is known. -/
theorem GI.ldV (h : GI G STK σ V LS s) {o : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) {v : BitVec 64}
    (hv : fw s.mem G o = v) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t v → WP isa (.block rest) s' Q) : WP isa (.block (ld t o :: rest)) s Q := by
  have := h.hEnd_le
  refine wp_ld (by decide) ⟨by simp only [hEnd, fSave] at ho; omega, by omega⟩ (by rw [h.r28])
    (h.inRdWr (by omega)) fun s' u => k s' (by rw [← hv]; exact u)

/-- A state of the search through a step that changes registers other than
`r28` alone. -/
theorem GI.of_keep {t : State} {ws : List Reg} (h : GI G STK σ V LS s) (r : Keep ws s t) (m : t.mem = s.mem)
    (sp : t.sp = s.sp) (h28 : .r28 ∉ ws := by decide) : GI G STK σ V LS t :=
  ⟨h.pre, h.hG, sp.trans h.sp, r.2.1.trans h.rd, r.2.2.trans h.wr, (r.gpr h28).trans h.r28,
    by rw [m]; exact h.saved, by rw [m]; exact h.lr, by rw [m]; exact h.fixed, by rw [m]; exact h.slots,
    h.ls, by rw [m]; exact h.frame⟩

theorem GI.of_upd {t : State} {r : Reg} {v : BitVec 64} (h : GI G STK σ V LS s) (u : Upd s t r v)
    (sp : t.sp = s.sp) (h28 : r ≠ .r28) : GI G STK σ V LS t :=
  h.of_keep (ws := [r]) ⟨fun r' hr' => u.other r' (by simpa using hr'), u.rd, u.wr⟩ u.mem sp
    (by simpa using h28.symm)

/-- A header word keeps its value through writes outside the header. -/
theorem fw_frame {G : GP} {m m' : Mem} {rs : List Region} (f : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, (G.rs o 8).Disjoint r) : fw m' G o = fw m G o :=
  f.readW (r := G.rs o 8) (Region.contains_self _ _) hd (by decide)

theorem fixed_ok (G : GP) : ∀ p ∈ fixedWords G, p.1 + 8 ≤ fSave ∧ p.1 % 8 = 0 := by
  intro p hp
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

/-- A state of the search through a step that writes `scratch` past the
header and the stack below the stack pointer. -/
theorem GI.of_scr {t : State} {ws : List Reg} (h : GI G STK σ V LS s) (r : Keep ws s t) (sp : t.sp = s.sp)
    {o n : Nat} (ho : hEnd ≤ o) (hon : o + n ≤ G.scrLen * 8)
    (f : Frame [G.rs o n, rBelow σ STK] s.mem t.mem) (h28 : .r28 ∉ ws := by decide) : GI G STK σ V LS t := by
  have big := h.hEnd_le
  have hd : ∀ p, p + 8 ≤ hEnd → ∀ r ∈ [G.rs o n, rBelow σ STK], (G.rs p 8).Disjoint r := fun p hp r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.sdisj (.inl (by omega)) (by omega) hon
    · exact h.scr_below (by omega)
  refine ⟨h.pre, h.hG, sp.trans h.sp, r.2.1.trans h.rd, r.2.2.trans h.wr, (r.gpr h28).trans h.r28,
    fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, h.ls, h.frame.trans (f.sub fun x hx => ?_)⟩
  · rw [fw_frame f (hd _ (by simp only [hEnd]; omega))]; exact h.saved i hi
  · rw [fw_frame f (hd _ (by decide))]; exact h.lr
  · rw [fw_frame f (hd _ (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega))]; exact h.fixed p hp
  · rw [fw_frame f (hd _ (by have := (h.ls p hp).1; simp only [hEnd]; omega))]; exact h.slots p hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨G.rScr, List.mem_cons_self, sw G hon⟩
    · exact ⟨rBelow σ STK, by simp, fun _ h => h⟩

/-- `std r, o(r28)` of a variable header word. -/
theorem GI.stF (h : GI G STK σ V LS s) {o : Nat} (hv : VarOk G o) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, GI G STK σ (upd V o (s.gpr r)) (o :: LS) t → Mupd s t (s.mem.writeW (G.sa o) (s.gpr r)) →
      t.lr = s.lr → WP isa (.block rest) t Q) :
    WP isa (.block (st r o :: rest)) s Q := by
  obtain ⟨oS, o8, oLR, ofix⟩ := hv
  have big := h.hEnd_le
  have fit := h.scrFit
  refine wp_std' (by decide) ⟨by simp only [fSave] at oS; omega, by omega⟩ (by rw [h.r28])
    (h.inScr (by simp only [hEnd] at big; omega)) fun t m tsp tlr => k t ?_ m tlr
  have mt : t.mem = s.mem.writeW (G.sa o) (s.gpr r) := m.mem
  have sep : ∀ {p : Nat}, p % 8 = 0 → p ≠ o → p + 8 ≤ hEnd → fw t.mem G p = fw s.mem G p := fun hp hne hpE => by
    show t.mem.readW _ 64 = s.mem.readW _ 64
    rw [mt]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by simp only [hEnd] at *; omega)
      (by simp only [hEnd, fSave] at *; omega)) (by decide)
  refine ⟨h.pre, h.hG, by rw [tsp, h.sp], by rw [m.rd, h.rd], by rw [m.wr, h.wr],
    by rw [m.gpr, h.r28], fun i hi => ?_, ?_, fun p hp => ?_, fun o' ho' => ?_, fun o' ho' => ?_, ?_⟩
  · rw [sep (by simp only [fSave]; omega) (by simp only [fSave] at *; omega) (by simp only [hEnd]; omega)]
    exact h.saved i hi
  · rw [sep (by decide) (Ne.symm oLR) (by decide)]; exact h.lr
  · obtain ⟨b1, b2⟩ := fixed_ok G p hp
    exact (sep b2 (fun e => ofix p hp e.symm) (by simp only [hEnd]; omega)).trans (h.fixed p hp)
  · by_cases he : o' = o
    · subst he; show t.mem.readW _ 64 = _; rw [mt, Mem.readW_writeW_self64, upd_self]
    · have ho'' := (List.mem_cons.mp ho').resolve_left he
      obtain ⟨l1, l2, _, _⟩ := h.ls o' ho''
      rw [sep l2 he (by simp only [hEnd]; omega), upd_ne _ _ he]; exact h.slots o' ho''
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ⟨oS, o8, oLR, ofix⟩
    · exact h.ls o' ho'
  · rw [mt]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by simp only [hEnd] at big; omega)
      (by simp only [fSave] at oS; omega))

end

end VG.Proof.Dsa.PPC64LE.Gen
