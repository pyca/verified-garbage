module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Base
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: steps of the frame

Loads of frame words (`GI.ldV`, a stack argument `GI.argW`), stores into
the frame's variable words (`GI.stF`), and what keeps a search state: steps
that change registers alone (`GI.of_rest`) or memory in `scratch`
(`GI.of_scr`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Arm.FrameStack
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd)

/-- `V` with the word at `o` := `v`. -/
def upd (V : Nat → BitVec 32) (o : Nat) (v : BitVec 32) : Nat → BitVec 32 := fun o' => if o' = o then v else V o'

@[simp] theorem upd_self (V : Nat → BitVec 32) (o : Nat) (v : BitVec 32) : upd V o v o = v := by simp [upd]
theorem upd_ne (V : Nat → BitVec 32) {o o' : Nat} (v : BitVec 32) (h : o' ≠ o) : upd V o v o' = V o' := by
  simp [upd, h]

/-- A variable frame word: past the saved registers and apart from the fixed words. -/
abbrev VarOk (G : GP) (o : Nat) : Prop := 40 ≤ o ∧ o + 4 ≤ F ∧ o % 4 = 0 ∧ ∀ p ∈ fixedWords G, o ≠ p.1

section
variable {G : GP} {σ : State} {V : Nat → BitVec 32} {LS : List Nat} {s : State}

theorem GI.sp0 (h : GI G σ V LS s) : G.sp0 = σ.sp := by rw [← h.hG]; rfl

theorem GI.spN (h : GI G σ V LS s) : G.sp.toNat = σ.sp.toNat - F := by
  have := h.pre.spLo; show (G.sp0 - BitVec.ofNat 32 F).toNat = _; rw [h.sp0]
  exact sub_toNat' (by simp only [F]; omega)

theorem GI.spHi (h : GI G σ V LS s) : G.sp.toNat + F + 32 ≤ 2 ^ 32 := by
  have := h.pre.spHi; have := h.spN; have := h.pre.spLo; simp only [F] at *; omega

/-- The address of the frame word at `o`. -/
theorem GI.addr (h : GI G σ V LS s) {o : Nat} (ho : o < F + 32) :
    State.addr (s.sp + BitVec.ofNat 32 o) = State.addr G.sp + BitVec.ofNat 64 o := by
  have := h.spHi; rw [h.sp]; exact addr_add (by omega)

/-- A frame word or a stack argument is readable. -/
theorem GI.read (h : GI G σ V LS s) {o : Nat} (ho : o + 4 ≤ F + 32) (h4 : o % 4 = 0) :
    InRegions (s.rd ++ s.wr) (State.addr G.sp + BitVec.ofNat 64 o) 4 := by
  have spHi := h.spHi
  rcases (by simp only [F]; omega : o + 4 ≤ F ∨ F ≤ o) with c | c
  · exact ⟨G.rFrame, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self),
      Offset.contains_base _ c (by simp only [F] at *; omega)⟩
  · refine ⟨G.rArgs, List.mem_append_left _ (by rw [h.rd, h.pre.rd, h.hG]; simp), ?_⟩
    have e : State.addr G.sp + BitVec.ofNat 64 o = State.addr (G.sp0 + BitVec.ofNat 32 (4 * 0)) +
        BitVec.ofNat 64 (o - F) := by
      have spLo := h.pre.spLo; rw [← h.sp0] at spLo
      rw [Nat.mul_zero, BitVec.add_zero, show G.sp = G.sp0 - BitVec.ofNat 32 F from rfl,
        addr_sub' (by simp only [F]; omega), ← Offset.add_sub_comm, Offset.add_ofNat_sub _ c]
    rw [e]; exact Offset.contains_base _ (by simp only [F] at *; omega) (by omega)

/-- `ldr t, [sp, #o]` of a word whose value `v` is known. -/
theorem GI.ldV (h : GI G σ V LS s) {o : Nat} (ho : o + 4 ≤ F + 32) (h4 : o % 4 = 0) {v : BitVec 32}
    (hv : fw s.mem G o = v) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t v → WP isa (.block rest) s' Q) : WP isa (.block (.ldrSp t o :: rest)) s Q :=
  VG.Proof.Bignum.Arm.wp_loadStack (by simp only [F] at ho; omega) (h.addr (by omega)) (h.read ho h4)
    fun s' u => k s' (by rw [← hv]; exact u)

/-- The 304 bytes below the caller's stack pointer. -/
abbrev rStack (σ : State) : Region := ⟨State.addr σ.sp - 304#64, 304⟩

theorem GI.frameSub (h : GI G σ V LS s) : Region.Sub G.rFrame (rStack σ) := by
  have := h.pre.spLo
  show Region.Sub ⟨State.addr (G.sp0 - BitVec.ofNat 32 F), F⟩ _
  rw [h.sp0, addr_sub' (by simp only [F]; omega)]
  exact Offset.sub_below _ (by simp only [F]; omega) (by simp only [F]; omega)

theorem GI.belowSub (h : GI G σ V LS s) : Region.Sub G.rBelow (rStack σ) := by
  have := h.pre.spLo
  show Region.Sub ⟨State.addr (G.sp0 - BitVec.ofNat 32 F) - 176#64, 176⟩ _
  rw [h.sp0, addr_sub' (by simp only [F]; omega), BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by simp only [F]; omega) (by simp only [F]; omega)

/-- A stack argument's address. -/
theorem GI.argAddr (h : GI G σ V LS s) {j : Nat} (hj : j < 32) :
    State.addr G.sp + BitVec.ofNat 64 (F + j) = State.addr (σ.sp + BitVec.ofNat 32 j) := by
  have := h.pre.spLo; have := h.pre.spHi
  rw [show G.sp = G.sp0 - BitVec.ofNat 32 F from rfl, h.sp0, addr_sub' (by simp only [F]; omega),
    ← Offset.add_sub_comm, Offset.add_ofNat_sub _ (Nat.le_add_right F j), Nat.add_sub_cancel_left,
    addr_add (by omega)]

/-- The stack argument `i` keeps its value. -/
theorem GI.argW (h : GI G σ V LS s) {i : Nat} (hi : i < 8) : fw s.mem G (arg i) = stackArg σ i := by
  have pre := h.pre
  have := pre.spHi
  show s.mem.readW (State.addr G.sp + BitVec.ofNat 64 (F + 4 * i)) 32 =
    σ.mem.readW (State.addr (σ.sp + BitVec.ofNat 32 (4 * i))) 32
  rw [h.argAddr (by omega)]
  have sub : Region.Sub ⟨State.addr (σ.sp + BitVec.ofNat 32 (4 * i)), 4⟩ (mkG σ).rArgs := by
    show Region.Sub _ ⟨State.addr (σ.sp + BitVec.ofNat 32 (4 * 0)), 32⟩
    rw [addr_add (by omega), Nat.mul_zero, BitVec.add_zero]
    exact Offset.sub_base _ (by omega)
  refine h.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [GP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (pre.fA.sub_left h.frameSub).symm.sub_left sub
  · rw [← h.hG]; exact pre.cA.symm.sub_left sub
  · exact (pre.fA.sub_left h.belowSub).symm.sub_left sub

/-- Two frame words at distinct aligned offsets are separate. -/
theorem fw_sep (G : GP) {o p : Nat} (ho : o % 4 = 0) (hp : p % 4 = 0) (h : o ≠ p) (ho' : o + 4 ≤ F)
    (hp' : p + 4 ≤ F) :
    Mem.Sep (State.addr G.sp + BitVec.ofNat 64 p) (32 / 8) (State.addr G.sp + BitVec.ofNat 64 o) (32 / 8) :=
  Offset.sep _ (by simp only [F] at *; omega) (by simp only [F] at *; omega) (by simp only [F] at *; omega)

/-- A state of the search through a step that changes registers alone. -/
theorem GI.of_rest {t : State} {ws : List Reg} (h : GI G σ V LS s) (r : Rest ws s t) (m : t.mem = s.mem) :
    GI G σ V LS t :=
  ⟨h.pre, h.hG, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, by rw [m]; exact h.saved,
    by rw [m]; exact h.fixed, by rw [m]; exact h.slots, h.ls, by rw [m]; exact h.frame⟩

/-- The frame is apart from `scratch` and from the stack below it. -/
theorem GI.frame_scr (h : GI G σ V LS s) : G.rFrame.Disjoint G.rScr := by
  rw [← h.hG]; exact h.pre.fC.sub_left (by rw [h.hG]; exact h.frameSub)

theorem GI.frame_below (h : GI G σ V LS s) : G.rFrame.Disjoint G.rBelow := by
  have := h.spN; have := h.pre.spLo
  show Region.Disjoint ⟨State.addr G.sp, F⟩ ⟨State.addr G.sp - 176#64, 176⟩
  have := Offset.base_disjoint_below (State.addr G.sp) (n := 176) (k := F) (by simp only [F]; omega)
  exact this

/-- A frame word keeps its value through writes outside the frame. -/
theorem frame_readW {G : GP} {m m' : Mem} {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, G.rFrame.Disjoint r)
    {o : Nat} (ho : o + 4 ≤ F) : fw m' G o = fw m G o :=
  f.readW (r := ⟨State.addr G.sp + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ ho)) (by decide)

/-- A state of the search through a step that writes only `scratch` and the stack below the frame. -/
theorem GI.of_scr {t : State} {ws : List Reg} (h : GI G σ V LS s) (r : Rest ws s t)
    (f : Frame [G.rScr, G.rBelow] s.mem t.mem) : GI G σ V LS t := by
  have hd : ∀ r ∈ [G.rScr, G.rBelow], G.rFrame.Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.frame_scr, h.frame_below]
  refine ⟨h.pre, h.hG, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, fun p hp => ?_, fun p hp => ?_,
    fun o ho => ?_, h.ls, h.frame.trans (f.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)⟩
  · have hb : p.2 + 4 ≤ F := by
      simp only [VG.Impl.Dsa.Arm.Generation.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    show fw t.mem G p.2 = _
    rw [frame_readW f hd hb]; exact h.saved p hp
  · have hb : p.1 + 4 ≤ F := by
      simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
    rw [frame_readW f hd hb]; exact h.fixed p hp
  · rw [frame_readW f hd (h.ls o ho).2.1]; exact h.slots o ho

theorem fixed_ok (G : GP) : ∀ p ∈ fixedWords G, 40 ≤ p.1 ∧ p.1 + 4 ≤ F ∧ p.1 % 4 = 0 := by
  intro p hp
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

theorem saved_ok : ∀ p ∈ VG.Impl.Dsa.Arm.Generation.saved, p.2 + 4 ≤ 40 ∧ p.2 % 4 = 0 := by decide

/-- `str r, [sp, #o]` (through `r12`) of a variable frame word. -/
theorem GI.stF (h : GI G σ V LS s) {o : Nat} (hv : VarOk G o) {r : Reg} (hr : r ≠ .r12)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, GI G σ (upd V o (s.gpr r)) (o :: LS) t → Rest [.r12] s t → WP isa (.block rest) t Q) :
    WP isa (.block (st r o ++ rest)) s Q := by
  obtain ⟨o40, oF, o4, ofix⟩ := hv
  have spHi := h.spHi
  simp only [st, List.cons_append, List.nil_append]
  refine VG.Proof.Bignum.Arm.wp_stackAddr (r := .r12) (d := 0) (by decide) fun u h0 => ?_
  have ea : State.addr (u.gpr .r12 + BitVec.ofNat 32 o) = State.addr G.sp + BitVec.ofNat 64 o := by
    rw [h0.gpr, BitVec.add_zero, h.sp]; exact addr_add (by simp only [F] at *; omega)
  refine VG.Proof.X25519.Arm.wp_str (by simp only [F] at *; omega) ea
    ⟨G.rFrame, by rw [h0.wr, h.wr]; exact List.mem_cons_self, Offset.contains_base _ oF (by omega)⟩
    fun t m => k t ?_ ((h0.rest (by simp)).trans (m.rest _))
  have vr : u.gpr r = s.gpr r := h0.other _ hr
  have mt : t.mem = s.mem.writeW (State.addr G.sp + BitVec.ofNat 64 o) (s.gpr r) := by rw [m.mem, h0.mem, vr]
  have sep : ∀ {p : Nat}, p % 4 = 0 → p ≠ o → p + 4 ≤ F → fw t.mem G p = fw s.mem G p := fun hp hne hpF => by
    show t.mem.readW _ 32 = s.mem.readW _ 32
    rw [mt]; exact Mem.readW_writeW_sep (fw_sep G o4 hp (Ne.symm hne) oF hpF) (by decide)
  refine ⟨h.pre, h.hG, by rw [m.sp, h0.sp, h.sp], by rw [m.rd, h0.rd, h.rd], by rw [m.wr, h0.wr, h.wr],
    fun p hp => ?_, fun p hp => ?_, fun o' ho' => ?_, fun o' ho' => ?_, ?_⟩
  · obtain ⟨b, a4⟩ := saved_ok p hp
    have := sep (p := p.2) a4 (by omega) (by simp only [F]; omega)
    exact this.trans (h.saved p hp)
  · obtain ⟨b1, b2, b3⟩ := fixed_ok G p hp
    exact (sep b3 (fun e => ofix p hp e.symm) b2).trans (h.fixed p hp)
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · show t.mem.readW _ 32 = _
      rw [mt, Mem.readW_writeW_self32, upd_self]
    · by_cases he : o' = o
      · subst he; show t.mem.readW _ 32 = _; rw [mt, Mem.readW_writeW_self32, upd_self]
      · obtain ⟨_, l2, l3, _⟩ := h.ls o' ho'
        rw [sep l3 he l2, upd_ne _ _ he]; exact h.slots o' ho'
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ⟨o40, oF, o4, ofix⟩
    · exact h.ls o' ho'
  · rw [mt]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ oF (by omega))

end

end VG.Proof.Dsa.Arm.Gen
