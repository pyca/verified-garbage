module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.St
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.VP
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter generation on PPC64LE: header words in pieces

`WP.wr`: an instruction that writes one register, with the stack pointer and
the link register kept. The taint analysis does not follow the header's
words, which the search keeps its state in: a load of one (`ld`) and a store
into one (`st`) leak only addresses from `r28`, which holds `scratch` in both
runs of the search, so they are analysed with `r28` public (`ld_vp`,
`st_vp`, `stImm_vp`, `cmpF_vp`), and the code between them with the registers
the loads set public (`VP.taint`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- An instruction that writes `v` to `d`. -/
theorem WP.wr {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 64}
    (h : exec i s = some (s.write d v))
    (k : ∀ s', Upd s s' d v → s'.sp = s.sp → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons h (k _ (Upd.write _ _ _) rfl rfl)

section
variable {G : GP} {STK : Nat}

/-- The stage's states hold `scratch` in `r28` and have the call's stack pointer. -/
abbrev Pub (G : GP) (F : State → State → Prop) : Prop :=
  ∀ σ s, F σ s → s.gpr .r28 = G.scr ∧ s.sp = G.sp

theorem SS.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G F := fun σ s h => ⟨(hF σ s h).gi.r28, by rw [(hF σ s h).gi.sp, ← (hF σ s h).gi.hG]; rfl⟩

/-- A piece analysed with `r28` and `rs` public. -/
theorem VP.pub {F Q : State → State → Prop} {c : Prog isa} (hp : Pub G F) (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs (.r28 :: rs)) c hc).isSome = true)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (Q σ)) : VP F c Q :=
  VP.taint (.r28 :: rs) cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [(hp _ _ h₁).2, (hp _ _ h₂).2])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [(hp _ _ h₁).1, (hp _ _ h₂).1]
      · exact regs _ _ _ _ h₁ h₂ r hr) wp

end

/-- `ld t, o(r28)` of a header word whose value `v` is known, keeping a stage. -/
theorem SS.ldK {G : GP} {STK : Nat} {σ s : State} {c : Cfg} (h : SS G STK σ c s) {o : Nat} (ho : o + 8 ≤ hEnd)
    (h8 : o % 8 = 0) {v : BitVec 64} (hv : fw s.mem G o = v) {t : Reg} (ht : t ≠ .r28) {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', SS G STK σ c s' → Upd s s' t v → WP isa (.block rest) s' Q) :
    WP isa (.block (ld t o :: rest)) s Q := by
  have hE := h.gi.hEnd_le
  refine WP.cons (s' := s.write t v) ?_ (k _ (h.of_upd (Upd.write _ _ _) rfl ht) (Upd.write _ _ _))
  rw [show ld t o = .load .d t .r28 o from rfl, exec_load_d (by decide) ⟨by simp only [hEnd, fSave] at ho; omega,
    by omega⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega)), h.gi.r28, ← hv]

/-! ## Header words as pieces -/

section
variable {G : GP} {STK : Nat}

/-- A load of a header word whose value both runs know. -/
theorem ld_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} (hr : r ≠ .r28) {o : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Upd s t r x → Q σ t) : VP P (.block [ld r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [ld r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have hE := h.gi.hEnd_le
  refine WP.cons (s' := s.write r x) ?_ (WP.block_nil (k σ s _ hs (h.of_upd (Upd.write _ _ _) rfl hr)
    (Upd.write _ _ _)))
  rw [show ld r o = .load .d r .r28 o from rfl, exec_load_d (by decide) ⟨by simp only [hEnd, fSave] at ho; omega,
    by omega⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega)), h.gi.r28, ← hx σ s hs]

/-- A store into a variable word of the header. -/
theorem st_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} {o : Nat} (hv : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (s.gpr r)) t → Keep [] s t → Q σ t) :
    VP P (.block [st r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [st r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  exact (hF σ s hs).stF hv fun t h m _ => WP.block_nil (k σ s t hs h ⟨fun r _ => by rw [m.gpr], m.rd, m.wr⟩)

/-- `stImm o v`: the header word `o` := `v`. -/
theorem stImm_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (hv : v < 2 ^ 15) (ho : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (BitVec.ofNat 64 v)) t → Keep [.r3] s t → Q σ t) :
    VP P (.block (stImm o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block (stImm o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  refine WP.wr (d := .r3) (exec_li hv) fun s₁ u₁ sp₁ _ => ?_
  have h₁ : SS G STK σ (c σ) s₁ := (hF σ s hs).of_upd u₁ sp₁ (by decide)
  refine h₁.stF ho fun t h m _ => WP.block_nil (k σ s t hs (by rw [u₁.gpr] at h; exact h) ?_)
  exact ⟨fun r hr => by rw [m.gpr, u₁.other _ (by simpa using hr)], by rw [m.rd, u₁.rd], by rw [m.wr, u₁.wr]⟩

theorem sub_beq_zero (x y : BitVec 64) : (x - y == 0) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0 := fun e => h (by rw [← BitVec.sub_add_cancel x y, e]; exact BitVec.zero_add y)
    rw [beq_false_of_ne this, beq_false_of_ne h]

/-- `cmpF o v`: `r0 = 0` iff the header word `o`, which both runs know, is `v`. -/
theorem cmpF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v ≤ 2 ^ 15) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.r0, .r3] s t →
      isa.eval (.zero .d .r0) t = some (x == BitVec.ofNat 64 v) → Q σ t) : VP P (.block (cmpF o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block (cmpF o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have hE := h.gi.hEnd_le
  refine WP.cons (s' := s.write .r3 x) ?_ ?_
  · rw [show ld .r3 o = .load .d .r3 .r28 o from rfl, exec_load_d (by decide)
      ⟨by simp only [hEnd, fSave] at ho; omega, by omega⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega)),
      h.gi.r28, ← hx σ s hs]
  refine WP.wr (exec_subi (by decide) hv) fun t u sp _ => WP.block_nil ?_
  have u₀ : Upd s (s.write .r3 x) .r3 x := Upd.write _ _ _
  refine k σ s t hs ((h.of_upd u₀ rfl (by decide)).of_upd u sp (by decide)) ?_ ?_
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u.other _ hr.1, u₀.other _ hr.2], by rw [u.rd, u₀.rd], by rw [u.wr, u₀.wr]⟩
  · rw [eval_zero, u.gpr, u₀.gpr, sub_beq_zero]

/-- `ltR`: `r0 = 0` iff `r3 < r4`, through the carry. -/
theorem ltR_ok {s : State} {rest : List Instr} {Q : State → Prop} {x y : BitVec 64} (h3 : s.gpr .r3 = x)
    (h4 : s.gpr .r4 = y)
    (k : ∀ t, Keep [.r0] s t → t.mem = s.mem → t.sp = s.sp → t.lr = s.lr →
      isa.eval (.zero .d .r0) t = some (decide (x.toNat < y.toNat)) → WP isa (.block rest) t Q) :
    WP isa (.block (ltR ++ rest)) s Q := by
  refine WP.cons exec_subc (WP.cons (exec_li (by decide)) (WP.cons exec_addze (k _ ?_ rfl rfl rfl ?_)))
  · refine ⟨fun r hr => ?_, rfl, rfl⟩
    have : r ≠ .r0 := by simpa using hr
    simp [State.writeCarry, State.write, this]
  · rw [eval_zero]
    simp only [State.writeCarry, State.write, ite_true, h3, h4]
    have hx := x.isLt
    have hy := y.isLt
    by_cases hl : x.toNat < y.toNat
    · simp [show ¬(2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - y.toNat) + 1) by omega, hl]
    · simp [show 2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - y.toNat) + 1 by omega, hl]

/-- `ld r3, o(r28); li r4, v; ltR`: `r0 = 0` iff the header word `o`, which
both runs know, is below `v`. -/
theorem ltF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v < 2 ^ 15) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.r0, .r3, .r4] s t →
      isa.eval (.zero .d .r0) t = some (decide (x.toNat < v)) → Q σ t) :
    VP P (.block ([ld .r3 o, .li .r4 v] ++ ltR)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block ([ld .r3 o, .li .r4 v] ++ ltR)), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => ?_
  have h := hF σ s hs
  refine h.ldK ho h8 (hx σ s hs) (by decide) fun s₁ h₁ u₁ => ?_
  refine WP.wr (d := .r4) (exec_li hv) fun s₂ u₂ sp₂ _ => ?_
  have h₂ := h₁.of_upd u₂ sp₂ (by decide)
  refine ltR_ok (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr fun t K m sp _ e => WP.block_nil ?_
  refine k σ s t hs (h₂.of_keep K m sp) ⟨fun r hr => ?_, by rw [K.2.1, u₂.rd, u₁.rd], by rw [K.2.2, u₂.wr, u₁.wr]⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K.gpr (by simpa using hr.1), u₂.other _ hr.2.2, u₁.other _ hr.2.1]
  · rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- An instruction that writes one register other than `r28` keeps a stage. -/
theorem SS.wrK {σ s : State} {c : Cfg} (h : SS G STK σ c s) {i : Instr} {d : Reg} {v : BitVec 64}
    (he : exec i s = some (s.write d v)) (hd : d ≠ .r28 := by decide) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', SS G STK σ c s' → Upd s s' d v → WP isa (.block rest) s' Q) : WP isa (.block (i :: rest)) s Q :=
  WP.wr he fun s' u sp _ => k s' (h.of_upd u sp hd) u

/-- `shl`: `r := v · 2^sh`. -/
theorem shl_ok {σ s : State} {c : Cfg} (h : SS G STK σ c s) {r : Reg} (hr : r ≠ .r28) {v sh : Nat}
    (hv : v < 2 ^ 15) (hsh : sh < 64) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', SS G STK σ c s' → Keep [r] s s' → s'.gpr r = BitVec.ofNat 64 (v * 2 ^ sh) → s'.mem = s.mem →
      WP isa (.block rest) s' Q) : WP isa (.block (shl r v sh ++ rest)) s Q := by
  refine h.wrK (exec_li hv) hr fun s₁ h₁ u₁ => h₁.wrK (exec_lsl hsh) hr fun s₂ h₂ u₂ => k s₂ h₂
    ⟨fun r' hr' => by rw [u₂.other _ (by simpa using hr'), u₁.other _ (by simpa using hr')],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩ ?_ (by rw [u₂.mem, u₁.mem])
  rw [u₂.gpr, u₁.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega)]

/-- `ld r3, o(r28); shl r4 v sh; ltR`: `r0 = 0` iff the header word `o` is
below `v · 2^sh`. -/
theorem ltShl_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v sh : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v < 2 ^ 15) (hsh : sh < 64)
    (hb : v * 2 ^ sh < 2 ^ 64) {x : BitVec 64} (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.r0, .r3, .r4] s t →
      isa.eval (.zero .d .r0) t = some (decide (x.toNat < v * 2 ^ sh)) → Q σ t) :
    VP P (.block ([ld .r3 o] ++ shl .r4 v sh ++ ltR)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block ([ld .r3 o] ++ shl .r4 v sh ++ ltR)), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => ?_
  have h := hF σ s hs
  rw [List.append_assoc]
  refine h.ldK ho h8 (hx σ s hs) (by decide) fun s₁ h₁ u₁ => ?_
  refine shl_ok h₁ (r := .r4) (by decide) hv hsh fun s₂ h₂ K₂ e₂ m₂ => ?_
  refine ltR_ok (by rw [K₂.gpr (by decide), u₁.gpr]) e₂ fun t K m sp _ e => WP.block_nil ?_
  refine k σ s t hs (h₂.of_keep K m sp) ⟨fun r hr => ?_, by rw [K.2.1, K₂.2.1, u₁.rd], by rw [K.2.2, K₂.2.2, u₁.wr]⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K.gpr (by simpa using hr.1), K₂.gpr (by simpa using hr.2.2), u₁.other _ hr.2.1]
  · rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

end

end VG.Proof.Dsa.PPC64LE.Gen
