module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.St
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.VP
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter search on RISC-V: header words in pieces

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Pieces.lean`). `WP.wr`: an
instruction that writes one register. The taint analysis does not follow the
header's words, which the search keeps its state in: a load of one (`ld`) and
a store into one (`st`) leak only addresses from `s6`, which holds `scratch`
in both runs of the search, so they are analysed with `s6` public (`ld_vp`,
`st_vp`, `stImm_vp`, `cmpF_vp`), and the code between them with the registers
the loads set public (`VP.taint`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- An instruction that writes `v` to `d`. -/
theorem WP.wr {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 64}
    (h : exec i s = some (s.write d v)) (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons h (k _ (Upd.write _ _ _))

section
variable {G : GP} {STK : Nat}

/-- The stage's states hold `scratch` in `s6` and have the call's stack pointer. -/
abbrev Pub (G : GP) (F : State → State → Prop) : Prop :=
  ∀ σ s, F σ s → s.gpr .s6 = G.scr ∧ s.sp = G.sp

theorem SS.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G F := fun σ s h => ⟨(hF σ s h).gi.s6, by rw [(hF σ s h).gi.sp, ← (hF σ s h).gi.hG]; rfl⟩

/-- A piece analysed with `s6` and `rs` public. -/
theorem VP.pub {F Q : State → State → Prop} {c : Prog isa} (hp : Pub G F) (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs (.s6 :: rs)) c hc).isSome = true)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (Q σ)) : VP F c Q :=
  VP.taint (.s6 :: rs) cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [(hp _ _ h₁).2, (hp _ _ h₂).2])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [(hp _ _ h₁).1, (hp _ _ h₂).1]
      · exact regs _ _ _ _ h₁ h₂ r hr) wp

end

/-- `ld t, o(s6)` of a header word whose value `v` is known, keeping a stage. -/
theorem SS.ldK {G : GP} {STK : Nat} {σ s : State} {c : Cfg} (h : SS G STK σ c s) {o : Nat} (ho : o + 8 ≤ hEnd)
    (h8 : o % 8 = 0) {v : BitVec 64} (hv : fw s.mem G o = v) {t : Reg} (ht : t ≠ .s6) {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', SS G STK σ c s' → Upd s s' t v → WP isa (.block rest) s' Q) :
    WP isa (.block (ld t o :: rest)) s Q :=
  h.gi.ldV ho h8 hv fun s' u => k s' (h.of_upd u ht) u

/-! ## Header words as pieces -/

section
variable {G : GP} {STK : Nat}

/-- A load of a header word whose value both runs know. -/
theorem ld_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} (hr : r ≠ .s6) {o : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Upd s t r x → Q σ t) : VP P (.block [ld r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  exact (hF σ s hs).ldK ho h8 (hx σ s hs) hr fun t h u => WP.block_nil (k σ s t hs h u)

/-- A store into a variable word of the header. -/
theorem st_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} {o : Nat} (hv : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (s.gpr r)) t → Keep [] s t → Q σ t) :
    VP P (.block [st r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [st r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  exact (hF σ s hs).stF hv fun t h m => WP.block_nil (k σ s t hs h ⟨fun r _ => by rw [m.gpr], m.rd, m.wr⟩)

/-- `stImm o v`: the header word `o` := `v`. -/
theorem stImm_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (hv : v < 2048) (ho : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (BitVec.ofNat 64 v)) t → Keep [.t2] s t → Q σ t) :
    VP P (.block (stImm o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (stImm o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  refine wp_li hv fun s₁ u₁ => ?_
  have h₁ : SS G STK σ (c σ) s₁ := (hF σ s hs).of_upd u₁ (by decide)
  refine h₁.stF ho fun t h m => WP.block_nil (k σ s t hs (by rw [u₁.gpr] at h; exact h) ?_)
  exact ⟨fun r hr => by rw [m.gpr, u₁.other _ (by simpa using hr)], by rw [m.rd, u₁.rd], by rw [m.wr, u₁.wr]⟩

theorem sub_beq_zero (x y : BitVec 64) : (x - y == 0) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0 := fun e => h (by rw [← BitVec.sub_add_cancel x y, e]; exact BitVec.zero_add y)
    rw [beq_false_of_ne this, beq_false_of_ne h]

/-- `cmpF o v`: `t2 = 0` iff the header word `o`, which both runs know, is `v`. -/
theorem cmpF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v ≤ 2048) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.t2] s t →
      isa.eval (.zero .t2) t = some (x == BitVec.ofNat 64 v) → Q σ t) : VP P (.block (cmpF o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (cmpF o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  refine h.ldK ho h8 (hx σ s hs) (t := .t2) (by decide) fun s₁ h₁ u₁ => ?_
  refine wp_subi hv fun t u => WP.block_nil ?_
  refine k σ s t hs (h₁.of_upd u (by decide)) ?_ ?_
  · exact ⟨fun r hr => by
      have hr' : r ≠ .t2 := by simpa using hr
      rw [u.other _ hr', u₁.other _ hr'], by rw [u.rd, u₁.rd], by rw [u.wr, u₁.wr]⟩
  · rw [eval_zero, u.gpr, u₁.gpr, sub_beq_zero]

end

end VG.Proof.Dsa.RISCV64.PSearch
