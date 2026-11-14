module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.St
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontSum
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! ### `Dsa.PPC64LE.Gen.VP`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: pieces proven correct and constant time at once

As on ARMv7 (`Proof/Rsa/Arm/RvVP.lean`): `VP F c G`: from any state at the
stage `F σ` of a run from `σ`, `c` ends at the stage `G σ` (`wp`), and two
runs, each at the stage `F` of its own run, leak the same trace and end at
the stages `G` (`ct`). The stages carry the public parameters both runs
share, so that a piece checked by the taint analysis needs only that the
registers it takes as public are determined by them (`VP.taint`), and pieces
compose by `seq`, `ite` and `loop` (whose number of iterations is public).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE

/-- Two runs, each at the stage `F` of its own run from `σ`. -/
def Two (F : State → State → Prop) (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, F σ₁ s₁ ∧ F σ₂ s₂

/-- The stage `F` of a run from `σ`, whose states name the statics `σ` names. -/
def Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

structure VP (F : State → State → Prop) (c : Prog isa) (G : State → State → Prop) : Prop where
  wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)
  ct : RelCT isa (Two (Sy F)) c (Two (Sy G))

namespace VP

variable {F G H : State → State → Prop}

/-- The stage after a piece names the statics of the run's start. -/
theorem wps {c : Prog isa} (wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)) {σ s : State}
    (hs : F σ s) (hy : s.syms = σ.syms) : WP isa c s (Sy G σ) :=
  WP.mono_syms (wp σ s hs hy) fun _ ht ty => ⟨ht, ty.trans hy⟩

/-- From a relation of any two runs and correctness of each. -/
theorem of_ct' {c : Prog isa}
    (ct : ∀ σ₁ σ₂, RelCT isa (fun s₁ s₂ => Sy F σ₁ s₁ ∧ Sy F σ₂ s₂) c (fun _ _ => True))
    (wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)) : VP F c G := by
  refine ⟨wp, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂
  have r := ((ct σ₁ σ₂).wp (F₁ := Sy G σ₁) (F₂ := Sy G σ₂) fun s t h =>
    ⟨wps wp h.1.1 h.1.2, wps wp h.2.1 h.2.2⟩) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, r.2.2.1, r.2.2.2⟩

/-- From a relation of any two runs and correctness of each. -/
theorem of_ct {c : Prog isa}
    (ct : ∀ σ₁ σ₂, RelCT isa (fun s₁ s₂ => F σ₁ s₁ ∧ F σ₂ s₂) c (fun _ _ => True))
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  of_ct' (fun σ₁ σ₂ => (ct σ₁ σ₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    fun σ s hs _ => wp σ s hs

/-- A piece the taint analysis checks with the registers `rs` public. -/
theorem taint {c : Prog isa} (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs rs) c hc).isSome = true)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  obtain ⟨_, hc⟩ := cert
  exact of_ct (fun σ₁ σ₂ => RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun s t h => ⟨sp _ _ _ _ h.1 h.2, fun r hr => regs _ _ _ _ h.1 h.2 r
      (by simpa [Taint.ofRegs] using RegSet.mem_ofList.mp hr)⟩) hc) wp

/-- `taint`, with the Montgomery kernel's summary in place of its code
(`Proof/Bignum/PPC64LE/MontSum.lean`). -/
theorem taintR {c : Prog isa} (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.checkR VG.PPC64LE.taint VG.Proof.Bignum.PPC64LE.montSums (Taint.ofRegs rs) c
      hc).isSome = true ∧ VG.Taint.fillR VG.Proof.Bignum.PPC64LE.montSums c hc = c)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  obtain ⟨_, hc, hf⟩ := cert
  exact of_ct (fun σ₁ σ₂ => RelCT.taintR VG.Proof.Bignum.PPC64LE.montSums_ok (Taint.ofRegs rs)
    (fun s t h => ⟨sp _ _ _ _ h.1 h.2, fun r hr => regs _ _ _ _ h.1 h.2 r
      (by simpa [Taint.ofRegs] using RegSet.mem_ofList.mp hr)⟩) hf hc) wp

theorem mono {F' G' : State → State → Prop} {c : Prog isa} (h : VP F c G)
    (hF : ∀ σ s, F' σ s → F σ s) (hG : ∀ σ s, G σ s → G' σ s) : VP F' c G' :=
  ⟨fun σ s hs hy => WP.mono (h.wp σ s (hF σ s hs) hy) (hG σ),
    h.ct.mono (fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨hF _ _ h₁.1, h₁.2⟩, ⟨hF _ _ h₂.1, h₂.2⟩⟩)
      fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨hG _ _ h₁.1, h₁.2⟩, ⟨hG _ _ h₂.1, h₂.2⟩⟩⟩

theorem seq {c₁ c₂ : Prog isa} (h₁ : VP F c₁ G) (h₂ : VP G c₂ H) : VP F (.seq c₁ c₂) H :=
  ⟨fun σ _ hs hy => WP.seq (WP.mono (wps h₁.wp hs hy) fun t ht => h₂.wp σ t ht.1 ht.2), RelCT.seq h₁.ct h₂.ct⟩

theorem assoc {a b c : Prog isa} (h : VP F (.seq (.seq a b) c) G) : VP F (.seq a (.seq b c)) G :=
  ⟨fun σ s hs hy => WP.assoc (h.wp σ s hs hy), RelCT.assoc h.ct⟩

theorem block_append {l₁ l₂ : List Instr} (h₁ : VP F (.block l₁) G) (h₂ : VP G (.block l₂) H) :
    VP F (.block (l₁ ++ l₂)) H :=
  ⟨fun σ _ hs hy => WP.block_append (WP.mono (wps h₁.wp hs hy) fun t ht => h₂.wp σ t ht.1 ht.2),
    RelCT.block_append (RelCT.seq h₁.ct h₂.ct)⟩

theorem block_nil (h : ∀ σ s, F σ s → G σ s) : VP F (.block []) G :=
  ⟨fun σ s hs _ => WP.block_nil (h σ s hs),
    RelCT.block_nil fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨h _ _ h₁.1, h₁.2⟩, ⟨h _ _ h₂.1, h₂.2⟩⟩⟩

/-- A branch on a condition both runs agree on. -/
theorem ite {c : Cond} {t e : Prog isa}
    (hc : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : VP (fun σ s => F σ s ∧ isa.eval c s = some true) t G)
    (he : VP (fun σ s => F σ s ∧ isa.eval c s = some false) e G) : VP F (.ite c t e) G := by
  refine ⟨fun σ s hs hy => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, isa.eval c s = some b := by cases c <;> exact ⟨_, rfl⟩
    exact WP.ite b hb (fun h => ht.wp σ s ⟨hs, by rw [hb, h]⟩ hy) (fun h => he.wp σ s ⟨hs, by rw [hb, h]⟩ hy)
  · refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => hc _ _ _ _ h₁.1 h₂.1) ?_ ?_
    · exact ht.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨⟨h₁.1, e⟩, h₁.2⟩, ⟨h₂.1, (hc _ _ _ _ h₁.1 h₂.1).symm.trans e⟩, h₂.2⟩) fun _ _ h => h
    · exact he.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨⟨h₁.1, e⟩, h₁.2⟩, ⟨h₂.1, (hc _ _ _ _ h₁.1 h₂.1).symm.trans e⟩, h₂.2⟩) fun _ _ h => h

/-- A loop whose iterations left, `n + 1` at the stage `I (n + 1)`, both
runs share: each iteration goes on iff `n > 0`. -/
theorem loop {I : Nat → State → State → Prop} {body : Prog isa} {c : Cond} {Q : State → State → Prop}
    (hb : ∀ n, VP (I (n + 1)) body fun σ s =>
      isa.eval c s = some (decide (0 < n)) ∧ (n = 0 → Q σ s) ∧ (0 < n → I n σ s))
    (n : Nat) : VP (I (n + 1)) (.loop body c) Q := by
  refine ⟨fun σ s hs hy => ?_, ?_⟩
  · refine WP.loop (M := isa) (Q := Q σ) (fun m u => Sy (I (m + 1)) σ u) (fun m u hu => ?_) n s ⟨hs, hy⟩
    refine WP.mono (wps (hb m).wp hu.1 hu.2) fun u' ⟨⟨he, hq, hi⟩, uy⟩ => ?_
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · exact .inl ⟨by rw [he, h0]; rfl, hq h0⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega_using [hp]⟩
      exact .inr ⟨by rw [he]; simp, k, by omega_using [], hi hp, uy⟩
  · refine RelCT.loop (M := isa) (fun m => Two (Sy (I (m + 1)))) (fun m => ?_) n
    refine (hb m).ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨σ₁, σ₂, ⟨⟨e₁, q₁, i₁⟩, y₁⟩, ⟨⟨e₂, q₂, i₂⟩, y₂⟩⟩ =>
      ⟨e₁.trans e₂.symm, fun hf => ?_, fun ht => ?_⟩
    · have h0 : m = 0 := by rw [e₁] at hf; simpa using hf
      exact ⟨σ₁, σ₂, ⟨q₁ h0, y₁⟩, ⟨q₂ h0, y₂⟩⟩
    · have hp : 0 < m := by rw [e₁] at ht; simpa using ht
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega_using [hp]⟩
      exact ⟨k, by omega_using [], σ₁, σ₂, ⟨i₁ hp, y₁⟩, ⟨i₂ hp, y₂⟩⟩

/-- A piece no state reaches. -/
theorem of_false {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁.1 (h σ _)⟩

end VP

end VG.Proof.Dsa.PPC64LE.Gen

end

end


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
  rw [show ld t o = .load .d t .r28 o from rfl, exec_load_d (by decide) ⟨by simp only [hEnd, fSave] at ho; omega_using [ho],
    by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])), h.gi.r28, ← hv]

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
  rw [show ld r o = .load .d r .r28 o from rfl, exec_load_d (by decide) ⟨by simp only [hEnd, fSave] at ho; omega_using [ho],
    by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])), h.gi.r28, ← hx σ s hs]

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
      ⟨by simp only [hEnd, fSave] at ho; omega_using [ho], by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])),
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
    · simp [show ¬(2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - y.toNat) + 1) by omega_using [hl], hl]
    · simp [show 2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - y.toNat) + 1 by omega_using [hl], hl]

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
  · rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hv])]

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
  rw [Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega_using [hv])]

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
