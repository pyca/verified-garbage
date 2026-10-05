import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Impl.MlKem.X86.Basic
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Piece`. -/
section

/-!
# ML-KEM on x86 (32-bit): pieces of code, correct and constant time

A function is proven piece by piece. `Piece Pre Pub A B c` says that, for
every initial state `s₀` satisfying `Pre`, `c` runs from any state
satisfying `A s₀` to one satisfying `B s₀` (`WP`), and that two runs of `c`
from states satisfying `A s₀` and `A s₀'`, for initial states related by
`Pub`, leak the same trace (`RelCT`). The invariants `A` and `B` say what
the correctness proof knows of each run, so a public value (a pointer, a
counter, a loop condition) is public in both runs as soon as correctness
determines it from public data, however it got there (through memory, or a
call). Pieces compose (`seq`, `ite`, `loop`, `frame`, calls of verified code
in a frame of their arguments: `callWith`), straight-line code whose
addresses depend only on registers that correctness determines is checked
by the taint analysis (`taint`), and a whole function from its entry state
gives `Verified` (`verified`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86

/-- See the module documentation. -/
structure Piece (Pre : VG.X86.State → Prop) (Pub : VG.X86.State → VG.X86.State → Prop) (A B : VG.X86.State → VG.X86.State → Prop)
    (c : Prog isa) : Prop where
  wp : ∀ s₀ s, Pre s₀ → A s₀ s → WP isa c s (B s₀)
  ct : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
    RelCT isa (fun s s' => A s₀ s ∧ A s₀' s') c fun _ _ => True

namespace Piece

variable {Pre : VG.X86.State → Prop} {Pub : VG.X86.State → VG.X86.State → Prop}

/-- Constant time, relating the final states by the postconditions. -/
theorem ct' {A B : VG.X86.State → VG.X86.State → Prop} {c : Prog isa} (h : VG.Proof.MlKem.X86.Piece Pre Pub A B c) {s₀ s₀' : VG.X86.State}
    (h₀ : Pre s₀) (h₀' : Pre s₀') (hp : Pub s₀ s₀') :
    RelCT isa (fun s s' => A s₀ s ∧ A s₀' s') c fun s s' => B s₀ s ∧ B s₀' s' :=
  ((h.ct _ _ h₀ h₀' hp).wp (F₁ := B s₀) (F₂ := B s₀')
    fun _ _ ⟨ha, ha'⟩ => ⟨h.wp _ _ h₀ ha, h.wp _ _ h₀' ha'⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, b, b'⟩ => ⟨b, b'⟩

theorem mono {A A' B B' : VG.X86.State → VG.X86.State → Prop} {c : Prog isa} (h : VG.Proof.MlKem.X86.Piece Pre Pub A B c)
    (ha : ∀ s₀ s, Pre s₀ → A' s₀ s → A s₀ s) (hb : ∀ s₀ s, Pre s₀ → B s₀ s → B' s₀ s) :
    VG.Proof.MlKem.X86.Piece Pre Pub A' B' c where
  wp s₀ s h₀ h' := (h.wp s₀ s h₀ (ha s₀ s h₀ h')).mono fun _ hb' => hb _ _ h₀ hb'
  ct s₀ s₀' h₀ h₀' hp := (h.ct s₀ s₀' h₀ h₀' hp).mono
    (fun _ _ ⟨a, a'⟩ => ⟨ha _ _ h₀ a, ha _ _ h₀' a'⟩) fun _ _ h => h

/-- Stronger preconditions and public data. -/
theorem pre_mono {Pre' : VG.X86.State → Prop} {Pub' : VG.X86.State → VG.X86.State → Prop} {A B : VG.X86.State → VG.X86.State → Prop}
    {c : Prog isa} (h : VG.Proof.MlKem.X86.Piece Pre Pub A B c) (hp : ∀ s, Pre' s → Pre s)
    (hq : ∀ s s', Pre' s → Pre' s' → Pub' s s' → Pub s s') : VG.Proof.MlKem.X86.Piece Pre' Pub' A B c where
  wp s₀ s h₀ ha := h.wp s₀ s (hp _ h₀) ha
  ct s₀ s₀' h₀ h₀' hpub := h.ct s₀ s₀' (hp _ h₀) (hp _ h₀') (hq _ _ h₀ h₀' hpub)

theorem seq {A B C : VG.X86.State → VG.X86.State → Prop} {c₁ c₂ : Prog isa} (h₁ : VG.Proof.MlKem.X86.Piece Pre Pub A B c₁)
    (h₂ : VG.Proof.MlKem.X86.Piece Pre Pub B C c₂) : VG.Proof.MlKem.X86.Piece Pre Pub A C (.seq c₁ c₂) where
  wp s₀ s h₀ ha := WP.seq ((h₁.wp s₀ s h₀ ha).mono fun s' hb => h₂.wp s₀ s' h₀ hb)
  ct s₀ s₀' h₀ h₀' hp := RelCT.seq (h₁.ct' h₀ h₀' hp) (h₂.ct s₀ s₀' h₀ h₀' hp)

/-- Code the taint analysis proves constant time from the registers `R`,
which correctness determines from public data. -/
theorem taint {A B : VG.X86.State → VG.X86.State → Prop} {c : Prog isa} (R : List Reg)
    (hw : ∀ s₀ s, Pre s₀ → A s₀ s → WP isa c s (B s₀))
    (hR : ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      ∀ r ∈ R, s.gpr r = s'.gpr r)
    {hc : Taint.Hint VG.X86.Taint.T} (h : (VG.X86.taint.check (τr R) c hc).isSome = true) :
    VG.Proof.MlKem.X86.Piece Pre Pub A B c where
  wp := hw
  ct _ _ h₀ h₀' hp :=
    RelCT.taint (A := VG.X86.taint) (τr R) (fun _ _ ⟨a, a'⟩ => agree_regs (hR _ _ _ _ h₀ h₀' hp a a')) h

/-- A branch whose condition correctness determines from public data. -/
theorem ite {A B : VG.X86.State → VG.X86.State → Prop} {cnd : Cond} {t e : Prog isa} (b : VG.X86.State → Bool)
    (hb : ∀ s₀ s, Pre s₀ → A s₀ s → isa.eval cnd s = some (b s₀))
    (hbp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → b s₀ = b s₀')
    (ht : VG.Proof.MlKem.X86.Piece Pre Pub (fun s₀ s => A s₀ s ∧ b s₀ = true) B t)
    (he : VG.Proof.MlKem.X86.Piece Pre Pub (fun s₀ s => A s₀ s ∧ b s₀ = false) B e) :
    VG.Proof.MlKem.X86.Piece Pre Pub A B (.ite cnd t e) where
  wp s₀ s h₀ ha := by
    refine WP.ite (b s₀) (hb _ _ h₀ ha) (fun h => ht.wp _ _ h₀ ⟨ha, h⟩) (fun h => he.wp _ _ h₀ ⟨ha, h⟩)
  ct s₀ s₀' h₀ h₀' hp := by
    refine RelCT.ite (fun s s' ⟨a, a'⟩ => by rw [hb _ _ h₀ a, hb _ _ h₀' a', hbp _ _ h₀ h₀' hp])
      ((ht.ct s₀ s₀' h₀ h₀' hp).mono ?_ fun _ _ h => h) ((he.ct s₀ s₀' h₀ h₀' hp).mono ?_ fun _ _ h => h)
    · rintro s s' ⟨⟨a, a'⟩, hc⟩
      rw [hb _ _ h₀ a, Option.some.injEq] at hc
      exact ⟨⟨a, hc⟩, a', by rw [← hbp _ _ h₀ h₀' hp]; exact hc⟩
    · rintro s s' ⟨⟨a, a'⟩, hc⟩
      rw [hb _ _ h₀ a, Option.some.injEq] at hc
      exact ⟨⟨a, hc⟩, a', by rw [← hbp _ _ h₀ h₀' hp]; exact hc⟩

/-- A loop of `N ≥ 1` iterations, with the invariant `Inv k` after `k`. -/
theorem loop {body : Prog isa} {cnd : Cond} (Inv : Nat → VG.X86.State → VG.X86.State → Prop) {N : Nat} (hN : 0 < N)
    (hb : ∀ k < N, VG.Proof.MlKem.X86.Piece Pre Pub (Inv k)
      (fun s₀ s => Inv (k + 1) s₀ s ∧ isa.eval cnd s = some (decide (k + 1 < N))) body) :
    VG.Proof.MlKem.X86.Piece Pre Pub (Inv 0) (Inv N) (.loop body cnd) where
  wp s₀ s h₀ ha := by
    refine WP.loop (M := isa) (fun n (s : VG.X86.State) => ∃ k, n = N - k ∧ k < N ∧ Inv k s₀ s)
      (fun n s hi => ?_) N s ⟨0, (Nat.sub_zero N).symm, hN, ha⟩
    obtain ⟨k, hn, hk, hi⟩ := hi
    refine ((hb k hk).wp _ _ h₀ hi).mono fun s' ⟨hi', hc⟩ => ?_
    by_cases h : k + 1 < N
    · exact .inr ⟨by rw [hc, decide_eq_true h], N - (k + 1), by omega, k + 1, rfl, h, hi'⟩
    · exact .inl ⟨by rw [hc, decide_eq_false h], by rw [show N = k + 1 by omega]; exact hi'⟩
  ct s₀ s₀' h₀ h₀' hp := by
    have := RelCT.loop (M := isa) (body := body) (c := cnd) (Q := fun _ _ => True)
      (fun n s s' => ∃ k, n = N - k ∧ k < N ∧ Inv k s₀ s ∧ Inv k s₀' s')
      (fun n => by
        refine RelCT.exists_ fun k => ?_
        by_cases hk : n = N - k ∧ k < N
        · refine ((hb k hk.2).ct' h₀ h₀' hp).mono (fun s s' ⟨_, _, a, a'⟩ => ⟨a, a'⟩) ?_
          rintro s s' ⟨⟨i₁, c₁⟩, i₂, c₂⟩
          refine ⟨by rw [c₁, c₂], fun _ => trivial, fun h => ?_⟩
          rw [c₁, Option.some.injEq, decide_eq_true_iff] at h
          exact ⟨N - (k + 1), by omega, k + 1, rfl, h, i₁, i₂⟩
        · exact RelCT.of_false fun s s' ⟨h1, h2, _⟩ => hk ⟨h1, h2⟩) N
    exact this.mono (fun s s' ⟨a, a'⟩ => ⟨0, (Nat.sub_zero N).symm, hN, a, a'⟩) fun _ _ h => h

/-- A loop of `N ≥ 1` iterations of a block, counting down with `sub ecx, 1`
(or anything else that leaves the condition `ne` as correctness says),
whose addresses depend only on the registers `R`. -/
theorem countLoop {body : List Instr} {N : Nat} (hN : 0 < N) (Inv : Nat → VG.X86.State → VG.X86.State → Prop)
    (R : List Reg)
    (hstep : ∀ k < N, ∀ s₀ s, Pre s₀ → Inv k s₀ s → WP isa (.block body) s fun s' =>
      Inv (k + 1) s₀ s' ∧ isa.eval .ne s' = some (decide (k + 1 < N)))
    (hR : ∀ k < N, ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → Inv k s₀ s → Inv k s₀' s' →
      ∀ r ∈ R, s.gpr r = s'.gpr r)
    {hc : Taint.Hint VG.X86.Taint.T} (ht : (VG.X86.taint.check (τr R) (.block body) hc).isSome = true) :
    VG.Proof.MlKem.X86.Piece Pre Pub (Inv 0) (Inv N) (.loop (.block body) .ne) :=
  Piece.loop Inv hN fun k hk => Piece.taint R (hstep k hk) (hR k hk) ht

/-- A frame around `body`. -/
theorem frame {A B : VG.X86.State → VG.X86.State → Prop} {rs : List Reg} {r : Reg} {body : Prog isa}
    (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) (hr : r ≠ .esp) (hsp : NoSp body)
    (hn : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length ≤ (s.gpr .esp).toNat)
    (hesp : ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      s.gpr .esp = s'.gpr .esp)
    (hb : VG.Proof.MlKem.X86.Piece Pre Pub (fun s₀ s => ∃ s₁, A s₀ s₁ ∧ s = pushed rs s₁)
      (fun s₀ s₂ => B s₀ (popped r rs.length s₂)) body) :
    VG.Proof.MlKem.X86.Piece Pre Pub A B (.frame (.push rs) body (.pop r rs.length)) where
  wp _ s h₀ ha := WP.frame hne hrs hr (hn _ _ h₀ ha) hsp (hb.wp _ _ h₀ ⟨s, ha, rfl⟩)
  ct _ _ h₀ h₀' hp := RelCT.frame (fun _ _ ⟨a, a'⟩ => hesp _ _ _ _ h₀ h₀' hp a a')
    ((hb.ct _ _ h₀ h₀' hp).mono (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂⟩, e₁, e₂⟩ => ⟨⟨s₁, h₁, e₁⟩, s₂, h₂, e₂⟩)
      fun _ _ h => h)

/-- A call of verified code in a frame of its arguments `rs`, with the
permissions `rd s₀` and `wr s₀`. -/
theorem callWith {A B : VG.X86.State → VG.X86.State → Prop} {rs : List Reg} {n : String} {c : Prog isa}
    {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    (rd wr : VG.X86.State → List Region)
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat)
    (hk : ∀ s₀ s, Pre s₀ → A s₀ s → CallPre k rs (rd s₀) (wr s₀) s)
    (hpub : ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧ s.gpr .esp = s'.gpr .esp ∧
      k.pub ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr s₀ ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : VG.X86.State, s₂.mem = s'.mem ∧
        k.post ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    VG.Proof.MlKem.X86.Piece Pre Pub A B (.frame (.push rs) (.call n c) (.pop .eax rs.length)) where
  wp s₀ s h₀ ha := WP.callWith hv hsp hne hrs (hd _ _ h₀ ha) (hk _ _ h₀ ha)
    fun s' h₁ h₂ h₃ h₄ h₅ => hQ _ _ _ h₀ ha h₁ h₂ h₃ h₄ h₅
  ct s₀ s₀' h₀ h₀' hp := RelCT.callWith hv hct (rd s₀) (wr s₀) fun s s' ⟨a, a'⟩ => by
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub _ _ _ _ h₀ h₀' hp a a'
    exact ⟨hk _ _ h₀ a, e₁ ▸ e₂ ▸ hk _ _ h₀' a', e₃, e₄⟩

/-- A whole function, from its entry state. -/
theorem verified {c : Prog isa} {k : Contract isa}
    (h : VG.Proof.MlKem.X86.Piece k.pre k.pub (fun s₀ s => s = s₀) (fun s₀ s' => abiPreserved s₀ s' ∧ k.post s₀ s') c)
    (hsat : ∃ s, k.pre s) : Verified X86.target c k :=
  ⟨fun s hs => h.wp s s hs rfl,
    fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h.ct s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hsat⟩

end Piece

end VG.Proof.MlKem.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Leaf`. -/
section

/-!
# ML-KEM on x86 (32-bit): leaf functions

A function that calls no other one (`Impl.MlKem.X86.leaf`) pushes its caller's
`ebx`, `esi`, `edi` and `ebp` in a frame of 16 bytes, runs its body, reloads
`esi`, `edi` and `ebp` from the frame, and pops the frame into `ebx`. If the
body changes memory only within regions `W` apart from the frame and the
return address, the function meets the calling convention (`Piece.leaf`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86

theorem ea_at (s : VG.X86.State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- The last word a frame's pop loads is the register it leaves. -/
theorem popReg_last (d : Reg) (hd : d ≠ .esp) :
    ∀ (k : Nat) (s : VG.X86.State), (popReg s d (k + 1)).gpr d =
      s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * k)).setWidth 64) 32
  | 0, s => by
    simp only [popReg, State.setReg, ite_eq_right hd, ite_true, Nat.mul_zero, BitVec.add_zero]
  | k + 1, s => by
    rw [popReg.eq_2, VG.Proof.MlKem.X86.popReg_last d hd k]
    simp only [State.setReg, ite_true]
    congr 2
    rw [BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]
    congr 2
    omega

section
variable (s₀ : VG.X86.State)

/-- The entry state's stack pointer. -/
abbrev E0 : BitVec 32 := s₀.gpr .esp

/-- The state after the leaf's frame's push. -/
abbrev P0 : VG.X86.State := pushed saveRegs s₀

/-- The leaf's frame. -/
abbrev frameR : Region := below (VG.Proof.MlKem.X86.E0 s₀) 16

/-- The return address. -/
abbrev retR : Region := ⟨(VG.Proof.MlKem.X86.E0 s₀).setWidth 64, 4⟩

end

theorem saveRegs_len : 4 * saveRegs.length = 16 := rfl

theorem P0_esp (s₀ : VG.X86.State) : (VG.Proof.MlKem.X86.P0 s₀).gpr .esp = VG.Proof.MlKem.X86.E0 s₀ - 16 := by
  rw [pushed_esp]; rfl

theorem P0_wr (s₀ : VG.X86.State) : (VG.Proof.MlKem.X86.P0 s₀).wr = VG.Proof.MlKem.X86.frameR s₀ :: s₀.wr := by
  rw [pushed_wr, VG.Proof.MlKem.X86.saveRegs_len]

/-- Word `i` of the frame holds the register pushed `i`-th from the end. -/
theorem frame_word (s₀ : VG.X86.State) (hE : 16 ≤ (VG.Proof.MlKem.X86.E0 s₀).toNat) {i : Nat} (hi : i < 4) :
    (VG.Proof.MlKem.X86.P0 s₀).mem.readW (((VG.Proof.MlKem.X86.P0 s₀).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 =
      s₀.gpr (saveRegs[3 - i]'(by simp [saveRegs]; omega)) :=
  pushed_word (rs := saveRegs) (s := s₀) (by decide) hE hi

/-- A word of the frame, at `esp + 4i` after the push, is within it. -/
theorem frame_contains (s₀ : VG.X86.State) (hE : 16 ≤ (VG.Proof.MlKem.X86.E0 s₀).toNat) {i : Nat} (hi : i < 4) :
    (VG.Proof.MlKem.X86.frameR s₀).Contains (((VG.Proof.MlKem.X86.P0 s₀).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 4 := by
  rw [VG.Proof.MlKem.X86.P0_esp]
  simp only [Region.Contains]
  have := (VG.Proof.MlKem.X86.E0 s₀).isLt
  bv_omega

/-- What the body of a leaf leaves: memory changed only within `W`, apart
from the frame and the return address, and `esp` and the permissions as
the push left them. -/
structure LeafEnd (s₀ : VG.X86.State) (W : List Region) (s : VG.X86.State) : Prop where
  frame : Frame W (VG.Proof.MlKem.X86.P0 s₀).mem s.mem
  esp : s.gpr .esp = (VG.Proof.MlKem.X86.P0 s₀).gpr .esp
  rd : s.rd = (VG.Proof.MlKem.X86.P0 s₀).rd
  wr : s.wr = (VG.Proof.MlKem.X86.P0 s₀).wr

/-- The final state of a leaf whose body ends in `s`. -/
def leafFinal (s : VG.X86.State) : VG.X86.State :=
  popped .ebx 4 (((s.setReg .esi (s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 32)).setReg
    .edi (s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32)).setReg
    .ebp (s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 0).setWidth 64) 32))

theorem restore_run (s : VG.X86.State)
    (h : ∀ i < 3, InRegions (s.rd ++ s.wr) ((s.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 4) :
    WP isa (.block restore) s fun s' => popped .ebx 4 s' = VG.Proof.MlKem.X86.leafFinal s := by
  have h8 := h 2 (by omega)
  have h4 := h 1 (by omega)
  have h0 := h 0 (by omega)
  simp only [Nat.reduceMul] at h8 h4 h0
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, restore, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.ea, State.load32, State.setReg, Option.map_some, h8, h4, h0,
    Option.some.injEq, exists_eq_left']
  rfl

/-- The postcondition of a leaf whose body satisfies `B`. -/
def LeafPost (B : VG.X86.State → Prop) (s₀ s' : VG.X86.State) : Prop :=
  abiPreserved s₀ s' ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
    ∃ s, B s ∧ s'.mem = s.mem ∧ s'.gpr .eax = s.gpr .eax

theorem leafFinal_ok {s₀ s : VG.X86.State} {W : List Region} {B : VG.X86.State → Prop}
    (hE : 16 ≤ (VG.Proof.MlKem.X86.E0 s₀).toNat)
    (hW : ∀ r ∈ W, (VG.Proof.MlKem.X86.frameR s₀).Disjoint r ∧ (VG.Proof.MlKem.X86.retR s₀).Disjoint r) (h : VG.Proof.MlKem.X86.LeafEnd s₀ W s) (hb : B s) :
    VG.Proof.MlKem.X86.LeafPost B s₀ (VG.Proof.MlKem.X86.leafFinal s) := by
  have hwf : ∀ i (hi : i < 4), s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 =
      s₀.gpr (saveRegs[3 - i]'(by simp [saveRegs]; omega)) := fun i hi => by
    rw [h.esp, h.frame.readW (VG.Proof.MlKem.X86.frame_contains s₀ hE hi) (fun r hr => (hW r hr).1) (by decide),
      VG.Proof.MlKem.X86.frame_word s₀ hE hi]
  have hm : (VG.Proof.MlKem.X86.leafFinal s).mem = s.mem := by simp [VG.Proof.MlKem.X86.leafFinal, State.setReg]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, s, hb, hm, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [VG.Proof.MlKem.X86.leafFinal, popped, VG.Proof.MlKem.X86.popReg_last _ (by decide) 3]
      simp only [State.setReg, show Reg.esp ≠ Reg.ebp by decide, show Reg.esp ≠ Reg.edi by decide,
        show Reg.esp ≠ Reg.esi by decide, ite_false]
      exact hwf 3 (by omega)
    · rw [VG.Proof.MlKem.X86.leafFinal, popped_gpr _ _ _ (by decide) (by decide)]
      simp only [State.setReg, show Reg.esi ≠ Reg.ebp by decide, show Reg.esi ≠ Reg.edi by decide,
        ite_false, ite_true]
      exact hwf 2 (by omega)
    · rw [VG.Proof.MlKem.X86.leafFinal, popped_gpr _ _ _ (by decide) (by decide)]
      simp only [State.setReg, show Reg.edi ≠ Reg.ebp by decide, ite_false, ite_true]
      exact hwf 1 (by omega)
    · rw [VG.Proof.MlKem.X86.leafFinal, popped_gpr _ _ _ (by decide) (by decide)]
      simp only [State.setReg, ite_true]
      exact hwf 0 (by omega)
    · rw [VG.Proof.MlKem.X86.leafFinal, popped_esp]
      simp only [State.setReg, show Reg.esp ≠ Reg.ebp by decide, show Reg.esp ≠ Reg.edi by decide,
        show Reg.esp ≠ Reg.esi by decide, ite_false, h.esp, VG.Proof.MlKem.X86.P0_esp]
      rw [show BitVec.ofNat 32 (4 * 4) = 16 from rfl, BitVec.sub_add_cancel]
  · rw [hm, h.frame.readW (Region.contains_self _ _) (fun r hr => (hW r hr).2) (by decide)]
    have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [VG.Proof.MlKem.X86.saveRegs_len]; exact hE)
    rw [VG.Proof.MlKem.X86.saveRegs_len] at hf
    refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    have := (VG.Proof.MlKem.X86.E0 s₀).isLt
    bv_omega
  · simp [VG.Proof.MlKem.X86.leafFinal, State.setReg, popped_rd, h.rd]
  · simp only [VG.Proof.MlKem.X86.leafFinal, popped_wr]
    simp only [State.setReg, h.wr, VG.Proof.MlKem.X86.P0_wr]
    rfl
  · rw [VG.Proof.MlKem.X86.leafFinal, popped_gpr _ _ _ (by decide) (by decide)]
    simp [State.setReg]

namespace Piece

variable {Pre : VG.X86.State → Prop} {Pub : VG.X86.State → VG.X86.State → Prop}

/-- A leaf, from its body. -/
theorem leaf {body : Prog isa} {B : VG.X86.State → VG.X86.State → Prop} (W : VG.X86.State → List Region)
    (hsp : NoSp body)
    (hE : ∀ s₀, Pre s₀ → 16 ≤ (VG.Proof.MlKem.X86.E0 s₀).toNat ∧ (VG.Proof.MlKem.X86.E0 s₀).toNat + 4 ≤ 2 ^ 32)
    (hW : ∀ s₀, Pre s₀ → ∀ r ∈ W s₀, (VG.Proof.MlKem.X86.frameR s₀).Disjoint r ∧ (VG.Proof.MlKem.X86.retR s₀).Disjoint r)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlKem.X86.E0 s₀ = VG.Proof.MlKem.X86.E0 s₀')
    (hb : VG.Proof.MlKem.X86.Piece Pre Pub (fun s₀ s => s = VG.Proof.MlKem.X86.P0 s₀) (fun s₀ s => VG.Proof.MlKem.X86.LeafEnd s₀ (W s₀) s ∧ B s₀ s) body) :
    VG.Proof.MlKem.X86.Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => VG.Proof.MlKem.X86.LeafPost (B s₀) s₀ s') (VG.Impl.MlKem.X86.leaf body) := by
  refine Piece.frame (by decide) (by decide) (by decide) (fun i hi => ?_)
    (fun s₀ s h₀ e => by rw [e]; exact (hE s₀ h₀).1)
    (fun s₀ s₀' s s' h₀ h₀' hp e e' => by rw [e, e']; exact hpub _ _ h₀ h₀' hp) ?_
  · have e : VG.instrs (Code.seq body (.block restore)) = VG.instrs body ++ restore := rfl
    rw [e, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hsp i hi
    · simp only [restore, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rfl
  refine Piece.seq (hb.mono (fun s₀ s _ ⟨s₁, e₁, e₂⟩ => e₁ ▸ e₂) fun _ _ _ h => h) ?_
  refine Piece.taint [.esp] (fun s₀ s h₀ ⟨he, hb'⟩ => ?_) ?_ (by taint_decide)
  · have hE' := hE s₀ h₀
    refine (VG.Proof.MlKem.X86.restore_run s fun i hi => ?_).mono fun s' e => ?_
    · rw [he.rd, he.wr, he.esp, VG.Proof.MlKem.X86.P0_wr]
      exact ⟨VG.Proof.MlKem.X86.frameR s₀, List.mem_append_right _ (List.mem_cons_self ..),
        VG.Proof.MlKem.X86.frame_contains s₀ hE'.1 (by omega)⟩
    · rw [show saveRegs.length = 4 from rfl, e]; exact VG.Proof.MlKem.X86.leafFinal_ok hE'.1 (hW s₀ h₀) he hb'
  · intro s₀ s₀' s s' h₀ h₀' hp ⟨e, _⟩ ⟨e', _⟩ r hr
    simp only [List.mem_singleton] at hr
    subst hr
    rw [e.esp, e'.esp, VG.Proof.MlKem.X86.P0_esp, VG.Proof.MlKem.X86.P0_esp, hpub _ _ h₀ h₀' hp]

end Piece

/-- Argument `i`, as a leaf addresses it after its push. -/
theorem P0_argAddr (s₀ : VG.X86.State) (i : Nat) :
    ((VG.Proof.MlKem.X86.P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := by
  rw [VG.Proof.MlKem.X86.P0_esp]; simp only [argAddr, VG.Proof.MlKem.X86.E0]; congr 1; bv_omega

/-- A word of the arguments. -/
theorem arg_contains {s₀ : VG.X86.State} {n i : Nat} (hi : i < n) (hfit : (VG.Proof.MlKem.X86.E0 s₀).toNat + 4 + 4 * n ≤ 2 ^ 32) :
    (⟨argAddr s₀ 0, 4 * n⟩ : Region).Contains (argAddr s₀ i) 4 := by
  simp only [argAddr, Region.Contains, VG.Proof.MlKem.X86.E0] at hfit ⊢
  bv_omega

/-- The push leaves the arguments. -/
theorem P0_arg {s₀ : VG.X86.State} (hE : 16 ≤ (VG.Proof.MlKem.X86.E0 s₀).toNat) {n i : Nat} (hi : i < n)
    (hfit : (VG.Proof.MlKem.X86.E0 s₀).toNat + 4 + 4 * n ≤ 2 ^ 32)
    (hd : (⟨(VG.Proof.MlKem.X86.E0 s₀).setWidth 64 - 16#64, 16⟩ : Region).Disjoint ⟨argAddr s₀ 0, 4 * n⟩) :
    (VG.Proof.MlKem.X86.P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [VG.Proof.MlKem.X86.saveRegs_len]; exact hE)
  rw [VG.Proof.MlKem.X86.saveRegs_len] at hf
  refine hf.readW (VG.Proof.MlKem.X86.arg_contains hi hfit) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  have e : VG.Proof.MlKem.X86.frameR s₀ = ⟨(VG.Proof.MlKem.X86.E0 s₀).setWidth 64 - 16#64, 16⟩ := by
    simp only [VG.Proof.MlKem.X86.frameR, below]; rw [Taint.sub_setWidth hE]
  exact (e ▸ hd).symm

/-- `[esp + 20 + 4i]`, argument `i`, may be read after the push. -/
theorem P0_argIn {s₀ : VG.X86.State} {n i : Nat} (hi : i < n) (hfit : (VG.Proof.MlKem.X86.E0 s₀).toNat + 4 + 4 * n ≤ 2 ^ 32)
    (hin : (⟨argAddr s₀ 0, 4 * n⟩ : Region) ∈ s₀.rd ++ s₀.wr) :
    InRegions ((VG.Proof.MlKem.X86.P0 s₀).rd ++ (VG.Proof.MlKem.X86.P0 s₀).wr) (argAddr s₀ i) 4 := by
  refine ⟨_, ?_, VG.Proof.MlKem.X86.arg_contains hi hfit⟩
  rw [pushed_rd, VG.Proof.MlKem.X86.P0_wr]
  rcases List.mem_append.mp hin with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

namespace Piece

variable {Pre : VG.X86.State → Prop} {Pub : VG.X86.State → VG.X86.State → Prop}

/-- A leaf whose body is a block and a loop over a block. -/
theorem leafLoop {init body : List Instr} {N : Nat} (W : VG.X86.State → List Region)
    (Inv : Nat → VG.X86.State → VG.X86.State → Prop)
    (hsp : NoSp (.seq (.block init) (.loop (.block body) .ne)))
    (hE : ∀ s₀, Pre s₀ → 16 ≤ (VG.Proof.MlKem.X86.E0 s₀).toNat ∧ (VG.Proof.MlKem.X86.E0 s₀).toNat + 4 ≤ 2 ^ 32)
    (hW : ∀ s₀, Pre s₀ → ∀ r ∈ W s₀, (VG.Proof.MlKem.X86.frameR s₀).Disjoint r ∧ (VG.Proof.MlKem.X86.retR s₀).Disjoint r)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → VG.Proof.MlKem.X86.E0 s₀ = VG.Proof.MlKem.X86.E0 s₀')
    (hinit : VG.Proof.MlKem.X86.Piece Pre Pub (fun s₀ s => s = VG.Proof.MlKem.X86.P0 s₀) (Inv 0) (.block init))
    (hloop : VG.Proof.MlKem.X86.Piece Pre Pub (Inv 0) (Inv N) (.loop (.block body) .ne))
    (hend : ∀ s₀ s, Pre s₀ → Inv N s₀ s → VG.Proof.MlKem.X86.LeafEnd s₀ (W s₀) s) :
    VG.Proof.MlKem.X86.Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => VG.Proof.MlKem.X86.LeafPost (Inv N s₀) s₀ s')
      (Impl.MlKem.X86.leaf (.seq (.block init) (.loop (.block body) .ne))) :=
  Piece.leaf W hsp hE hW hpub
    ((Piece.seq hinit hloop).mono (fun _ _ _ h => h) fun s₀ s h₀ h => ⟨hend s₀ s h₀ h, h⟩)

end Piece

/-- A state with `esp = 0x5000`, the given memory and regions: a witness
that a precondition can hold. -/
def satState (m : Mem) (rd wr : List Region) : VG.X86.State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := m
  rd := rd
  wr := wr

end VG.Proof.MlKem.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Common`. -/
section

/-!
# ML-KEM on x86 (32-bit): common lemmas

Addresses of coefficients and bytes at a 32-bit pointer, the states a
straight-line block leaves (`Only`), and the arithmetic of `condSub`.
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-! ## Numbers -/

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem eq_ofNat_of_toNat {x : BitVec 32} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 32 n := by
  subst h; simp

/-- `condSub` as the code computes it: `x - q`, plus `q` masked by the borrow. -/
theorem condSub_bv (x d : BitVec 32) (hx : x.toNat < 2 * q) :
    (x - Q + ((d - d - (BitVec.ofBool (decide (x.toNat < Q.toNat))).setWidth 32) &&& Q)).toNat =
      condSub x.toNat := by
  have hq : Q.toNat = 3329 := rfl
  rw [hq]
  unfold condSub
  rw [q_eq] at hx ⊢
  by_cases h : x.toNat < 3329
  · rw [ite_eq_right (by omega), decide_eq_true h]
    have e : (d - d - (BitVec.ofBool true).setWidth 32) &&& Q = Q := by
      rw [BitVec.sub_self]; decide
    rw [e, BitVec.sub_add_cancel]
  · rw [ite_eq_left (by omega), decide_eq_false h]
    have e : (d - d - (BitVec.ofBool false).setWidth 32) &&& Q = 0 := by
      rw [BitVec.sub_self]; decide
    rw [e]; unfold Q; bv_omega

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem ofNat_sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  rw [show BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem add_ofNat_add (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, VG.Proof.MlKem.X86.ofNat_add_ofNat]

theorem sub_beq_zero (x v : BitVec 32) : (x - v == 0) = decide (x.toNat = v.toNat) := by
  by_cases h : x.toNat = v.toNat
  · have e : x = v := BitVec.eq_of_toNat_eq h
    subst e; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    exact h (by have := congrArg BitVec.toNat e; simp only [BitVec.toNat_sub] at this; bv_omega)

/-- The returned `u32` is the low word, `eax`, of the returned pair. -/
theorem setWidth_append32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega

/-- A pointer advanced by `d`. -/
theorem ptr_next (x : BitVec 32) (k d : Nat) :
    x + BitVec.ofNat 32 (d * k) + BitVec.ofNat 32 d = x + BitVec.ofNat 32 (d * (k + 1)) := by
  rw [VG.Proof.MlKem.X86.add_ofNat_add, Nat.mul_succ]

/-- A counter counted down. -/
theorem cnt_next {N k : Nat} (hk : k < N) :
    BitVec.ofNat 32 (N - k) - 1 = BitVec.ofNat 32 (N - (k + 1)) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Proof.MlKem.X86.ofNat_sub_ofNat (by omega)]
  congr 1

/-- The loop condition after counting down. -/
theorem cnt_ne {N k : Nat} (hk : k < N) (hN : N < 2 ^ 32) :
    (some (BitVec.ofNat 32 (N - k) - 1 == 0) : Option Bool).map (!·) = some (decide (k + 1 < N)) := by
  rw [VG.Proof.MlKem.X86.cnt_next hk, VG.Proof.MlKem.X86.ofNat_beq_zero (by omega)]
  simp only [Option.map_some, Option.some.injEq]
  by_cases h : k + 1 < N
  · simp [h, show N - (k + 1) ≠ 0 by omega]
  · simp [h, show N - (k + 1) = 0 by omega]

/-! ## Bits -/

/-- A value less than `2ⁿ`, rotated right by `n`, is shifted left by `32 - n`. -/
theorem rotr_small (x : BitVec 32) {n : Nat} (h0 : 0 < n) (h : n < 32) (hx : x.toNat < 2 ^ n) :
    (x.rotateRight n).toNat = x.toNat * 2 ^ (32 - n) := by
  rw [BitVec.rotateRight_def, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.mod_eq_of_lt h]
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx, Nat.zero_or, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have : x.toNat * 2 ^ (32 - n) < 2 ^ n * 2 ^ (32 - n) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
  rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)] at this
  exact this

theorem toNat_shr (x : BitVec 32) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_and_mask (x : BitVec 32) (k : Nat) (hk : k < 32) :
    (x &&& BitVec.ofNat 32 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
    omega), Nat.and_two_pow_sub_one_eq_mod]

/-- The low byte of a word. -/
theorem setWidth8_eq (x : BitVec 32) : x.setWidth 8 = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte, zero-extended. -/
theorem toNat_byte32 (b : Byte) : (b.setWidth 32).toNat = b.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := b.isLt; omega)

/-- `csub` as the code computes it, as a word. -/
theorem csub_eq (x d : BitVec 32) (hx : x.toNat < 2 * q) :
    x - Q + ((d - d - (BitVec.ofBool (decide (x.toNat < Q.toNat))).setWidth 32) &&& Q) =
      BitVec.ofNat 32 (x.toNat % q) := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.MlKem.X86.condSub_bv x d hx, condSub_eq hx, VG.Proof.MlKem.X86.toNat_ofNat32 (by rw [q_eq]; omega)]

/-- Coefficients `i < k + c` after `c` words `V (k + t)` are written. -/
theorem coef_extend2 {m : Mem} {p : Addr} {V : Nat → BitVec 32} {k : Nat} (hk : k + 2 ≤ 256)
    (h : ∀ i < k, coeffAt m p i = V i) :
    ∀ i < k + 2, coeffAt ((m.writeW (coeffAddr p k) (V k)).writeW (coeffAddr p (k + 1)) (V (k + 1))) p i =
      V i := by
  intro i hi
  rw [coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (show k + 1 < n by rw [n_eq]; omega),
    coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (show k < n by rw [n_eq]; omega)]
  by_cases e1 : k + 1 = i
  · rw [ite_eq_left e1, e1]
  rw [ite_eq_right e1]
  by_cases e0 : k = i
  · rw [ite_eq_left e0, e0]
  rw [ite_eq_right e0]
  exact h i (by omega)

/-! ## States -/

/-- `s'` is `s` but for the registers `ds` and the flags. -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Only.refl (ds : List Reg) (s : State) : VG.Proof.MlKem.X86.Only ds s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlKem.X86.Only ds s₁ s₂) (h₂ : VG.Proof.MlKem.X86.Only es s₂ s₃) :
    VG.Proof.MlKem.X86.Only (ds ++ es) s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : VG.Proof.MlKem.X86.Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    VG.Proof.MlKem.X86.Only es s s' := ⟨fun r hr => h.gpr r fun h' => hr (he r h'), h.mem, h.rd, h.wr⟩

/-! ## Single instructions -/

theorem wp_cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

/-- `mov d, [b + disp]` -/
theorem wp_movm {d b : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b disp)) 4)
    (k : WP isa (.block is) (s.setReg d (s.mem.readW (s.ea (at_ b disp)) 32)) Q) :
    WP isa (.block (.mov d (.mem (at_ b disp)) :: is)) s Q :=
  VG.Proof.MlKem.X86.wp_cons (by simp only [exec, readSrc, State.load32, hin, ite_true, Option.map_some]) k

/-- `movzx d, byte [b + disp]` -/
theorem wp_movzx {d b : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b disp)) 1)
    (k : WP isa (.block is) (s.setReg d ((s.mem (s.ea (at_ b disp))).setWidth 32)) Q) :
    WP isa (.block (.movzx8 d (at_ b disp) :: is)) s Q :=
  VG.Proof.MlKem.X86.wp_cons (by simp only [exec, State.load8, hin, ite_true, Option.map_some]) k

/-- `mov d, r` -/
theorem wp_movr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : WP isa (.block is) (s.setReg d (s.gpr r)) Q) : WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  VG.Proof.MlKem.X86.wp_cons (by simp only [exec, readSrc, Option.map_some]) k

/-- `mov [b + disp], r` -/
theorem wp_store {b r : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions s.wr (s.ea (at_ b disp)) 4)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (s.ea (at_ b disp)) (s.gpr r) } Q) :
    WP isa (.block (.store (at_ b disp) r :: is)) s Q :=
  VG.Proof.MlKem.X86.wp_cons (by simp only [exec, State.store32, hin, ite_true]) k

/-- `shr d, n` -/
theorem wp_shr {d : Reg} {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) {is : List Instr} {s : State}
    {Q : State → Prop} (k : ∀ s', VG.Proof.MlKem.X86.Only [d] s s' → s'.gpr d = s.gpr d >>> n → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine VG.Proof.MlKem.X86.wp_cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_)
  · simp only [exec, execShift, h1, h2, and_self, ite_true]
  · simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : r = d) => absurd (e ▸ List.mem_singleton_self d) hr]
    rfl
  · simp [State.setReg]

theorem Only.setReg (s : State) (r : Reg) (v : BitVec 32) : VG.Proof.MlKem.X86.Only [r] s (s.setReg r v) :=
  ⟨fun x hx => by
    simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : x = r) => absurd (e ▸ List.mem_singleton_self r) hx], rfl, rfl, rfl⟩

/-- `and r, imm` -/
theorem wp_and {r : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', VG.Proof.MlKem.X86.Only [r] s s' → s'.gpr r = s.gpr r &&& v → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and r (.imm v) :: is)) s Q := by
  refine VG.Proof.MlKem.X86.wp_cons (s' := (arithFlags s (s.gpr r &&& v) false false).setReg r (s.gpr r &&& v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some]) (k _ ⟨fun x hx => ?_, rfl, rfl, rfl⟩ ?_)
  · simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : x = r) => absurd (e ▸ List.mem_singleton_self r) hx]
    rfl
  · simp [State.setReg]

/-! ## Addresses -/

/-- `[x + k + d]` of a 32-bit pointer `x`, where nothing wraps around. -/
theorem addr_add {x : BitVec 32} {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) d = x.setWidth 64 + BitVec.ofNat 64 (k + d) := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k) (by omega), Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (a := k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat + (k + d)) (by omega)]
  omega

/-- The same, as the model computes it for an access `[r + d]` with `r = x + k`. -/
theorem ea_add {x : BitVec 32} {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 k + BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 (k + d) :=
  VG.Proof.MlKem.X86.addr_add h

/-- `[x + d]` of a 32-bit pointer `x`, where nothing wraps around. -/
theorem ea_off {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 d := by
  have := VG.Proof.MlKem.X86.ea_add (x := x) (k := 0) (d := d) (by omega)
  simpa using this

/-- An access within a region is a sub-region of it. -/
theorem sub_of_contains {r : Region} {a : Addr} {n : Nat} (h : r.Contains a n) : Region.Sub ⟨a, n⟩ r :=
  fun _ hx => h.byte (by simp only [Region.Contains] at hx; omega)

/-- An access of `n` bytes at offset `o` of a region at a 32-bit pointer. -/
theorem contains_at {x : BitVec 32} {len o n : Nat} (h : o + n ≤ len) (hx : x.toNat + len ≤ 2 ^ 32) :
    (⟨x.setWidth 64, len⟩ : Region).Contains (x.setWidth 64 + BitVec.ofNat 64 o) n := by
  simp only [Region.Contains]
  rw [show x.setWidth 64 + BitVec.ofNat 64 o - x.setWidth 64 = BitVec.ofNat 64 o by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact h

theorem polyLen (p : Addr) : (polyRegion p).len ≤ 2 ^ 64 := by show 1024 ≤ 2 ^ 64; decide

/-- Offsets within a region that does not wrap are distinct addresses. -/
theorem add_ofNat_ne {x : Addr} {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    x + BitVec.ofNat 64 a ≠ x + BitVec.ofNat 64 b := by
  intro e
  have e' : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
    have := congrArg (fun y => y - x) e; simpa using this
  have := congrArg BitVec.toNat e'
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

/-- Bytes `j < k + c` at `o`, after `c` bytes `x t` are written at `o + k + t` to bytes `j < k` of
`L`. -/
theorem bytes_extend {m : Mem} {o : Addr} {L : List Byte} {k : Nat} (hk : k + 3 < 2 ^ 64)
    (h : ∀ j < k, m (o + BitVec.ofNat 64 j) = L[j]!) {x0 x1 x2 : Byte} (h0 : x0 = L[k]!)
    (h1 : x1 = L[k + 1]!) (h2 : x2 = L[k + 2]!) :
    ∀ j < k + 3, ((m.writeW (o + BitVec.ofNat 64 k) x0).writeW (o + BitVec.ofNat 64 (k + 1)) x1).writeW
      (o + BitVec.ofNat 64 (k + 2)) x2 (o + BitVec.ofNat 64 j) = L[j]! := by
  intro j hj
  simp only [VG.WriteBytes.writeW8_apply]
  by_cases e2 : j = k + 2
  · subst e2; simp [h2]
  rw [ite_eq_right_iff.mpr fun e => absurd e (VG.Proof.MlKem.X86.add_ofNat_ne (by omega) (by omega) e2)]
  by_cases e1 : j = k + 1
  · subst e1; simp [h1]
  rw [ite_eq_right_iff.mpr fun e => absurd e (VG.Proof.MlKem.X86.add_ofNat_ne (by omega) (by omega) e1)]
  by_cases e0 : j = k
  · subst e0; simp [h0]
  rw [ite_eq_right_iff.mpr fun e => absurd e (VG.Proof.MlKem.X86.add_ofNat_ne (by omega) (by omega) e0)]
  exact h j (by omega)

/-- Bytes `j < k + 1` at `o`, after the byte `x = L[k]` is written at `o + k`. -/
theorem bytes_extend1 {m : Mem} {o : Addr} {L : List Byte} {k : Nat} (hk : k < 2 ^ 64)
    (h : ∀ j < k, m (o + BitVec.ofNat 64 j) = L[j]!) {x : Byte} (hx : x = L[k]!) :
    ∀ j < k + 1, (m.writeW (o + BitVec.ofNat 64 k) x) (o + BitVec.ofNat 64 j) = L[j]! := by
  intro j hj
  simp only [VG.WriteBytes.writeW8_apply]
  by_cases e : j = k
  · subst e; simp [hx]
  rw [ite_eq_right_iff.mpr fun e' => absurd e' (VG.Proof.MlKem.X86.add_ofNat_ne (by omega) (by omega) e)]
  exact h j (by omega)

/-- Coefficient `k` of a polynomial at a 32-bit pointer. -/
theorem coeffAddr_eq (x : BitVec 32) (k : Nat) :
    coeffAddr (x.setWidth 64) k = x.setWidth 64 + BitVec.ofNat 64 (4 * k) := rfl

/-- Two accesses at offsets `a` and `b` of a region at a 32-bit pointer. -/
theorem sep_at {x : BitVec 32} {len a b n k : Nat} (ha : a + n ≤ len) (hb : b + k ≤ len)
    (hx : x.toNat + len ≤ 2 ^ 32) (h : a + n ≤ b ∨ b + k ≤ a) :
    Mem.Sep (x.setWidth 64 + BitVec.ofNat 64 a) n (x.setWidth 64 + BitVec.ofNat 64 b) k := by
  intro y hy hy'
  have := x.isLt
  have hx' := VG.Proof.MlKem.X86.toNat_setWidth64 x
  generalize x.setWidth 64 = X at *
  bv_omega

/-- All-zero memory holds a reduced polynomial. -/
theorem reduced_of_zero {m : Mem} {p : Addr} (h : ∀ k < 1024, m (p + BitVec.ofNat 64 k) = 0) :
    VG.Spec.MlKem.Reduced m p := fun i hi => by
  rw [VG.Proof.MlKem.coeffAt_congr (m' := m) (m := fun _ => 0) (fun k hk => h k hk) hi]
  simp [VG.Spec.MlKem.coeffAt, Mem.readW, Mem.read]

/-- Memory that is zero but at the arguments above `0x5004`, which hold
`ws`: polynomials below `0x5000` are all zero. -/
theorem reduced_below {m : Mem} (hm : ∀ a : Addr, a.toNat < 0x5000 → m a = 0) (p : Nat)
    (hp : p + 1024 ≤ 0x5000) : VG.Spec.MlKem.Reduced m (BitVec.ofNat 64 p) :=
  VG.Proof.MlKem.X86.reduced_of_zero fun k hk => hm _ (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
end VG.Proof.MlKem.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.AddSub`. -/
section

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_add` and `vg_mlkem_sub`

Both are `mapLoop` around an arithmetic step; the loop is proven once for any
step that computes a function `F` of the two coefficients (`OpSpec`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- `op` computes `F a b` in `eax` from `eax = a` and `[edi] = b`, changing
only `eax`, `edx` and the flags. -/
def OpSpec (op : List Instr) (F : Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (Q : State → Prop) (a b : Nat), a < q → b < q →
    (s.gpr .eax).toNat = a → InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4 →
    (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = b →
    (∀ s', VG.Proof.MlKem.X86.Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = F a b → WP isa (.block is) s' Q) →
    WP isa (.block (op ++ is)) s Q

theorem addOp_spec : VG.Proof.MlKem.X86.OpSpec addOp fun a b => condSub (a + b) := by
  intro is s P a b ha hb h₁ hin h₂ k
  simp only [State.ea, at_] at hin h₂
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, addOp, csub, at_, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, hin, Option.some.injEq, exists_eq_left']
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · have e : (s.gpr .eax + s.mem.readW (BitVec.setWidth 64 (s.gpr .edi + 0#32)) 32).toNat = a + b := by
      rw [BitVec.toNat_add, h₁, h₂, Nat.mod_eq_of_lt (by rw [q_eq] at ha hb; omega)]
    simp only [ite_true]
    rw [VG.Proof.MlKem.X86.condSub_bv _ _ (by rw [e]; omega), e]

theorem subOp_spec : VG.Proof.MlKem.X86.OpSpec subOp fun a b => condSub (a + q - b) := by
  intro is s P a b ha hb h₁ hin h₂ k
  simp only [State.ea, at_] at hin h₂
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, subOp, csub, at_, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, hin, Option.some.injEq, exists_eq_left']
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · have e : (s.gpr .eax + Q - s.mem.readW (BitVec.setWidth 64 (s.gpr .edi + 0#32)) 32).toNat =
        a + q - b := by
      rw [q_eq] at ha hb ⊢
      have hQ : (s.gpr .eax + Q).toNat = a + 3329 := by
        rw [BitVec.toNat_add, h₁, show Q.toNat = 3329 from rfl, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, h₂]; omega), hQ, h₂]
    simp only [ite_true]
    rw [VG.Proof.MlKem.X86.condSub_bv _ _ (by rw [e]; omega), e]

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev gP : BitVec 32 := arg s₀ 1
abbrev fA : Addr := (VG.Proof.MlKem.X86.fP s₀).setWidth 64
abbrev gA : Addr := (VG.Proof.MlKem.X86.gP s₀).setWidth 64
abbrev aR2 : Region := ⟨argAddr s₀ 0, 8⟩
/-- The stack below the return address, as the contract states it. -/
abbrev stkR : Region := ⟨(VG.Proof.MlKem.X86.E0 s₀).setWidth 64 - 16#64, 16⟩
end

structure AccPre (s₀ : State) : Prop where
  sp : 16 ≤ (VG.Proof.MlKem.X86.E0 s₀).toNat
  sp' : (VG.Proof.MlKem.X86.E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (VG.Proof.MlKem.X86.gA s₀)]
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.X86.fA s₀), VG.Proof.MlKem.X86.aR2 s₀]
  f_g : (polyRegion (VG.Proof.MlKem.X86.fA s₀)).Disjoint (polyRegion (VG.Proof.MlKem.X86.gA s₀))
  f_a : (polyRegion (VG.Proof.MlKem.X86.fA s₀)).Disjoint (VG.Proof.MlKem.X86.aR2 s₀)
  g_a : (polyRegion (VG.Proof.MlKem.X86.gA s₀)).Disjoint (VG.Proof.MlKem.X86.aR2 s₀)
  ret_f : (VG.Proof.MlKem.X86.retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.fA s₀))
  ret_g : (VG.Proof.MlKem.X86.retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.gA s₀))
  ret_a : (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.aR2 s₀)
  stk_f : (VG.Proof.MlKem.X86.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.fA s₀))
  stk_g : (VG.Proof.MlKem.X86.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.gA s₀))
  stk_a : (VG.Proof.MlKem.X86.stkR s₀).Disjoint (VG.Proof.MlKem.X86.aR2 s₀)
  f_fit : (VG.Proof.MlKem.X86.fP s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (VG.Proof.MlKem.X86.gP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (VG.Proof.MlKem.X86.fA s₀)
  g_red : Reduced s₀.mem (VG.Proof.MlKem.X86.gA s₀)

theorem AccPre.of_add {s₀ : State} (h : (addContract X86.abi 16).pre s₀) : VG.Proof.MlKem.X86.AccPre s₀ := by
  sig_pre [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem AccPre.of_sub {s₀ : State} (h : (subContract X86.abi 16).pre s₀) : VG.Proof.MlKem.X86.AccPre s₀ := by
  sig_pre [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem stkR_eq {s₀ : State} (h : 16 ≤ (VG.Proof.MlKem.X86.E0 s₀).toNat) : VG.Proof.MlKem.X86.stkR s₀ = VG.Proof.MlKem.X86.frameR s₀ := by
  simp only [VG.Proof.MlKem.X86.stkR, VG.Proof.MlKem.X86.frameR, below]; rw [Taint.sub_setWidth h]

/-- The push changes nothing of a region apart from the frame. -/
theorem P0_mem {s₀ : State} (h : 16 ≤ (VG.Proof.MlKem.X86.E0 s₀).toNat) :
    Frame [VG.Proof.MlKem.X86.frameR s₀] s₀.mem (VG.Proof.MlKem.X86.P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [VG.Proof.MlKem.X86.saveRegs_len]; exact h)
  rw [VG.Proof.MlKem.X86.saveRegs_len] at hf
  exact hf

/-! ## The loop -/

/-- The new value of coefficient `i`. -/
def newC (F : Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (F (coeffAt s₀.mem (VG.Proof.MlKem.X86.fA s₀) i).toNat (coeffAt s₀.mem (VG.Proof.MlKem.X86.gA s₀) i).toNat)

/-- After `k` coefficients. -/
structure MapInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (VG.Proof.MlKem.X86.P0 s₀).gpr .esp
  rd : s.rd = (VG.Proof.MlKem.X86.P0 s₀).rd
  wr : s.wr = (VG.Proof.MlKem.X86.P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlKem.X86.fP s₀ + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = VG.Proof.MlKem.X86.gP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [polyRegion (VG.Proof.MlKem.X86.fA s₀)] (VG.Proof.MlKem.X86.P0 s₀).mem s.mem
  f : ∀ i < 256, coeffAt s.mem (VG.Proof.MlKem.X86.fA s₀) i = if i < k then VG.Proof.MlKem.X86.newC F s₀ i else coeffAt s₀.mem (VG.Proof.MlKem.X86.fA s₀) i


namespace AccPre
variable {s₀ : State} (hp : VG.Proof.MlKem.X86.AccPre s₀)
include hp

theorem in_f {s : State} (hw : s.wr = (VG.Proof.MlKem.X86.P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (VG.Proof.MlKem.X86.fA s₀) k) 4 := by
  rw [hw, VG.Proof.MlKem.X86.P0_wr, hp.wr]
  exact ⟨polyRegion (VG.Proof.MlKem.X86.fA s₀), by simp, coeff_contains _ hk⟩

theorem in_f' {s : State} (hw : s.wr = (VG.Proof.MlKem.X86.P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (VG.Proof.MlKem.X86.fA s₀) k) 4 :=
  let ⟨r, h, c⟩ := hp.in_f hw hk; ⟨r, List.mem_append_right _ h, c⟩

theorem in_g {s : State} (hr : s.rd = (VG.Proof.MlKem.X86.P0 s₀).rd) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (VG.Proof.MlKem.X86.gA s₀) k) 4 := by
  rw [hr, pushed_rd, hp.rd]
  exact ⟨polyRegion (VG.Proof.MlKem.X86.gA s₀), by simp, coeff_contains _ hk⟩

/-- `g` is never written. -/
theorem g_keep {s : State} (hf : Frame [polyRegion (VG.Proof.MlKem.X86.fA s₀)] (VG.Proof.MlKem.X86.P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (VG.Proof.MlKem.X86.gA s₀) i = coeffAt s₀.mem (VG.Proof.MlKem.X86.gA s₀) i := by
  have f₁ := VG.Proof.MlKem.X86.P0_mem hp.sp
  rw [coeffAt_congr (m := s.mem) (m' := s₀.mem) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion (VG.Proof.MlKem.X86.gA s₀)) (by simpa using hp.f_g.symm) (VG.Proof.MlKem.X86.polyLen _) hj,
    f₁.bytes (R := polyRegion (VG.Proof.MlKem.X86.gA s₀)) (by simpa [← VG.Proof.MlKem.X86.stkR_eq hp.sp] using hp.stk_g.symm) (VG.Proof.MlKem.X86.polyLen _) hj]

theorem f_P0 {i : Nat} (hi : i < 256) : coeffAt (VG.Proof.MlKem.X86.P0 s₀).mem (VG.Proof.MlKem.X86.fA s₀) i = coeffAt s₀.mem (VG.Proof.MlKem.X86.fA s₀) i :=
  coeffAt_congr (fun j hj => (VG.Proof.MlKem.X86.P0_mem hp.sp).bytes (R := polyRegion (VG.Proof.MlKem.X86.fA s₀))
    (by simpa [← VG.Proof.MlKem.X86.stkR_eq hp.sp] using hp.stk_f.symm) (VG.Proof.MlKem.X86.polyLen _) hj) hi

theorem ea_f (k : Nat) (hk : k < 256) :
    (VG.Proof.MlKem.X86.fP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.fA s₀) k := by
  rw [VG.Proof.MlKem.X86.ea_add (by have := hp.f_fit; omega), Nat.add_zero]

theorem ea_g (k : Nat) (hk : k < 256) :
    (VG.Proof.MlKem.X86.gP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.gA s₀) k := by
  rw [VG.Proof.MlKem.X86.ea_add (by have := hp.g_fit; omega), Nat.add_zero]

end AccPre

theorem map_step {op : List Instr} {F : Nat → Nat → Nat} (hop : VG.Proof.MlKem.X86.OpSpec op F) {s₀ : State} (hp : VG.Proof.MlKem.X86.AccPre s₀) {k : Nat} (hk : k < 256)
    {s : State} (h : VG.Proof.MlKem.X86.MapInv F s₀ k s) :
    WP isa (.block (mapBody op)) s fun s' =>
      VG.Proof.MlKem.X86.MapInv F s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < n := hk
  have ef : s.ea (at_ .esi 0) = coeffAddr (VG.Proof.MlKem.X86.fA s₀) k := by
    rw [State.ea, at_, h.esi]; exact hp.ea_f k hk
  refine VG.Proof.MlKem.X86.wp_movm (by rw [ef]; exact hp.in_f' h.wr hk) ?_
  set s₁ := s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32) with hs₁
  have ha : (coeffAt s₀.mem (VG.Proof.MlKem.X86.fA s₀) k).toNat < q := hp.f_red k hk'
  have hb : (coeffAt s₀.mem (VG.Proof.MlKem.X86.gA s₀) k).toNat < q := hp.g_red k hk'
  have eg : s₁.ea (at_ .edi 0) = coeffAddr (VG.Proof.MlKem.X86.gA s₀) k := by
    simp only [hs₁, State.ea, at_, State.setReg, show Reg.edi ≠ Reg.eax by decide, ite_false, h.edi]
    exact hp.ea_g k hk
  refine hop _ s₁ _ _ _ ha hb ?_ ?_ ?_ fun s₂ o₂ v₂ => ?_
  · simp only [hs₁, State.setReg, ite_true]
    rw [ef, ← coeffAt_eq, h.f k hk, ite_eq_right (Nat.lt_irrefl k)]
  · rw [eg]; exact hp.in_g h.rd hk
  · rw [eg, show s₁.mem = s.mem from rfl, ← coeffAt_eq, hp.g_keep h.frame hk]
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [o₂.gpr r (by simp [h₁, h₂])]; simp [hs₁, State.setReg, h₁]
  have m₂ : s₂.mem = s.mem := o₂.mem
  have r₂ : s₂.rd = (VG.Proof.MlKem.X86.P0 s₀).rd := o₂.rd.trans h.rd
  have w₂ : s₂.wr = (VG.Proof.MlKem.X86.P0 s₀).wr := o₂.wr.trans h.wr
  have esi₂ : s₂.gpr .esi = VG.Proof.MlKem.X86.fP s₀ + BitVec.ofNat 32 (4 * k) := by rw [g₂ _ (by decide) (by decide), h.esi]
  have edi₂ : s₂.gpr .edi = VG.Proof.MlKem.X86.gP s₀ + BitVec.ofNat 32 (4 * k) := by rw [g₂ _ (by decide) (by decide), h.edi]
  have ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (256 - k) := by rw [g₂ _ (by decide) (by decide), h.ecx]
  have out : InRegions s₂.wr (coeffAddr (VG.Proof.MlKem.X86.fA s₀) k) 4 := hp.in_f w₂ hk
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, esi₂,
    hp.ea_f k hk, out, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hv : s₂.gpr .eax = VG.Proof.MlKem.X86.newC F s₀ k := VG.Proof.MlKem.X86.eq_ofNat_of_toNat v₂
  refine ⟨⟨by simp [g₂, h.esp], r₂, w₂, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · simp only [ite_true, ite_false, show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide]
    exact VG.Proof.MlKem.X86.ptr_next _ _ 4
  · simp only [ite_true, ite_false, show Reg.edi ≠ Reg.ecx by decide, edi₂]
    exact VG.Proof.MlKem.X86.ptr_next _ _ 4
  · simp only [ite_true, ecx₂]
    exact VG.Proof.MlKem.X86.cnt_next hk
  · rw [m₂]; exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk')
  · dsimp only
    rw [coeffAt_writeW _ _ (show i < n from hi) hk', m₂, hv, h.f i hi]
    by_cases e : k = i
    · subst e; simp
    · rw [ite_eq_right e]
      by_cases hik : i < k
      · rw [ite_eq_left hik, ite_eq_left (by omega)]
      · rw [ite_eq_right hik, ite_eq_right (by omega)]
  · simp only [eval, ecx₂]
    exact VG.Proof.MlKem.X86.cnt_ne hk (by decide)

/-! ## The function -/

/-- The public data: the stack pointer and the pointers. -/
def AccPub (s₀ s₀' : State) : Prop := VG.Proof.MlKem.X86.E0 s₀ = VG.Proof.MlKem.X86.E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- The arguments, which the push leaves in place. -/
theorem AccPre.arg_P0 {s₀ : State} (hp : VG.Proof.MlKem.X86.AccPre s₀) {i : Nat} (hi : i < 2) :
    ((VG.Proof.MlKem.X86.P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      InRegions ((VG.Proof.MlKem.X86.P0 s₀).rd ++ (VG.Proof.MlKem.X86.P0 s₀).wr) (argAddr s₀ i) 4 ∧
      (VG.Proof.MlKem.X86.P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hc : (VG.Proof.MlKem.X86.aR2 s₀).Contains (argAddr s₀ i) 4 := by
    have := hp.sp'
    simp only [argAddr, Region.Contains, VG.Proof.MlKem.X86.E0] at this ⊢
    bv_omega
  refine ⟨?_, ⟨VG.Proof.MlKem.X86.aR2 s₀, by simp [hp.wr], hc⟩, ?_⟩
  · rw [VG.Proof.MlKem.X86.P0_esp]; simp only [argAddr, VG.Proof.MlKem.X86.E0]; congr 1; bv_omega
  · exact (VG.Proof.MlKem.X86.P0_mem hp.sp).readW hc (by simpa [← VG.Proof.MlKem.X86.stkR_eq hp.sp] using hp.stk_a.symm) (by decide)

theorem init_piece (F : Nat → Nat → Nat) :
    VG.Proof.MlKem.X86.Piece VG.Proof.MlKem.X86.AccPre VG.Proof.MlKem.X86.AccPub (fun s₀ s => s = VG.Proof.MlKem.X86.P0 s₀) (VG.Proof.MlKem.X86.MapInv F · 0) (.block mapInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    obtain ⟨a₀, i₀, v₀⟩ := hp.arg_P0 (i := 0) (by omega)
    obtain ⟨a₁, i₁, v₁⟩ := hp.arg_P0 (i := 1) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
    apply WP.of_runBlock
    simp (config := {decide := true}) only [mapInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, i₀, i₁, v₀, v₁,
      ite_true, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, by simp, by simp, by simp, Frame.refl _ _, fun i hi => ?_⟩
    simp only [Nat.not_lt_zero, ite_false]
    exact hp.f_P0 hi
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', VG.Proof.MlKem.X86.P0_esp, VG.Proof.MlKem.X86.P0_esp, hq.1]

theorem loop_piece {op : List Instr} {F : Nat → Nat → Nat} (hop : VG.Proof.MlKem.X86.OpSpec op F)
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (mapBody op)) hc).isSome = true) :
    VG.Proof.MlKem.X86.Piece VG.Proof.MlKem.X86.AccPre VG.Proof.MlKem.X86.AccPub (VG.Proof.MlKem.X86.MapInv F · 0) (VG.Proof.MlKem.X86.MapInv F · 256) (.loop (.block (mapBody op)) .ne) :=
  Piece.loop (fun k s₀ s => VG.Proof.MlKem.X86.MapInv F s₀ k s) (by decide) fun k hk =>
    Piece.taint [.esp, .esi, .edi, .ecx] (fun _ _ hp h => VG.Proof.MlKem.X86.map_step hop hp hk h)
      (fun s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, VG.Proof.MlKem.X86.P0_esp, VG.Proof.MlKem.X86.P0_esp, hq.1]
        · rw [h.esi, h'.esi, VG.Proof.MlKem.X86.fP, VG.Proof.MlKem.X86.fP, hq.2.1]
        · rw [h.edi, h'.edi, VG.Proof.MlKem.X86.gP, VG.Proof.MlKem.X86.gP, hq.2.2]
        · rw [h.ecx, h'.ecx]) ht

theorem map_piece {op : List Instr} {F : Nat → Nat → Nat} (hop : VG.Proof.MlKem.X86.OpSpec op F)
    (hsp : NoSp (mapLoop op)) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (mapBody op)) hc).isSome = true) :
    VG.Proof.MlKem.X86.Piece VG.Proof.MlKem.X86.AccPre VG.Proof.MlKem.X86.AccPub (fun s₀ s => s = s₀) (fun s₀ s' => VG.Proof.MlKem.X86.LeafPost (VG.Proof.MlKem.X86.MapInv F s₀ 256) s₀ s')
      (VG.Impl.MlKem.X86.leaf (mapLoop op)) :=
  Piece.leaf (fun s₀ => [polyRegion (VG.Proof.MlKem.X86.fA s₀)]) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← VG.Proof.MlKem.X86.stkR_eq hp.sp]; exact hp.stk_f, hp.ret_f⟩)
    (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (VG.Proof.MlKem.X86.init_piece F) (VG.Proof.MlKem.X86.loop_piece hop ht)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem vec_zipWith_get (G : Zq → Zq → Zq) (f g : Poly) {i : Nat} (hi : i < n) :
    (Vector.zipWith G f g)[i]! = G f[i]! g[i]! := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, getElem!_eq _ hi, Vector.getElem_zipWith]

/-- The polynomial the loop leaves. -/
theorem map_post {F : Nat → Nat → Nat} {G : Zq → Zq → Zq} (hG : ∀ x y : Zq, (G x y).val = F x.val y.val)
    {s₀ s : State} (hp : VG.Proof.MlKem.X86.AccPre s₀) (h : VG.Proof.MlKem.X86.MapInv F s₀ 256 s) :
    PolyIs s.mem (VG.Proof.MlKem.X86.fA s₀) (Vector.zipWith G (polyAt s₀.mem (VG.Proof.MlKem.X86.fA s₀)) (polyAt s₀.mem (VG.Proof.MlKem.X86.gA s₀))) := by
  refine polyIs_of_toNat fun i hi => ?_
  have hlt := val_lt (G (polyAt s₀.mem (VG.Proof.MlKem.X86.fA s₀))[i]! (polyAt s₀.mem (VG.Proof.MlKem.X86.gA s₀))[i]!)
  rw [hG, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi] at hlt
  rw [h.f i hi, ite_eq_left hi, VG.Proof.MlKem.X86.vec_zipWith_get _ _ _ hi, hG, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi,
    VG.Proof.MlKem.X86.newC, VG.Proof.MlKem.X86.toNat_ofNat32 (by omega)]


/-- Memory whose argument words (at `0x5004`) hold `0` and `0x400`. -/
def accSatMem : Mem := fun a => if a = 0x5009 then 4 else 0

/-- A state satisfying the precondition: `f` at `0`, `g` at `0x400`. -/
def accSat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.MlKem.X86.accSatMem
  rd := [⟨0x400, 1024⟩]
  wr := [⟨0, 1024⟩, ⟨0x5004, 8⟩]

theorem accSat_red (p : Nat) (hp : p + 1024 ≤ 0x5000) : Reduced VG.Proof.MlKem.X86.accSatMem (BitVec.ofNat 64 p) :=
  VG.Proof.MlKem.X86.reduced_of_zero fun k hk => by
    simp only [VG.Proof.MlKem.X86.accSatMem]
    rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega)]

theorem add_verified : Verified X86.target add (addContract X86.abi 16) := by
  refine Piece.verified (((VG.Proof.MlKem.X86.map_piece VG.Proof.MlKem.X86.addOp_spec (NoSp.of_all (by decide +kernel)) (by taint_decide)).pre_mono
    (fun _ h => AccPre.of_add h) fun s s' _ _ h => by
      sig_pub [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact VG.Proof.MlKem.X86.map_post (G := (· + ·)) (fun x y => val_add x y) (AccPre.of_add h₀) hinv
  · refine ⟨VG.Proof.MlKem.X86.accSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg VG.Proof.MlKem.X86.accSat 0) = BitVec.ofNat 64 0 by decide]
           exact VG.Proof.MlKem.X86.accSat_red 0 (by decide))
        | (rw [show BitVec.setWidth 64 (arg VG.Proof.MlKem.X86.accSat 1) = BitVec.ofNat 64 0x400 by decide]
           exact VG.Proof.MlKem.X86.accSat_red 0x400 (by decide))
        | decide +kernel

theorem sub_verified : Verified X86.target sub (subContract X86.abi 16) := by
  refine Piece.verified (((VG.Proof.MlKem.X86.map_piece VG.Proof.MlKem.X86.subOp_spec (NoSp.of_all (by decide +kernel)) (by taint_decide)).pre_mono
    (fun _ h => AccPre.of_sub h) fun s s' _ _ h => by
      sig_pub [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact VG.Proof.MlKem.X86.map_post (G := (· - ·)) (fun x y => val_sub x y) (AccPre.of_sub h₀) hinv
  · refine ⟨VG.Proof.MlKem.X86.accSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg VG.Proof.MlKem.X86.accSat 0) = BitVec.ofNat 64 0 by decide]
           exact VG.Proof.MlKem.X86.accSat_red 0 (by decide))
        | (rw [show BitVec.setWidth 64 (arg VG.Proof.MlKem.X86.accSat 1) = BitVec.ofNat 64 0x400 by decide]
           exact VG.Proof.MlKem.X86.accSat_red 0x400 (by decide))
        | decide +kernel
end VG.Proof.MlKem.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.CallRet`. -/
section

/-!
# ML-KEM on x86 (32-bit): calls that return a value

`callWith` pops the frame of a call's arguments into `eax`, where the callee
returns its value; `callRet` pops it into `ecx` instead, and `WP.callRet` also
gives the value in `eax` of the state the callee's postcondition holds of.
-/

namespace VG.X86

open VG.Impl.MlKem.X86 (callRet)

theorem WP.callRet {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) {s : VG.X86.State}
    (hd : 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat) {rd wr : List Region}
    (hk : CallPre k rs rd wr s) {Q : VG.X86.State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : VG.X86.State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post ((pushed rs s).callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (VG.Impl.MlKem.X86.callRet rs n c) s Q := by
  have hn : 4 * rs.length ≤ (s.gpr .esp).toNat := by omega
  have e : ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
    rw [pushed_esp, VG.X86.sub_toNat hn]
  refine WP.frame hne hrs (by decide) hn (fun i hi => hsp i hi) ?_
  refine WP.call hv hsp (by rw [e]; omega) hk.pre (by rw [pushed_rd, pushed_wr]; exact hk.cov)
    (by rw [pushed_wr]; exact hk.covw) fun s₂ rd₂ wr₂ cs₂ f₂ _ ⟨s₃, m₃, g₃, post₃⟩ => ?_
  refine hQ _ (by rw [popped_rd, rd₂, pushed_rd]) (by rw [popped_wr, wr₂, pushed_wr]; rfl) (fun r hr => ?_) ?_
    ⟨s₃, by rw [m₃, popped_mem], by rw [popped_gpr _ _ _ (by decide) (by decide), g₃ _ (by decide)], post₃⟩
  · by_cases h : r = .esp
    · subst h
      rw [popped_esp, cs₂ .esp hr, pushed_esp]; exact BitVec.sub_add_cancel _ _
    · have hne' : r ≠ .ecx := by
        rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ h hne', cs₂ r hr, pushed_gpr _ _ h]
  · rw [popped_mem]
    refine ((pushed_frame hrs hn).sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) hd⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [pushed_esp]
        exact below_inner (by omega) hd

theorem RelCT.callRet {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : VG.X86.State → VG.X86.State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ → CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧
      s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    RelCT isa P (VG.Impl.MlKem.X86.callRet rs n c) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP _ _ h).2.2.1) (RelCT.call hv hct rd wr ?_)
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨k₁, k₂, hsp, hpub⟩ := hP _ _ h
  refine ⟨k₁.pre, k₂.pre, hpub, by rw [pushed_rd, pushed_wr]; exact k₁.cov, by rw [pushed_wr]; exact k₁.covw,
    by rw [pushed_rd, pushed_wr]; exact k₂.cov, by rw [pushed_wr]; exact k₂.covw, ?_⟩
  rw [pushed_esp, pushed_esp, hsp]

end VG.X86

namespace VG.Proof.MlKem.X86.Piece

open VG VG.X86 VG.Impl.MlKem.X86

variable {Pre : VG.X86.State → Prop} {Pub : VG.X86.State → VG.X86.State → Prop}

/-- `Piece.callWith`, for `callRet`. -/
theorem callRet {A B : VG.X86.State → VG.X86.State → Prop} {rs : List Reg} {n : String} {c : Prog isa}
    {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    (rd wr : VG.X86.State → List Region)
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat)
    (hk : ∀ s₀ s, Pre s₀ → A s₀ s → CallPre k rs (rd s₀) (wr s₀) s)
    (hpub : ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧ s.gpr .esp = s'.gpr .esp ∧
      k.pub ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr s₀ ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : VG.X86.State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    VG.Proof.MlKem.X86.Piece Pre Pub A B (VG.Impl.MlKem.X86.callRet rs n c) where
  wp s₀ s h₀ ha := WP.callRet hv hsp hne hrs (hd _ _ h₀ ha) (hk _ _ h₀ ha)
    fun s' h₁ h₂ h₃ h₄ h₅ => hQ _ _ _ h₀ ha h₁ h₂ h₃ h₄ h₅
  ct s₀ s₀' h₀ h₀' hp := RelCT.callRet hv hct (rd s₀) (wr s₀) fun s s' ⟨a, a'⟩ => by
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub _ _ _ _ h₀ h₀' hp a a'
    exact ⟨hk _ _ h₀ a, e₁ ▸ e₂ ▸ hk _ _ h₀' a', e₃, e₄⟩

end VG.Proof.MlKem.X86.Piece

end
