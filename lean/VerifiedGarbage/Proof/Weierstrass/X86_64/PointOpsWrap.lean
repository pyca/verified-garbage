import VerifiedGarbage.Impl.Weierstrass.X86_64.PointOps
import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming

/-!
# Point operations as functions on x86-64: the registers they keep

A function's body runs between `saves`, which copies `rbp` and `r12`–`r15`
into `xmm0`–`xmm4` and changes nothing else that the proofs follow
(`saves_ok`), and `restores`, which copies them back and changes only them
(`restores_ok`): a run of `wrap d` is a run of `d` from a state that keeps
every register and the memory (`wrap_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Weierstrass.X86_64.PointOps
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64

/-- The registers `restores` writes. -/
abbrev keptRegs : List Reg := kept.map Prod.fst

private theorem setXmm_gpr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl

theorem saves_ok (s : State) : WP isa (.block saves) s fun t => Keeps [] s t := by
  apply WP.of_runBlock
  simp only [saves, kept, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, Option.some.injEq, exists_eq_left', setXmm_gpr]
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem restores_ok (s : State) : WP isa (.block restores) s fun t => Keeps keptRegs s t := by
  apply WP.of_runBlock
  simp only [restores, kept, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2]

/-- A run of `wrap d`: `d` from a state keeping every register and the
memory, then `restores`, which keeps all but `keptRegs`. -/
theorem wrap_ok {d : Prog isa} {s : State} {F : State → Prop}
    (h : ∀ s₁, Keeps [] s s₁ → s₁.syms = s.syms →
      WP isa d s₁ fun t => ∀ u, Keeps keptRegs t u → u.syms = t.syms → F u) :
    WP isa (wrap d) s F :=
  WP.seq (WP.mono_syms (saves_ok s) fun s₁ k₁ y₁ =>
    WP.seq (WP.mono (h s₁ k₁ y₁) fun t ht => WP.mono_syms (restores_ok t) fun u ku yu => ht u ku yu))

/-- `ProgKeep` from `Keeps` of registers the field arithmetic may write. -/
theorem progKeep_of_keeps {M : Mod} {base : Addr} {W : List Nat} {s t : State} {rs : List Reg}
    (hk : Keeps rs s t) (hr : ∀ r ∈ rs, r ∈ clob M.n) : ProgKeep M base W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')), hk.2.2.1, hk.2.2.2, fun x _ _ => congrFun hk.2.1 x⟩

/-- `wrap d` keeps what `d` keeps, for a precondition `P` and a postcondition
`F` that the registers `saves` and `restores` write do not affect. -/
theorem wrap_keep_ok {M : Mod} {base : Addr} {W : List Nat} {d : Prog isa} {s : State}
    {P F : State → Prop} (hclob : ∀ r ∈ keptRegs, r ∈ clob M.n)
    (hP : ∀ x y, ProgKeep M base W x y → Keeps [] x y → y.syms = x.syms → P x → P y)
    (hF : ∀ x y, ProgKeep M base W x y → Keeps keptRegs x y → y.syms = x.syms → F x → F y)
    (hs : P s) (hd : ∀ x, P x → WP isa d x fun t => ProgKeep M base W x t ∧ F t) :
    WP isa (wrap d) s fun t => ProgKeep M base W s t ∧ F t := by
  apply wrap_ok
  intro s₁ k₁ y₁
  have p₁ : ProgKeep M base W s s₁ := progKeep_of_keeps k₁ (by simp)
  refine WP.mono (hd s₁ (hP s s₁ p₁ k₁ y₁ hs)) fun t ⟨kt, ft⟩ u ku yu => ?_
  have pu : ProgKeep M base W t u := progKeep_of_keeps ku hclob
  exact ⟨(p₁.trans kt).trans pu, hF t u pu ku yu ft⟩

/-! ## The callee-saved registers -/

theorem allInstrs_block {p : Instr → Bool} : ∀ (is : List Instr), (Code.block is : Prog isa).allInstrs p = is.all p
  | [] => rfl
  | i :: is => by
    have h := allInstrs_block (p := p) is
    simp only [Code.allInstrs] at h ⊢
    simp only [List.all_cons, h]

theorem execBlock_xmm : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    is.all (fun i => !KeepReg.writesVec i) = true → execBlock isa is s = some (s', t) → s'.xmm = s.xmm
  | [], s, s', t, _, h => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | i :: is, s, s', t, hv, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hv
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      exact (execBlock_xmm (t := p.2) hv.2 (by rw [hp])).trans (KeepReg.exec_xmm hv.1 h₁)

/-- Code that writes no vector register, and calls nothing, keeps the SSE
registers. -/
theorem Exec.xmm_of {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    c.allInstrs (fun i => !KeepReg.writesVec i) = true → c.noCalls = true → s'.xmm = s.xmm := by
  induction h with
  | block he =>
    intro hv _
    rw [allInstrs_block] at hv
    exact execBlock_xmm hv he
  | seq _ _ ih₁ ih₂ =>
    intro hv hn
    simp only [Code.allInstrs, Code.noCalls, Bool.and_eq_true] at hv hn
    exact (ih₂ hv.2 hn.2).trans (ih₁ hv.1 hn.1)
  | iteT _ _ ih =>
    intro hv hn
    simp only [Code.allInstrs, Code.noCalls, Bool.and_eq_true] at hv hn
    exact ih hv.1 hn.1
  | iteF _ _ ih =>
    intro hv hn
    simp only [Code.allInstrs, Code.noCalls, Bool.and_eq_true] at hv hn
    exact ih hv.2 hn.2
  | loopExit _ _ ih =>
    intro hv hn
    exact ih hv hn
  | loopNext _ _ _ ih₁ ih₂ =>
    intro hv hn
    exact (ih₂ hv hn).trans (ih₁ hv hn)
  | call => intro _ hn; simp [Code.noCalls] at hn
  | frame => intro _ hn; simp [Code.noCalls] at hn

/-- `wrap body` restores the registers it saves, if `body` writes no vector
register and calls nothing: `saves` copies each into its `xmm` register,
which `body` keeps, and `restores` copies it back. -/
theorem wrap_gpr {body : Prog isa} (hv : body.allInstrs (fun i => !KeepReg.writesVec i) = true)
    (hn : body.noCalls = true) {s s' : State} {t : List Leak} (he : Exec isa (wrap body) s t s') :
    ∀ r ∈ keptRegs, s'.gpr r = s.gpr r := by
  intro r hr
  cases he with
  | seq h₁ h₂ =>
    cases h₂ with
    | seq h₂ h₃ =>
      have hs := KeepReg.Exec.holds (v := s.gpr r) h₁ (a := ⟨true, .empty⟩) rfl
        ⟨fun _ => rfl, fun x hx => absurd hx (RegSet.not_mem_empty x)⟩
      let A := KeepReg.run r saves true 0
      have hA : KeepReg.Holds r (s.gpr r) ⟨false, A.xs⟩ _ :=
        hs.mono (a := ⟨false, A.xs⟩) (by
          simp only [KeepReg.le, Bool.not_false, Bool.true_or, Bool.true_and]
          rw [RegSet.subset_eq]
          simp only [A, show (RegSet.empty : RegSet XReg).bits = 0 from rfl, Nat.and_self, beq_self_eq_true])
      have hx := Exec.xmm_of h₂ hv hn
      have hB : KeepReg.Holds r (s.gpr r) ⟨false, A.xs⟩ _ := ⟨nofun, fun x h => by
        rw [hx]; exact hA.2 x h⟩
      have hr' := KeepReg.Exec.holds (v := s.gpr r) h₃ (a := ⟨false, A.xs⟩) rfl hB
      refine hr'.1 ?_
      simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- What the functions' checks ask of their code `wrap b`, in one pass: no
instruction loads MXCSR, and `b` writes no vector register. -/
def wrapOk : Prog isa → Bool
  | .seq (.block sv) (.seq b (.block rs)) =>
    sv.all (fun i => !loadsMxcsr i) && rs.all (fun i => !loadsMxcsr i) &&
      b.allInstrs (fun i => !KeepReg.writesVec i && !loadsMxcsr i)
  | _ => false

theorem allInstrs_and {p q : Instr → Bool} : ∀ (c : Prog isa),
    c.allInstrs (fun i => p i && q i) = true → c.allInstrs p = true ∧ c.allInstrs q = true := by
  intro c h
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  refine ⟨?_, ?_⟩ <;> rw [Code.allInstrs_eq, List.all_eq_true] <;> intro i hi <;>
    have := h i hi <;> simp only [Bool.and_eq_true] at this
  · exact this.1
  · exact this.2

theorem wrapOk_spec {b : Prog isa} (h : wrapOk (wrap b) = true) :
    b.allInstrs (fun i => !KeepReg.writesVec i) = true ∧
      (wrap b).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [wrapOk, wrap, Bool.and_eq_true] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  obtain ⟨hv, hm⟩ := allInstrs_and b h₃
  refine ⟨hv, ?_⟩
  show ((Code.block saves : Prog isa).allInstrs _ && (b.allInstrs _ &&
    (Code.block restores : Prog isa).allInstrs _)) = true
  rw [allInstrs_block, allInstrs_block, h₁, h₂, hm]
  rfl

/-! ## Timing -/

theorem saves_ct : ScratchCT (.block saves) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem restores_ct : ScratchCT (.block restores) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- `wrap d` is constant time for runs agreeing on the field values `E` of
the slots `V` if `d` is. -/
theorem wrap_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    {V W : List Nat} {E : Nat → Fin m} {d : Prog isa}
    (hd : RelCT isa (FieldPair M base size m Sl V E) d
      (fun s t => ∃ E', FieldPair M base size m Sl W E' s t)) :
    RelCT isa (FieldPair M base size m Sl V E) (wrap d)
      (fun s t => ∃ E', FieldPair M base size m Sl W E' s t) :=
  RelCT.seq (fieldProgram_relCT saves_ct fun s h => WP.mono (saves_ok s) fun _ k => h.of_keeps k (by simp))
    (RelCT.seq hd (RelCT.exists_ fun E' =>
      (fieldProgram_relCT (V := W) (E := E') restores_ct fun s h =>
        WP.mono (restores_ok s) fun _ k => h.of_keeps k (by decide)).mono
        (fun _ _ h => h) fun _ _ h => ⟨E', h⟩))

end VG.Proof.Weierstrass.X86_64.PointOps
