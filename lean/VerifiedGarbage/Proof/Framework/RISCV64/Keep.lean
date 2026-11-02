module

public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# What RISC-V code keeps

Untrusted: everything here is checked by Lean. `Keep rs s s'` says that `s'`
differs from `s` only in the registers `rs` (and memory), with the same
permissions; `WP.keep` adds it to a postcondition for code without calls
(`callFree`; frames are allowed, which restore every register their pushes
and pops do not write) whose instructions write only `rs` (`writesOnly`,
decided by evaluation), as `VG.PPC64LE.WP.keep` does.
-/

@[expose] public section

namespace VG.RISCV64

/-- `s'` differs from `s` only in the registers `rs` (memory aside), with the
same permissions. -/
def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂)
    (h₂ : Keep rs' s₂ s₃) : Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

/-- Whether code calls no function; it may have frames. -/
def callFree : Prog isa → Bool
  | .block _ => true
  | .seq a b => callFree a && callFree b
  | .ite _ t e => callFree t && callFree e
  | .loop b _ => callFree b
  | .call _ _ => false
  | .frame _ b _ => callFree b
  | .icall .. => false

/-- A register that no instruction of code without calls writes keeps its
value. -/
theorem Exec.gpr_callFree {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, dstOf i ≠ some r)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') (hn : callFree c = true) :
    s'.gpr r = s.gpr r := by
  induction h with
  | icall hi => nomatch hi
  | icallNext hi => nomatch hi
  | block h => exact execBlock_gpr hc h
  | seq _ _ ih₁ ih₂ =>
    simp only [callFree, Bool.and_eq_true] at hn
    rw [ih₂ (fun i hi => hc i (List.mem_append_right _ hi)) hn.2,
      ih₁ (fun i hi => hc i (List.mem_append_left _ hi)) hn.1]
  | iteT _ _ ih =>
    simp only [callFree, Bool.and_eq_true] at hn
    exact ih (fun i hi => hc i (List.mem_append_left _ hi)) hn.1
  | iteF _ _ ih =>
    simp only [callFree, Bool.and_eq_true] at hn
    exact ih (fun i hi => hc i (List.mem_append_right _ hi)) hn.2
  | loopExit _ _ ih => exact ih hc hn
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc hn, ih₁ hc hn]
  | call => simp [callFree] at hn
  | frame hp _ hq ih =>
    obtain ⟨-, -, -, hg, -⟩ := push_eq hp
    rw [(pop_eq hq).2.2.2.1 r (hc _ (by simp [instrs])),
      ih (fun i hi => hc i (by simp [instrs, hi])) hn, hg]

/-- Every instruction of the code writes only registers among `rs`. -/
noncomputable def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => match dstOf i with
    | none => true
    | some r => rs.contains r

/-- Registers that no instruction of code without calls writes keep their
values. -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa c s Q) (hc : writesOnly rs c = true)
    (hn : callFree c = true := by decide +kernel) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr_callFree (fun i hi => ?_) he hn,
    (Exec.rdwr he).1, (Exec.rdwr he).2.1⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have hh := hc i hi
  intro hd
  rw [hd] at hh
  exact hr (List.contains_iff_mem.mp hh)

/-- Code keeps the permissions and the stack pointer. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.rdwr he⟩

/-- Code without calls that writes neither a preserved register nor `ra`
keeps what the calling convention preserves. -/
theorem abiPreserved_of_keep {c : Prog isa} {s s' : State} {t : List Leak} {rs : List Reg}
    (he : Exec isa c s t s') (hk : Keep rs s s') (hp : ∀ r ∈ preserved, r ∉ rs)
    (hra : Reg.ra ∉ rs) : abiPreserved s s' :=
  ⟨fun r hr => hk.gpr (hp r hr), Exec.sp he, hk.gpr hra⟩

end VG.RISCV64
