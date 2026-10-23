module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# What PPC64LE code keeps

Untrusted: everything here is checked by Lean. `Keep rs s s'` says that `s'`
differs from `s` only in the registers `rs` (and memory), with the same
permissions; `WP.keep` adds it to a postcondition for code without calls
whose instructions write only `rs` (`writesOnly`, decided by evaluation).
-/

@[expose] public section

namespace VG.PPC64LE

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

/-- Every instruction of the code writes only registers among `rs`. -/
def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => match dstOf i with
    | none => true
    | some r => rs.contains r

/-- Registers that no instruction of code without calls writes keep their
values. -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa c s Q) (hc : writesOnly rs c = true)
    (hn : c.noCalls = true := by decide +kernel) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn),
    (Exec.rdwr he).1, (Exec.rdwr he).2.1⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have hh := hc i hi
  intro hd
  rw [hd] at hh
  exact hr (List.contains_iff_mem.mp hh)

/-- Code that writes only volatile registers, never `sp` or `lr` and without
calls or frames keeps what the calling convention preserves. -/
theorem abiPreserved_of_keep {c : Prog isa} {s s' : State} {t : List Leak} {rs : List Reg}
    (he : Exec isa c s t s') (hk : Keep rs s s') (hp : ∀ r ∈ preserved, r ∉ rs)
    (hn : c.noCalls = true) (hl : (instrs c).all (fun i => !i.writesLr) = true) :
    abiPreserved s s' :=
  ⟨fun r hr => hk.gpr (hp r hr), Exec.sp he, Exec.lr he hn hl⟩

end VG.PPC64LE
