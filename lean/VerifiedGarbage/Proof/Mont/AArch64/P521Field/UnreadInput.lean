module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamInvariant
import VerifiedGarbage.Proof.Framework.Omega

/-! Streaming products may overwrite already-consumed input limbs. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- Only input bytes at or beyond the written prefix remain live. This
admits exact input/output aliasing without permitting partial overlap. -/
def UnreadInput (s₀ : State) (pa pt : Addr) : Prop :=
  ∀ n, n≤64 → ∀m,Outside pt 0 n s₀.mem m →
    ∀d,n≤d → d+8≤72 → word m pa d=word s₀.mem pa d

theorem unread_input_alias (s : State) (p : Addr) : UnreadInput s p p := by
  intro n hn m hm d hd hd72
  exact hm.word (Or.inr (by omega_arith)) (by omega_arith)

theorem unread_input_of_stable {s : State} {pa pt : Addr}
    (stable : StableInput s pa pt) : UnreadInput s pa pt := by
  intro n hn m hm d _ hd
  exact stable m (hm.mono (o':=0) (n':=64) (by decide) (by omega_arith)) d hd

/-- A two-limb spill retains all future input limbs, including when the
spill destination is the input itself. -/
theorem unread_after_spill {s₀ s : State} {pa pt : Addr} {i : Nat} {m : Mem}
    (stable : UnreadInput s₀ pa pt) (hi : i+2≤8)
    (before : Outside pt 0 (8*i) s₀.mem s.mem)
    (spill : Outside pt (8*i) 16 s.mem m) :
    Outside pt 0 (8*(i+2)) s₀.mem m ∧
    ∀d,8*(i+2)≤d → d+8≤72 → word m pa d=word s₀.mem pa d := by
  have whole : Outside pt 0 (8*(i+2)) s₀.mem m :=
    (before.mono (o':=0) (n':=8*(i+2)) (by decide) (by omega_arith)).trans
      (spill.mono (o':=0) (n':=8*(i+2)) (by omega_arith) (by omega_arith))
  exact ⟨whole,fun d hd hd72 => stable _ (by omega_arith) m whole d hd hd72⟩

/-- The immediate next two-limb load sees the same words before and after
that spill; earlier consumed input is intentionally unconstrained. -/
theorem unread_spill_next {s₀ s : State} {pa pt : Addr} {i : Nat} {m : Mem}
    (stable : UnreadInput s₀ pa pt) (hi : i+4≤9)
    (before : Outside pt 0 (8*i) s₀.mem s.mem)
    (spill : Outside pt (8*i) 16 s.mem m) :
    word m pa (8*(i+2))=word s.mem pa (8*(i+2)) ∧
    word m pa (8*(i+2)+8)=word s.mem pa (8*(i+2)+8) := by
  have after := (unread_after_spill stable (by omega_arith) before spill).2
  exact ⟨(after _ (by omega_arith) (by omega_arith)).trans
      (stable _ (by omega_arith) s.mem before _ (by omega_arith) (by omega_arith)).symm,
    (after _ (by omega_arith) (by omega_arith)).trans
      (stable _ (by omega_arith) s.mem before _ (by omega_arith) (by omega_arith)).symm⟩

end VG.Proof.Mont.AArch64.P521Field
