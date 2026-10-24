module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingBase
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.TaintErase
public import VerifiedGarbage.Proof.Mont.Words

/-! # Two runs at a branch on a state word -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation

/-- After a comparison of a state word, from a state where `Φ a` held:
only `eax` and the flags changed. -/
def CmpAfter {α : Type} (Φ : α → State → Prop) (a : α) (t : State) : Prop :=
  ∃ s, Φ a s ∧ (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    t.syms = s.syms

theorem CmpAfter.base {α : Type} {Φ : α → State → Prop} {E : Env} (hb : ∀ a s, Φ a s → Base E s) {a : α}
    {t : State} (h : CmpAfter Φ a t) : Base E t := by
  obtain ⟨s, hs, g, m, rd, wr, sy⟩ := h
  exact (hb a s hs).regs m (g _ (by decide)) (g _ (by decide)) rd wr sy

theorem cmpF_erase (o v : Nat) : Code.erase (.block (cmpF o v)) = Code.erase (.block (cmpF 0 0)) := rfl

theorem stImm_erase (o v : Nat) : Code.erase (.block (stImm o v)) = Code.erase (.block (stImm 0 0)) := rfl

/-- A store of a constant into a state word. -/
theorem stImm_ct {α : Type} {Φ : α → State → Prop} {E : Env} (hb : ∀ a s, Φ a s → Base E s) (o v : Nat) :
    RelCT isa (Both Φ) (.block (stImm o v)) fun _ _ => True :=
  both_agree [.esp, .edi] (fun _ => baseVal E) (fun a s h => base_pins (hb a s h))
    (tcheckE _ _ (.block (stImm 0 0)) (stImm_erase _ _) (by decide +kernel) (by decide +kernel))

/-- A comparison of the state word at `o`, whose value `w a` the parameters
fix, then a branch on it. -/
theorem cmpF_ct {α : Type} {Φ : α → State → Prop} {E : Env} {o v : Nat} (ho : o + 4 ≤ E.size)
    (hv : v < 2 ^ 32) (w : α → Nat) (hb : ∀ a s, Φ a s → Base E s)
    (hw : ∀ a s, Φ a s → s.mem.readW (off E.base o) 32 = BitVec.ofNat 32 (w a)) (hwl : ∀ a, w a < 2 ^ 32)
    {th el : Prog isa} {Q : State → State → Prop}
    (ht : RelCT isa (Both fun a t => CmpAfter Φ a t ∧ decide (w a = v) = true) th Q)
    (he : RelCT isa (Both fun a t => CmpAfter Φ a t ∧ decide (w a = v) = false) el Q) :
    RelCT isa (Both Φ) (.seq (.block (cmpF o v)) (.ite .e th el)) Q := by
  refine RelCT.seq (both_post (Ψ := fun a t => CmpAfter Φ a t ∧ isa.eval .e t = some (decide (w a = v)))
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a s h => base_pins (hb a s h))
      (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    fun a s h => cmpF_end (hb a s h).scr ho (hw a s h) (hwl a) hv fun t g m rd wr sy z =>
      ⟨⟨s, h, g, m, rd, wr, sy⟩, z⟩) ?_
  exact both_ite (fun a => decide (w a = v)) (fun a t h => h.2)
    (ht.mono (fun _ _ ⟨a, ⟨h₁, e⟩, h₂, _⟩ => ⟨a, ⟨h₁.1, e⟩, h₂.1, e⟩) fun _ _ h => h)
    (he.mono (fun _ _ ⟨a, ⟨h₁, e⟩, h₂, _⟩ => ⟨a, ⟨h₁.1, e⟩, h₂.1, e⟩) fun _ _ h => h)

end VG.Proof.Dsa.X86.Generation
