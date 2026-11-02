module

public import VerifiedGarbage.Impl.SubstLocal
public import VerifiedGarbage.Proof.Framework.Subst

/-! Inline substitutions preserve behavior without changing registered callees. -/

@[expose] public section
namespace VG
variable {M : ISA} [DecidableEq M.Instr] [DecidableEq M.Cond]

theorem Exec.substLocal {a b : Prog M} (hab : Sim a b) {c : Prog M}
    {s s' : M.State} {t : List Leak} (h : Exec M c s t s') :
    Exec M (Code.substLocal a b c) s t s' := by
  induction h with
  | block h =>
    simp only [Code.substLocal]; split
    · rename_i e; exact hab (e ▸ .block h)
    · exact .block h
  | seq h₁ h₂ ih₁ ih₂ =>
    simp only [Code.substLocal]; split
    · rename_i e; exact hab (e ▸ .seq h₁ h₂)
    · exact .seq ih₁ ih₂
  | iteT hc h ih =>
    simp only [Code.substLocal]; split
    · rename_i e; exact hab (e ▸ .iteT hc h)
    · exact .iteT hc ih
  | iteF hc h ih =>
    simp only [Code.substLocal]; split
    · rename_i e; exact hab (e ▸ .iteF hc h)
    · exact .iteF hc ih
  | loopExit h hc ih =>
    simp only [Code.substLocal]; split
    · rename_i e; exact hab (e ▸ .loopExit h hc)
    · exact .loopExit ih hc
  | loopNext h hc h' ih ih' =>
    simp only [Code.substLocal]; split
    · rename_i e; exact hab (e ▸ .loopNext h hc h')
    · rename_i e
      simp only [Code.substLocal, e, ↓reduceIte] at ih'
      exact .loopNext ih hc ih'
  | call hc h hr _ => exact .call hc h hr
  | frame hp h hq ih =>
    simp only [Code.substLocal]; split
    · rename_i e; exact hab (e ▸ .frame hp h hq)
    · exact .frame hp ih hq
  | icall hi hc h hr _ => exact .icall hi hc h hr
  | icallNext hi hne h _ => exact .icallNext hi hne h

/-- Call-free replacements cannot change any named call recorded by the emitter. -/
theorem Code.calls_substLocal {a b c : Prog M} (ha : a.calls = []) (hb : b.calls = []) :
    (Code.substLocal a b c).calls = c.calls := by
  induction c with
  | block is => simp only [Code.substLocal]; split <;> simp_all [Code.calls]
  | seq x y ihx ihy =>
    simp only [Code.substLocal]; split
    · rename_i equal; rw [← equal] at ha; exact hb.trans ha.symm
    · simp only [Code.calls, ihx, ihy]
  | ite k x y ihx ihy =>
    simp only [Code.substLocal]; split
    · rename_i equal; rw [← equal] at ha; exact hb.trans ha.symm
    · simp only [Code.calls, ihx, ihy]
  | loop x k ih =>
    simp only [Code.substLocal]; split
    · rename_i equal; rw [← equal] at ha; exact hb.trans ha.symm
    · exact ih
  | call n x _ => rfl
  | icall => rfl
  | frame i x j ih =>
    simp only [Code.substLocal]; split
    · rename_i equal; rw [← equal] at ha; exact hb.trans ha.symm
    · exact ih

end VG
