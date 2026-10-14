module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.CtrsBe
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The counters' constants, kept by the output written

`R10.dataTo`: `R10` (with a public block index, the constants in the
working space) is kept by sixteen output blocks written out of place.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode nb pp pR oR)
open VG.Proof.Gcm.X86_64.StitchZTo (oAddr)
open VG.Proof.Gcm.X86_64.StitchZ (R10 BeConsts)

/-- The working space at `pp + o` is kept by the sixteen output blocks
written from block `c`. -/
theorem keepAtTo {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} (hc : c + 16 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨oAddr s₀ c, 256⟩] m m') {o : Nat} (ho : o + 16 ≤ 1024) :
    m'.readW (pp s₀ + BitVec.ofNat 64 o) 128 = m.readW (pp s₀ + BitVec.ofNat 64 o) 128 := by
  have hw := hp.wrap_o
  have hwp := hp.wrap_p
  exact hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.o_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)

/-- `R10` is kept by the sixteen output blocks written from block `c`, with
`r10` kept. -/
theorem R10.dataTo {M : CtxMode} {be : Bool} {s₀ : State} (hp : SPreTo M s₀) {c c' : Nat} (hc : c + 16 ≤ nb s₀)
    {s s' : State} (h : R10 be s₀ c' s) (hg : s'.gpr .r10 = s.gpr .r10)
    (hf : Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem) : R10 be s₀ c' s' := by
  cases be
  · simp only [R10, Bool.false_eq_true, ↓reduceIte] at h ⊢; rw [hg]; exact h
  · simp only [R10, ↓reduceIte, BeConsts] at h ⊢
    exact ⟨by rw [hg]; exact h.1, by rw [keepAtTo hp hc hf (by decide)]; exact h.2.1,
      by rw [keepAtTo hp hc hf (by decide)]; exact h.2.2⟩

end VG.Proof.Gcm.X86_64.StitchZHTo
