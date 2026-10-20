module

public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Cold branches

`Code.iteCold c t e` (`TCB/Code.lean`) is `ite c t e` with `t` behind two
empty blocks, which run as nothing and leak nothing: it runs, leaks and is
proven as `ite c t e` (`Exec.iteCold_iff`, `WP.iteCold_iff`,
`RelCT.iteCold`). Only its layout differs (`Printer.lower`).
-/

@[expose] public section

namespace VG

variable {M : ISA}

theorem Exec.emptyMark_iff {t : Prog M} {s s' : M.State} {tr : List Leak} :
    Exec M (.seq (.seq (.block []) (.block [])) t) s tr s' ↔ Exec M t s tr s' := by
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ =>
      cases h₁ with
      | seq a b =>
        rw [Exec.block_iff] at a b
        simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at a b
        obtain ⟨rfl, rfl⟩ := a
        obtain ⟨rfl, rfl⟩ := b
        exact h₂
  · intro h
    rw [show tr = ([] ++ []) ++ tr from rfl]
    exact .seq (.seq (.block rfl) (.block rfl)) h

theorem Exec.iteCold_iff {c : M.Cond} {t e : Prog M} {s s' : M.State} {tr : List Leak} :
    Exec M (Code.iteCold c t e) s tr s' ↔ Exec M (.ite c t e) s tr s' := by
  constructor
  · intro h
    cases h with
    | iteT hc h => exact .iteT hc (Exec.emptyMark_iff.mp h)
    | iteF hc h => exact .iteF hc h
  · intro h
    cases h with
    | iteT hc h => exact .iteT hc (Exec.emptyMark_iff.mpr h)
    | iteF hc h => exact .iteF hc h

theorem WP.iteCold_iff {c : M.Cond} {t e : Prog M} {s : M.State} {Q : M.State → Prop} :
    WP M (Code.iteCold c t e) s Q ↔ WP M (.ite c t e) s Q :=
  ⟨fun ⟨tr, s', h, q⟩ => ⟨tr, s', Exec.iteCold_iff.mp h, q⟩,
    fun ⟨tr, s', h, q⟩ => ⟨tr, s', Exec.iteCold_iff.mpr h, q⟩⟩

theorem RelCT.iteCold {P Q : M.State → M.State → Prop} {c : M.Cond} {t e : Prog M}
    (h : RelCT M P (.ite c t e) Q) : RelCT M P (Code.iteCold c t e) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (Exec.iteCold_iff.mp e₁) (Exec.iteCold_iff.mp e₂)

end VG
