module

public import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
public import VerifiedGarbage.Proof.Framework.AArch64.TaintICall

/-! `relRegs` for code with indirect calls of one function, checked with them
erased (`Code.eraseI`, `check_eraseI_sound`), from runs that agree on the
addresses of the functions called (`Code.IcallsP`). -/

@[expose] public section

namespace VG.AArch64.VectorTaint

theorem relRegsI {P : State → State → Prop} {c : Prog isa} (rs : List Reg) {Q : String → Prop}
    (hp : ∀ x y, P x y → (x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) ∧ ∀ n, Q n → x.syms n = y.syms n)
    (hq : Code.IcallsP Q c) {hc : VG.Taint.Hint T}
    (h : (taint.check (ofRegs rs) (Code.eraseI c) hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  intro x y t₁ t₂ x' y' hxy e₁ e₂
  obtain ⟨τ', h'⟩ := Option.isSome_iff_exists.mp h
  have ha : Agree (ofRegs rs) x y :=
    agree_initial ⟨(hp x y hxy).1.1, fun r hr => (hp x y hxy).1.2 r (AArch64.Taint.mem_ofRegs.mp hr)⟩
  exact ⟨(AArch64.Taint.check_eraseI_sound h' ha (hp x y hxy).2 hq e₁ e₂).1, trivial⟩

end VG.AArch64.VectorTaint
