import VerifiedGarbage.Proof.X448.X86_64.Pow223
import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-!
# X448 on x86-64: the inversion by a call

`invertCall`, inlined (`Code.inline`, which `CallInline.lean` relates to the
call): `Z2` copied to slot 12, `vg_gf448_r64_pow223`'s code, then `invTail`.
It keeps the registers but `clob` and `rbx` and the memory outside
`[832, 1648)` (slot 12 and the function's bytes), and slot 21 ends as
`invert` of slot 2, as the inline inversion's does (`invert_ok`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

theorem invert_c (z : Spec.X448.Fe) : VG.Proof.X448.invert z = sqn (c223 z) 225 * (sqn (c222 z) 2 * z) := rfl

theorem invertCall_inline (fld : Field) (keep : List Nat) :
    (invertCall fld keep).inline =
      .seq (.block (copyOut (slot 12) Z2)) (.seq (pow223Keep keep).inline (invTail fld)) := rfl

variable {fld : Field} (hf : FieldOk fld)

/-- What both inversions keep and compute. -/
def InvPost (base : Addr) (s s' : State) : Prop :=
  (∀ r, r ∉ clob → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    Outside base 832 816 s.mem s'.mem ∧ E s'.mem base 21 = VG.Proof.X448.invert (E s.mem base 2)

include hf in
theorem invert_post {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (Impl.X448.X86_64.invert fld) s (InvPost base s) :=
  WP.mono (invert_ok hf hs) fun _ ⟨g, rd, wr, o, e⟩ => ⟨g, rd, wr, o.mono (by decide) (by decide), e⟩

include hf in
theorem invertCall_post {keep : List Nat} (hk : ∀ d ∈ keep, d + 8 ≤ 832 ∨ (1648 ≤ d ∧ d + 8 ≤ 8192))
    {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (invertCall fld keep).inline s (InvPost base s) := by
  rw [invertCall_inline]
  refine WP.seq (WP.mono (copyOut_ok hs (o := slot 12) (a := Z2) (by decide) (by decide))
    fun s₁ ⟨v₁, o₁, g₁, rd₁, wr₁⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by decide)).trans hs.rdi, wr₁ ▸ hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (pow223Keep_ok keep (fun d hd => by rcases hk d hd with h | h <;> omega) hs₁)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, e₂⟩ => ?_)
  have hs₂ : Scr s₂ base :=
    ⟨(g₂ .rdi (by decide) (by decide) (by decide)).trans hs₁.rdi, wr₂ ▸ hs₁.wr, hs₁.nowrap⟩
  refine WP.mono (invTail_spec hf base s₂ hs₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  have z₁ : E s₁.mem base 12 = E s.mem base 2 := congrArg toFe v₁
  have z₂ : E s₂.mem base 2 = E s.mem base 2 :=
    (E_outside o₂ 2 (by decide)).trans (E_outside o₁ 2 (by decide))
  refine ⟨fun r hr hb => ?_, k₃.rd.trans (rd₂.trans rd₁), k₃.wr.trans (wr₂.trans wr₁), ?_, ?_⟩
  · rw [k₃.gpr r hr hb, g₂ r (by revert hr; cases r <;> decide) (by revert hr; cases r <;> decide)
      (by revert hr; cases r <;> decide), g₁ r (by revert hr; cases r <;> decide)]
  · intro x hx
    rw [k₃.out x (by omega), o₂ x (by omega), o₁ x (by simp only [slot]; omega)]
  · rw [e₃, invert_c]
    simp only [↓reduceIte, tailEnv, opMul, opSqn, Function.update_apply]
    rw [z₂, e₂, chainEnv_21, chainEnv_20, z₁]
    rfl

end VG.Proof.X448.X86_64
