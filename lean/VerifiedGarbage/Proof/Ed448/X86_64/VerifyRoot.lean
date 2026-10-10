import VerifiedGarbage.Proof.X448.X86_64.Pow223
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation

/-!
# Ed448 verification's equation on x86-64: the square root's power

`root fld 12` writes only the temporaries of X448's inversion (slots 14–21)
and the product's words, and the counter `rbx` (an `ISpec`, as X448's
inversion); slot 21 ends as `rootPow` of slot 12. Decoding takes any power
with that effect on the slots that writes no more than `[960, 1648)`
(`RootOk`): `root` (`root_ok`), or its chain by a call of
`vg_gf448_r64_pow223`, inlined (`rootCall_ok`).
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Env ISpec IKeep WKeep FieldOk Scr E Outside clob opMul opSqn sqnI mulI chainEnv
  chain223_spec pow223Keep_ok powClob)
open VG.Impl.X448.X86_64 (pow223Keep)

/-- The slots after `rootTail`. -/
def rootTailEnv (e : Env) : Env := opMul 21 21 20 (opSqn 21 21 223 e)

/-- The slots after `root`. -/
def rootEnv (e : Env) : Env := rootTailEnv (chainEnv 12 e)

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem rootTail_spec (base : Addr) : ISpec base (rootTail fld) rootTailEnv :=
  (sqnI hf base 21 21 (by decide) 223 (by decide) (by decide)).seq (mulI hf base 21 21 20 (by decide))

include hf in
theorem root_spec (base : Addr) : ISpec base (root fld 12) rootEnv :=
  (chain223_spec hf base 12).seq (rootTail_spec hf base)

/-- What decoding needs of the square root's power `rt`: `root`'s effect on the slots,
keeping what `WKeep` says. -/
def RootOk (rt : Prog isa) : Prop :=
  ∀ {s : State} {base : Addr}, Scr s base →
    WP isa rt s fun s' => WKeep base s s' ∧ E s'.mem base = rootEnv (E s.mem base)

include hf in
theorem root_ok : RootOk (root fld 12) := fun hs =>
  WP.mono (root_spec hf _ _ hs) fun _ ⟨k, e⟩ => ⟨k.weak, e⟩

theorem rootCall_inline : (rootCall fld).inline = .seq (pow223Keep [PPK, CNT]).inline (rootTail fld) := rfl

include hf in
/-- The power by a call of `vg_gf448_r64_pow223`, inlined. -/
theorem rootCall_ok : RootOk (rootCall fld).inline := fun {s} {base} hs => by
  rw [rootCall_inline]
  refine WP.seq (WP.mono (pow223Keep_ok [PPK, CNT] (by simp [PPK, CNT]) hs) fun s₁ ⟨g₁, rd₁, wr₁, o₁, e₁⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨(g₁ .rdi (by decide) (by decide) (by decide)).trans hs.rdi, wr₁ ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (rootTail_spec hf base s₁ hs₁) fun s₂ ⟨k₂, e₂⟩ => ⟨⟨fun r hr hb => ?_, k₂.rd.trans rd₁,
    k₂.wr.trans wr₁, o₁.trans k₂.out⟩, by rw [e₂, e₁]; rfl⟩
  rw [k₂.gpr r hr hb, g₁ r (by revert hr; cases r <;> decide) (by revert hr; cases r <;> decide)
    (by revert hr; cases r <;> decide)]

theorem rootEnv_eval (e : Env) : rootEnv e 21 = rootPow (e 12) := by
  simp (config := {decide := true}) only [rootEnv, rootTailEnv, chainEnv, opMul, opSqn, Function.update_apply]
  rfl

theorem rootEnv_keep (e : Env) (i : Proof.X448.X86_64.Index) (hi : i.val < 14) : rootEnv e i = e i := by
  have h1 : i ≠ 14 := fun h => absurd hi (by rw [h]; decide)
  have h2 : i ≠ 15 := fun h => absurd hi (by rw [h]; decide)
  have h3 : i ≠ 16 := fun h => absurd hi (by rw [h]; decide)
  have h4 : i ≠ 17 := fun h => absurd hi (by rw [h]; decide)
  have h5 : i ≠ 18 := fun h => absurd hi (by rw [h]; decide)
  have h6 : i ≠ 19 := fun h => absurd hi (by rw [h]; decide)
  have h7 : i ≠ 20 := fun h => absurd hi (by rw [h]; decide)
  have h8 : i ≠ 21 := fun h => absurd hi (by rw [h]; decide)
  simp only [rootEnv, rootTailEnv, chainEnv, opMul, opSqn, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
    Function.update_of_ne h6, Function.update_of_ne h7, Function.update_of_ne h8]

end VG.Proof.Ed448.X86_64
