module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.CTBase
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCall
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.HCall
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.CT
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Correct
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Body

/-!
# Argon2 on PPC64LE: the calls of G and H′, in two runs

`ccall_rel` and `hcall_rel` relate the calls of G and H′, from their
preconditions in both runs (`ccall_pre`, `hcall_pre`) and their public
arguments, by the callees' constant time (`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- A call of G: `compress(r3, r4, r5, r6)` to `scratch + o`, with the same
blocks in both runs. -/
theorem ccall_rel {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ →
      (Inv s₀₁ s₁ ∧ s₁.gpr .r6 = scrP s₀₁ ∧ s₁.gpr .r5 = scrP s₀₁ + BitVec.ofNat 64 o ∧
        GArg s₀₁ o (s₁.gpr .r3) ∧ GArg s₀₁ o (s₁.gpr .r4)) ∧
      (Inv s₀₂ s₂ ∧ s₂.gpr .r6 = scrP s₀₂ ∧ s₂.gpr .r5 = scrP s₀₂ + BitVec.ofNat 64 o ∧
        GArg s₀₂ o (s₂.gpr .r3) ∧ GArg s₀₂ o (s₂.gpr .r4)) ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4) :
    RelCT isa P Impl.Argon2.PPC64LE.Derive.compressCall fun _ _ => True := by
  unfold Impl.Argon2.PPC64LE.Derive.compressCall
  refine RelCT.callEx (k := Proof.Argon2.PPC64LE.compressLocal) Proof.Argon2.PPC64LE.compress_correct
    Proof.Argon2.PPC64LE.compress_ct fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, c₁, x₁, y₁⟩, ⟨i₂, d₂, c₂, x₂, y₂⟩, ea, es⟩ := h s₁ s₂ hP
  obtain ⟨p₁, v₁, w₁⟩ := ccall_pre T.hp₁ i₁ d₁ ho ho' c₁ x₁ y₁
  obtain ⟨p₂, v₂, w₂⟩ := ccall_pre T.hp₂ i₂ d₂ ho ho' c₂ x₂ y₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [Proof.Argon2.PPC64LE.compressLocal, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide)]
  exact ⟨ea, es, by rw [c₁, c₂, T.pb.scrP_eq], by rw [d₁, d₂, T.pb.scrP_eq],
    by rw [i₁.sp, i₂.sp, T.pb.E_eq]⟩

/-- What a call of H′ needs in one run. -/
def HArgs (s₀ s : State) : Prop :=
  Inv s₀ s ∧ s.gpr .r7 = scrP s₀ ∧
    (∃ R ∈ [memR s₀, inR s₀], ∃ off, s.gpr .r3 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r4).toNat ≤ R.len) ∧
    (∃ R ∈ [memR s₀, outR s₀], ∃ off, s.gpr .r5 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r6).toNat ≤ R.len) ∧
    (s.gpr .r4).toNat < 2 ^ 32 ∧ (1 ≤ (s.gpr .r6).toNat ∧ (s.gpr .r6).toNat < 2 ^ 32)

/-- A call of H′: `hprime(r3, r4, r5, r6, r7)`, with the same arguments in
both runs. -/
theorem hcall_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → HArgs s₀₁ s₁ ∧ HArgs s₀₂ s₂ ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
        s₁.gpr .r6 = s₂.gpr .r6) :
    RelCT isa P Impl.Argon2.PPC64LE.Derive.hPrimeCall fun _ _ => True := by
  unfold Impl.Argon2.PPC64LE.Derive.hPrimeCall
  refine RelCT.callEx (k := HPrime.localContract) HPrime.code_correct HPrime.code_ct fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, n₁, o₁, l₁, q₁⟩, ⟨i₂, d₂, n₂, o₂, l₂, q₂⟩, e3, e4, e5, e6⟩ := h s₁ s₂ hP
  obtain ⟨p₁, v₁, w₁, -⟩ := hcall_pre T.hp₁ i₁ d₁ n₁ o₁ l₁ q₁
  obtain ⟨p₂, v₂, w₂, -⟩ := hcall_pre T.hp₂ i₂ d₂ n₂ o₂ l₂ q₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [HPrime.localContract, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r7 ∉ linkRegs by decide)]
  exact ⟨e3, e4, e5, e6, by rw [d₁, d₂, T.pb.scrP_eq], by rw [i₁.sp, i₂.sp, T.pb.E_eq]⟩

end Two

end VG.Proof.Argon2.PPC64LE.Derive
