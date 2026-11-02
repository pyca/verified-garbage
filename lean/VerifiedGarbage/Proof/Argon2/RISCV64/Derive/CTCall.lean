module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTBase
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCall
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.HCall
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.CT
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Correct
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body

/-!
# Argon2 on RISC-V: the calls of G and H′, in two runs

`ccall_rel` and `hcall_rel` relate the calls of G and H′, from their
preconditions in both runs (`ccall_pre`, `hcall_pre`) and their public
arguments, by the callees' constant time (`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- A call of G: `compress(a0, a1, a2, a3)` to `scratch + o`, with the same
blocks in both runs. -/
theorem ccall_rel {o : Nat} (ho' : o + 1024 ≤ 4096) (ho8 : o % 8 = 0) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ →
      (Inv s₀₁ s₁ ∧ s₁.gpr .a3 = gwP s₀₁ ∧ s₁.gpr .a2 = scrP s₀₁ + BitVec.ofNat 64 o ∧
        GArg s₀₁ o (s₁.gpr .a0) ∧ GArg s₀₁ o (s₁.gpr .a1)) ∧
      (Inv s₀₂ s₂ ∧ s₂.gpr .a3 = gwP s₀₂ ∧ s₂.gpr .a2 = scrP s₀₂ + BitVec.ofNat 64 o ∧
        GArg s₀₂ o (s₂.gpr .a0) ∧ GArg s₀₂ o (s₂.gpr .a1)) ∧
      s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1) :
    RelCT isa P Impl.Argon2.RISCV64.Derive.compressCall fun _ _ => True := by
  unfold Impl.Argon2.RISCV64.Derive.compressCall
  refine RelCT.callEx (k := Proof.Argon2.RISCV64.compressLocal) Proof.Argon2.RISCV64.compress_correct
    Proof.Argon2.RISCV64.compress_ct fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, c₁, x₁, y₁⟩, ⟨i₂, d₂, c₂, x₂, y₂⟩, ea, es⟩ := h s₁ s₂ hP
  obtain ⟨p₁, v₁, w₁⟩ := ccall_pre T.hp₁ i₁ d₁ ho' ho8 c₁ x₁ y₁
  obtain ⟨p₂, v₂, w₂⟩ := ccall_pre T.hp₂ i₂ d₂ ho' ho8 c₂ x₂ y₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [Proof.Argon2.RISCV64.compressLocal, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide)]
  exact ⟨ea, es, by rw [c₁, c₂, T.pb.scrP_eq], by rw [d₁, d₂, gwP, gwP, T.pb.scrP_eq],
    by rw [i₁.sp, i₂.sp, T.pb.E_eq]⟩

/-- What a call of H′ needs in one run. -/
def HArgs (s₀ s : State) : Prop :=
  Inv s₀ s ∧ s.gpr .a4 = scrP s₀ ∧
    (∃ R ∈ [memR s₀, inR s₀], ∃ off, s.gpr .a0 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .a1).toNat ≤ R.len) ∧
    (∃ R ∈ [memR s₀, outR s₀], ∃ off, s.gpr .a2 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .a3).toNat ≤ R.len) ∧
    (s.gpr .a1).toNat < 2 ^ 32 ∧ (1 ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat < 2 ^ 32)

/-- A call of H′: `hprime(a0, a1, a2, a3, a4)`, with the same arguments in
both runs. -/
theorem hcall_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → HArgs s₀₁ s₁ ∧ HArgs s₀₂ s₂ ∧
      s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
        s₁.gpr .a3 = s₂.gpr .a3) :
    RelCT isa P Impl.Argon2.RISCV64.Derive.hPrimeCall fun _ _ => True := by
  unfold Impl.Argon2.RISCV64.Derive.hPrimeCall
  refine RelCT.callEx (k := HPrime.localContract) HPrime.code_correct HPrime.code_ct fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, n₁, o₁, l₁, q₁⟩, ⟨i₂, d₂, n₂, o₂, l₂, q₂⟩, e3, e4, e5, e6⟩ := h s₁ s₂ hP
  obtain ⟨p₁, v₁, w₁, -⟩ := hcall_pre T.hp₁ i₁ d₁ n₁ o₁ l₁ q₁
  obtain ⟨p₂, v₂, w₂, -⟩ := hcall_pre T.hp₂ i₂ d₂ n₂ o₂ l₂ q₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [HPrime.localContract, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a4 ∉ linkRegs by decide)]
  exact ⟨e3, e4, e5, e6, by rw [d₁, d₂, T.pb.scrP_eq], by rw [i₁.sp, i₂.sp, T.pb.E_eq]⟩

end Two

end VG.Proof.Argon2.RISCV64.Derive
