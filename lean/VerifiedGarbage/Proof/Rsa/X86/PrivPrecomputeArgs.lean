module

public import VerifiedGarbage.Proof.Rsa.X86.PrivArguments
public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputeLength
public import VerifiedGarbage.Proof.Rsa.X86.PrivSaveStatus

/-! # Retaining the CRT status and preparing the public-key precomputation call -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def pcArgument (g : PrivGeometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.precomputation
  | 1 => BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)
  | 2 => g.sources 0
  | 3 => BitVec.ofNat 32 g.length
  | 4 => g.workspace
  | _ => BitVec.ofNat 32 g.scratchLength

theorem precomputeSetup_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) :
    WP isa (.block (localArgument precomputeOffset 0 ++ precomputeLength 1 ++
      copyArgument 2 2 ++ copyArgument 3 3 ++ copyArgument 18 4 ++ copyArgument 19 5)) s fun t =>
      PrivContext g bs t ∧ Arguments g (pcArgument g) 6 t ∧
      Frame [⟨byteAddr g.stack, 72⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  simp only [List.append_assoc]
  have A0 : Arguments g (pcArgument g) 0 s := by intro j hj; omega
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A0 (by decide : 0 < 18) (localArgument_ok s h precomputeOffset (by decide : 0 < 18))) ?_
  rintro s1 ⟨h1, A1, F1, K1⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A1 (by decide : 1 < 18) (precomputeLength_ok s1 h1 (by decide : 1 < 18))) ?_
  rintro s2 ⟨h2, A2, F2, K2⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A2 (by decide : 2 < 18) (copyArgument_ok s2 h2 (by decide : 2 < 20) (by decide : 2 < 18))) ?_
  rintro s3 ⟨h3, A3, F3, K3⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A3 (by decide : 3 < 18) (copyArgument_ok s3 h3 (by decide : 3 < 20) (by decide : 3 < 18))) ?_
  rintro s4 ⟨h4, A4, F4, K4⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A4 (by decide : 4 < 18) (copyArgument_ok s4 h4 (by decide : 18 < 20) (by decide : 4 < 18))) ?_
  rintro s5 ⟨h5, A5, F5, K5⟩
  refine WP.mono (prepareArgument_ok A5 (by decide : 5 < 18) (copyArgument_ok s5 h5 (by decide : 19 < 20) (by decide : 5 < 18))) ?_
  rintro s6 ⟨h6, A6, F6, K6⟩
  exact ⟨h6, A6, F1.trans (F2.trans (F3.trans (F4.trans (F5.trans (F6))))), K1.trans (K2.trans (K3.trans (K4.trans (K5.trans (K6)))))⟩

theorem precomputeArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) :
    WP isa (.block precomputeArgs) s fun t => PrivContext g bs t ∧ Arguments g (pcArgument g) 6 t ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 crtStatusOffset) 32 = s.gpr .eax ∧
      Frame [⟨byteAddr g.stack, 88⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold precomputeArgs
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (saveStatus_ok s h (by decide : crtStatusOffset + 4 ≤ 88)) ?_
  rintro u ⟨hu, M, F, K⟩
  have setup := precomputeSetup_ok u hu
  simp only [List.append_assoc] at setup
  refine WP.mono setup ?_
  rintro t ⟨ht, A, F', K'⟩
  refine ⟨ht, A, ?_, (F.sub ?_).trans (F'.sub ?_), (K.mono (by simp)).trans K'⟩
  · rw [status_preserved (by decide : 72 ≤ crtStatusOffset) (by decide : crtStatusOffset + 4 ≤ 88) F',
      M, Mem.readW_writeW_self32]
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : crtStatusOffset + 4 ≤ 88)⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide : 72 ≤ 88)⟩

end VG.Proof.Rsa.X86.PrivChecked
