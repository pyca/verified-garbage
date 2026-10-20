module
public import VerifiedGarbage.Proof.Rsa.X86.PrivArguments

import VerifiedGarbage.Proof.Rsa.X86.PrivSaveStatus
import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputeLength
import VerifiedGarbage.Proof.Rsa.X86.PrivLocalArgument
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-! # Preparing public re-exponentiation while retaining both prior call results -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def pdArgument (g : PrivGeometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.output | 1 => BitVec.ofNat 32 g.length
  | 2 => g.precomputation | 3 => BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.temporary | 7 => BitVec.ofNat 32 g.length
  | 8 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

theorem publicSetup_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) :
    WP isa (.block (copyArgument 0 0 ++ copyArgument 1 1 ++ localArgument precomputeOffset 2 ++ precomputeLength 3 ++
      copyArgument 4 4 ++ copyArgument 5 5 ++ localArgument candidateOffset 6 ++ copyArgument 7 7 ++
      copyArgument 18 8 ++ copyArgument 19 9)) s fun t =>
      PrivContext g bs t ∧ Arguments g (pdArgument g) 10 t ∧
      Frame [⟨byteAddr g.stack, 72⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  simp only [List.append_assoc]
  have A0 : Arguments g (pdArgument g) 0 s := by intro j hj; omega
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A0 (by decide : 0 < 18) (copyArgument_ok s h (by decide : 0 < 20) (by decide : 0 < 18))) ?_
  rintro s1 ⟨h1, A1, F1, K1⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A1 (by decide : 1 < 18) (copyArgument_ok s1 h1 (by decide : 1 < 20) (by decide : 1 < 18))) ?_
  rintro s2 ⟨h2, A2, F2, K2⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A2 (by decide : 2 < 18) (localArgument_ok s2 h2 precomputeOffset (by decide : 2 < 18))) ?_
  rintro s3 ⟨h3, A3, F3, K3⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A3 (by decide : 3 < 18) (precomputeLength_ok s3 h3 (by decide : 3 < 18))) ?_
  rintro s4 ⟨h4, A4, F4, K4⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A4 (by decide : 4 < 18) (copyArgument_ok s4 h4 (by decide : 4 < 20) (by decide : 4 < 18))) ?_
  rintro s5 ⟨h5, A5, F5, K5⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A5 (by decide : 5 < 18) (copyArgument_ok s5 h5 (by decide : 5 < 20) (by decide : 5 < 18))) ?_
  rintro s6 ⟨h6, A6, F6, K6⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A6 (by decide : 6 < 18) (localArgument_ok s6 h6 candidateOffset (by decide : 6 < 18))) ?_
  rintro s7 ⟨h7, A7, F7, K7⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A7 (by decide : 7 < 18) (copyArgument_ok s7 h7 (by decide : 7 < 20) (by decide : 7 < 18))) ?_
  rintro s8 ⟨h8, A8, F8, K8⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A8 (by decide : 8 < 18) (copyArgument_ok s8 h8 (by decide : 18 < 20) (by decide : 8 < 18))) ?_
  rintro s9 ⟨h9, A9, F9, K9⟩
  refine WP.mono (prepareArgument_ok A9 (by decide : 9 < 18) (copyArgument_ok s9 h9 (by decide : 19 < 20) (by decide : 9 < 18))) ?_
  rintro s10 ⟨h10, A10, F10, K10⟩
  exact ⟨h10, A10, F1.trans (F2.trans (F3.trans (F4.trans (F5.trans (F6.trans (F7.trans (F8.trans (F9.trans (F10))))))))), K1.trans (K2.trans (K3.trans (K4.trans (K5.trans (K6.trans (K7.trans (K8.trans (K9.trans (K10)))))))))⟩

theorem publicArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) :
    WP isa (.block publicArgs) s fun t => PrivContext g bs t ∧ Arguments g (pdArgument g) 10 t ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 precomputeStatusOffset) 32 = s.gpr .eax ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 crtStatusOffset) 32 =
        s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 crtStatusOffset) 32 ∧
      Frame [⟨byteAddr g.stack, 88⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold publicArgs
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (saveStatus_ok s h (by decide : precomputeStatusOffset + 4 ≤ 88)) ?_
  rintro u ⟨hu, M, F, K⟩
  have setup := publicSetup_ok u hu
  simp only [List.append_assoc] at setup
  refine WP.mono setup ?_
  rintro t ⟨ht, A, F', K'⟩
  refine ⟨ht, A, ?_, ?_, (F.sub ?_).trans (F'.sub ?_), (K.mono (by simp)).trans K'⟩
  · rw [status_preserved (by decide : 72 ≤ precomputeStatusOffset)
      (by decide : precomputeStatusOffset + 4 ≤ 88) F', M, Mem.readW_writeW_self32]
  · rw [status_preserved (by decide : 72 ≤ crtStatusOffset) (by decide : crtStatusOffset + 4 ≤ 88) F']
    apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 crtStatusOffset, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint _ (Or.inl (by decide : crtStatusOffset + 4 ≤ precomputeStatusOffset)) (by decide) (by decide)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : precomputeStatusOffset + 4 ≤ 88)⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide : 72 ≤ 88)⟩

end VG.Proof.Rsa.X86.PrivChecked
