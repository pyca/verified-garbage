module
public import VerifiedGarbage.Proof.Rsa.X86.PrivContext

import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-! # Retaining a call result above the outgoing argument area -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem saveStatus_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) {d : Nat} (hd : d + 4 ≤ 88) :
    WP isa (.block [.store (stackAt d) .eax]) s fun t => PrivContext g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 d) (s.gpr .eax) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩] s.mem t.mem ∧ Keeps [] s t := by
  unfold stackAt
  refine wp_stm (B := s.gpr .esp) rfl
    (by rw [h.address (d := d) (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)]
        exact h.inner.write (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega))
    fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 d) (s.gpr .eax) := by
    rw [T.mem, h.address (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)]
  have K := T.keeps []
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), M, F, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)⟩

theorem status_preserved {g : PrivGeometry} {m m' : Mem} {d : Nat} (hd : 72 ≤ d) (hf : d + 4 ≤ 88)
    (F : Frame [⟨byteAddr g.stack, 72⟩] m m') :
    m'.readW (byteAddr g.stack + BitVec.ofNat 64 d) 32 =
      m.readW (byteAddr g.stack + BitVec.ofNat 64 d) 32 := by
  apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint_base _ hd (by omega)

end VG.Proof.Rsa.X86.PrivChecked
