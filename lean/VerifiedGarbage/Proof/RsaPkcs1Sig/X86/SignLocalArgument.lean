module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContext

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackWord
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! # Passing a pointer into the wrapper's local frame as a cdecl argument -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.X86.Wp VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem localArgument_ok (s : State) {g : Geometry} {bs : Fin 8 → List Byte}
    (h : Context g bs s) (d : Nat) {j : Nat} (hj : j < 20) :
    WP isa (.block (localArgument d j)) s fun t =>
      Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (g.stack + BitVec.ofNat 32 d) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold localArgument stackAt
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  refine wp_stm (B := s.gpr .esp)
    (by rw [B.other .esp (by decide), A.other .esp (by decide)])
    (by rw [B.wr, A.wr, h.address (by omega)]; exact h.inner.write (by simp only [VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes]; omega))
    fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (g.stack + BitVec.ofNat 32 d) := by
    rw [T.mem, B.gpr, A.gpr, B.mem, A.mem, h.address (by omega), h.sp]
  have K : Keeps [.eax] s t := A.keeps.trans (B.keeps.trans (T.keeps _))
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), M, F, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes]; omega)⟩

theorem outgoing_word_preserved {g : Geometry} {m m' : Mem} {i j : Nat}
    (hi : i < 20) (hj : j < 20) (hne : i ≠ j)
    (f : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] m m') :
    m'.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * i)) 32 =
      m.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * i)) 32 := by
  apply f.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 (4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

end VG.Proof.RsaPkcs1Sig.X86.Sgn
