module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QBuild
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryHash
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryStack
import VerifiedGarbage.Proof.Dsa.X86.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Hashing a seed builds q while preserving search arguments and all public tapes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem searchQBuild_ok {H : Hash} (K : HashOK H) {P : SearchContextPlan} {T : GenerationTape P.geometry}
    {W : Nat → BitVec 32} {s : State} (R : SearchContext P W s) (seed : TapeMemory T s)
    (len : T.bytes.length = P.geometry.qLen) (source : W 1 = T.pointer)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.geometry.qLen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * P.geometry.qLen) bs).length = P.geometry.qLen) :
    WP isa (qBuild H P.geometry.qLen) s fun t => SearchContext P W t ∧ TapeMemory T t ∧
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off P.geometry.base q) P.geometry.qLen) =
        Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes ∧
      Frame (parameterWrites P.geometry) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have qw := P.geometry.qWidth
  have qr : q + P.geometry.qLen ≤ usedBytes P.geometry.pLen := by unfold q usedBytes domainCheck; omega
  have qs : q < usedBytes P.geometry.pLen := by omega
  have hr : VG.Impl.Dsa.Generation.Layout.hash + 8192 ≤ usedBytes P.geometry.pLen := by
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega
  have hs : VG.Impl.Dsa.Generation.Layout.hash < usedBytes P.geometry.pLen := by omega
  have sr : VG.Impl.Dsa.Generation.Layout.hash + 512 + H.S ≤ usedBytes P.geometry.pLen := by
    have := K.hSB; unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this]
  have ss : VG.Impl.Dsa.Generation.Layout.hash + 512 < usedBytes P.geometry.pLen := by
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega
  have work : VG.Impl.Dsa.Generation.Layout.hash + K.Wb ≤ usedBytes P.geometry.pLen := by
    have := K.hWb; have hw := K.hW; unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this, hw]
  have resources := hashArenaResources K R.arena (len := P.geometry.qLen) (by omega)
    (by rw [← len]; exact T.fit) (by
      apply Covers.one
      have read := seed.read 0 T.bytes.length (by omega)
      simpa only [len, off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using read)
    (by rw [← len]; exact T.part hr) (by rw [← len]; exact (T.below (Nat.le_refl _)).symm)
    (output := q) (by rw [final]; exact qr) (by
      rw [final]; exact P.geometry.parts_disjoint qr hr (.inr (by unfold q VG.Impl.Dsa.Generation.Layout.hash; decide)))
  have parent : W 5 = P.geometry.parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
  have scratch : W 14 = P.geometry.pointer VG.Impl.Dsa.Generation.Layout.hash :=
    (R.fixed 14 (by decide) (by decide)).trans P.hashPointer
  have inputs : HashResources K (W 1) (W 5 + BitVec.ofNat 32 q) (W 14) P.geometry.qLen s := by
    rw [source, parent, scratch]; exact resources
  refine WP.mono (qBuild_ok K P.geometry.qLen R.arena.frame R.representation inputs (by omega) digest final hash hashSize)
    fun t ⟨value, O, Kt⟩ => ?_
  rw [source, parent] at value
  change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem ((P.geometry.pointer q).setWidth 64) P.geometry.qLen) = _ at value
  rw [P.geometry.pointer_addr qs] at value
  have tape : Spec.Sha256.bytesAt s.mem (T.pointer.setWidth 64) P.geometry.qLen = T.bytes := by
    rw [← len]; exact seed.value
  rw [tape] at value
  rw [scratch, parent, final] at O
  have stateAddress : (P.geometry.pointer VG.Impl.Dsa.Generation.Layout.hash + 512#32).setWidth 64 =
      off P.geometry.base (VG.Impl.Dsa.Generation.Layout.hash + 512) := by
    rw [P.geometry.pointer_add, P.geometry.pointer_addr ss]
  have qAddress : (P.geometry.parent + BitVec.ofNat 32 q).setWidth 64 = off P.geometry.base q := P.geometry.pointer_addr qs
  rw [stateAddress, qAddress, P.geometry.pointer_addr hs] at O
  have stack : stk s = below P.geometry.frame 48 := by unfold stk; rw [R.arena.frameReg]
  rw [stack] at O
  have apart : ∀ r ∈ [P.geometry.part (VG.Impl.Dsa.Generation.Layout.hash + 512) H.S,
      P.geometry.part q P.geometry.qLen, P.geometry.part VG.Impl.Dsa.Generation.Layout.hash K.Wb, below P.geometry.frame 48],
      (⟨P.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint r := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact P.geometry.frame_part sr
    · exact P.geometry.frame_part qr
    · exact P.geometry.frame_part work
    · exact P.geometry.frame_below (by decide)
  have F : Frame (parameterWrites P.geometry) s.mem t.mem := O.sub (by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, P.geometry.mutablePart (by decide) sr⟩
    · exact ⟨_, List.mem_cons_self, P.geometry.mutablePart (by decide) qr⟩
    · exact ⟨_, List.mem_cons_self, P.geometry.mutablePart (Nat.le_refl _) work⟩
    · exact ⟨below P.geometry.frame 128, by simp [parameterWrites], below_sub (by decide) P.geometry.stackSize⟩)
  exact ⟨R.frame (R.representation.keep O apart) (fun _ _ _ => rfl) F Kt (by decide),
    seed.keep F T.parameterApart Kt, value, F, Kt⟩
end VG.Proof.Dsa.X86.Generation
