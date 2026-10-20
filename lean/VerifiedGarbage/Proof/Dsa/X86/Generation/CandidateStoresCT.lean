module
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateStore
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorOutputCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.StorePublicCT

/-! # Persist p and its quotient with public frame and output addresses -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

def CandidateStoresAt (len : Nat) (G : GenerationGeometry) (s : State) : Prop :=
  G.pLen = len ∧ ArenaReady G s ∧ s.mem.readW (off G.frameBase 20) 32 = G.parent ∧
    s.gpr .edi = G.pointer arithmetic

def candidateStorePublic (G : GenerationGeometry) : GeneratorOutputPublic :=
  ⟨⟨G.frameBase, fun _ => G.parent⟩, G.pointer arithmetic, 0⟩

theorem candidateStoresAt_store {len : Nat} {G : GenerationGeometry} {s : State}
    (R : CandidateStoresAt len G s) : GeneratorStoreAt (candidateStorePublic G) s := by
  refine ⟨⟨R.2.1.frame, ?_⟩, R.2.2.2⟩
  intro i hi
  obtain rfl := List.mem_singleton.mp hi
  exact R.2.2.1

theorem candidateStoreP_ct (len : Nat) : RelCT isa (Two (CandidateStoresAt len))
    (.seq (.block (bufferPointer .esi p)) (storePublic len candidateP)) (Two (CandidateStoresAt len)) := by
  refine two_post (two_map candidateStorePublic (fun _ _ h => candidateStoresAt_store h)
    (bufferPointerStore_ct len candidateP p)) ?_
  rintro G s ⟨width, R, saved, di⟩
  have pw := G.width
  have pr : p + G.pLen ≤ usedBytes G.pLen := by unfold p usedBytes domainCheck; omega
  have ar : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  have ps : p < usedBytes G.pLen := by omega
  have room : candidateP + 8 * (G.pLen / 8) ≤ arithmeticBytes := by unfold candidateP arithmeticBytes; omega
  have apart := G.parts_disjoint pr ar (Or.inl (by unfold p arithmetic; omega))
  rw [← width]
  refine WP.seq (WP.mono (bufferPointer_ok R.frame saved .esi p) fun a ⟨si, mem, Ka⟩ => ?_)
  change a.gpr .esi = G.pointer p at si
  have Ra := R.keep Ka (by decide)
  have dia : a.gpr .edi = G.pointer arithmetic := (Ka.1 _ (by decide)).trans di
  have len : G.pLen ≤ 8 * (G.pLen / 8) := by rcases pw with h | h | h <;> rw [h] <;> decide
  have words : G.pLen % 4 = 0 := by rcases pw with h | h | h <;> rw [h] <;> decide
  refine WP.mono (storePublic_ok (Ra.arithmeticScr dia) room (by omega) len words
    (by rw [si]; exact G.pointer_fit ps pr)
    (by intro d k hk; rw [si]; exact Ra.writePointer ps pr d k hk)
    (by rw [si, G.pointer_addr ps]; exact apart.symm.sub_left (Offset.sub_base _ room)))
    fun t ⟨_, O, K⟩ => ?_
  have frame := copyOutside_frame O
  rw [si, G.pointer_addr ps] at frame
  have parent : t.mem.readW (off G.frameBase 20) 32 = G.parent := by
    rw [frame.readW (r := ⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩)
      (Offset.contains_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide) (by decide))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact G.frame_part pr) (by decide), mem, saved]
  exact ⟨rfl, Ra.keep K (by decide), parent, (K.1 _ (by decide)).trans dia⟩

theorem candidateStores_ct (len : Nat) : RelCT isa (Two (CandidateStoresAt len))
    (candidateStores len) (fun _ _ => True) := by
  apply RelCT.assoc
  exact RelCT.seq (candidateStoreP_ct len)
    (two_map candidateStorePublic (fun _ _ h => candidateStoresAt_store h)
      (bufferPointerStore_ct len candidateQuotient exponent))
end VG.Proof.Dsa.X86.Generation
