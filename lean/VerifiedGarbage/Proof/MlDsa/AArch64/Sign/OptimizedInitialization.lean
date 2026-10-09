import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedInitialization
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecode

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Spec.Sha3 (bytesAt)

/-- The optimized signer has decoded secret transforms and derived the
same mask seed as the canonical implementation. -/
structure PositiveIK (p : Params) (S : Nat) (σ s : State) : Prop where
  d : PositiveID p S σ p.ℓ p.k p.k s
  rpp : bytesAt s.mem (pa s (sc oMS)) 64=rppOf p σ

theorem seedWrites_ok {p : Params} (hp : Ok3 p) :
    ∀ w∈[(sc 0,200),(sc 200,640),(sc oMS,64)],inB (sgW p) w.1 w.2=true := by
  rcases hp with rfl | rfl | rfl <;> decide

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem positiveSeed_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} (hs : PositiveID p S σ p.ℓ p.k p.k s) :
    WP isa (shakeAtWith keccak.callee [⟨.x25,32,32⟩,⟨.x27,0,32⟩,⟨.x26,0,64⟩]
      ⟨.x28,oMS,64⟩) s (PositiveIK p S σ) := by
  obtain ⟨_,_,_,hc,hkeep,_,_,hsk⟩ := dChk_spec (dChk_ok hp)
  refine WP.mono_syms (shake_ok hP.s16 hP.s64 hs.im.st.lay (by simp) hc)
    fun t ⟨hpt,_,hb⟩ hy => ⟨hs.step hpt hy hkeep (seedWrites_ok hp),?_⟩
  rw [hpt.pa (by decide),hb]
  simp only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]
  show H (bytesAt s.mem (pa s (.x25,32)) 32 ++ (bytesAt s.mem (pa s (.x27,0)) 32 ++
    bytesAt s.mem (pa s (.x26,0)) 64)) 64 = _
  rw [sk_slice hs.im.st (o := 32) (len := 32) (by omega),hs.im.st.rnd,hs.im.st.mu,← List.append_assoc]

theorem positiveInitialization_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} (hs : IM p S σ s) (ht : StaticRoots S s) :
    WP isa (positiveDecodeWith keccak.callee P p) s (PositiveIK p S σ) := by
  unfold positiveDecodeWith
  refine WP.seq (WP.mono (positiveDecodeSecrets_ok hP (dChk_ok hp)
    (s := s) ⟨hs,ht,by simp [PosFam],by simp [PosFam],by simp [PosFam]⟩)
    fun t hd => positiveSeed_ok hP hp hd)

end VG.Proof.MlDsa.AArch64.Sign
