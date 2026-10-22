module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.SLoop
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Pre
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the search

`search_vp`: from the entry's frame words (the first seed, all seeds left,
nothing read, `fStatus` = 0) to the domain the spec's search finds.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {X : State → Prop}

theorem search_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n)
    (hlb : HO.md.lenBytes G.qLen =
      [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * G.qLen / 256), BitVec.ofNat 8 (8 * G.qLen % 256)])
    {V : Nat → BitVec 32} {LS : List Nat} (hS : fSeed ∈ LS) (hSv : V fSeed = G.seeds)
    (hL : fSeedLeft ∈ LS) (hLv : V fSeedLeft = BitVec.ofNat 32 G.seedsLen) (hT : fStatus ∈ LS)
    (hTv : V fStatus = 0) (hU : fUsed ∈ LS) (hUv : V fUsed = 0) :
    VP (fun σ s => GI G σ V LS s ∧ X σ) g.search
      (St G (sFin G (Spec.Dsa.generateParameters.attempt (8 * G.pLen) (hsL G) (8 * G.qLen)
        (Spec.Dsa.generationChunks G.qLen G.seedsB) G.witB)) X) := by
  unfold Geo.search
  refine VP.seq (G := St G { V := V, LS := LS, cl := [(G.qLen, padTail HO.md G.qLen)] } X) ?_ ?_
  · rw [O.hp, O.hq]; exact pre_vp HO.md HO.hL O.hlq hlb
  have := sLoop_vp (X := X) O (u0 := 0) (Nat.zero_le _)
  rw [List.drop_zero] at this
  refine this.mono (fun σ s ⟨h, x⟩ => ⟨h.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
    (fun _ h' => absurd h' (by simp)), x⟩) fun _ _ h => h
  change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: [] at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact ⟨hU, by simp [upd, hUv]⟩
  · exact ⟨hT, by show V _ = _; rw [hTv]; simp [upd, fStatus, fUsed]⟩
  · exact ⟨hL, by show V _ = _; rw [hLv]; simp [upd, fStatus, fUsed, fSeedLeft]⟩
  · exact ⟨hS, by show V _ = _; rw [hSv]; simp [upd, fStatus, fUsed, fSeedLeft, fSeed]⟩

end

end VG.Proof.Dsa.Arm.Gen
