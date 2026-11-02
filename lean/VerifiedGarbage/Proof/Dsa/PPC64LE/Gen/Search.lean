module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.SLoop
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Pre
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Hash
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test

/-! # DSA parameter generation on PPC64LE: the search

`search_vp`: from the entry's header words (the first seed, all seeds left,
nothing read, `fStatus` = 0) to the domain the spec's search finds.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {X : State → Prop}

theorem search_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (O : GenOk G g HO Lq Lp)
    (hlb : HO.md.lenBytes G.qLen =
      [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * G.qLen / 256), BitVec.ofNat 8 (8 * G.qLen % 256)])
    {V : Nat → BitVec 64} {LS : List Nat} (hS : fSeed ∈ LS) (hSv : V fSeed = G.seeds)
    (hL : fSeedLeft ∈ LS) (hLv : V fSeedLeft = BitVec.ofNat 64 G.seedsLen) (hT : fStatus ∈ LS)
    (hTv : V fStatus = 0) (hU : fUsed ∈ LS) (hUv : V fUsed = 0) :
    VP (fun σ s => GI G 176 σ V LS s ∧ X σ) g.search
      (St G (sFin G (Spec.Dsa.generateParameters.attempt (8 * G.pLen) (hsL G) (8 * G.qLen)
        (Spec.Dsa.generationChunks G.qLen G.seedsB) G.witB)) X) := by
  unfold Geo.search
  refine VP.seq (G := St G { V := V, LS := LS, cl := [(sMsg + G.qLen, padTail HO.md G.qLen)] } X) ?_ ?_
  · rw [O.hq]; exact pre_vp HO.md HO.hL O.hlq hlb
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

end VG.Proof.Dsa.PPC64LE.Gen
