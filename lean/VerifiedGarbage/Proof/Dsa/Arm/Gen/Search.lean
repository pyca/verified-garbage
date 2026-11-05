module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.SLoop
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Pre
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the search

`search_vp`: from the entry's frame words (the cursor at 0, `state[0]` seeds
left, `fStatus` = 0) to the controller's end (`sLoop_vp`).
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
    {V : Nat → BitVec 32} {LS : List Nat} (hL : fSeedLeft ∈ LS) (hLv : V fSeedLeft = BitVec.ofNat 32 G.k0)
    (hT : fStatus ∈ LS) (hTv : V fStatus = 0) (hC : fC ∈ LS) (hCv : V fC = 0) :
    VP (fun σ s => GI G σ V LS s ∧ X σ) g.search
      (fun σ s => St G (cFin G (cOut G (sCount G G.k0 0 0))) X σ s ∧
        cRes G (cOut G (sCount G G.k0 0 0)) = sW G ∧ cOk G (cOut G (sCount G G.k0 0 0))) := by
  unfold Geo.search
  refine VP.seq (G := St G { V := V, LS := LS, cl := [(G.qLen, padTail HO.md G.qLen)] } X) ?_ ?_
  · rw [O.hp, O.hq]; exact pre_vp HO.md HO.hL O.hlq hlb
  refine (sLoop_vp (X := X) O).mono
    (fun σ s ⟨h, x⟩ => ⟨h.mono (fun o ho => ?_) (fun y hy => hy)
      (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp)), x⟩) fun _ _ h => h
  change o ∈ [fStatus, fSeedLeft, fC] at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact ⟨hT, by show V _ = _; rw [hTv]; simp [upd]⟩
  · exact ⟨hL, by show V _ = _; rw [hLv]; simp [upd, fStatus, fSeedLeft]⟩
  · exact ⟨hC, by show V _ = _; rw [hCv]; simp [upd, fStatus, fSeedLeft, fC]⟩

end

end VG.Proof.Dsa.Arm.Gen
