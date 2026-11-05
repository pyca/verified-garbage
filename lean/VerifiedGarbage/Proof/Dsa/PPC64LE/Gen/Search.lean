module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.SLoop
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Pre
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Hash
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test

/-! # DSA parameter generation on PPC64LE: the search

`search_vp`: from the entry's header words (the cursor at 0, `state[0]` seeds
left, `fStatus` = 0) to the controller's end (`sLoop_vp`).
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
    {V : Nat → BitVec 64} {LS : List Nat} (hL : fSeedLeft ∈ LS) (hLv : V fSeedLeft = BitVec.ofNat 64 G.k0)
    (hT : fStatus ∈ LS) (hTv : V fStatus = 0) (hC : fC ∈ LS) (hCv : V fC = 0) :
    VP (fun σ s => GI G 176 σ V LS s ∧ X σ) g.search
      (fun σ s => St G (cFin G (cOut G (sCount G G.k0 0 0))) X σ s ∧
        cRes G (cOut G (sCount G G.k0 0 0)) = sW G ∧ cOk G (cOut G (sCount G G.k0 0 0))) := by
  unfold Geo.search
  refine VP.seq (G := St G { V := V, LS := LS, cl := [(sMsg + G.qLen, padTail HO.md G.qLen)] } X) ?_ ?_
  · rw [O.hq]; exact pre_vp HO.md HO.hL O.hlq hlb
  rw [show ∀ c : Prog isa, VG.Impl.Rsa.PPC64LE.Keys.seqs [c] = c from fun _ => rfl]
  refine (sLoop_vp (X := X) O).mono (F' := St G { V := V, LS := LS, cl := [(sMsg + G.qLen, padTail HO.md G.qLen)] } X)
    (fun σ s ⟨h, x⟩ => ⟨h.mono (fun o ho => ?_) (fun y hy => hy)
    (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp)), x⟩) fun _ _ h => h
  change o ∈ [fStatus, fSeedLeft, fC] at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact ⟨hT, by show V _ = _; rw [hTv]; simp [upd]⟩
  · exact ⟨hL, by show V _ = _; rw [hLv]; simp [upd, fStatus, fSeedLeft]⟩
  · exact ⟨hC, by show V _ = _; rw [hCv]; simp [upd, fStatus, fSeedLeft, fC]⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
