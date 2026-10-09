import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Final
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedTimingBase

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs HintIs Bounds minBounds rejNTTPoly sampleInBall
  simpleBitPack verifyMu normRq normR)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlDsa.Verify (w1Row aSeed)

/-- Final digest while preserving the optimized representation invariant. -/
abbrev SCH (p : Params) (S : Nat) (σ s : State) : Prop :=
  ∃ h A' c0 q, SC p S σ h A' c0 q p.ℓ true p.k s ∧
    bytesAt s.mem (pa s (sc oCT)) p.ctildeLen=Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen

theorem rows_bytes {S : Nat} {p : Params} {σ : State} {h : List (Vector Bool Spec.MlDsa.n)} {A' : Nat → Nat → Poly} {c0 : Poly}
    {q : Bool} {s : State} (hs : SC p S σ h A' c0 q p.ℓ true p.k s) :
    Proof.MlKem.AArch64.pbytes s ⟨.x28, oP (p.k * p.ℓ + 0), p.k * w1Len p⟩ = w1Enc p σ h A' c0 := by
  show bytesAt s.mem (s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + 0))) (p.k * w1Len p) = _
  rw [show p.k * w1Len p = w1Len p * p.k from Nat.mul_comm _ _, Proof.MlDsa.KeyGen.bytesAt_pieces]
  exact flatMap_congr' fun r hr => hs.rows r (List.mem_range.mp hr)

theorem hash_vpiece {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) {p : Params} (hF : VFacts p) :
    VPiece p S (SCx p S p.ℓ true p.k) (SCH p S) ((shake256With keccak.callee) (hIns p) [⟨.x28, oCT, p.ctildeLen⟩]) := by
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, vrel_of (Q := VTwo p S) (hash_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => vc_two hF p₁ p₂ pub h₁.vc h₂.vc⟩
  have L := hs.vc.lay hF hp
  refine WP.mono_syms (shake_ok h16 hSl L (by simp) (hash_chk hF)) fun s' ⟨hP', x', ho⟩ hy => ⟨h, A', c0, q, ?_, ?_⟩
  · exact hs.keep hF hp hP' (by scchks hF (Nat.le_refl _)) hy (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl
      all_goals have := hF.ct.2;have := hF.scr;have := hF.k;have := hF.l;have := hF.kl
      all_goals vlay) x'
  · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at ho
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide), ho, rows_bytes hs]
    refine congrArg (Spec.MlDsa.H · p.ctildeLen) (congrArg (· ++ _) ?_)
    show bytesAt s.mem (s.gpr .x26 + BitVec.ofNat 64 0) 64 = _
    exact hs.vc.mu

/-! ## The comparison -/

theorem cmp_vpiece {S : Nat} {p : Params} (hF : VFacts p) :
    VPiece p S (SCH p S) (VFin p) (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen) := by
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hH⟩ => ?_, vrel_of (Q := VTwo p S) (cmp_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => vc_two hF p₁ p₂ pub h₁.vc h₂.vc⟩
  have L := hs.vc.lay hF hp
  have := hF.ct.2; have := hF.sig; have := hF.scr; have := hF.k; have := hF.l; have := hF.kl
  refine WP.mono (cmpAnd_ok L (by omega) (by omega) (by vlayd) (by vlayd)) fun s' ⟨hP', x'⟩ => ⟨?_, ?_⟩
  · exact hs.vc.step hF hp hP' (by unfold vcChk; vlayd)
  · rw [hH, ctOf_eq hF hs.vc, hs.x24] at x'
    have e : s'.gpr .x24 = flag (q = true ∧ Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen = ctOf p σ) := by
      rw [x', and_flag (P := q = true)
        (Q := Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen = ctOf p σ) _ (by split <;> rfl)]
    obtain ⟨hA1, hA0⟩ := hs.gd
    cases q with
    | false =>
      refine .inr ⟨by rw [e]; exact ifn (fun h => Bool.false_ne_true h.1) _ _, ?_⟩
      rcases hA0 rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
      · show verifyMu p minBounds _ _ _ ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_rej_none minBounds _ _ hs.hh hr hc hn']; nofun
      · show verifyMu p minBounds _ _ _ ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_ball_none minBounds _ _ hs.hh (Option.map_eq_none_iff.mp hn')]; nofun
    | true =>
      obtain ⟨hA, hB⟩ := hA1 rfl
      obtain ⟨nA, hnA⟩ := Proof.MlDsa.Verify.common_bound (P := fun r n => ∀ c < p.ℓ,
          rejNTTPoly n (aSeed (vPk p σ) r c) = some (A' r c))
        (fun _ _ _ hle h c hc => Proof.MlDsa.Verify.rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
          Proof.MlDsa.Verify.common_bound (P := fun c n => rejNTTPoly n (aSeed (vPk p σ) r c) = some (A' r c))
            (fun _ _ _ hle h => Proof.MlDsa.Verify.rejNTTPoly_mono hle h) p.ℓ fun c hc =>
              let ⟨b, hb⟩ := hA r hr c hc; ⟨b.rejNTT, hb⟩
      obtain ⟨bB, hbB⟩ := hB
      obtain ⟨cc, hcc, hcc'⟩ := Option.map_eq_some_iff.mp hbB
      have hl : h.length = p.k := hs.hint.1
      have ev := Proof.MlDsa.Verify.verifyMu_rows p ⟨0, 0, nA, bB.ball⟩ (vPk p σ) (vMu σ) (vSig p σ) hs.hh hl hnA
        hcc
      rw [decide_eq_true ((Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1 _).mpr hs.nok), hcc', Bool.true_and,
        ← hF.g2.2] at ev
      by_cases hE : Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen = ctOf p σ
      · exact .inl ⟨by rw [e]; exact ifp (show true = true ∧ _ from ⟨rfl, hE⟩) _ _, ⟨_, ev.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
      · exact .inr ⟨by rw [e]; exact ifn (fun h : true = true ∧ _ => hE h.2) _ _,
          false_ne (ev.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩


/-- Final hashing and comparison use no transformed z/c representation. -/
theorem finish_vpiece {S : Nat} (h16 : 16≤S) (hS : S<2^64) {p : Params} (hF : VFacts p) :
    VPiece p S (SCx p S p.ℓ true p.k) (VFin p)
      (.seq (shake256With keccak.callee (hIns p) [⟨.x28,oCT,p.ctildeLen⟩])
        (cmpAnd (sc oCT) (.x27,0) p.ctildeLen)) :=
  (hash_vpiece h16 hS hF).seq (cmp_vpiece hF)

/-- The final phase preserves public table addresses even though its semantic
postcondition no longer needs table contents. -/
theorem finish_rootPair {S : Nat} (h16 : 16≤S) (hS : S<2^64) {p : Params} (hF : VFacts p) :
    RelCT isa (RootPair p S (SCx p S p.ℓ true p.k))
      (.seq (shake256With keccak.callee (hIns p) [⟨.x28,oCT,p.ctildeLen⟩])
        (cmpAnd (sc oCT) (.x27,0) p.ctildeLen))
      (RootPair p S (VFin p)) := by
  have h := finish_vpiece (keccak:=keccak) h16 hS hF
  exact rootPair_progress h.ok (RelCT.mono h.tr (fun _ _ h=>h.1) (fun _ _ _=>trivial))

end VG.Proof.MlDsa.AArch64.Verify.Optimized
