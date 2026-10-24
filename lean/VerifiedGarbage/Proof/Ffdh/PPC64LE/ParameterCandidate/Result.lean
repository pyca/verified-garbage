module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Mr
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.End
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# An FFDH parameter candidate on PPC64LE: the results of the tests

`pResult_ok`: after p's test, p to `out` if it passed, the status by its
`hStat`; `qResult_ok`: after a failed test of q.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

theorem ofNat_toNat64' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `hStat` into `r3`. -/
theorem statLoad_ok {p : PP} {mb N : Nat} {s : State} (M : MSt p mb N s) :
    WP isa (.block [ldh .r3 hStat]) s fun t => MSt p mb N t ∧ t.gpr .r3 = word s.mem p.B 160 ∧ t.mem = s.mem ∧
      Keep [.r3] s t := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = word s.mem p.B 160 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; prun [M.st.r31, l160]) (by decide)) fun t ⟨⟨t3, tm⟩, k⟩ => ?_
  exact ⟨M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k (by decide) (k.gpr _ (by decide))
    (k.gpr _ (by decide)) (k.gpr _ (by decide)), t3, tm, k⟩

/-- After p's test. -/
theorem pResult_ok {p : PP} {s : State} {c : Nat} {resP : Option (Bool × List Byte)}
    (hE : MrEnd p p.bits c resP s) (hc : c < 2 ^ p.bits) :
    WP isa pResult s (CEnd p (resP.map fun x => (if x.1 then some c else none, x.2))) := by
  obtain ⟨M, hnone, hsome⟩ := hE
  unfold pResult
  refine WP.seq (WP.mono (statLoad_ok M) fun t ⟨Mt, t3, tm, _⟩ => ?_)
  have h152 : word t.mem p.B 152 = word s.mem p.B 152 := by rw [tm]
  rcases resP with _ | ⟨b, rest⟩
  · have h0 := hnone rfl
    refine WP.ite true (eval_zero_ofNat t .r3 (k := 0) (by decide) (t3.trans h0)) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact finEnd Mt.st (r := 0) (Or.inl rfl) rfl rfl rfl (ofNat_toNat64' _)
  · obtain ⟨hS, u, hul, rfl, hU⟩ := hsome b rest rfl
    have hU' : word t.mem p.B 152 = BitVec.ofNat 64 u := h152.trans hU
    cases b
    · refine WP.ite false (eval_zero_ofNat t .r3 (k := 2) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 1 ∧ v.mem = t.mem)
        (by prun [t3, hS]; rfl) (by decide)) fun v ⟨⟨v3, vm⟩, k⟩ => ?_)
      have Mv : MSt p p.bits c v := Mt.frm (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) k (by decide)
        (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide))
      refine WP.ite false (eval_zero_ofNat v .r3 (k := 1) (by decide) v3) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine finEnd Mv.st (r := 2) (v := u) (Or.inr rfl) rfl rfl ?_ (by rw [vm]; exact hU')
      simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte, usedOf, List.length_drop, Nat.reduceEqDiff]
      omega_arith
    · refine WP.ite false (eval_zero_ofNat t .r3 (k := 1) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 0 ∧ v.mem = t.mem)
        (by prun [t3, hS]; rfl) (by decide)) fun v ⟨⟨v3, vm⟩, k⟩ => ?_)
      have Mv : MSt p p.bits c v := Mt.frm (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) k (by decide)
        (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide))
      refine WP.ite true (eval_zero_ofNat v .r3 (k := 0) (by decide) v3) (fun _ => ?_) (fun h => absurd h (by decide))
      have hn : Mont.val32 v.mem p.B 256 (2 * wOf p.bits) = c := by
        have := Mv.prep.n
        simp only [MillerRabin.PPC64LE.arr] at this
        rw [show slot (wOf p.bits) 0 = 256 by simp [slot, hdrBytes]] at this
        exact this
      exact pEnd Mv.st Mv.ph hn hc (by rw [vm]; exact hU') hul

/-- After a failed test of q. -/
theorem qResult_ok {p : PP} {s : State} {mb N : Nat} {resQ : Option (Bool × List Byte)}
    (hE : MrEnd p mb N resQ s) (hq : ∀ rest, resQ ≠ some (true, rest)) :
    WP isa qResult s (CEnd p (resQ.map fun x => (none, x.2))) := by
  obtain ⟨M, hnone, hsome⟩ := hE
  unfold qResult
  refine WP.seq (WP.mono (statLoad_ok M) fun t ⟨Mt, t3, tm, _⟩ => ?_)
  rcases resQ with _ | ⟨b, rest⟩
  · refine WP.ite true (eval_zero_ofNat t .r3 (k := 0) (by decide) (t3.trans (hnone rfl))) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact finEnd Mt.st (r := 0) (Or.inl rfl) rfl rfl rfl (ofNat_toNat64' _)
  · cases b
    · obtain ⟨hS, u, hul, rfl, hU⟩ := hsome false rest rfl
      refine WP.ite false (eval_zero_ofNat t .r3 (k := 2) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine finEnd Mt.st (r := 2) (v := u) (Or.inr rfl) rfl rfl ?_ (by rw [tm]; exact hU)
      simp only [Option.map_some, ↓reduceIte, usedOf, List.length_drop, Nat.reduceEqDiff]
      omega_arith
    · exact absurd rfl (hq rest)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
