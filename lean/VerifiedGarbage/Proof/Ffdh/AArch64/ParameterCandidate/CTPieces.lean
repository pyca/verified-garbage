module
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Halve
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Halve
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots

/-!
# An FFDH parameter candidate on AArch64: constant time of the shape's checks

The congruence (`residue_ct`), RSA's table (`tableWrite_ct`), the sieve
(`sieve_ct`, RSA's `trialEntry_ct` for the words it reads, `stopN`, which
the number in `aN` fixes) and `q` (`halveQ_ct`), each from the working
space and what it reads.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The working space of `p`'s words. -/
def WQ (L : WsP) (s : State) : Prop := Ws s L.B L.Z L.w

theorem residue_ct : RelCT isa (Two WQ) (seqs residue) fun _ _ => True :=
  ws_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) (by taint_decide)

theorem tableWrite_ct : RelCT isa (Two WQ) tableWrite fun _ _ => True :=
  ws_block_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) (by taint_decide)

/-! ## The sieve -/

/-- RSA's public data, for the working space alone. -/
def fpubOf (L : WsP) : VG.Proof.RsaKeyGen.AArch64.FPub := ⟨L.B, L.Z, L.w, [], 0, 0, 0, [], 0, 0, 0, 0, ⟨false, false, false, none⟩⟩

/-- Before the sieve of the number `a.2` in `aN`. -/
def SV (a : WsP × Nat) (s : State) : Prop :=
  Ws s a.1.B a.1.Z a.1.w ∧ slot a.1.w aTab + 2048 ≤ a.1.Z ∧ TabOk s.mem a.1.B a.1.w ∧
    wv s.mem a.1.B (slot a.1.w aN) a.1.w = a.2

/-- Before word `k` of the table. -/
def SI (a : WsP × Nat) (k : Nat) (s : State) : Prop :=
  Ws s a.1.B a.1.Z a.1.w ∧ slot a.1.w aTab + 2048 ≤ a.1.Z ∧ s.gpr .x9 = off a.1.B (slot a.1.w aTab + 8 * k) ∧
    s.gpr .x10 = BitVec.ofNat 64 (trialN a.1.w - k) ∧ s.gpr .x7 = 0 ∧ s.gpr .x8 = mask true ∧
    TabOk s.mem a.1.B a.1.w ∧ wv s.mem a.1.B (slot a.1.w aN) a.1.w = a.2 ∧ s.gpr .x1 = mask (anyPre a.2 (4 * k))

/-- After the loop. -/
def SIE (a : WsP × Nat) (s : State) : Prop := Ws s a.1.B a.1.Z a.1.w

/-- The words the sieve reads. -/
abbrev sieveN (a : WsP × Nat) : Nat := stopN a.2 (trialN a.1.w)

theorem trialN_le (w : Nat) : trialN w ≤ 256 ∧ 1 ≤ trialN w := by unfold trialN; split <;> omega_using []

theorem sieveIter_ok {a : WsP × Nat} {k : Nat} {s : State} (hk : k < stopN a.2 (trialN a.1.w)) (h : SI a k s) :
    WP isa (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)) ++
      ([sieveStop] : List (Prog isa)))) s fun t =>
      isa.eval (.nonzero .x .x10) t = some (decide (k + 1 < stopN a.2 (trialN a.1.w))) ∧
        (k + 1 < stopN a.2 (trialN a.1.w) → SI a (k + 1) t) ∧ (k + 1 = stopN a.2 (trialN a.1.w) → SIE a t) := by
  obtain ⟨hw, hT, h9, h10, h7, h8, htab, hc, h1⟩ := h
  have hN := trialN_le a.1.w
  have hle : stopN a.2 (trialN a.1.w) ≤ trialN a.1.w := stopN_le _ _
  obtain ⟨nxt, nxf⟩ := stopN_next hk
  have e10 : BitVec.ofNat 64 (trialN a.1.w - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (trialN a.1.w - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hk, hle, hN.1]
  refine WP.mono (sieveWord_ok (s₀ := s) hc hT (by omega_using [hk, hle, hN.1]) htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩
    h9 h1) fun t ⟨hI, h9', h1', h10'⟩ => ⟨?_, fun hlt => ⟨hI.ws, hT, h9', ?_, hI.x7, hI.x8, fun i hi => by
      rw [hI.mem]; exact htab i hi, by rw [hI.mem]; exact hc, h1'⟩, fun _ => hI.ws⟩
  · rw [eval_nonzero, h10']
    rcases Bool.eq_false_or_eq_true (anyPre a.2 (4 * (k + 1))) with hd | hd
    · have e := nxt hd
      rw [ite_eq_left hd]
      exact congrArg some ((decide_eq_false (by omega_using [e])).symm)
    · have hi := nxf hd
      rw [ite_eq_right (by rw [hd]; exact Bool.false_ne_true), h10,
        sub1_bne (by omega_using [hk, hle]) (by omega_using [hN.1])]
      exact congrArg some (decide_eq_decide.mpr (by omega_using [hi]))
  · rw [h10', ite_eq_right (by rw [stopN_before _ _ (k + 1) hlt]; exact Bool.false_ne_true), h10, e10]

theorem sieveBody_ct : RelCT isa (Two fun (a : (WsP × Nat) × Nat) s => a.2 < sieveN a.1 ∧ SI a.1 a.2 s)
    (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)) ++
      ([sieveStop] : List (Prog isa)))) fun _ _ => True := by
  simp only [List.append_assoc, List.singleton_append]
  have ne : ∀ j, trialEntry j ≠ [] := fun j => by unfold trialEntry; exact List.cons_ne_nil _ _
  refine seqs_cons_ct (by simp [ne]) (RelCT.seq (two_post (Ψ := fun a s => TBI (fpubOf a.1.1, a.2) s)
    (two_taint [.x9] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.1, h₂.2.2.2.1]) (by taint_decide))
    (fun p s h => ?_)) ?_)
  · obtain ⟨hk, hw, hT, h9, -, h7, h8, htab, -, -⟩ := h
    have hN := trialN_le p.1.1.w
    have hle : stopN p.1.2 (trialN p.1.1.w) ≤ trialN p.1.1.w := stopN_le _ _
    replace hk : p.2 < stopN p.1.2 (trialN p.1.1.w) := hk
    exact WP.mono (tlLoad_ok hT (by omega_using [hk, hN, hle]) htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩ h9) fun t ⟨⟨h17, _, hm⟩, k⟩ =>
      ⟨hw.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k (by decide), by omega_using [hk, hN, hle], h17,
        (k.gpr .x7 (by decide)).trans h7, (k.gpr .x8 (by decide)).trans h8⟩
  refine two_map (Φ' := TBI) (fun a : (WsP × Nat) × Nat => (fpubOf a.1.1, a.2)) (fun _ _ h => h) ?_
  refine RelCT.seqs_append (ne 0) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 1) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 2) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 3) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  exact two_taint [] (pins_nil₀ _) (by taint_decide)

/-- The sieve leaks the same in runs with the same working space and the
same number in `aN`, which fixes the word it stops at. -/
theorem sieve_ct : RelCT isa (Two SV) (seqs sieve) fun _ _ => True := by
  rw [sieve_eq]
  simp only [seqs]
  refine RelCT.seq (two_post (ws_block_ct0 (fun a : WsP × Nat => a.1.B) (fun a : WsP × Nat => a.1.Z)
    (fun a : WsP × Nat => a.1.w) (fun _ _ h => h.1) (by taint_decide)) (Ψ := fun a s => 0 < sieveN a ∧ SI a 0 s)
      fun a s ⟨hw, hT, htab, hc⟩ => ?_)
    (RelCT.seq (two_loop (Φ := SI) (Ψ := SIE) sieveN sieveBody_ct fun _ _ _ hk h => sieveIter_ok hk h)
      (two_taint [.x0] (pins_ws' (fun a : WsP × Nat => a.1.B) (fun a : WsP × Nat => a.1.Z)
        (fun a : WsP × Nat => a.1.w) fun _ _ h => h) (by taint_decide)))
  refine WP.mono (sieveInit_ok hw) fun t ⟨⟨h9, h10, h1, h7, h8, hm⟩, k⟩ =>
    ⟨stopN_pos _ (trialN_le a.1.w).2, ?_⟩
  exact ⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), hT, h9,
    by rw [h10, Nat.sub_zero], h7, h8, fun i hi => by rw [hm]; exact htab i hi, by rw [hm]; exact hc,
    by rw [h1, Nat.mul_zero, anyPre_zero]; rfl⟩

/-! ## `q` -/

theorem halvePass_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (seqs (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1]) :: halfPass))
      s fun t => Ws t B Z w := by
  have hn := h.scr.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have sN := h.sl (show aN < 16 by decide)
  have e : seqs (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1]) :: halfPass) =
      .seq (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1])) (seqs halfPass) := rfl
  rw [e]
  refine WP.seq (WP.mono (halveHead_ok h) fun s₁ ⟨⟨h16, h17, h15, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (halfPass_ok (mb := true) (h.scr.congr k₁.wr) h16 h17 h15 h12 hw1 (by omega_using [hw2]) (by omega_using [sN]) (by omega_using [sN])
    (.inl rfl)) fun t ⟨_, o, k₂⟩ => ?_
  rw [hm₁] at o
  exact h.congr' (Frm.of_outside (o.mono (o' := slot w aN) (n' := 8 * (w + 2)) (by omega_using []) (by omega_using []))
    (List.mem_singleton_self _)) (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _)
    (k₁.trans k₂) (by decide)

/-- `halveQ` leaks the same in runs with the same working space. -/
theorem halveQ_ct : RelCT isa (Two WQ) (seqs halveQ) fun _ _ => True := by
  unfold halveQ
  rw [List.cons_append]
  refine ct_app' (a := _ :: halfPass) (by simp) (by simp) (Ψ := WQ) (two_post ?_ fun L s h => halvePass_ok h) ?_
  · exact ws_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) (by taint_decide)
  · rw [seqs_one]
    exact ws_block_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h)
      (by taint_decide)

end VG.Proof.Ffdh.AArch64.ParameterCandidate
