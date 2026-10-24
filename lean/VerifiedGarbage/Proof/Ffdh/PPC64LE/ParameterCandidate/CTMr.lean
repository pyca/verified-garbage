module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTDraw
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Mr
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTDraw
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Mr

/-!
# An FFDH parameter candidate on PPC64LE: the witnesses in constant time

`millerRabin_ct`: two runs testing the same modulus from the same tape
(`MI0`) leak the same: whether there is room for a witness, the draw
(`draw_ct`), and whether the loop goes on (`mrGo`), each decided by the
public data, the next iteration's data a function of it (`mrNext`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-- The witness loop's public data. -/
structure MrD where
  q : PP
  mb : Nat
  N : Nat
  res : Option (Bool × List Byte)
  i : Nat
  u : Nat

/-- At the head of the witness loop. -/
def MI (a : MrD) (s : State) : Prop :=
  (∃ sv toc, MrSt (a.q.with sv toc) a.mb a.N a.res a.i a.u s) ∧ Spec.RsaKeyGen.bitLength (a.N - 1) = a.mb

/-- After the loop. -/
def ME (a : MrD) (s : State) : Prop := ∃ sv toc, MrEnd (a.q.with sv toc) a.mb a.N a.res s

def mrNext (a : MrD) : MrD :=
  { a with i := dIdx a.N a.i (wA a.mb a.q.r a.u), u := a.u + (a.mb + 7) / 8 }

/-- The working space's address. -/
def R31 (a : MrD) (s : State) : Prop := s.gpr .r31 = a.q.B

theorem pins_R31 : Pins R31 [.r31] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

theorem pins_MI : Pins MI [.r31] := by
  rintro d s₁ s₂ ⟨⟨_, _, h₁⟩, -⟩ ⟨⟨_, _, h₂⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.m.st.r31, h₂.m.st.r31]; rfl

/-- After the head's block. -/
def MH (a : MrD) (s : State) : Prop :=
  MI a s ∧ s.gpr .r5 = BitVec.ofNat 64 (if (a.mb + 7) / 8 ≤ a.q.r.length - a.u then 1 else 0)

theorem headBlk_MH {a : MrD} {s : State} (h : MI a s) :
    WP isa (.block (([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] : List Instr) ++
      geFlag .r5 .r3 .r4)) s (MH a) := by
  obtain ⟨⟨sv, toc, hs⟩, hbl⟩ := h
  refine WP.mono (mrHeadBlk_ok hs) fun t ⟨⟨t5, tm⟩, k⟩ => ⟨⟨⟨sv, toc, ?_⟩, hbl⟩, t5⟩
  have M : MSt (a.q.with sv toc) a.mb a.N t := hs.m.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k
    (by decide) (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide))
  exact ⟨M, by rw [tm]; exact hs.used, by rw [tm]; exact hs.idx, by rw [tm]; exact hs.stat, hs.ul, hs.ik, hs.rest⟩

theorem mrBody_ct (R : RoundImpl) : RelCT isa (Two MI)
    (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] : List Instr) ++
        geFlag .r5 .r3 .r4))
      (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw R.name R.code))
        (.block [ldh .r3 hStat, .subi .r3 .r3 4]))) fun _ _ => True := by
  refine RelCT.seq (two_post (two_taint _ pins_MI (by taint_decide)) fun _ _ h => headBlk_MH h)
    (RelCT.seq (R := Two R31) ?_ ?_)
  rotate_left
  · exact two_taint _ pins_R31 (by taint_decide)
  have ev : ∀ a s, MH a s → isa.eval (.zero .d .r5) s = some (!decide ((a.mb + 7) / 8 ≤ a.q.r.length - a.u)) :=
    fun a s h => by
      rw [eval_zero_ofNat s .r5 (by split <;> decide) h.2]
      split <;> simp_all
  refine two_ite' (fun a => !decide ((a.mb + 7) / 8 ≤ a.q.r.length - a.u)) ev ?_ ?_
  · refine two_post (two_taint _ (fun a s₁ s₂ h₁ h₂ => pins_MI a s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide))
      fun a s h => ?_
    obtain ⟨⟨⟨⟨sv, toc, hs⟩, -⟩, -⟩, -⟩ := h
    have l160 := hs.m.st.st (d := 160) (by decide)
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r31 = a.q.B) ?_ (by decide)) fun t ⟨ht, _⟩ => ht
    simp only [sth, hStat]; prun [hs.m.st.r31, l160]; rfl
  · have hd : ∀ a s, MH a s ∧ (!decide ((a.mb + 7) / 8 ≤ a.q.r.length - a.u)) = false →
        DI ⟨a.q, a.mb, a.N, a.u, a.i⟩ s := by
      rintro a s ⟨⟨⟨⟨sv, toc, hs⟩, -⟩, -⟩, hb⟩
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
      have hul : a.u ≤ a.q.r.length := hs.ul
      have hik : a.i < Spec.Ffdh.primeChecks a.mb := hs.ik
      have hK : Spec.Ffdh.primeChecks a.mb ≤ 128 := by unfold Spec.Ffdh.primeChecks; split <;> omega
      exact ⟨sv, toc, hs.m, hs.used, show a.u + (a.mb + 7) / 8 ≤ a.q.r.length by omega, hs.idx, hs.stat,
        show a.i < 2 ^ 62 by omega⟩
    refine two_post (two_map (fun a : MrD => (⟨a.q, a.mb, a.N, a.u, a.i⟩ : DrawD)) hd (draw_ct R)) fun a s h => ?_
    obtain ⟨sv, toc, M, hu, hroom, hI, hS, hi⟩ := hd a s h
    exact WP.mono (draw_ok R M hu hroom hI hS hi) fun t ht => ht.1.st.r31

/-- Before the witness loop. -/
def MI0 (a : MrD) (s : State) : Prop :=
  (∃ sv toc, MSt (a.q.with sv toc) a.mb a.N s ∧ word s.mem a.q.B 152 = BitVec.ofNat 64 a.u) ∧
    a.u ≤ a.q.r.length ∧ a.i = 0 ∧ a.res = checkWitnesses a.N (Spec.Ffdh.primeChecks a.mb) (a.q.r.drop a.u) ∧
    Spec.RsaKeyGen.bitLength (a.N - 1) = a.mb

theorem pins_MI0 : Pins MI0 [.r31] := by
  rintro d s₁ s₂ ⟨⟨_, _, h₁, -⟩, -⟩ ⟨⟨_, _, h₂, -⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.st.r31, h₂.st.r31]; rfl

/-- The witness loop leaks the same in runs testing the same modulus from the
same tape. -/
theorem millerRabin_ct (R : RoundImpl) : RelCT isa (Two MI0) (millerRabin R.name R.code) (Two ME) := by
  unfold millerRabin
  refine RelCT.seq (two_post (two_taint _ pins_MI0 (by taint_decide)) (Ψ := MI) fun a s h => ?_)
    (two_loopD (fun a => a.q.r.length + 1 - a.u) mrNext (fun a => mrGo a.q.r a.mb a.N a.i a.u) (mrBody_ct R)
      fun a s h => ?_)
  · obtain ⟨⟨sv, toc, M, hu⟩, hul, hi, hres, hbl⟩ := h
    refine WP.mono (mrInit_ok M hu hul) fun t ht => ⟨⟨sv, toc, ?_⟩, hbl⟩
    rw [hi, hres]; exact ht
  · obtain ⟨⟨sv, toc, hs⟩, hbl⟩ := h
    have hm1 := hs.m.mb1
    refine WP.mono (mrIter_ok R hbl hs) fun t ⟨he, hend, hgo⟩ =>
      ⟨he, fun hg => ⟨sv, toc, hend hg⟩, fun hg => ⟨?_, ⟨sv, toc, hgo hg⟩, hbl⟩⟩
    have hul : a.u + (a.mb + 7) / 8 ≤ a.q.r.length := (hgo hg).ul
    show a.q.r.length + 1 - (a.u + (a.mb + 7) / 8) < a.q.r.length + 1 - a.u
    omega

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
