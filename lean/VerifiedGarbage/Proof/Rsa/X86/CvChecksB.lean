module

public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
public import VerifiedGarbage.Proof.Rsa.X86.CvChecksA
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
import VerifiedGarbage.Proof.Rsa.X86.KeyWord
import VerifiedGarbage.Proof.Rsa.X86.KeyEq
import VerifiedGarbage.Proof.Rsa.X86.InvParts

/-! # CRT inverse checks and the mask for releasing calculated parameters -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

def checksB (w : Nat) : List (Prog isa) := [inverse w, eqS w sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  copy w aDQ aD, copy w aDD aP, .block (clrLow w aDD)]

/-- The mask of the checks, from the quotient `X₁` and remainder `X₂` of `n / p` and the gcd `V`. -/
abbrev maskOf := VG.Proof.Rsa.CrtValues.maskOf

def InverseResult (g : Geometry) (X₁ X₂ : Nat) (m : Mem) : Prop :=
  ∃ V, slot m g.base sMask = (if maskOf g.P g.Q X₁ X₂ V then 1 else 0) ∧
    (1 < g.M → V = Nat.gcd g.Q g.M ∧
      (g.M : Int) ∣ (num m g.base g.w 3 : Int) * g.Q - V ∧ num m g.base g.w 3 < g.M)

/-- Before the division of `d` by `p - 1`. -/
structure StD (g : Geometry) (X₁ X₂ : Nat) (s : State) : Prop where
  ws : Ws s g.base g.size g.w nArr
  q : num s.mem g.base g.w aQ = g.Q
  d : num s.mem g.base g.w aD = g.D
  ddTop : w32 s.mem g.base (arr g.w aDD + 4 * g.w) = 0
  dq : num s.mem g.base g.w aDQ = g.D
  dd : num s.mem g.base g.w aDD = 2 * (g.P / 2)
  mask : InverseResult g X₁ X₂ s.mem

theorem checksB_ok {g : Geometry} {s : State} {X₁ X₂ : Nat} (h : StI g X₁ X₂ s) :
    WP isa (seqs (checksB g.w)) s fun t => StD g X₁ X₂ t ∧
      Keep g.base g.w (invArrs ++ [aDQ, aDD]) (invSlots ++ [sT, sE3, sMask]) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have hw := h.ws
  have fit := fun j (hj : j < nArr) => hw.fit64 (j := j) hj
  unfold checksB
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (inverse_ok hw (by decide)) fun t1 ⟨h1, k1, r1, inv⟩ => ?_
  have I := fun (hM : 1 < g.M) => inv (by rw [h.m, h.nm]) h.zero (by rw [h.m]; simp only [Geometry.M]; omega)
    (by rw [h.m]; exact hM) (by simp only [bank]; rw [h.u, h.v, h.x₁, h.x₂, h.m])
  rw [h.m, h.u] at I
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h1 (d := sE3) (a := 1) (b := aOne) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have one1 : num t1.mem g.base g.w aOne = 1 := by
    rw [k1.num (by decide) (by decide) (fit _ (by decide)), h.one]
  rw [one1] at e2
  have sl : ∀ d, d + 4 ≤ hdr → d % 4 = 0 → d ∉ [sT, sE3, sOdd, sB, sC] →
      slot t2.mem g.base d = slot s.mem g.base d := fun d hd h4 hn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp only [sT, sE3, sOdd, sB, sC, hdr] at hn hd
    rw [k2.slot (by simp only [hdr]; omega) (by simp only [sT, sE3]; simp; omega),
      k1.slot (by simp only [hdr]; omega) (by simp only [invSlots, sOdd, sB, sC]; simp; omega)]
  rw [wp_seqs_cons (List.cons_ne_nil _ _), List.append_assoc]
  refine WP.block_append ?_
  refine WP.mono (andS_ok h2 (d := sMask) (a := sPodd) (b := sE1) (by decide) (by decide) (by decide)
    (by rw [sl _ (by decide) (by decide) (by decide), h.podd]; omega) (by rw [sl _ (by decide) (by decide) (by decide), h.e1]; split <;> omega)
    ) fun t3a ⟨h3a, k3a, m3a, r3a⟩ => ?_
  refine WP.block_append ?_
  refine WP.mono (andS_ok h3a (d := sMask) (a := sMask) (b := sE2) (by decide) (by decide) (by decide)
    (by rw [m3a]; split <;> omega) (by rw [k3a.slot (by decide) (by decide), sl _ (by decide) (by decide) (by decide), h.e2]; split <;> omega)
    ) fun t3b ⟨h3b, k3b, m3b, r3b⟩ => ?_
  refine WP.mono (andS_ok h3b (d := sMask) (a := sMask) (b := sE3) (by decide) (by decide) (by decide)
    (by rw [m3b]; split <;> omega)
    (by rw [k3b.slot (by decide) (by decide), k3a.slot (by decide) (by decide), e2]; split <;> omega)
    ) fun t3 ⟨h3, k3, m3, r3⟩ => ?_
  have K3 : Keep g.base g.w [] [sMask] t2.mem t3.mem := k3a.trans (k3b.trans k3)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (o := aDQ) (a := aD) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (o := aDD) (a := aP) (by decide) (by decide))
    fun t5 ⟨h5, k5, e5, r5, top5⟩ => ?_
  refine WP.mono (clrLow_ok h5 (by decide)) fun t ⟨h6, k6, e6, r6, top6⟩ => ?_
  -- The count, through every step.
  have K : Keep g.base g.w (invArrs ++ [aDQ, aDD]) (invSlots ++ [sT, sE3, sMask]) s.mem t.mem :=
    k1.mono.trans (k2.mono.trans (K3.mono.trans (k4.mono.trans (k5.mono.trans k6.mono))))
  have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
    r1.trans ((r2.mono (by decide)).trans ((r3a.mono (by decide)).trans ((r3b.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans (r6.mono (by decide))))))))
  have tr : ∀ j, j < nArr → j ∉ invArrs ++ [aDQ, aDD] →
      num t.mem g.base g.w j = num s.mem g.base g.w j := fun j hj hn =>
    K.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj)
  have fDD := fit aDD (by decide)
  have hS : S g.w = 4 * (g.w + 2) := rfl
  refine ⟨?_, K, R⟩
  refine ⟨h6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tr _ (by decide) (by decide), h.q]
  · rw [tr _ (by decide) (by decide), h.d]
  · rw [top6, top5,
      k4.word (by omega) (by decide) (by simp) fDD, K3.word (by omega) (by simp) (by decide) fDD,
      k2.word (by omega) (by decide) (by decide) fDD, k1.word (by omega) (by decide) (by decide) fDD, h.ddTop]
  · rw [k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), e4, K3.num (by simp) (by decide) (fit _ (by decide)),
      k2.num (by decide) (by decide) (fit _ (by decide)), k1.num (by decide) (by decide) (fit _ (by decide)), h.d]
  · rw [e6, e5, k4.num (by decide) (by simp) (fit _ (by decide)),
      K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      k1.num (by decide) (by decide) (fit _ (by decide)), h.p]
  · have x3 : num t.mem g.base g.w 3 = num t1.mem g.base g.w 3 := by
      rw [k6.num (by decide) (by simp) (fit _ (by decide)),
        k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
        K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide))]
    refine ⟨num t1.mem g.base g.w 1, ?_, fun hM => by rw [x3]; exact I hM⟩
    rw [k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), m3, m3b, k3b.slot (e := sE3) (by decide) (by decide), m3a,
      k3a.slot (e := sE2) (by decide) (by decide), k3a.slot (e := sE3) (by decide) (by decide), e2,
      sl sPodd (by decide) (by decide) (by decide), sl sE1 (by decide) (by decide) (by decide),
      sl sE2 (by decide) (by decide) (by decide), h.podd, h.e1, h.e2]
    simp only [maskOf, VG.Proof.Rsa.CrtValues.maskOf]
    by_cases a : g.P % 2 = 1 <;> by_cases b : X₁ = g.Q <;> by_cases c : X₂ = 0 <;>
      by_cases d : num t1.mem g.base g.w 1 = 1 <;> simp [a, b, c, d]

end VG.Proof.Rsa.X86.CrtValues
