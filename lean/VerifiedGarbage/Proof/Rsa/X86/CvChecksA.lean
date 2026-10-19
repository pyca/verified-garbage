module

import VerifiedGarbage.Proof.Rsa.X86.KeyEq
import VerifiedGarbage.Proof.Rsa.X86.KeyWord
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeySub

/-! # CRT checks and initialization of binary inversion -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

structure Geometry where
  base : Addr
  size : Nat
  w : Nat
  P : Nat
  Q : Nat
  D : Nat
  N : Nat

def Geometry.M (g : Geometry) : Nat := 2 * (g.P / 2) + 1

def zeroC : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22, 23]

structure StC (g : Geometry) (s : State) : Prop where
  ws : Ws s g.base g.size g.w nArr
  podd : slot s.mem g.base sPodd = g.P % 2
  p : num s.mem g.base g.w aP = g.P
  q : num s.mem g.base g.w aQ = g.Q
  d : num s.mem g.base g.w aD = g.D
  ddTop : w32 s.mem g.base (arr g.w aDD + 4 * g.w) = 0
  division : 0 < g.P → num s.mem g.base g.w aDQ = g.N / g.P ∧ num s.mem g.base g.w aDR = g.N % g.P
  zeros : ∀ j ∈ zeroC, num s.mem g.base g.w j = 0

def checksA (w : Nat) : List (Prog isa) :=
  [eqS w sE1 aDQ aQ aT1, eqS w sE2 aDR aZero aT1] ++ invSetup w

structure StI (g : Geometry) (X₁ X₂ : Nat) (s : State) : Prop where
  ws : Ws s g.base g.size g.w nArr
  podd : slot s.mem g.base sPodd = g.P % 2
  e1 : slot s.mem g.base sE1 = if X₁ = g.Q then 1 else 0
  e2 : slot s.mem g.base sE2 = if X₂ = 0 then 1 else 0
  p : num s.mem g.base g.w aP = g.P
  q : num s.mem g.base g.w aQ = g.Q
  d : num s.mem g.base g.w aD = g.D
  ddTop : w32 s.mem g.base (arr g.w aDD + 4 * g.w) = 0
  u : num s.mem g.base g.w 0 = g.Q
  v : num s.mem g.base g.w 1 = g.M
  x₁ : num s.mem g.base g.w 2 = 1
  x₂ : num s.mem g.base g.w 3 = 0
  m : num s.mem g.base g.w aM = g.M
  nm : num s.mem g.base g.w aNM + g.M = 2 ^ (32 * g.w)
  zero : num s.mem g.base g.w aZero = 0
  one : num s.mem g.base g.w aOne = 1

theorem checksA_ok {g : Geometry} {s : State} (h : StC g s) :
    WP isa (seqs (checksA g.w)) s fun t =>
      StI g (num s.mem g.base g.w aDQ) (num s.mem g.base g.w aDR) t ∧
      Keep g.base g.w [aT1, 0, aM, 1, 2, aOne, aNM] [sT, sE1, sE2] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have h1 := h.ws
  unfold checksA invSetup
  simp only [List.cons_append, List.nil_append]
  have fit := fun j (hj : j < nArr) => h1.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h1 (d := sE1) (a := aDQ) (b := aQ) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h2 (d := sE2) (a := aDR) (b := aZero) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (o := 0) (a := aQ) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (o := aM) (a := aP) (by decide) (by decide))
    fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (orOne_ok h5 (by decide)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h6 (o := 1) (a := aM) (by decide) (by decide))
    fun t7 ⟨h7, k7, e7, r7, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.block_append (WP.mono (setOne_ok h7 (j := 2) (by decide)) fun t8' ⟨h8', k8', e8', r8'⟩ => ?_)
  refine WP.mono (setOne_ok h8' (j := aOne) (by decide)) fun t8 ⟨h8, k8, e8, r8⟩ => ?_
  refine WP.mono (sub3_ok h8 (o := aNM) (a := aZero) (b := aM) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨ht, k9, e9, b9, r9⟩ => ?_
  have K : Keep g.base g.w [aT1, 0, aM, 1, 2, aOne, aNM] [sT, sE1, sE2] s.mem t.mem :=
    k2.mono.trans (k3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans (k7.mono.trans
      (k8'.mono.trans (k8.mono.trans k9.mono)))))))
  have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t :=
    r2.trans (r3.trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans
      ((r6.mono (by decide)).trans ((r7.mono (by decide)).trans ((r8'.mono (by decide)).trans
        ((r8.mono (by decide)).trans r9)))))))
  have z0 : ∀ j ∈ zeroC, num s.mem g.base g.w j = 0 := fun j hj => h.zeros j hj
  have K1 : ∀ j, j < nArr → j ∉ [aT1, 0, aM, 1, 2, aOne, aNM] →
      num t.mem g.base g.w j = num s.mem g.base g.w j := fun j hj hn => by
    rw [K.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj)]
  -- `M`.
  have M5 : num t5.mem g.base g.w aM = g.P := by
    rw [e5, k4.num (by decide) (by simp) (fit _ (by decide)), k3.num (by decide) (by decide) (fit _ (by decide)),
      k2.num (by decide) (by decide) (fit _ (by decide)), h.p]
  have M6 : num t6.mem g.base g.w aM = g.M := by rw [e6, M5]; rfl
  have M8 : num t8.mem g.base g.w aM = g.M := by
    rw [k8.num (by decide) (by simp) (fit _ (by decide)), k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), M6]
  have Z8 : num t8.mem g.base g.w aZero = 0 := by
    rw [k8.num (by decide) (by simp) (fit _ (by decide)), k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]
  refine ⟨?_, K, R⟩
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [K.slot (by decide) (by decide), h.podd]
  · rw [k9.slot (by decide) (by simp), k8.slot (by decide) (by simp), k8'.slot (by decide) (by simp),
      k7.slot (by decide) (by simp), k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), k3.slot (by decide) (by decide), e2, h.q]
  · rw [k9.slot (by decide) (by simp), k8.slot (by decide) (by simp), k8'.slot (by decide) (by simp),
      k7.slot (by decide) (by simp), k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), e3, k2.num (j := aDR) (by decide) (by decide) (fit _ (by decide)),
      k2.num (j := aZero) (by decide) (by decide) (fit _ (by decide)), z0 aZero (by decide)]
  · rw [K1 _ (by decide) (by decide), h.p]
  · rw [K1 _ (by decide) (by decide), h.q]
  · rw [K1 _ (by decide) (by decide), h.d]
  · rw [K.word (by simp only [S]; omega) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), k8.num (by decide) (by simp) (fit _ (by decide)),
      k8'.num (by decide) (by simp) (fit _ (by decide)), k7.num (by decide) (by simp) (fit _ (by decide)),
      k6.num (by decide) (by simp) (fit _ (by decide)), k5.num (by decide) (by simp) (fit _ (by decide)), e4,
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      h.q]
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), k8.num (by decide) (by simp) (fit _ (by decide)),
      k8'.num (by decide) (by simp) (fit _ (by decide)), e7, M6]
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), k8.num (by decide) (by simp) (fit _ (by decide)), e8',
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]
  · rw [K1 _ (by decide) (by decide)]; exact z0 _ (by decide)
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), M8]
  · rw [Z8, M8] at e9
    have : 0 < g.M := by unfold Geometry.M; omega
    have l := val32_lt t.mem g.base (arr g.w aNM) g.w
    rcases (by omega : (t.gpr .ebx).toNat = 0 ∨ (t.gpr .ebx).toNat = 1) with e | e <;> rw [e] at e9 <;> omega
  · rw [K1 _ (by decide) (by decide)]; exact z0 _ (by decide)
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), e8, k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]

end VG.Proof.Rsa.X86.CrtValues
