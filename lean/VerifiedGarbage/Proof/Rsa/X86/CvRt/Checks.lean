module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
import VerifiedGarbage.Proof.Rsa.X86.InvChoose
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Framework.Mem
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Proof.Rsa.X86.InvGate

/-! # CRT parameter calculation at a run-time width: the checks

`CrtValues`' checks and the binary inversion's setup (`checksA_ok`), then the
inversion, its check and the mask releasing the results (`checksB_ok`), on
`RtWs` at the width `kw len`.
-/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr seqs andS)
open VG.Impl.Rsa.X86.KeyRt (Lay)
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr)
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot wp_seqs_cons wp_seqs_append bank invArrs invSlots)
open VG.Proof.Rsa.X86.KeyRt

/-- The values the arithmetic works on. -/
structure Geometry where
  base : Addr
  size : Nat
  P : Nat
  Q : Nat
  D : Nat
  N : Nat

def Geometry.M (g : Geometry) : Nat := 2 * (g.P / 2) + 1

def zeroC : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22, 23]

structure StC (g : Geometry) (len : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  podd : slot s.mem g.base sPodd = g.P % 2
  p : num s.mem g.base (kw len) aP = g.P
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  division : 0 < g.P → num s.mem g.base (kw len) aDQ = g.N / g.P ∧ num s.mem g.base (kw len) aDR = g.N % g.P
  zeros : ∀ j ∈ zeroC, num s.mem g.base (kw len) j = 0

def checksA : List (Prog isa) :=
  [VG.Impl.Rsa.X86.KeyRt.eqS lay sE1 aDQ aQ aT1, VG.Impl.Rsa.X86.KeyRt.eqS lay sE2 aDR aZero aT1] ++ invSetup

structure StI (g : Geometry) (len : Nat) (X₁ X₂ : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  podd : slot s.mem g.base sPodd = g.P % 2
  e1 : slot s.mem g.base sE1 = if X₁ = g.Q then 1 else 0
  e2 : slot s.mem g.base sE2 = if X₂ = 0 then 1 else 0
  p : num s.mem g.base (kw len) aP = g.P
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  u : num s.mem g.base (kw len) 0 = g.Q
  v : num s.mem g.base (kw len) 1 = g.M
  x₁ : num s.mem g.base (kw len) 2 = 1
  x₂ : num s.mem g.base (kw len) 3 = 0
  m : num s.mem g.base (kw len) aM = g.M
  nm : num s.mem g.base (kw len) aNM + g.M = 2 ^ (32 * kw len)
  zero : num s.mem g.base (kw len) aZero = 0
  one : num s.mem g.base (kw len) aOne = 1

omit rsaBatchLaw in
theorem checksA_ok {g : Geometry} {len : Nat} {s : State} (h : StC g len s) :
    WP isa (seqs (checksA)) s fun t =>
      StI g len (num s.mem g.base (kw len) aDQ) (num s.mem g.base (kw len) aDR) t ∧
      Keep g.base (kw len) [aT1, 0, aM, 1, 2, aOne, aNM] [sT, sE1, sE2] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have h1 := h.ws
  unfold checksA invSetup
  simp only [List.cons_append, List.nil_append]
  have fit := fun j (hj : j < nArr) => h1.ws.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h1 (d := sE1) (a := aDQ) (b := aQ) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h2 (d := sE2) (a := aDR) (b := aZero) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (o := 0) (a := aQ) (by decide) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (o := aM) (a := aP) (by decide) (by decide) (by decide))
    fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (orOne_ok h5 (by decide)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h6 (o := 1) (a := aM) (by decide) (by decide) (by decide))
    fun t7 ⟨h7, k7, e7, r7, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.block_append (WP.mono (setOne_ok h7 (j := 2) (by decide)) fun t8' ⟨h8', k8', e8', r8'⟩ => ?_)
  refine WP.mono (setOne_ok h8' (j := aOne) (by decide)) fun t8 ⟨h8, k8, e8, r8⟩ => ?_
  refine WP.mono (sub3_ok h8 (o := aNM) (a := aZero) (b := aM) (by decide) (by decide) (by decide)) fun t ⟨ht, k9, e9, b9, r9⟩ => ?_
  have K : Keep g.base (kw len) [aT1, 0, aM, 1, 2, aOne, aNM] [sT, sE1, sE2] s.mem t.mem :=
    k2.mono.trans (k3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans (k7.mono.trans
      (k8'.mono.trans (k8.mono.trans k9.mono)))))))
  have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t :=
    (r2.mono (by decide)).trans ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans
      ((r6.mono (by decide)).trans ((r7.mono (by decide)).trans ((r8'.mono (by decide)).trans
        ((r8.mono (by decide)).trans (r9.mono (by decide)))))))))
  have z0 : ∀ j ∈ zeroC, num s.mem g.base (kw len) j = 0 := fun j hj => h.zeros j hj
  have K1 : ∀ j, j < nArr → j ∉ [aT1, 0, aM, 1, 2, aOne, aNM] →
      num t.mem g.base (kw len) j = num s.mem g.base (kw len) j := fun j hj hn => by
    rw [K.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj)]
  -- `M`.
  have M5 : num t5.mem g.base (kw len) aM = g.P := by
    rw [e5, k4.num (by decide) (by simp) (fit _ (by decide)), k3.num (by decide) (by decide) (fit _ (by decide)),
      k2.num (by decide) (by decide) (fit _ (by decide)), h.p]
  have M6 : num t6.mem g.base (kw len) aM = g.M := by rw [e6, M5]; rfl
  have M8 : num t8.mem g.base (kw len) aM = g.M := by
    rw [k8.num (by decide) (by simp) (fit _ (by decide)), k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), M6]
  have Z8 : num t8.mem g.base (kw len) aZero = 0 := by
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
    have l := val32_lt t.mem g.base (arr (kw len) aNM) (kw len)
    rcases (by omega : (t.gpr .ebx).toNat = 0 ∨ (t.gpr .ebx).toNat = 1) with e | e <;> rw [e] at e9 <;> omega
  · rw [K1 _ (by decide) (by decide)]; exact z0 _ (by decide)
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), e8, k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]


def checksB : List (Prog isa) := [inverseChoice, VG.Impl.Rsa.X86.KeyRt.eqS lay sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  VG.Impl.Rsa.X86.KeyRt.copy lay aDQ aD, VG.Impl.Rsa.X86.KeyRt.copy lay aDD aP, .block (VG.Impl.Rsa.X86.KeyRt.clrLow lay aDD)]

/-- The mask of the checks, from the quotient `X₁` and remainder `X₂` of `n / p` and the gcd `V`. -/
abbrev maskOf := VG.Proof.Rsa.CrtValues.maskOf

def InverseResult (g : Geometry) (len : Nat) (X₁ X₂ : Nat) (m : Mem) : Prop :=
  ∃ V, slot m g.base sMask = (if maskOf g.P g.Q X₁ X₂ V then 1 else 0) ∧
    (1 < g.M → V = Nat.gcd g.Q g.M ∧
      (g.M : Int) ∣ (num m g.base (kw len) 3 : Int) * g.Q - V ∧ num m g.base (kw len) 3 < g.M)

/-- Before the division of `d` by `p - 1`. -/
structure StD (g : Geometry) (len : Nat) (X₁ X₂ : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  dq : num s.mem g.base (kw len) aDQ = g.D
  dd : num s.mem g.base (kw len) aDD = 2 * (g.P / 2)
  mask : InverseResult g len X₁ X₂ s.mem

theorem checksB_ok {g : Geometry} {len : Nat} {s : State} {X₁ X₂ : Nat} (h : StI g len X₁ X₂ s) {args : Nat → BitVec 32}
    (gate : InvGate args g.base g.size g.P g.Q s) :
    WP isa (seqs (checksB)) s fun t => StD g len X₁ X₂ t ∧
      Keep g.base (kw len) (invArrs ++ [aDQ, aDD]) (invSlots ++ [sT, sE3, sMask]) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have hw := h.ws
  have fit := fun j (hj : j < nArr) => hw.ws.fit64 (j := j) hj
  unfold checksB
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have input : InvInput args g.base g.size len g.P g.Q s :=
    ⟨h.ws,gate,h.u,h.m,h.nm,h.zero,by simp only [bank]; rw [h.u,h.v,h.x₁,h.x₂]; rfl⟩
  refine WP.mono (inverseDispatch_ok input) fun t1 ⟨h1,k1,r1,inv⟩ => ?_
  have I : 1<g.M → num t1.mem g.base (kw len) 1=Nat.gcd g.Q g.M ∧
      (g.M : Int)∣(num t1.mem g.base (kw len) 3 : Int)*g.Q-num t1.mem g.base (kw len) 1 ∧
      num t1.mem g.base (kw len) 3<g.M := inv
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h1 (d := sE3) (a := 1) (b := aOne) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have one1 : num t1.mem g.base (kw len) aOne = 1 := by
    rw [k1.num (by decide) (by decide) (fit _ (by decide)), h.one]
  rw [one1] at e2
  have sl : ∀ d, d + 4 ≤ hdr → d % 4 = 0 → d ∉ [sT, sE3, sOdd, sB, sC] →
      slot t2.mem g.base d = slot s.mem g.base d := fun d hd h4 hn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp only [sT, sE3, sOdd, sB, sC, hdr] at hn hd
    rw [k2.slot (by simp only [hdr]; omega_arith) (by simp only [sT, sE3]; simp; omega_arith),
      k1.slot (by simp only [hdr]; omega_arith) (by simp only [invSlots, sOdd, sB, sC]; simp; omega_arith)]
  rw [wp_seqs_cons (List.cons_ne_nil _ _), List.append_assoc]
  refine WP.block_append ?_
  refine WP.mono (andS_ok h2 (d := sMask) (a := sPodd) (b := sE1) (by decide) (by decide) (by decide)
    (by rw [sl _ (by decide) (by decide) (by decide), h.podd]; omega_arith) (by rw [sl _ (by decide) (by decide) (by decide), h.e1]; split <;> omega_arith)
    ) fun t3a ⟨h3a, k3a, m3a, r3a⟩ => ?_
  refine WP.block_append ?_
  refine WP.mono (andS_ok h3a (d := sMask) (a := sMask) (b := sE2) (by decide) (by decide) (by decide)
    (by rw [m3a]; split <;> omega_arith) (by rw [k3a.slot (by decide) (by decide), sl _ (by decide) (by decide) (by decide), h.e2]; split <;> omega_arith)
    ) fun t3b ⟨h3b, k3b, m3b, r3b⟩ => ?_
  refine WP.mono (andS_ok h3b (d := sMask) (a := sMask) (b := sE3) (by decide) (by decide) (by decide)
    (by rw [m3b]; split <;> omega_arith)
    (by rw [k3b.slot (by decide) (by decide), k3a.slot (by decide) (by decide), e2]; split <;> omega_arith)
    ) fun t3 ⟨h3, k3, m3, r3⟩ => ?_
  have K3 : Keep g.base (kw len) [] [sMask] t2.mem t3.mem := k3a.trans (k3b.trans k3)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (o := aDQ) (a := aD) (by decide) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (o := aDD) (a := aP) (by decide) (by decide) (by decide))
    fun t5 ⟨h5, k5, e5, r5, top5⟩ => ?_
  refine WP.mono (clrLow_ok h5 (by decide)) fun t ⟨h6, k6, e6, r6, top6⟩ => ?_
  -- The count, through every step.
  have K : Keep g.base (kw len) (invArrs ++ [aDQ, aDD]) (invSlots ++ [sT, sE3, sMask]) s.mem t.mem :=
    k1.mono.trans (k2.mono.trans (K3.mono.trans (k4.mono.trans (k5.mono.trans k6.mono))))
  have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
    (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3a.mono (by decide)).trans ((r3b.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans (r6.mono (by decide))))))))
  have tr : ∀ j, j < nArr → j ∉ invArrs ++ [aDQ, aDD] →
      num t.mem g.base (kw len) j = num s.mem g.base (kw len) j := fun j hj hn =>
    K.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj)
  have fDD := fit aDD (by decide)
  have hS : S (kw len) = 4 * ((kw len) + 2) := rfl
  refine ⟨?_, K, R⟩
  refine ⟨h6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tr _ (by decide) (by decide), h.q]
  · rw [tr _ (by decide) (by decide), h.d]
  · rw [top6, top5,
      k4.word (by omega_arith) (by decide) (by simp) fDD, K3.word (by omega_arith) (by simp) (by decide) fDD,
      k2.word (by omega_arith) (by decide) (by decide) fDD, k1.word (by omega_arith) (by decide) (by decide) fDD, h.ddTop]
  · rw [k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), e4, K3.num (by simp) (by decide) (fit _ (by decide)),
      k2.num (by decide) (by decide) (fit _ (by decide)), k1.num (by decide) (by decide) (fit _ (by decide)), h.d]
  · rw [e6, e5, k4.num (by decide) (by simp) (fit _ (by decide)),
      K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      k1.num (by decide) (by decide) (fit _ (by decide)), h.p]
  · have x3 : num t.mem g.base (kw len) 3 = num t1.mem g.base (kw len) 3 := by
      rw [k6.num (by decide) (by simp) (fit _ (by decide)),
        k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
        K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide))]
    refine ⟨num t1.mem g.base (kw len) 1, ?_, fun hM => by rw [x3]; exact I hM⟩
    rw [k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), m3, m3b, k3b.slot (e := sE3) (by decide) (by decide), m3a,
      k3a.slot (e := sE2) (by decide) (by decide), k3a.slot (e := sE3) (by decide) (by decide), e2,
      sl sPodd (by decide) (by decide) (by decide), sl sE1 (by decide) (by decide) (by decide),
      sl sE2 (by decide) (by decide) (by decide), h.podd, h.e1, h.e2]
    simp only [maskOf, VG.Proof.Rsa.CrtValues.maskOf]
    by_cases a : g.P % 2 = 1 <;> by_cases b : X₁ = g.Q <;> by_cases c : X₂ = 0 <;>
      by_cases d : num t1.mem g.base (kw len) 1 = 1 <;> simp [a, b, c, d]

end VG.Proof.Rsa.X86.CrtValuesRt
