module

public import VerifiedGarbage.Proof.Rsa.X86.CvChecksA
public import VerifiedGarbage.Proof.Rsa.X86.KeyDiv

/-! # Dividing the public modulus by the first private factor -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

def divIds (r : Nat) : Fin 4 → Nat := fun i => if i = 0 then aDQ else if i = 1 then r else if i = 2 then aDD else aDT

def firstDiv (w : Nat) : Prog isa := seqs [
  copy w aDD aP, .block (bitOf w sPodd aP), div w aDR]

structure Start (g : Geometry) (s : State) : Prop where
  ws : Ws s g.base g.size g.w nArr
  n : num s.mem g.base g.w aDQ = g.N
  p : num s.mem g.base g.w aP = g.P
  q : num s.mem g.base g.w aQ = g.Q
  d : num s.mem g.base g.w aD = g.D
  ddTop : w32 s.mem g.base (arr g.w aDD + 4 * g.w) = 0
  zeros : ∀ j ∈ zeroC, num s.mem g.base g.w j = 0

theorem firstDiv_ok {g : Geometry} {s : State} (h : Start g s) :
    WP isa (firstDiv g.w) s fun t => StC g t ∧
      Keep g.base g.w [aDD, aDQ, aDR, aDT] [sPodd] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  unfold firstDiv
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := aDD) (a := aP) (by decide) (by decide)) fun u ⟨hu, ku, vu, ru, topu⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok hu (j := aP) (sl := sPodd) (by decide) (by decide)) fun v ⟨hv, kv, vv, rv⟩ => ?_
  have topv : w32 v.mem g.base (arr g.w aDD + 4 * g.w) = 0 := by
    rw [kv.word (by unfold S; omega) (by simp) (by decide) (fit _ (by decide)), topu, h.ddTop]
  refine WP.mono (div_ok (ids := divIds aDR) hv (by decide) (by decide) topv) fun t ⟨ht, kt, rt, vt⟩ => ?_
  have K : Keep g.base g.w [aDD, aDQ, aDR, aDT] [sPodd] s.mem t.mem :=
    ku.mono.trans (kv.mono.trans (kt.mono (by decide) (by simp)))
  have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans rt)
  have same (j : Nat) (hj : j < nArr) (notWritten : j ∉ [aDD, aDQ, aDR, aDT]) :
      num t.mem g.base g.w j = num s.mem g.base g.w j :=
    K.num (fun k hk e => notWritten (by subst e; exact hk)) (by decide) (fit j hj)
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, K, R⟩
  · rw [kt.slot (by decide) (by simp), vv, ku.num (by decide) (by simp) (fit _ (by decide)), h.p]
  · rw [same _ (by decide) (by decide), h.p]
  · rw [same _ (by decide) (by decide), h.q]
  · rw [same _ (by decide) (by decide), h.d]
  · rw [kt.word (by unfold S; omega) (by decide) (by simp) (fit _ (by decide)), topv]
  · have divisor : num v.mem g.base g.w aDD = g.P := by
      rw [kv.num (by simp) (by decide) (fit _ (by decide)), vu, h.p]
    have numerator : num v.mem g.base g.w aDQ = g.N := by
      rw [kv.num (by simp) (by decide) (fit _ (by decide)), ku.num (by decide) (by simp) (fit _ (by decide)), h.n]
    change 0 < g.P → num t.mem g.base g.w aDQ = g.N / g.P ∧ num t.mem g.base g.w aDR = g.N % g.P
    change 0 < num v.mem g.base g.w aDD →
      num t.mem g.base g.w aDQ = num v.mem g.base g.w aDQ / num v.mem g.base g.w aDD ∧
      num t.mem g.base g.w aDR = num v.mem g.base g.w aDQ % num v.mem g.base g.w aDD at vt
    rw [divisor, numerator] at vt
    exact vt
  · intro j hj
    have fits : j < nArr := by
      simp only [zeroC, List.mem_cons, List.not_mem_nil, or_false] at hj
      unfold nArr; omega
    have notWritten : j ∉ [aDD, aDQ, aDR, aDT] := by
      simp only [zeroC, List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [aDD, aDQ, aDR, aDT, List.mem_cons, List.not_mem_nil, or_false]
      omega
    rw [same j fits notWritten]
    exact h.zeros j hj
end VG.Proof.Rsa.X86.CrtValues
