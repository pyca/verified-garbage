module

public import VerifiedGarbage.Proof.Rsa.X86.CvChecksB
import VerifiedGarbage.Proof.Rsa.X86.CvDivN
import VerifiedGarbage.Proof.Rsa.X86.KeyDiv
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
import VerifiedGarbage.Proof.Rsa.X86.KeyWord
import VerifiedGarbage.Proof.Rsa.X86.InvParts

/-! # Reducing the private exponent modulo each factor minus one -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

theorem InverseResult.frame {g : Geometry} {X₁ X₂ : Nat} {m m' : Mem} {js ds : List Nat}
    (h : InverseResult g X₁ X₂ m) (keep : Keep g.base g.w js ds m m')
    (hj : ∀ j ∈ js, j ≠ 3) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (mask : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) (fit : arr g.w 3 + S g.w ≤ 2 ^ 64) :
    InverseResult g X₁ X₂ m' := by
  obtain ⟨v, hv, hi⟩ := h
  refine ⟨v, ?_, ?_⟩
  · rw [keep.slot (by decide) mask]; exact hv
  · rw [keep.num hj hd fit]; exact hi

structure StE (g : Geometry) (X₁ X₂ : Nat) (s : State) : Prop where
  ws : Ws s g.base g.size g.w nArr
  q : num s.mem g.base g.w aQ = g.Q
  d : num s.mem g.base g.w aD = g.D
  ddTop : w32 s.mem g.base (arr g.w aDD + 4 * g.w) = 0
  remP : 0 < 2 * (g.P / 2) → num s.mem g.base g.w aDR2 = g.D % (2 * (g.P / 2))
  mask : InverseResult g X₁ X₂ s.mem

theorem divP_ok {g : Geometry} {s : State} {X₁ X₂ : Nat} (h : StD g X₁ X₂ s) :
    WP isa (div g.w aDR2) s fun t => StE g X₁ X₂ t ∧
      Keep g.base g.w [aDQ, aDR2, aDT] [] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  refine WP.mono (div_ok (ids := divIds aDR2) h.ws (by decide) (by decide) h.ddTop) ?_
  rintro t ⟨ht, kt, rt, vt⟩
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_⟩, kt, rt⟩
  · rw [kt.num (by decide) (by simp) (fit _ (by decide)), h.q]
  · rw [kt.num (by decide) (by simp) (fit _ (by decide)), h.d]
  · rw [kt.word (by unfold S; omega) (by decide) (by simp) (fit _ (by decide)), h.ddTop]
  · intro pos
    have positive : 0 < num s.mem g.base g.w (divIds aDR2 2) := by change 0 < num s.mem g.base g.w aDD; rw [h.dd]; exact pos
    have rem := (vt positive).2
    change num t.mem g.base g.w aDR2 = num s.mem g.base g.w aDQ % num s.mem g.base g.w aDD at rem
    rw [h.dq, h.dd] at rem
    exact rem
  · exact h.mask.frame kt (by decide) (by simp) (by simp) (fit _ (by decide))

def divQ (w : Nat) : Prog isa := seqs [
  copy w aDQ aD, copy w aDD aQ, .block (clrLow w aDD), div w aDR3]

structure Computed (g : Geometry) (X₁ X₂ : Nat) (s : State) : Prop where
  ws : Ws s g.base g.size g.w nArr
  remP : 0 < 2 * (g.P / 2) → num s.mem g.base g.w aDR2 = g.D % (2 * (g.P / 2))
  remQ : 0 < 2 * (g.Q / 2) → num s.mem g.base g.w aDR3 = g.D % (2 * (g.Q / 2))
  mask : InverseResult g X₁ X₂ s.mem

theorem divQ_ok {g : Geometry} {s : State} {X₁ X₂ : Nat} (h : StE g X₁ X₂ s) :
    WP isa (divQ g.w) s fun t => Computed g X₁ X₂ t ∧
      Keep g.base g.w [aDQ, aDD, aDR3, aDT] [] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  unfold divQ
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := aDQ) (a := aD) (by decide) (by decide)) fun u ⟨hu, ku, vu, ru, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok hu (o := aDD) (a := aQ) (by decide) (by decide)) fun v ⟨hv, kv, vv, rv, topv⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clrLow_ok hv (j := aDD) (by decide)) fun z ⟨hz, kz, vz, rz, topz⟩ => ?_
  have top : w32 z.mem g.base (arr g.w aDD + 4 * g.w) = 0 := by
    rw [topz, topv, ku.word (by unfold S; omega) (by decide) (by simp) (fit _ (by decide)), h.ddTop]
  refine WP.mono (div_ok (ids := divIds aDR3) hz (by decide) (by decide) top) fun t ⟨ht, kt, rt, vt⟩ => ?_
  have K : Keep g.base g.w [aDQ, aDD, aDR3, aDT] [] s.mem t.mem :=
    ku.mono.trans (kv.mono.trans (kz.mono.trans (kt.mono (by decide) (by simp))))
  have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans ((rz.mono (by decide)).trans rt))
  refine ⟨⟨ht, ?_, ?_, h.mask.frame K (by decide) (by simp) (by simp) (fit _ (by decide))⟩, K, R⟩
  · rw [K.num (by decide) (by simp) (fit _ (by decide))]; exact h.remP
  · have divisor : num z.mem g.base g.w aDD = 2 * (g.Q / 2) := by
      rw [vz, vv, ku.num (by decide) (by simp) (fit _ (by decide)), h.q]
    have numerator : num z.mem g.base g.w aDQ = g.D := by
      rw [kz.num (by decide) (by simp) (fit _ (by decide)), kv.num (by decide) (by simp) (fit _ (by decide)), vu, h.d]
    intro pos
    have positive : 0 < num z.mem g.base g.w (divIds aDR3 2) := by
      change 0 < num z.mem g.base g.w aDD; rw [divisor]; exact pos
    have rem := (vt positive).2
    change num t.mem g.base g.w aDR3 = num z.mem g.base g.w aDQ % num z.mem g.base g.w aDD at rem
    rw [divisor, numerator] at rem
    exact rem
end VG.Proof.Rsa.X86.CrtValues
