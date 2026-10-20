module

public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Checks
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word

/-! # CRT parameter calculation at a run-time width: the divisions

`n / p` before the checks (`firstDiv_ok`), and `d mod (p - 1)` and
`d mod (q - 1)` after them (`divP_ok`, `divQ_ok`), on `RtWs`; `core_ok`
composes them with the checks.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr seqs andS)
open VG.Impl.Rsa.X86.KeyRt (Lay sCy sQb)
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr)
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot wp_seqs_cons wp_seqs_append bank invArrs invSlots)
open VG.Proof.Rsa.X86.KeyRt

structure Start (g : Geometry) (len : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  n : num s.mem g.base (kw len) aDQ = g.N
  p : num s.mem g.base (kw len) aP = g.P
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  zeros : ∀ j ∈ zeroC, num s.mem g.base (kw len) j = 0

theorem firstDiv_ok {g : Geometry} {len : Nat} {s : State} (h : Start g len s) :
    WP isa firstDiv s fun t => StC g len t ∧
      Keep g.base (kw len) [aDD, aDQ, aDR, aDT] [sPodd, sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  unfold VG.Impl.Rsa.X86.CrtValuesRt.firstDiv
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := aDD) (a := aP) (by decide) (by decide) (by decide)) fun u ⟨hu, ku, vu, ru, topu⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok hu (j := aP) (sl := sPodd) (by decide) (by decide)) fun v ⟨hv, kv, vv, rv⟩ => ?_
  have topv : w32 v.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0 := by
    rw [kv.word (by unfold S; omega) (by decide) (by decide) (fit _ (by decide)), topu, h.ddTop]
  refine WP.mono (div_ok hv (q := aDQ) (r := aDR) (d := aDD) (t := aDT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) topv) fun t ⟨ht, kt, rt, vt⟩ => ?_
  have K : Keep g.base (kw len) [aDD, aDQ, aDR, aDT] [sPodd, sCy, sQb] s.mem t.mem :=
    ku.mono.trans (kv.mono.trans (kt.mono (by decide) (by decide)))
  have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans (rt.mono (by decide)))
  have same (j : Nat) (hj : j < nArr) (notWritten : j ∉ [aDD, aDQ, aDR, aDT]) :
      num t.mem g.base (kw len) j = num s.mem g.base (kw len) j :=
    K.num (fun k hk e => notWritten (by subst e; exact hk)) (by decide) (fit j hj)
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, K, R⟩
  · rw [kt.slot (by decide) (by decide), vv, ku.num (by decide) (by decide) (fit _ (by decide)), h.p]
  · rw [same _ (by decide) (by decide), h.p]
  · rw [same _ (by decide) (by decide), h.q]
  · rw [same _ (by decide) (by decide), h.d]
  · rw [kt.word (by unfold S; omega) (by decide) (by decide) (fit _ (by decide)), topv]
  · have divisor : num v.mem g.base (kw len) aDD = g.P := by
      rw [kv.num (by decide) (by decide) (fit _ (by decide)), vu, h.p]
    have numerator : num v.mem g.base (kw len) aDQ = g.N := by
      rw [kv.num (by decide) (by decide) (fit _ (by decide)), ku.num (by decide) (by decide) (fit _ (by decide)), h.n]
    change 0 < g.P → num t.mem g.base (kw len) aDQ = g.N / g.P ∧ num t.mem g.base (kw len) aDR = g.N % g.P
    change 0 < num v.mem g.base (kw len) aDD →
      num t.mem g.base (kw len) aDQ = num v.mem g.base (kw len) aDQ / num v.mem g.base (kw len) aDD ∧
      num t.mem g.base (kw len) aDR = num v.mem g.base (kw len) aDQ % num v.mem g.base (kw len) aDD at vt
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

theorem InverseResult.frame {g : Geometry} {len : Nat} {X₁ X₂ : Nat} {m m' : Mem} {js ds : List Nat}
    (h : InverseResult g len X₁ X₂ m) (keep : Keep g.base (kw len) js ds m m')
    (hj : ∀ j ∈ js, j ≠ 3) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (mask : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) (fit : arr (kw len) 3 + S (kw len) ≤ 2 ^ 64) :
    InverseResult g len X₁ X₂ m' := by
  obtain ⟨v, hv, hi⟩ := h
  refine ⟨v, ?_, ?_⟩
  · rw [keep.slot (by decide) mask]; exact hv
  · rw [keep.num hj hd fit]; exact hi

structure StE (g : Geometry) (len : Nat) (X₁ X₂ : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  remP : 0 < 2 * (g.P / 2) → num s.mem g.base (kw len) aDR2 = g.D % (2 * (g.P / 2))
  mask : InverseResult g len X₁ X₂ s.mem

theorem divP_ok {g : Geometry} {len : Nat} {s : State} {X₁ X₂ : Nat} (h : StD g len X₁ X₂ s) :
    WP isa (div aDR2) s fun t => StE g len X₁ X₂ t ∧
      Keep g.base (kw len) [aDQ, aDR2, aDT] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  refine WP.mono (div_ok h.ws (q := aDQ) (r := aDR2) (d := aDD) (t := aDT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.ddTop) ?_
  rintro t ⟨ht, kt, rt, vt⟩
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_⟩, kt, rt.mono (by decide)⟩
  · rw [kt.num (by decide) (by decide) (fit _ (by decide)), h.q]
  · rw [kt.num (by decide) (by decide) (fit _ (by decide)), h.d]
  · rw [kt.word (by unfold S; omega) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  · intro pos
    have positive : 0 < num s.mem g.base (kw len) aDD := by rw [h.dd]; exact pos
    have rem := (vt positive).2
    change num t.mem g.base (kw len) aDR2 = num s.mem g.base (kw len) aDQ % num s.mem g.base (kw len) aDD at rem
    rw [h.dq, h.dd] at rem
    exact rem
  · exact h.mask.frame kt (by decide) (by decide) (by decide) (fit _ (by decide))

structure Computed (g : Geometry) (len : Nat) (X₁ X₂ : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  remP : 0 < 2 * (g.P / 2) → num s.mem g.base (kw len) aDR2 = g.D % (2 * (g.P / 2))
  remQ : 0 < 2 * (g.Q / 2) → num s.mem g.base (kw len) aDR3 = g.D % (2 * (g.Q / 2))
  mask : InverseResult g len X₁ X₂ s.mem

theorem divQ_ok {g : Geometry} {len : Nat} {s : State} {X₁ X₂ : Nat} (h : StE g len X₁ X₂ s) :
    WP isa divQ s fun t => Computed g len X₁ X₂ t ∧
      Keep g.base (kw len) [aDQ, aDD, aDR3, aDT] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  unfold VG.Impl.Rsa.X86.CrtValuesRt.divQ
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := aDQ) (a := aD) (by decide) (by decide) (by decide)) fun u ⟨hu, ku, vu, ru, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok hu (o := aDD) (a := aQ) (by decide) (by decide) (by decide)) fun v ⟨hv, kv, vv, rv, topv⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clrLow_ok hv (j := aDD) (by decide)) fun z ⟨hz, kz, vz, rz, topz⟩ => ?_
  have top : w32 z.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0 := by
    rw [topz, topv, ku.word (by unfold S; omega) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  refine WP.mono (div_ok hz (q := aDQ) (r := aDR3) (d := aDD) (t := aDT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) top) fun t ⟨ht, kt, rt, vt⟩ => ?_
  have K : Keep g.base (kw len) [aDQ, aDD, aDR3, aDT] [sCy, sQb] s.mem t.mem :=
    ku.mono.trans (kv.mono.trans (kz.mono.trans (kt.mono (by decide) (by decide))))
  have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans ((rz.mono (by decide)).trans (rt.mono (by decide))))
  refine ⟨⟨ht, ?_, ?_, h.mask.frame K (by decide) (by decide) (by decide) (fit _ (by decide))⟩, K, R⟩
  · rw [K.num (by decide) (by decide) (fit _ (by decide))]; exact h.remP
  · have divisor : num z.mem g.base (kw len) aDD = 2 * (g.Q / 2) := by
      rw [vz, vv, ku.num (by decide) (by decide) (fit _ (by decide)), h.q]
    have numerator : num z.mem g.base (kw len) aDQ = g.D := by
      rw [kz.num (by decide) (by decide) (fit _ (by decide)), kv.num (by decide) (by decide) (fit _ (by decide)), vu, h.d]
    intro pos
    have positive : 0 < num z.mem g.base (kw len) aDD := by rw [divisor]; exact pos
    have rem := (vt positive).2
    change num t.mem g.base (kw len) aDR3 = num z.mem g.base (kw len) aDQ % num z.mem g.base (kw len) aDD at rem
    rw [divisor, numerator] at rem
    exact rem

def coreArrays : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23]
def coreSlots : List Nat := [sOdd, sB, sC, sT, sPodd, sE1, sE2, sE3, sMask, sCy, sQb]

theorem core_ok {g : Geometry} {len : Nat} {s : State} (h : Start g len s) :
    WP isa core s fun t =>
      Keep g.base (kw len) coreArrays coreSlots s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      num t.mem g.base (kw len) aZero = 0 ∧
      ∃ X₁ X₂, (0 < g.P → X₁ = g.N / g.P ∧ X₂ = g.N % g.P) ∧ Computed g len X₁ X₂ t := by
  unfold VG.Impl.Rsa.X86.CrtValuesRt.core
  refine WP.seq (WP.mono (firstDiv_ok h) fun a ⟨ha, ka, ra⟩ => ?_)
  refine WP.seq ?_
  change WP isa (seqs (checksA ++ checksB)) a _
  rw [wp_seqs_append (by unfold checksA; exact List.cons_ne_nil _ _) (by unfold checksB; exact List.cons_ne_nil _ _)]
  refine WP.mono (checksA_ok ha) fun b ⟨hb, kb, rb⟩ => ?_
  refine WP.mono (checksB_ok hb) fun c ⟨hc, kc, rc⟩ => ?_
  refine WP.seq (WP.mono (divP_ok hc) fun d ⟨hd, kd, rd⟩ => ?_)
  refine WP.mono (divQ_ok hd) fun t ⟨ht, kt, rt⟩ => ?_
  have K : Keep g.base (kw len) coreArrays coreSlots s.mem t.mem :=
    (ka.mono (by decide) (by decide)).trans ((kb.mono (by decide) (by decide)).trans
      ((kc.mono (by decide) (by decide)).trans ((kd.mono (by decide) (by decide)).trans
        (kt.mono (by decide) (by decide)))))
  refine ⟨K, ra.trans ((rb.mono (by decide)).trans (rc.trans (rd.trans rt))), ?_, _, _, ha.division, ht⟩
  rw [K.num (by decide) (by decide) (h.ws.ws.fit64 (by decide))]
  exact h.zeros aZero (by decide)
end VG.Proof.Rsa.X86.CrtValuesRt
