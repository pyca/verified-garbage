module
public import VerifiedGarbage.Proof.Rsa.X86.CvDivN
public import VerifiedGarbage.Proof.Rsa.X86.CvFrames

import VerifiedGarbage.Proof.Rsa.X86.CvZero
import VerifiedGarbage.Proof.Rsa.X86.CvLoad
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.KeyWorkspace

/-! # Loading the modulus, factors, and exponent into initialized CRT arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

def arithmeticGeometry (g : CallGeometry) (m : Mem) : Geometry :=
  ⟨g.base, g.size, 2 * g.n, Spec.Rsa.os2ip (inputBytes g m 1), Spec.Rsa.os2ip (inputBytes g m 2),
    Spec.Rsa.os2ip (inputBytes g m 3), Spec.Rsa.os2ip (inputBytes g m 0)⟩

theorem loads_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa (loads g.n) s fun t => Inputs g t ∧ Start (arithmeticGeometry g s.mem) t ∧
      Outside g.base 16 (g.size - 16) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have header := h.ws.hdr_le
  have fits := h.ws.fits
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  unfold loads
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroArrays_ok h) fun z ⟨hz, oz, zeros, rz⟩ => ?_
  have Oz : Outside g.base 0 g.size s.mem z.mem := oz.mono (by omega) (by
    change hdr + nArr * (4 * (2 * g.n + 2)) ≤ g.size at fits
    unfold nArr at fits ⊢
    omega)
  have Bz : Outside g.base 16 (g.size - 16) s.mem z.mem := oz.mono (by unfold hdr; omega) (by
    change hdr + nArr * (4 * (2 * g.n + 2)) ≤ g.size at fits
    unfold nArr at fits ⊢
    unfold hdr at header; omega)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok hz 0 (j := aDQ) (by decide)) fun u ⟨hu, ku, vu, ru⟩ => ?_
  have Ou := hz.keepOutside ku (by decide) (by simp)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok hu 1 (j := aP) (by decide)) fun v ⟨hv, kv, vv, rv⟩ => ?_
  have Ov := hu.keepOutside kv (by decide) (by simp)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok hv 2 (j := aQ) (by decide)) fun x ⟨hx, kx, vx, rx⟩ => ?_
  have Ox := hv.keepOutside kx (by decide) (by simp)
  refine WP.mono (load_ok hx 3 (j := aD) (by decide)) fun t ⟨ht, kt, vt, rt⟩ => ?_
  have K : Keep g.base (2 * g.n) [aDQ, aP, aQ, aD] [] z.mem t.mem :=
    ku.mono.trans (kv.mono.trans (kx.mono.trans kt.mono))
  have R : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    (rz.mono (by decide)).trans (ru.trans (rv.trans (rx.trans rt)))
  have body := hz.keepBody K (by decide) (by simp)
  refine ⟨ht, ?_, Bz.trans body, R⟩
  refine ⟨ht.ws, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change num t.mem g.base (2 * g.n) aDQ = Spec.Rsa.os2ip (inputBytes g s.mem 0)
    rw [kt.num (by decide) (by simp) (fit _ (by decide)), kx.num (by decide) (by simp) (fit _ (by decide)),
      kv.num (by decide) (by simp) (fit _ (by decide)), vu]
    change Spec.Rsa.os2ip (inputBytes g z.mem 0) = _
    rw [h.inputFrame Oz]
  · change num t.mem g.base (2 * g.n) aP = Spec.Rsa.os2ip (inputBytes g s.mem 1)
    rw [kt.num (by decide) (by simp) (fit _ (by decide)), kx.num (by decide) (by simp) (fit _ (by decide)), vv]
    change Spec.Rsa.os2ip (inputBytes g u.mem 1) = _
    rw [h.inputFrame (Oz.trans Ou)]
  · change num t.mem g.base (2 * g.n) aQ = Spec.Rsa.os2ip (inputBytes g s.mem 2)
    rw [kt.num (by decide) (by simp) (fit _ (by decide)), vx]
    change Spec.Rsa.os2ip (inputBytes g v.mem 2) = _
    rw [h.inputFrame ((Oz.trans Ou).trans Ov)]
  · change num t.mem g.base (2 * g.n) aD = Spec.Rsa.os2ip (inputBytes g s.mem 3)
    rw [vt]
    change Spec.Rsa.os2ip (inputBytes g x.mem 3) = _
    rw [h.inputFrame (((Oz.trans Ou).trans Ov).trans Ox)]
  · change w32 t.mem g.base (arr (2 * g.n) aDD + 4 * (2 * g.n)) = 0
    rw [K.word (by unfold S; omega) (by decide) (by simp) (fit _ (by decide))]
    have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zeros aDD (by decide))
      (a := 2 * g.n) (c := 1) (by omega)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using part
  · intro j hj
    have jfit : j < nArr := by
      simp only [zeroC, List.mem_cons, List.not_mem_nil, or_false] at hj
      unfold nArr; omega
    have separate : ∀ k ∈ [aDQ, aP, aQ, aD], k ≠ j := by
      simp only [zeroC, List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [aDQ, aP, aQ, aD, List.mem_cons, List.not_mem_nil, or_false]
      omega
    change num t.mem g.base (2 * g.n) j = 0
    rw [K.num separate (by simp) (fit _ jfit)]
    have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zeros j jfit) (a := 0) (c := 2 * g.n) (by omega)
    simpa only [Nat.mul_zero, Nat.add_zero] using part
end VG.Proof.Rsa.X86.CrtValues
