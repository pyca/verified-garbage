module
public import VerifiedGarbage.Proof.Rsa.X86.CvInputs
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Rsa.X86.CvStore
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! # Release all three CRT values under their common acceptance mask -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

theorem storeFrame_body {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 3)
    {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.base (arr (2 * g.n) j), S (2 * g.n)⟩, g.buffer (2 * i.val)] m m') :
    Frame (bodyWrites g) m m' := by
  apply f.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨⟨off g.base 16, g.size - 16⟩, by simp [bodyWrites], Offset.sub g.base ?_ ?_⟩
    · have : hdr ≤ arr (2 * g.n) j := Nat.le_add_right _ _
      unfold hdr at this; omega
    · have := h.ws.arr_fit hj
      have := h.ws.hdr_le
      unfold hdr at this; omega
  · refine ⟨g.buffer (2 * i.val), ?_, fun _ hx => hx⟩
    have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases cases with e | e | e <;> simp [bodyWrites, e]

theorem output_preserved {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i k : Fin 3)
    (ne : k ≠ i) {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.base (arr (2 * g.n) j), S (2 * g.n)⟩, g.buffer (2 * i.val)] m m') :
    Spec.Rsa.bytesAt m' (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len =
      Spec.Rsa.bytesAt m (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame f (by have := h.outputBound k; have := h.upper; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.outputScratch k).sub_right (Offset.sub_base g.base (h.ws.arr_fit hj))
  · exact h.outputSeparate k i ne

def resultBytes (g : CallGeometry) (m : Mem) (accept : Bool) (i : Fin 3) (j : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then num m g.base (2 * g.n) j else 0) %
    2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len

theorem stores_ok {g : CallGeometry} {s : State} (h : Inputs g s)
    (zero : num s.mem g.base (2 * g.n) aZero = 0) (accept : Bool)
    (mask : slot s.mem g.base sMask = if accept then 1 else 0) :
    WP isa (stores g.n) s fun t => Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = resultBytes g s.mem accept 0 aDR2 ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = resultBytes g s.mem accept 1 aDR3 ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 4).base (g.buffer 4).len = resultBytes g s.mem accept 2 3 ∧
      t.gpr .eax = BitVec.ofNat 32 accept.toNat ∧ Frame (bodyWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok h 0 (j := aDR2) (by decide) zero accept mask) fun u ⟨hu, vu, fu, huHeader, huOther, ru⟩ => ?_
  have zeroU : num u.mem g.base (2 * g.n) aZero = 0 := by rw [huOther _ (by decide) (by decide), zero]
  have maskU : slot u.mem g.base sMask = if accept then 1 else 0 := by rw [huHeader _ (by decide), mask]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok hu 1 (j := aDR3) (by decide) zeroU accept maskU) fun v ⟨hv, vv, fv, hvHeader, hvOther, rv⟩ => ?_
  have zeroV : num v.mem g.base (2 * g.n) aZero = 0 := by rw [hvOther _ (by decide) (by decide), zeroU]
  have maskV : slot v.mem g.base sMask = if accept then 1 else 0 := by rw [hvHeader _ (by decide), maskU]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok hv 2 (j := 3) (by decide) zeroV accept maskV) fun x ⟨hx, vx, fx, hxHeader, hxOther, rx⟩ => ?_
  have maskX : slot x.mem g.base sMask = if accept then 1 else 0 := by rw [hxHeader _ (by decide), maskV]
  refine wp_movS (readSrc_sc hx.ws.workspace (by have := hx.ws.hdr_le; unfold sMask hdr at *; omega)) fun t T _ => WP.block_nil ?_
  have frame : Frame (bodyWrites g) s.mem t.mem := by
    rw [T.mem]
    exact (storeFrame_body h 0 (by decide) fu).trans
      ((storeFrame_body hu 1 (by decide) fv).trans (storeFrame_body hv 2 (by decide) fx))
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    ru.trans (rv.trans (rx.trans (T.keeps.mono (by decide))))
  refine ⟨hx.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _), ?_, ?_, ?_, ?_, frame, all⟩
  · rw [T.mem]
    exact (output_preserved hv 2 0 (by decide) (by decide) fx).trans
      ((output_preserved hu 1 0 (by decide) (by decide) fv).trans vu)
  · rw [T.mem]
    refine (output_preserved hv 2 1 (by decide) (by decide) fx).trans ?_
    rw [huOther _ (by decide) (by decide)] at vv
    exact vv
  · rw [T.mem]
    rw [hvOther _ (by decide) (by decide), huOther _ (by decide) (by decide)] at vx
    exact vx
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr]
    change slot x.mem g.base sMask = _
    rw [maskX]; cases accept <;> rfl
end VG.Proof.Rsa.X86.CrtValues
