module

public import VerifiedGarbage.Proof.Rsa.X86.RvStore
public import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! # Release both recovered factors under their common acceptance mask -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def bodyWrites (g : CallGeometry) : List Region :=
  [⟨off g.B 16, g.Z - 16⟩, g.buffer 0, g.buffer 2]

theorem storeFrame_body {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 2)
    {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.B (arr g.toGeo.w j), S g.toGeo.w⟩, g.buffer (2 * i.val)] m m') :
    Frame (bodyWrites g) m m' := by
  apply f.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨⟨off g.B 16, g.Z - 16⟩, by simp [bodyWrites], Offset.sub g.B ?_ ?_⟩
    · have : hdr ≤ arr g.toGeo.w j := Nat.le_add_right _ _
      unfold hdr at this; omega
    · have := h.ws.arr_fit hj
      have := h.ws.hdr_le
      unfold hdr at this; omega
  · refine ⟨g.buffer (2 * i.val), ?_, fun _ hx => hx⟩
    have cases : i.val = 0 ∨ i.val = 1 := by omega
    rcases cases with e | e <;> simp [bodyWrites, e]

theorem output_preserved {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i k : Fin 2)
    (ne : k ≠ i) {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.B (arr g.toGeo.w j), S g.toGeo.w⟩, g.buffer (2 * i.val)] m m') :
    Spec.Rsa.bytesAt m' (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len =
      Spec.Rsa.bytesAt m (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame f (by have := h.outputBound k; have := h.upper; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.outputScratch k).sub_right (Offset.sub_base g.B (h.ws.arr_fit hj))
  · exact h.outputSeparate k i ne

def resultBytes (g : CallGeometry) (m : Mem) (accept : Bool) (i : Fin 2) (j : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then num m g.B g.toGeo.w j else 0) %
    2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len

theorem stores_ok {g : CallGeometry} {s : State} (h : Inputs g s)
    (zero : num s.mem g.B g.toGeo.w aZero = 0) (accept : Bool)
    (mask : slot s.mem g.B sMask = if accept then 1 else 0) :
    WP isa (stores g.n) s fun t => Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = resultBytes g s.mem accept 0 5 ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = resultBytes g s.mem accept 1 6 ∧
      t.gpr .eax = BitVec.ofNat 32 accept.toNat ∧ Frame (bodyWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok h 0 (j := 5) (by decide) zero accept mask) fun u ⟨hu, vu, fu, huHeader, huOther, ru⟩ => ?_
  have zeroU : num u.mem g.B g.toGeo.w aZero = 0 := by rw [huOther _ (by decide) (by decide), zero]
  have maskU : slot u.mem g.B sMask = if accept then 1 else 0 := by rw [huHeader _ (by decide), mask]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok hu 1 (j := 6) (by decide) zeroU accept maskU) fun v ⟨hv, vv, fv, hvHeader, _, rv⟩ => ?_
  have maskV : slot v.mem g.B sMask = if accept then 1 else 0 := by rw [hvHeader _ (by decide), maskU]
  refine wp_movS (readSrc_sc hv.ws.workspace (by have := hv.ws.hdr_le; unfold sMask hdr at *; omega)) fun t T _ => WP.block_nil ?_
  have frame : Frame (bodyWrites g) s.mem t.mem := by
    rw [T.mem]
    exact (storeFrame_body h 0 (by decide) fu).trans (storeFrame_body hu 1 (by decide) fv)
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    ru.trans (rv.trans (T.keeps.mono (by decide)))
  refine ⟨hv.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _), ?_, ?_, ?_, frame, all⟩
  · rw [T.mem]
    exact (output_preserved hu 1 0 (by decide) (by decide) fv).trans vu
  · rw [T.mem]
    rw [huOther _ (by decide) (by decide)] at vv
    exact vv
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr]
    change slot v.mem g.B sMask = _
    rw [maskV]; cases accept <;> rfl

end VG.Proof.Rsa.X86.Recover
