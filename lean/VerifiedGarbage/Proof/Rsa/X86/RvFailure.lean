module

public import VerifiedGarbage.Proof.Rsa.X86.RvStores

import VerifiedGarbage.Proof.Rsa.X86.CvClear
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.CvInputs
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
/-! # Invalid moduli clear both recovery outputs while preserving inputs and the ABI save area -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/CvStores.lean`, which only this module imported.
section

/-! # Release all three CRT values under their common acceptance mask -/

section
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

end VG.Proof.Rsa.X86.CrtValues
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.CrtValues (clear)
open VG.Proof.Rsa.X86.CrtValues (clear_ok)

theorem outputFrame_body {g : CallGeometry} {m m' : Mem} (i : Fin 2)
    (f : Frame [g.buffer (2 * i.val)] m m') : Frame (bodyWrites g) m m' := by
  apply f.mono
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> simp [bodyWrites, e]

theorem clear_input_ok {g : CallGeometry} {s : State} (h : Inputs g s) (i : Fin 2) :
    WP isa (clear (2 * i.val)) s fun t => Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer (2 * i.val)).base (g.buffer (2 * i.val)).len =
        List.replicate (g.buffer (2 * i.val)).len 0 ∧
      t.gpr .eax = 0 ∧ Frame [g.buffer (2 * i.val)] s.mem t.mem ∧
      Keeps [.esi, .ecx, .eax] s t := by
  have arg := h.arguments (2 * i.val) (by omega)
  have len := h.arguments (2 * i.val + 1) (by omega)
  have bound : (g.buffer (2 * i.val)).len < 2 ^ 32 := by
    have := h.outputBound i; have := h.upper; omega
  refine WP.mono (clear_ok (2 * i.val) (h.outputPositive i) bound (h.outputFit i)
    arg.readSrc (by simpa only [CallGeometry.buffer, BitVec.ofNat_toNat, BitVec.setWidth_eq] using len.readSrc)
    (h.outputWrite i)) fun t ⟨v, z, o, k⟩ => ?_
  have f : Frame [g.buffer (2 * i.val)] s.mem t.mem := by
    simpa only [CallGeometry.buffer, byteAddr, off, BitVec.add_zero] using outside_frame o (by omega)
  refine ⟨h.after k (by decide) (by decide) ?_, v, z, f, k⟩
  apply f.mono
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> simp [CallGeometry.writes, e]

theorem clear_other {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s)
    (i k : Fin 2) (ne : k ≠ i) (f : Frame [g.buffer (2 * i.val)] m m') :
    Spec.Rsa.bytesAt m' (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len =
      Spec.Rsa.bytesAt m (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame f (by have := h.outputBound k; have := h.upper; omega)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.outputSeparate k i ne

theorem failure_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa failure s fun t => Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = List.replicate (g.buffer 0).len 0 ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = List.replicate (g.buffer 2).len 0 ∧
      t.gpr .eax = 0 ∧ Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  unfold VG.Impl.Rsa.X86.Recover.failure
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clear_input_ok h 0) fun u ⟨hu, vu, _, fu, ku⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clear_input_ok hu 1) fun v ⟨hv, vv, _, fv, kv⟩ => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  refine ⟨hv.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _),
    ?_, ?_, T.gpr, ?_, ku.trans (kv.trans (T.keeps.mono (by decide)))⟩
  · rw [T.mem]
    exact (clear_other hu 1 0 (by decide) fv).trans vu
  · rw [T.mem]
    exact vv
  · rw [T.mem]
    exact (outputFrame_body 0 fu).trans (outputFrame_body 1 fv)

end VG.Proof.Rsa.X86.Recover
