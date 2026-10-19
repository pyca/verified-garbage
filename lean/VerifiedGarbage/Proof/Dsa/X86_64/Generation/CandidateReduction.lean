module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Rsa.Ranges

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate

/-! # Complete native p-candidate reduction, retaining the quotient -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64.Keys VG.Proof.Dsa.Generation VG.Proof.Rsa

theorem reduceCandidate_ok {s : State} {B : Addr} {Z w x q : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w 0) w = x)
    (hq : wv s.mem B (slot w 2) w = 2 * q) (hqpos : 0 < q) :
    WP isa Impl.Dsa.X86_64.Generation.reduceCandidate s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 5) w = x + 1 - x % (2 * q) ∧
      wv t.mem B (slot w 0) w = x / (2 * q) ∧
      Frm B [ar w 4, ar w 0, ar w 1, ar w 3, ar w 5] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := h.scr.nowrap
  have hr : ∀ j < 16, slot w j + 8 * w ≤ 2 ^ 64 := by
    intro j hj; have := h.sl hj; omega
  unfold Impl.Dsa.X86_64.Generation.reduceCandidate
  simp only [seqs]
  refine WP.seq (WP.mono (copyA_ok h (by decide : 4 < 16) (by decide : 0 < 16) (by decide))
    fun u ⟨hu, hou, ku⟩ => ?_)
  have fu : Frm B [ar w 4] s.mem u.mem :=
    Frm.of_outside (hou.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  have wu := h.congr fu (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot w 4 _) ku (by decide)
  have ux : wv u.mem B (slot w 0) w = x := by rw [fu.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega) (hr 0 (by decide))]; exact hx
  have uq : wv u.mem B (slot w 2) w = 2 * q := by rw [fu.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega) (hr 2 (by decide))]; exact hq
  refine WP.seq (WP.mono (candidateDivision_ok wu.scr wu.rdi wu.hw wu.hS
    (by have := wu.w1; omega) wu.w2 wu.hZ (iQ := 0) (iR := 1) (iD := 2) (iT := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ux uq hqpos) fun v ⟨_, fv, kv, vr, vq, _⟩ => ?_)
  have wv' := wu.congr fv (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) kv (by decide)
  have vx : wv v.mem B (slot w 4) w = x := by
    rw [fv.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega) (hr 4 (by decide)), hu, hx]
  refine WP.mono (reduceRemainder_ok wv' (by decide : 5 < 16) (by decide : 4 < 16)
    (by decide : 1 < 16) (by decide) (by decide) vx vr) fun t ⟨tp, hot, kt⟩ => ?_
  have ft : Frm B [ar w 5] v.mem t.mem :=
    Frm.of_outside (hot.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  have wt := wv'.congr ft (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kt (by decide)
  refine ⟨wt, tp, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [ft.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega) (hr 0 (by decide)), vq]
  · exact (fu.append (fv.append ft)).mono (by simp)

end VG.Proof.Dsa.X86_64.Generation
