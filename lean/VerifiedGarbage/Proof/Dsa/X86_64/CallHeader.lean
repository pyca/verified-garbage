module

public import VerifiedGarbage.Proof.Dsa.X86_64.Return
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.CrtMath
import Batteries.Logic

/-! # Frames for DSA arithmetic call arguments -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def callRanges (sp sl : Nat) : List (Nat × Nat) := [(8 * sp, 8), (8 * sl, 8)]

/-- Each pair of argument writes preserves the parent structure and saved
fields, and records the exact pointer and length handed to the child. -/
theorem operand_context {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : pWorkspace ≤ Z) (a : Operand) (ha : pointerFits a.pointer)
    {sp sl : Nat} (hsp0 : 16 ≤ sp) (hsp : sp < 32) (hsl0 : 16 ≤ sl) (hsl : sl < 32)
    (hne : sp ≠ sl) :
    WP isa (.block (Core.operand sp sl a)) s fun t =>
      Good t B Z w minv ∧
      word t.mem B (8 * sp) = pointerValue s.mem B a.pointer ∧
      word t.mem B (8 * sl) = word s.mem B a.length.offset ∧
      (∀ f : Field, word t.mem B f.offset = word s.mem B f.offset) ∧
      Frm B (callRanges sp sl) s.mem t.mem ∧ Keep [.rax] s t := by
  refine WP.mono (operand_ok hg.scr hg.rdi hZ a ha hsp hsl) fun t ⟨hmem, hk⟩ => ?_
  let first := s.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)
  have ho1 : Outside B (8 * sp) 8 s.mem first := writeW_outside _ _ _ (by omega)
  have ho2 : Outside B (8 * sl) 8 first t.mem := by
    rw [hmem]; exact writeW_outside _ _ _ (by omega)
  refine ⟨⟨hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, ?_⟩, ?_, ?_, ?_, ?_, hk⟩
  · rw [hmem]
    exact (hg.hdr.store hsp0 hsp _).store hsl0 hsl _
  · rw [hmem, hdrStore_hdr _ _ _ hsl hsp (Ne.symm hne), word_writeW_self]
  · rw [hmem, word_writeW_self]
  · intro f
    have hf := VG.Proof.Dsa.field_bounds f
    have hp : pWorkspace < 2 ^ 64 := by decide
    rw [ho2.word (Or.inr (by omega)) (by omega), ho1.word (Or.inr (by omega)) (by omega)]
  · exact (Frm.of_outside ho1 (by simp [callRanges])).trans
      (Frm.of_outside ho2 (by simp [callRanges]))

/-- Call-header writes leave every child workspace header intact. -/
theorem call_child {mem mem' : Mem} {B : Addr} {o wx sp sl : Nat} {minv : BitVec 64}
    (h : WsAt mem B o wx minv) (hf : Frm B (callRanges sp sl) mem mem')
    (hsp : sp < 32) (hsl : sl < 32) (ho : 256 ≤ o) (hbound : o + 136 ≤ 2 ^ 64) :
    WsAt mem' B o wx minv := by
  apply h.of_words
  intro i hi
  rw [word_off, word_off]
  apply hf.word_eq
  · intro r hr
    simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> right <;> omega
  · omega

/-- Arguments remain in the active arithmetic prefix, so sources in the
scratch suffix or caller buffers retain their values and permissions. -/
theorem call_source {s t : State} {B p : Addr} {Z sp sl : Nat} {bytes : List Byte}
    {rs : List Reg} (hf : Frm B (callRanges sp sl) s.mem t.mem) (hk : Keep rs s t)
    (hsp : sp < 32) (hsl : sl < 32) (hZ : 256 ≤ Z) (hs : Src s B Z p bytes) :
    Src t B Z p bytes := by
  apply hs.congrK _ hk
  apply InScr.of_frm hf
  intro r hr
  simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only <;> omega

/-- Saved-field equality is sufficient to resolve every operand identically. -/
theorem pointerValue_congr {mem mem' : Mem} {B : Addr}
    (hf : ∀ f : Field, word mem' B f.offset = word mem B f.offset) (p : Pointer) :
    pointerValue mem' B p = pointerValue mem B p := by
  cases p with
  | input f => exact hf f
  | «local» _ => rfl
  | signatureS => exact congrArg₂ (· + ·) (hf .signature) (hf .qLen)

/-- Argument writes preserve the selected child's full reusable modulus state. -/
theorem call_ready {mem mem' : Mem} {B : Addr} {o wx m sp sl : Nat} {minv : BitVec 64}
    (h : ChildReady mem B o wx m minv) (hf : Frm B (callRanges sp sl) mem mem')
    (hsp : sp < 32) (hsl : sl < 32) (ho : 256 ≤ o)
    (hbound : o + slot wx 8 ≤ 2 ^ 64) : ChildReady mem' B o wx m minv := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hword : ∀ d, 256 ≤ d → d + 8 ≤ 2 ^ 64 → word mem' B d = word mem B d := by
    intro d hd hd'
    apply hf.word_eq _ hd'
    intro r hr
    simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> right <;> omega
  have hN := slot_le (w := wx) (show aN < 8 by decide)
  have hNlo : 256 ≤ slot wx aN := by unfold slot hdrBytes; omega
  refine ⟨call_child h.header hf hsp hsl ho (by omega), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => by rw [word_off, word_off]; exact hword _ (by omega) (by omega))]
    exact h.modulus
  · rw [word_off, hword _ (by omega) (by omega), ← word_off]
    exact h.inverse

end VG.Proof.Dsa.X86_64
