module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Public counts and array pointers for the shared key code -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Rsa.X86.KeyRt (RtWs kw LenSrc)
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem offset_array (n : Nat) (w : Width) (j : Nat) :
    Loc.offset n (.array w j) = VG.Proof.Rsa.X86.Keys.arr (w.words n) j := rfl

theorem kw_words {n : Nat} (h : n % 4 = 0) (w : Width) :
    kw (w.len n) = w.words n := by
  cases w
  · exact kw_full h
  · exact kw_prime h
  · simp only [Width.len, Width.words, kw, Spec.Rsa.modulusWords]
  · simp only [Width.len, Width.words, kw, Spec.Rsa.modulusWords]

theorem Ws.runtime {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N)
    {w : Width} (hw : w ≠ .correction) : RtWs w.lay s B Z (w.len n) N := by
  cases w
  · exact h.full
  · exact h.prime
  · exact h.exponent
  · exact False.elim (hw rfl)

theorem Ws.afterBank {s t : State} {B : Addr} {Z n N : Nat} {w : Width} {rs : List Reg}
    {js ds : List Nat} (h : Ws s B Z n N) (hw : w ≠ .correction) (K : Keeps rs s t)
    (O : VG.Proof.Rsa.X86.Keys.Keep B (w.words n) js ds s.mem t.mem)
    (hj : ∀ j ∈ js, j < N) (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Ws t B Z n N := by
  have O' : VG.Proof.Rsa.X86.Keys.Keep B (kw (w.len n)) js ds s.mem t.mem := by
    rw [kw_words h.width]; exact O
  exact h.keep K (VG.Proof.Rsa.X86.KeyRt.keep_outside (h.runtime hw).ws O' hj hd) edi esp

theorem Ws.bytes_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N)
    (w : Width) (r : Reg) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem →
      (t.gpr r).toNat = 4 * w.words n → WP isa (.block is) t Q) :
    WP isa (.block (bytes w r ++ is)) s Q := by
  by_cases hw : w = .correction
  · subst w
    refine wp_movS rfl fun t T _ => ?_
    exact k t T.keeps T.mem (by rw [T.gpr]; rfl)
  · have H := h.runtime hw
    have code : bytes w r = VG.Impl.Rsa.X86.KeyRt.bytesB w.lay r := by
      cases w <;> simp_all [bytes]
    rw [code]
    exact VG.Proof.Rsa.X86.KeyRt.bytesB_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc H) H.lenLe
      fun t K m e => k t K m (by simpa only [kw_words h.width] using e)

theorem Ws.ptr_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N)
    (l : Loc) {r t : Reg} (hrt : r ≠ t) (hte : t ≠ .edi)
    (fit : l.offset n < 2 ^ 32) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem →
      PtrAt u B r (l.offset n) → WP isa (.block is) u Q) :
    WP isa (.block (ptr l r t ++ is)) s Q := by
  have edi : (s.gpr .edi).toNat = B.toNat := h.old.workspace.edi_toNat
  have fixed (off : Nat) (bound : off < 2 ^ 32)
      (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem →
        PtrAt u B r off → WP isa (.block is) u Q) :
      WP isa (.block ([.mov r (.reg .edi), .alu .add r (.imm (BitVec.ofNat 32 off))] ++ is)) s Q := by
    refine wp_movS rfl fun u U _ => wp_addS rfl fun v V _ => ?_
    refine kk v ((U.keeps.trans V.keeps).mono (by simp)) (V.mem.trans U.mem) ?_
    change (v.gpr r).toNat = (B.toNat + off) % 2 ^ 32
    rw [V.gpr, U.gpr, BitVec.toNat_add, BitVec.toNat_ofNat, edi,
      Nat.mod_eq_of_lt bound]
  cases l with
  | fixed off => exact fixed off fit k
  | array w j =>
    by_cases hw : w = .correction
    · subst w
      exact fixed _ fit k
    · have H := h.runtime hw
      have f : VG.Proof.Rsa.X86.Keys.arr (kw (w.len n)) j < 2 ^ 32 := by
        simpa only [kw_words h.width, Loc.offset, VG.Proof.Rsa.X86.Keys.arr,
          VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.slot, VG.Impl.Rsa.X86.Keys.stride] using fit
      have code : ptr (.array w j) r t = VG.Impl.Rsa.X86.KeyRt.arrPtr w.lay r j t := by
        cases w <;> simp_all [ptr]
      rw [code]
      refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc H) H.lenLe
        edi hrt hte f fun u K m P _ => k u K m ?_
      simpa only [kw_words h.width, Loc.offset, VG.Proof.Rsa.X86.Keys.arr,
        VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.slot, VG.Impl.Rsa.X86.Keys.stride] using P

end VG.Proof.RsaKeyGen.X86.KeyRuntime
