module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # The three public runtime widths of the key workspace

Arithmetic changes only the workspace. Consequently the cdecl length and
workspace arguments remain available throughout derivation, including when
the inverse temporarily uses the prime or exponent bank.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)

theorem kw_full {n : Nat} (h : n % 4 = 0) : kw (4 * n) = n := by
  simp only [kw, Spec.Rsa.modulusWords]
  omega

theorem kw_prime {n : Nat} (h : n % 4 = 0) : kw (2 * n) = n / 2 := by
  simp only [kw, Spec.Rsa.modulusWords]
  omega

structure Ws (s : State) (B : Addr) (Z n N : Nat) : Prop where
  full : RtWs Width.modulus.lay s B Z (4 * n) N
  prime : RtWs Width.prime.lay s B Z (2 * n) N
  exponent : RtWs Width.exponent.lay s B Z 8 N
  width : n % 4 = 0
  size : 16 ≤ n ∧ n ≤ 256
  deep : VG.Proof.RsaKeyGen.X86.KeyArgs.DeepStk (s.gpr .esp) B Z

theorem shrinkRt {L : VG.Impl.Rsa.X86.KeyRt.Lay} {s : State} {B : Addr} {Z len N K : Nat}
    (h : RtWs L s B Z len N) (bound : K ≤ N) : RtWs L s B Z len K :=
  { h with ws := { h.ws with fits :=
      (Nat.le_trans (VG.Proof.Rsa.X86.Keys.arr_mono bound) h.ws.fits) } }

theorem Ws.shrink {s : State} {B : Addr} {Z n N K : Nat} (h : Ws s B Z n N)
    (bound : K ≤ N) : Ws s B Z n K :=
  ⟨shrinkRt h.full bound, shrinkRt h.prime bound, shrinkRt h.exponent bound, h.width, h.size, h.deep⟩

theorem Ws.old {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) :
    VG.Proof.Rsa.X86.Keys.Ws s B Z n N := by
  have old := h.full.ws
  rw [kw_full h.width] at old
  exact old

theorem Ws.arr_fit {s : State} {B : Addr} {Z n N j : Nat} (h : Ws s B Z n N) (hj : j < N) :
    VG.Proof.Rsa.X86.Keys.arr n j + VG.Proof.Rsa.X86.Keys.S n ≤ Z := h.old.arr_fit hj

theorem Ws.fit64 {s : State} {B : Addr} {Z n N j : Nat} (h : Ws s B Z n N) (hj : j < N) :
    VG.Proof.Rsa.X86.Keys.arr n j + VG.Proof.Rsa.X86.Keys.S n ≤ 2 ^ 64 := h.old.fit64 hj

theorem Ws.wpos {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) : 0 < n := h.old.wpos

theorem Ws.hdr_le {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) :
    VG.Impl.Rsa.X86.Keys.hdr ≤ Z := h.old.hdr_le

theorem Ws.keep {s t : State} {B : Addr} {Z n N : Nat} {rs : List Reg}
    (h : Ws s B Z n N) (K : Keeps rs s t) (O : Outside B 0 Z s.mem t.mem)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Ws t B Z n N :=
  ⟨h.full.keep K edi esp O, h.prime.keep K edi esp O,
    h.exponent.keep K edi esp O, h.width, h.size, by rw [K.1 .esp esp]; exact h.deep⟩

theorem Ws.afterKeep {s t : State} {B : Addr} {Z n N : Nat} {rs : List Reg}
    {js ds : List Nat} (h : Ws s B Z n N) (K : Keeps rs s t)
    (O : VG.Proof.Rsa.X86.Keys.Keep B n js ds s.mem t.mem)
    (hj : ∀ j ∈ js, j < N) (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Ws t B Z n N := by
  have O' : VG.Proof.Rsa.X86.Keys.Keep B (kw (4 * n)) js ds s.mem t.mem := by
    rw [kw_full h.width]
    exact O
  exact h.keep K (VG.Proof.Rsa.X86.KeyRt.keep_outside h.full.ws O' hj hd) edi esp

theorem Ws.lift {s : State} {B : Addr} {Z n N : Nat} {rs : List Reg}
    {js ds : List Nat} {p : Prog isa} {P : State → Prop} (h : Ws s B Z n N)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) (hj : ∀ j ∈ js, j < N)
    (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (k : WP isa p s fun t => VG.Proof.Rsa.X86.Keys.Ws t B Z n N ∧
      VG.Proof.Rsa.X86.Keys.Keep B n js ds s.mem t.mem ∧ P t ∧ Keeps rs s t) :
    WP isa p s fun t => Ws t B Z n N ∧ VG.Proof.Rsa.X86.Keys.Keep B n js ds s.mem t.mem ∧
      P t ∧ Keeps rs s t :=
  WP.mono k fun _ ⟨_, O, V, K⟩ => ⟨h.afterKeep K O hj hd edi esp, O, V, K⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
