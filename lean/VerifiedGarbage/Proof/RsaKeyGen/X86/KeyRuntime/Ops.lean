module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half

/-! # Runtime key arithmetic reuses the common RSA word-loop proofs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem sub_ok {s : State} {B : Addr} {Z n N o a b : Nat}
    (h : Ws s B Z n N) (ho : o < N) (ha : a < N) (hb : b < N) :
    WP isa (sub o a b) s fun t => Ws t B Z n N ∧ Keep B n [o] [] s.mem t.mem ∧
      num t.mem B n o + num s.mem B n b =
        num s.mem B n a + 2 ^ (32 * n) * (t.gpr .ebx).toNat ∧
      (t.gpr .ebx).toNat ≤ 1 ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have core := VG.Proof.Rsa.X86.KeyRt.sub3_ok h.full ho ha hb
  rw [kw_full h.width] at core
  exact WP.mono core fun _ ⟨_, O, V, bit, K⟩ =>
    ⟨h.afterKeep K O (by simpa using ho) (by simp), O, V, bit, K.mono (by decide)⟩

theorem copy_ok {s : State} {B : Addr} {Z n N o a : Nat}
    (h : Ws s B Z n N) (ho : o < N) (ha : a < N) (hoa : o ≠ a) :
    WP isa (cp o a) s fun t => Ws t B Z n N ∧ Keep B n [o] [] s.mem t.mem ∧
      num t.mem B n o = num s.mem B n a ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t ∧
      w32 t.mem B (VG.Proof.Rsa.X86.Keys.arr n o + 4 * n) =
        w32 s.mem B (VG.Proof.Rsa.X86.Keys.arr n o + 4 * n) := by
  have core := VG.Proof.Rsa.X86.KeyRt.copy_ok h.full ho ha hoa
  rw [kw_full h.width] at core
  exact WP.mono core fun _ ⟨_, O, V, K, top⟩ =>
    ⟨h.afterKeep K O (by simpa using ho) (by simp), O, V, K.mono (by decide), top⟩

theorem sel_ok {s : State} {B : Addr} {Z n N o a b sl : Nat}
    (h : Ws s B Z n N) (ho : o < N) (ha : a < N) (hb : b < N)
    (hs : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (bit : slot s.mem B sl ≤ 1)
    (hab : o ≠ a ∨ o ≠ b) :
    WP isa (sel o a b sl) s fun t => Ws t B Z n N ∧ Keep B n [o] [] s.mem t.mem ∧
      num t.mem B n o = (if slot s.mem B sl = 0 then num s.mem B n a else num s.mem B n b) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have core := VG.Proof.Rsa.X86.KeyRt.sel_ok h.full ho ha hb hs bit hab
  rw [kw_full h.width] at core
  exact WP.mono core fun _ ⟨_, O, V, K⟩ =>
    ⟨h.afterKeep K O (by simpa using ho) (by simp), O, V, K.mono (by decide)⟩

theorem eq_ok {s : State} {B : Addr} {Z n N d a b tmp : Nat}
    (h : Ws s B Z n N) (ht : tmp < N) (ha : a < N) (hb : b < N)
    (hta : tmp ≠ a) (htb : tmp ≠ b) (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (eq d a b tmp) s fun t => Ws t B Z n N ∧
      Keep B n [tmp] [VG.Impl.Rsa.X86.Keys.sT, d] s.mem t.mem ∧
      slot t.mem B d = (if num s.mem B n a = num s.mem B n b then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have core := VG.Proof.Rsa.X86.KeyRt.eqS_ok h.full ht ha hb hta htb hd
  rw [kw_full h.width] at core
  refine WP.mono core fun _ ⟨_, O, V, K⟩ => ⟨h.afterKeep K O (by simpa using ht) ?_, O, V, K⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · decide
  · exact hd


theorem half_ok {s : State} {B : Addr} {Z n N j : Nat}
    (h : Ws s B Z n N) (hj : j < N) (bit : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.half full j) s fun t => Ws t B Z n N ∧
      Keep B n [j] [] s.mem t.mem ∧
      num t.mem B n j = (num s.mem B n j + 2 ^ (32 * n) * (s.gpr .ebx).toNat) / 2 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have core := VG.Proof.Rsa.X86.KeyRt.half_ok h.full hj bit
  rw [kw_full h.width] at core
  exact WP.mono core fun _ ⟨_, O, V, K⟩ =>
    ⟨h.afterKeep K O (by simpa using hj) (by simp), O, V, K⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
