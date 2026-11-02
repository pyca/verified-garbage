module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

/-! # The contract of the batched inverse on x86-64

`InvLaw`: what `Impl/Rsa/X86_64/Keys.lean`'s `inverse u v x₂ m` does, for
its callers to use without importing the algebra of its proof
(`InvB/Main.lean`'s `inverse_ok`); the registrations supply the instance
(`InvInstance.lean`).

At the width `w`, with room for its private arrays 16 to 25: for an odd `m`
in `[m]`, `[v] = gcd(u, m)`, `m ∣ [x₂] u - [v]` and `[x₂] < m`; it writes
only `[v]`, `[x₂]` and the private arrays, and keeps `rdi`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- An array's offset, as a linear term. -/
theorem slot_lin (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := by unfold slot hdrBytes; rfl

class InvLaw : Prop where
  inverse_ok {s : State} {B : Addr} {Z w iU iV iX₂ iM : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
      (hw20 : w < 2 ^ 20) (hU : iU < 16) (hV : iV < 16) (hX : iX₂ < 16) (hM : iM < 16) (hVX : iV ≠ iX₂) :
      WP isa (inverse iU iV iX₂ iM) s fun t => t.gpr .rdi = B ∧
        Frm B [(slot w iV, 8 * w), (slot w iX₂, 8 * w), (slot w 16, 80 * (w + 2))] s.mem t.mem ∧
        Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t ∧
        (wv s.mem B (slot w iM) w % 2 = 1 →
          wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w) ∧
          ((wv s.mem B (slot w iM) w : Nat) : Int) ∣
            (wv t.mem B (slot w iX₂) w : Int) * wv s.mem B (slot w iU) w - wv t.mem B (slot w iV) w ∧
          wv t.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w)

end VG.Proof.Rsa.X86_64
