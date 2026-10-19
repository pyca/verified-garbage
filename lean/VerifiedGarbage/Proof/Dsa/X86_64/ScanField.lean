module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.DomainShape

import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Tactic.Set

/-! # Scanning modulus buffers through the saved DSA fields -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem scanField_ok {s : State} {B p : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z) (fp fl : Field) {bytes : List Byte}
    (hp : word s.mem B fp.offset = p)
    (hl : word s.mem B fl.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z p bytes) (h1 : 0 < bytes.length) (h64 : bytes.length < 2 ^ 64) :
    WP isa (.seq (.block [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl))])
      Checks.significant) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (VG.Proof.Dsa.significant bytes).1 ∧
      t.gpr .r9 = (VG.Proof.Dsa.significant bytes).2.zeroExtend 64 ∧
      t.mem = s.mem ∧ Keep [.rax, .r8, .r9, .rsi, .rcx] s t := by
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx] (Q := fun u =>
    u.gpr .rsi = p ∧ u.gpr .rcx = BitVec.ofNat 64 bytes.length ∧ u.mem = s.mem) ?_ rfl)
    fun u ⟨⟨hup, hul, hum⟩, hku⟩ => ?_)
  · xrun [State.ea, Core.field, hdi, fieldAddress, hp, hl,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 hZ)]
  refine WP.mono (significant_ok hup hul (hsrc.congrK (by rw [hum]; exact InScr.refl _ _ _) hku) h1 h64)
    fun t ⟨ht8, ht9, htm, hkt⟩ => ⟨ht8, ht9, htm.trans hum, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
