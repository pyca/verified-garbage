module
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! # Reading the final encoded modulus byte for oddness validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem lastByte_ok {s : State} {B p : Addr} {Z n : Nat} {b : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (fp fl : Field) (r : Reg) (hp : word s.mem B fp.offset = p)
    (hl : word s.mem B fl.offset = BitVec.ofNat 64 n) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (n - 1)) 1)
    (hb : s.mem (p + BitVec.ofNat 64 (n - 1)) = b) :
    WP isa (.block [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl)),
      .movzx8 r { base := .rsi, index := some .rcx, disp := -1 }]) s fun t =>
      t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem ∧ Keep [.rsi, .rcx, r] s t := by
  have he : p + BitVec.ofNat 64 n + BitVec.ofInt 64 (-1) = p + BitVec.ofNat 64 (n - 1) := by
    rw [BitVec.add_assoc, show BitVec.ofInt 64 (-1) = -(1#64) from rfl,
      ← BitVec.sub_eq_add_neg]
    exact congrArg (p + ·) (ofNat64_pred h1 h64)
  refine WP.mono (WP.keep [.rsi, .rcx, r] (Q := fun t =>
    t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem) ?_ ?_)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  · xrun [State.ea, Core.field, hdi, fieldAddress, hp, hl, show ∀ x : Addr, x * 1#64 = x from fun x => BitVec.mul_one x, he, hr, hb,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 hZ)]
  · cases r <;> rfl

end VG.Proof.Dsa.X86_64
