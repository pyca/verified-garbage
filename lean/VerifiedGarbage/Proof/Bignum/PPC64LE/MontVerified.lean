module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
public import VerifiedGarbage.Proof.Framework.Inline

/-!
# Montgomery multiplication on PPC64LE: reading the working space

Two states that agree on the working space read the same words from it
(`agree_read`, `agree_readW`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

/-! ## Reading memory within the working space -/

theorem agree_read {m₁ m₂ : Mem} {ws : Addr} {L d k : Nat}
    (h : ∀ a, (⟨ws, L⟩ : Region).Contains a 1 → m₁ a = m₂ a) (hk : d + k ≤ L) (hk' : d + k < 2 ^ 64) :
    m₁.read (ws + BitVec.ofNat 64 d) k = m₂.read (ws + BitVec.ofNat 64 d) k :=
  Mem.read_congr fun i hi => h _ (by
    simp only [Region.Contains]
    rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)]
    omega_arith)

theorem agree_readW {m₁ m₂ : Mem} {ws : Addr} {L d : Nat}
    (h : ∀ a, (⟨ws, L⟩ : Region).Contains a 1 → m₁ a = m₂ a) (hk : d + 8 ≤ L) (hk' : d + 8 < 2 ^ 64) :
    m₁.readW (ws + BitVec.ofNat 64 d) 64 = m₂.readW (ws + BitVec.ofNat 64 d) 64 := by
  simp only [Mem.readW, agree_read h hk hk']

end VG.Proof.Bignum.PPC64LE
