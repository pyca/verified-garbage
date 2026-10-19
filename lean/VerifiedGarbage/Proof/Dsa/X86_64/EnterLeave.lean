module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame

import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Bignum.CrtMath
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Exp
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Proof.Dsa.X86_64.Load
public import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Switching between the DSA parent and arithmetic workspaces -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Enter a linked child without changing memory or any other register. -/
theorem enter_ok {s : State} {B : Addr} {Z o w wx : Nat} {parentMinv minv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : WsAt s.mem B o wx minv)
    (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31) :
    WP isa (.block (Core.enter o)) s fun t =>
      SubCtx t B Z o w wx minv ∧ t.mem = s.mem ∧ Keep [.rdi] s t := by
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hdi, hm⟩, hk⟩ =>
      ⟨⟨hg.scr.congr hk.2.2, hdi, hm ▸ child.hdr, hm ▸ child.link,
        hm ▸ hg.hdr.hw, hm ▸ hg.hdr.harr, hlo, hhi⟩, hm, hk⟩
  unfold Core.enter
  xrun [hg.rdi, sx_ofNat ho]

/-- Return through the child's parent link; all parent fields and operand
buffers retain the memory frame established by the arithmetic routine. -/
theorem leave_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv parentMinv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv)
    (hp : word s.mem B (8 * sMinv) = parentMinv) :
    WP isa (.block [Crt.leave]) s fun t =>
      Good t B Z w parentMinv ∧ t.mem = s.mem ∧ Keep [.rdi] s t := by
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hdi, hm⟩, hk⟩ =>
      ⟨⟨hc.scr.congr hk.2.2, hdi, ⟨hm ▸ hc.nw, hm ▸ hp, hm ▸ hc.narr⟩⟩, hm, hk⟩
  unfold Crt.leave
  xrun [State.ea, hdr, hc.rdi, hdrOff, hc.link,
    hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot wx 8 from hdr_lt_slot wx 8 (by decide))]

end VG.Proof.Dsa.X86_64
