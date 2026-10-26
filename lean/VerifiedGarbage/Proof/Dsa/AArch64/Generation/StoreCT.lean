module
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import Mathlib.Tactic.ToAdditive
public import Aesop.BuiltinRules
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import Mathlib.Tactic.ToAdditive
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! Full-width candidate and exponent stores have public addressing. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

structure StorePublic where
  B : Addr
  Z : Nat
  w : Nat
  out : Addr

structure StoreState (ptr : Nat) (p : StorePublic) (s : State) : Prop where
  ws : VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w
  pointer : word s.mem p.B (8 * ptr) = p.out
  length : word s.mem p.B 136 = BitVec.ofNat 64 (8 * p.w)
  mask : word s.mem p.B (8 * sMask) = mask true
  write : ∀ i < 8 * p.w, InRegions s.wr (off p.out i) 1
  outside : ∀ i < 8 * p.w, p.Z ≤ ofs p.B (off p.out i)

theorem storeCandidate_ct {a ptr : Nat} (ha : a < 16) (hp : ptr < 32)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base a .x8 ++
      [ldh .x1 ptr, ldh .x9 17, .add .x .x1 .x1 .x9, ldh .x15 sMask])) hc).isSome = true) :
    RelCT isa (Two (StoreState ptr)) (seqs (storeA a ptr 17 sMask)) (fun _ _ => True) := by
  have ct := pin_ct (c₂ := storeBE) (Φ := StoreState ptr) (Ψ := fun _ _ => True)
    [.x0] [.x0, .x8, .x1, .x9] (fun p => soVal p.B (off p.B (slot p.w a)) p.out (8 * p.w))
    (fun _ _ _ hs ht r hr => by obtain rfl := List.mem_singleton.mp hr; exact hs.ws.x0.trans ht.ws.x0.symm)
    ht (fun p s h => storeBlk_ok h.ws hp (by decide : 17 < 32) h.pointer h.length) (by taint_decide)
    (fun _ _ h => WP.mono (storeCandidateArray_ok h.ws ha hp h.pointer h.length h.mask h.write h.outside)
      (fun _ _ => True.intro))
  exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.AArch64.Generation
