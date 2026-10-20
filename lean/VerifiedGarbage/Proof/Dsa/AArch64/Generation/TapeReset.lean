module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Reset a bounded-tape cursor without changing other memory -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem tapeReset_ok (slots : TapeSlots) {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hsp : s.sp = B)
    (hd : 8 * slots.used + 8 ≤ Z) (hi : 8 * slots.used < 4096) :
    WP isa (.block (tapeReset slots)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * slots.used)) (0 : BitVec 64) ∧
      Keep [.x0, .x15] s t := by
  refine WP.keep [.x0, .x15] (Q := fun t =>
    t.mem = s.mem.writeW (off B (8 * slots.used)) (0 : BitVec 64)) ?_ rfl rfl rfl
  unfold tapeReset Impl.Dsa.AArch64.Random.store
  brun [exec_addSp hi, hsp, hs.st hd]
  rfl

end VG.Proof.Dsa.AArch64.Generation
