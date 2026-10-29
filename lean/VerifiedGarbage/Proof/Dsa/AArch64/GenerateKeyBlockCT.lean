module
public import VerifiedGarbage.Impl.Dsa.AArch64.GenerateKey
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.GenerateKey
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Key generation's straight-line pieces: only the stack pointer is public in them -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_head_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block (GenerateKey.entry ++ GenerateKey.checkArgs)) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

theorem keygen_testCheck_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0]) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

theorem keygen_storeStatus_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block (Random.store Random.oStatus .x0 ++ ([.subImm .x .x4 .x0 1] : List Instr))) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

theorem keygen_deriveArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block GenerateKey.deriveArgs) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

theorem keygen_keepStatus_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block GenerateKey.keepStatus) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

end VG.Proof.Dsa.AArch64
