module
public import VerifiedGarbage.Impl.Dsa.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.GenerateKey
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub


/-! # Key generation's straight-line pieces: only the stack pointer is public in them -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_rsp_pins : Pins (fun (B : Addr) (s : State) => s.gpr .rsp = B) [.rsp] := by
  intro B s t hs ht r hr
  rw [List.mem_singleton] at hr
  subst r
  exact hs.trans ht.symm

theorem keygen_head_ct : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    (.block (GenerateKey.entry ++ GenerateKey.checkArgs)) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.gpr .rsp = B) [.rsp] keygen_rsp_pins (by taint_decide)).mono
    (fun s _ h => ⟨s.gpr .rsp, rfl, h.symm⟩) (fun _ _ _ => trivial)

theorem keygen_testCheck_ct : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 0)]) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.gpr .rsp = B) [.rsp] keygen_rsp_pins (by taint_decide)).mono
    (fun s _ h => ⟨s.gpr .rsp, rfl, h.symm⟩) (fun _ _ _ => trivial)

theorem keygen_storeStatus_ct : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    (.block [.store (Random.sp Random.oStatus) .rax, .alu .cmp .rax (.imm 1)]) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.gpr .rsp = B) [.rsp] keygen_rsp_pins (by taint_decide)).mono
    (fun s _ h => ⟨s.gpr .rsp, rfl, h.symm⟩) (fun _ _ _ => trivial)

theorem keygen_deriveArgs_ct : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    (.block GenerateKey.deriveArgs) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.gpr .rsp = B) [.rsp] keygen_rsp_pins (by taint_decide)).mono
    (fun s _ h => ⟨s.gpr .rsp, rfl, h.symm⟩) (fun _ _ _ => trivial)

theorem keygen_keepStatus_ct : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    (.block GenerateKey.keepStatus) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.gpr .rsp = B) [.rsp] keygen_rsp_pins (by taint_decide)).mono
    (fun s _ h => ⟨s.gpr .rsp, rfl, h.symm⟩) (fun _ _ _ => trivial)

end VG.Proof.Dsa.X86_64
