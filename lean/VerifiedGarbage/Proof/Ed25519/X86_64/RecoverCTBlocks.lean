module

public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
public import VerifiedGarbage.Proof.Ed25519.X86_64.Field
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.X25519.X86_64.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Ed25519.ScalarMul
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverPoint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.X25519.X86_64.Inv
import VerifiedGarbage.Proof.X25519.X86_64.Invert
import VerifiedGarbage.Proof.X25519.X86_64.Sqr
meta import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
meta import VerifiedGarbage.Impl.Mont.Mod
meta import VerifiedGarbage.Proof.Ed25519.ScalarMul
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Points
meta import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverPoint
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.X25519.X86_64.AddSub
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
meta import VerifiedGarbage.Proof.X25519.X86_64.Freeze
meta import VerifiedGarbage.Proof.X25519.X86_64.Inv
meta import VerifiedGarbage.Proof.X25519.X86_64.Invert
meta import VerifiedGarbage.Proof.X25519.X86_64.Sqr

/-! Fixed-trace arithmetic blocks used in point recovery. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem rdi_agree {base : Addr} {s t : State} (hs : s.gpr .rdi = base) (ht : t.gpr .rdi = base) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi]) s t := Taint.agree_ofRegs (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) (recoverCandidate fld) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem parityBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem zeroBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem negateBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (fieldCode fld [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem successBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (recoverSuccess fld)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem recoverInvalid_ct : RelCT isa (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
  exact fun _ _ _ => Taint.agree_ofRegs (by simp)

end VG.Proof.Ed25519.X86_64
