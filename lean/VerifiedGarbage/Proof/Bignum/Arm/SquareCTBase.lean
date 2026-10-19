module

import VerifiedGarbage.Proof.Bignum.Arm.SquareInit
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Square
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.Square
public import VerifiedGarbage.Proof.Bignum.Arm.SquareState
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Two runs of a square leak the same trace: the pieces

The square's addresses and counts come from its metadata and the header,
which correctness shows hold the same public values in both runs. Each
piece between such loads is checked by the taint analysis from the
registers correctness pins down (`seg`), or by an existing constant-time
proof (`segCT`); the loads from the stack (`segStack`) have the same
address in both runs. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

/-- A piece the taint analysis checks with the registers `rs` public. -/
abbrev SqCert (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs rs) c hc).isSome = true

theorem seg {P Q : State → Prop} {c : Prog isa} {rs : List Reg} (hc : SqCert rs c)
    (pin : ∀ s t, P s → P t → ∀ r ∈ rs, s.gpr r = t.gpr r) (wp : ∀ s, P s → WP isa c s Q) :
    RelCT isa (fun s t => P s ∧ P t) c (fun s t => Q s ∧ Q t) := by
  obtain ⟨h, hh⟩ := hc
  exact pair_posts (RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun s t hst => Taint.agree_ofRegs (pin s t hst.1 hst.2)) hh) wp

/-- The last piece: its trace alone. -/
theorem segEnd {P : State → Prop} {c : Prog isa} {rs : List Reg} (hc : SqCert rs c)
    (pin : ∀ s t, P s → P t → ∀ r ∈ rs, s.gpr r = t.gpr r) :
    RelCT isa (fun s t => P s ∧ P t) c (fun _ _ => True) := by
  obtain ⟨h, hh⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s t hst => Taint.agree_ofRegs (pin s t hst.1 hst.2)) hh

theorem segStack {P Q : State → Prop} {r : Reg} {d : Nat} (sp : ∀ s t, P s → P t → s.sp = t.sp)
    (wp : ∀ s, P s → WP isa (.block [.ldrSp r d]) s Q) :
    RelCT isa (fun s t => P s ∧ P t) (.block [.ldrSp r d]) (fun s t => Q s ∧ Q t) :=
  pair_posts ((loadStack_ct r d).mono (fun s t h => sp s t h.1 h.2) (fun _ _ _ => trivial)) wp

theorem segCT {P Q : State → Prop} {c : Prog isa} {Pub : State → State → Prop}
    (ct : ConstantTime isa (fun _ => True) Pub c) (pub : ∀ s t, P s → P t → Pub s t)
    (wp : ∀ s, P s → WP isa c s Q) :
    RelCT isa (fun s t => P s ∧ P t) c (fun s t => Q s ∧ Q t) :=
  pair_posts (fun s t tr1 tr2 u v h e1 e2 =>
    ⟨ct s t tr1 tr2 u v trivial trivial (pub s t h.1 h.2) e1 e2, trivial⟩) wp

theorem anchorLoad_cert : SqCert [.r0] (.block [.ldr .r0 .r0 80]) := ⟨_, by taint_decide⟩

section
variable {base : BitVec 32} {size out a mod M n : Nat} {sp0 : BitVec 32}

/-- What every point of a square keeps: the stack pointer and the environment. -/
def SqHold (base : BitVec 32) (size out a mod M n : Nat) (sp0 : BitVec 32) (s : State) : Prop :=
  s.sp = sp0 ∧ ∃ m0 inv, SqEnv m0 base size out a mod M n inv s

theorem sqAnchor_ct {P : State → Prop} (hold : ∀ s, P s → SqHold base size out a mod M n sp0 s)
    (stable : ∀ s t, P s → t.mem = s.mem → Rest [.r0] s t → P t) :
    RelCT isa (fun s t => P s ∧ P t) sqAnchor fun s t =>
      (P s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M) ∧ (P t ∧ t.gpr .r0 = base + BitVec.ofNat 32 M) := by
  unfold sqAnchor
  have first := segStack (P := P) (Q := fun s => P s ∧ s.gpr .r0 = base) (r := .r0) (d := 0)
    (fun s t hs ht => (hold s hs).1.trans (hold t ht).1.symm) (fun s hs => by
      obtain ⟨_, m0, inv, env⟩ := hold s hs
      exact WP.mono (sqBase_ok s env .r0) fun t ⟨p, mem, rest⟩ => ⟨stable s t hs mem rest, p⟩)
  refine first.seq (seg anchorLoad_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_))
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
  · obtain ⟨_, m0, inv, env⟩ := hold s hs.1
    have nowrap := env.nowrap
    have := env.header; have := env.fits
    refine wp_ldr (a := off (State.addr base) 80) (by decide) (sq_ea0 nowrap hs.2 (by omega))
      (env.read (by omega)) fun t ut => WP.block_nil ?_
    exact ⟨stable s t hs.1 ut.mem (ut.rest (by simp)), ut.gpr.trans env.metaNow⟩

end

end VG.Proof.Bignum.Arm
