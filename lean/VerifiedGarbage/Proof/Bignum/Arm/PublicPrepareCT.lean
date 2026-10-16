module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Bignum.Arm.PcFn
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Public RSA workspace setup has a public trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicPrepare_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicValidInput base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicValidInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.prepare (fun s t => PublicPrepared base dst np ep xp len k eLen nb eb xb1 s ∧
        PublicPrepared base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp) := by
  let P := fun (s t : State) => PublicValidInput base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicValidInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have head : RelCT isa P (.block PcFn.head) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) {xb : List Byte} (h : PublicValidInput base dst np ep xp len k eLen nb eb xb s) :
      WP isa (.block PcFn.head) s (fun t => t.gpr .r0 = base) :=
    WP.mono (pcHead_ok s h.buffers.maxLength h.count) (fun _ j => (j.2.2.2.gpr .r0 (by simp)).trans h.ptr)
  have headReady := (relCT_keep_sp head (fun _ _ h => h.2.2)).wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have setupTrace : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .r0 = base ∧ t.gpr .r0 = base)
      setup (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h.1)
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.2.1.trans h.2.2.symm) e1 e2, trivial⟩
  have inputs : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.inputs) (fun s t => s.sp = t.sp) :=
    stackLoads_ct [(.r4, 8), (.r6, 12)]
  have prepare (s : State) {xb : List Byte} (h : PublicValidInput base dst np ep xp len k eLen nb eb xb s) :
      WP isa PublicFn.prepare s (PublicPrepared base dst np ep xp len k eLen nb eb xb) :=
    WP.mono (publicPrepare_ok s h) (fun _ h => h.1)
  exact (((headReady.seq (setupTrace.seq inputs)).wp (fun s t h => ⟨prepare s h.1, prepare t h.2.1⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩))

end VG.Proof.Bignum.Arm
