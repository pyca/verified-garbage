module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWide
public import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtClearWide
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Clearing a CRT buffer reveals only its public pointer and width -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtClearWideInput (base dst : BitVec 32) (size slot w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w
  link : s.mem.readW (off (State.addr base) slot) 32 = dst

theorem crt_clearWide_ct {base dst : BitVec 32} {size slot w : Nat}
    (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096) :
    RelCT isa (fun s t => CrtClearWideInput base dst size slot w s ∧ CrtClearWideInput base dst size slot w t ∧ s.sp = t.sp)
      (clearWide slot) (fun _ _ => True) := by
  let P := CrtClearWideInput base dst size slot w
  let Q := fun s : State => s.gpr .r0 = dst ∧ s.gpr .lr = BitVec.ofNat 32 (4 * w + 2)
  have args : RelCT isa (fun s t => P s ∧ P t) (.block (clearWideArgs slot)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block (clearWideArgs slot)) s Q :=
    WP.mono (crt_clearWideArgs_ok s h.workspace fit slotFit hs h.ptr h.count h.link) (fun _ j => ⟨j.1, j.2.1⟩)
  have clear : RelCT isa (fun s t => Q s ∧ Q t) zero (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨zero_ct s t tr1 tr2 u v trivial trivial ⟨h.1.1.trans h.2.1.symm, h.1.2.trans h.2.2.symm⟩ e1 e2, trivial⟩
  have body := relCT_keep_sp (((pair_posts args wp).seq clear).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)
  exact ((body.seq (loadStack_ct .r0 0)).assoc).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
