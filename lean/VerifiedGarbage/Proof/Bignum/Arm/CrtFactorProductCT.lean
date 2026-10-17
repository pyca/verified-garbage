module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWideCT
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete factor-product validation arithmetic conceals both factors -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

theorem crt_factorProduct_ct {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool} (fit : 236 ≤ size) :
    RelCT isa (fun s t => CrtProductInput base size o a b cp cq w s coefficient ∧
      CrtProductInput base size o a b cp cq w t coefficient ∧ s.sp = t.sp) (factorProduct coefficient) (fun _ _ => True) := by
  let P := fun s => CrtProductInput base size o a b cp cq w s coefficient
  let R := fun s : State => P s ∧ val32 s.mem (State.addr base) o (2 * w + 2 * w + 2) = 0
  have clear := (crt_clearWide_ct (base := base) (dst := base + BitVec.ofNat 32 o) (size := size) (slot := 232) (w := w)
    (by omega) (by omega) (by decide)).mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.workspace, h.1.ptr, h.1.count, h.1.product⟩,
      ⟨h.2.1.workspace, h.2.1.ptr, h.2.1.count, h.2.1.product⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have clearWP (s : State) (h : P s) : WP isa (clearWide 232) s R :=
    WP.mono (crt_productClear_ready s h) (fun _ j => ⟨j.1, j.2.1⟩)
  have first := (relCT_keep_sp clear (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨clearWP s h.1, clearWP t h.2.1⟩)
  have args := (crt_productArgs_ct (base := base) (o := o) (a := a) (b := b) (cp := cp) (cq := cq) (w := w) (coefficient := coefficient) fit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ R s ∧ R t)
    (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) (fun _ _ _ => trivial)
  have argsWP (s : State) (h : R s) : WP isa (productArgs coefficient) s (CrtProductStart base size o a b w) :=
    WP.mono (crt_productArgs_ready s h.1 h.2) (fun _ j => j.1)
  have second := (relCT_keep_sp args (fun _ _ h => h.1)).wp
    (fun s t h => ⟨argsWP s h.2.1, argsWP t h.2.2⟩)
  have mul : RelCT isa (fun s t => s.sp = t.sp ∧ CrtProductStart base size o a b w s ∧
      CrtProductStart base size o a b w t) wideProduct (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact wideProduct_ct h.2.1.context h.2.2.context s t tr1 tr2 u v
      ⟨h.2.1.initial, h.2.2.initial, h.1⟩ e1 e2
  exact first.seq (second.seq mul)

end VG.Proof.Bignum.Arm
