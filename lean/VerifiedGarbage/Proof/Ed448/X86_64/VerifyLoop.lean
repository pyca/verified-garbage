module

public import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.X86_64.BaseStep
import VerifiedGarbage.Proof.X448.X86_64.Chain
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Ed448 verification's equation on x86-64: pieces of the loop

Pieces of an iteration of the loop over the bits `t` of `S` (at `BITS`, read
at `ea_bitsAt`): a slot copied into another (`copySlot_ok`), a constant into
a slot (`constE_ok`), and points whose slots are kept (`pt_congr`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk off contains_sc mask cswapE opSwap clob Outside
  copyOut_ok E_outside)
open VG.Impl.X448.X86_64 (BITS slot cswap copyOut W)

theorem ea_bitsAt {s : State} {base : Addr} (hr : s.gpr .rdi = base) {t : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (o : Nat) :
    s.ea { base := .rdi, index := some .rbx, disp := (o : Int) } = off base (o + t) := by
  simp only [State.ea, hr, hb, off, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm t o]

theorem pt_congr {e e' : Env} {a b c : Index} (ha : e' a = e a) (hb : e' b = e b) (hc : e' c = e c) :
    pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

/-- Slot `j` copied into slot `i`. -/
theorem copySlot_ok {s : State} {base : Addr} (hs : Scr s base) (i j : Index) :
    WP isa (.block (copyOut (slot i.val) (slot j.val))) s fun t =>
      Keep base s t ∧ E t.mem base = Function.update (E s.mem base) i (E s.mem base j) := by
  have hW : ∀ x ∈ W, x ∈ clob := by decide
  have hi := Proof.X448.X86_64.slot_lt i
  have hj := Proof.X448.X86_64.slot_lt j
  have gi := Proof.X448.X86_64.slot_ge i
  simp only [Impl.X448.X86_64.ACC] at hi hj
  refine WP.mono (copyOut_ok hs (by omega) (by omega)) fun t ⟨ft, ot, gt, rdt, wrt⟩ =>
    ⟨⟨fun r hr => gt r (fun h => hr (hW r h)), rdt, wrt,
      ot.mono (by omega) (by omega)⟩, ?_⟩
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self]
    show VG.Proof.X448.toFe (Proof.X448.X86_64.fe t.mem base (slot k.val)) =
      VG.Proof.X448.toFe (Proof.X448.X86_64.fe s.mem base (slot j.val))
    rw [ft]
  · rw [Function.update_of_ne hk]
    exact E_outside ot k (Proof.X448.X86_64.slot_sep hk)

/-- A constant into slot `i`. -/
theorem constE_ok {s : State} {base : Addr} (hs : Scr s base) (i : Index) (v : Spec.X448.Fe)
    (hv : VG.Proof.X448.toFe (Proof.X448.X86_64.wv (words7 v.val)) = v) :
    WP isa (.block (constSlot i.val v)) s fun t =>
      Keep base s t ∧ E t.mem base = Function.update (E s.mem base) i v := by
  have hW : ∀ x ∈ W, x ∈ clob := by decide
  have hi := Proof.X448.X86_64.slot_lt i
  have gi := Proof.X448.X86_64.slot_ge i
  simp only [Impl.X448.X86_64.ACC] at hi
  exact WP.mono (constSlot_ok hs i v hv) fun t ⟨et, ot, gt, rdt, wrt⟩ =>
    ⟨⟨fun r hr => gt r (fun h => hr (hW r h)), rdt, wrt,
      ot.mono (by omega) (by omega)⟩, et⟩

end VG.Proof.Ed448.X86_64
