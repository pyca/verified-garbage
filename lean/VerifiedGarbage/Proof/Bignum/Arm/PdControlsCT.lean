module

public import VerifiedGarbage.Proof.Bignum.Arm.PdControls
public import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Exponent-control initialization is independent of secret input and acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pdControls_ct {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PdAccepted base dst np ep xp len k eLen N R eb xb1 s ∧
      PdAccepted base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PublicFn.controls (fun _ _ => True) := by
  let P := fun (s t : State) => PdAccepted base dst np ep xp len k eLen N R eb xb1 s ∧
    PdAccepted base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp
  have wp (s : State) {xb : List Byte} (h : PdAccepted base dst np ep xp len k eLen N R eb xb s) :
      WP isa (.block PublicFn.controlArgs) s (PdAccepted base dst np ep xp len k eLen N R eb xb) := by
    refine WP.mono (publicControlArgs_ok s h.stack) ?_
    rintro t ⟨_, _, mem, rest⟩
    exact h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
  have args := (publicControlArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact args.seq (expControls_ct.mono (fun _ _ h => h.2.1.ready.ptr.trans h.2.2.ready.ptr.symm) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
