module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePower
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrimeCT
public import VerifiedGarbage.Proof.Bignum.Arm.SecretPowerCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A complete CRT factor power hides acceptance, factors, input and exponent -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (arrAt)

theorem crt_primePower_ct {base xp ep : BitVec 32} {len w k eLen slot : Nat} {xb1 xb2 eb1 eb2 : List Byte}
    (countFits : 128 * w < 2 ^ 32) (fit : arrAt w 3 + 32 ≤ 8 * len)
    (positive : 0 < eb1.length) (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => CrtPrimePowerInput base xp ep len w k eLen slot xb1 eb1 s ∧
      CrtPrimePowerInput base xp ep len w k eLen slot xb2 eb2 t ∧ s.sp = t.sp)
      (primePower slot) (fun _ _ => True) := by
  let P := fun (s t : State) => CrtPrimePowerInput base xp ep len w k eLen slot xb1 eb1 s ∧
    CrtPrimePowerInput base xp ep len w k eLen slot xb2 eb2 t ∧ s.sp = t.sp
  let Q := fun (xb eb : List Byte) (s : State) => ∃ M, CrtPreparedPower base xp ep len w k eLen slot M xb eb s
  let R := fun (xb eb : List Byte) (s : State) => ∃ M, SecretPowerInput base xp ep len w k eLen M xb eb s
  have prepare : RelCT isa P prepareAcceptedPrime (fun _ _ => True) :=
    (prepareAcceptedPrime_ct countFits).mono
      (fun _ _ h => ⟨h.1.accepted, h.2.1.accepted, h.2.2⟩) (fun _ _ _ => trivial)
  have prepWP (s : State) {xb eb : List Byte} (h : CrtPrimePowerInput base xp ep len w k eLen slot xb eb s) :
      WP isa prepareAcceptedPrime s (Q xb eb) :=
    (crt_primePower_prepare s h countFits).mono (fun _ j => ⟨_, j.1⟩)
  have first := (relCT_keep_sp prepare (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨prepWP s h.1, prepWP t h.2.1⟩)
  have args : RelCT isa (fun (s t : State) => s.sp = t.sp ∧ Q xb1 eb1 s ∧ Q xb2 eb2 t)
      (.block (primePowerArgs slot)) (fun s t => s.sp = t.sp) :=
    (stackLoads_ct [(.r4, 56), (.r6, 12), (.r1, slot), (.r2, slot + 4)]).mono
      (fun _ _ h => h.1) (fun _ _ h => h)
  have argsWP (s : State) {xb eb : List Byte} (h : Q xb eb s) :
      WP isa (.block (primePowerArgs slot)) s (R xb eb) := by
    obtain ⟨M, h⟩ := h
    exact (crt_primePower_ready s h).mono (fun _ j => ⟨M, j.1⟩)
  have second := args.wp (fun s t h => ⟨argsWP s h.2.1, argsWP t h.2.2⟩)
  have power : RelCT isa (fun (s t : State) => s.sp = t.sp ∧ R xb1 eb1 s ∧ R xb2 eb2 t)
      secretPower (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨sp, ⟨M1, h1⟩, ⟨M2, h2⟩⟩ := h
    exact secretPower_ct fit positive length s t tr1 tr2 u v ⟨h1, h2, sp⟩ e1 e2
  exact first.seq (second.seq power)

end VG.Proof.Bignum.Arm
