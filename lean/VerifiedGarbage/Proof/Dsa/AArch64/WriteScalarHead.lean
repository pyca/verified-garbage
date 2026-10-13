module

public import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
public import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Resolving the two signature output halves -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev scalarHead (offset : Nat) (second : Bool) : List Instr :=
  ([.movz .x .x1 (BitVec.ofNat 16 offset) 0, .add .x .x1 .x0 .x1,
    Core.field .x2 .out, Core.field .x9 .qLen, Core.field .x8 .mask] : List Instr) ++
    (if second then [.add .x .x2 .x2 .x9] else [])

theorem scalarHead_ok {s : State} {B out : Addr} {Z offset q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) (ho : offset < 2 ^ 16)
    (hout : word s.mem B Field.out.offset = out) (hq : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) (second : Bool) :
    WP isa (.block (scalarHead offset second)) s fun t =>
      t.gpr .x1 = off B offset ∧ t.gpr .x2 = (if second then out + BitVec.ofNat 64 q else out) ∧
      t.gpr .x9 = BitVec.ofNat 64 q ∧ t.gpr .x8 = mask valid ∧
      t.mem = s.mem ∧ Keep [.x1, .x2, .x9, .x8] s t := by
  refine WP.mono (WP.keep [.x1, .x2, .x9, .x8] (Q := fun t =>
      t.gpr .x1 = off B offset ∧ t.gpr .x2 = (if second then out + BitVec.ofNat 64 q else out) ∧
      t.gpr .x9 = BitVec.ofNat 64 q ∧ t.gpr .x8 = mask valid ∧ t.mem = s.mem) ?_
      (by cases second <;> rfl) (by cases second <;> rfl) (by cases second <;> rfl))
    fun t ⟨⟨hsi, hdx, hcx, h8, hmem⟩, hk⟩ => ⟨hsi, hdx, hcx, h8, hmem, hk⟩
  cases second <;> unfold scalarHead <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append]
  all_goals
    unfold Core.field
    brun [hdi, field_enc, hout, hq, hm, movz_ofNat ho,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ)]

end VG.Proof.Dsa.AArch64
