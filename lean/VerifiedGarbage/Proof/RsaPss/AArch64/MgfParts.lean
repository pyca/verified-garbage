module
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS on AArch64: clearing, `DB`'s place and the frame's slots

Ranges of the working space cleared eight bytes at a time (`clearQ_ok`);
where `DB` and `H` are (`DbAt`); and the slots of the frame (`slotR`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_eor wp_lsr wp_ldrb wp_strb
  wp_strx wp_add wp_sub eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_addSp wp_countdown wp_mov setWidth_ofNat16 copy_ok ofNat_succ'
  ite_both)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-! ## Clearing -/

/-- `V` with `n` bytes cleared from `o`. -/
def clr (V : Nat → Byte) (o n : Nat) : Nat → Byte := fun x => if o ≤ x ∧ x < o + n then 0 else V x

theorem clr_zero (V : Nat → Byte) (o : Nat) : clr V o 0 = V := by
  funext x; simp only [clr]; rw [ite_eq_right (by omega_using [])]

theorem Rep.wz {m : Mem} {S : Addr} {V : Nat → Byte} (h : Rep m S V) {o : Nat} (ho : o + 8 ≤ oRsa) :
    Rep (m.writeW (off S o) (0#64)) S (clr V o 8) := by
  have e : m.writeW (off S o) (0#64) = VG.WriteBytes.writeBytes m (off S o) (List.replicate 8 0) := by
    rw [Mem.writeW, write_eq_writeBytes]; rfl
  rw [e]
  refine (h.writeBytes (by simp only [List.length_replicate]; omega_using [ho])).congr fun x _ => ?_
  simp only [updL, clr, List.length_replicate]
  by_cases hx : o ≤ x ∧ x < o + 8
  · rw [ite_eq_left hx, ite_eq_left hx, List.getD_eq_getElem?_getD, List.getElem?_replicate,
      ite_eq_left (by omega_using [hx])]
    rfl
  · rw [ite_eq_right hx, ite_eq_right hx]

/-- `n` words of zeros from `x10 = scratch + o`, counted down in `x12`. -/
theorem clearQ_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {o n : Nat}
    (hn : 0 < n) (ho : o + 8 * n ≤ oRsa) (h10 : t.gpr .x10 = off S o) (h9 : t.gpr .x9 = 0#64)
    (h12 : t.gpr .x12 = BitVec.ofNat 64 n) :
    WP isa (.loop (.block [.str .x .x9 .x10 0, .addImm .x .x10 .x10 8, .subImm .x .x12 .x12 1])
      (.nonzero .x .x12)) t fun t' => Keep [.x10, .x12] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
        Rep t'.mem S (clr V o (8 * n)) := by
  have c6 : oRsa = 8192 := rfl
  refine WP.mono (wp_countdown (cnt := .x12) (by omega_using [ho, c6]) hn (fun j u => Keep [.x10, .x12] t u ∧
      u.gpr .x10 = off S (o + 8 * j) ∧ Frame [⟨S, oRsa⟩] t.mem u.mem ∧ Rep u.mem S (clr V o (8 * j)))
    (fun j hj u ⟨hK, h10', hF, hR⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [h10, Nat.mul_zero, Nat.add_zero], Frame.refl _ _, by rw [Nat.mul_zero, clr_zero]; exact R⟩
    h12) fun u h => ⟨h.1, h.2.2⟩
  have hj8 : o + 8 * j + 8 ≤ oRsa := by omega_using [ho, hj]
  refine wp_strx (by decide) (by rw [h10', BitVec.add_zero]) (by rw [hK.wr]; exact L.st hj8) fun u₁ m₁ => ?_
  refine wp_addImm (by decide) fun u₂ o₂ e₂ => wp_subImm (by decide) fun u₃ o₃ e₃ => wp_nil ?_
  have hm : u₃.mem = u.mem.writeW (off S (o + 8 * j)) (0#64) := by
    rw [o₃.mem, o₂.mem, m₁.mem, hK.get .x9, h9]
  refine ⟨⟨(hK.trans (m₁.keep.trans (o₂.keep.trans o₃.keep))).mono, ?_, ?_, ?_⟩, ?_⟩
  · rw [o₃.get .x10, e₂, m₁.gpr, h10', off_add, Nat.mul_succ, Nat.add_assoc]
  · rw [hm]
    exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hj8]) (by omega_using [c6, hj8]))
  · rw [hm]
    refine (hR.wz hj8).congr fun x _ => ?_
    simp only [clr]
    by_cases h₁ : o + 8 * j ≤ x ∧ x < o + 8 * j + 8
    · rw [ite_eq_left h₁, ite_eq_left (by rw [Nat.mul_succ]; omega_using [h₁])]
    · rw [ite_eq_right h₁]
      by_cases h₂ : o ≤ x ∧ x < o + 8 * j
      · rw [ite_eq_left h₂, ite_eq_left (by rw [Nat.mul_succ]; omega_using [h₂])]
      · rw [ite_eq_right h₂, ite_eq_right (by rw [Nat.mul_succ]; omega_using [h₁, h₂])]
  · rw [e₃, o₂.get .x12, m₁.gpr]

/-- Where `DB` and `H` are: `DB` the `db` bytes at `scratch + e`, `H` the
`hLen` after them, within `EM`'s place. -/
structure DbAt (D e db : Nat) : Prop where
  e1 : oEm ≤ e
  db1 : 1 ≤ db
  fit : e + db + D ≤ oY

/-- A slot of the frame. -/
abbrev slotR (F : Addr) (d : Nat) : Region := ⟨off F d, 8⟩

theorem frame_slot (m : Mem) (F : Addr) (d : Nat) (v : BitVec 64) :
    Frame [slotR F d] m (m.writeW (off F d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Lay.slotS {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (h : d + 8 ≤ frameBytes) :
    ∀ r ∈ [slotR F d], Region.Disjoint ⟨S, oRsa⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (L.dFS.sub_left (Offset.sub_base F h)).symm

end VG.Proof.RsaPss.AArch64
