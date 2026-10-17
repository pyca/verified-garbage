module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
public import VerifiedGarbage.Impl.RsaPss.X86_64.AnyHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSASSA-PSS on x86-64 with the hash functions as arguments: the length checks

`emLenAny` and `saltFitsAny` do what `emLen` and `saltFits` do for a hash
function whose digest is `D` bytes, `D` from the slot `sHd`
(`emLenAny_ok`, `saltFitsAny_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)

theorem emLenAny_ok {D : Nat} (hD : D + 2 < 2 ^ 31) {u : State} {F S : Addr}
    (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {x k : Nat}
    (hk : W 17 = BitVec.ofNat 64 k) (h15 : W 15 = BitVec.ofNat 64 D) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 32)
    (hdx : u.gpr .rdx = (if x = 1 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)))
    (hz : u.zf = some (decide (x = 1))) :
    WP isa emLenAny u fun u' => Lay u' F S ∧ Keep [.rdx, .r8, .rax, .r9] u u' ∧
      Rep u'.mem F S V (upd (upd W 25 (maskV x)) 26 (BitVec.ofNat 64 (loV x))) ∧
      u'.gpr .rax = BitVec.ofNat 64 (k - loV x) ∧ u'.cf = some (decide (k - loV x < D + 2)) := by
  have G := L.geo
  have hl : loV x ≤ 1 := by unfold loV; split <;> omega
  -- The mask and `lo`.
  refine WP.seq (WP.mono (Q := fun (v : State) => Keep [.rdx, .r8] u v ∧ v.mem = u.mem ∧ v.gpr .rdx = maskV x ∧
      v.gpr .r8 = BitVec.ofNat 64 (loV x)) ?_ fun v ⟨kv, hmv, hdv, h8v⟩ => ?_)
  · refine WP.ite (M := isa) _ (show isa.eval .e u = _ from hz) (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      refine WP.mono (WP.keep [.rdx, .r8] (Q := fun v => v.mem = u.mem ∧ v.gpr .rdx = maskV x ∧
        v.gpr .r8 = BitVec.ofNat 64 (loV x)) ?_ rfl) fun v ⟨h, k'⟩ => ⟨k', h⟩
      xrun [maskV, loV, hb]
    · rw [decide_eq_false_iff_not] at hb
      refine WP.mono (WP.keep [.r8] (Q := fun v => v.mem = u.mem ∧
        v.gpr .r8 = BitVec.ofNat 64 (loV x)) ?_ rfl) fun v ⟨⟨h, h'⟩, k'⟩ =>
          ⟨k'.mono (by decide), h, by rw [k'.gpr (by decide), hdx, ifn hb, maskV, ifn hb], h'⟩
      xrun [loV, hb]
  have Lv : Lay v F S := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hmv])
  have Rv : Rep v.mem F S V W := hmv ▸ R
  have R1 := Rv.wf G (k := 25) (by decide) (maskV x)
  have R2 := R1.wf G (k := 26) (by decide) (BitVec.ofNat 64 (loV x))
  rw [show off F (8 * 25) = off F sC from rfl] at R1 R2
  rw [show off F (8 * 26) = off F sLo from rfl] at R2
  have h17 : ((v.mem.writeW (off F sC) (maskV x)).writeW (off F sLo) (BitVec.ofNat 64 (loV x))).readW
      (off F sK) 64 = BitVec.ofNat 64 k := by
    have := R2.fr 17 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hk, ← this]; rfl
  have h15' : ((v.mem.writeW (off F sC) (maskV x)).writeW (off F sLo) (BitVec.ofNat 64 (loV x))).readW
      (off F sHd) 64 = BitVec.ofNat 64 D := by
    have := R2.fr 15 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← h15, ← this]; rfl
  refine WP.mono (WP.keep [.rax, .r9] (Q := fun w => w.mem = (v.mem.writeW (off F sC) (maskV x)).writeW (off F sLo)
      (BitVec.ofNat 64 (loV x)) ∧ w.gpr .rax = BitVec.ofNat 64 (k - loV x) ∧
      w.cf = some (decide (k - loV x < D + 2))) ?_ rfl) fun w ⟨⟨hm, ha, hc⟩, kw⟩ => ?_
  · xrun [ea_sp, Lv.rsp, Lv.st (d := sC) (by decide), Lv.st (d := sLo) (by decide), Lv.ld (d := sK) (by decide),
      Lv.ld (d := sHd) (by decide), hdv, h8v, h17, h15', VG.Offset.ofNat_sub_ofNat (show loV x ≤ k by omega),
      ofNat_add_lit]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨Lv.congr (kw.gpr (by decide)) kw.2.2 ?_, (kv.trans kw).mono (by decide), hm ▸ R2, ha, hc⟩
  have h1 := R2.fr 21 (by decide)
  rw [← hm] at h1
  rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, Rv.fr 21 (by decide)]
  simp [upd]

theorem saltFitsAny_ok {D : Nat} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) (h15 : W 15 = BitVec.ofNat 64 D) {a : Nat} {b : BitVec 64}
    (ha : D + 2 ≤ a) (ha' : a < 2 ^ 32) (hax : u.gpr .rax = BitVec.ofNat 64 a) (hdx : u.gpr .rdx = b) :
    WP isa (.block saltFitsAny) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rax = BitVec.ofNat 64 (a - (D + 2)) ∧ u'.cf = some (decide (a - (D + 2) < b.toNat)) := by
  have h15' : u.mem.readW (off F sHd) 64 = BitVec.ofNat 64 D := by rw [R.rd (d := sHd) 15 rfl (by decide), h15]
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rax = BitVec.ofNat 64 (a - (D + 2)) ∧
    u'.cf = some (decide (a - (D + 2) < b.toNat))) ?_ rfl) fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [saltFitsAny, ea_sp, L.rsp, L.ld (d := sHd) (by decide), h15', hax, hdx,
    VG.Offset.ofNat_sub_ofNat (show D ≤ a by omega), VG.Proof.MlKem.X86_64.sx_ofNat (show 2 < 2 ^ 31 by decide)]
  have e : BitVec.ofNat 64 (a - D) - 2 = BitVec.ofNat 64 (a - (D + 2)) := by
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, VG.Offset.ofNat_sub_ofNat (by omega),
      show a - D - 2 = a - (D + 2) by omega]
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨rfl, rfl⟩

end VG.Proof.RsaPss.X86_64.Any
