module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS on x86-64: the encoding's parameters

`lo` and the mask of the top bits from the modulus' first byte (`loV`,
`maskV`); whether the salt fits (`saltFits_ok`); and `DB`'s slots
(`dbSlots_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)

/-- `lo = k - emLen`: 1 if `n₀ = 1`. -/
def loV (x : Nat) : Nat := if x = 1 then 1 else 0

/-- The mask `0xFF >>> z`, as a word. -/
def maskV (x : Nat) : BitVec 64 := if x = 1 then BitVec.ofNat 64 0xFF else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)

theorem saltFits_ok {H : Impl.Pbkdf2.Md.X86_64.Hash} (hD : H.D + 2 < 2 ^ 31) (u : State) {a : Nat} {b : BitVec 64}
    (ha : H.D + 2 ≤ a) (ha' : a < 2 ^ 32) (hax : u.gpr .rax = BitVec.ofNat 64 a) (hdx : u.gpr .rdx = b) :
    WP isa (.block (saltFits H)) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rax = BitVec.ofNat 64 (a - (H.D + 2)) ∧ u'.cf = some (decide (a - (H.D + 2) < b.toNat)) := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rax = BitVec.ofNat 64 (a - (H.D + 2)) ∧
    u'.cf = some (decide (a - (H.D + 2) < b.toNat))) ?_ rfl) fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [saltFits, hax, hdx, VG.Proof.MlKem.X86_64.sx_ofNat hD, VG.Offset.ofNat_sub_ofNat ha]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem dbSlots_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a lo : Nat} (hlo : W 26 = BitVec.ofNat 64 lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 a) :
    WP isa (.block dbSlots) u fun u' => Lay u' F S ∧ Keep [.rax, .rdx] u u' ∧
      Rep u'.mem F S V (upd (upd W 24 (BitVec.ofNat 64 (a + 1))) 23 (off S (oEm + lo))) := by
  have G := L.geo
  have hs := L.slot
  simp only [Bignum.word] at hs
  have R1 := R.wf G (k := 24) (by decide) (BitVec.ofNat 64 (a + 1))
  have R2 := R1.wf G (k := 23) (by decide) (off S (oEm + lo))
  rw [show off F (8 * 24) = off F sDb from rfl] at R1 R2
  rw [show off F (8 * 23) = off F sEb from rfl] at R2
  have h21 : (u.mem.writeW (off F sDb) (BitVec.ofNat 64 (a + 1))).readW (off F sScr) 64 = S := by
    have := R1.fr 21 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this
    rw [show (S : Addr) = W 21 from ((R.fr 21 (by decide)).symm.trans hs).symm, ← this]; rfl
  have h26 : (u.mem.writeW (off F sDb) (BitVec.ofNat 64 (a + 1))).readW (off F sLo) 64 = BitVec.ofNat 64 lo := by
    have := R1.fr 26 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hlo, ← this]; rfl
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u' => u'.mem = (u.mem.writeW (off F sDb)
      (BitVec.ofNat 64 (a + 1))).writeW (off F sEb) (off S (oEm + lo))) ?_ rfl) fun u' ⟨hm, k⟩ => ?_
  · xrun [dbSlots, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.st (d := sDb) (by decide),
      L.ld (d := sScr) (by decide), L.ld (d := sLo) (by decide), L.st (d := sEb) (by decide), hax, h21, h26,
      ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), off_plus]
  refine ⟨L.congr (k.gpr (by decide)) k.2.2 ?_, k, hm ▸ R2⟩
  have h1 := R2.fr 21 (by decide)
  rw [← hm] at h1
  rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, R.fr 21 (by decide)]
  simp [upd]

end VG.Proof.RsaPss.X86_64
