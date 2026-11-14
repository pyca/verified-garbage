module
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk

/-! ### `RsaPss.AArch64.VerifyScan`, which only this module used -/

section

/-!
# RSASSA-PSS verification on AArch64: the first nonzero byte of `DB`

`posScan` visits every byte of `DB` and keeps, under masks, the index and
the value of the first nonzero one, and a mask of all ones while there is
none (`posScan_ok`), which is the number of leading zero octets `lz`
(`lz_of_nz`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsr wp_ldrb wp_and wp_orr
  wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov wp_countdown)
open VG.Proof.RsaPss (lz)

/-- The first index below `j` at which `f` is not zero. -/
def nz (f : Nat → Byte) : Nat → Option Nat
  | 0 => none
  | j + 1 => match nz f j with
    | some i => some i
    | none => if f j = 0 then none else some j

theorem nz_none {f : Nat → Byte} : ∀ {j : Nat}, nz f j = none → ∀ i < j, f i = 0
  | 0, _, _, hi => absurd hi (by omega_using [])
  | j + 1, h, i, hi => by
    simp only [nz] at h
    split at h
    · cases h
    · rename_i h'
      by_cases e : f j = 0
      · rcases (by omega_using [hi] : i < j ∨ i = j) with hl | rfl
        · exact nz_none h' i hl
        · exact e
      · rw [ite_eq_right e] at h; cases h

theorem nz_some {f : Nat → Byte} : ∀ {j i : Nat}, nz f j = some i → i < j ∧ f i ≠ 0 ∧ ∀ k < i, f k = 0
  | 0, _, h => by cases h
  | j + 1, i, h => by
    simp only [nz] at h
    split at h
    · rename_i i' h'
      cases h
      obtain ⟨a, b, c⟩ := nz_some h'
      exact ⟨by omega_using [a], b, c⟩
    · rename_i h'
      by_cases e : f j = 0
      · rw [ite_eq_left e] at h; cases h
      · rw [ite_eq_right e] at h
        cases h
        exact ⟨by omega_using [], e, nz_none h'⟩

/-- The value of the first nonzero byte, or 0. -/
def nzV (f : Nat → Byte) (j : Nat) : Byte :=
  match nz f j with
  | some i => f i
  | none => 0

theorem zero_bit (b : Byte) : (BitVec.setWidth 64 b - BitVec.ofNat 64 1) >>> 63 = if b = 0 then 1#64 else 0#64 := by
  by_cases h : b = 0
  · subst h; rw [ite_eq_left rfl]; decide
  · rw [ite_eq_right h]
    have h' : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    have := b.isLt
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega_using [])]
    exact Nat.div_eq_of_lt (by omega_using [h'])

theorem posScan_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {e db : Nat}
    (he : e + db ≤ oRsa) (hdb : 0 < db) (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) :
    WP isa posScan t fun t' => Only [.x10, .x11, .x12, .x13, .x14, .x15, .x9, .x8, .x16, .x17] t t' ∧
      t'.gpr .x13 = (if nz (fun i => V (e + i)) db = none then BitVec.allOnes 64 else 0) ∧
      t'.gpr .x14 = BitVec.ofNat 64 ((nz (fun i => V (e + i)) db).getD 0) ∧
      t'.gpr .x15 = (nzV (fun i => V (e + i)) db).setWidth 64 := by
  have c6 : oRsa = 8192 := rfl
  unfold posScan
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x10, .x11, .x12, .x13, .x14, .x15] t u ∧
      u.gpr .x10 = off S e ∧ u.gpr .x11 = 0#64 ∧ u.gpr .x12 = BitVec.ofNat 64 db ∧ u.gpr .x13 = BitVec.allOnes 64 ∧
      u.gpr .x14 = 0#64 ∧ u.gpr .x15 = 0#64) ?_ fun u ⟨O, h10, h11, h12, h13, h14, h15⟩ => ?_)
  · refine wp_mov fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_movz fun u₄ o₄ e₄ =>
      wp_subImm (by decide) fun u₅ o₅ e₅ => wp_movz fun u₆ o₆ e₆ => wp_movz fun u₇ o₇ e₇ => wp_nil
        ⟨(o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₇.get .x10, o₆.get .x10, o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, h24]
    · rw [o₇.get .x11, o₆.get .x11, o₅.get .x11, o₄.get .x11, o₃.get .x11, e₂]; rfl
    · rw [o₇.get .x12, o₆.get .x12, o₅.get .x12, o₄.get .x12, e₃, o₂.get .x25, o₁.get .x25, h25]
    · rw [o₇.get .x13, o₆.get .x13, e₅, e₄]; rfl
    · rw [o₇.get .x14, e₆]; rfl
    · rw [e₇]; rfl
  have Ru : Rep u.mem S V := O.mem ▸ R
  have Lu : Lay u F S := L.congr O.sp O.wr (O.get .x20)
  refine WP.mono (wp_countdown (cnt := .x12) (N := db) (by omega_using [he, c6]) hdb
    (fun j v => Only [.x9, .x8, .x16, .x17, .x10, .x11, .x12, .x13, .x14, .x15] u v ∧
      v.gpr .x10 = off S (e + j) ∧ v.gpr .x11 = BitVec.ofNat 64 j ∧
      v.gpr .x13 = (if nz (fun i => V (e + i)) j = none then BitVec.allOnes 64 else 0) ∧
      v.gpr .x14 = BitVec.ofNat 64 ((nz (fun i => V (e + i)) j).getD 0) ∧
      v.gpr .x15 = (nzV (fun i => V (e + i)) j).setWidth 64)
    (fun j hj v ⟨hO, h10', h11', h13', h14', h15'⟩ _ => ?_)
    ⟨Only.refl _ _, by rw [Nat.add_zero, h10], h11, by rw [h13]; rfl, by rw [h14]; rfl, by rw [h15]; rfl⟩ h12)
    fun v ⟨hO, _, _, h13', h14', h15'⟩ => ⟨(O.trans hO).mono, h13', h14', h15'⟩
  refine wp_ldrb (by decide) (by rw [h10', BitVec.add_zero]) (by rw [hO.rd, hO.wr]; exact Lu.ld (by omega_using [he, hj]))
    fun w₁ q₁ g₁ => ?_
  refine wp_subImm (by decide) fun w₂ q₂ g₂ => wp_lsr (by decide) fun w₃ q₃ g₃ => wp_subImm (by decide) fun w₄ q₄ g₄ =>
    wp_and fun w₅ q₅ g₅ => wp_and fun w₆ q₆ g₆ => wp_orr fun w₇ q₇ g₇ => wp_and fun w₈ q₈ g₈ =>
    wp_orr fun w₉ q₉ g₉ => wp_movz fun w₁₀ q₁₀ g₁₀ => wp_sub fun w₁₁ q₁₁ g₁₁ => wp_and fun w₁₂ q₁₂ g₁₂ =>
    wp_addImm (by decide) fun w₁₃ q₁₃ g₁₃ => wp_addImm (by decide) fun w₁₄ q₁₄ g₁₄ =>
    wp_subImm (by decide) fun w₁₅ q₁₅ g₁₅ => wp_nil ?_
  have Q : Only [.x9, .x8, .x16, .x17, .x14, .x15, .x13, .x10, .x11, .x12] v w₁₅ :=
    (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans (q₆.trans (q₇.trans (q₈.trans (q₉.trans (q₁₀.trans
      (q₁₁.trans (q₁₂.trans (q₁₃.trans (q₁₄.trans q₁₅)))))))))))))).mono
  generalize hb : V (e + j) = b
  have v9 : w₁.gpr .x9 = b.setWidth 64 := by rw [g₁, hO.mem, Ru _ (by omega_using [he, hj]), hb]
  have v8 : w₃.gpr .x8 = if b = 0 then 1#64 else 0#64 := by rw [g₃, g₂, v9, zero_bit]
  have v16 : w₅.gpr .x16 = (w₃.gpr .x8 - BitVec.ofNat 64 1) &&& v.gpr .x13 := by
    rw [g₅, g₄, q₄.get .x13, q₃.get .x13, q₂.get .x13, q₁.get .x13]
  have v14 : w₁₅.gpr .x14 = v.gpr .x14 ||| (BitVec.ofNat 64 j &&& w₅.gpr .x16) := by
    rw [q₁₅.get .x14, q₁₄.get .x14, q₁₃.get .x14, q₁₂.get .x14, q₁₁.get .x14, q₁₀.get .x14, q₉.get .x14,
      q₈.get .x14, g₇, g₆, q₆.get .x14, q₅.get .x14, q₄.get .x14, q₃.get .x14, q₂.get .x14, q₁.get .x14,
      q₅.get .x11, q₄.get .x11, q₃.get .x11, q₂.get .x11, q₁.get .x11, h11']
  have v15 : w₁₅.gpr .x15 = v.gpr .x15 ||| (b.setWidth 64 &&& w₅.gpr .x16) := by
    rw [q₁₅.get .x15, q₁₄.get .x15, q₁₃.get .x15, q₁₂.get .x15, q₁₁.get .x15, q₁₀.get .x15, g₉, g₈,
      q₈.get .x15, q₇.get .x15, q₆.get .x15, q₅.get .x15, q₄.get .x15, q₃.get .x15, q₂.get .x15, q₁.get .x15,
      q₇.get .x9, q₆.get .x9, q₅.get .x9, q₄.get .x9, q₃.get .x9, q₂.get .x9, v9, q₇.get .x16, q₆.get .x16]
  have v13 : w₁₅.gpr .x13 = v.gpr .x13 &&& (0#64 - w₃.gpr .x8) := by
    rw [q₁₅.get .x13, q₁₄.get .x13, q₁₃.get .x13, g₁₂, q₁₁.get .x13, q₁₀.get .x13, q₉.get .x13, q₈.get .x13,
      q₇.get .x13, q₆.get .x13, q₅.get .x13, q₄.get .x13, q₃.get .x13, q₂.get .x13, q₁.get .x13, g₁₁, g₁₀,
      q₁₀.get .x8, q₉.get .x8, q₈.get .x8, q₇.get .x8, q₆.get .x8, q₅.get .x8, q₄.get .x8]
    rfl
  have x10 : w₁₅.gpr .x10 = off S (e + (j + 1)) := by
    rw [q₁₅.get .x10, q₁₄.get .x10, g₁₃, q₁₂.get .x10, q₁₁.get .x10, q₁₀.get .x10, q₉.get .x10, q₈.get .x10,
      q₇.get .x10, q₆.get .x10, q₅.get .x10, q₄.get .x10, q₃.get .x10, q₂.get .x10, q₁.get .x10, h10', off_add,
      Nat.add_assoc]
  have x11 : w₁₅.gpr .x11 = BitVec.ofNat 64 (j + 1) := by
    rw [q₁₅.get .x11, g₁₄, q₁₃.get .x11, q₁₂.get .x11, q₁₁.get .x11, q₁₀.get .x11, q₉.get .x11, q₈.get .x11,
      q₇.get .x11, q₆.get .x11, q₅.get .x11, q₄.get .x11, q₃.get .x11, q₂.get .x11, q₁.get .x11, h11',
      BitVec.ofNat_add_ofNat]
  have x12 : w₁₅.gpr .x12 = v.gpr .x12 - BitVec.ofNat 64 1 := by
    rw [g₁₅, q₁₄.get .x12, q₁₃.get .x12, q₁₂.get .x12, q₁₁.get .x12, q₁₀.get .x12, q₉.get .x12, q₈.get .x12,
      q₇.get .x12, q₆.get .x12, q₅.get .x12, q₄.get .x12, q₃.get .x12, q₂.get .x12, q₁.get .x12]
  suffices key : w₁₅.gpr .x13 = (if nz (fun i => V (e + i)) (j + 1) = none then BitVec.allOnes 64 else 0) ∧
      w₁₅.gpr .x14 = BitVec.ofNat 64 ((nz (fun i => V (e + i)) (j + 1)).getD 0) ∧
      w₁₅.gpr .x15 = (nzV (fun i => V (e + i)) (j + 1)).setWidth 64 from
    ⟨⟨(hO.trans Q).mono, x10, x11, key.1, key.2.1, key.2.2⟩, x12⟩
  have hS : ∀ i, nz (fun i => V (e + i)) j = some i → nz (fun i => V (e + i)) (j + 1) = some i := fun i h => by
    simp only [nz, h]
  have hN0 : nz (fun i => V (e + i)) j = none → b = 0 → nz (fun i => V (e + i)) (j + 1) = none := fun h h0 => by
    simp only [nz, h, hb, h0, ite_true]
  have hN1 : nz (fun i => V (e + i)) j = none → b ≠ 0 → nz (fun i => V (e + i)) (j + 1) = some j := fun h h0 => by
    simp only [nz, h, hb, h0, ite_false]
  have az : ∀ x : BitVec 64, x &&& 0 = 0 := fun x => by ext i; simp
  have za : ∀ x : BitVec 64, 0 &&& x = 0 := fun x => by ext i; simp
  have oz : ∀ x : BitVec 64, x ||| 0 = x := fun x => by ext i; simp
  have zo : ∀ x : BitVec 64, 0 ||| x = x := fun x => by ext i; simp
  have aa : ∀ x : BitVec 64, x &&& BitVec.allOnes 64 = x := fun x => BitVec.and_allOnes
  have hb0 : (1#64 - BitVec.ofNat 64 1) = 0 := rfl
  have hb1 : (0#64 - BitVec.ofNat 64 1) = BitVec.allOnes 64 := rfl
  by_cases hN : nz (fun i => V (e + i)) j = none
  · rw [hN, ite_eq_left rfl] at h13'
    rw [hN] at h14'
    have h15'' : v.gpr .x15 = 0 := by rw [h15']; simp only [nzV, hN]; rfl
    by_cases b0 : b = 0
    · have e1 := hN0 hN b0
      rw [v8, ite_eq_left b0] at v16
      rw [v16, hb0, za] at v14 v15
      refine ⟨by rw [v13, h13', v8, ite_eq_left b0, e1, ite_eq_left rfl]; rfl, by rw [v14, h14', az, oz, e1],
        by rw [v15, h15'', az, oz]; simp only [nzV, e1]; rfl⟩
    · have e1 := hN1 hN b0
      rw [v8, ite_eq_right b0, hb1, h13', aa] at v16
      rw [v16] at v14 v15
      refine ⟨by rw [v13, h13', v8, ite_eq_right b0, e1]; rfl, by rw [v14, h14', aa]; simp [e1],
        by rw [v15, h15'', aa, zo]; simp only [nzV, e1, hb]⟩
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hN
    have e1 := hS i hi
    rw [hi] at h13' h14'
    rw [h13', ite_eq_right (by simp), az] at v16
    rw [v16, az, oz] at v14 v15
    refine ⟨by rw [v13, h13', ite_eq_right (by simp), za, e1]; rfl, by rw [v14, h14', e1],
      by rw [v15, h15']; simp only [nzV, hi, e1]⟩

end VG.Proof.RsaPss.AArch64

end

end


/-!
# RSASSA-PSS verification on AArch64: unmasking `DB`

From RSAVP1's result in `EM`: the first checks into `acc` (`acc0`), `DB`
unmasked (`mgfXor`) and its top bits cleared (`clearTop`), its first
nonzero byte found (`posScan`) and checked (`posCheck`): `b1_ok`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- `EM` after the mask and `clearTop`, from `V`, with `DB` at `e`. -/
def wct (V : Nat → Byte) (mk : List Byte) (e db : Nat) (c : Byte) : Nat → Byte :=
  upd (mixV V mk e db) e (mixV V mk e db e &&& c)

/-- The mask: MGF1 of `H`, the `hLen` bytes after `DB`. -/
def mkB (G : Spec.Mgf1.Hash) (D : Nat) (V : Nat → Byte) (e db : Nat) : List Byte :=
  Spec.Mgf1.mgf1 G ((List.range D).map fun i => V (e + db + i)) db

/-- `acc` after `acc0`. -/
def acc0V (V : Nat → Byte) (k lo : Nat) (c : Byte) : BitVec 64 :=
  ((V (oEm + k - 1)).setWidth 64 ^^^ BitVec.ofNat 64 0xbc) |||
    ((V oEm).setWidth 64 &&& (0#64 - BitVec.ofNat 64 lo)) |||
    ((V (oEm + lo)).setWidth 64 &&& (c.setWidth 64 ^^^ BitVec.ofNat 64 0xFF))

/-- `acc` after `posCheck`, for `DB`'s bytes `f`. -/
def acc1V (a0 : BitVec 64) (f : Nat → Byte) (db : Nat) (any sv : BitVec 64) : BitVec 64 :=
  (a0 ||| (((nzV f db).setWidth 64 ^^^ 1#64) |||
    (if nz f db = none then BitVec.allOnes 64 else 0) >>> 63)) |||
    (if any = 0 then sv ^^^ BitVec.ofNat 64 (db - (nz f db).getD 0 - 1) else 0)

/-- After `posCheck`. -/
structure B1 (G : Spec.Mgf1.Hash) (D : Nat) (t : State) (F S : Addr) (V : Nat → Byte) (k lo db : Nat) (c : Byte)
    (any sv : BitVec 64) (u : State) : Prop where
  sp : u.sp = t.sp
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u.gpr r = t.gpr r
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  fr : Frame (mgfWr F S ++ [slotR F sPos]) t.mem u.mem
  em : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c o
  pos : u.mem.readW (off F sPos) 64 =
    BitVec.ofNat 64 ((nz (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db).getD 0)
  acc : u.gpr .x26 = acc1V (acc0V V k lo c)
    (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db any sv
  sy : u.syms = t.syms

theorem nz_congr {f g : Nat → Byte} : ∀ {j : Nat}, (∀ i < j, f i = g i) → nz f j = nz g j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [nz]
    rw [nz_congr (fun i hi => h i (by omega_using [hi])), h j (by omega_using [])]

theorem nzV_congr {f g : Nat → Byte} {j : Nat} (h : ∀ i < j, f i = g i) : nzV f j = nzV g j := by
  unfold nzV
  rw [← nz_congr h]
  split
  · rename_i i hi
    exact h i (nz_some hi).1
  · rfl

theorem nz_lt {f : Nat → Byte} {j : Nat} (hj : 0 < j) : (nz f j).getD 0 < j := by
  cases h : nz f j with
  | none => exact hj
  | some i => exact (nz_some h).1

section
variable {Gm : Impl.Pbkdf2.Md.AArch64.Stream} (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm)
  {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D) (hGv : Proof.Mgf1.Valid Gs)
  {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hGh hGl hGv in
/-- From RSAVP1's result in `EM` (`V`), `DB` at `oEm + lo`, to `B1`. -/
theorem b1_ok {H : Hash} {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {k lo db : Nat} {c : Byte} {any sv : BitVec 64} (hk : lo + db + H.D + 1 = k) (hdb : 1 ≤ db)
    (hk2 : k ≤ 1024) (hlo : lo ≤ 1)
    (h23 : t.gpr .x23 = BitVec.ofNat 64 k) (h24 : t.gpr .x24 = off S (oEm + lo))
    (h25 : t.gpr .x25 = BitVec.ofNat 64 db) (hLo : t.mem.readW (off F sLo) 64 = BitVec.ofNat 64 lo)
    (hC : t.mem.readW (off F sC) 64 = c.setWidth 64) (hA : t.mem.readW (off F sAny) 64 = any)
    (hS : t.mem.readW (off F sSaltLen) 64 = sv) {p : Addr} (E : Env Gm g t F S p) {rest : Prog isa}
    {Q : State → Prop} (hQ : ∀ u, B1 Gs H.D t F S V k lo db c any sv u → WP isa rest u Q) :
    WP isa (seqs [.block acc0, mgfXor H g, .block clearTop, posScan, posCheck, rest]) t Q := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  have hW : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      ∀ {m : Mem}, Frame (mgfWr F S) t.mem m → m.readW (off F d) 64 = t.mem.readW (off F d) 64 :=
    fun hd h1 h2 _ hf => slot_keep hf (L.slotW hd h1 h2)
  unfold seqs seqs seqs seqs seqs
  -- `acc0`.
  refine WP.seq (WP.mono_syms (acc0_ok L R (by omega_using [hk]) hk2 hlo h23 h24 hLo hC) fun u1 ⟨O1, x26₁⟩ sy1 => ?_)
  have L1 := L.congr O1.sp O1.wr (O1.get .x20)
  have R1 : Rep u1.mem S V := O1.mem ▸ R
  have E1 : Env Gm g u1 F S p := E.step L (by rw [O1.mem]; exact Frame.refl _ _) O1.rd O1.wr sy1
  -- The mask.
  refine WP.seq (WP.mono (mgfXor_ok hGm hGh hGl hGv L1 R1 (e := oEm + lo) (db := db) ⟨by omega_using [], hdb, by omega_using [hk, hk2, c1, c2]⟩
    (by rw [O1.get .x24, h24]) (by rw [O1.get .x25, h25]) E1)
    fun u2 ⟨sp2, rd2, wr2, cs2, v2, fr2, sy2, em2⟩ => ?_)
  have L2 := L1.congr sp2 wr2 (cs2 .x20 (by decide) (by decide))
  have F2 : Frame (mgfWr F S) t.mem u2.mem := by rw [O1.mem] at fr2; exact fr2
  -- `DB`'s top bits.
  refine WP.seq (WP.mono_syms (clearTop_ok L2 (fun _ _ => rfl) (e := oEm + lo) (c := c)
    (by rw [cs2 .x24 (by decide) (by decide), O1.get .x24, h24]) (by omega_using [hlo, c1, c6])
    (by rw [hW (by decide) (by decide) (by decide) F2, hC])) fun u3 ⟨k3, f3, R3⟩ sy3 => ?_)
  have L3 := L2.congr k3.sp k3.wr (k3.get .x20)
  have hX : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      u3.mem.readW (off F d) 64 = t.mem.readW (off F d) 64 := fun hd h1 h2 => by
    rw [slot_keep f3 (L.slotSd hd), hW hd h1 h2 F2]
  -- The first nonzero byte.
  generalize hmk : mkB Gs H.D V (oEm + lo) db = mk
  have hmk' : Spec.Mgf1.mgf1 Gs ((List.range H.D).map fun i => V (oEm + lo + db + i)) db = mk := hmk
  rw [hmk'] at em2
  have hv : ∀ o, oEm ≤ o → o < oY →
      upd (fun o => u2.mem (off S o)) (oEm + lo) (u2.mem (off S (oEm + lo)) &&& c) o =
        wct V mk (oEm + lo) db c o := fun o h1 h2 => by
    unfold wct upd
    simp only []
    rw [em2 o h1 h2, em2 (oEm + lo) (by omega_using []) (by omega_using [hlo, c1, c2])]
  have hf : ∀ i < db, upd (fun o => u2.mem (off S o)) (oEm + lo) (u2.mem (off S (oEm + lo)) &&& c) (oEm + lo + i) =
      wct V mk (oEm + lo) db c (oEm + lo + i) := fun i hi => hv _ (by omega_using []) (by omega_using [hk, hk2, c1, c2, hi])
  refine WP.seq (WP.mono_syms (posScan_ok L3 R3 (e := oEm + lo) (db := db) (by omega_using [hk, hk2, c1, c6]) (by omega_using [hdb])
    (by rw [k3.get .x24, cs2 .x24 (by decide) (by decide), O1.get .x24, h24])
    (by rw [k3.get .x25, cs2 .x25 (by decide) (by decide), O1.get .x25, h25])) fun u4 ⟨O4, x13₄, x14₄, x15₄⟩ sy4 => ?_)
  rw [nz_congr hf] at x13₄ x14₄
  rw [nzV_congr hf] at x15₄
  have L4 := L3.congr O4.sp O4.wr (O4.get .x20)
  -- Its checks.
  refine WP.seq (WP.mono_syms (posCheck_ok L4 x13₄ x14₄ x15₄ (acc := acc0V V k lo c) (any := any) (sv := sv)
    (by rw [O4.get .x26, k3.get .x26, cs2 .x26 (by decide) (by decide), x26₁]; rfl)
    (by rw [O4.get .x25, k3.get .x25, cs2 .x25 (by decide) (by decide), O1.get .x25, h25]) (nz_lt (by omega_using [hdb]))
    (by rw [O4.mem, hX (by decide) (by decide) (by decide), hA])
    (by rw [O4.mem, hX (by decide) (by decide) (by decide), hS])) fun u5 ⟨k5, m5, x26₅⟩ sy5 => hQ u5 ?_)
  have R5 := R3.frame (m' := u5.mem) (rs := [slotR F sPos]) (by rw [m5, O4.mem]; exact frame_slot _ F sPos _)
    (L.slotS (by decide))
  subst hmk
  exact {
    sp := by rw [k5.sp, O4.sp, k3.sp, sp2, O1.sp]
    rd := by rw [k5.rd, O4.rd, k3.rd, rd2, O1.rd]
    wr := by rw [k5.wr, O4.wr, k3.wr, wr2, O1.wr]
    cs := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [k5.get _ (by decide), O4.get _ (by decide), k3.get _ (by decide), cs2 _ (by decide) (by decide),
          O1.get _ (by decide)]
    v := fun r hr => by rw [k5.vcs r hr, O4.vcs r hr, k3.vcs r hr, v2 r hr, O1.vcs r hr]
    fr := ((F2.mono (by simp)).trans ((f3.mono (by simp)).trans (by
      rw [m5, O4.mem]; exact (frame_slot _ F sPos _).mono (by simp))))
    em := fun o h1 h2 => by rw [R5 o (by omega_using [c2, c6, h2]), hv o h1 h2]
    pos := by rw [m5, Mem.readW_writeW_self64]
    acc := x26₅
    sy := by rw [sy5, sy4, sy3, sy2, sy1] }

end

end VG.Proof.RsaPss.AArch64
