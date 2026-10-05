import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
import VerifiedGarbage.Proof.RsaPss.MgfBytes

/-!
# RSASSA-PSS on x86-64: MGF1

`mgfXor` XORs `MGF1(H, dbLen)` into `DB`, the `dbLen` bytes at
`scratch + e`, where `H` is the `hLen` bytes after them (`mgfXor_ok`): for
each counter `c`, `H ‖ I2OSP(c, 4)` is written to `Y` (`clearBlock`,
`copyH`, `counter`), hashed (`ctHash`), and the first
`min(hLen, dbLen - c hLen)` bytes of its digest XORed into `DB` at `c hLen`
(`xorOut`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off Scr off_off ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {H : Hash} (hH : HashOK H) (K : Callees H)

include hH in
theorem mgfNb_spec : H.D + 4 + 1 + H.P.L ≤ mgfNb H * H.P.B ∧ mgfNb H * H.P.B ≤ 256 := by
  have hB := hH.dims.B
  have hDL := hH.hDL
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  unfold mgfNb
  have hB0 : 0 < H.P.B := by omega
  have := Nat.lt_div_mul_add (a := H.D + 4 + H.P.L) (b := H.P.B) hB0
  have h1 : (H.D + 4 + H.P.L) / H.P.B ≤ 1 := Nat.div_le_of_le_mul (by rcases hB with h | h <;> rw [h] <;> omega)
  refine ⟨by rw [Nat.succ_mul]; omega, ?_⟩
  have : ((H.D + 4 + H.P.L) / H.P.B + 1) * H.P.B ≤ 2 * H.P.B := Nat.mul_le_mul_right _ (by omega)
  rcases hB with h | h <;> rw [h] at this ⊢ <;> omega

/-! ## `H ‖ C` in `Y` -/

include hH in
theorem clearBlock_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa (clearBlock H) u fun u' => Lay u' F S ∧ Keep [.rcx, .rax, .r8] u u' ∧ u'.gpr .rcx = off S oY ∧
      Rep u'.mem F S (clrV V oY (mgfNb H * H.P.B)) W := by
  obtain ⟨_, hnb⟩ := mgfNb_spec hH
  have hB := hH.dims.B
  have h8 : mgfNb H * H.P.B % 8 = 0 := by
    rcases hB with h | h <;> rw [h] <;> generalize mgfNb H = a <;> omega
  have hpos : 0 < mgfNb H * H.P.B := Nat.mul_pos (Nat.succ_pos _) hH.B_pos
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax, .r8] (Q := fun v => v.gpr .rcx = off S oY ∧ v.gpr .rax = 0 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, hm⟩, hk⟩ => ?_)
  · have hs := L.slot
    simp only [Bignum.X86_64.word] at hs
    xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (clearQ_ok Lv (hm ▸ R) hpos h8 (by unfold oY oRsa; omega) (by omega) h₁ h₂ h₃)
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), (kw.gpr (by decide)).trans h₁, Rw⟩

/-- Where `DB` and `H` are: `DB` the `db` bytes at `scratch + e`, `H` the
`hLen` after them, within `EM`'s place. -/
structure DbAt (D e db : Nat) : Prop where
  e1 : oEm ≤ e
  db1 : 1 ≤ db
  fit : e + db + D ≤ oEm + 1024

include hH in
theorem copyH_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (hd : DbAt H.D e db) (he : W 23 = off S e)
    (hdb : W 24 = BitVec.ofNat 64 db) (hcx : u.gpr .rcx = off S oY) :
    WP isa (copyH H) u fun u' => Lay u' F S ∧ Keep [.rsi, .r8, .rax] u u' ∧
      Rep u'.mem F S (cpV V (fun i => V (e + db + i)) oY H.D) W := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have h23 : u.mem.readW (off F sEb) 64 = off S e := by rw [← he, ← R.fr 23 (by decide)]; rfl
  have h24 : u.mem.readW (off F sDb) 64 = BitVec.ofNat 64 db := by rw [← hdb, ← R.fr 24 (by decide)]; rfl
  refine WP.seq (WP.mono (WP.keep [.rsi, .r8] (Q := fun v => v.gpr .rsi = off S (e + db) ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, hm⟩, hk⟩ => ?_)
  · xrun [copyH, ea_sp, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide), h23, h24]
    exact off_off S e db
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  have hfit := hd.fit
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have hcp := copy_ok Lv Rv (d := .rcx) (by decide) (p := off S (e + db)) (o := oY) (disp := 0) (n := H.D)
    (stepI_ok (show H.D < 2 ^ 31 by omega) v [.rax, .r8]) hD (by unfold oRsa; omega) h₁
    ((hk.gpr (by decide)).trans hcx) h₂
    (fun i hi => by rw [off_plus]; exact Lv.sld8 (by unfold oRsa; omega))
    (fun i hi j hj => by
      rw [off_plus]; exact Offset.add_ofNat_ne S (by omega) (by omega) (by omega))
  refine WP.mono hcp fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), ?_⟩
  refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
  simp only [cpV, Nat.add_zero]
  split
  · rw [off_plus, Rv.scr _ (by unfold oRsa; omega)]
  · rfl

/-- `Y` with the counter `c` after `H`. -/
def ctrV (D : Nat) (V : Nat → Byte) (c : Nat) (x : Nat) : Byte :=
  if oY + D ≤ x ∧ x < oY + D + 4 then (Spec.Rsa.i2osp c 4).getD (x - (oY + D)) 0 else V x

theorem trunc_ofNat (x : Nat) : BitVec.setWidth 8 (BitVec.ofNat 64 x) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

include hH in
theorem counter_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {c : Nat} (hc : W 31 = BitVec.ofNat 64 c) (hc32 : c < 2 ^ 32)
    (hcx : u.gpr .rcx = off S oY) :
    WP isa (.block (counter H)) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      Rep u'.mem F S (ctrV H.D V c)
        (upd (upd W 27 (BitVec.ofNat 64 (H.D + 4))) 28 (BitVec.ofNat 64 (mgfNb H))) := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  obtain ⟨_, hnb⟩ := mgfNb_spec hH
  have hmg : mgfNb H ≤ 256 := Nat.le_trans (Nat.le_mul_of_pos_right _ hH.B_pos) hnb
  have h31 : u.mem.readW (off F sCtr) 64 = BitVec.ofNat 64 c := by rw [← hc, ← R.fr 31 (by decide)]; rfl
  have G := L.geo
  -- The bytes, most significant first.
  have R1 := (((R.wb G (o := oY + (H.D + 3)) (by unfold oY oRsa; omega) (BitVec.ofNat 8 c)).wb G
    (o := oY + (H.D + 2)) (by unfold oY oRsa; omega) (BitVec.ofNat 8 (c / 2 ^ 8))).wb G
    (o := oY + (H.D + 1)) (by unfold oY oRsa; omega) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).wb G
    (o := oY + H.D) (by unfold oY oRsa; omega) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))
  have R2 := (R1.wf G (k := 27) (by decide) (BitVec.ofNat 64 (H.D + 4))).wf G (k := 28) (by decide)
    (BitVec.ofNat 64 (mgfNb H))
  rw [show off F (8 * 27) = off F sL from rfl, show off F (8 * 28) = off F sNb from rfl] at R2
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem =
      (((((u.mem.writeW (off S (oY + (H.D + 3))) (BitVec.ofNat 8 c)).writeW (off S (oY + (H.D + 2)))
        (BitVec.ofNat 8 (c / 2 ^ 8))).writeW (off S (oY + (H.D + 1))) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).writeW
        (off S (oY + H.D)) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))).writeW (off F sL)
        (BitVec.ofNat 64 (H.D + 4))).writeW (off F sNb) (BitVec.ofNat 64 (mgfNb H))) ?_ rfl)
    fun u' ⟨hm, hk⟩ => ⟨?_, hk, hm ▸ ?_⟩
  · xrun [counter, ea_at, ea_sp, hcx, L.rsp, L.ld (d := sCtr) (by decide), h31, off_off,
      L.sst8 (d := oY + (H.D + 3)) (by unfold oY oRsa; omega), L.sst8 (d := oY + (H.D + 2)) (by unfold oY oRsa; omega),
      L.sst8 (d := oY + (H.D + 1)) (by unfold oY oRsa; omega), L.sst8 (d := oY + H.D) (by unfold oY oRsa; omega),
      L.st (d := sL) (by decide), L.st (d := sNb) (by decide), trunc_ofNat,
      shr_ofNat 8 (show c < 2 ^ 64 by omega), shr_ofNat 8 (show c / 2 ^ 8 < 2 ^ 64 by omega),
      shr_ofNat 8 (show c / 2 ^ 8 / 2 ^ 8 < 2 ^ 64 by omega),
      zx32 (show H.D + 4 < 2 ^ 32 by omega), zx32 (show mgfNb H < 2 ^ 32 by omega)]
  · refine L.congr (hk.gpr (by decide)) hk.2.2 ?_
    have h1 := R2.fr 21 (by decide)
    rw [← hm] at h1
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, R.fr 21 (by decide)]
    simp [upd]
  · refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R2
    have e1 : c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 3 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    have e2 : c / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 2 := by rw [Nat.div_div_eq_div_mul]
    have e3 : c / 2 ^ 8 = c / 256 ^ 1 := rfl
    have e4 : c = c / 256 ^ 0 := by simp
    simp only [upd, ctrV, Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases (show x = oY + H.D ∨ x = oY + (H.D + 1) ∨ x = oY + (H.D + 2) ∨ x = oY + (H.D + 3) ∨
        ¬(oY + H.D ≤ x ∧ x < oY + H.D + 4) by omega) with h | h | h | h | h
    · subst h; simp [e1]
    · subst h
      simp [e2, show oY + (H.D + 1) - (oY + H.D) = 1 by omega, show oY + (H.D + 1) < oY + H.D + 4 by omega]
    · subst h
      simp [e3, show oY + (H.D + 2) - (oY + H.D) = 2 by omega, show oY + (H.D + 2) < oY + H.D + 4 by omega]
    · subst h
      simp [show oY + (H.D + 3) - (oY + H.D) = 3 by omega, show oY + (H.D + 3) < oY + H.D + 4 by omega]
    · rw [ifn h, ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]

end VG.Proof.RsaPss.X86_64
