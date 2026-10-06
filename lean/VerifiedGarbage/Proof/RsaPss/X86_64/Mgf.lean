import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
import VerifiedGarbage.Proof.RsaPss.MgfBytes

/-!
# RSASSA-PSS on x86-64: MGF1

`mgfXor` XORs `MGF1(H, dbLen)` into `DB`, the `dbLen` bytes at
`scratch + e`, where `H` is the `hLen` bytes after them (`mgfXor_ok`): for
each counter `c`, `H ‖ I2OSP(c, 4)` is written to `Y` (`clearBlock`,
`copyH`, `counter`), hashed (`mgfHash`), and the first
`min(hLen, dbLen - c hLen)` bytes of its digest XORed into `DB` at `c hLen`
(`xorOut`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)
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
    simp only [Bignum.word] at hs
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

/-! ## The digest into `DB` -/

include hH in
theorem xorOut_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db done : Nat} (hd : DbAt H.D e db) (he : W 23 = off S e)
    (hdb : W 24 = BitVec.ofNat 64 db) (hdn : W 32 = BitVec.ofNat 64 done) (hlt : done < db) :
    WP isa (xorOut H) u fun u' => Lay u' F S ∧ Keep [.rcx, .rdi, .rax, .r10, .r8, .rdx] u u' ∧
      Rep u'.mem F S (xorV V oDig (e + done) (min H.D (db - done))) W := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hfit := hd.fit
  have he1 := hd.e1
  have c1 : oEm = 2560 := rfl
  have c3 : oDig = 2304 := rfl
  have hdbn : db < 2 ^ 63 := by omega
  have h23 : u.mem.readW (off F sEb) 64 = off S e := by rw [← he, ← R.fr 23 (by decide)]; rfl
  have h24 : u.mem.readW (off F sDb) 64 = BitVec.ofNat 64 db := by rw [← hdb, ← R.fr 24 (by decide)]; rfl
  have h32 : u.mem.readW (off F sDone) 64 = BitVec.ofNat 64 done := by rw [← hdn, ← R.fr 32 (by decide)]; rfl
  have hs := L.slot
  simp only [Bignum.word] at hs
  unfold xorOut seqs seqs seqs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdi, .rax, .r10, .rdx] (Q := fun v => v.gpr .rcx = off S oDig ∧
      v.gpr .rdi = off S (e + done) ∧ v.gpr .rax = BitVec.ofNat 64 (db - done) ∧
      v.gpr .r10 = BitVec.ofNat 64 H.D ∧ v.cf = some (decide (db - done < H.D)) ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk⟩ => ?_)
  · xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide), L.ld (d := sEb) (by decide),
      L.ld (d := sDone) (by decide), L.ld (d := sDb) (by decide), h23, h24, h32,
      VG.Offset.ofNat_sub_ofNat (show done ≤ db by omega), zx32 (show H.D < 2 ^ 32 by omega), off_plus]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  -- The count, `min(hLen, dbLen - done)`.
  have hmin : 0 < min H.D (db - done) := by omega
  refine WP.seq (WP.mono (Q := fun (w : State) => Keep [.r10] v w ∧ w.mem = v.mem ∧
      w.gpr .r10 = BitVec.ofNat 64 (min H.D (db - done))) ?_ fun w ⟨kw, hmw, h10⟩ => ?_)
  · refine WP.ite (M := isa) _ (show isa.eval .b v = _ from h₅) (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      refine WP.mono (WP.keep [.r10] (Q := fun w => w.mem = v.mem ∧ w.gpr .r10 = BitVec.ofNat 64 (db - done))
        ?_ rfl) fun w ⟨⟨hm', h'⟩, k'⟩ => ⟨k', hm', by rw [h', Nat.min_eq_right (by omega)]⟩
      xrun [h₃]
    · rw [decide_eq_false_iff_not] at hb
      refine WP.mono (WP.keep [] (Q := fun w => w = v) ?_ rfl) fun w ⟨hw, _⟩ => ?_
      · xrun
      · subst hw; exact ⟨Keep.refl _ _, rfl, by rw [h₄, Nat.min_eq_left (by omega)]⟩
  have Lw : Lay w F S := Lv.congr (kw.gpr (by decide)) kw.2.2 (by rw [hmw])
  have Rw : Rep w.mem F S V W := hmw ▸ Rv
  refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r8 = BitVec.ofNat 64 0 ∧ x.mem = w.mem) ?_ rfl)
    fun x ⟨⟨h8, hmx⟩, kx⟩ => ?_)
  · xrun
  have Lx : Lay x F S := Lw.congr (kx.gpr (by decide)) kx.2.2 (by rw [hmx])
  have Rx : Rep x.mem F S V W := hmx ▸ Rw
  have kvx := kw.trans kx
  refine WP.mono (xor_ok Lx Rx (a := oDig) (b := e + done) (n := min H.D (db - done))
    (stepR_ok (by omega) x (show Reg.r10 ∉ [Reg.rax, .rdx, .r8] by decide) (by decide)
      ((kx.gpr (by decide)).trans h10)) hmin (by unfold oRsa; omega) (by unfold oRsa; omega) (by omega)
    ((kvx.gpr (by decide)).trans h₁) ((kvx.gpr (by decide)).trans h₂) h8)
    fun y ⟨Ly, ky, Ry⟩ => ⟨Ly, ?_, Ry⟩
  exact (hk.trans (kvx.trans ky)).mono (by decide)

/-! ## The next counter -/

include hH in
theorem nextCtr_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {c done db : Nat} (hc : W 31 = BitVec.ofNat 64 c) (hdn : W 32 = BitVec.ofNat 64 done)
    (hdb : W 24 = BitVec.ofNat 64 db) (hd' : done + H.D < 2 ^ 32) (hdb' : db < 2 ^ 32) :
    WP isa (.block (nextCtr H)) u fun u' => Lay u' F S ∧ Keep [.rax, .rdx] u u' ∧
      u'.cf = some (decide (done + H.D < db)) ∧
      Rep u'.mem F S V (upd (upd W 31 (BitVec.ofNat 64 (c + 1))) 32 (BitVec.ofNat 64 (done + H.D))) := by
  have hDN := hH.hDN
  have hN := hH.N_le
  have h31 : u.mem.readW (off F sCtr) 64 = BitVec.ofNat 64 c := by rw [← hc, ← R.fr 31 (by decide)]; rfl
  have h32 : u.mem.readW (off F sDone) 64 = BitVec.ofNat 64 done := by rw [← hdn, ← R.fr 32 (by decide)]; rfl
  have G := L.geo
  have R1 := R.wf G (k := 31) (by decide) (BitVec.ofNat 64 (c + 1))
  have R2 := R1.wf G (k := 32) (by decide) (BitVec.ofNat 64 (done + H.D))
  rw [show off F (8 * 31) = off F sCtr from rfl] at R1 R2
  rw [show off F (8 * 32) = off F sDone from rfl] at R2
  have h32' : (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).readW (off F sDone) 64 =
      BitVec.ofNat 64 done := by
    have := R1.fr 32 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hdn, ← this]; rfl
  have h24 : ((u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).writeW (off F sDone)
      (BitVec.ofNat 64 (done + H.D))).readW (off F sDb) 64 = BitVec.ofNat 64 db := by
    have := R2.fr 24 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hdb, ← this]; rfl
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u' => u'.cf = some (decide (done + H.D < db)) ∧ u'.mem =
      (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).writeW (off F sDone) (BitVec.ofNat 64 (done + H.D)))
      ?_ rfl) fun u' ⟨⟨hcf, hm⟩, hk⟩ => ⟨?_, hk, hcf, hm ▸ R2⟩
  · xrun [nextCtr, ea_sp, L.rsp, L.ld (d := sCtr) (by decide), L.ld (d := sDone) (by decide),
      L.ld (d := sDb) (by decide), L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide), h31, h32', h24,
      ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat (show H.D < 2 ^ 31 by omega), BitVec.ofNat_add_ofNat]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · refine L.congr (hk.gpr (by decide)) hk.2.2 ?_
    have h1 := R2.fr 21 (by decide)
    rw [← hm] at h1
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, R.fr 21 (by decide)]
    simp [upd]

/-! ## One counter -/

/-- `DB` with the first `n` bytes of the mask `mk` XORed in. -/
def mixV (V : Nat → Byte) (mk : List Byte) (e n : Nat) (o : Nat) : Byte :=
  if e ≤ o ∧ o < e + n then V o ^^^ mk.getD (o - e) 0 else V o

theorem map_range_getD {f : Nat → Byte} {n : Nat} {xs : List Byte} (h : (List.range n).map f = xs) {j : Nat}
    (hj : j < n) : f j = xs.getD j 0 := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- The loop's invariant after `c` counters. -/
structure MgfI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (mk : List Byte)
    (e db D c : Nat) (v : State) : Prop where
  L : Lay v F S
  rd : v.rd = u₀.rd
  wr : v.wr = u₀.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], v.gpr r = u₀.gpr r
  rep : ∃ V' W', Rep v.mem F S V' W' ∧ W' 31 = BitVec.ofNat 64 c ∧ W' 32 = BitVec.ofNat 64 (c * D) ∧
    (∀ k < nW, k < 27 ∨ 32 < k → W' k = W k) ∧
    ∀ o < oRsa, ctOut o → V' o = mixV V mk e (min (c * D) db) o

theorem keep_cs {u v : State} {rs : List Reg} (k : Keep rs u v)
    (h : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], r ∉ rs) : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], v.gpr r = u.gpr r :=
  fun r hr => k.gpr (h r hr)

include K in
theorem round_ok {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) {u₀ : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {e db c : Nat} (hd : DbAt H.D e db) (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    {v : State} (I : MgfI u₀ F S V W (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (e + db + i)) db)
      e db H.D c v) (hc : c * H.D < db) :
    WP isa (seqs [clearBlock H, copyH H, .block (counter H), mgfHash H, xorOut H, .block (nextCtr H)]) v
      fun v' => v'.cf = some (decide ((c + 1) * H.D < db)) ∧
        MgfI u₀ F S V W (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (e + db + i)) db)
          e db H.D (c + 1) v' := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hfit := hd.fit
  have he1 := hd.e1
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c4 : oLen = 2368 := rfl
  have c5 : oRsa = 8192 := rfl
  obtain ⟨hnb1, hnb2⟩ := mgfNb_spec hH
  have hcD : c ≤ c * H.D := Nat.le_mul_of_pos_right c hD
  obtain ⟨V1, W1, R1, h31, h32, hW, hV⟩ := I.rep
  have hW23 : W1 23 = off S e := (hW 23 (by decide) (by omega)).trans he
  have hW24 : W1 24 = BitVec.ofNat 64 db := (hW 24 (by decide) (by omega)).trans hdb
  have hH1 : ∀ i < H.D, V1 (e + db + i) = V (e + db + i) := fun i hi => by
    rw [hV _ (by omega) ⟨by omega, by omega⟩, mixV, ifn (by omega)]
  set hB := (List.range H.D).map fun i => V (e + db + i) with hhB
  set mk := Spec.Mgf1.mgf1 G hB db with hmk
  have hBl : hB.length = H.D := by rw [hhB, List.length_map, List.length_range]
  have hBg : ∀ i < H.D, hB.getD i 0 = V (e + db + i) := fun i hi => by
    rw [hhB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  unfold seqs seqs seqs seqs seqs
  -- `Y` cleared.
  refine WP.seq (WP.mono (clearBlock_ok hH I.L R1) fun u1 ⟨L1, k1, hcx1, R1'⟩ => ?_)
  -- `H`.
  refine WP.seq (WP.mono (copyH_ok hH L1 R1' hd hW23 hW24 hcx1) fun u2 ⟨L2, k2, R2⟩ => ?_)
  -- The counter.
  refine WP.seq (WP.mono (counter_ok hH L2 R2 h31 (by omega) ((k2.gpr (by decide)).trans hcx1))
    fun u3 ⟨L3, k3, R3⟩ => ?_)
  -- The digest of `H ‖ C`.
  have hml : (hB ++ Spec.Rsa.i2osp c 4).length = H.D + 4 := by
    rw [List.length_append, hBl, i2osp_len]
  refine WP.seq (WP.mono (mgfHash_ok hH K L3 R3 (msg := hB ++ Spec.Rsa.i2osp c 4) (nbm := mgfNb H) hml
    (by simp [upd, hml]) (by simp [upd]) (by omega) (by omega) (fun i hi => ?_))
    fun u4 ⟨L4, rd4, wr4, cs4, V5, W3, R4, hout4, hW4, hdig⟩ => ?_)
  · simp only [ctrV, cpV, clrV, getD_app, hBl]
    by_cases h1 : i < H.D
    · rw [ifn (by omega), ifp (by omega), ifp h1, ifn (by omega), Nat.add_sub_cancel_left, hH1 i h1, hBg i h1]
    · by_cases h2 : i < H.D + 4
      · rw [ifp (by omega), ifn h1, show oY + i - (oY + H.D) = i - H.D by omega]
      · rw [ifn (by omega), ifn (by omega), ifp (by omega), ifn h1, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [i2osp_len]; omega)]
        rfl
  -- Into `DB`.
  have hW3 : ∀ k < nW, k < 27 ∨ 32 < k → W3 k = W k := fun k hk h => by
    rw [hW4 k hk (by omega) (by omega)]; simp only [upd, ifn (show k ≠ 28 by omega), ifn (show k ≠ 27 by omega)]
    exact hW k hk h
  have hW3' : ∀ k, k = 31 ∨ k = 32 → W3 k = W1 k := fun k h => by
    rw [hW4 k (by unfold nW frameBytes; omega) (by omega) (by omega)]
    simp only [upd, ifn (show k ≠ 28 by omega), ifn (show k ≠ 27 by omega)]
  have hcD' : c * H.D + H.D ≤ db + H.D := by omega
  refine WP.seq (WP.mono (xorOut_ok hH L4 R4 hd ((hW3 23 (by decide) (by omega)).trans he)
    ((hW3 24 (by decide) (by omega)).trans hdb) ((hW3' 32 (by omega)).trans h32) hc)
    fun u5 ⟨L5, k5, R5⟩ => ?_)
  -- The next counter.
  refine WP.mono (nextCtr_ok hH L5 R5 ((hW3' 31 (by omega)).trans h31) ((hW3' 32 (by omega)).trans h32)
    ((hW3 24 (by decide) (by omega)).trans hdb) (by omega) (by omega)) fun u6 ⟨L6, k6, cf6, R6⟩ => ?_
  refine ⟨by rw [cf6, Nat.succ_mul], L6, ?_, ?_, ?_, _, _, R6, by simp [upd], ?_, ?_, ?_⟩
  · rw [k6.2.1, k5.2.1, rd4, k3.2.1, k2.2.1, k1.2.1, I.rd]
  · rw [k6.2.2, k5.2.2, wr4, k3.2.2, k2.2.2, k1.2.2, I.wr]
  · intro r hr
    rw [keep_cs k6 (by decide) r hr, keep_cs k5 (by decide) r hr, cs4 r hr, keep_cs k3 (by decide) r hr,
      keep_cs k2 (by decide) r hr, keep_cs k1 (by decide) r hr, I.cs r hr]
  · simp [upd, Nat.succ_mul]
  · intro k hk h
    simp only [upd, ifn (show k ≠ 32 by omega), ifn (show k ≠ 31 by omega)]
    exact hW3 k hk h
  · intro o ho hco
    have hcm : H.D * c = c * H.D := Nat.mul_comm _ _
    have hs1 : (c + 1) * H.D = c * H.D + H.D := Nat.succ_mul _ _
    have hY := hco.2
    have hl := hco.1
    have hdg : ∀ j < H.D, V5 (oDig + j) = (hH.SH.H.hash (hB ++ Spec.Rsa.i2osp c 4)).getD j 0 :=
      fun j hj => map_range_getD (f := fun i => V5 (oDig + i)) hdig hj
    have hold : V5 o = mixV V mk e (min (c * H.D) db) o := by
      rw [hout4 o ho hco]
      simp only [ctrV, cpV, clrV]
      rw [ifn (by omega), ifn (by omega), ifn (by omega), hV o ho hco]
    simp only [xorV]
    by_cases hx : e + c * H.D ≤ o ∧ o < e + c * H.D + min H.D (db - c * H.D)
    · have hq : (o - e) / H.D = c :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega) (by rw [Nat.succ_mul, Nat.mul_comm]; omega)
      have hr : (o - e) % H.D = o - (e + c * H.D) := by
        rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]; omega
      rw [ifp hx, hold, hdg _ (by omega), mixV, mixV, ifn (by omega), ifp (by omega), hmk,
        mgf1_getD hG hB (show o - e < db by omega), hGl, hGh, hq, hr]
    · rw [ifn hx, hold, mixV, mixV]
      by_cases hy : e ≤ o ∧ o < e + min (c * H.D) db
      · rw [ifp hy, ifp (by omega)]
      · rw [ifn hy, ifn (by omega)]

/-! ## MGF1 -/

include K in
/-- `DB ⊕= MGF1(H, dbLen)`, where `H` is the `hLen` bytes after `DB`. -/
theorem mgfXor_ok {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (hd : DbAt H.D e db) (he : W 23 = off S e)
    (hdb : W 24 = BitVec.ofNat 64 db) :
    WP isa (mgfXor H) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧ (∀ k < nW, k < 27 ∨ 32 < k → W' k = W k) ∧
        ∀ o < oRsa, ctOut o → V' o = mixV V (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (e + db + i)) db)
          e db o := by
  have hD := hH.hD0
  have hdb1 := hd.db1
  have G' := L.geo
  have R2 := (R.wf G' (k := 31) (by decide) 0#64).wf G' (k := 32) (by decide) 0#64
  rw [show off F (8 * 31) = off F sCtr from rfl, show off F (8 * 32) = off F sDone from rfl] at R2
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun v => v.mem =
      (u.mem.writeW (off F sCtr) 0#64).writeW (off F sDone) 0#64) ?_ rfl)
    fun v ⟨hm, hk⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl]
  have R2' : Rep v.mem F S V (upd (upd W 31 0#64) 32 0#64) := hm ▸ R2
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, R2'.fr 21 (by decide), R.fr 21 (by decide)]; simp [upd])
  have I0 : MgfI u F S V W (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (e + db + i)) db) e db H.D 0 v :=
    ⟨Lv, hk.2.1, hk.2.2, keep_cs hk (by decide), _, _, R2', by simp [upd], by simp [upd],
      fun k _ h => by simp only [upd, ifn (show k ≠ 32 by omega), ifn (show k ≠ 31 by omega)],
      fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega)]⟩
  refine WP.loop (M := isa) (fun n w => ∃ c, n = db - c * H.D ∧ c * H.D < db ∧
      MgfI u F S V W (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (e + db + i)) db) e db H.D c w)
    ?_ (db - 0 * H.D) v ⟨0, rfl, by omega, I0⟩
  rintro n w ⟨c, rfl, hc, I⟩
  refine WP.mono (round_ok hH K hGh hGl hG hd he hdb I hc) fun w' ⟨hcf, I'⟩ => ?_
  have hs1 : (c + 1) * H.D = c * H.D + H.D := Nat.succ_mul _ _
  by_cases h : (c + 1) * H.D < db
  · refine .inr ⟨by simp only [eval, hcf, h, decide_true], _, ?_, c + 1, rfl, h, I'⟩
    omega
  · refine .inl ⟨by simp only [eval, hcf, h, decide_false], I'.L, I'.rd, I'.wr, I'.cs, ?_⟩
    obtain ⟨V', W', R', _, _, hW', hV'⟩ := I'.rep
    exact ⟨V', W', R', hW', fun o ho hco => by rw [hV' o ho hco, Nat.min_eq_right (by omega)]⟩

end VG.Proof.RsaPss.X86_64
