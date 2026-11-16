module
public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigit
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Dsa.AArch64.SharedGroup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Every digit of both exponents

The digits of a group of bytes, then the groups from the exponents' ends:
when no byte is left, the buckets hold every digit of both exponents. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- What the digits keep of the arrays and the header from `s₀`. -/
structure DigitsKeep (s₀ : State) (P : Addr) (wx : Nat) (t : State) : Prop where
  arr : ∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT → j ≠ Crt.aXc →
    wv t.mem P (slot wx j) wx = wv s₀.mem P (slot wx j) wx
  hdr : ∀ i < 32, i ≠ Crt.sNib → i ≠ Crt.sEnt → i ≠ Crt.sJ → i ≠ Crt.sV → i ≠ Crt.sMaskX → i ≠ Crt.sBit →
    word t.mem P (8 * i) = word s₀.mem P (8 * i)
  frm : Frm P (workRanges wx) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

theorem DigitsKeep.refl (s : State) (P : Addr) (wx : Nat) : DigitsKeep s P wx s :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, Frm.refl _ _ _, Keep.refl _ _⟩

/-- After `i` digits of the group whose values are `V` and `Q`. -/
structure DigitsInv (s₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (N g ex eq k V Q c i : Nat)
    (t : State) : Prop where
  dig : DigitInv P wx minv N g ex eq (k + i) t
  v : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (V / 8 ^ i)
  q : word t.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 (Q / 8 ^ i)
  b : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (c - i)
  rest : DigitsKeep s₀ P wx t

theorem digitStep_ok (M : Mont) {s₀ s : State} {P : Addr} {wx : Nat} {minv : BitVec 64}
    {N g ex eq k V Q c i : Nat} (hw : 8 ≤ wx) (hw' : wx < 2 ^ 30) (hd : wx % 8 = 0)
    (hR : Nat.Coprime (2 ^ (64 * wx)) N) (hc8 : c ≤ 8) (hi : i < c) (hV' : V < 2 ^ 64) (hQ' : Q < 2 ^ 64)
    (hVd : ∀ i < c, V / 8 ^ i % 8 = ex / 8 ^ (k + i) % 8) (hQd : ∀ i < c, Q / 8 ^ i % 8 = eq / 8 ^ (k + i) % 8)
    (hI : DigitsInv s₀ P wx minv N g ex eq k V Q c i s) :
    WP isa (digit M.mm) s fun t => DigitsInv s₀ P wx minv N g ex eq k V Q c (i + 1) t ∧
      ((t.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ c) := by
  have hle (a b : Nat) : a / 8 ^ b ≤ a := Nat.div_le_self _ _
  refine WP.mono (digit_ok M hw hw' hd hR hI.dig hI.v (by have := hle V i; omega_arith) (hVd i hi)
    hI.q (by have := hle Q i; omega_arith) (hQd i hi) hI.b (by omega_arith))
    fun t ⟨hdig, hv, hq, hb, h3, harr, hhdr, hfrm, hk⟩ => ?_
  refine ⟨⟨hdig, ?_, ?_, ?_, ⟨fun j hj h1 h2 h3 h4 h5 => ?_, fun i' hi' h1 h2 h3 h4 h5 h6 => ?_,
    hI.rest.frm.trans hfrm, (hI.rest.keep.trans hk).mono (by decide)⟩⟩, ?_⟩
  · rw [hv, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  · rw [hq, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  · rw [hb, Nat.sub_sub]
  · rw [harr j hj h1 h2 h3 h4 h5, hI.rest.arr j hj h1 h2 h3 h4 h5]
  · rw [hhdr i' hi' h1 h2 h3 h4 h5 h6, hI.rest.hdr i' hi' h1 h2 h3 h4 h5 h6]
  · rw [h3, cnt_ne (by omega_arith)]
    omega_arith

/-- The `c` digits of a group. -/
theorem digitLoop_ok (M : Mont) {s₀ s : State} {P : Addr} {wx : Nat} {minv : BitVec 64}
    {N g ex eq k V Q c : Nat} (hw : 8 ≤ wx) (hw' : wx < 2 ^ 30) (hd : wx % 8 = 0)
    (hR : Nat.Coprime (2 ^ (64 * wx)) N) (hc1 : 1 ≤ c) (hc8 : c ≤ 8) (hV' : V < 2 ^ 64) (hQ' : Q < 2 ^ 64)
    (hVd : ∀ i < c, V / 8 ^ i % 8 = ex / 8 ^ (k + i) % 8) (hQd : ∀ i < c, Q / 8 ^ i % 8 = eq / 8 ^ (k + i) % 8)
    (hI : DigitsInv s₀ P wx minv N g ex eq k V Q c 0 s) :
    WP isa (.loop (digit M.mm) (.nonzero .x .x3)) s (DigitsInv s₀ P wx minv N g ex eq k V Q c c) :=
  count_loop (cr := .x3) (n := c) (by omega_arith) (DigitsInv s₀ P wx minv N g ex eq k V Q c)
    (fun _ hi _ hI => digitStep_ok M hw hw' hd hR hc8 hi hV' hQ' hVd hQd hI) hI

/-- The buckets through changes to the header's slots for the functions' own use. -/
theorem DigitInv.of_fn {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N g ex eq k : Nat}
    (h : DigitInv P wx minv N g ex eq k s) (ho : Outside P 136 120 s.mem t.mem)
    (htab : word t.mem P (8 * Crt.sTab) = word s.mem P (8 * Crt.sTab)) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = s.gpr .x0) : DigitInv P wx minv N g ex eq k t := by
  have hn := h.ctx.scrT.nowrap
  have ax : wv t.mem P (slot wx Crt.aXc) wx = wv s.mem P (slot wx Crt.aXc) wx := fn_arr ho hn (by decide)
  exact ⟨by rw [ax]; exact ctx_of_fn h.ctx ho hwr h0, htab.trans h.tab,
    fun j hj => by rw [fn_ent ho hn hj]; exact h.lt j hj,
    fun d hd => by rw [fn_ent ho hn (by omega_arith)]; exact h.xs d hd,
    fun d hd hd0 => by rw [fn_ent ho hn (by omega_arith)]; exact h.qs d hd hd0,
    by rw [ax]; exact h.alt, by rw [ax]; exact h.a⟩

/-- The exponents' bytes, outside the workspace, as the start state has them. -/
structure Exps (s₀ : State) (P : Addr) (wx : Nat) (xp qp : Addr) (xb qb : List Byte) : Prop where
  xrd : ∀ i < xb.length, InRegions (s₀.rd ++ s₀.wr) (xp + BitVec.ofNat 64 i) 1
  xv : ∀ i (h : i < xb.length), s₀.mem (xp + BitVec.ofNat 64 i) = xb[i]
  xout : ∀ i < xb.length, slot wx 8 + tabBytes wx ≤ ofs P (xp + BitVec.ofNat 64 i)
  qrd : ∀ i < qb.length, InRegions (s₀.rd ++ s₀.wr) (qp + BitVec.ofNat 64 i) 1
  qv : ∀ i (h : i < qb.length), s₀.mem (qp + BitVec.ofNat 64 i) = qb[i]
  qout : ∀ i < qb.length, slot wx 8 + tabBytes wx ≤ ofs P (qp + BitVec.ofNat 64 i)
  len : qb.length = xb.length

/-- After `j` groups of bytes, and `k` digits. -/
structure GroupsInv (s₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (N g : Nat) (xp qp : Addr)
    (xb qb : List Byte) (j k : Nat) (t : State) : Prop where
  dig : DigitInv P wx minv N g (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip qb) k t
  xr : Spec.Rsa.os2ip xb / 8 ^ k = pre xb (xb.length - 3 * j)
  qr : Spec.Rsa.os2ip qb / 8 ^ k = pre qb (xb.length - 3 * j)
  rem : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 (xb.length - 3 * j)
  xptr : word t.mem P (8 * Crt.sExp) = xp
  qptr : word t.mem P (8 * Crt.sSrc) = qp
  arr : ∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT → j ≠ Crt.aXc →
    wv t.mem P (slot wx j) wx = wv s₀.mem P (slot wx j) wx
  frm : Frm P (workRanges wx) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

/-- One group of bytes: its digits, and the bytes left into `x3`. -/
theorem groupsStep_ok (M : Mont) {s₀ s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N g : Nat}
    {xp qp : Addr} {xb qb : List Byte} {j k : Nat} (hw : 8 ≤ wx) (hw' : wx < 2 ^ 30) (hd : wx % 8 = 0)
    (hR : Nat.Coprime (2 ^ (64 * wx)) N) (hx : Exps s₀ P wx xp qp xb qb) (hL : xb.length < 2 ^ 31)
    (hj : j < (xb.length + 2) / 3) (hI : GroupsInv s₀ P wx minv N g xp qp xb qb j k s) :
    WP isa (seqs [group, .loop (digit M.mm) (.nonzero .x .x3), .block [ldh .x3 Crt.sI]]) s fun t =>
      (∃ k', GroupsInv s₀ P wx minv N g xp qp xb qb (j + 1) k' t) ∧
      ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ (xb.length + 2) / 3) := by
  have hn := hI.dig.ctx.scrT.nowrap
  have hr1 : 1 ≤ xb.length - 3 * j := by omega_arith
  have hsub : xb.length - 3 * j - 3 = xb.length - 3 * (j + 1) := by omega_arith
  have hmemx : ∀ i (h : i < xb.length), s.mem (xp + BitVec.ofNat 64 i) = xb[i] := fun i hi => by
    rw [hI.frm _ fun r hr => Or.inr (by have := (workRanges_ok wx r hr).2; have := hx.xout i hi; omega_arith)]
    exact hx.xv i hi
  have hmemq : ∀ i (h : i < qb.length), s.mem (qp + BitVec.ofNat 64 i) = qb[i] := fun i hi => by
    rw [hI.frm _ fun r hr => Or.inr (by have := (workRanges_ok wx r hr).2; have := hx.qout i hi; omega_arith)]
    exact hx.qv i hi
  simp only [seqs]
  refine WP.seq (WP.mono (group_ok hI.dig.ctx hr1 (by omega_arith) (by rw [hx.len]; omega_arith) (by omega_arith)
    hI.rem hI.xptr hI.qptr (fun i hi => by rw [hI.keep.rd, hI.keep.wr]; exact hx.xrd i hi) hmemx
    (fun i hi => by rw [hI.keep.rd, hI.keep.wr]; exact hx.qrd i hi) hmemq) fun u ⟨hm, ku⟩ => ?_)
  have oU : Outside P 136 120 s.mem u.mem := by
    rw [hm]
    exact (((fn_outside _ P _ (by decide) (by decide)).trans (fn_outside _ P _ (by decide) (by decide))).trans
      (fn_outside _ P _ (by decide) (by decide))).trans (fn_outside _ P _ (by decide) (by decide))
  have hh : ∀ i < 32, i ≠ Crt.sI → i ≠ Crt.sV → i ≠ Crt.sMaskX → i ≠ Crt.sBit →
      word u.mem P (8 * i) = word s.mem P (8 * i) := fun i hi h1 h2 h3 h4 => by
    rw [hm, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h4), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h3),
      hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]
  have hdigU := hI.dig.of_fn oU (hh _ (by decide) (by decide) (by decide) (by decide) (by decide)) ku.wr
    (ku.gpr .x0 (by decide))
  have I0 : DigitsInv u P wx minv N g (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip qb) k
      (gval xb (xb.length - 3 * j)) (gval qb (xb.length - 3 * j)) (gcount (xb.length - 3 * j)) 0 u :=
    ⟨hdigU, by
        rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
          hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.pow_zero, Nat.div_one],
      by rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.pow_zero,
          Nat.div_one],
      by rw [hm, word_writeW_self, Nat.sub_zero], DigitsKeep.refl _ _ _⟩
  have hV24 := gval_lt xb (xb.length - 3 * j)
  have hQ24 := gval_lt qb (xb.length - 3 * j)
  refine WP.seq (WP.mono (digitLoop_ok M hw hw' hd hR (gcount_pos _) (gcount_le _) (by omega_arith)
    (by omega_arith)
    (fun i hi => by
      rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hI.xr]
      exact (group_digit xb hr1 (by omega_arith) hi).symm)
    (fun i hi => by
      rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hI.qr]
      exact (group_digit qb hr1 (by rw [hx.len]; omega_arith) hi).symm) I0) fun v hv => ?_)
  have remV : word v.mem P (8 * Crt.sI) = BitVec.ofNat 64 (xb.length - 3 * (j + 1)) := by
    rw [hv.rest.hdr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hm,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, hsub]
  have hcv := hv.dig.ctx
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (xb.length - 3 * (j + 1)) ∧
    t.mem = v.mem) (by
      brun [hcv.good.x0, hdr_enc (show Crt.sI < 32 by decide), hcv.ld (i := Crt.sI) (by decide), remV])
    rfl rfl rfl) fun t ⟨⟨h3, hmt⟩, kt⟩ => ?_
  refine ⟨⟨k + gcount (xb.length - 3 * j), ⟨?_, ?_, ?_, by rw [hmt]; exact remV, ?_, ?_,
    fun j' hj' h1 h2 h3 h4 h5 => ?_, ?_,
    (((hI.keep.trans (ku.mono (rs' := mmRegs) (by decide))).trans hv.rest.keep).trans kt).mono (by decide)⟩⟩, ?_⟩
  · exact hv.dig.of_fn (by rw [hmt]; exact Outside.refl _ _ _ _) (by rw [hmt]) kt.wr (kt.gpr .x0 (by decide))
  · rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hI.xr, group_rest xb hr1 (by omega_arith), hsub]
  · rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hI.qr, group_rest qb hr1 (by rw [hx.len]; omega_arith), hsub]
  · rw [hmt, hv.rest.hdr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hh _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hI.xptr
  · rw [hmt, hv.rest.hdr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hh _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hI.qptr
  · rw [hmt, hv.rest.arr j' hj' h1 h2 h3 h4 h5, fn_arr oU hn hj', hI.arr j' hj' h1 h2 h3 h4 h5]
  · rw [hmt]
    exact (hI.frm.trans (fn_work oU)).trans hv.rest.frm
  · rw [h3, cnt_ne (by omega_arith)]
    omega_arith

/-- Every digit of both exponents: the buckets hold them all. -/
theorem digits_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N g : Nat}
    {xp qp : Addr} {xb qb : List Byte} (hw : 8 ≤ wx) (hw' : wx < 2 ^ 30) (hd : wx % 8 = 0)
    (hR : Nat.Coprime (2 ^ (64 * wx)) N) (hx : Exps s P wx xp qp xb qb) (hL1 : 1 ≤ xb.length)
    (hL : xb.length < 2 ^ 31) (hI : GroupsInv s P wx minv N g xp qp xb qb 0 0 s) :
    WP isa (digits M.mm) s fun t =>
      ∃ k, GroupsInv s P wx minv N g xp qp xb qb ((xb.length + 2) / 3) k t := by
  unfold digits
  exact count_loop (cr := .x3) (n := (xb.length + 2) / 3) (by omega_arith)
    (fun j t => ∃ k, GroupsInv s P wx minv N g xp qp xb qb j k t)
    (fun j hj t ⟨k, hI⟩ => groupsStep_ok M hw hw' hd hR hx hL hj hI) ⟨0, hI⟩

end VG.Proof.Dsa.AArch64.SharedPower
