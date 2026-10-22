module
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
public import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtComp

import VerifiedGarbage.Proof.RsaPss.X86_64.BufferCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirect
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# RSASSA-PSS on x86-64: hashing verification's input of a public length

With a given salt length, the input `M'` has a public length `ℓ`, so
`fixedSaltPrefix` builds it, `0x80` included, in `Y`'s first `nbm` blocks
(`clearNb`, `padSalt`), and `fixedHash` writes the length field straight to
the last block (`lenLast`) and compresses every block (`compAll`), whose last
hash value is the digest's (`fixedHash_gen`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.RsaPss (lastBlk padded)

/-- `clearQ_ok`, with the count in `r10`. -/
theorem clearQR_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o n : Nat} (hn : 0 < n) (h8 : n % 8 = 0) (ho : o + n ≤ oRsa)
    (hcx : u.gpr .rcx = off S o) (hax : u.gpr .rax = 0) (hr8 : u.gpr .r8 = BitVec.ofNat 64 0)
    (hr10 : u.gpr .r10 = BitVec.ofNat 64 n) :
    WP isa (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8),
        .alu .cmp .r8 (.reg .r10)]) .ne) u fun u' =>
      Lay u' F S ∧ Keep [.r8] u u' ∧ Rep u'.mem F S (clrV V o n) W := by
  have hnR : n < 2 ^ 63 := by unfold oRsa at ho; omega
  refine wp_upto (a := 0) (N := n / 8) (by omega) (fun j v => Lay v F S ∧ Keep [.r8] u v ∧
      v.gpr .r8 = BitVec.ofNat 64 (8 * j) ∧ Rep v.mem F S (clrV V o (8 * j)) W) ?_ (fun v ⟨Lv, k, _, Rv⟩ => ?_)
    ⟨L, Keep.refl _ _, hr8, (congrArg (fun V' => Rep u.mem F S V' W) (funext fun x => by
      simp only [clrV]; rw [ifn (by omega)])).mpr R⟩
  · intro j _ hj v ⟨Lv, k, hv8, Rv⟩
    have hea : v.ea (ix .rcx .r8) = off S (o + 8 * j) := by
      rw [ea_ix0, k.gpr (by decide), hcx, hv8]; exact off_off S o (8 * j)
    refine WP.mono (WP.keep [.r8] (Q := fun v' => v'.zf = some (decide (j + 1 = n / 8)) ∧
        v'.gpr .r8 = BitVec.ofNat 64 (8 * (j + 1)) ∧ v'.mem = v.mem.writeW (off S (o + 8 * j)) (0#64)) ?_ rfl)
      fun v' ⟨⟨hz, h8', hm⟩, k'⟩ => ⟨hz, ?_⟩
    · xrun [hea, Lv.sst (d := o + 8 * j) (by omega), k.gpr (show Reg.rax ∉ [Reg.r8] by decide), hax, hv8,
        k.gpr (show Reg.r10 ∉ [Reg.r8] by decide), hr10, ofNat_add_lit,
        ofNat_sub_beq (show 8 * j + 8 < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega)]
      exact ⟨by simp only [decide_eq_decide]; omega, by congr 1, rfl⟩
    · have R' := Rv.ws Lv.geo (o := o + 8 * j) (w := 64) (by omega) (0#64)
      rw [← hm] at R'
      have R'' : Rep v'.mem F S (clrV V o (8 * (j + 1))) W := by
        refine (congrArg (fun V' => Rep v'.mem F S V' W) (funext fun x => ?_)).mp R'
        simp only [stBytes, clrV]
        by_cases h1 : o + 8 * j ≤ x ∧ x < o + 8 * j + 64 / 8
        · rw [ifp h1, ifp (by omega)]
          exact BitVec.eq_of_toNat_eq (by simp)
        · rw [ifn h1]
          by_cases h2 : o ≤ x ∧ x < o + 8 * j
          · rw [ifp h2, ifp (by omega)]
          · rw [ifn h2, ifn (by omega)]
      exact ⟨Lv.of_rep Rv R'' (k'.gpr (by decide)) k'.2.2, (k.trans k').mono (by decide), h8', R''⟩
  · rw [show 8 * (n / 8) = n by omega] at Rv
    exact ⟨Lv, k, Rv⟩

variable {H : Hash} (hH : HashOK H) (K : Callees H)

include hH in
/-- `Y`'s first `nbm` blocks cleared. -/
theorem clearNb_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {nbm : Nat} (hn : W 28 = BitVec.ofNat 64 nbm) (h1 : 1 ≤ nbm)
    (hnb : nbm * H.P.B ≤ 2048) :
    WP isa (clearNb H) u fun u' => Lay u' F S ∧ Keep [.rcx, .r10, .rax, .r8] u u' ∧ u'.gpr .rcx = off S oY ∧
      Rep u'.mem F S (clrV V oY (nbm * H.P.B)) W := by
  obtain ⟨hpow, hlg1, hlg2⟩ := lgB_spec hH
  have hB := hH.B_pos
  have hB8 : H.P.B % 8 = 0 := by rcases hH.dims.B with h | h <;> rw [h]
  have hN : nbm * H.P.B < 2 ^ 63 := by omega
  refine WP.seq (WP.mono (WP.keep [.rcx, .r10, .rax, .r8] (Q := fun v => v.gpr .rcx = off S oY ∧
      v.gpr .r10 = BitVec.ofNat 64 (nbm * H.P.B) ∧ v.gpr .rax = 0 ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧
      v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, h₄, hm⟩, hk⟩ => ?_)
  · have hs := L.slot
    simp only [Bignum.word] at hs
    have e28 : u.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by
      rw [← hn, ← R.fr 28 (by decide)]; rfl
    xrun [clearNb, scr, ea_sp, L.rsp, L.ld (d := sScr) (by decide), L.ld (d := sNb) (by decide), hs, e28,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY < 2 ^ 31 by decide),
      ror_mul (x := nbm) (k := lgB H) (B := H.P.B) (by omega) (by omega) hpow (show nbm * H.P.B < 2 ^ 64 by omega),
      List.cons_append, List.nil_append, show 1 ≤ 64 - lgB H ∧ 64 - lgB H ≤ 63 from ⟨by omega, by omega⟩,
      show ¬ 64 - lgB H = 1 by omega]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (clearQR_ok Lv (hm ▸ R) (o := oY) (n := nbm * H.P.B) (Nat.mul_pos (by omega) hB)
    (by rw [Nat.mul_mod, hB8, Nat.mul_zero, Nat.zero_mod]) (by unfold oY oRsa; omega) h₁ h₃ h₄ h₂)
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), (kw.gpr (by decide)).trans h₁, Rw⟩

/-- `0x80` to byte `8 + hLen + sLen` of `Y`. -/
theorem padSalt_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {sl : Nat} (hsl : W 36 = BitVec.ofNat 64 sl) (hfit : 8 + H.D + sl < 2048) :
    WP isa (.block (padSalt H)) u fun u' => Lay u' F S ∧ Keep [.rcx, .rdx, .rax] u u' ∧
      Rep u'.mem F S (upd V (oY + (8 + H.D + sl)) 0x80) W := by
  have hb : oY + (8 + H.D + sl) < oRsa := by unfold oY oRsa; omega
  refine WP.mono (WP.keep [.rcx, .rdx, .rax] (Q := fun v =>
      v.mem = u.mem.writeW (off S (oY + (8 + H.D + sl))) (0x80 : Byte)) ?_ rfl) fun v ⟨hv, kv⟩ => ?_
  · have hs := L.slot
    simp only [Bignum.word] at hs
    have hea : off S oY + BitVec.ofNat 64 sl + BitVec.ofNat 64 (8 + H.D) = off S (oY + (8 + H.D + sl)) := by
      rw [off_ix, off_off]; congr 1; omega
    xrun [padSalt, scr, ea_sp, ea_ix, L.rsp, L.ld (d := sScr) (by decide), L.ld (d := sSlen) (by decide), hs,
      R.rd (d := sSlen) 36 rfl (by decide), hsl, hea, L.sst8 hb,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY < 2 ^ 31 by decide), List.cons_append, List.nil_append]
    rfl
  · have Rv : Rep v.mem F S (upd V (oY + (8 + H.D + sl)) 0x80) W := by
      rw [hv]
      have rr := R.wb L.geo (o := oY + (8 + H.D + sl)) hb (0x80 : Byte)
      exact rr
    exact ⟨L.of_rep R Rv (kv.gpr (by decide)) kv.2.2, kv, Rv⟩

include hH in
/-- The length field copied to the last `L` bytes of block `nbm - 1`. -/
theorem lenLast_ok {u : State} {F S : Addr} (L : Lay u F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {len : List Byte}
    (hlen : ∀ i < H.P.L, V (oLen + i) = len.getD i 0) {nbm : Nat} (hn : W 28 = BitVec.ofNat 64 nbm)
    (h1 : 1 ≤ nbm) (hnb : nbm * H.P.B ≤ 2048) :
    WP isa (lenLast H) u fun t => Lay t F S ∧ Keep [.rsi, .rcx, .rax, .r8] u t ∧
      Rep t.mem F S (cpV V (fun i => len.getD i 0) (oY + (nbm * H.P.B - H.P.L)) H.P.L) W := by
  obtain ⟨hpow, hlg1, hlg2⟩ := lgB_spec hH
  have hL := hH.dims.L
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hBn : H.P.B ≤ nbm * H.P.B := Nat.le_mul_of_pos_left _ h1
  have hLB : H.P.L < H.P.B := by have := hH.dims.L; rcases hH.dims.B with h | h <;> omega
  unfold lenLast
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun v =>
    v.gpr .rsi = off S oLen ∧ v.gpr .rcx = off S (oY + (nbm * H.P.B - H.P.L)) ∧ v.mem = u.mem)
    ?_ rfl) fun v ⟨⟨hs, hd, hm⟩, hk⟩ => ?_)
  · have hslot := L.slot
    simp only [Bignum.word] at hslot
    have e28 : u.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by
      rw [← hn, ← R.fr 28 (by decide)]; rfl
    have hc : S + BitVec.ofNat 64 (nbm * H.P.B) + BitVec.ofNat 64 (oY - H.P.L) =
        off S (oY + (nbm * H.P.B - H.P.L)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add,
        show nbm * H.P.B + (oY - H.P.L) = oY + (nbm * H.P.B - H.P.L) by unfold oY; omega]
    xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide),
      L.ld (d := sNb) (by decide), hslot, e28,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oLen < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY - H.P.L < 2 ^ 31 by unfold oY; omega),
      ror_mul (x := nbm) (k := lgB H) (B := H.P.B) (by omega) (by omega) hpow (show nbm * H.P.B < 2 ^ 64 by omega),
      show 1 ≤ 64 - lgB H ∧ 64 - lgB H ≤ 63 from ⟨by omega, by omega⟩, show ¬ 64 - lgB H = 1 by omega, hc]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have finish : ∀ t, Lay t F S → Keep [.rax, .r8] v t →
      Rep t.mem F S (cpV V (fun i => V (oLen + i)) (oY + (nbm * H.P.B - H.P.L)) H.P.L) W →
      Lay t F S ∧ Keep [.rsi, .rcx, .rax, .r8] u t ∧
      Rep t.mem F S (cpV V (fun i => len.getD i 0) (oY + (nbm * H.P.B - H.P.L)) H.P.L) W := by
    intro t Lt kt Rt
    refine ⟨Lt, (hk.trans kt).mono (by decide), ?_⟩
    refine (congrArg (fun V' => Rep t.mem F S V' W) (funext fun x => ?_)).mp Rt
    simp only [cpV]
    split
    · exact hlen _ (by omega)
    · rfl
  split
  · rename_i h8
    have hwords : 8 * (H.P.L / 8) = H.P.L := by omega
    refine WP.mono (copyScratchWords_ok Lv (hm ▸ R) (by decide) (by decide)
      (by rw [hwords]; unfold oLen oRsa; omega)
      (by rw [hwords]; unfold oY oRsa; omega)
      (by rw [hwords]; unfold oLen oY; omega) hs hd) fun t ⟨Lt, kt, Rt⟩ => ?_
    rw [hwords] at Rt
    exact finish t Lt (kt.mono (by decide)) Rt
  · exact WP.mono (copyScratchBytes_ok Lv (hm ▸ R) (by omega)
      (by unfold oLen oRsa; omega) (by unfold oY oRsa; omega)
      (by unfold oLen oY; omega) hs hd) fun t ⟨Lt, kt, Rt⟩ => finish t Lt kt Rt

/-- Before block `b`, with no selection. -/
def CA2 (t : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (n b : Nat) (u : State) : Prop :=
  Lay u F S ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
  ∃ V' : Nat → Byte, Rep u.mem F S V' (upd W 29 (BitVec.ofNat 64 b)) ∧
    (∀ o < oRsa, ¬ inR [(oSt, H.P.N), (0, H.P.so)] o → V' o = V o) ∧
    hH.md.stateAt u.mem (off S oSt) = hH.md.compressList hH.iv (yList V n) b

include hH in
/-- Every block compressed. -/
theorem compAll_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (hiv : hH.md.stateAt t.mem (off S oSt) = hH.iv) {nbm : Nat}
    (hn : W 28 = BitVec.ofNat 64 nbm) (h1 : 1 ≤ nbm) (hnb : nbm * H.P.B ≤ 2048) :
    WP isa (compAll H) t (CA2 hH t F S V W (nbm * H.P.B) nbm) := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hN := hH.N_le
  have hso := hH.hso
  have hnbm : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right nbm hB0) hnb
  refine WP.seq (WP.mono (startZero_ok L R) fun u ⟨L0, hk, R0⟩ => ?_)
  have hst0 : hH.md.stateAt u.mem (off S oSt) = hH.md.compressList hH.iv (yList V (nbm * H.P.B)) 0 := by
    rw [stateAt_rep hH R R0 (o := oSt) (by unfold oSt oRsa; omega_using [hN]) (fun _ _ => rfl), hiv]
    exact (MdStream.Md.compressList_zero _ _ _).symm
  refine wp_upto (a := 0) (N := nbm) (by omega_using [h1]) (CA2 hH t F S V W (nbm * H.P.B)) ?_ (fun _ h => h)
    ⟨L0, hk.2.1, hk.2.2, fun r hr => hk.gpr (cs_keep hr (by decide)), V, R0, fun _ _ _ => rfl, hst0⟩
  intro b _ hb u ⟨Lu, hrd, hwr, hcs, V', Ru, hkeep, hst⟩
  have hbB : H.P.B * b + H.P.B ≤ 2048 := by
    rw [← Nat.mul_succ]; exact Nat.le_trans (Nat.mul_le_mul_left _ hb) (by rw [Nat.mul_comm]; exact hnb)
  refine WP.seq_assoc (WP.seq (WP.mono (compCall_ok hH Lu Ru hbB (by simp [upd]))
    fun v ⟨Lv, hrdv, hwrv, hcsv, Rv, hstv⟩ => ?_))
  refine WP.mono (nextBlock_ok Lv Rv (b := b) (nbm := nbm) (by simp [upd]) (by simp [upd, hn])
    (by omega_using [hnbm, hb]) (by omega_using [hnbm])) fun u' ⟨hz, Lu', hk', Ru'⟩ => ⟨hz, ?_⟩
  rw [upd_upd] at Ru'
  have hY : ∀ i < 2048, V' (oY + i) = V (oY + i) := fun i hi => hkeep _ (by unfold oY oRsa; omega_using [hi]) (by
    simp only [inR_cons, inR_nil, or_false]; unfold oY oSt; omega_using [hN, hso])
  have hst' : hH.md.stateAt u'.mem (off S oSt) = hH.md.compressList hH.iv (yList V (nbm * H.P.B)) (b + 1) := by
    rw [stateAt_rep hH Rv Ru' (o := oSt) (by unfold oSt oRsa; omega_using [hN]) (fun _ _ => rfl), hstv, hst,
      MdStream.Md.compressList_succ]
    refine congrArg (hH.md.compress _) (hH.md.parse_congr fun k hk => ?_)
    rw [Nat.add_assoc, hY _ (by omega_arith),
      yList_getD V (show H.P.B * b + k < nbm * H.P.B by
        have := Nat.mul_le_mul_right H.P.B hb; rw [Nat.succ_mul, Nat.mul_comm b] at this; omega_arith)]
  refine ⟨Lu', hk'.2.1.trans (hrdv.trans hrd), hk'.2.2.trans (hwrv.trans hwr),
    fun r hr => (hk'.gpr (cs_keep hr (by decide))).trans ((hcsv r hr).trans (hcs r hr)), _, Ru',
    fun o ho hno => ?_, hst'⟩
  simp only [inR_cons, inR_nil, or_false, not_or] at hno
  simp only [inR_cons, inR_nil, or_false]
  rw [ifn (by omega_using [hno])]
  exact hkeep o ho (by simp only [inR_cons, inR_nil, or_false]; omega_using [hno])

/-- `Y` after the `0x80` and the length field copied to the last block: the
padded message. -/
theorem y_last {B L fb : Nat} (msg len : List Byte) (hfb : fb = lastBlk B L msg.length) (hLB : L < B)
    (hlen : len.length = L) (V : Nat → Byte)
    (hV : ∀ j < B * (fb + 1), V (oY + j) = msg.getD j 0 ||| (if j = msg.length then 0x80 else 0)) :
    ∀ j < B * (fb + 1), cpV V (fun i => len.getD i 0) (oY + (B * (fb + 1) - L)) L (oY + j) =
      padded B L msg len j := by
  intro j hj
  have hfit : msg.length + L < B * (fb + 1) := by
    subst hfb; unfold lastBlk
    have := Nat.lt_div_mul_add (a := msg.length + L) (b := B) (by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]; omega
  rw [← y_padded msg len hfb hLB hlen V hV j hj]
  rw [Nat.mul_add, Nat.mul_one] at hj hfit
  simp only [cpV, lenAt]
  by_cases h : oY + (B * fb + B - L) ≤ oY + j ∧ oY + j < oY + (B * fb + B - L) + L
  · have hm : msg.getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have zo : ∀ x : Byte, 0 ||| x = x := fun _ => BitVec.zero_or
    rw [Nat.mul_add, Nat.mul_one, ifp h, ifp (by omega), hV j (by rw [Nat.mul_add, Nat.mul_one]; omega), hm,
      ifn (by omega : j ≠ msg.length), zo, zo, show oY + j - (oY + (B * fb + B - L)) =
        oY + j - (oY + B * fb + (B - L)) by omega]
  · rw [Nat.mul_add, Nat.mul_one, ifn h, ifn (by omega)]

include hH K in
/-- `fixedHash` on the first `ℓ` bytes of `Y` (`sL`), in the `nbm` blocks
(`sNb`) of their padding, whose `0x80` is already in place. -/
theorem fixedHash_gen {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {ℓ nbm : Nat} (hl : W 27 = BitVec.ofNat 64 ℓ)
    (hn : W 28 = BitVec.ofNat 64 nbm) (hnbm : nbm = lastBlk H.P.B H.P.L ℓ + 1) (hnb : nbm * H.P.B ≤ 2048) :
    WP isa (fixedHash H) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t'.gpr r = t.gpr r) ∧
      ∃ V' W', Rep t'.mem F S V' W' ∧ (∀ o < oRsa, ctOut o → V' o = V o) ∧
        (∀ k < nW, k ≠ 29 → k ≠ 30 → W' k = W k) ∧
        ∀ msg : List Byte, msg.length = ℓ →
          (∀ i < nbm * H.P.B, V (oY + i) = msg.getD i 0 ||| (if i = ℓ then 0x80 else 0)) →
          (List.range H.D).map (fun i => V' (oDig + i)) = hH.SH.H.hash msg := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hN := hH.N_le
  have hL := hH.dims.L
  have hNL := hH.hNL
  have hDN := hH.hDN
  have hLB : H.P.L < H.P.B := by have := hH.dims.L; rcases hH.dims.B with h | h <;> omega
  have h1 : 1 ≤ nbm := by omega
  have hBn : H.P.B ≤ nbm * H.P.B := Nat.le_mul_of_pos_left _ h1
  have hfitℓ : ℓ + H.P.L < nbm * H.P.B := by
    rw [hnbm]; unfold lastBlk
    have := Nat.lt_div_mul_add (a := ℓ + H.P.L) (b := H.P.B) hB0
    rw [Nat.succ_mul]; omega
  unfold fixedHash seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (WP.mono (ctInit_ok hH K L R) fun u1 ⟨L1, rd1, wr1, cs1, R1, iv1⟩ => ?_)
  -- The length field.
  refine WP.seq (WP.mono (lenField_ok hH L1 R1 hl (by omega)) fun u3 ⟨L3, k3, R3⟩ => ?_)
  -- Into the last block.
  refine WP.seq (WP.mono (lenLast_ok hH L3 R3 (len := hH.md.lenBytes ℓ) (fun i hi => by
      simp only [lenV, hH.md.lenBytes_length]; rw [ifp (by omega), Nat.add_sub_cancel_left])
    (by simp [upd, hn]) h1 hnb) fun u4 ⟨L4, k4, R4⟩ => ?_)
  -- Every block.
  refine WP.seq (WP.mono (compAll_ok hH L4 R4 ?_ (by simp [upd, hn]) h1 hnb)
    fun u5 ⟨L5, rd5, wr5, cs5, V5, R5, keep5, st5⟩ => ?_)
  · rw [← iv1]
    refine stateAt_rep hH R1 R4 (by unfold oSt oRsa; omega) fun i hi => ?_
    simp only [cpV, lenV]
    rw [ifn (by unfold oY oSt; omega), ifn (by unfold oLen oSt; omega)]
  -- The digest.
  refine WP.mono (digestAt_ok hH L5 R5 (src := oSt) (by unfold oSt oDig; omega)) fun u6 ⟨L6, k6, R6⟩ => ?_
  have c1 : oY = 3584 := rfl
  have c2 : oLen = 2368 := rfl
  have c3 : oDig = 2304 := rfl
  have c4 : oSt = 2048 := rfl
  have hso := hH.hso
  refine ⟨L6, k6.2.1.trans (rd5.trans (k4.2.1.trans (k3.2.1.trans rd1))),
    k6.2.2.trans (wr5.trans (k4.2.2.trans (k3.2.2.trans wr1))), ?_, _, _, R6, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hcs : r ∈ calleeSaved := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h1 : r ∉ [Reg.rbx, .rbp, .rax] := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h2 : r ∉ [Reg.rsi, .rcx, .rax, .r8] := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h3 : r ∉ [Reg.rbx, .r12, .rax] := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [k6.gpr h1, cs5 r hcs, k4.gpr h2, k3.gpr h3, cs1 r hcs]
  · intro o ho ⟨h1, h2⟩
    have hno : ¬ (oDig ≤ o ∧ o < oDig + H.P.N) := by omega
    simp only [hno, ite_false]
    rw [keep5 o ho (by simp only [inR_cons, inR_nil, or_false]; omega)]
    simp only [cpV, lenV, inR_cons, inR_nil, or_false]
    rw [ifn (by omega), ifn (by rw [hH.md.lenBytes_length]; omega), ifn (by omega)]
  · intro k hk h29 h30
    simp [upd, h29, h30]
  · intro msg hml hY
    subst hml
    rw [hH.hash, MdStream.Md.hash, ← range_map_getD (by rw [hH.md.digest_length]; exact hDN)]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [show oDig ≤ oDig + i ∧ oDig + i < oDig + H.P.N from ⟨by omega, by omega⟩,
      Nat.add_sub_cancel_left]
    rw [st5]
    refine congrArg (fun x => (hH.md.digest x).getD i 0) ?_
    rw [RsaPss.pad_length hH.md msg hB0 (by omega), Nat.mul_div_cancel_left _ hB0, ← hnbm]
    refine hH.md.compressList_congr fun j hj => ?_
    have hj' : j < nbm * H.P.B := by rw [Nat.mul_comm]; exact hj
    rw [yList_getD _ hj', RsaPss.pad_getD hH.md msg hB0 (by omega) (by rw [← hnbm]; exact hj)]
    have e : oY + (nbm * H.P.B - H.P.L) = oY + (H.P.B * (lastBlk H.P.B H.P.L msg.length + 1) - H.P.L) := by
      rw [← hnbm, Nat.mul_comm]
    rw [e]
    refine y_last msg _ rfl hLB (hH.md.lenBytes_length _) _ (fun j' hj' => ?_) j (by rw [← hnbm]; exact hj)
    have hj'' : j' < nbm * H.P.B := by rw [hnbm, Nat.mul_comm]; exact hj'
    simp only [lenV, hH.md.lenBytes_length, inR_cons, inR_nil, or_false]
    rw [ifn (by omega), ifn (by omega), hY j' hj'']

end VG.Proof.RsaPss.X86_64
