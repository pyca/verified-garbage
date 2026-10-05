import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
import VerifiedGarbage.Proof.RsaPss.X86_64.Params

/-!
# RSASSA-PSS on x86-64: the blocks of the encoding

`Y` cleared (`clearY_ok`), `mHash` and the salt copied after its eight
zeros (`copyDigest_ok`, `copySaltY_ok`), the length of `M'` and its blocks
(`signLen_ok`); `EM` cleared (`clearEm_ok`), the `0x01` and the salt
(`putSalt_ok`), `H` and `0xbc` (`putH_ok`) placed in it, and the top bits
of `maskedDB` cleared (`clearTop_ok`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off Scr off_off ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-! ## `Y` -/

theorem clearY_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa clearY u fun u' => Lay u' F S ∧ Keep [.rcx, .rax, .r8] u u' ∧ u'.gpr .rcx = off S oY ∧
      Rep u'.mem F S (clrV V oY 2048) W := by
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax, .r8] (Q := fun v => v.gpr .rcx = off S oY ∧ v.gpr .rax = 0 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, hm⟩, hk⟩ => ?_)
  · have hs := L.slot
    simp only [Bignum.X86_64.word] at hs
    xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (clearQ_ok Lv (hm ▸ R) (n := 2048) (by decide) (by decide) (by decide) (by decide) h₁ h₂ h₃)
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), (kw.gpr (by decide)).trans h₁, Rw⟩

variable {H : Hash} (hH : Proof.Pbkdf2.Md.X86_64.HashOK H)

include hH in
/-- `mHash`, the `hLen` bytes at `p`, after the eight zeros of `Y`. -/
theorem copyDigest_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {p : Addr} (hp : W 37 = p) (hcx : u.gpr .rcx = off S oY)
    (hsrc : ∀ i < H.D, InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < H.D, ∀ j < H.D, p + BitVec.ofNat 64 i ≠ off S (oY + 8 + j)) :
    WP isa (copyDigest H) u fun u' => Lay u' F S ∧ Keep [.rsi, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV V (fun i => u.mem (p + BitVec.ofNat 64 i)) (oY + 8) H.D) W := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (WP.mono (WP.keep [.rsi, .r8] (Q := fun v => v.gpr .rsi = p ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, hm⟩, hk⟩ => ?_)
  · xrun [copyDigest, ea_sp, L.rsp, L.ld (d := sDig) (by decide), R.rd (d := sDig) 37 rfl (by decide), hp]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (copy_ok Lv (hm ▸ R) (d := .rcx) (by decide) (p := p) (o := oY) (disp := 8) (n := H.D)
    (stepI_ok (show H.D < 2 ^ 31 by omega) v [.rax, .r8]) hD (by unfold oY oRsa; omega) h₁
    ((hk.gpr (by decide)).trans hcx) h₂ (fun i hi => by rw [hk.2.1, hk.2.2]; exact hsrc i hi) hdis)
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), by rw [hm] at Rw; exact Rw⟩

theorem cpV_zero (V : Nat → Byte) (f : Nat → Byte) (o : Nat) : cpV V f o 0 = V := by
  funext x; simp only [cpV]; rw [ifn (by omega)]

include hH in
/-- The salt, the `sl` bytes at `q`, after `mHash` in `Y`. -/
theorem copySaltY_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {q : Addr} {sl : Nat} (hq : W 39 = q) (hsl : W 40 = BitVec.ofNat 64 sl)
    (hsl' : 8 + H.D + sl ≤ 2048) (hcx : u.gpr .rcx = off S oY)
    (hsrc : ∀ i < sl, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < sl, ∀ j < sl, q + BitVec.ofNat 64 i ≠ off S (oY + (8 + H.D) + j)) :
    WP isa (copySaltY H) u fun u' => Lay u' F S ∧ Keep [.rsi, .r10, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV V (fun i => u.mem (q + BitVec.ofNat 64 i)) (oY + (8 + H.D)) sl) W := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (WP.mono (WP.keep [.rsi, .r10, .r8] (Q := fun v => v.gpr .rsi = q ∧
      v.gpr .r10 = BitVec.ofNat 64 sl ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.zf = some (decide (sl = 0)) ∧
      v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₁₀, h₂, hz, hm⟩, hk⟩ => ?_)
  · xrun [copySaltY, ea_sp, L.rsp, L.ld (d := sSalt) (by decide), L.ld (d := sSaltLen) (by decide),
      R.rd (d := sSalt) 39 rfl (by decide), R.rd (d := sSaltLen) 40 rfl (by decide), hq, hsl]
    rw [BitVec.and_self, ofNat_beq_zero (by omega)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    subst hb
    refine WP.mono (WP.keep [] (Q := fun w => w = v) ?_ rfl) fun w ⟨hw, _⟩ => ?_
    · xrun
    · subst hw
      exact ⟨Lv, hk.mono (by decide), by rw [cpV_zero, hm]; exact R⟩
  · rw [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok Lv (hm ▸ R) (d := .rcx) (by decide) (p := q) (o := oY) (disp := 8 + H.D) (n := sl)
      (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₁₀) (by omega)
      (by unfold oY oRsa; omega) h₁ ((hk.gpr (by decide)).trans hcx) h₂
      (fun i hi => by rw [hk.2.1, hk.2.2]; exact hsrc i hi) hdis)
      fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), by rw [hm] at Rw; exact Rw⟩

/-! ## The length of `M'` -/

include hH in
theorem signLen_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {sl : Nat} (hsl : W 40 = BitVec.ofNat 64 sl) (hsl' : sl < 2 ^ 32) :
    WP isa (.block (signLen H)) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      Rep u'.mem F S V (upd (upd W 27 (BitVec.ofNat 64 (8 + H.D + sl)))
        28 (BitVec.ofNat 64 ((8 + H.D + sl + H.P.L) / H.P.B + 1))) := by
  obtain ⟨hpow, hlg1, hlg2⟩ := lgB_spec hH
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have G := L.geo
  have R1 := R.wf G (k := 27) (by decide) (BitVec.ofNat 64 (8 + H.D + sl))
  have R2 := R1.wf G (k := 28) (by decide) (BitVec.ofNat 64 ((8 + H.D + sl + H.P.L) / H.P.B + 1))
  rw [show off F (8 * 27) = off F sL from rfl] at R1 R2
  rw [show off F (8 * 28) = off F sNb from rfl] at R2
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = (u.mem.writeW (off F sL)
      (BitVec.ofNat 64 (8 + H.D + sl))).writeW (off F sNb) (BitVec.ofNat 64 ((8 + H.D + sl + H.P.L) / H.P.B + 1)))
      ?_ rfl) fun u' ⟨hm, k⟩ => ⟨L.of_rep' R (hm ▸ R2) (by simp [upd]) (k.gpr (by decide)) k.2.2, k, hm ▸ R2⟩
  have hsh : BitVec.ofNat 64 (8 + H.D + sl + H.P.L) >>> lgB H = BitVec.ofNat 64 ((8 + H.D + sl + H.P.L) / H.P.B) := by
    rw [shr_ofNat (lgB H) (by omega), hpow]
  xrun [signLen, ea_sp, L.rsp, L.ld (d := sSaltLen) (by decide), L.st (d := sL) (by decide),
    L.st (d := sNb) (by decide), R.rd (d := sSaltLen) 40 rfl (by decide), hsl, BitVec.ofNat_add_ofNat,
    VG.Proof.MlKem.X86_64.sx_ofNat (show 8 + H.D < 2 ^ 31 by omega),
    VG.Proof.MlKem.X86_64.sx_ofNat (show H.P.L < 2 ^ 31 by omega), hsh, ofNat_add_lit,
    show sl + (8 + H.D) = 8 + H.D + sl by omega,
    show 1 ≤ lgB H ∧ lgB H ≤ 63 from ⟨by omega, by omega⟩]

/-! ## `EM` -/

theorem clearEm_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 17 = BitVec.ofNat 64 k) (hk1 : 1 ≤ k) (hk2 : k ≤ 1024) :
    WP isa clearEm u fun u' => Lay u' F S ∧ Keep [.rcx, .r10, .rax, .r8] u u' ∧
      Rep u'.mem F S (clrV V oEm k) W := by
  refine WP.seq (WP.mono (WP.keep [.rcx, .r10, .rax, .r8] (Q := fun v => v.gpr .rcx = off S oEm ∧
      v.gpr .r10 = BitVec.ofNat 64 k ∧ v.gpr .rax = 0 ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₁₀, h₂, h₃, hm⟩, hkv⟩ => ?_)
  · have hs := L.slot
    simp only [Bignum.X86_64.word] at hs
    xrun [clearEm, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      L.ld (d := sK) (by decide), R.rd (d := sK) 17 rfl (by decide), hk,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hkv.gpr (by decide)) hkv.2.2 (by rw [hm])
  refine WP.mono (fill_ok Lv (hm ▸ R) (n := k) (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.r8] by decide)
    (by decide) h₁₀) (by omega) (by unfold oEm oRsa; omega) h₁ h₂ h₃)
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hkv.trans kw).mono (by decide), Rw⟩

/-- `EM` with `0x01` before the salt, at `e + db - sl - 1`. -/
theorem putSalt_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db sl : Nat} {q : Addr} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hq : W 39 = q) (hsl : W 40 = BitVec.ofNat 64 sl) (hfit : sl + 1 ≤ db) (hend : e + db ≤ oRsa)
    (hsrc : ∀ i < sl, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < sl, ∀ j < sl + 1, q + BitVec.ofNat 64 i ≠ off S (e + db - sl - 1 + j)) :
    WP isa putSalt u fun u' => Lay u' F S ∧ Keep [.rdi, .rsi, .r10, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV (upd V (e + db - sl - 1) 1) (fun i => u.mem (q + BitVec.ofNat 64 i))
        (e + db - sl - 1 + 1) sl) W := by
  have G := L.geo
  have R1 := R.wb G (o := e + db - sl - 1) (by omega) (1 : Byte)
  refine WP.seq (WP.mono (WP.keep [.rdi, .rax] (Q := fun v => v.gpr .rdi = off S (e + db - sl - 1) ∧
      v.mem = u.mem.writeW (off S (e + db - sl - 1)) (1 : Byte)) ?_ rfl) fun v ⟨⟨h₁, hm⟩, hk⟩ => ?_)
  · have ea : off S e + BitVec.ofNat 64 db - BitVec.ofNat 64 sl - 1 = off S (e + db - sl - 1) := by
      rw [off_plus, off_sub S (by omega), off_sub1 S (by omega)]
    xrun [putSalt, ea_sp, ea_at0, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide),
      L.ld (d := sSaltLen) (by decide), R.rd (d := sEb) 23 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      R.rd (d := sSaltLen) 40 rfl (by decide), he, hdb, hsl, ea, L.sst8 (d := e + db - sl - 1) (by omega)]
    rfl
  have R1' : Rep v.mem F S (upd V (e + db - sl - 1) 1) W := hm ▸ R1
  have Lv : Lay v F S := L.of_rep R R1' (hk.gpr (by decide)) hk.2.2
  refine WP.seq (WP.mono (WP.keep [.rsi, .r10, .r8] (Q := fun w => w.gpr .rsi = q ∧
      w.gpr .r10 = BitVec.ofNat 64 sl ∧ w.gpr .r8 = BitVec.ofNat 64 0 ∧ w.zf = some (decide (sl = 0)) ∧
      w.mem = v.mem) ?_ rfl) fun w ⟨⟨h₂, h₁₀, h₈, hz, hm'⟩, hk'⟩ => ?_)
  · xrun [ea_sp, Lv.rsp, Lv.ld (d := sSalt) (by decide), Lv.ld (d := sSaltLen) (by decide),
      R1'.rd (d := sSalt) 39 rfl (by decide), R1'.rd (d := sSaltLen) 40 rfl (by decide), hq, hsl]
    rw [BitVec.and_self, ofNat_beq_zero (by unfold oRsa at hend; omega)]
  have Lw : Lay w F S := Lv.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm'])
  have hsrc' : ∀ i < sl, u.mem (q + BitVec.ofNat 64 i) = w.mem (q + BitVec.ofNat 64 i) := fun i hi => by
    rw [hm', hm, VG.WriteBytes.writeW8_apply, ifn (fun h => hdis i hi 0 (by omega) (by rw [h]; rfl))]
  refine WP.ite (M := isa) _ (show isa.eval .e w = _ from hz) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    subst hb
    refine WP.mono (WP.keep [] (Q := fun x => x = w) ?_ rfl) fun x ⟨hx, _⟩ => ?_
    · xrun
    · subst hx
      exact ⟨Lw, (hk.trans hk').mono (by decide), by rw [cpV_zero, hm']; exact R1'⟩
  · rw [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok Lw (hm' ▸ R1') (d := .rdi) (by decide) (p := q) (o := e + db - sl - 1) (disp := 1)
      (n := sl) (stepR_ok (by unfold oRsa at hend; omega) w (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₁₀)
      (by omega) (by omega) h₂ ((hk'.gpr (by decide)).trans h₁) h₈
      (fun i hi => by rw [hk'.2.1, hk'.2.2, hk.2.1, hk.2.2]; exact hsrc i hi)
      (fun i hi j hj => by
        have := hdis i hi (1 + j) (by omega)
        rwa [show e + db - sl - 1 + (1 + j) = e + db - sl - 1 + 1 + j by omega] at this))
      fun x ⟨Lx, kx, Rx⟩ => ⟨Lx, (hk.trans (hk'.trans kx)).mono (by decide), ?_⟩
    refine (congrArg (fun V' => Rep x.mem F S V' W) (funext fun y => ?_)).mp Rx
    simp only [cpV]
    split
    · rw [hsrc' _ (by omega)]
    · rfl

include hH in
/-- `H`, the digest at `scratch + oDig`, after `DB`, and `0xbc` at the end of
`EM`. -/
theorem putH_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db k : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hk : W 17 = BitVec.ofNat 64 k) (he1 : oEm ≤ e) (hend : e + db + H.D + 1 = oEm + k) (hk2 : k ≤ 1024) :
    WP isa (putH H) u fun u' => Lay u' F S ∧ Keep [.rdi, .rsi, .rax, .r8] u u' ∧
      Rep u'.mem F S (upd (cpV V (fun i => V (oDig + i)) (e + db) H.D) (oEm + k - 1) 0xbc) W := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c3 : oDig = 2304 := rfl
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  unfold putH
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi, .r8, .rax] (Q := fun v => v.gpr .rdi = off S (e + db) ∧
      v.gpr .rsi = off S oDig ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide), R.rd (d := sEb) 23 rfl (by decide),
      R.rd (d := sDb) 24 rfl (by decide), he, hdb, off_plus,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hkv.gpr (by decide)) hkv.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.seq (WP.mono (copy_ok Lv Rv (d := .rdi) (by decide) (p := off S oDig) (o := e + db) (disp := 0)
    (n := H.D) (stepI_ok (show H.D < 2 ^ 31 by omega) v [.rax, .r8]) hD (by unfold oRsa; omega) h₂ h₁ h₃
    (fun i hi => by rw [off_plus]; exact Lv.sld8 (by unfold oRsa; omega))
    (fun i hi j hj => by rw [off_plus]; exact Offset.add_ofNat_ne S (by omega) (by omega) (by omega)))
    fun w ⟨Lw, kw, Rw⟩ => ?_)
  have Rw' : Rep w.mem F S (cpV V (fun i => V (oDig + i)) (e + db) H.D) W := by
    refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
    simp only [cpV, Nat.add_zero]
    split
    · rw [off_plus, Rv.scr _ (by unfold oRsa; omega)]
    · rfl
  have R2 := Rw'.wb Lw.geo (o := oEm + k - 1) (by unfold oRsa; omega) (0xbc : Byte)
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun x => x.mem = w.mem.writeW (off S (oEm + k - 1)) (0xbc : Byte))
    ?_ rfl) fun x ⟨hmx, kx⟩ => ⟨Lw.of_rep Rw' (hmx ▸ R2) (kx.gpr (by decide)) kx.2.2,
      (hkv.trans (kw.trans kx)).mono (by decide), hmx ▸ R2⟩
  have hs' : w.mem.readW (off F sScr) 64 = S := by rw [Rw'.rd (d := sScr) 21 rfl (by decide), ← R.rd (d := sScr) 21 rfl (by decide)]; exact hs
  xrun [scr, List.cons_append, List.nil_append, ea_sp, ea_at0, Lw.rsp, Lw.ld (d := sScr) (by decide), hs',
    Lw.ld (d := sK) (by decide), Rw'.rd (d := sK) 17 rfl (by decide), hk, off_plus, off_sub1 S (show 1 ≤ oEm + k by omega),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), Lw.sst8 (d := oEm + k - 1) (by unfold oRsa; omega)]
  rfl

theorem trunc_and (x y : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 x &&& BitVec.setWidth 64 y) = x &&& y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega)]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ y.isLt)

/-- The top bits of `maskedDB`'s first byte cleared by the mask in `sC`. -/
theorem clearTop_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e : Nat} {c : Byte} (he : W 23 = off S e) (hc : W 25 = BitVec.setWidth 64 c)
    (he1 : e < oRsa) :
    WP isa (.block clearTop) u fun u' => Lay u' F S ∧ Keep [.rdi, .rax] u u' ∧
      Rep u'.mem F S (upd V e (V e &&& c)) W := by
  have R2 := R.wb L.geo (o := e) he1 (V e &&& c)
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun x => x.mem = u.mem.writeW (off S e) (V e &&& c))
    ?_ rfl) fun x ⟨hmx, kx⟩ => ⟨L.of_rep R (hmx ▸ R2) (kx.gpr (by decide)) kx.2.2, kx, hmx ▸ R2⟩
  xrun [clearTop, ea_sp, ea_at0, L.rsp, L.ld (d := sEb) (by decide), R.rd (d := sEb) 23 rfl (by decide), he,
    L.sld8 (d := e) (by omega), R.scr e he1, L.ld (d := sC) (by decide), R.rd (d := sC) 25 rfl (by decide), hc,
    L.sst8 (d := e) (by omega)]
  rw [trunc_and]

end VG.Proof.RsaPss.X86_64
