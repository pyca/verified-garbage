import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.Mask

/-!
# RSAES-OAEP on x86-64: MGF1

`mgfXor lay G` XORs `MGF1(src, dstLen)` into `dst` (`mgfXor_ok`), where
`src` (`srcLen` bytes) and `dst` (`dstLen` bytes) are ranges of our working
space below the hash function's, given by MGF1's slots: for each counter
`c`, the state is set by `init`, `update` absorbs `src` and then
`I2OSP(c, 4)` (written to `scratch + oCtr`, `counter_ok`), `finalize`
writes the digest to `scratch + oDig`, and the first
`min(hLen, dstLen - c hLen)` bytes of the digest are XORed into
`dst + c hLen` (`xorOut_ok`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs round xorOut xorHead nextCtr initArgs updSrcArgs
  updCtrArgs finArgs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-! ## Where MGF1 works -/

/-- The ranges of our working space the hash functions' calls and MGF1's
counter write. -/
def hashR : List (Nat × Nat) := [(oSt, 256), (oDig, 64), (oCtr, 4), (oW, 2048)]

/-- Outside them. -/
def mOut (o : Nat) : Prop := ¬ inR hashR o

theorem mOut_iff (o : Nat) : mOut o ↔ o < oSt ∨ (oDig + 64 ≤ o ∧ o < oCtr) ∨ (oCtr + 4 ≤ o ∧ o < oW) ∨
    oW + 2048 ≤ o := by
  simp only [mOut, hashR, inR_cons, inR_nil, or_false, oSt, oDig, oCtr, oW]
  omega_using []

/-- `src` and `dst`, below the hash functions' ranges and apart. -/
structure MFit (src srcLen dst dstLen : Nat) : Prop where
  fs : src + srcLen ≤ oSt
  fd : dst + dstLen ≤ oSt
  sep : src + srcLen ≤ dst ∨ dst + dstLen ≤ src
  pos : 0 < dstLen
  dstB : dstLen ≤ 2048

/-- What MGF1's slots hold. -/
structure MArgs (W : Nat → BitVec 64) (S : Addr) (src srcLen dst dstLen : Nat) : Prop where
  hsrc : W 15 = off S src
  hsl : W 16 = BitVec.ofNat 64 srcLen
  hdst : W 17 = off S dst
  hdl : W 18 = BitVec.ofNat 64 dstLen

theorem MArgs.of_eq {W W' : Nat → BitVec 64} {S : Addr} {src srcLen dst dstLen : Nat}
    (h : MArgs W S src srcLen dst dstLen) (hW : ∀ k, 15 ≤ k → k ≤ 18 → W' k = W k) :
    MArgs W' S src srcLen dst dstLen :=
  ⟨(hW 15 (by omega_using []) (by omega_using [])).trans h.hsrc, (hW 16 (by omega_using []) (by omega_using [])).trans h.hsl,
    (hW 17 (by omega_using []) (by omega_using [])).trans h.hdst, (hW 18 (by omega_using []) (by omega_using [])).trans h.hdl⟩

/-- A slot, read through `Rep`. -/
theorem Rep.slot {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W) {d k : Nat}
    (hd : d = 8 * k) (hk : k < nW) {v : BitVec 64} (hv : W k = v) : m.readW (off F d) 64 = v := by
  rw [← hv, R.rd k hd hk]

variable {G : Stream} (hG : StreamOK G)

/-! ## The arguments of the calls -/

theorem updSrc_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {src srcLen dst dstLen : Nat} (A : MArgs W S src srcLen dst dstLen) :
    WP isa (.block (updSrcArgs lay)) u fun u' => u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 0 ∧
      u'.gpr .rdx = off S src ∧ u'.gpr .rcx = BitVec.ofNat 64 srcLen ∧ u'.gpr .r8 = off S oW ∧ u'.mem = u.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx, .r8] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 0 ∧ u'.gpr .rdx = off S src ∧ u'.gpr .rcx = BitVec.ofNat 64 srcLen ∧
      u'.gpr .r8 = off S oW ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, e, f⟩, k⟩ => ⟨a, b, c, d, e, f, k⟩
  xrun [updSrcArgs, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sSrc) (by decide), L.ld (d := sSrcLen) (by decide), hs,
    R.slot (d := sSrc) (k := 15) rfl (by decide) A.hsrc, R.slot (d := sSrcLen) (k := 16) rfl (by decide) A.hsl,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

/-- `I2OSP(c, 4)` at `scratch + oCtr`. -/
def ctrV (V : Nat → Byte) (c : Nat) (x : Nat) : Byte :=
  if oCtr ≤ x ∧ x < oCtr + 4 then (Spec.Rsa.i2osp c 4).getD (x - oCtr) 0 else V x

theorem trunc_ofNat (x : Nat) : BitVec.setWidth 8 (BitVec.ofNat 64 x) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

theorem updCtr_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen c : Nat} (hl : W 16 = BitVec.ofNat 64 srcLen) (hc : W 19 = BitVec.ofNat 64 c)
    (hc32 : c < 2 ^ 32) :
    WP isa (.block (updCtrArgs lay)) u fun u' => Lay u' F S ∧ u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 srcLen ∧ u'.gpr .rdx = off S oCtr ∧ u'.gpr .rcx = BitVec.ofNat 64 4 ∧
      u'.gpr .r8 = off S oW ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8, .rax] u u' ∧ Rep u'.mem F S (ctrV V c) W := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have G' := L.geo
  have R1 := (((R.wb G' (o := oCtr + 3) (by decide) (BitVec.ofNat 8 c)).wb G'
    (o := oCtr + 2) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8))).wb G'
    (o := oCtr + 1) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).wb G'
    (o := oCtr) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .rax] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 srcLen ∧ u'.gpr .rdx = off S oCtr ∧ u'.gpr .rcx = BitVec.ofNat 64 4 ∧
      u'.gpr .r8 = off S oW ∧ u'.mem =
      (((u.mem.writeW (off S (oCtr + 3)) (BitVec.ofNat 8 c)).writeW (off S (oCtr + 2))
        (BitVec.ofNat 8 (c / 2 ^ 8))).writeW (off S (oCtr + 1)) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).writeW
        (off S oCtr) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))) ?_ rfl)
    fun u' ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk⟩ => ⟨?_, h₁, h₂, h₃, h₄, h₅, hk, hm ▸ ?_⟩
  · xrun [updCtrArgs, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_at, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), L.ld (d := sCtr) (by decide), L.ld (d := sSrcLen) (by decide), hs,
      R.slot (d := sCtr) (k := 19) rfl (by decide) hc, off_off,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oCtr < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide),
      L.sst8 (d := oCtr + 3) (by decide), L.sst8 (d := oCtr + 2) (by decide), L.sst8 (d := oCtr + 1) (by decide),
      L.sst8 (d := oCtr) (by decide), trunc_ofNat, shr_ofNat 8 (show c < 2 ^ 64 by omega_using [hc32]),
      shr_ofNat 8 (show c / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]), shr_ofNat 8 (show c / 2 ^ 8 / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]),
      zx32 (show 4 < 2 ^ 32 by omega_using []), show off S oCtr + 0 = off S oCtr from BitVec.add_zero _]
    have w14 : W 14 = S := (R.rd 14 rfl (by decide)).symm.trans hs
    simp only [show S + BitVec.ofNat 64 oCtr = off S oCtr from rfl, R1.slot (d := sScr) (k := 14) rfl (by decide) w14,
      R1.slot (d := sSrcLen) (k := 16) rfl (by decide) hl]
    exact ⟨trivial, trivial, trivial⟩
  · exact L.congr (hk.gpr (by decide)) hk.2.2 (by
      rw [hm, slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, R1.fr 14 (by decide), R.fr 14 (by decide)])
  · refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R1
    have e1 : c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 3 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    have e2 : c / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 2 := by rw [Nat.div_div_eq_div_mul]
    have e3 : c / 2 ^ 8 = c / 256 ^ 1 := rfl
    simp only [upd, ctrV, Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases (show x = oCtr ∨ x = oCtr + 1 ∨ x = oCtr + 2 ∨ x = oCtr + 3 ∨
        ¬(oCtr ≤ x ∧ x < oCtr + 4) by omega_using []) with h | h | h | h | h
    · subst h; simp [e1]
    · subst h; simp [e2]
    · subst h; simp [e3]
    · subst h; simp
    · rw [ifn h, ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h])]

theorem finA_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen : Nat} (hl : W 16 = BitVec.ofNat 64 srcLen) :
    WP isa (.block (finArgs lay)) u fun u' => u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 (srcLen + 4) ∧
      u'.gpr .rdx = off S oDig ∧ u'.gpr .rcx = off S oW ∧ u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 (srcLen + 4) ∧ u'.gpr .rdx = off S oDig ∧ u'.gpr .rcx = off S oW ∧
      u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, d, e, k⟩
  xrun [finArgs, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sSrcLen) (by decide), hs,
    R.slot (d := sSrcLen) (k := 16) rfl (by decide) hl, ofNat_add_lit,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

/-! ## The digest into `dst` -/

theorem xorOut_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {dst dstLen done : Nat} (hfit : dst + dstLen ≤ oSt) (hD : 0 < G.D) (hDF : G.D ≤ 64)
    (he : W 17 = off S dst) (hdb : W 18 = BitVec.ofNat 64 dstLen) (hdn : W 20 = BitVec.ofNat 64 done)
    (hlt : done < dstLen) :
    WP isa (xorOut lay G) u fun u' => Lay u' F S ∧ Keep [.rcx, .rdi, .rax, .r10, .r8, .rdx] u u' ∧
      Rep u'.mem F S (xorV V oDig (dst + done) (min G.D (dstLen - done))) W := by
  have c1 : oSt = 3072 := rfl
  have c3 : oDig = 3328 := rfl
  have hs := L.slot
  simp only [Bignum.word] at hs
  unfold xorOut seqs seqs seqs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdi, .rax, .r10, .rdx] (Q := fun v => v.gpr .rcx = off S oDig ∧
      v.gpr .rdi = off S (dst + done) ∧ v.gpr .rax = BitVec.ofNat 64 (dstLen - done) ∧
      v.gpr .r10 = BitVec.ofNat 64 G.D ∧ v.cf = some (decide (dstLen - done < G.D)) ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk⟩ => ?_)
  · xrun [xorHead, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), hs, VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide),
      L.ld (d := sDst) (by decide), L.ld (d := sDone) (by decide), L.ld (d := sDstLen) (by decide),
      R.slot (d := sDst) (k := 17) rfl (by decide) he, R.slot (d := sDstLen) (k := 18) rfl (by decide) hdb,
      R.slot (d := sDone) (k := 20) rfl (by decide) hdn,
      VG.Offset.ofNat_sub_ofNat (show done ≤ dstLen by omega_using [hlt]), zx32 (show G.D < 2 ^ 32 by omega_using [hDF]), off_plus]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hfit, c1]), Nat.mod_eq_of_lt (by omega_using [hDF])]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  have hmin : 0 < min G.D (dstLen - done) := by omega_using [hD, hlt]
  refine WP.seq (WP.mono (Q := fun (w : State) => Keep [.r10] v w ∧ w.mem = v.mem ∧
      w.gpr .r10 = BitVec.ofNat 64 (min G.D (dstLen - done))) ?_ fun w ⟨kw, hmw, h10⟩ => ?_)
  · refine WP.ite (M := isa) _ (show isa.eval .b v = _ from h₅) (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      refine WP.mono (WP.keep [.r10] (Q := fun w => w.mem = v.mem ∧ w.gpr .r10 = BitVec.ofNat 64 (dstLen - done))
        ?_ rfl) fun w ⟨⟨hm', h'⟩, k'⟩ => ⟨k', hm', by rw [h', Nat.min_eq_right (by omega_using [hb])]⟩
      xrun [h₃]
    · rw [decide_eq_false_iff_not] at hb
      refine WP.mono (WP.keep [] (Q := fun w => w = v) ?_ rfl) fun w ⟨hw, _⟩ => ?_
      · xrun
      · subst hw; exact ⟨Keep.refl _ _, rfl, by rw [h₄, Nat.min_eq_left (by omega_using [hb])]⟩
  have Lw : Lay w F S := Lv.congr (kw.gpr (by decide)) kw.2.2 (by rw [hmw])
  have Rw : Rep w.mem F S V W := hmw ▸ Rv
  refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r8 = BitVec.ofNat 64 0 ∧ x.mem = w.mem) ?_ rfl)
    fun x ⟨⟨h8, hmx⟩, kx⟩ => ?_)
  · xrun
  have Lx : Lay x F S := Lw.congr (kx.gpr (by decide)) kx.2.2 (by rw [hmx])
  have Rx : Rep x.mem F S V W := hmx ▸ Rw
  have kvx := kw.trans kx
  refine WP.mono (xor_ok Lx Rx (a := oDig) (b := dst + done) (n := min G.D (dstLen - done))
    (stepR_ok (by omega_using [hDF]) x (show Reg.r10 ∉ [Reg.rax, .rdx, .r8] by decide) (by decide)
      ((kx.gpr (by decide)).trans h10)) hmin (by unfold oRsa; omega_using [hDF, c3]) (by unfold oRsa; omega_using [hfit, c1, hmin]) (by omega_using [hfit, c1, c3])
    ((kvx.gpr (by decide)).trans h₁) ((kvx.gpr (by decide)).trans h₂) h8)
    fun y ⟨Ly, ky, Ry⟩ => ⟨Ly, ?_, Ry⟩
  exact (hk.trans (kvx.trans ky)).mono (by decide)

/-! ## The next counter -/

theorem nextCtr_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {c done dstLen : Nat} (hc : W 19 = BitVec.ofNat 64 c)
    (hdn : W 20 = BitVec.ofNat 64 done) (hdb : W 18 = BitVec.ofNat 64 dstLen) (hd' : done + G.D < 2 ^ 32)
    (hdb' : dstLen < 2 ^ 32) (hD : G.D < 2 ^ 31) :
    WP isa (.block (nextCtr lay G)) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      u'.cf = some (decide (done + G.D < dstLen)) ∧
      Rep u'.mem F S V (upd (upd W 19 (BitVec.ofNat 64 (c + 1))) 20 (BitVec.ofNat 64 (done + G.D))) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 19) (by decide) (BitVec.ofNat 64 (c + 1))
  have R2 := R1.wf G' (k := 20) (by decide) (BitVec.ofNat 64 (done + G.D))
  rw [show off F (8 * 19) = off F sCtr from rfl] at R1 R2
  rw [show off F (8 * 20) = off F sDone from rfl] at R2
  have h20 : (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).readW (off F sDone) 64 =
      BitVec.ofNat 64 done := by
    have := R1.fr 20 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hdn, ← this]; rfl
  have h18 : ((u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).writeW (off F sDone)
      (BitVec.ofNat 64 (done + G.D))).readW (off F sDstLen) 64 = BitVec.ofNat 64 dstLen := by
    have := R2.fr 18 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hdb, ← this]; rfl
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.cf = some (decide (done + G.D < dstLen)) ∧ u'.mem =
      (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).writeW (off F sDone) (BitVec.ofNat 64 (done + G.D)))
      ?_ rfl) fun u' ⟨⟨hcf, hm⟩, hk⟩ => ⟨?_, hk, hcf, hm ▸ R2⟩
  · xrun [nextCtr, lay, ea_sp, L.rsp, L.ld (d := sCtr) (by decide), L.ld (d := sDone) (by decide),
      L.ld (d := sDstLen) (by decide), L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      R.slot (d := sCtr) (k := 19) rfl (by decide) hc, h20, h18,
      ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat hD, BitVec.ofNat_add_ofNat]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hd']), Nat.mod_eq_of_lt (by omega_using [hdb'])]
  · refine L.congr (hk.gpr (by decide)) hk.2.2 ?_
    have h1 := R2.fr 14 (by decide)
    rw [← hm] at h1
    rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, h1, R.fr 14 (by decide)]
    simp [upd]

/-! ## One counter -/

/-- The view of memory after a call, as a function of its own. -/
theorem Rep.ex {m : Mem} {F S : Addr} {p : Nat → Prop} [DecidablePred p] {f V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep m F S (fun o => if p o then f o else V o) W) :
    ∃ V', Rep m F S V' W ∧ (∀ o, ¬ p o → V' o = V o) ∧ (∀ o, p o → V' o = f o) :=
  ⟨_, R, fun _ h => ifn h _ _, fun _ h => ifp h _ _⟩

theorem repr_congr {R : Mem → Addr → List Byte → Prop} {m : Mem} {p : Addr} {a b : List Byte} (h : a = b)
    (hr : R m p a) : R m p b := h ▸ hr

/-- The loop's invariant after `c` counters. -/
structure MgfI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (mk : List Byte)
    (dst dstLen D c : Nat) (v : State) : Prop where
  L : Lay v F S
  rd : v.rd = u₀.rd
  wr : v.wr = u₀.wr
  cs : ∀ r ∈ calleeSaved, v.gpr r = u₀.gpr r
  rep : ∃ V' W', Rep v.mem F S V' W' ∧ W' 19 = BitVec.ofNat 64 c ∧ W' 20 = BitVec.ofNat 64 (c * D) ∧
    (∀ k < nW, k ≠ 19 → k ≠ 20 → W' k = W k) ∧
    ∀ o < oRsa, mOut o → V' o = mixV V mk dst (min (c * D) dstLen) o

theorem keep_cs' {u v : State} {rs : List Reg} (k : Keep rs u v)
    (h : ∀ r ∈ calleeSaved, r ∉ rs) : ∀ r ∈ calleeSaved, v.gpr r = u.gpr r :=
  fun r hr => k.gpr (h r hr)

theorem cs_disj (rs : List Reg) (h : rs.all (fun r => !calleeSaved.contains r) = true) :
    ∀ r ∈ calleeSaved, r ∉ rs := fun r hr hr' => by
  have := List.all_eq_true.mp h r hr'
  simp only [Bool.not_eq_true'] at this
  simp_all

include hG in
theorem round_ok {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {u₀ : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {src srcLen dst dstLen c : Nat} (hf : MFit src srcLen dst dstLen) (A : MArgs W S src srcLen dst dstLen)
    {v : State} (I : MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen G.D c v)
    (hc : c * G.D < dstLen) :
    WP isa (round lay G) v fun v' => v'.cf = some (decide ((c + 1) * G.D < dstLen)) ∧
      MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen G.D (c + 1) v' := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oCtr = 3456 := rfl
  have c4 : oW = 4096 := rfl
  have c5 : oRsa = 8192 := rfl
  have hfs := hf.fs
  have hfd := hf.fd
  have hsep := hf.sep
  have hdb := hf.dstB
  have hcD : c ≤ c * G.D := Nat.le_mul_of_pos_right c hzD
  obtain ⟨V1, W1, R1, h19, h20, hW, hV⟩ := I.rep
  have A1 : MArgs W1 S src srcLen dst dstLen := A.of_eq fun k h1 h2 => hW k (by unfold nW frameBytes; omega_using [h2])
    (by omega_using [h2]) (by omega_using [h2])
  have hsrc1 : ∀ i < srcLen, V1 (src + i) = V (src + i) := fun i hi => by
    rw [hV _ (by omega_using [c1, c5, hfs, hi]) ((mOut_iff _).mpr (by omega_using [hfs, hi])), mixV, ifn (by omega_using [hsep, hi])]
  unfold round seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (WP.mono (scr_ok I.L (d := .rdi) (by decide) (o := oSt) (by decide)) fun u1 ⟨hdi1, hm1, k1⟩ => ?_)
  have L1 : Lay u1 F S := I.L.congr (k1.gpr (by decide)) k1.2.2 (by rw [hm1])
  have R1' : Rep u1.mem F S V1 W1 := hm1 ▸ R1
  refine WP.seq (WP.mono (init_ok hG L1 R1' hdi1) fun u2 ⟨L2, rd2, wr2, cs2, R2, _, hr2⟩ => ?_)
  obtain ⟨V2, R2, hV2, -⟩ := Rep.ex R2
  -- `update` with `src`.
  refine WP.seq (WP.mono (updSrc_ok L2 R2 A1) fun u3 ⟨hdi3, hsi3, hdx3, hcx3, h83, hm3, k3⟩ => ?_)
  have L3 : Lay u3 F S := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W1 := hm3 ▸ R2
  have hr3 : hG.SH.Repr u3.mem (off S oSt) [] := hm3 ▸ hr2
  refine WP.seq (WP.mono (upd_ok hG L3 R3 (a := src) (len := srcLen) (by omega_using [c1, c5, hfs])
      (by omega_using [hfs]) (by omega_using [c1, c4, hfs])
    hdi3 hdx3 hcx3 h83) fun u4 ⟨L4, rd4, wr4, cs4, R4, hr4⟩ => ?_)
  have hR4 := hr4 [] hr3 (by rw [hsi3]; rfl)
  obtain ⟨V4, R4, hV4, hV4'⟩ := Rep.ex R4
  -- The counter, and `update` with it.
  refine WP.seq (WP.mono (updCtr_ok L4 R4 A1.hsl h19 (by omega_using [hc, hdb, hcD])) fun u5 ⟨L5, hdi5, hsi5, hdx5,
      hcx5, h85, k5, R5⟩ => ?_)
  have hst5 : ∀ i < G.S, u5.mem (off S oSt + BitVec.ofNat 64 i) = u4.mem (off S oSt + BitVec.ofNat 64 i) :=
    fun i hi => by
      rw [off_plus, R5.scr _ (by omega_using [hzS, c1, c5, hi]), R4.scr _ (by omega_using [hzS, c1, c5, hi]), ctrV,
          ifn (by omega_using [hzS, c1, c3, hi])]
  have hR5 := hG.repr _ _ _ _ _ hst5 hR4
  refine WP.seq (WP.mono (upd_ok hG L5 R5 (a := oCtr) (len := 4) (by omega_using [c3, c5])
      (by omega_using [hzS, c1, c3]) (by omega_using [c3, c4])
    hdi5 hdx5 hcx5 h85) fun u6 ⟨L6, rd6, wr6, cs6, R6, hr6⟩ => ?_)
  have hR6 : hG.SH.Repr u6.mem (off S oSt) (srcB V src srcLen ++ Spec.Rsa.i2osp c 4) := repr_congr ?msg
    (hr6 _ hR5 (by rw [hsi5, List.nil_append, List.length_map, List.length_range]))
  case msg =>
    rw [List.nil_append]
    refine (congrArg (· ++ _) ?_).trans (congrArg (_ ++ ·) ?_)
    · refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      rw [hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hfs, this]), hsrc1 i this]
    · refine (List.map_congr_left fun i hi => ?_).trans ((range_map_getD (n := 4) (xs := Spec.Rsa.i2osp c 4)
        (by rw [Proof.Mgf1.i2osp_length])).trans (List.take_of_length_le (by rw [Proof.Mgf1.i2osp_length])))
      have := List.mem_range.mp hi
      rw [ctrV, ifp (by omega_using [this]), Nat.add_sub_cancel_left]
  obtain ⟨V6, R6, hV6, -⟩ := Rep.ex R6
  -- `finalize`.
  refine WP.seq (WP.mono (finA_ok L6 R6 A1.hsl) fun u7 ⟨hdi7, hsi7, hdx7, hcx7, hm7, k7⟩ => ?_)
  have L7 : Lay u7 F S := L6.congr (k7.gpr (by decide)) k7.2.2 (by rw [hm7])
  have R7 : Rep u7.mem F S V6 W1 := hm7 ▸ R6
  have hR7 : hG.SH.Repr u7.mem (off S oSt) (srcB V src srcLen ++ Spec.Rsa.i2osp c 4) := hm7 ▸ hR6
  refine WP.seq (WP.mono (fin_ok hG L7 R7 (o := oDig) (by omega_using [c1, c2, c4]) hdi7 hdx7 hcx7)
    fun u8 ⟨L8, rd8, wr8, cs8, R8, hr8⟩ => ?_)
  have hml : (srcB V src srcLen ++ Spec.Rsa.i2osp c 4).length = srcLen + 4 := by
    rw [List.length_append, srcB, List.length_map, List.length_range, Proof.Mgf1.i2osp_length]
  have hdig := hr8 _ hR7 (by rw [hml]; omega_using [c1, hfs]) (by rw [hsi7, hml])
  obtain ⟨V8, R8, hV8, hV8'⟩ := Rep.ex R8
  -- Into `dst`.
  have hlt : c * G.D < dstLen := hc
  refine WP.seq (WP.mono (xorOut_ok L8 R8 (dst := dst) (dstLen := dstLen) (done := c * G.D) hfd hzD (by omega_using [hzF, hzDF])
    A1.hdst A1.hdl h20 hlt) fun u9 ⟨L9, k9, R9⟩ => ?_)
  -- The next counter.
  refine WP.mono (nextCtr_ok L9 R9 h19 h20 A1.hdl (by omega_using [hzF, hzDF, hdb, hlt]) (by omega_using [hdb])
      (by omega_using [hzF, hzDF])) fun u10 ⟨L10, k10, cf10, R10⟩ => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  refine ⟨by rw [cf10, hs1], L10, ?_, ?_, ?_, _, _, R10, by simp [upd], by simp [upd, hs1], ?_, ?_⟩
  · rw [k10.2.1, k9.2.1, rd8, k7.2.1, rd6, k5.2.1, rd4, k3.2.1, rd2, k1.2.1, I.rd]
  · rw [k10.2.2, k9.2.2, wr8, k7.2.2, wr6, k5.2.2, wr4, k3.2.2, wr2, k1.2.2, I.wr]
  · intro r hr
    rw [keep_cs' k10 (cs_disj _ (by decide)) r hr, keep_cs' k9 (cs_disj _ (by decide)) r hr, cs8 r hr,
      keep_cs' k7 (cs_disj _ (by decide)) r hr, cs6 r hr, keep_cs' k5 (cs_disj _ (by decide)) r hr, cs4 r hr,
      keep_cs' k3 (cs_disj _ (by decide)) r hr, cs2 r hr, keep_cs' k1 (cs_disj _ (by decide)) r hr, I.cs r hr]
  · intro k hk h1 h2
    simp only [upd, ifn h2, ifn h1]
    exact hW k hk h1 h2
  · intro o ho hmo
    have hold : ∀ x, mOut x → V8 x = V1 x := by
      intro x hx
      have := (mOut_iff x).mp hx
      rw [hV8 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzF, hzW, c1, c2, c3, c4, this]),
        hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzW, c1, c2, c3, c4, this]), ctrV,
            ifn (by omega_using [c1, c3, c4, this]),
        hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzW, c1, c2, c3, c4, this]),
        hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, c1, c2, c3, c4, this])]
    have hdg : ∀ j < G.D, V8 (oDig + j) = (Gs.hash (srcB V src srcLen ++ Spec.Rsa.i2osp c 4)).getD j 0 :=
      fun j hj => by
        rw [hV8' _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzDF, hj]), hdig j hj, hGh]
    simp only [xorV]
    by_cases hx : dst + c * G.D ≤ o ∧ o < dst + c * G.D + min G.D (dstLen - c * G.D)
    · have hq : (o - dst) / G.D = c :=
        Nat.div_eq_of_lt_le (by omega_using [hx]) (by omega_using [hs1, hx])
      have hr : (o - dst) % G.D = o - (dst + c * G.D) := by
        rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]; omega_using []
      rw [ifp hx, hold o hmo, hV o ho hmo, mixV, mixV,
        ifn (show ¬ (dst ≤ o ∧ o < dst + min (c * G.D) dstLen) by omega_using [hx]),
        ifp (show dst ≤ o ∧ o < dst + min ((c + 1) * G.D) dstLen by omega_using [hs1, hx]), hdg _ (by omega_using [hx]),
        Proof.Mgf1.mgf1_getD hGv _ (show o - dst < dstLen by omega_using [hx]), hGl, hq, hr]
    · rw [ifn hx, hold o hmo, hV o ho hmo, mixV, mixV]
      by_cases hy : dst ≤ o ∧ o < dst + min (c * G.D) dstLen
      · rw [ifp hy, ifp (by omega_using [hs1, hy])]
      · rw [ifn hy, ifn (by omega_using [hs1, hx, hy])]

/-! ## MGF1 -/

/-- The counter and `done` set to 0: the loop's invariant for counter 0. -/
theorem mgfHead_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (mk : List Byte) (dst dstLen : Nat) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (sp lay.sCtr) .rax, .store (sp lay.sDone) .rax]) u
      (MgfI u F S V W mk dst dstLen G.D 0) := by
  have G' := L.geo
  have R2 := (R.wf G' (k := 19) (by decide) 0#64).wf G' (k := 20) (by decide) 0#64
  rw [show off F (8 * 19) = off F sCtr from rfl, show off F (8 * 20) = off F sDone from rfl] at R2
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem =
      (u.mem.writeW (off F sCtr) 0#64).writeW (off F sDone) 0#64) ?_ rfl) fun v ⟨hm, hk⟩ => ?_
  · xrun [lay, ea_sp, L.rsp, L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl]
  have R2' : Rep v.mem F S V (upd (upd W 19 0#64) 20 0#64) := hm ▸ R2
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by
    rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, R2'.fr 14 (by decide), R.fr 14 (by decide)]; simp [upd])
  exact ⟨Lv, hk.2.1, hk.2.2, keep_cs' hk (cs_disj _ (by decide)), _, _, R2', by simp [upd], by simp [upd],
    fun k _ h1 h2 => by simp only [upd, ifn h2, ifn h1],
    fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega_using [])]⟩

include hG in
/-- `dst ⊕= MGF1(src, dstLen)`. -/
theorem mgfXor_ok {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen)
    (A : MArgs W S src srcLen dst dstLen) :
    WP isa (mgfXor lay G) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧ (∀ k < nW, k ≠ 19 → k ≠ 20 → W' k = W k) ∧
        ∀ o < oRsa, mOut o → V' o = mixV V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen o := by
  have hpos := hf.pos
  refine WP.seq (WP.mono (mgfHead_ok (G := G) L R (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen)
    fun v I0 => ?_)
  refine WP.loop (M := isa) (fun n w => ∃ c, n = dstLen - c * G.D ∧ c * G.D < dstLen ∧
      MgfI u F S V W (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen G.D c w)
    ?_ (dstLen - 0 * G.D) v ⟨0, rfl, by omega_using [hpos], I0⟩
  rintro n w ⟨c, rfl, hc, I⟩
  refine WP.mono (round_ok hG hGh hGl hGv hf A I hc) fun w' ⟨hcf, I'⟩ => ?_
  have hD := (sizes hG).2.2.2.2
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  by_cases h : (c + 1) * G.D < dstLen
  · refine .inr ⟨by simp only [eval, hcf, h, decide_true], _, ?_, c + 1, rfl, h, I'⟩
    omega_using [hD, hs1, h]
  · refine .inl ⟨by simp only [eval, hcf, h, decide_false], I'.L, I'.rd, I'.wr, I'.cs, ?_⟩
    obtain ⟨V', W', R', _, _, hW', hV'⟩ := I'.rep
    exact ⟨V', W', R', hW', fun o ho hco => by rw [hV' o ho hco, Nat.min_eq_right (by omega_using [h])]⟩

end VG.Proof.RsaOaep.X86_64
