import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSAES-OAEP on AArch64: MGF1

As on x86-64 (`Proof/RsaOaep/X86_64/Mgf.lean`): `mgfXor lay G` XORs
`MGF1(src, dstLen)` into `dst` (`mgfXor_ok`), where `src` (`srcLen` bytes)
and `dst` (`dstLen` bytes) are ranges of our working space below the hash
function's, given by MGF1's slots: for each counter `c`, the state is set
by `init`, `update` absorbs `src` and then `I2OSP(c, 4)` (written to
`scratch + oCtr`, `updCtr_ok`), `finalize` writes the digest to
`scratch + oDig`, and the first `min(hLen, dstLen - c hLen)` bytes of the
digest are XORed into `dst + c hLen` (`xorOut_ok`).
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs round xorOut xorHead xorBody nextCtr initArgs updSrcArgs updCtrArgs
  finArgs mgfXor)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Stream Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK VecKept)

/-! ## Blocks -/

/-- A slot, read through `Rep`. -/
theorem Rep.rd8 {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W) {d k : Nat}
    (hd : d = 8 * k) (hk : k < nW) {v : BitVec 64} (hv : W k = v) : m.read (F + BitVec.ofNat 64 d) 8 = v := by
  rw [← hv, ← R.fr k hk, hd]; rfl

/-- `scratch` in its slot. -/
theorem Lay.rd8 {t : State} {F S : Addr} (L : Lay t F S) : t.mem.read (F + BitVec.ofNat 64 sScr) 8 = S :=
  L.slot

/-- What MGF1's slots hold. -/
structure MArgs (W : Nat → BitVec 64) (S : Addr) (src srcLen dst dstLen : Nat) : Prop where
  hsrc : W 13 = off S src
  hsl : W 14 = BitVec.ofNat 64 srcLen
  hdst : W 15 = off S dst
  hdl : W 16 = BitVec.ofNat 64 dstLen

theorem MArgs.of_eq {W W' : Nat → BitVec 64} {S : Addr} {src srcLen dst dstLen : Nat}
    (h : MArgs W S src srcLen dst dstLen) (hW : ∀ k, 13 ≤ k → k ≤ 16 → W' k = W k) :
    MArgs W' S src srcLen dst dstLen :=
  ⟨(hW 13 (by omega) (by omega)).trans h.hsrc, (hW 14 (by omega) (by omega)).trans h.hsl,
    (hW 15 (by omega) (by omega)).trans h.hdst, (hW 16 (by omega) (by omega)).trans h.hdl⟩

theorem initArgs_ok {u : State} {F S : Addr} (L : Lay u F S) (ws : List Region) :
    WP isa (.block (initArgs lay)) u fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = off S oSt := by
  have h₁ : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  oaep_run [initArgs, Mgf1.scr, lay, sScr, oSt, h₁, L.sp, hs]
  exact ⟨blk_step, trivial⟩

theorem updSrc_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {src srcLen dst dstLen : Nat} (A : MArgs W S src srcLen dst dstLen) (ws : List Region) :
    WP isa (.block (updSrcArgs lay)) u fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = off S oSt ∧
      u'.gpr .x1 = BitVec.ofNat 64 0 ∧ u'.gpr .x2 = off S src ∧ u'.gpr .x3 = BitVec.ofNat 64 srcLen ∧
      u'.gpr .x4 = off S oW := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h104 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 104) 8 := L.ld (d := 104) (by decide)
  have h112 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 112) 8 := L.ld (d := 112) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have hsrc := R.rd8 (d := 104) (k := 13) rfl (by decide) A.hsrc
  have hsl := R.rd8 (d := 112) (k := 14) rfl (by decide) A.hsl
  oaep_run [updSrcArgs, Mgf1.scr, lay, sScr, sSrc, sSrcLen, oSt, oW, h96, h104, h112, L.sp, hs, hsrc, hsl]
  exact ⟨blk_step, trivial, trivial, by decide, trivial⟩

theorem finA_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen : Nat} (hl : W 14 = BitVec.ofNat 64 srcLen) (ws : List Region) :
    WP isa (.block (finArgs lay)) u fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = off S oSt ∧
      u'.gpr .x1 = BitVec.ofNat 64 (srcLen + 4) ∧ u'.gpr .x2 = off S oDig ∧ u'.gpr .x3 = off S oW := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h112 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 112) 8 := L.ld (d := 112) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have hsl := R.rd8 (d := 112) (k := 14) rfl (by decide) hl
  oaep_run [finArgs, Mgf1.scr, lay, sScr, sSrcLen, oSt, oW, oDig, h96, h112, L.sp, hs, hsl]
  exact ⟨blk_step, trivial, trivial, by rw [BitVec.ofNat_add], trivial⟩

/-! ## The counter -/

/-- `I2OSP(c, 4)` at `scratch + oCtr`. -/
def ctrV (V : Nat → Byte) (c : Nat) (x : Nat) : Byte :=
  if oCtr ≤ x ∧ x < oCtr + 4 then (Spec.Rsa.i2osp c 4).getD (x - oCtr) 0 else V x

theorem trunc8 (x : Nat) : BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)]

theorem shr8 {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 8 = BitVec.ofNat 64 (x / 2 ^ 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem updCtr_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen c : Nat} (hl : W 14 = BitVec.ofNat 64 srcLen) (hc : W 17 = BitVec.ofNat 64 c)
    (hc32 : c < 2 ^ 32) (ws : List Region) :
    WP isa (.block (updCtrArgs lay)) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧ Rep u'.mem F S (ctrV V c) W ∧
      u'.gpr .x0 = off S oSt ∧ u'.gpr .x1 = BitVec.ofNat 64 srcLen ∧ u'.gpr .x2 = off S oCtr ∧
      u'.gpr .x3 = BitVec.ofNat 64 4 ∧ u'.gpr .x4 = off S oW := by
  have G' := L.geo
  have w12 : W 12 = S := (R.fr 12 (by decide)).symm.trans L.slot
  have R1 := (((R.wb G' (o := 3459) (by decide) (BitVec.ofNat 8 c)).wb G'
    (o := 3458) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8))).wb G'
    (o := 3457) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).wb G'
    (o := 3456) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h112 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 112) 8 := L.ld (d := 112) (by decide)
  have h136 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 136) 8 := L.ld (d := 136) (by decide)
  have s0 : InRegions u.wr (S + BitVec.ofNat 64 3456) 1 := L.sst (o := 3456) (by decide)
  have s1 : InRegions u.wr (S + BitVec.ofNat 64 3457) 1 := L.sst (o := 3457) (by decide)
  have s2 : InRegions u.wr (S + BitVec.ofNat 64 3458) 1 := L.sst (o := 3458) (by decide)
  have s3 : InRegions u.wr (S + BitVec.ofNat 64 3459) 1 := L.sst (o := 3459) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have hcr := R.rd8 (d := 136) (k := 17) rfl (by decide) hc
  have hs4 := R1.rd8 (d := 96) (k := 12) rfl (by decide) w12
  have hl4 := R1.rd8 (d := 112) (k := 14) rfl (by decide) hl
  refine WP.mono (Q := fun (u' : State) => u'.mem = (((u.mem.write (off S 3459) 1 (BitVec.ofNat 8 c)).write (off S 3458) 1
      (BitVec.ofNat 8 (c / 2 ^ 8))).write (off S 3457) 1 (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).write (off S 3456) 1
      (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x0 = off S oSt ∧
      u'.gpr .x1 = BitVec.ofNat 64 srcLen ∧ u'.gpr .x2 = off S oCtr ∧ u'.gpr .x3 = BitVec.ofNat 64 4 ∧
      u'.gpr .x4 = off S oW) ?_ fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x0, x1, x2, x3, x4⟩ => ?_
  · oaep_run [updCtrArgs, Mgf1.scr, lay, sScr, sSrcLen, sCtr, oSt, oW, oCtr, h96, h112, h136, L.sp, hs, hcr,
      BitVec.add_assoc, BitVec.reduceAdd, s0, s1, s2, s3, trunc8, shr8 (show c < 2 ^ 64 by omega),
      shr8 (show c / 2 ^ 8 < 2 ^ 64 by omega), shr8 (show c / 2 ^ 8 / 2 ^ 8 < 2 ^ 64 by omega), hs4, hl4]
    exact ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, trivial, trivial, trivial, by decide, trivial⟩
  have R' : Rep u'.mem F S (ctrV V c) W := by
    rw [hm]
    refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R1
    have e1 : c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 3 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    have e2 : c / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 2 := by rw [Nat.div_div_eq_div_mul]
    have e3 : c / 2 ^ 8 = c / 256 ^ 1 := rfl
    simp only [upd, ctrV, oCtr, Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases (show x = 3456 ∨ x = 3457 ∨ x = 3458 ∨ x = 3459 ∨ ¬(3456 ≤ x ∧ x < 3456 + 4) by omega) with
      h | h | h | h | h
    · subst h; simp [e1]
    · subst h; simp [e2]
    · subst h; simp [e3]
    · subst h; simp
    · rw [ifn h, ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R', x0, x1, x2, x3, x4⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  · rw [hm]
    exact frame_wb (frame_wb (frame_wb (frame_wb (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _

/-! ## The digest into `dst` -/

theorem imm16 {n : Nat} (hn : n < 65536) : BitVec.setWidth 64 (BitVec.ofNat 16 n) <<< 0 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem xorHead_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {G : Hash} {dst dstLen done : Nat} (hD : G.D < 65536) (hdl : dstLen < 2 ^ 64)
    (he : W 15 = off S dst) (hdb : W 16 = BitVec.ofNat 64 dstLen) (hdn : W 18 = BitVec.ofNat 64 done)
    (hlt : done < dstLen) (ws : List Region) :
    WP isa (.block (xorHead lay G)) u fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x11 = off S oDig ∧
      u'.gpr .x12 = off S (dst + done) ∧ u'.gpr .x14 = BitVec.ofNat 64 (min G.D (dstLen - done)) := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h120 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 120) 8 := L.ld (d := 120) (by decide)
  have h128 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 128) 8 := L.ld (d := 128) (by decide)
  have h144 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 144) 8 := L.ld (d := 144) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have r15 := R.rd8 (d := 120) (k := 15) rfl (by decide) he
  have r16 := R.rd8 (d := 128) (k := 16) rfl (by decide) hdb
  have r18 := R.rd8 (d := 144) (k := 18) rfl (by decide) hdn
  have hD' : G.D < 2 ^ 64 := by omega
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S oDig ∧
      u'.gpr .x12 = off S dst + BitVec.ofNat 64 done ∧
      u'.gpr .x14 = if (BitVec.ofNat 64 G.D).toNat ≤ (BitVec.ofNat 64 (dstLen - done)).toNat then
        BitVec.ofNat 64 G.D else BitVec.ofNat 64 (dstLen - done)) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x14⟩ => ⟨Step.blk ws hrd hwr hsp hv hcs hm, hm, x11,
      x12.trans (off_off S dst done), by
        rw [x14, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD',
          Nat.mod_eq_of_lt (show dstLen - done < 2 ^ 64 by omega)]
        split <;> (congr 1; omega)⟩
  oaep_run [xorHead, Mgf1.scr, lay, sScr, sDst, sDstLen, sDone, oDig, h96, h120, h128, h144, L.sp, hs, r15, r16,
    r18, imm16 hD, Offset.ofNat_sub_ofNat (show done ≤ dstLen by omega), carry_sub, decide_eq_true_eq]
  oaep_fin

theorem xorOut_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {G : Hash} {dst dstLen done : Nat} (hfit : dst + dstLen ≤ oSt) (hD : 0 < G.D)
    (hDF : G.D ≤ 64) (he : W 15 = off S dst) (hdb : W 16 = BitVec.ofNat 64 dstLen)
    (hdn : W 18 = BitVec.ofNat 64 done) (hlt : done < dstLen) (ws : List Region) :
    WP isa (xorOut lay G) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S (xorV V oDig (dst + done) (min G.D (dstLen - done))) W := by
  have c1 : oSt = 3072 := rfl
  have c3 : oDig = 3328 := rfl
  have c5 : oRsa = 8192 := rfl
  refine WP.seq (WP.mono (xorHead_ok L R (G := G) (by omega) (by omega) he hdb hdn hlt ws)
    fun v ⟨Sv, hm, x11, x12, x14⟩ => ?_)
  have Lv : Lay v F S := L.congr Sv.sp Sv.wr (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.mono (xorLoop_ok Lv Rv (a := oDig) (b := dst + done) (n := min G.D (dstLen - done)) (by omega)
    (by omega) (by omega) (by omega) x11 x12 x14 ws) fun w ⟨Lw, Sw, Rw⟩ => ⟨Lw, Sv.trans Sw, Rw⟩

/-! ## The next counter -/

theorem nextCtr_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {G : Hash} {c done dstLen : Nat} (hc : W 17 = BitVec.ofNat 64 c)
    (hdn : W 18 = BitVec.ofNat 64 done) (hdb : W 16 = BitVec.ofNat 64 dstLen) (hd' : done + G.D < 2 ^ 32)
    (hdb' : dstLen < 2 ^ 32) (hD : G.D < 4096) (ws : List Region) :
    WP isa (.block (nextCtr lay G)) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      (u'.gpr .x12 != 0) = decide (done + G.D < dstLen) ∧
      Rep u'.mem F S V (upd (upd W 17 (BitVec.ofNat 64 (c + 1))) 18 (BitVec.ofNat 64 (done + G.D))) := by
  have G' := L.geo
  have R1 : Rep (u.mem.write (off F 136) 8 (BitVec.ofNat 64 (c + 1))) F S V (upd W 17 (BitVec.ofNat 64 (c + 1))) :=
    R.wq G' (k := 17) (by decide) _
  have R2 : Rep ((u.mem.write (off F 136) 8 (BitVec.ofNat 64 (c + 1))).write (off F 144) 8
      (BitVec.ofNat 64 (done + G.D))) F S V
      (upd (upd W 17 (BitVec.ofNat 64 (c + 1))) 18 (BitVec.ofNat 64 (done + G.D))) :=
    R1.wq G' (k := 18) (by decide) _
  have h136 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 136) 8 := L.ld (d := 136) (by decide)
  have h144 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 144) 8 := L.ld (d := 144) (by decide)
  have h128 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 128) 8 := L.ld (d := 128) (by decide)
  have w136 : InRegions u.wr (F + BitVec.ofNat 64 136) 8 := L.st (d := 136) (by decide)
  have w144 : InRegions u.wr (F + BitVec.ofNat 64 144) 8 := L.st (d := 144) (by decide)
  have rc := R.rd8 (d := 136) (k := 17) rfl (by decide) hc
  have rd1 := R1.rd8 (d := 144) (k := 18) rfl (by decide) (show upd W 17 _ 18 = _ by simp only [upd]; exact hdn)
  have rl2 := R2.rd8 (d := 128) (k := 16) rfl (by decide) (show upd (upd W 17 _) 18 _ 16 = _ by simp only [upd]; exact hdb)
  refine WP.mono (Q := fun (u' : State) => u'.mem = (u.mem.write (off F 136) 8 (BitVec.ofNat 64 (c + 1))).write
      (off F 144) 8 (BitVec.ofNat 64 (done + G.D)) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x12 = if (BitVec.ofNat 64 dstLen).toNat ≤ (BitVec.ofNat 64 (done + G.D)).toNat then 0
        else BitVec.allOnes 64) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x12⟩ => ?_
  · oaep_run [nextCtr, lay, sCtr, sDone, sDstLen, h136, h144, h128, w136, w144, L.sp, BitVec.add_zero, rc, rd1, rl2,
      BitVec.ofNat_add_ofNat, sbc_self, hD]
    oaep_fin
  have R' : Rep u'.mem F S V (upd (upd W 17 (BitVec.ofNat 64 (c + 1))) 18 (BitVec.ofNat 64 (done + G.D))) := by
    rw [hm]; exact R2
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, ?_, R'⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]; rfl
  · rw [hm]
    exact (Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide)))
      (List.mem_cons_self ..) _ (cF F (by decide)))
  · rw [x12, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    by_cases h : dstLen ≤ done + G.D
    · rw [ifp h]; simp only [bne_self_eq_false]; exact (decide_eq_false (by omega)).symm
    · rw [ifn h]; exact (decide_eq_true (by omega)).symm

end VG.Proof.RsaOaep.AArch64
