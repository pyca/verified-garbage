module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkFrame
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyB1
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyB2
import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyLogic
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-! ### `RsaPss.AArch64.FixedSaltSelect`, which only this module used -/

section

/-! ### `RsaPss.AArch64.FixedSaltHash`, which only this module used -/

section

/-! Hashing the fixed-length salt after all encoding checks. -/

@[expose] public section
namespace VG.Proof.RsaPss.AArch64.FixedSalt
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

theorem fixed_msg_y {H : Hash} (hH : HashOK H) {u : State} {S : Addr}
    {W : Nat → Byte} {mH : List Byte} {e db pos i : Nat}
    (hm : mH.length = H.D) (hpos : pos < db) (hdb : db < 1024)
    (he : oEm ≤ e) (hfit : e + db + H.D ≤ oY)
    (hEm : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = W o) (hi : i < 2048) :
    updL (updL (clr (fun o => u.mem (off S o)) oY 2048) (oY + 8) mH)
      (oY + 8 + H.D)
      ((List.range (db - pos - 1)).map fun j =>
        updL (clr (fun o => u.mem (off S o)) oY 2048) (oY + 8) mH (e + db - (db - pos - 1) + j))
      (oY + i) = (msgV mH (fun j => W (e + j)) db pos).getD i 0 := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hD := hH.sizes.D0
  unfold msgV
  rw [getD_app, getD_app]
  simp only [List.length_append, RsaPss.zeros_length, hm]
  by_cases h1 : i < 8
  · simp (disch := omega) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right]
    exact (RsaPss.zeros_getD _ _).symm
  by_cases h2 : i < 8 + H.D
  · simp (disch := omega) only [updL, ↓ite_eq_left, ↓ite_eq_right]
    rw [show oY + i - (oY + 8) = i - 8 by omega]
  by_cases h3 : i - (8 + H.D) < db - pos - 1
  · simp (disch := omega) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right, hm, List.length_map, List.length_range]
    rw [show oY + i - (oY + 8 + H.D) = i - (8 + H.D) by omega]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h3, Option.map_some, Option.getD_some]
    simp (disch := omega) only [↓ite_eq_right]
    rw [hEm _ (by omega) (by omega)]
    congr 1
    omega
  · simp (disch := omega) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right, hm, List.length_map, List.length_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by rw [List.length_range]; omega)]
    rfl

variable {H : Hash} (hH : HashOK H)
include hH in
theorem finish_ok {u : State} {F S : Addr} (L : Lay u F S) {W : Nat → Byte} {e db pos : Nat} {acc : BitVec 64}
    {dig : Addr} (hEm : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = W o) (he : oEm ≤ e)
    (hfit : e + db + H.D ≤ oY) (hpos : pos < db) (hdb : db < 1024)
    (h19 : u.gpr .x19 = off S oSt) (h21 : u.gpr .x21 = off S oDig) (h24 : u.gpr .x24 = off S e)
    (h25 : u.gpr .x25 = BitVec.ofNat 64 db) (h26 : u.gpr .x26 = acc)
    (hS : u.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 (db - pos - 1)) (hdg : u.mem.readW (off F sDig) 64 = dig)
    (hr : ∀ j < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨dig, H.D⟩ ⟨S, oRsa⟩) {f : MdFns} {dn : String} (hT : HT H dn f F u.mem u.syms)
    (hdo : DigOK H.P) :
    WP isa (Impl.RsaPss.AArch64.FixedSalt.finish f H) u
      fun u' => u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
        (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u'.gpr r = u.gpr r) ∧
        (∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) ∧
        Frame (mgfWr F S) u.mem u'.mem ∧
        u'.gpr .x0 = resV acc (hH.SH.H.hash (msgV (Spec.Rsa.bytesAt u.mem dig H.D) (fun i => W (e + i)) db pos))
          W e db H.D := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold Impl.RsaPss.AArch64.FixedSalt.finish seqs seqs seqs seqs seqs
  -- `Y` cleared.
  refine WP.seq (WP.mono_syms (clearY_ok L (V := fun o => u.mem (off S o)) (fun _ _ => rfl)) fun u1 ⟨k1, f1, R1⟩ sy1 => ?_)
  obtain L1 := L.congr k1.sp k1.wr (k1.get .x20)
  obtain hm1 : Spec.Rsa.bytesAt u1.mem dig H.D = Spec.Rsa.bytesAt u.mem dig H.D :=
    bytes_apartL f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by omega_using [hDN, hN])
  -- `mHash`.
  refine WP.seq (WP.mono_syms (copyDigest_ok hH L1 R1 (dig := dig) (by rw [slot_keep f1 (L.slotSd (by decide)), hdg])
    (by rw [k1.rd, k1.wr]; exact hr) hd) fun u2 ⟨k2, f2, R2⟩ sy2 => ?_)
  rw [hm1] at R2
  generalize hmH : Spec.Rsa.bytesAt u.mem dig H.D = mH at R2
  obtain hml : mH.length = H.D := by rw [← hmH, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  obtain L2 := L1.congr k2.sp k2.wr (k2.get .x20)
  obtain F3 : Frame [⟨S, oRsa⟩] u.mem u2.mem := f1.trans f2
  refine WP.seq (WP.mono_syms (copySalt_ok hH L2 R2 (e := e) (db := db) (sl := db - pos - 1)
    he (by omega_using [hfit]) (by omega_using []) hdb
    (by rw [k2.get .x24, k1.get .x24, h24])
    (by rw [k2.get .x25, k1.get .x25, h25])
    (by rw [slot_keep F3 (L.slotSd (by decide)), hS])) fun u4 ⟨k4, f4, R4⟩ sy4 => ?_)
  obtain L4 := L2.congr k4.sp k4.wr (k4.get .x20)
  -- `nbm`.
  refine WP.seq (WP.mono_syms (signLen_ok hH L4 (sl := db - pos - 1)
    (by rw [slot_keep (F3.trans f4) (L.slotSd (by decide)), hS]) (by omega_using [hdb]))
    fun u5 ⟨k5, x22₅, m5⟩ sy5 => ?_)
  obtain L5 := L4.congr k5.sp k5.wr (k5.get .x20)
  obtain R5 := R4.frame (m' := u5.mem) (rs := [slotR F sNb]) (by rw [m5]; exact frame_slot _ F sNb _)
    (L.slotS (by decide))
  -- `Hash(M')`.
  generalize hmsg : msgV mH (fun i => W (e + i)) db pos = msg
  obtain hmsgl : msg.length = 8 + H.D + (db - pos - 1) := by rw [← hmsg, msgV_length, hml]
  obtain hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + (db - pos - 1) + H.P.L) (b := H.P.B) hB0
  obtain hnb2 := Nat.div_mul_le_self (8 + H.D + (db - pos - 1) + H.P.L) H.P.B
  obtain hnbB : ((8 + H.D + (db - pos - 1) + H.P.L) / H.P.B + 1) * H.P.B =
      (8 + H.D + (db - pos - 1) + H.P.L) / H.P.B * H.P.B + H.P.B := Nat.succ_mul _ _
  obtain g5 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u5.gpr r = u.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k5.get _ (by decide), k4.get _ (by decide), k2.get _ (by decide),
        k1.get _ (by decide)]
  obtain F5 : Frame (mgfWr F S) u.mem u5.mem :=
    (F3.trans f4).mono (by simp) |>.trans (by rw [m5]; exact (frame_slot _ F sNb _).mono (by simp))
  obtain hT5 : HT H dn f F u5.mem u5.syms := by rw [sy5, sy4, sy2, sy1]; exact hT.stepW L F5
  refine WP.seq (WP.mono (ctHash_ok hH L5 R5 (msg := msg) (nbm := (8 + H.D + (db - pos - 1) + H.P.L) / H.P.B + 1)
    (by rw [g5 .x19 (by decide), h19]) (by rw [g5 .x21 (by decide), h21])
    (by rw [x22₅, hmsgl]) (by rw [m5, Mem.readW_writeW_self64]) (by rw [hmsgl, hnbB]; omega_using [hnb1])
    (by rw [hnbB]; omega_using [he, hfit, hpos, hdb, hD, hDN, hN, hL, hB0, hBl, c2, hnb1, hnb2, hnbB]) (fun i hi => ?_) hT5 hdo) fun u6 ⟨O6, d6⟩ => ?_)
  · rw [← hmsg]
    exact fixed_msg_y hH hml hpos hdb he hfit hEm (by rw [hnbB] at hi; omega_using [he, hfit, hpos, hdb, hD, hDN, hN, hL, hB0, hBl, c1, c2, hnb1, hnb2, hnbB, hi])
  obtain L6 := L5.congr O6.sp O6.wr (O6.cs .x20 (by decide))
  -- The comparison.
  refine WP.mono (cmpH_ok hH L6 (V := fun o => u6.mem (off S o)) (fun _ _ => rfl) (e := e) (db := db) (acc := acc)
    hfit (by rw [O6.cs .x21 (by decide), g5 .x21 (by decide), h21])
    (by rw [O6.cs .x24 (by decide), g5 .x24 (by decide), h24])
    (by rw [O6.cs .x25 (by decide), g5 .x25 (by decide), h25])
    (by rw [O6.cs .x26 (by decide), g5 .x26 (by decide), h26])) fun u7 ⟨O7, x0₇⟩ => ?_
  refine ⟨by rw [O7.sp, O6.sp, k5.sp, k4.sp, k2.sp, k1.sp], by rw [O7.rd, O6.rd, k5.rd, k4.rd, k2.rd, k1.rd],
    by rw [O7.wr, O6.wr, k5.wr, k4.wr, k2.wr, k1.wr], fun r hr => ?_,
    fun r hr => by rw [O7.vcs r hr, O6.vec r hr, k5.vcs r hr, k4.vcs r hr, k2.vcs r hr, k1.vcs r hr],
    by rw [O7.mem]; exact F5.trans (O6.fr.mono (by simp)), ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [O7.get r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      O6.cs r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      g5 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  · rw [x0₇, resV]
    congr 2
    refine congrArg (acc ||| ·) (orF_congr fun i hi => ?_)
    rw [← off_add, byte_of_bytesAt d6 hi, O6.em _ (by omega_using [he]) (by omega_using [hfit, hi])]
    simp (disch := omega_using [hfit, hi]) only [updL, clr, ↓ite_eq_right]
    rw [hEm _ (by omega_using [he]) (by omega_using [hfit, hi])]


end VG.Proof.RsaPss.AArch64.FixedSalt

end

end


/-! A known salt length changes only the hash of already rejected encodings. -/

@[expose] public section
namespace VG.Proof.RsaPss.AArch64.FixedSalt
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (Only wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp)

theorem resV_nonzero {acc : BitVec 64} (ha : acc.toNat < 2^63) (hn : acc ≠ 0)
    (h : List Byte) (W : Nat → Byte) (e db D : Nat) : resV acc h W e db D = 0 := by
  unfold resV
  rw [top_sub _ (lt_or ha (orF_lt _ (fun i => lt_xor (lt_byte _ (by decide)) (lt_byte _ (by decide))) D))]
  rw [ite_eq_right (fun he => hn (or_eq_zero64 _ _ |>.mp he).1)]
  rfl

variable {H : Hash} (hH : HashOK H)
include hH in
theorem select_ok {u : State} {F S : Addr} (L : Lay u F S) {W : Nat → Byte} {e db pos : Nat} {acc : BitVec 64}
    {dig : Addr} (hEm : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = W o) (he : oEm ≤ e)
    (hfit : e + db + H.D ≤ oY) (hpos : pos < db) (hdb : db < 1024)
    (h19 : u.gpr .x19 = off S oSt) (h21 : u.gpr .x21 = off S oDig) (h24 : u.gpr .x24 = off S e)
    (h25 : u.gpr .x25 = BitVec.ofNat 64 db) (h26 : u.gpr .x26 = acc)
    (hP : u.mem.readW (off F sPos) 64 = BitVec.ofNat 64 pos) (hdg : u.mem.readW (off F sDig) 64 = dig)
    (hr : ∀ j < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨dig, H.D⟩ ⟨S, oRsa⟩)
    {any : BitVec 64} {sl : Nat}
    (hAny : u.mem.readW (off F sAny) 64 = any)
    (hSl : u.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 sl)
    (hFits : any = 0 → sl < db)
    (hMatch : any = 0 → acc = 0 → sl = db - pos - 1)
    (hAcc : acc.toNat < 2^63) {f : MdFns} {dn : String} (hT : HT H dn f F u.mem u.syms) (hdo : DigOK H.P) :
    WP isa (Impl.RsaPss.AArch64.FixedSalt.select f H) u
      fun u' => u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
        (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u'.gpr r = u.gpr r) ∧
        (∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) ∧
        Frame (mgfWr F S) u.mem u'.mem ∧
        u'.gpr .x0 = resV acc (hH.SH.H.hash (msgV (Spec.Rsa.bytesAt u.mem dig H.D) (fun i => W (e + i)) db pos))
          W e db H.D := by
  unfold Impl.RsaPss.AArch64.FixedSalt.select
  refine WP.seq (WP.of_syms (wp_ldrSp (by decide) (ld_slot L (by decide)) fun v O e9 => wp_nil fun sy => ?_))
  obtain hTv : HT H dn f F v.mem v.syms := by rw [sy, O.mem]; exact hT
  obtain Lv := L.congr O.sp O.wr (O.get .x20)
  obtain h9 : v.gpr .x9 = any := by rw [e9, L.sp, hAny]
  obtain hEmv : ∀ o, oEm ≤ o → o < oY → v.mem (off S o) = W o := by rw [O.mem]; exact hEm
  obtain h19v : v.gpr .x19 = off S oSt := by rw [O.get .x19, h19]
  obtain h21v : v.gpr .x21 = off S oDig := by rw [O.get .x21, h21]
  obtain h24v : v.gpr .x24 = off S e := by rw [O.get .x24, h24]
  obtain h25v : v.gpr .x25 = BitVec.ofNat 64 db := by rw [O.get .x25, h25]
  obtain h26v : v.gpr .x26 = acc := by rw [O.get .x26, h26]
  obtain hdgv : v.mem.readW (off F sDig) 64 = dig := by rw [O.mem, hdg]
  obtain hrv : ∀ j < H.D, InRegions (v.rd ++ v.wr) (dig + BitVec.ofNat 64 j) 1 := by
    rw [O.rd, O.wr]; exact hr
  refine WP.ite _ (eval_zero _ _) (fun ht => ?_) (fun hf => ?_)
  · have ha : any = 0 := by rw [h9] at ht; exact beq_iff_eq.mp ht
    obtain hslt := hFits ha
    obtain hp' : db - sl - 1 < db := by omega_using [hpos]
    obtain hrev : db - (db - sl - 1) - 1 = sl := by omega_using [hslt]
    refine WP.mono (finish_ok hH Lv hEmv he hfit hp' hdb h19v h21v h24v h25v h26v
      (by rw [O.mem, hrev, hSl]) hdgv hrv hd hTv hdo) fun t ⟨sp, rd, wr, cs, vs, fr, result⟩ => ?_
    refine ⟨sp.trans O.sp, rd.trans O.rd, wr.trans O.wr, ?_, ?_, O.mem ▸ fr, ?_⟩
    · intro r hr
      rw [cs r hr, O.get r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · intro r hr; rw [vs r hr, O.vcs r hr]
    · rw [result, O.mem]
      by_cases hz : acc = 0
      · have heq : db - sl - 1 = pos := by have := hMatch ha hz; omega_using [hpos, this]
        rw [heq]
      · rw [resV_nonzero hAcc hz, resV_nonzero hAcc hz]
  · refine WP.mono (b2_ok hH Lv hEmv he hfit hpos hdb h19v h21v h24v h25v h26v
      (by rw [O.mem, hP]) hdgv hrv hd hTv hdo) fun t ⟨sp, rd, wr, cs, vs, fr, result⟩ => ?_
    refine ⟨sp.trans O.sp, rd.trans O.rd, wr.trans O.wr, ?_, ?_, O.mem ▸ fr, ?_⟩
    · intro r hr
      rw [cs r hr, O.get r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · intro r hr; rw [vs r hr, O.vcs r hr]
    · simpa only [O.mem] using result

end VG.Proof.RsaPss.AArch64.FixedSalt

end

end


/-!
# EMSA-PSS's check of an encoding on AArch64: correctness after the prologue

The encoding copied to `EM` (`copyIn_okC`); after the checks of the lengths,
verification's checks of `EM` (`check_ok`): `x0` is 1 exactly when the
encoding is consistent with the digest (`EncOk`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss (EncOk)
open VG.Proof.RsaPss.AArch64 (off off_add Lay Rep mgfWr slotR slot_keep updL b1_ok B1 wct mkB nz nz_lt resV msgV
  acc0V acc1V vlogic copyIn_ok bytes_apartL)
open VG.Proof.RsaPss.AArch64.Sgn (fb kR frame_sub frame_sub0 below_sub)

/-- What `chkK.post` asks of `x0`: the check with the hash function `Hs` (of
digests of `D` bytes) and MGF1's `Gs`. -/
def chkOut (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) : Bool :=
  Spec.RsaPss.verifyEncoding Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x0) D)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (s.gpr .x3).toNat
    (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32))

/-- The encoding, as the entry state gives it. -/
abbrev emB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat

/-- In the frame: the slots and the callee-saved registers' values. -/
structure MidC (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : FrC s t.mem

theorem AtC.toMid {s u : State} (h : AtC s u) : MidC s u := ⟨h.sp, h.rd, h.wr, h.v, h.fr⟩

/-- `AtC` after code that writes registers other than ours, and nothing but
`EM` in memory. -/
theorem AtC.only {s u u' : State} (h : AtC s u) {rs : List Reg} (o : Only rs u u')
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x1], r ∉ rs := by decide) : AtC s u' where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr .x19 (hr _ (by simp))).trans h.x19
  x20 := (o.gpr .x20 (hr _ (by simp))).trans h.x20
  x21 := (o.gpr .x21 (hr _ (by simp))).trans h.x21
  x23 := (o.gpr .x23 (hr _ (by simp))).trans h.x23
  x1 := (o.gpr .x1 (hr _ (by simp))).trans h.x1
  v := fun r hr' => (o.vcs r hr').trans (h.v r hr')
  mem := o.mem ▸ h.mem
  fr := o.mem ▸ h.fr
  lo := o.mem ▸ h.lo
  c := o.mem ▸ h.c

/-- `AtCT` after code that writes registers other than ours. -/
theorem AtCT.only {s u u' : State} (h : AtCT s u) {rs : List Reg} (o : Only rs u u') (hsy : u'.syms = u.syms)
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x1], r ∉ rs := by decide) : AtCT s u' :=
  ⟨h.e.only o hr, o.mem ▸ h.wm, o.mem ▸ h.wi, o.mem ▸ h.wc, o.mem ▸ h.wd, hsy.trans h.sy⟩

/-- Our part of the working space. -/
theorem rsa_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreC D tsH tsG s) :
    Region.Sub ⟨s.gpr .x6, oRsa⟩ (sR s) := rsa_subC hp

/-- The 16 bytes below the frame, in the stack. -/
theorem below16_sub (s : State) : Region.Sub (below (fb s) 16) (kR 288 s) := fun x h =>
  below_sub 288 s x (Offset.sub_below (fb s) (a := 16) (n := 16) (b := 288) (m := 288) (by decide) (by decide) x h)

/-- Our working space and the frame, laid out. -/
theorem lay_of {D : Nat} {tsH tsG : List FnTable} {s w : State} (hp : PreC D tsH tsG s) (hsp : w.sp = fb s) (h20 : w.gpr .x20 = s.gpr .x6)
    (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr) : Lay w (fb s) (s.gpr .x6) := by
  obtain hfb := fb_toNat hp
  have := s.sp.isLt
  have hws := hp.ws
  have hhs := hp.hs
  exact {
    sp := hsp
    x20 := h20
    fw := by rw [hwr]; exact List.mem_cons_self
    sw := ⟨sR s, by rw [hwr, hp.hwr]; simp, ⟨rfl, show oRsa ≤ (s.gpr .x7).toNat * 8 by unfold oRsa Proof.RsaPss.encScratch at *; omega_using [hhs]⟩⟩
    Fw := by omega_using [hfb]
    Sw := by unfold oRsa Proof.RsaPss.encScratch at *; omega_using [hws, hhs]
    dFS := (hp.ks.sub_left (frame_sub0 288 s)).sub_right (rsa_sub hp)
    dB := (hp.ks.sub_left (below16_sub s)).sub_right (rsa_sub hp) }

/-- What the checks write keeps `FrC`. -/
theorem fr_mgf {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreC D tsH tsG s) {m m' : Mem} (h : FrC s m)
    (hf : Frame (mgfWr (fb s) (s.gpr .x6) ++ [slotR (fb s) sPos]) m m') : FrC s m' := by
  refine h.frame hf (fun r hr => ?_) (fun r hr => ?_) <;>
  · simp only [mgfWr, slotR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.ks.sub_left (frame_sub 288 s (by decide))).sub_right (rsa_sub hp)
    · exact Offset.disjoint_below _ (by omega_using [])
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint_below _ (by rw [mgfFrame_eq]; omega_using [])
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)

/-- `AtC` after code that writes registers other than ours, and memory only
in our working space. -/
theorem AtC.keep {D : Nat} {tsH tsG : List FnTable} {s u u' : State} (hp : PreC D tsH tsG s) (h : AtC s u) {rs : List Reg} (k : Keep rs u u')
    (hf : Frame [⟨s.gpr .x6, oRsa⟩] u.mem u'.mem)
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x1], r ∉ rs := by decide) : AtC s u' := by
  obtain hd : ∀ {d n : Nat}, d + n ≤ frameBytes →
      ∀ r ∈ [(⟨s.gpr .x6, oRsa⟩ : Region)], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun hdn r hr' => by
    rw [List.mem_singleton.mp hr']
    exact (hp.ks.sub_left (frame_sub 288 s hdn)).sub_right (rsa_sub hp)
  exact {
    sp := k.sp.trans h.sp
    rd := k.rd.trans h.rd
    wr := k.wr.trans h.wr
    x19 := (k.gpr .x19 (hr _ (by simp))).trans h.x19
    x20 := (k.gpr .x20 (hr _ (by simp))).trans h.x20
    x21 := (k.gpr .x21 (hr _ (by simp))).trans h.x21
    x23 := (k.gpr .x23 (hr _ (by simp))).trans h.x23
    x1 := (k.gpr .x1 (hr _ (by simp))).trans h.x1
    v := fun r hr' => (k.vcs r hr').trans (h.v r hr')
    mem := h.mem.trans (hf.mono (by simp))
    fr := h.fr.frame hf (hd (by decide)) (hd (by decide))
    lo := by rw [slot_keep (d := sLo) hf (hd (by decide))]; exact h.lo
    c := by rw [slot_keep (d := sC) hf (hd (by decide))]; exact h.c }

/-- The encoding copied to `EM`. -/
theorem copyIn_okC {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreC D tsH tsG s) (hu : AtC s u) :
    WP isa copyIn u fun t => AtC s t ∧
      (∀ i < (s.gpr .x2).toNat, t.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0) ∧
      Frame [⟨s.gpr .x6, oRsa⟩] u.mem t.mem := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  have hwe := hp.we
  obtain L := lay_of hp hu.sp hu.x20 hu.wr
  unfold copyIn
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_addImm (by decide) fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_nil ?_)
  obtain O : Only [.x11, .x14, .x12] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  obtain L₃ := L.congr O.sp O.wr (O.get .x20)
  obtain hu₃ := hu.only O
  refine WP.mono (copyIn_ok L₃ (V := fun o => u₃.mem (off (s.gpr .x6) o)) (fun _ _ => rfl)
    (q := s.gpr .x1) (o := oEm) (n := (s.gpr .x2).toNat) (by omega_using [hk1]) (by unfold oEm oRsa; omega_using [hk2])
    (by rw [o₃.get .x14, e₂, o₁.get .x20, hu.x20])
    (by rw [o₃.get .x11, o₂.get .x11, e₁, hu.x1])
    (by rw [e₃, o₂.get .x23, o₁.get .x23, hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by
      rw [O.rd, O.wr, hu.rd, hp.hrd]
      exact ⟨emR s, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩)
    (hp.es.sub_right (rsa_sub hp))) fun t ⟨K, F, R⟩ => ⟨hu₃.keep hp K F, fun i hi => ?_, by rw [← O.mem]; exact F⟩
  obtain hb : Spec.Rsa.bytesAt u₃.mem (s.gpr .x1) (s.gpr .x2).toNat = emB s :=
    bytes_apartL hu₃.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.ke.sub_left (frame_sub0 288 s)).symm
      · exact hp.es.sub_right (rsa_sub hp)) (by omega_using [])
  rw [R (oEm + i) (by unfold oEm oRsa; omega_using [hk2, hi])]
  simp only [updL]
  rw [ite_eq_left ⟨by omega_using [], by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; omega_using [hi]⟩, Nat.add_sub_cancel_left, hb]

/-- The slots of the table of `MdHash`, from the table at the entry. -/
theorem ht_of {H : Hash} {dn : String} {f : MdFns} {G : Impl.Pbkdf2.Md.AArch64.Stream}
    {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State} (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s)
    (hw : AtCT s w) : HT H dn f (fb s) w.mem w.syms where
  wi := hw.wi.trans (ht.h0.trans (by rw [hw.sy]))
  wc := hw.wc.trans (ht.h3.trans (by rw [hw.sy]))
  wd := hw.wd.trans (ht.h4.trans (by rw [hw.sy]))
  fi := by rw [hw.sy]; exact ht.fi
  fc := by rw [hw.sy]; exact ht.fc
  fd := by rw [hw.sy]; exact ht.fd

/-- MGF1's working space, in ours. -/
theorem mgfScr_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreC D tsH tsG s) :
    Region.Sub ⟨off (s.gpr .x6) mgfOff, 8192⟩ (sR s) :=
  Offset.sub_base _ (by have := hp.hs; unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [this])

/-- Where MGF1 works, and the table of `MdHash`, from the table at the entry. -/
theorem env_of {D : Nat} {tsH tsG : List FnTable} {H : Hash} {dn : String} {f : MdFns}
    {G : Impl.Pbkdf2.Md.AArch64.Stream} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State}
    (hp : PreC D tsH tsG s) (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s) (hw : AtCT s w) :
    Env G g w (fb s) (s.gpr .x6) (stackArg s 1) := by
  obtain hfb := fb_toNat hp
  have hsp1 := hp.sp1
  have hwtG := hp.wtG
  have hws := hp.ws
  have hhs := hp.hs
  obtain hS := mgfScr_sub hp
  obtain kG : ∀ {R : Region}, R.Sub (kR 288 s) → Region.Disjoint ⟨stackArg s 1, 88⟩ R := fun hR =>
    (hp.ktG.sub_left hR).symm
  obtain sG : ∀ {R : Region}, R.Sub (sR s) → Region.Disjoint ⟨stackArg s 1, 88⟩ R := fun hR =>
    (hp.stG.sub_left hR).symm
  obtain hd : ∀ r ∈ mgfWr (fb s) (s.gpr .x6) ++ [⟨off (s.gpr .x6) mgfOff, 8192⟩, slotR (fb s) sPos],
      Region.Disjoint ⟨stackArg s 1, 88⟩ r := by
    intro r hr
    simp only [mgfWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sG (rsa_sub hp)
    · exact kG (below16_sub s)
    · exact kG (frame_sub 288 s (by decide))
    · exact kG (frame_sub 288 s (by decide))
    · rw [mgfFrame_eq]; exact (hp.ktG.sub_left (below_sub 288 s)).symm
    · exact sG hS
    · exact kG (frame_sub 288 s (by decide))
  obtain hd0 : ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region), ⟨s.gpr .x6, oRsa⟩], Region.Disjoint ⟨stackArg s 1, 88⟩ r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kG (frame_sub0 288 s)
      · exact sG (rsa_sub hp)
  obtain hin : ∀ d, d + 8 ≤ 88 → InRegions (w.rd ++ w.wr) (off (stackArg s 1) d) 8 := fun d hd' => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨tGR s, by simp, Offset.contains_base _ (k := 88) (by omega_using [hd']) (by omega_using [hd'])⟩
  exact {
    slot := hw.wm
    ok := by rw [hw.sy]; exact ht.gok
    rd := fun j hj => hin (8 * j) (by omega_using [hj])
    rdD := hin 48 (by decide)
    mem := fun m hm => by
      rw [hw.sy]
      exact ⟨TabMem.keep (TabMem.keep ht.gm hw.e.mem hd0) hm hd,
        ((tabG_keep hm hd (by decide)).trans (tabG_keep hw.e.mem hd0 (by decide))).trans ht.gD⟩
    sc := Covers.one (by
      rw [hw.e.wr, hp.hwr]
      exact ⟨sR s, by simp, Offset.contains_base _ (by unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [hhs])
        (by unfold mgfOff; omega_using [])⟩)
    F288 := by rw [mgfFrame_eq]; unfold chkStack Sgn.stk at hsp1; omega_using [hfb, hsp1]
    dStk := by rw [mgfFrame_eq]; exact (hp.ks.sub_left (below_sub 288 s)).sub_right hS
    Sw := by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [hws, hhs]
    dFw := (hp.ks.sub_left (frame_sub0 288 s)).sub_right hS }

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hHl hHv hGh hGl hGv hdo in
/-- After the checks of the lengths: `EM` checked, `x0` 1 exactly when the
encoding is consistent. -/
theorem chkMain_ok {tsH tsG : List FnTable} {s u : State} (hp : PreC H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hu : AtCT s u)
    (hem : ∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x2).toNat - (H.D + 2)))
    (hfit : H.D + 2 ≤ (s.gpr .x2).toNat)
    (hs : anyC s = 0 → (s.gpr .x4).toNat < (s.gpr .x2).toNat - H.D - 1) :
    WP isa (chkMain f H g) u fun t => MidC s t ∧ ∀ b : Bool, (b = true ↔ (0 = 1 → (emB s).getD 0 0 = 0) ∧
      Proof.RsaPss.EncOk₂ Gs Hs (Spec.Rsa.bytesAt s.mem (s.gpr .x0) H.D) ((emB s).drop 0) ((s.gpr .x2).toNat - 0) (zC s)
        (if anyC s = 0 then some (s.gpr .x4).toNat else none)) → t.gpr .x0 = if b then 1#64 else 0#64 := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hT0 := ht_of ht hu
  obtain E0 := env_of hp ht hu
  have hu := hu.e
  obtain L₀ := lay_of hp hu.sp hu.x20 hu.wr
  show WP isa (.seq (.block dbRegs) (seqs [.block acc0, mgfXor H g, .block clearTop, posScan, posCheck,
    FixedSalt.select f H])) u _
  refine WP.seq (WP.mono_syms (dbRegs_ok L₀ h9 hu.lo) fun t ⟨O, x25, x24⟩ sy => ?_)
  obtain hT1 : HT H dn f (fb s) t.mem t.syms := by rw [sy, O.mem]; exact hT0
  obtain E1 : Env Gm g t (fb s) (s.gpr .x6) (stackArg s 1) :=
    E0.step L₀ (by rw [O.mem]; exact Frame.refl _ _) O.rd O.wr sy
  obtain ht := hu.only O
  obtain L := lay_of hp ht.sp ht.x20 ht.wr
  generalize hk : (s.gpr .x2).toNat = k at hfit hs x25 hk1 hk2 hem
  obtain hkd : 0 + (k - H.D - 1) + H.D + 1 = k := by omega_using [hfit]
  obtain h25 : t.gpr .x25 = BitVec.ofNat 64 (k - H.D - 1) := by rw [x25]; congr 1; omega_using [hfit]
  obtain h23 : t.gpr .x23 = BitVec.ofNat 64 k := by rw [ht.x23, ← hk, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (b1_ok hGm hGh hGl hGv (H := H) L (V := fun o => t.mem (off (s.gpr .x6) o)) (fun _ _ => rfl) (k := k)
    (lo := 0) (db := k - H.D - 1) (c := cC s) (any := anyC s) (sv := s.gpr .x4) hkd (by omega_using [hfit]) hk2 (Nat.zero_le 1)
    h23 x24 h25 ht.lo ht.c ht.fr.any ht.fr.sl E1
    (rest := Impl.RsaPss.AArch64.FixedSalt.select f H)
    fun u B => ?_ : WP isa (seqs [.block acc0, mgfXor H g, .block clearTop, posScan, posCheck,
      Impl.RsaPss.AArch64.FixedSalt.select f H]) t _)
  have gu : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u.gpr r = t.gpr r := B.cs
  obtain hslot : ∀ d, d + 8 ≤ frameBytes →
      (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      (d + 8 ≤ sPos ∨ sPos + 8 ≤ d) →
      u.mem.readW (off (fb s) d) 64 = t.mem.readW (off (fb s) d) 64 := by
    intro d hd hn hf hpos
    apply slot_keep B.fr
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact L.slotW hd hn hf r h
    · rw [List.mem_singleton.mp h]
      exact Offset.disjoint _ hpos (by unfold frameBytes at hd; omega_using [hd]) (by decide)
  obtain hTu : HT H dn f (fb s) u.mem u.syms := by
    rw [B.sy]
    exact ⟨(hslot sIniH (by decide) (by decide) (by decide) (by decide)).trans hT1.wi,
      (hslot sCmpH (by decide) (by decide) (by decide) (by decide)).trans hT1.wc,
      (hslot sDigH (by decide) (by decide) (by decide) (by decide)).trans hT1.wd, hT1.fi, hT1.fc, hT1.fd⟩
  obtain hrd : ∀ j < H.D, InRegions (u.rd ++ u.wr) (s.gpr .x0 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [B.rd, B.wr, ht.rd, hp.hrd]
    exact ⟨dgR H.D s, by simp, Offset.contains_base _ (by omega_using [hj]) (by have := hp.wd; omega_using [hj, this])⟩
  refine WP.mono (VG.Proof.RsaPss.AArch64.FixedSalt.select_ok hH (L.congr B.sp B.wr (gu .x20 (by decide)))
    (W := wct (fun o => t.mem (off (s.gpr .x6) o)) (mkB Gs H.D (fun o => t.mem (off (s.gpr .x6) o)) (oEm + 0)
      (k - H.D - 1)) (oEm + 0) (k - H.D - 1) (cC s)) (e := oEm + 0) (db := k - H.D - 1)
    B.em (by omega_using []) (by unfold oEm oY; omega_using [hfit, hk2])
    (nz_lt (by omega_using [hfit])) (by omega_using [hk2]) (by rw [gu .x19 (by decide), ht.x19]) (by rw [gu .x21 (by decide), ht.x21])
    (by rw [gu .x24 (by decide), x24]) (by rw [gu .x25 (by decide), h25]) B.acc B.pos
    (by rw [hslot sDig (by decide) (by decide) (by decide) (by decide)]; exact ht.fr.dig) hrd
    (hp.ds.sub_right (rsa_sub hp))
    (by rw [hslot sAny (by decide) (by decide) (by decide) (by decide)]; exact ht.fr.any)
    (sl := (s.gpr .x4).toNat)
    (by rw [hslot sSaltLen (by decide) (by decide) (by decide) (by decide), ht.fr.sl, BitVec.ofNat_toNat,
      BitVec.setWidth_eq])
    hs
    (by
      intro hany hacc
      obtain heq := (VG.Proof.RsaPss.AArch64.acc1V_eq_zero _ _ _ _ _).mp hacc
      exact (VG.Proof.RsaPss.AArch64.eq_ofNat_iff (by omega_using [hk]) _).mp (heq.2.2.2 hany))
    (by
      obtain hb := VG.Proof.RsaPss.AArch64.acc_lt (fun o => t.mem (off (s.gpr .x6) o)) k 0 (cC s)
        (fun i => wct (fun o => t.mem (off (s.gpr .x6) o))
          (mkB Gs H.D (fun o => t.mem (off (s.gpr .x6) o)) (oEm + 0) (k - H.D - 1))
          (oEm + 0) (k - H.D - 1) (cC s) (oEm + 0 + i))
        (k - H.D - 1) (anyC s) (s.gpr .x4) (fun _ => 0) 0 (by omega_using [hk2])
        (fun h => by have := hs h; omega_using [hk2, this]) (fun _ => by decide)
      simpa [VG.Proof.RsaPss.AArch64.orF] using hb) hTu hdo) fun u' ⟨sp', rd', wr', cs', v', fr', x0'⟩ =>
    ⟨?_, fun b hb => ?_⟩
  · exact ⟨by rw [sp', B.sp, ht.sp], by rw [rd', B.rd, ht.rd], by rw [wr', B.wr, ht.wr],
      fun r hr => by rw [v' r hr, B.v r hr, ht.v r hr],
      fr_mgf hp (fr_mgf hp ht.fr B.fr) (fr'.mono fun r hr => List.mem_append_left _ hr)⟩
  obtain hl : H.D ≤ 2 ^ 64 := by have := hp.wd; omega_using [this]
  obtain hd : ∀ r ∈ mgfWr (fb s) (s.gpr .x6) ++ [slotR (fb s) sPos], Region.Disjoint (dgR H.D s) r := fun r hr => by
    simp only [mgfWr, slotR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ds.sub_right (rsa_sub hp)
    · exact (hp.kd.sub_left (below16_sub s)).symm
    · exact (hp.kd.sub_left (frame_sub 288 s (by decide))).symm
    · exact (hp.kd.sub_left (frame_sub 288 s (by decide))).symm
    · rw [mgfFrame_eq]; exact (hp.kd.sub_left (below_sub 288 s)).symm
    · exact (hp.kd.sub_left (frame_sub 288 s (by decide))).symm
  obtain hdig : Spec.Rsa.bytesAt u.mem (s.gpr .x0) H.D = Spec.Rsa.bytesAt s.mem (s.gpr .x0) H.D := by
    rw [bytes_apartL B.fr hd hl]
    exact bytes_apartL ht.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.kd.sub_left (frame_sub0 288 s)).symm
      · exact hp.ds.sub_right (rsa_sub hp)) hl
  rw [x0', hdig, ← funext hHs]
  refine vlogic hHv hGv hHl (x := emB s) (k := k) (lo := 0) (db := k - H.D - 1) (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hk]) (fun i hi => ?_) hkd
    (by omega_using [hfit]) (Nat.zero_le 1) hk2 (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _) rfl (fun h => hs h) ?_
  · show t.mem (off (s.gpr .x6) (oEm + i)) = _
    rw [O.mem]; exact hem i hi
  exact hb

end

end VG.Proof.RsaPss.AArch64.Chk
