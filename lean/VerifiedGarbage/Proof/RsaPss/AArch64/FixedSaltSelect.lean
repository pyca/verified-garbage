module
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyB2

import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltHash
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyLogic
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.AArch64.Select

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
    (hAcc : acc.toNat < 2^63) :
    WP isa (Impl.RsaPss.AArch64.FixedSalt.select H) u
      fun u' => u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
        (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u'.gpr r = u.gpr r) ∧
        (∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) ∧
        Frame (mgfWr F S) u.mem u'.mem ∧
        u'.gpr .x0 = resV acc (hH.SH.H.hash (msgV (Spec.Rsa.bytesAt u.mem dig H.D) (fun i => W (e + i)) db pos))
          W e db H.D := by
  unfold Impl.RsaPss.AArch64.FixedSalt.select
  refine WP.seq (wp_ldrSp (by decide) (ld_slot L (by decide)) fun v O e9 => wp_nil ?_)
  have Lv := L.congr O.sp O.wr (O.get .x20)
  have h9 : v.gpr .x9 = any := by rw [e9, L.sp, hAny]
  have hEmv : ∀ o, oEm ≤ o → o < oY → v.mem (off S o) = W o := by rw [O.mem]; exact hEm
  have h19v : v.gpr .x19 = off S oSt := by rw [O.get .x19, h19]
  have h21v : v.gpr .x21 = off S oDig := by rw [O.get .x21, h21]
  have h24v : v.gpr .x24 = off S e := by rw [O.get .x24, h24]
  have h25v : v.gpr .x25 = BitVec.ofNat 64 db := by rw [O.get .x25, h25]
  have h26v : v.gpr .x26 = acc := by rw [O.get .x26, h26]
  have hdgv : v.mem.readW (off F sDig) 64 = dig := by rw [O.mem, hdg]
  have hrv : ∀ j < H.D, InRegions (v.rd ++ v.wr) (dig + BitVec.ofNat 64 j) 1 := by
    rw [O.rd, O.wr]; exact hr
  refine WP.ite _ (eval_zero _ _) (fun ht => ?_) (fun hf => ?_)
  · have ha : any = 0 := by rw [h9] at ht; exact beq_iff_eq.mp ht
    have hslt := hFits ha
    have hp' : db - sl - 1 < db := by omega
    have hrev : db - (db - sl - 1) - 1 = sl := by omega
    refine WP.mono (finish_ok hH Lv hEmv he hfit hp' hdb h19v h21v h24v h25v h26v
      (by rw [O.mem, hrev, hSl]) hdgv hrv hd) fun t ⟨sp, rd, wr, cs, vs, fr, result⟩ => ?_
    refine ⟨sp.trans O.sp, rd.trans O.rd, wr.trans O.wr, ?_, ?_, O.mem ▸ fr, ?_⟩
    · intro r hr
      rw [cs r hr, O.get r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · intro r hr; rw [vs r hr, O.vcs r hr]
    · rw [result, O.mem]
      by_cases hz : acc = 0
      · have heq : db - sl - 1 = pos := by have := hMatch ha hz; omega
        rw [heq]
      · rw [resV_nonzero hAcc hz, resV_nonzero hAcc hz]
  · refine WP.mono (b2_ok hH Lv hEmv he hfit hpos hdb h19v h21v h24v h25v h26v
      (by rw [O.mem, hP]) hdgv hrv hd) fun t ⟨sp, rd, wr, cs, vs, fr, result⟩ => ?_
    refine ⟨sp.trans O.sp, rd.trans O.rd, wr.trans O.wr, ?_, ?_, O.mem ▸ fr, ?_⟩
    · intro r hr
      rw [cs r hr, O.get r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · intro r hr; rw [vs r hr, O.vcs r hr]
    · simpa only [O.mem] using result

end VG.Proof.RsaPss.AArch64.FixedSalt
