module
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignMain
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedHash
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBlocks
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain

/-! ### `RsaPss.X86_64.FixedSaltBack`, which only this module used -/

section

/-! Verification's fixed-length salt input, built without a masked shift. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H)
  (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem fixedSaltBack_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {lo db sl : Nat} {dig : Addr}
    (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db)
    (hsl : W 36 = BitVec.ofNat 64 sl) (hdg : W 37 = dig)
    (hlo : lo ≤ 1) (hslFit : sl < db) (hfit : lo + db + H.D + 1 ≤ 1024)
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i)) {dn : String} {f : MdFns}
    (hT : HT H dn f W u.syms) (hdk : DigOK H) :
    let msg := Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++
      (List.range sl).map (fun i => V (oEm + lo + db - sl + i))
    WP isa (fixedSaltBack f H) u fun u' =>
      Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      (∃ V' W', Rep u'.mem F S V' W' ∧
        ∀ j < nW, j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 → W' j = W j) ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D,
        (lk.G.hash msg).getD i 0 = V (oEm + lo + db + i) then 1 else 0 := by
  intro msg
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hL := hH.dims.L
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have hml : msg.length = 8 + H.D + sl := by
    simp only [msg, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range]
  have hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + sl + H.P.L) (b := H.P.B) hB0
  have hnb2 := Nat.div_mul_le_self (8 + H.D + sl + H.P.L) H.P.B
  have hnb : ((8 + H.D + sl + H.P.L) / H.P.B + 1) * H.P.B ≤ 2048 := by rw [Nat.succ_mul]; omega_arith
  have hfitN : 8 + H.D + sl < ((8 + H.D + sl + H.P.L) / H.P.B + 1) * H.P.B := by rw [Nat.succ_mul]; omega_arith
  unfold fixedSaltBack fixedSaltPrefix fixedHead seqs seqs seqs seqs
  apply WP.assoc'
  apply WP.assoc'
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [hashSaltLen]) (by exact Nat.zero_le 16)
    (hashSaltLen_ok hH L R (k := 36) (by decide) hsl (by omega_arith))) fun u0 ⟨⟨L0, k0, R0⟩, f0⟩ s0 => ?_)
  have hS0 := chain (u := u) rfl L.rsp (fun _ _ => rfl) f0
  apply WP.assoc'
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [clearNb]) (by exact Nat.zero_le 16)
    (clearNb_ok hH L0 R0 (nbm := (8 + H.D + sl + H.P.L) / H.P.B + 1) (by simp [upd]) (Nat.succ_pos _) hnb))
    fun u1 ⟨⟨L1, k1, hcx1, R1⟩, f1⟩ s1 => ?_)
  have hS1 := chain (u := u) k0.2.2 L0.rsp hS0 f1
  refine WP.seq (X86_64.WP.mono_syms (copyDigest_ok hH L1 R1 (p := dig) (by simp [upd, hdg]) hcx1
    (fun i hi => by rw [k1.2.1, k0.2.1, k1.2.2, k0.2.2]; exact hdR i hi)
    (fun i hi j hj => Outside.ne L1 (by rw [k1.2.2, k0.2.2]; exact hdO i hi) (by omega_arith)))
    fun u2 ⟨L2, k2, R2⟩ s2 => ?_)
  have salt_src : ∀ i < sl, u2.mem (off S (oEm + lo + db - sl + i)) =
      V (oEm + lo + db - sl + i) := by
    intro i hi
    rw [R2.scr _ (by omega_arith)]
    simp only [cpV, clrV]
    rw [ifn (by omega_arith), ifn (by omega_arith)]
  apply WP.assoc'
  refine WP.seq (X86_64.WP.mono_syms (copyFixedSalt_ok hH L2 R2 (e := oEm + lo) (by simp [upd, he]) (by simp [upd, hdb])
    (by simp [upd, hsl]) hslFit (by omega_arith) (by omega_arith)
    ((k2.gpr (by decide)).trans hcx1)) fun u3 ⟨L3, k3, R3⟩ s3 => ?_)
  refine WP.seq (X86_64.WP.mono_syms (padSalt_ok L3 R3 (sl := sl) (by simp [upd, hsl]) (by omega_arith))
    fun u4 ⟨L4, k4, R4⟩ s4 => ?_)
  refine WP.seq (WP.mono (fixedHash_gen hH K L4 R4 (ℓ := 8 + H.D + sl)
    (nbm := (8 + H.D + sl + H.P.L) / H.P.B + 1) (by simp [upd]) (by simp [upd]) rfl hnb
    (by rw [s4, s3, s2, s1, s0]; exact hT.congr rfl (by simp [upd]) (by simp [upd]) (by simp [upd])) hdk)
    fun u5 ⟨L5, rd5, wr5, cs5, V5, W5, R5, hout5, hW5, hdig⟩ => ?_)
  have hdig5 := hdig msg hml (fun i hi => ?_)
  rotate_left
  · simp only [upd, cpV, clrV, msg, getD_app, List.length_append, RsaPss.zeros_length,
      List.length_map, List.length_range, getD_map_range, bytesF]
    by_cases h0 : i = 8 + H.D + sl
    · subst h0
      rw [ifp rfl, ifp rfl, ifn (by omega_arith), ifn (by omega_arith)]
      exact BitVec.zero_or.symm
    rw [ifn (by omega_arith), ifn h0]
    have oz : ∀ x : Byte, x ||| 0 = x := fun x => BitVec.or_zero
    rw [oz]
    by_cases h1 : i < 8
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_arith),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega_arith),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + ((8 + H.D + sl + H.P.L) / H.P.B + 1) * H.P.B by omega_arith),
        ifp (show i < 8 + H.D by omega_arith), ifp h1, RsaPss.zeros_getD]
    by_cases h2 : i < 8 + H.D
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_arith),
        ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D by omega_arith), ifp h2, ifn h1,
        ifp (show i - 8 < H.D by omega_arith), show oY + i - (oY + 8) = i - 8 by omega_arith]
      exact hS1 _ (hdO _ (by omega_arith))
    by_cases h3 : i < 8 + H.D + sl
    · rw [ifp (show oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl by omega_arith), ifn h2,
        ifp (show i - (8 + H.D) < sl by omega_arith), show oY + i - (oY + (8 + H.D)) = i - (8 + H.D) by omega_arith]
      exact salt_src _ (by omega_arith)
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_arith),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega_arith),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + ((8 + H.D + sl + H.P.L) / H.P.B + 1) * H.P.B by omega_arith), ifn h2,
        ifn (show ¬ i - (8 + H.D) < sl by omega_arith)]
  have h23 : W5 23 = off S (oEm + lo) := by
    rw [hW5 23 (by decide) (by decide) (by decide)]; simp [upd, he]
  have h24 : W5 24 = BitVec.ofNat 64 db := by
    rw [hW5 24 (by decide) (by decide) (by decide)]; simp [upd, hdb]
  refine WP.mono (cmpH_ok hH L5 R5 h23 h24 (by omega_arith)) fun u6 ⟨k6, hm6, hax6⟩ => ?_
  have L6 : Lay u6 F S := L5.congr (k6.gpr (by decide)) k6.2.2 (by rw [hm6])
  refine ⟨L6, k6.2.1.trans (rd5.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans (k1.2.1.trans k0.2.1))))),
    k6.2.2.trans (wr5.trans (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans (k1.2.2.trans k0.2.2))))),
    fun r hr => ?_, ⟨V5, W5, hm6 ▸ R5, fun j hj a b c d => ?_⟩, ?_⟩
  · rw [keep_cs k6 (by decide) r hr, cs5 r hr, keep_cs k4 (by decide) r hr,
      keep_cs k3 (by decide) r hr, keep_cs k2 (by decide) r hr, keep_cs k1 (by decide) r hr,
      keep_cs k0 (by decide) r hr]
  · rw [hW5 j hj c d]; simp [upd, a, b]
  · rw [hax6]
    have h33 : W5 33 = W 33 := by
      rw [hW5 33 (by decide) (by decide) (by decide)]; simp [upd]
    have hH' : ∀ i < H.D, V5 (oDig + i) = (lk.G.hash msg).getD i 0 := fun i hi => by
      rw [map_range_getD hdig5 hi, ← lk.hash]
    have hE : ∀ i < H.D, V5 (oEm + lo + db + i) = V (oEm + lo + db + i) := fun i hi => by
      rw [hout5 _ (by omega_arith) ⟨by unfold oLen; omega_arith, by omega_arith⟩]
      simp only [upd, cpV, clrV]
      rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
    rw [h33]
    congr 1
    apply propext
    exact and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => by rw [hH' i hi, hE i hi]

end VG.Proof.RsaPss.X86_64

end

end


/-! Public dispatch between fixed and inferred salt lengths. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

/-- The public fixed-length suffix agrees with the decoded suffix when
padding and length checks have succeeded. -/
theorem fixedSalt_suffix (V : Nat → Byte) (e : Nat) {db pos : Nat} (hp : pos < db) :
    (List.range (db - pos - 1)).map (fun i => V (e + db - (db - pos - 1) + i)) =
      ((List.range db).map (fun i => V (e + i))).drop (pos + 1) := by
  apply List.ext_getElem (by simp; omega_using [])
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
  congr 1
  omega_using [hp]

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H)
  (K : Pbkdf2.Md.X86_64.Callees H) {f : MdFns} (hf : MdFnsSafe f)

include hH hf in
theorem saltBack_safe : (saltBack f H).allInstrs safeI = true := by
  simp only [saltBack, fixedSaltBack, fixedSaltPrefix, fixedHead, clearNb, padSalt, genericSaltBack, seqs, clearY,
    copyDigest, copyFixedSalt, copyDb, shift, shiftPass, cmpH, Code.allInstrs, ctHash_safe hH hf, fixedHash_safe hH hf,
    rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hf in
theorem saltBack_xd : (saltBack f H).x86_64Depth ≤ 8 := by
  have := ctHash_xd (H := H) hf
  have := fixedHash_xd (H := H) hf
  simp only [saltBack, fixedSaltBack, fixedSaltPrefix, fixedHead, clearNb, padSalt, genericSaltBack, seqs, clearY,
    copyDigest, copyFixedSalt, copyDb, shift, shiftPass, cmpH, byteLoop, Code.x86_64Depth, Nat.max_le]
  omega_arith

include hH K in
theorem saltBack_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {dn : String} (hdk : DigOK H)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (hT : HT H dn f W u.syms) {lo db pos : Nat} {dig : Addr}
    (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db)
    (hpos : W 34 = BitVec.ofNat 64 pos)
    (hl : W 27 = BitVec.ofNat 64 (db - pos - 1 + (8 + H.D))) (hdg : W 37 = dig)
    (hlo : lo ≤ 1) (hdb1 : 1 ≤ db) (hpd : pos < db) (hfit : lo + db + H.D + 1 ≤ 1024)
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i))
    (hmatch : W 35 = 0 → W 33 = 0 → W 36 = BitVec.ofNat 64 (db - pos - 1)) :
    let msg := Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++
      ((List.range db).map fun i => V (oEm + lo + i)).drop (pos + 1)
    WP isa (saltBack f H) u fun u' =>
      Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      (∃ V' W', Rep u'.mem F S V' W' ∧
        ∀ j < nW, j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 →
          j ≠ 44 → j ≠ 45 → j ≠ 46 → W' j = W j) ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D,
        (lk.G.hash msg).getD i 0 = V (oEm + lo + db + i) then 1 else 0 := by
  intro msg
  let Q := fun u' : State =>
    Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      (∃ V' W', Rep u'.mem F S V' W' ∧
        ∀ j < nW, j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 →
          j ≠ 44 → j ≠ 45 → j ≠ 46 → W' j = W j) ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D,
        (lk.G.hash msg).getD i 0 = V (oEm + lo + db + i) then 1 else 0
  have generic {v : State} (kv : Keep [.rax] u v) (hm : v.mem = u.mem) (hs : v.syms = u.syms) :
      WP isa (genericSaltBack f H) v Q := by
    have Lv := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
    refine WP.mono (vback_ok hH K lk hdk Lv (hm ▸ R) (hs ▸ hT) he hdb hpos hl hdg hlo hdb1 hpd hfit
      (fun i hi => by rw [kv.2.1, kv.2.2]; exact hdR i hi)
      (fun i hi => by rw [kv.2.2]; exact hdO i hi)) fun t ⟨Lt, rd, wr, cs, ⟨Vt, Wt, Rt, hw⟩, out⟩ => ?_
    refine ⟨Lt, rd.trans kv.2.1, wr.trans kv.2.2, fun r hr => ?_,
      ⟨Vt, Wt, Rt, fun j hj _ b c d e f g => hw j hj b c d e f g⟩, ?_⟩
    · rw [cs r hr, keep_cs kv (by decide) r hr]
    · simpa only [hm] using out
  unfold saltBack
  refine WP.seq (X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun v =>
    v.mem = u.mem ∧ v.zf = some (decide (W 35 = 0))) ?_ rfl) fun v ⟨⟨hm, hz⟩, kv⟩ sv => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  have Lv := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun _ => generic kv hm sv)
  rw [decide_eq_true_eq] at hb
  refine WP.seq (X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun w =>
    w.mem = v.mem ∧ w.cf = some (decide ((W 36).toNat < db))) ?_ rfl) fun w ⟨⟨hmw, hc⟩, kw⟩ sw => ?_)
  · xrun [ea_sp, Lv.rsp, Lv.ld (d := sSlen) (by decide), Lv.ld (d := sDb) (by decide),
      Rv.rd (d := sSlen) 36 rfl (by decide), Rv.rd (d := sDb) 24 rfl (by decide), hdb]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show db < 2 ^ 64 by omega_using [hfit])]
  have kuw : Keep [.rax] u w := (kv.trans kw).mono (by decide)
  have hmu : w.mem = u.mem := hmw.trans hm
  refine WP.ite (M := isa) _ (show isa.eval .b w = _ from hc) (fun hf => ?_) (fun _ => generic kuw hmu (sw.trans sv))
  rw [decide_eq_true_eq] at hf
  have Lw := L.congr (kuw.gpr (by decide)) kuw.2.2 (by rw [hmu])
  refine WP.mono (fixedSaltBack_ok hH K lk Lw (hmu ▸ R) he hdb
    (show W 36 = BitVec.ofNat 64 (W 36).toNat by simp) hdg hlo hf hfit
    (fun i hi => by rw [kuw.2.1, kuw.2.2]; exact hdR i hi)
    (fun i hi => by rw [kuw.2.2]; exact hdO i hi) (by rw [sw, sv]; exact hT) hdk)
    fun t ⟨Lt, rd, wr, cs, ⟨Vt, Wt, Rt, hw⟩, out⟩ => ?_
  refine ⟨Lt, rd.trans kuw.2.1, wr.trans kuw.2.2, fun r hr => ?_,
    ⟨Vt, Wt, Rt, fun j hj a b c d _ _ _ => hw j hj a b c d⟩, ?_⟩
  · rw [cs r hr, keep_cs kuw (by decide) r hr]
  · rw [out]
    by_cases hacc : W 33 = 0
    · have hsl : (W 36).toNat = db - pos - 1 := by
        rw [hmatch hb hacc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hfit])]
      rw [hsl, fixedSalt_suffix V (oEm + lo) hpd, hmu]
    · simp only [hacc, false_and, ↓reduceIte]

end VG.Proof.RsaPss.X86_64
