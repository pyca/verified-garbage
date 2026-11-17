module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBlocks
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.PrefixCheck
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedHash
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! ### `RsaPss.X86_64.VerifyPadding`, which this module and modules that import it used -/

section

/-! ### `RsaPss.X86_64.SaltBack`, which this module and modules that import it used -/

section

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
    obtain Lv := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
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
  obtain Lv := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
  obtain Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun _ => generic kv hm sv)
  rw [decide_eq_true_eq] at hb
  refine WP.seq (X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun w =>
    w.mem = v.mem ∧ w.cf = some (decide ((W 36).toNat < db))) ?_ rfl) fun w ⟨⟨hmw, hc⟩, kw⟩ sw => ?_)
  · xrun [ea_sp, Lv.rsp, Lv.ld (d := sSlen) (by decide), Lv.ld (d := sDb) (by decide),
      Rv.rd (d := sSlen) 36 rfl (by decide), Rv.rd (d := sDb) 24 rfl (by decide), hdb]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show db < 2 ^ 64 by omega_using [hfit])]
  obtain kuw : Keep [.rax] u w := (kv.trans kw).mono (by decide)
  obtain hmu : w.mem = u.mem := hmw.trans hm
  refine WP.ite (M := isa) _ (show isa.eval .b w = _ from hc) (fun hf => ?_) (fun _ => generic kuw hmu (sw.trans sv))
  rw [decide_eq_true_eq] at hf
  obtain Lw := L.congr (kuw.gpr (by decide)) kuw.2.2 (by rw [hmu])
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

end

end

/-!
# RSASSA-PSS verification on x86-64: correctness

`vlogic`: what the code computes is zero exactly when the encoding is
valid, byte by byte (`VerifyCases.lean`). `verify_body`: from the entry
state, the body of the frame returns 1 exactly when `RsaPss.verify` holds,
with the callee-saved registers restored.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

theorem list_eq_iff_getD {a b : List Byte} {n : Nat} (ha : a.length = n) (hb : b.length = n) :
    a = b ↔ ∀ i < n, a.getD i 0 = b.getD i 0 := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    apply List.ext_getElem (by omega_arith)
    intro i h₁ h₂
    have := h i (by omega_arith)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂] at this

theorem ofNat_eq_iff {a : Nat} (ha : a < 2 ^ 64) (b : BitVec 64) : BitVec.ofNat 64 a = b ↔ a = b.toNat := by
  constructor
  · rintro rfl; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  · rintro rfl; simp

/-- What the code computes, against the checks of `verifyEncoding` (MGF1's `G`, the
digest's `H`). -/
theorem vlogic (G H : Spec.Mgf1.Hash) (hH : Proof.Mgf1.Valid H) (x mHash : List Byte) {k lo z : Nat} (fixed : Bool)
    (slen : BitVec 64) {sLen : Option Nat} (hsl : sLen = if fixed then some slen.toNat else none)
    (hx : x.length = k) (hlo : lo ≤ 1) (hfit : H.len + 2 ≤ k - lo) (hk : k ≤ 1024) :
    let em := x.drop lo
    let L := k - lo - H.len - 1
    let dbL := vDb₂ G H em L z
    let fd := decide (lz dbL < L)
    let pos := if lz dbL < L then lz dbL else 0
    let val := if lz dbL < L then dbL.getD (lz dbL) 0 else 0
    (acc1V (acc0V (x.getD (k - 1) 0) (x.getD 0 0) (x.getD lo 0) ((0xFF : Byte) >>> z) lo) fd val fixed
        (BitVec.ofNat 64 (L - pos - 1)) slen = 0 ∧
      ∀ i < H.len, (H.hash (Spec.RsaPss.zeros 8 ++ mHash ++ dbL.drop (pos + 1))).getD i 0 = (vH H em L).getD i 0) ↔
    ((lo = 1 → x.getD 0 0 = 0) ∧ EncOk₂ G H mHash em (k - lo) z sLen) := by
  dsimp only
  have hvH : (vH H (x.drop lo) (k - lo - H.len - 1)).length = H.len := by simp [vH]; omega_arith
  rw [acc1V_eq_zero, acc0V_eq_zero _ _ _ _ hlo]
  have e1 : x.getD (k - 1) 0 = (x.drop lo).getD (k - lo - 1) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]; congr 2; omega_arith
  have e2 : x.getD lo 0 = (x.drop lo).getD 0 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  rw [e1, e2]
  unfold EncOk₂
  rw [← list_eq_iff_getD (hH.2 _) hvH]
  generalize vDb₂ G H (x.drop lo) (k - lo - H.len - 1) z = dbL
  by_cases hf : lz dbL < k - lo - H.len - 1
  · rw [ifp hf, ifp hf, decide_eq_true hf, ofNat_eq_iff (by omega_arith)]
    subst hsl
    constructor
    · rintro ⟨⟨⟨hA, hP, hB⟩, hC, -, hS⟩, hH⟩
      refine ⟨hP, hA, hB, hf, hC, ?_, hH⟩
      cases fixed
      · exact .inl rfl
      · exact .inr (by rw [ifp rfl]; congr 1; have := hS rfl; omega_arith)
    · rintro ⟨hP, hA, hB, -, hC, hS, hH⟩
      refine ⟨⟨⟨hA, hP, hB⟩, hC, rfl, fun hfx => ?_⟩, hH⟩
      subst hfx
      rw [ifp rfl] at hS
      rcases hS with h | h
      · cases h
      · have := Option.some.inj h; omega_arith
  · rw [decide_eq_false hf]
    constructor
    · rintro ⟨⟨_, _, h, _⟩, _⟩; cases h
    · rintro ⟨_, _, _, h, _⟩; exact absurd h hf

/-- What `verifyK.post` asks of `rax`: verification with the hash function
`Hs` and MGF1's `Gs`. -/
def verifyOut (Hs Gs : Spec.Mgf1.Hash) (s : State) : Bool :=
  Spec.RsaPss.verify Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) Hs.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
    (Spec.RsaPss.expectedSaltLen (stackArg s 2) ((stackArg s 3).setWidth 32))

/-- Before the epilogue: the result in `rax`, the saved registers in their
slots. -/
structure VDone (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 4)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : (t.gpr .rax).setWidth 32 = if verifyOut Hs Gs s then 1 else 0

variable {H : Impl.Pbkdf2.Md.X86_64.Hash}

variable {g : Impl.Mgf1.X86_64.Table.Fns} (hg : FnsSafe g)

include hg in
theorem vmid_safe : (seqs [.block acc0, mgfXor H g, .block clearTop, scanCheck H]).allInstrs safeI = true := by
  simp only [seqs, scanCheck, prefixCheck, prefixWords, prefixBytes, posScan, posCheck, Code.allInstrs,
    mgfXor_safe hg, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hg in
theorem vmid_xd : (seqs [.block acc0, mgfXor H g, .block clearTop, scanCheck H]).x86_64Depth ≤ 16 := by
  have := mgfXor_xd (H := H) hg
  simp only [seqs, scanCheck, prefixCheck, prefixWords, prefixBytes, posScan, posCheck, byteLoop, Code.x86_64Depth,
    Nat.max_le]
  omega_using [this]

theorem ite_setWidth {p : Prop} [Decidable p] {b : Bool} (h : p ↔ b = true) :
    ((if p then 1 else 0 : BitVec 64).setWidth 32) = if b then 1 else 0 := by
  by_cases hb : b = true
  · rw [ifp (h.mpr hb), ifp hb]; rfl
  · rw [ifn (fun hp => hb (h.mp hp)), ifn hb]; rfl

theorem map_range_drop {x : List Byte} {lo n : Nat} (hn : lo + n ≤ x.length) {f : Nat → Byte}
    (hf : ∀ i < n, f i = x.getD (lo + i) 0) : (List.range n).map f = (x.drop lo).take n := by
  rw [list_eq_iff_getD (n := n) (by simp) (by simp; omega_arith)]
  intro i hi
  rw [getD_map_range, ifp hi, hf i hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi, List.getElem?_drop]

end VG.Proof.RsaPss.X86_64

end

end

/-!
# RSASSA-PSS verification on x86-64: the checks and the calling convention

`verify_ok`: from the entry state, `verify` returns 1 exactly when
`RsaPss.verify` holds, refusing a modulus whose first byte is zero and an
encoding too short for the digest and the salt, with the callee-saved
registers restored. `verify_correct`: it meets `verifyK`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

variable {tsH tsG : List FnTable} {Hs Gs : Spec.Mgf1.Hash}

theorem vfail_done {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 4)) (R : Rep t.mem (fb s) (stackArg s 4) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12) (hf : verifyOut Hs Gs s = false) :
    WP isa verifyFail t (VDone Hs Gs s) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rax = 0) ?_ rfl)
    fun t' ⟨⟨hm, hax⟩, k⟩ => ?_
  · xrun [verifyFail]
  have R' : Rep t'.mem (fb s) (stackArg s 4) V W := hm ▸ R
  refine ⟨L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), k.2.2.trans hw, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide), hcs r hr]
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · rw [hax, hf]; rfl

/-- The modulus' first byte. -/
theorem vn0_ok {s t : State} (hp : VPre tsH tsG s) (L : Lay t (fb s) (stackArg s 4)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 4) V W) (h18 : W 18 = s.gpr .rdi) (hrd : t.rd = s.rd)
    (hf : Frame (vwrR s) s.mem t.mem) :
    WP isa (.block n0) t fun t' => Keep [.rsi, .rax] t t' ∧ t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdi)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdi)).toNat = 0)) := by
  have hk1 := hp.k1
  have hn : t.mem (s.gpr .rdi) = s.mem (s.gpr .rdi) := by
    have := hf.bytes (R := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) (vin_apart hp.dKn hp.dns)
      (by dsimp only; have := hp.wN; omega_using []) (i := 0) (by dsimp only; omega_using [hk1])
    simpa using this
  have hin : InRegions (t.rd ++ t.wr) (s.gpr .rdi) 1 := by
    rw [hrd]
    apply hp.hrd.left
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hk1]⟩
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdi)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdi)).toNat = 0))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨k, h⟩
  xrun [n0, ea_sp, ea_at0, L.rsp, L.ld (d := sN) (by decide), R.rd (d := sN) 18 rfl (by decide), h18, hin, hn]
  rw [zext8, BitVec.and_self, ofNat_beq_zero (by have := (s.mem (s.gpr .rdi)).isLt; omega_using [])]
  exact ⟨rfl, rfl⟩

theorem expectedSaltLen_eq (slen : BitVec 64) (any : BitVec 32) :
    Spec.RsaPss.expectedSaltLen slen any = if decide (any = 0) then some slen.toNat else none := by
  unfold Spec.RsaPss.expectedSaltLen; by_cases h : any = 0 <;> simp [h]


end VG.Proof.RsaPss.X86_64
