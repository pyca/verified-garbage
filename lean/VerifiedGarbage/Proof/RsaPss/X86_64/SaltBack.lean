module
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignMain

import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltBack
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.Framework.X86_64.Syms

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
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
  congr 1
  omega

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
  omega

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
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show db < 2 ^ 64 by omega)]
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
        rw [hmatch hb hacc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hsl, fixedSalt_suffix V (oEm + lo) hpd, hmu]
    · simp only [hacc, false_and, ↓reduceIte]

end VG.Proof.RsaPss.X86_64
