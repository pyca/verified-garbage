module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecOut
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaOaep.Arm.DecSpec
import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSAES-OAEP decryption on ARMv7: the message's length and the result

`*msg_len := (t - idx - 1) ∧ ok` and the result `(ok ∧ 1) ∨ ((r = 2) ? 2 :
0)` (`end_vp`): with `out` from `DecOut.lean`, what `decrypt` says
(`decOut_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sAcc sPos)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.Mgf1 (ifp ifn)

variable (h g : OHash)

theorem mlV_eq {P : EP} {σ : State} (ht : 0 < tN h P) :
    (BitVec.ofNat 32 P.K - BitVec.ofNat 32 (2 * h.H.D + 2) - BitVec.ofNat 32 (idx h g P σ)) &&& okW h g P σ =
      BitVec.ofNat 32 (mlV h g P σ) := by
  have hl := idx_lt h g (P := P) (σ := σ) ht
  have htN : tN h P = P.K - (2 * h.H.D + 1) := rfl
  unfold mlV okW maskOf
  by_cases hc : okP h g P σ
  · rw [ifp hc, ifp hc, BitVec.and_allOnes, Offset.ofNat_sub_ofNat (w := 32) (by omega),
      Offset.ofNat_sub_ofNat (w := 32) (by omega)]
  · rw [ifn hc, ifn hc]; exact BitVec.and_zero

theorem okW_one (P : EP) (σ : State) : okW h g P σ &&& 1 = if okP h g P σ then 1 else 0 := by
  unfold okW maskOf
  by_cases hc : okP h g P σ
  · rw [ifp hc, ifp hc]; decide
  · rw [ifn hc, ifn hc]; decide

theorem Bp_getD (P : EP) (σ : State) (j : Nat) : Bp h g P σ j = (sL (tN h P) (T h g P σ)).getD j 0 := by
  unfold Bp
  by_cases e : j < tN h P
  · rw [ifp e, sL_getD e]
  · rw [ifn e, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [sL_length]; omega)]; rfl

/-- `msg_len` in `r1`, the length in `r3`, zero in `r2`. -/
abbrev O4 (P : EP) (σ s : State) : Prop :=
  (Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧
    ∀ i < P.K, s.mem (byteAt P.out i) = if okP h g P σ then Bp h g P σ (i + aV h g P σ) else 0) ∧
    s.gpr .r1 = P.ml ∧ s.gpr .r3 = BitVec.ofNat 32 (mlV h g P σ) ∧ s.gpr .r2 = 0

/-- After `*msg_len`. -/
abbrev O5 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧
    (∀ i < P.K, s.mem (byteAt P.out i) = if okP h g P σ then Bp h g P σ (i + aV h g P σ) else 0) ∧
    s.mem.readW (State.addr P.ml) 64 = BitVec.ofNat 64 (mlV h g P σ)

theorem mlV_lt (P : EP) (σ : State) (hK : P.K ≤ 1024) : mlV h g P σ < 2 ^ 32 := by
  unfold mlV; split <;> omega

theorem end_vp (P : EP) :
    VP (O3 h g P) (.seq (.block (mlSet h.H)) (.seq (.block mlStore) (.block decRet))) (Fin h.G g.G P) := by
  refine VP.seq (G := O4 h g P)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hb⟩ => ?_) ?_
  · have hi := hk.1.1
    have hg := hi.geo
    have hD := h.D_le
    have hK := hi.k1024
    have hfit := hk.1.2.1
    obtain ⟨a2, r2, v2⟩ := argAt hi hc.st (j := 2) (by decide)
    obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
    replace v2 : s.mem.readW (P.lay.fr (arg 2)) 32 = P.ml := v2
    replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
    have hw : WP isa (.block (mlSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r1 = P.ml ∧ t.gpr .r3 = BitVec.ofNat 32 (mlV h g P σ) ∧ t.gpr .r2 = 0 := by
      prun [mlSet, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, a2, r2, v2, a4, r4, v4, arg_lt, hk.2.1, hk.2.2,
        sOk_lt, movw_val (show 2 * h.H.D + 2 < 2 ^ 16 by omega), movw_val (show 0 < 2 ^ 16 by decide), dpVal,
        mlV_eq h g (P := P) (σ := σ) (show 0 < tN h P by show 0 < P.K - (2 * h.H.D + 1); omega)]
      rfl
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t1, t3, t2⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hb⟩, t1, t3, t2⟩
  refine VP.seq (G := O5 h g P) (mlStore_vp P (fun σ s hs => ⟨⟨hs.1.2.1.1.1, hs.1.1.st⟩, hs.2.1⟩)
    (fun σ s m ⟨_, _, r3, _⟩ fr hr ⟨⟨hc', hk', hb'⟩, _⟩ => ⟨hc', hk', hb', by
      rw [hr, r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (mlV_lt h g P σ hk'.1.1.k1024)]⟩)
    (fun σ s m ⟨⟨hc, hk, hb⟩, r1, r3, r2⟩ fr => ⟨⟨?_, ?_, ?_⟩, r1, r3, r2⟩) fun σ s hs => hs.2.2.2) ?_
  · exact hc.write (t := { s with mem := m }) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.ML, by simp, fun _ h => h⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ml_slot hk.1.1 (by decide)) rfl rfl rfl
  · exact hk.keep h g fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨ml_slot hk.1.1 (by decide), ml_slot hk.1.1 (by decide), ml_slot hk.1.1 (by decide)⟩
  · intro i hi
    rw [← hb i hi]
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact out_ml hk.1.1 _ (contains_byte (Region.contains_self _ _) (out_wbuf hk.1.1).fit hi)
  -- The result.
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, hk, hb, hml⟩ => ?_
  have hi := hk.1.1
  have hg := hi.geo
  have hfit := hk.1.2.1
  have hK := hi.k1024
  refine fault_wp hc hi hk.1.2.2.1 fun t m rd wr sp _ r0 => ?_
  have hw : WP isa (.block [ld .r1 sOk, .dp .and .r1 .r1 (.imm 1), .dp .orr .r0 .r0 (.reg .r1)]) t fun u =>
      u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      u.gpr .r0 = faultV (rV P σ) ||| (okW h g P σ &&& 1) := by
    prun [ld, sp, rd, wr, hc.st.sp, hc.aFr hg, hc.rFr hg, m, hk.2.2, r0, sOk_lt]
  refine WP.mono hw fun u ⟨mu, rdu, wru, spu, u0⟩ => ⟨⟨hi, hc.st.regs (rdu.trans rd) (wru.trans wr)
    (spu.trans sp) (mu.trans m)⟩, ?_⟩
  rw [mu, m, u0, okW_one]
  have ec : (ctB P σ).length = P.nB.length := by rw [ctB_length, nB_length hi]
  have hfv : faultV (rV P σ) = if rV P σ = 2 then 2 else 0 := faultV_r (oc P σ)
  have htN : tN h P = P.K - (2 * h.H.D + 1) := rfl
  have ht : 0 < tN h P := by omega
  have hil := idx_lt h g (P := P) (σ := σ) ht
  rw [Res, Proof.RsaOaep.decrypt_eq ec, decOut_eq h g P σ hfit hk.1.2.2.2, hfv]
  have hz : ¬ okP h g P σ → Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K = Spec.RsaOaep.zeros P.K :=
    fun hn => Proof.RsaOaep.out_zero fun i hi' => by rw [← byteAt, hb i hi', ifn hn]
  have hm0 : ¬ okP h g P σ → s.mem.readW (State.addr P.ml) 64 = 0 := fun hn => by
    rw [hml, mlV, ifn hn]; rfl
  by_cases h1 : rV P σ = 1
  · have h2 : ¬ rV P σ = 2 := by rw [h1]; decide
    rw [ifp h1, ifn h2]
    by_cases ha : allOk h g P σ
    · have hc : okP h g P σ := ⟨h1, ha⟩
      rw [ifp ha, ifp hc]
      refine ⟨by decide, ?_, ?_⟩
      · refine Proof.RsaOaep.out_list (T := sL (tN h P) (T h g P σ)) (idx := idx h g P σ)
          (by rw [sL_length]; omega) (by rw [sL_length]; exact hil) fun i hi' => ?_
        rw [← byteAt, hb i hi', ifp hc, Bp_getD]
      · rw [hml, mlV, ifp hc, List.length_drop, sL_length]
        congr 1; show P.K - (2 * h.H.D + 2) - idx h g P σ = P.K - (2 * h.H.D + 1) - (idx h g P σ + 1); omega
    · have hn : ¬ okP h g P σ := fun e => ha e.2
      rw [ifn ha, ifn hn]
      exact ⟨by decide, hz hn, hm0 hn⟩
  · have hn : ¬ okP h g P σ := fun e => h1 e.1
    rw [ifn h1, ifn hn]
    by_cases h2 : rV P σ = 2
    · rw [ifp h2, ifp h2]; exact ⟨by decide, hz hn, hm0 hn⟩
    · rw [ifn h2, ifn h2]; exact ⟨by decide, hz hn, hm0 hn⟩

end VG.Proof.RsaOaep.Arm.Dec
