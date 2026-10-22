module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Out
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Spec
import VerifiedGarbage.Proof.RsaOaep.X86.Instr
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on x86: `*msg_len` and the result

As on ARMv7 (`Proof/RsaOaep/Arm/DecEnd.lean`): the message's length ANDed
with `ok` to `*msg_len` as a 64-bit word, and the result
`(ok ∧ 1) ∨ ((r = 2) ? 2 : 0)` (`end_vp`): what `decrypt` says
(`Proof.RsaOaep.decrypt_eq`, `decOut_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi sPos)
open VG.Proof.Mont.X86 (wp_storeS)
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

theorem faultV_r (o : Spec.Rsa.Outcome) : faultV (rOf o) = if rOf o = 2 then 2 else 0 := by
  rw [faultV_rOf]; cases o <;> simp [rOf]

theorem Bp_getD (P : EP) (σ : State) (j : Nat) : Bp h g P σ j = (sL (tN h P) (T h g P σ)).getD j 0 := by
  unfold Bp
  by_cases e : j < tN h P
  · rw [ifp e, sL_getD e]
  · rw [ifn e, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [sL_length]; omega)]; rfl

theorem mlV_lt (P : EP) (σ : State) (hK : P.K ≤ 1024) : mlV h g P σ < 2 ^ 32 := by
  unfold mlV; split <;> omega

/-- `msg_len` in `esi`, the length in `eax`. -/
abbrev O4 (P : EP) (σ s : State) : Prop :=
  O3 h g P σ s ∧ s.gpr .esi = P.ml ∧ s.gpr .eax = BitVec.ofNat 32 (mlV h g P σ)

/-- After `*msg_len`. -/
abbrev O5 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧
    (∀ i < P.K, s.mem (byteAt P.out i) = if okP h g P σ then Bp h g P σ (i + aV h g P σ) else 0) ∧
    s.mem.readW (P.ml.setWidth 64) 64 = BitVec.ofNat 64 (mlV h g P σ)

theorem mlHead_vp (P : EP) : VP (O3 h g P) (.block ((mlSet h.H).take 5)) (O4 h g P) := by
  refine VP.taint [.esp] h.certs.mlHead (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.st.sp, h₂.1.st.sp])
    fun σ s ⟨hc, hk, hb⟩ => ?_
  have hi := hk.1.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hD := h.D_le
  have hK := hi.k1024
  have hfit := hk.1.2.1
  simp only [mlSet, ld, Impl.RsaPkcs1Sig.X86.stk, List.take_succ_cons, List.take_zero]
  refine hc.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
    wp_subi fun t2 u2 _ _ => ?_
  have c2 := c1.upd u2 (by decide) (by decide)
  refine wp_subm (B := P.lay.B) (by rw [c2.st.sp]) (by rw [hg.aFr ok sPos (by decide)]; exact c2.rFr hg sPos (by decide))
    fun t3 u3 => ?_
  have c3 := c2.upd u3 (by decide) (by decide)
  refine wp_andm (B := P.lay.B) (by rw [c3.st.sp]) (by rw [hg.aFr ok sOk (by decide)]; exact c3.rFr hg sOk (by decide))
    fun t4 u4 => ?_
  have c4 := c3.upd u4 (by decide) (by decide)
  refine c4.wp_arg hg (dec_arg (j := 2) (by decide)) (by decide) (by decide) fun t5 c5 u5 => WP.block_nil ?_
  have m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨c5, m5 ▸ hk, m5 ▸ hb⟩, by rw [u5.gpr]; rfl, ?_⟩
  rw [u5.other _ (by decide), u4.gpr, u3.gpr, u2.gpr, u1.gpr, u3.mem, u2.mem, u1.mem,
    hg.aFr ok sPos (by decide), hg.aFr ok sOk (by decide), hk.2.1, hk.2.2]
  show BitVec.ofNat 32 P.K - _ - _ &&& _ = _
  exact mlV_eq h g (show 0 < tN h P by show 0 < P.K - (2 * h.H.D + 1); omega)

theorem mlRest_vp (P : EP) : VP (O4 h g P) (.block ((mlSet h.H).drop 5)) (O5 h g P) := by
  refine VP.taint [.esp, .esi] mlRest_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
      · rw [h₁.2.1, h₂.2.1]) fun σ s ⟨⟨hc, hk, hb⟩, si, ax⟩ => ?_
  have hi := hk.1.1
  have fit := ml_fit hi
  have hK := hi.k1024
  have win : ∀ d, d + 4 ≤ 8 → InRegions s.wr (P.ml.setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd =>
    ⟨P.ML, hc.st.inRw (by simp), Offset.contains_base _ hd (by omega)⟩
  simp only [mlSet, mi, List.drop_succ_cons, List.drop_zero]
  refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 0)
    (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si]; exact addr_eq (by omega)) (win 0 (by decide)) fun t1 m1 => ?_
  refine wp_movi fun t2 u2 => ?_
  refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 4)
    (by show t2.ea ⟨.esi, 4⟩ = _; rw [ea_at, u2.other _ (by decide), m1.gpr, si]; exact addr_eq (by omega))
    (by rw [u2.wr, m1.wr]; exact win 4 (by decide)) fun t3 m3 => WP.block_nil ?_
  have mm : t3.mem = (s.mem.writeW (P.ml.setWidth 64 + BitVec.ofNat 64 0) (BitVec.ofNat 32 (mlV h g P σ))).writeW
      (P.ml.setWidth 64 + BitVec.ofNat 64 4) (BitVec.ofNat 32 0) := by
    rw [m3.mem, u2.gpr, u2.mem, m1.mem, ax]
  have fr : Frame [P.ML] s.mem t3.mem := by
    rw [mm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine ⟨hc.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.ML, by simp, fun _ h => h⟩)
    (by rw [m3.rd, u2.rd, m1.rd]) (by rw [m3.wr, u2.wr, m1.wr])
    (by rw [m3.gpr, u2.other _ (by decide), m1.gpr]) (by rw [m3.gpr, u2.other _ (by decide), m1.gpr]),
    hk.keep h g fr fun r hr => ?_, fun i hi' => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ml_slot hi (by decide), ml_slot hi (by decide), ml_slot hi (by decide)⟩
  · rw [← hb i hi']
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact out_ml hi _ (contains_byte (Region.contains_self _ _) (out_wbuf hi).fit hi')
  · rw [mm, BitVec.add_zero]
    exact readW_pair s.mem (P.ml.setWidth 64) (mlV_lt h g P σ hK)

theorem end_vp (P : EP) : VP (O3 h g P) (.seq (.block (mlSet h.H)) (.block decRet)) (Fin h.G g.G P) := by
  have e : (mlSet h.H) = (mlSet h.H).take 5 ++ (mlSet h.H).drop 5 := (List.take_append_drop _ _).symm
  rw [e]
  refine VP.seq ((mlHead_vp h g P).block_append (mlRest_vp h g P)) ?_
  refine VP.taint [.esp, .ebp] decRet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, hb, hml⟩ => ?_
  have hi := hk.1.1
  have hg := hi.geo
  have hfit := hk.1.2.1
  have hK := hi.k1024
  refine fault_wp hc hi hk.1.2.2.1 fun t ct m r0 => ?_
  simp only [ld]
  refine ct.wp_slot hg (d := sOk) (by decide) (by decide) (by decide) fun t1 c1 u1 =>
    wp_andi fun t2 u2 => wp_or fun t3 u3 => WP.block_nil ?_
  have c3 := (c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
  refine ⟨⟨hi, c3.st⟩, ?_⟩
  have m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem, m]
  have v3 : t3.gpr .eax = faultV (rV P σ) ||| (okW h g P σ &&& 1) := by
    rw [u3.gpr, u2.gpr, u2.other _ (by decide), u1.gpr, u1.other _ (by decide), r0, m, hk.2.2]
  rw [m3, v3, okW_one]
  have ec : (ctB P σ).length = P.nB.length := by rw [ctB_length, nB_length hi]
  have hfv : faultV (rV P σ) = if rV P σ = 2 then 2 else 0 := faultV_r (oc P σ)
  have htN : tN h P = P.K - (2 * h.H.D + 1) := rfl
  have ht : 0 < tN h P := by omega
  have hil := idx_lt h g (P := P) (σ := σ) ht
  rw [Res, Proof.RsaOaep.decrypt_eq ec, decOut_eq h g P σ hfit hk.1.2.2.2, hfv]
  have hz : ¬ okP h g P σ → Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K = Spec.RsaOaep.zeros P.K :=
    fun hn => Proof.RsaOaep.out_zero fun i hi' => by rw [hb i hi', ifn hn]
  have hm0 : ¬ okP h g P σ → s.mem.readW (P.ml.setWidth 64) 64 = 0 := fun hn => by
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
        rw [hb i hi', ifp hc, Bp_getD]
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

end VG.Proof.RsaOaep.X86.Dec
