module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SEmBytes
public import VerifiedGarbage.Proof.RsaPss.X86_64.Goods
public import VerifiedGarbage.Proof.RsaPss.X86_64.Hashing
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the encoding

After the checks, `signEnc` leaves `EM` (`k` bytes, `emT`) at
`scratch + oEm` (`signEnc_ok`): `DB`'s slots, `EM` cleared, the prefix
`0⁸ ‖ mHash`, `H = Hash(0⁸ ‖ mHash ‖ salt)` (the salt hashed where it is),
`0x01` and the salt, `H` and `0xbc`, MGF1's mask and the top bits.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr oEm oSt oDig oW oRsa lay clearEm)
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.RsaOaep.X86_64 (decStack stkD fb frR frame_subD ret_subD Lay Rep upd nW inR inR_cons inR_nil
  StepW outR wp_good block_good keep_cs3 lenOf tw Here Fns FnsD mgfXor_ok MFit mW mW_args mW_other mOut mOut_iff
  cpV clrV stBytes clearEm_ok clearEm_good mgfXor_good sizes rdIn_entry fnW selW)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.MlKem.X86_64 (Keep ifp ifn)
open VG.Proof.HashFns (StreamingOK)

variable {s : State}

theorem scW_w (s : State) :
    scW s 14 = stackArg s 14 ∧ scW s 21 = s.gpr .rdi ∧ scW s 22 = s.gpr .rdx ∧ scW s 23 = s.gpr .rcx ∧
      scW s 24 = s.gpr .r8 ∧ scW s 25 = s.gpr .r9 ∧ scW s 26 = stackArg s 15 ∧ scW s 27 = stackArg s 10 ∧
      scW s 28 = stackArg s 12 ∧ scW s 29 = stackArg s 13 ∧ scW s 30 = maskV (sn0v s) ∧
      scW s 31 = BitVec.ofNat 64 (loV (sn0v s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [scW, signW, fnW, selW, signPW, upd]

theorem scW_sel (s : State) :
    scW s 39 = BitVec.ofNat 64 (lenOf (sselH s)) ∧ scW s 43 = BitVec.ofNat 64 (lenOf (sselG s)) ∧
    (scW s 45 = tw s.mem (stabH s) 0 ∧ scW s 46 = tw s.mem (stabH s) 1 ∧ scW s 47 = tw s.mem (stabH s) 2) ∧
    (scW s 48 = tw s.mem (stabG s) 0 ∧ scW s 49 = tw s.mem (stabG s) 1 ∧ scW s 50 = tw s.mem (stabG s) 2) := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [scW, signW, fnW, selW, upd]

/-- The slots `privArgs` reads. -/
def sKs : List Nat := [14, 21, 22, 23, 24, 25, 26]

/-- After the encoding: in the frame, the slots `privArgs` reads, and `EM`. -/
def SEnc (H G : Spec.Mgf1.Hash) (s t : State) : Prop :=
  SEnv s t ∧ Lay t (fb s) (stackArg s 14) ∧ ∃ V W, Rep t.mem (fb s) (stackArg s 14) V W ∧
    (∀ k ∈ sKs, W k = scW s k) ∧
    ∀ i < sk s, V (oEm + i) = RsaPss.emT (loV (sn0v s)) (sk s - loV (sn0v s) - H.len - 1) (ssl s)
      (Spec.Rsa.bytesAt s.mem (stackArg s 12) (ssl s))
      (H.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (stackArg s 10) H.len ++
        Spec.Rsa.bytesAt s.mem (stackArg s 12) (ssl s)))
      (Spec.Mgf1.mgf1 G (H.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (stackArg s 10) H.len ++
        Spec.Rsa.bytesAt s.mem (stackArg s 12) (ssl s))) (sk s - loV (sn0v s) - H.len - 1))
      ((maskV (sn0v s)).setWidth 8) i

/-- An input apart from what the function writes keeps its bytes. -/
theorem SEnv.byte {t : State} (he : SEnv s t) {r : Region} (hK : (stkD s).Disjoint r) (hO : (outR s).Disjoint r)
    (hS : r.Disjoint (sscrR s)) {x : Addr} (hx : r.Contains x 1) : t.mem x = s.mem x :=
  he.fr x fun r' hr' hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact hK x hc hx
    · exact hO x hc hx
    · exact hS x hx hc

variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh)

include hTH hTG in
theorem signEnc_ok (hp : SPre s) (fH : FnsD s TH 18) (fG : FnsD s TG 19)
    (eH : Spec.HashId.mgf1 (sselH s) = some Hh) (eG : Spec.HashId.mgf1 (sselG s) = some Gh) {t : State}
    (he : SEnv s t) (L : Lay t (fb s) (stackArg s 14)) (R : Rep t.mem (fb s) (stackArg s 14) (sv0 s) (scW s))
    (hax : t.gpr .rax = BitVec.ofNat 64 (sk s - loV (sn0v s) - (lenOf (sselH s) + 2))) (hfit : SFit s) :
    WP isa signEnc t (SEnc Hh Gh s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hDH : TH.S.digestBytes = lenOf (sselH s) := VG.Proof.RsaOaep.X86_64.lenOf_eq hTH eH
  have hDG : TG.S.digestBytes = lenOf (sselG s) := VG.Proof.RsaOaep.X86_64.lenOf_eq hTG eG
  have hHl : Hh.len = lenOf (sselH s) := hTH.len.trans hDH
  obtain ⟨-, hzF, -, hzDF, hzD⟩ := sizes hTH
  have hlo := loV_le (sn0v s)
  have hsl := hp.hsl
  have hwS := hp.wS
  have hwD := hp.wD
  have hwSa := hp.wSa
  have hD64 : lenOf (sselH s) ≤ 64 := pssLensOK.le _ (mem_pssLens hp.iH)
  have hdlen : (stackArg s 11).toNat = lenOf (sselH s) := by rw [hp.dl Hh eH, hHl]
  obtain ⟨hn0, hfit⟩ := hfit
  have c1 : oEm = 0 := rfl
  have c2 : oSt = 3072 := rfl
  have c3 : oDig = 3328 := rfl
  have c4 : oMp = 3584 := rfl
  have c5 : oRsa = 8192 := rfl
  have c6 : oW = 4096 := rfl
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := scW_w s
  obtain ⟨w39, w43, wH, wG⟩ := scW_sel s
  unfold SEnc
  rw [hHl]
  generalize hD : lenOf (sselH s) = D at *
  generalize hlo' : loV (sn0v s) = lo at *
  generalize hk : sk s = k at *
  generalize hsl' : ssl s = sl at *
  have hk' : (s.gpr .rcx).toNat = k := hk
  have hsl'' : (stackArg s 13).toNat = sl := hsl'
  generalize hdb : k - lo - D - 1 = db
  have hdb' : k - lo - (D + 2) + 1 = db := by omega
  unfold signEnc seqs seqs seqs seqs seqs seqs seqs seqs
  -- `DB`'s slots.
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (dbSlots_ok L R w31 hax))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ => ?_)
  have he1 := he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1
  rw [hdb'] at R1
  set W1 := upd (upd (scW s) 44 (BitVec.ofNat 64 db)) 33 (off (stackArg s 14) (oEm + lo)) with hW1
  have x : ∀ j, j ≠ 33 → j ≠ 44 → W1 j = scW s j := fun j a b => by simp only [hW1, upd, ifn a, ifn b]
  have x33 : W1 33 = off (stackArg s 14) (oEm + lo) := by simp [hW1, upd]
  have x44 : W1 44 = BitVec.ofNat 64 db := by simp [hW1, upd]
  -- `EM` cleared.
  refine WP.seq (WP.mono (wp_good clearEm_good (clearEm_ok L1 R1)) fun t2 ⟨⟨L2, k2, R2⟩, sp2, mx2, f2⟩ => ?_)
  have he2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  -- The prefix.
  have dgc : ∀ i < D, (sdgR s).Contains (stackArg s 10 + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by rw [hdlen]; omega) (by omega)
  have scc : ∀ o < 1024 + 4096, (sscrR s).Contains (off (stackArg s 14) o) 1 := fun o ho =>
    Offset.contains_base _ (by omega) (by omega)
  refine WP.seq (WP.mono (wp_good mPrefix_good (mPrefix_ok L2 R2 (p := stackArg s 10)
      ((x 27 (by decide) (by decide)).trans w27) ((x 39 (by decide) (by decide)).trans w39) (by omega) hD64
      (fun i hi => by
        rw [he2.rd, hp.hrd]
        exact ⟨sdgR s, List.mem_append_left _ (by simp [srd]), dgc i hi⟩)
      (fun i hi j hj => VG.Proof.RsaOaep.X86_64.ne_of_disjoint hp.dds (dgc i hi) (scc _ (by omega)))))
    fun t3 ⟨⟨L3, k3, R3⟩, sp3, mx3, f3⟩ => ?_)
  have he3 := he2.step k3.2.1 k3.2.2 sp3 (keep_cs3 k3 (by decide)) mx3 f3
  have hdg : (List.range D).map (fun i => t2.mem (stackArg s 10 + BitVec.ofNat 64 i)) =
      Spec.Rsa.bytesAt s.mem (stackArg s 10) D :=
    List.map_congr_left fun i hi => he2.byte hp.dKd hp.dOd hp.dds (dgc i (List.mem_range.mp hi))
  -- `H`.
  have sac : ∀ i < sl, (ssaR s).Contains (stackArg s 12 + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  have A : VG.Proof.RsaPss.X86_64.SaltAt t3 (fb s) (stackArg s 14) W1 (stackArg s 12) sl :=
    ⟨(x 28 (by decide) (by decide)).trans w28,
      by rw [x 29 (by decide) (by decide), w29, ← hsl'', BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [← hsl'']; exact (stackArg s 13).isLt,
      VG.Covers.left (VG.Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr, he3.rd, hp.hrd, ← hsl'']; simp [srd]),
      by rw [← hsl'']; exact hp.dsas.sub_right (Region.sub_prefix (by unfold oRsa; omega)),
      by rw [← hsl'']; exact hp.dKsa.sub_left (ret_subD s)⟩
  have hsW : ∀ y, (⟨stackArg s 12, sl⟩ : Region).Contains y 1 →
      ∀ r ∈ s.wr ++ abi.reserved decStack s, ¬ r.Contains y 1 := fun y hy r hr hc => by
    rw [← hsl''] at hy
    rw [show abi.reserved decStack s = [⟨s.gpr .rsp, 8⟩, stkS s] from rfl, hp.hwr] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.dOsa y hc hy
    · exact hp.dsas y hy hc
    · exact hp.dRsa y hc hy
    · exact hp.dKsa y hc hy
  refine WP.seq (WP.mono (wp_good hashM_good (hashM_ok hTH fH (Hs := Hh) (fun y => by rw [hTH.hash]) he3.here
      L3 R3 ((x 39 (by decide) (by decide)).trans w39) hD64
      ⟨(x 45 (by decide) (by decide)).trans wH.1, (x 46 (by decide) (by decide)).trans wH.2.1,
        (x 47 (by decide) (by decide)).trans wH.2.2⟩ A (by omega) (by omega)
      (rdIn_entry (r := ⟨stackArg s 12, sl⟩) (by rw [hp.hrd, ← hsl'']; simp [srd])) hsW))
    fun t4 ⟨⟨L4, hh4, rd4, wr4, cs4, V4, R4, hV4, hd4⟩, sp4, mx4, f4⟩ => ?_)
  have he4 := he3.step rd4 wr4 sp4 (fun r hr _ => cs4 r hr) mx4 f4
  -- `0x01` and the salt.
  refine WP.seq (WP.mono (wp_good putSalt_good (putSalt_ok L4 R4 (e := oEm + lo) (db := db) x33 x44
      ((x 28 (by decide) (by decide)).trans w28)
      (by rw [x 29 (by decide) (by decide), w29, ← hsl'', BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega) (by omega)
      (fun i hi => by rw [he4.rd, hp.hrd]; exact ⟨ssaR s, List.mem_append_left _ (by simp [srd]), sac i hi⟩)
      (fun i hi j hj => VG.Proof.RsaOaep.X86_64.ne_of_disjoint hp.dsas (sac i hi) (scc _ (by omega)))))
    fun t5 ⟨⟨L5, k5, R5⟩, sp5, mx5, f5⟩ => ?_)
  have he5 := he4.step k5.2.1 k5.2.2 sp5 (keep_cs3 k5 (by decide)) mx5 f5
  -- `H` and `0xbc`.
  refine WP.seq (WP.mono (wp_good putH_good (putH_ok L5 R5 (k := k) x33 x44
      (by rw [x 23 (by decide) (by decide), w23, ← hk', BitVec.ofNat_toNat, BitVec.setWidth_eq])
      ((x 39 (by decide) (by decide)).trans w39) (by omega) hD64 (by omega) (by omega)))
    fun t6 ⟨⟨L6, k6, R6⟩, sp6, mx6, f6⟩ => ?_)
  have he6 := he5.step k6.2.1 k6.2.2 sp6 (keep_cs3 k6 (by decide)) mx6 f6
  -- MGF1.
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (mgfArgs_ok L6 R6 x33 x44
      ((x 39 (by decide) (by decide)).trans w39)))
    fun t7 ⟨⟨L7, k7, R7⟩, sp7, mx7, f7⟩ => ?_)
  have he7 := he6.step k7.2.1 k7.2.2 sp7 (keep_cs3 k7 (by decide)) mx7 f7
  have y : ∀ j, (j < 15 ∨ 18 < j) → mW W1 (stackArg s 14) (oEm + lo + db) D (oEm + lo) db j = W1 j :=
    fun j hj => mW_other hj
  refine WP.seq (WP.mono (wp_good mgfXor_good (mgfXor_ok hTG fG (Gs := Gh) (fun y => by rw [hTG.hash]) hTG.len
      hTG.valid he7.here L7 R7 ⟨by omega, by omega, .inr (Nat.le_refl _), by omega, by omega⟩ (mW_args _ _ _ _ _ _)
      ⟨by rw [y 48 (by decide), x 48 (by decide) (by decide)]; exact wG.1,
        by rw [y 49 (by decide), x 49 (by decide) (by decide)]; exact wG.2.1,
        by rw [y 50 (by decide), x 50 (by decide) (by decide)]; exact wG.2.2⟩
      (by rw [y 43 (by decide), x 43 (by decide) (by decide), w43, hDG])))
    fun t8 ⟨⟨L8, _, rd8, wr8, cs8, V8, W3, R8, hW3, hV8⟩, sp8, mx8, f8⟩ => ?_)
  have he8 := he7.step rd8 wr8 sp8 (fun r hr _ => cs8 r hr) mx8 f8
  have z : ∀ j, j < nW → (j < 15 ∨ 18 < j) → j ≠ 19 → j ≠ 20 → j ≠ 33 → j ≠ 44 → W3 j = scW s j :=
    fun j hj h1 h2 h3 h4 h5 => (hW3 j hj h2 h3).trans ((y j h1).trans (x j h4 h5))
  -- The top bits.
  have hc8 := maskV_byte (show sn0v s < 256 from (s.mem (s.gpr .rdx)).isLt)
  refine WP.mono (wp_good (block_good _ rfl rfl) (clearTop_ok L8 R8 (e := oEm + lo)
      (c := (maskV (sn0v s)).setWidth 8)
      ((hW3 33 (by decide) (by decide) (by decide)).trans ((y 33 (by decide)).trans x33))
      (by rw [z 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w30]; exact hc8)
      (by omega)))
    fun t9 ⟨⟨L9, k9, R9⟩, sp9, mx9, f9⟩ => ?_
  refine ⟨he8.step k9.2.1 k9.2.2 sp9 (keep_cs3 k9 (by decide)) mx9 f9, L9, _, W3, R9, fun j hj => ?_,
    em_bytes (V₃ := V4) (sf := fun i => t4.mem (stackArg s 12 + BitVec.ofNat 64 i)) ?_ ?_ ?_ ?_ (by omega) hlo
      (by omega) (by omega) hV8⟩
  · simp only [sKs, List.mem_cons, List.not_mem_nil, or_false] at hj
    exact z j (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · intro i hi
    rw [hV4 _ (by simp only [mR, inR_cons, inR_nil, or_false]; omega)]
    simp only [mpV, stBytes, cpV, clrV]
    rw [ifn (by omega), ifn (by omega), ifp ⟨by omega, by omega⟩]
  · intro j hj
    rw [hd4 j (by rw [hDH]; exact hj), VG.Proof.RsaPss.X86_64.mpV_bytes, hdg]
  · exact (hTH.valid.2 _).trans hHl
  · intro j hj
    rw [he4.byte hp.dKsa hp.dOsa hp.dsas (sac j hj), Spec.Rsa.bytesAt]
    exact VG.Proof.RsaOaep.map_range_getD (f := fun i => s.mem (stackArg s 12 + BitVec.ofNat 64 i)) rfl hj

end VG.Proof.RsaPss.X86_64
