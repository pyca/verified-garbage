import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEntry
import VerifiedGarbage.Proof.RsaOaep.Encode

/-!
# RSAES-OAEP encryption on AArch64: `EM`

`encEm` (`encEm_ok`): `EM` before masking, `0x00 ‖ seed ‖ lHash ‖ 0…0 ‖ 0x01
‖ M`, in our working space (`EmAt`), from the seed, the label and the
message as on entry.
-/

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

theorem nil_ws {L : ELay} : ∀ r ∈ ([] : List Region), Region.Sub r L.OUT :=
  fun _ h => absurd h List.not_mem_nil

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

variable {Hl : Hash} (hH : StreamOK Hl.stream)

include hH in
theorem encEm_ok {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) {L : ELay} (hL : L.Ok)
    (hP : 16 ≤ L.P) (hD : L.D = Hl.D) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W)
    (hS : Slots L W) (hk : 2 * Hl.D + 2 + L.ml.toNat ≤ L.k.toNat) :
    WP isa (encEm Hl) t fun t' => Ctx L g vv m₀ t' ∧ ∃ V', Rep t'.mem L.Q L.scr V' W ∧
      EmAt V' L.k.toNat Hl.D (Spec.Rsa.bytesAt m₀ L.sd Hl.D)
        (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)) (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) L.ml.toNat := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have hk1024 := hL.k1024
  have c0 : oEm = 0 := rfl
  have cR : oRsa = 8192 := rfl
  have hk3 : W 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm3 : W 28 = BitVec.ofNat 64 L.ml.toNat := by rw [hS.ml, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- The seed's and the message's bytes are apart from our working space.
  have hsdS : ∀ i < Hl.D, ∀ j < oRsa, off L.sd i ≠ off L.scr j := fun i hi j hj
      (h' : L.sd + BitVec.ofNat 64 i = L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_SD L)) _ (hL.ours_scr _ (Offset.contains_base L.scr (d := j) (n := 1) (by omega) (by omega)))
      (h' ▸ Offset.contains_base L.sd (d := i) (n := 1) (k := L.D) (by omega)
        (by have := hL.bR _ (ro_SD L); simp only at this; omega))
  have hmsS : ∀ i < L.ml.toNat, ∀ j < oRsa, off L.msg i ≠ off L.scr j := fun i hi j hj
      (h' : L.msg + BitVec.ofNat 64 i = L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_MSG L)) _ (hL.ours_scr _ (Offset.contains_base L.scr (d := j) (n := 1) (by omega) (by omega)))
      (h' ▸ Offset.contains_base L.msg (d := i) (n := 1) (k := L.ml.toNat) (by omega)
        (by have := hL.bR _ (ro_MSG L); simp only at this; omega))
  have inRd : ∀ {u : State} {R : Region}, Ctx L g vv m₀ u → R ∈ [L.N, L.E, L.LAB, L.MSG, L.SD, L.ARGS] →
      ∀ {a : Addr} {n : Nat}, R.Contains a n → InRegions (u.rd ++ u.wr) a n := fun hcu hR _ _ h3 =>
    ⟨_, List.mem_append_left _ (by rw [hcu.rd]; exact hR), h3⟩
  unfold encEm seqs seqs seqs seqs
  -- `EM`'s place cleared.
  refine WP.seq (WP.mono (clearEm_ok (hc.lay hL hP R hS.scr) R) fun t1 ⟨_, S1, R1⟩ => ?_)
  have hc1 := hc.step hL hP S1 nil_ws
  -- The seed.
  refine WP.seq (WP.mono (copySeed_ok (hc1.lay hL hP R1 hS.scr) R1 (H := Hl) hS.sd hD0 hD64
    (fun i hi => inRd hc1 (by simp) (Offset.contains_base L.sd (d := i) (n := 1) (k := L.D) (by omega)
      (by have := hL.bR _ (ro_SD L); simp only at this; omega)))
    (fun i hi j hj => hsdS i hi _ (by unfold oEm; omega))) fun t2 ⟨_, S2, R2⟩ => ?_)
  have hc2 := hc1.step hL hP S2 nil_ws
  -- The label's hash.
  refine WP.seq (WP.mono (hashLabel_ok hH (Hs := Hs) hHh (hc2.lay hL hP R2 hS.scr) R2 (hc2.labAt hL hP hS)
    (o := oDig) (.inl rfl)) fun t3 ⟨_, S3, V3, R3, hV3, hV3'⟩ => ?_)
  have hc3 := hc2.step hL hP S3 nil_ws
  have hlab := hc2.bytes_ro hL (ro_LAB L)
  simp only at hlab
  rw [hlab] at hV3'
  -- `lHash` after the seed.
  refine WP.seq (WP.mono (copyLh_ok (hc3.lay hL hP R3 hS.scr) R3 (H := Hl) hD0 hD64) fun t4 ⟨_, S4, R4⟩ => ?_)
  have hc4 := hc3.step hL hP S4 nil_ws
  -- `0x01` and the message.
  refine WP.mono (putMsg_ok (hc4.lay hL hP R4 hS.scr) R4 hk3 hm3 hS.msg (by omega) hk1024
    (fun i hi => inRd hc4 (by simp) (Offset.contains_base L.msg (d := i) (n := 1) (k := L.ml.toNat) (by omega)
      (by have := hL.bR _ (ro_MSG L); simp only at this; omega)))
    hmsS) fun t5 ⟨_, S5, R5⟩ => ⟨hc4.step hL hP S5 nil_ws, _, R5, ?_⟩
  have nl : ∀ x, x < oSt → ¬ inR (labR oDig) x := fun x hx => by
    simp only [labR, inR_cons, inR_nil, or_false]; unfold oSt oDig oW at *; omega
  have bsd : ∀ i < Hl.D, t1.mem (off L.sd i) = (Spec.Rsa.bytesAt m₀ L.sd Hl.D).getD i 0 := fun i hi => by
    rw [bytesAt_getD _ _ hi]
    exact hc1.byte_ro hL (ro_SD L) (by simp only; omega)
  have bms : ∀ i < L.ml.toNat, t4.mem (off L.msg i) = (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat).getD i 0 :=
    fun i hi => by
      rw [bytesAt_getD _ _ hi]
      exact hc4.byte_ro hL (ro_MSG L) (by simp only; omega)
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · simp only [cpV, upd]
    rw [ifn (by omega), ifn (by omega), ifn (by unfold oEm; omega), hV3 _ (nl _ (by unfold oSt; omega))]
    simp only [cpV, zV]
    rw [ifn (by unfold oEm; omega), ifp (by unfold oEm; omega)]
  · simp only [cpV, upd]
    rw [ifn (by omega), ifn (by omega), ifn (by unfold oEm; omega), hV3 _ (nl _ (by unfold oSt; omega))]
    simp only [cpV]
    rw [ifp (by unfold oEm; omega), show 1 + i - (oEm + 1) = i by unfold oEm; omega, bsd i hi]
  · simp only [cpV, upd]
    rw [ifn (by omega), ifn (by omega), ifp (by unfold oEm; omega),
      show 1 + Hl.D + i - (oEm + 1 + Hl.D) = i by unfold oEm; omega, hV3' i hi]
  · simp only [cpV, upd]
    rw [ifn (by omega), ifn (by omega), ifn (by unfold oEm; omega), hV3 _ (nl _ (by unfold oSt; omega))]
    simp only [cpV, zV]
    rw [ifn (by unfold oEm; omega), ifp (by unfold oEm; omega)]
  · simp only [cpV, upd]
    rw [ifn (by omega)]; rfl
  · simp only [cpV]
    rw [ifp (by omega), show L.k.toNat - L.ml.toNat + i - (L.k.toNat - L.ml.toNat) = i by omega, bms i hi]

end VG.Proof.RsaOaep.AArch64.Enc
