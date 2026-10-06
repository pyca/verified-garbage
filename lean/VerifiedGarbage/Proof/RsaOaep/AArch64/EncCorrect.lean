import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall

/-!
# RSAES-OAEP encryption on AArch64: correctness

After the checks (`encMain_ok`): `EM` written, `DB` masked with MGF1 of the
seed and the seed with MGF1 of the masked `DB`, then `vg_rsa_public_checked`
of it into `out`. The frames, the prologue and the checks of `k` and the
message's length, with zeros to `out` if either fails: `enc_ok`, against the
shared contract.
-/

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Enc.AArch64 (PubImpl)

variable {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

include hH hG in
theorem encMain_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (pv : PubImpl) {L : ELay} (hL : L.Ok) (hP : pv.S + 1 ≤ L.P) (hP16 : 16 ≤ L.P)
    (hD : L.D = Hl.D) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W)
    (hk : 2 * Hl.D + 2 + L.ml.toNat ≤ L.k.toNat) :
    WP isa (encMain Hl Gm pv.name pv.code) t fun t' => Ctx L g vv m₀ t' ∧
      Spec.Rsa.written t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
          (emOf Gs Hl.D L.k.toNat L.ml.toNat (Spec.Rsa.bytesAt m₀ L.sd Hl.D)
            (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)) (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat))) := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have hk1024 := hL.k1024
  have cSt : oSt = 3072 := rfl
  have cR : oRsa = 8192 := rfl
  have hk3 : W 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have f4 : MFit 1 Hl.D (1 + Hl.D) (L.k.toNat - Hl.D - 1) :=
    ⟨by rw [cSt]; omega, by rw [cSt]; omega, by omega, by omega, by omega⟩
  have f2 : MFit (1 + Hl.D) (L.k.toNat - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega, by rw [cSt]; omega, by omega, by omega, by omega⟩
  unfold encMain seqs seqs seqs seqs seqs seqs
  -- `EM` before masking.
  refine WP.seq (WP.mono (encEm_ok hH hHh hL hP16 hD hc R hS hk) fun t5 ⟨hc5, V5, R5, E⟩ => ?_)
  -- `DB` masked.
  refine WP.seq (WP.mono (dbArgs_ok (hc5.lay hL hP16 R5 hS.scr) R5 hk3 (by omega) (by omega) hk1024 [])
    fun t6 ⟨_, S6, R6⟩ => ?_)
  have hc6 := hc5.step hL hP16 S6 nil_ws
  have hS6 : Slots L (mW W L.scr 1 Hl.D (1 + Hl.D) (L.k.toNat - Hl.D - 1)) :=
    hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega)
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv (hc6.lay hL hP16 R6 hS6.scr) R6 f4 (mW_args _ _ _ _ _ _))
    fun t7 ⟨_, S7, V7, W7, R7, hW7, hV7⟩ => ?_)
  have hc7 := hc6.step hL hP16 S7 nil_ws
  have hS7 : Slots L W7 := hS6.of fun j _ h2 h3 => hW7 j (by unfold nW frameBytes; omega) (by omega) (by omega)
  -- The seed masked.
  refine WP.seq (WP.mono (seedArgs_ok (hc7.lay hL hP16 R7 hS7.scr) R7 (by rw [hS7.k, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]) (by omega) (by omega) hk1024 []) fun t8 ⟨_, S8, R8⟩ => ?_)
  have hc8 := hc7.step hL hP16 S8 nil_ws
  have hS8 : Slots L (mW W7 L.scr (1 + Hl.D) (L.k.toNat - Hl.D - 1) 1 Hl.D) :=
    hS7.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega)
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv (hc8.lay hL hP16 R8 hS8.scr) R8 f2 (mW_args _ _ _ _ _ _))
    fun t9 ⟨_, S9, V9, W9, R9, hW9, hV9⟩ => ?_)
  have hc9 := hc8.step hL hP16 S9 nil_ws
  have hS9 : Slots L W9 := hS8.of fun j _ h2 h3 => hW9 j (by unfold nW frameBytes; omega) (by omega) (by omega)
  -- The call.
  refine WP.seq ?_
  rw [pubArgs_eq, WP.block_append_iff]
  refine WP.mono (pubW_ok hL hP16 hc9 R9 hS9) fun t10 ⟨hc10, R10⟩ => ?_
  have hS10 : Slots L (pubW L W9) := hS9.of fun j h1 _ _ => by
    simp only [pubW, upd]; rw [ifn (by omega), ifn (by omega)]
  refine WP.mono (pubR_ok hL hP16 hc10 R10 hS10) fun t11 ⟨hc11, hm11, hr11⟩ => ?_
  have R11 : Rep t11.mem L.Q L.scr V9 (pubW L W9) := hm11 ▸ R10
  refine WP.mono (pub_call pv hL hP hP16 hc11 hr11 R11 ⟨by simp [pubW, upd], by simp [pubW, upd]⟩)
    fun t12 ⟨hc12, hout⟩ => ⟨hc12, ?_⟩
  -- `EM` masked.
  have hlhl : (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)).length = Hl.D := by rw [hHv.2, hHl]
  have hml : (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat).length = L.ml.toNat := by simp [Spec.Rsa.bytesAt]
  have hsdl : (Spec.Rsa.bytesAt m₀ L.sd Hl.D).length = Hl.D := by simp [Spec.Rsa.bytesAt]
  have e1 : L.k.toNat - (Hl.D + 1) = L.k.toNat - Hl.D - 1 := by omega
  have hm : ∀ o, o < L.k.toNat → mOut o := fun o ho => (mOut_iff o).mpr (.inl (by unfold oSt; omega))
  have hsrc : srcB V7 (1 + Hl.D) (L.k.toNat - Hl.D - 1) =
      srcB (mixV V5 (Spec.Mgf1.mgf1 Gs (srcB V5 1 Hl.D) (L.k.toNat - Hl.D - 1)) (1 + Hl.D)
        (L.k.toNat - Hl.D - 1)) (1 + Hl.D) (L.k.toNat - Hl.D - 1) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      exact hV7 _ (by unfold oRsa; omega) (hm _ (by omega))
  have hlist : Spec.Rsa.bytesAt t11.mem (L.scr + BitVec.ofNat 64 0) L.k.toNat =
      emOf Gs Hl.D L.k.toNat L.ml.toNat (Spec.Rsa.bytesAt m₀ L.sd Hl.D)
        (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)) (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) := by
    unfold emOf
    rw [← em_mask hGv (V₁ := V5) (by omega) hsdl (by
        simp only [List.length_append, List.length_cons, hlhl, hml, Spec.RsaOaep.zeros, List.length_replicate]; omega)
      E.z0 E.sd (E.db hlhl hml hk)]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [BitVec.add_zero, show L.scr + BitVec.ofNat 64 i = off L.scr i from rfl, R11.scr i (by omega),
      hV9 _ (by omega) (hm _ hi'), hsrc]
    exact mixV_congr _ _ _ (hV7 _ (by omega) (hm _ hi'))
  rw [hlist] at hout
  exact hout

end VG.Proof.RsaOaep.AArch64.Enc
