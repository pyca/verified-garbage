module
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic

import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp

/-! Copy the public number of salt bytes from the end of the decoded DB. -/

@[expose] public section
namespace VG.Proof.RsaPss.AArch64.FixedSalt
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.RsaPss.AArch64.FixedSalt
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_sub wp_addImm wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp)

theorem copySalt_ok {H : Hash} (hH : HashOK H) {t : State} {F S : Addr}
    (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {e db sl : Nat}
    (he : oEm ≤ e) (hfit : e + db ≤ oY) (hsl : sl ≤ db) (hdb : db < 1024)
    (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
    (hs : t.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 sl) :
    WP isa (copySalt H) t fun t' => Keep [.x11, .x12, .x14, .x15] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (updL V (oY + 8 + H.D)
        ((List.range sl).map fun i => V (e + db - sl + i))) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  unfold copySalt
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x11, .x12, .x14] t u ∧
      u.gpr .x11 = off S (e + db - sl) ∧
      u.gpr .x14 = off S (oY + 8 + H.D) ∧ u.gpr .x12 = BitVec.ofNat 64 sl) ?_
    fun u ⟨O, h11, h14, h12⟩ => ?_)
  · refine wp_add fun u₁ o₁ e₁ => wp_ldrSp (by decide)
      (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot L (by decide)) fun u₂ o₂ e₂ =>
      wp_sub fun u₃ o₃ e₃ => wp_addImm (by unfold oY; omega) fun u₄ o₄ e₄ => wp_nil ?_
    refine ⟨(o₁.trans (o₂.trans (o₃.trans o₄))).mono, ?_, ?_, ?_⟩
    · rw [o₄.get .x11, e₃, o₂.get .x11, e₁, h24, h25, off_add,
        e₂, o₁.sp, L.sp, o₁.mem, hs, off_sub _ (by omega)]
    · rw [e₄, o₃.get .x20, o₂.get .x20, o₁.get .x20, L.x20]
    · rw [o₄.get .x12, o₃.get .x12, e₂, o₁.sp, L.sp, o₁.mem, hs]
  refine WP.ite _ (eval_zero _ _) (fun h => ?_) (fun h => ?_)
  · rw [h12] at h
    have h0 : sl = 0 := by
      have : (BitVec.ofNat 64 sl).toNat = 0 := by rw [beq_iff_eq.mp h]; rfl
      rw [BitVec.toNat_ofNat] at this
      omega
    subst h0
    refine wp_nil ⟨O.keep.mono, O.mem ▸ Frame.refl _ _, ?_⟩
    simp only [List.range_zero, List.map_nil, updL_nil]
    exact O.mem ▸ R
  · rw [h12] at h
    have h0 : 0 < sl := by
      rcases Nat.eq_zero_or_pos sl with e | e
      · subst e; simp at h
      · exact e
    refine WP.mono (copyWithin_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R)
      h0 (by unfold oY oRsa at *; omega) (by unfold oY oRsa; omega)
      (Or.inl (by omega)) h14 h11 h12) fun v ⟨k, f, r⟩ =>
        ⟨(O.keep.trans k).mono, O.mem ▸ f, r⟩

end VG.Proof.RsaPss.AArch64.FixedSalt
