import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc

/-! Copying the requested salt directly, with no secret-dependent offset. -/
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {H : Hash} (hH : HashOK H)

include hH in
theorem copyFixedSalt_ok {u : State} {F S : Addr} (L : Lay u F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {e db sl : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hsl : W 36 = BitVec.ofNat 64 sl) (hfit : sl < db) (heEnd : e + db ≤ oY)
    (hlen : 8 + H.D + sl ≤ 2048) (hcx : u.gpr .rcx = off S oY) :
    WP isa (copyFixedSalt H) u fun u' =>
      Lay u' F S ∧ Keep [.rsi, .r10, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV V (fun i => u.mem (off S (e + db - sl + i))) (oY + (8 + H.D)) sl) W := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (WP.mono (WP.keep [.rsi, .r10, .r8, .rax] (Q := fun v =>
    v.gpr .rsi = off S (e + db - sl) ∧ v.gpr .r10 = BitVec.ofNat 64 sl ∧
    v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.zf = some (decide (sl = 0)) ∧ v.mem = u.mem)
    ?_ rfl) fun v ⟨⟨h₁, h₁₀, h₂, hz, hm⟩, hk⟩ => ?_)
  · have ea : off S e + BitVec.ofNat 64 db - BitVec.ofNat 64 sl = off S (e + db - sl) := by
      rw [off_plus, off_sub S (by omega)]
    xrun [copyFixedSalt, ea_sp, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide),
      L.ld (d := sSlen) (by decide), R.rd (d := sEb) 23 rfl (by decide),
      R.rd (d := sDb) 24 rfl (by decide), R.rd (d := sSlen) 36 rfl (by decide), he, hdb, hsl, ea]
    rw [BitVec.and_self, ofNat_beq_zero (by omega)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    subst sl
    exact WP.block_nil ⟨Lv, hk.mono (by decide), by rw [cpV_zero, hm]; exact R⟩
  · rw [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok Lv (hm ▸ R) (d := .rcx) (by decide)
      (p := off S (e + db - sl)) (o := oY) (disp := 8 + H.D) (n := sl)
      (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₁₀)
      (by omega) (by unfold oY oRsa; omega) h₁ ((hk.gpr (by decide)).trans hcx) h₂ ?_ ?_)
      fun w ⟨Lw, kw, Rw⟩ => ?_
    · intro i hi
      rw [off_plus]
      exact Lv.sld8 (by unfold oY at heEnd; unfold oRsa; omega)
    · intro i hi j hj
      rw [off_plus]
      exact Offset.add_ofNat_ne S (by unfold oY at heEnd; omega)
        (by unfold oY; omega) (by omega)
    · refine ⟨Lw, (hk.trans kw).mono (by decide), ?_⟩
      simpa only [hm, off_off] using Rw

end VG.Proof.RsaPss.X86_64
