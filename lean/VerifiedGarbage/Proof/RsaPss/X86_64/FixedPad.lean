import VerifiedGarbage.Proof.RsaPss.X86_64.CtHash

/-! A fixed message length permits a single padding write. -/
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Bignum (off)

/-- The padding facts used by the remainder of the hash computation. -/
structure PadResult (t : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64)
    (ℓ N : Nat) (u : State) : Prop where
  L : Lay u F S
  keep : Keep [.rcx, .rdx, .r10, .r8, .rax, .r9] t u
  R : Rep u.mem F S (v80 V ℓ N) W

theorem fixed_or80 : ∀ b : Byte,
    (BitVec.setWidth 64 b ||| BitVec.signExtend 64 (128 : BitVec 32)).setWidth 8 = b ||| 0x80 := by
  decide

theorem fixedPad80_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {ℓ N : Nat} (hℓ : ℓ < N) (hN : N ≤ 2048) :
    WP isa (fixedPad80 ℓ) t (PadResult t F S V W ℓ N) := by
  unfold fixedPad80
  refine WP.seq (WP.mono (scr_ok L (d := .rcx) (by decide) (o := oY) (by decide))
    fun u ⟨hcx, hm, ku⟩ => ?_)
  have Lu := L.congr (ku.gpr (by decide)) ku.2.2 (by rw [hm])
  have Ru : Rep u.mem F S V W := hm ▸ R
  have hb : oY + ℓ < oRsa := by unfold oY oRsa; omega
  refine WP.mono (WP.keep [.rax] (Q := fun v =>
      v.mem = u.mem.writeW (off S (oY + ℓ)) (u.mem (off S (oY + ℓ)) ||| 0x80)) ?_ rfl)
    fun v ⟨hv, kv⟩ => ?_
  · xrun [ea_at, hcx, VG.Proof.Bignum.off_off, Lu.sld8 hb, Lu.sst8 hb, fixed_or80]
  · have Rv : Rep v.mem F S (v80 V ℓ N) W := by
      rw [hv]
      have rr := Ru.wb Lu.geo (o := oY + ℓ) hb (u.mem (off S (oY + ℓ)) ||| 0x80)
      refine (congrArg (fun V' => Rep _ F S V' W) (funext fun o => ?_)).mpr rr
      simp only [v80, upd, Ru.scr (oY + ℓ) hb]
      by_cases he : o = oY + ℓ
      · subst he
        simp [hℓ]
      · by_cases hi : oY ≤ o ∧ o < oY + N
        · rw [ifp hi, ifn he, ifn (by omega)]
          exact BitVec.or_zero
        · rw [ifn hi, ifn he]
    exact ⟨Lu.of_rep Ru Rv (kv.gpr (by decide)) kv.2.2, (ku.trans kv).mono (by decide), Rv⟩

end VG.Proof.RsaPss.X86_64
