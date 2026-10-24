module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem
import VerifiedGarbage.Proof.Dsa.SizeBounds

/-!
# DSA prevalidated verification on PPC64LE: the working spaces

`setup_ok`: for a key that passes `KeyOk`, `Prevalidated.setup rest fail`
runs `rest` from a state that is what `checkKey` leaves for it (`Checked`):
the sizes (`sizes_ok`) pass, then q goes into the Q space (`setupQ_ok`), p
and `R² mod p` into the P space (`setupP_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE

theorem setup_ok {s : State} {L : Lay} {key sig dig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig dig)
    (h2 : s.gpr .r2 = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (3 * L.pl + L.ql))
    (hK : KeyOk s.mem L key)
    (hrest : ∀ t, KeyOk s.mem L key → Checked s t L key sig dig d → Body L s.mem t.mem → Keep ckRegs s t →
      WP isa rest t Q) :
    WP isa (Prevalidated.setup rest fail) s Q := by
  have hk2 : Src s L key (2 * L.pl + L.ql) := hk.take (by omega)
  have vals : ∀ {m : Mem}, Body L s.mem m →
      pOf m L key = pOf s.mem L key ∧ qOf m L key = qOf s.mem L key := fun hm => by
    obtain ⟨a, b, -⟩ := params_kept hk2 (Kept.ofBody hL hm).out
    exact ⟨a, b⟩
  have hSz : SizesOk s.mem L key := hK.1.1
  have hp2 : 2 ≤ pOf s.mem L key := (VG.Proof.Dsa.supported_bounds hSz).1
  unfold Prevalidated.setup
  refine sizes_ok hL hr h2 hk2 hd (fun t₁ _ m₁ r2₁ k₁ => ?_) (fun _ hn _ _ _ => absurd hSz hn)
  have hqb : Spec.Dsa.bitLength (qOf s.mem L key) / 8 < 2 ^ 16 := by
    have h := hSz
    simp only [SizesOk] at h
    unfold Spec.Dsa.supportedSizes at h; simp only [Nat.reducePow]; omega
  have hr₁ : Regs t₁ L key sig dig :=
    Regs.of_pack hL ((k₁.gpr .r21 (by decide)).trans hr.r21) ((k₁.gpr .r27 (by decide)).trans hr.r27)
      ((k₁.gpr .r28 (by decide)).trans hr.r28) ((k₁.gpr .r26 (by decide)).trans hr.r26) r2₁ hqb hd
  have K₁ : Body L s.mem t₁.mem := by rw [m₁]; exact Body.refl _ _
  refine WP.seq (WP.mono (setupQ_ok hL (hs.congr k₁.wr) hr₁ (hk2.keep k₁.rd k₁.wr))
    fun t₂ ⟨⟨_, q0₂, qtop₂, qb₂⟩, k₂⟩ => ?_)
  have K₂ := K₁.trans (qb₂.body hL)
  have k₁₂ := k₁.trans k₂
  refine WP.seq (WP.mono (setupP_ok hL (hs.congr k₁₂.wr) (hr₁.keep k₂) (hk2.keep k₁₂.rd k₁₂.wr)
      (by rw [(vals K₂).1]; exact hp2)) fun t₃ ⟨⟨ip₃, p0₃, ptop₃, p8₃, pb₃⟩, k₃⟩ => ?_)
  rw [(vals K₂).1] at p0₃ p8₃
  rw [(vals K₁).2] at q0₂
  have k₁₃ := k₁₂.trans k₃
  refine hrest t₃ hK ⟨ip₃, hs.congr k₁₃.wr, (hr₁.keep k₂).keep k₃, p0₃, ptop₃, p8₃,
    (pb₃.arrQ hL 0 (by decide)).trans q0₂, (pb₃.qtop hL).trans qtop₂, ?_⟩ (K₂.trans (pb₃.body hL))
    (k₁₃.mono (by decide))
  rw [k₃.gpr .r2 (by decide), k₂.gpr .r2 (by decide)]; exact r2₁

end VG.Proof.Dsa.PPC64LE
