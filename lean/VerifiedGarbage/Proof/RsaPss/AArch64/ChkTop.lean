module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCorrect
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-!
# EMSA-PSS's check of an encoding on AArch64: the whole function

`code_ok`: from the precondition, `checkEncoding` keeps the calling
convention and returns 1 exactly when `Spec.RsaPss.verifyEncoding` holds
(`Post`): the prologue (`prologue_ok`), the copy (`copyIn_okC`), the checks
of the lengths (`body_ok`), verification's checks (`chkMain_ok`), and the
restores (`restore_frame_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (wp_nil wp_movz eval_nonzero)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (fitH_ok saltFitsR_ok expLen_ok restore_frame_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb stk)

/-- The result, and the calling convention. -/
def Post (G : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (s'.gpr .x0).setWidth 32 = if chkOut G s then 1 else 0

theorem anyC_eq (s : State) : anyC s = 0 ↔ (s.gpr .x5).setWidth 32 = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [anyC, BitVec.toNat_setWidth] at this ⊢
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
    rw [show (0 : BitVec 32).toNat = 0 from rfl]
    omega
  · intro h; unfold anyC; rw [h]; rfl

theorem expected_eq (s : State) : Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32) =
    if anyC s = 0 then some (s.gpr .x4).toNat else none := by
  unfold Spec.RsaPss.expectedSaltLen
  by_cases h : anyC s = 0
  · rw [ite_eq_left h, ite_eq_left ((anyC_eq s).mp h)]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ((anyC_eq s).mpr h')]

/-- A refusal: 0. -/
theorem ret0_ok {G : Spec.Mgf1.Hash} {s u : State} (hu : MidC s u) (hn : chkOut G s = false) :
    WP isa ret0 u fun t => MidC s t ∧ (t.gpr .x0).setWidth 32 = if chkOut G s then 1 else 0 := by
  unfold ret0
  refine wp_movz fun t o e => wp_nil ⟨⟨o.sp.trans hu.sp, o.rd.trans hu.rd, o.wr.trans hu.wr,
    fun r hr => (o.vcs r hr).trans (hu.v r hr), o.mem ▸ hu.fr⟩, ?_⟩
  rw [hn, e]
  rfl

section
variable {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
  (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G)

include hH hGh hGl hG in
/-- After the copy and `fitH`: the checks of the lengths, then verification's
checks or 0. -/
theorem body_ok {s u : State} (hp : PreC H.D s) (hu : AtC s u)
    (hem : ∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 (s.gpr .x2).toNat)
    (h10 : (u.gpr .x10 != 0) = decide ((s.gpr .x2).toNat < H.D + 2)) :
    WP isa (.ite (.nonzero .x .x10) ret0 (seqs [expLen, .block (saltFits H),
      .ite (.nonzero .x .x10) ret0 (chkMain H)])) u fun t =>
        MidC s t ∧ (t.gpr .x0).setWidth 32 = if chkOut G s then 1 else 0 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  have hel := hp.hel
  have hshort : (s.gpr .x2).toNat < G.len +
      (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32)).getD 0 + 2 → chkOut G s = false :=
    fun h => by
      unfold chkOut Spec.RsaPss.verifyEncoding
      exact ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (Or.inr (by rw [← hel]; exact h)))) |>.trans rfl
  refine WP.ite _ (eval_nonzero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [h10, decide_eq_true_eq] at hb
    exact ret0_ok hu.toMid (hshort (by rw [hGl]; omega))
  rw [h10, decide_eq_false_iff_not] at hb
  have L := lay_of hp hu.sp hu.x20 hu.wr
  unfold seqs seqs
  refine WP.seq (WP.mono (expLen_ok L hu.fr.any hu.fr.sl) fun u₁ ⟨O₁, x12₁⟩ => ?_)
  refine WP.seq (WP.mono (saltFitsR_ok H hD (a := (s.gpr .x2).toNat) (by omega) (by omega)
    (by rw [O₁.get .x9, h9]) x12₁) fun u₂ ⟨O₂, x9₂, x10₂⟩ => ?_)
  have hu₂ := (hu.only O₁).only O₂
  have hsv : (if anyC s = 0 then s.gpr .x4 else 0).toNat =
      (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32)).getD 0 := by
    rw [expected_eq]; split <;> rfl
  rw [hsv] at x10₂
  refine WP.ite _ (eval_nonzero _ _) (fun hb₂ => ?_) (fun hb₂ => ?_)
  · rw [x10₂, decide_eq_true_eq] at hb₂
    exact ret0_ok hu₂.toMid (hshort (by rw [hGl]; omega))
  rw [x10₂, decide_eq_false_iff_not] at hb₂
  have hs : anyC s = 0 → (s.gpr .x4).toNat < (s.gpr .x2).toNat - H.D - 1 := fun ha => by
    rw [expected_eq, ite_eq_left ha, Option.getD_some] at hb₂
    omega
  refine WP.mono (chkMain_ok hH hGh hGl hG hp hu₂ (fun i hi => by rw [O₂.mem, O₁.mem]; exact hem i hi) x9₂
    (by omega) hs) fun t ⟨m, r⟩ => ⟨m, ?_⟩
  have hfit : G.len + (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32)).getD 0 + 2 ≤
      Spec.RsaPss.emLength (s.gpr .x3).toNat := by rw [← hel, hGl]; omega
  rw [r (chkOut G s) ?_]
  · split <;> rfl
  rw [chkOut, RsaPss.verifyEncoding_bytes G hG (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _)
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hel]) hfit, ← hel, expected_eq, hGl]
  exact ⟨fun h => ⟨fun h01 => absurd h01 (by decide), h⟩, fun h => h.2⟩

include hH hGh hGl hG in
theorem code_ok {s : State} (hp : PreC H.D s) : WP isa (checkEncoding H) s (Post G s) := by
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  have hk2 := hp.k2
  unfold checkEncoding
  refine WP.alloc (by decide) (by have := hp.sp1; unfold chkStack stk at this; omega) ?_
  unfold chkBody seqs seqs seqs seqs
  refine WP.seq (WP.mono (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu => ?_)
  refine WP.seq (WP.mono (copyIn_okC hp hu) fun u₁ ⟨hu₁, hem⟩ => ?_)
  refine WP.seq (WP.mono (fitH_ok H hD (k := (s.gpr .x2).toNat)
    (by rw [hu₁.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)) fun u₂ ⟨O₂, x9₂, x10₂⟩ => ?_)
  refine WP.seq (WP.mono (body_ok hH hGh hGl hG hp (hu₁.only O₂) (fun i hi => by rw [O₂.mem]; exact hem i hi)
    x9₂ x10₂) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, _⟩ =>
    ⟨habi, by rw [hx0]; exact r⟩

end

end VG.Proof.RsaPss.AArch64.Chk
