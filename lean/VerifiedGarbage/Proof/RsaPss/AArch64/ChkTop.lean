module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCorrect
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
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
open VG.Proof.RsaPss.AArch64 (fitH_ok saltFitsR_ok expLen_ok restore_frame_ok slot_keep)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.RsaPss.AArch64.Sgn (fb stk)

/-- The result, and the calling convention. -/
def Post (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (s'.gpr .x0).setWidth 32 = if chkOut D Hs Gs s then 1 else 0

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
theorem ret0_ok {D : Nat} {Hs Gs : Spec.Mgf1.Hash} {s u : State} (hu : MidC s u) (hn : chkOut D Hs Gs s = false) :
    WP isa ret0 u fun t => MidC s t ∧ (t.gpr .x0).setWidth 32 = if chkOut D Hs Gs s then 1 else 0 := by
  unfold ret0
  refine wp_movz fun t o e => wp_nil ⟨⟨o.sp.trans hu.sp, o.rd.trans hu.rd, o.wr.trans hu.wr,
    fun r hr => (o.vcs r hr).trans (hu.v r hr), o.mem ▸ hu.fr⟩, ?_⟩
  rw [hn, e]
  rfl

/-- `AtCT` at a later state for which `AtC` holds, after writes only in our
working space. -/
theorem AtCT.of {D : Nat} {tsH tsG : List FnTable} {s u u' : State} (hp : PreC D tsH tsG s) (h : AtCT s u)
    (h' : AtC s u') (hf : Frame [⟨s.gpr .x6, oRsa⟩] u.mem u'.mem) (hsy : u'.syms = u.syms) : AtCT s u' := by
  have L := lay_of hp h.e.sp h.e.x20 h.e.wr
  exact ⟨h', by rw [slot_keep (d := sMgfT) hf (L.slotSd (by decide))]; exact h.wm,
    by rw [slot_keep (d := sIniH) hf (L.slotSd (by decide))]; exact h.wi,
    by rw [slot_keep (d := sCmpH) hf (L.slotSd (by decide))]; exact h.wc,
    by rw [slot_keep (d := sDigH) hf (L.slotSd (by decide))]; exact h.wd, hsy.trans h.sy⟩

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hHl hHv hGh hGl hGv hdo in
/-- After the copy and `fitH`: the checks of the lengths, then verification's
checks or 0. -/
theorem body_ok {tsH tsG : List FnTable} {s u : State} (hp : PreC H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hu : AtCT s u)
    (hem : ∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 (s.gpr .x2).toNat)
    (h10 : (u.gpr .x10 != 0) = decide ((s.gpr .x2).toNat < H.D + 2)) :
    WP isa (.ite (.nonzero .x .x10) ret0 (seqs [expLen, .block (saltFits H),
      .ite (.nonzero .x .x10) ret0 (chkMain f H g)])) u fun t =>
        MidC s t ∧ (t.gpr .x0).setWidth 32 = if chkOut H.D Hs Gs s then 1 else 0 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  have hel := hp.hel
  have hshort : (s.gpr .x2).toNat < Hs.len +
      (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32)).getD 0 + 2 → chkOut H.D Hs Gs s = false :=
    fun h => by
      unfold chkOut Spec.RsaPss.verifyEncoding
      exact ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (Or.inr (by rw [← hel]; exact h)))) |>.trans rfl
  refine WP.ite _ (eval_nonzero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [h10, decide_eq_true_eq] at hb
    exact ret0_ok hu.e.toMid (hshort (by rw [hHl]; omega))
  rw [h10, decide_eq_false_iff_not] at hb
  have L := lay_of hp hu.e.sp hu.e.x20 hu.e.wr
  unfold seqs seqs
  refine WP.seq (WP.mono_syms (expLen_ok L hu.e.fr.any hu.e.fr.sl) fun u₁ ⟨O₁, x12₁⟩ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (saltFitsR_ok H hD (a := (s.gpr .x2).toNat) (by omega) (by omega)
    (by rw [O₁.get .x9, h9]) x12₁) fun u₂ ⟨O₂, x9₂, x10₂⟩ sy₂ => ?_)
  have hu₂ := (hu.only O₁ sy₁).only O₂ sy₂
  have hsv : (if anyC s = 0 then s.gpr .x4 else 0).toNat =
      (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32)).getD 0 := by
    rw [expected_eq]; split <;> rfl
  rw [hsv] at x10₂
  refine WP.ite _ (eval_nonzero _ _) (fun hb₂ => ?_) (fun hb₂ => ?_)
  · rw [x10₂, decide_eq_true_eq] at hb₂
    exact ret0_ok hu₂.e.toMid (hshort (by rw [hHl]; omega))
  rw [x10₂, decide_eq_false_iff_not] at hb₂
  have hs : anyC s = 0 → (s.gpr .x4).toNat < (s.gpr .x2).toNat - H.D - 1 := fun ha => by
    rw [expected_eq, ite_eq_left ha, Option.getD_some] at hb₂
    omega
  refine WP.mono (chkMain_ok hH hGm hHs hHl hHv hGh hGl hGv hdo hp ht hu₂
    (fun i hi => by rw [O₂.mem, O₁.mem]; exact hem i hi) x9₂ (by omega) hs) fun t ⟨m, r⟩ => ⟨m, ?_⟩
  have hfit : Hs.len + (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32)).getD 0 + 2 ≤
      Spec.RsaPss.emLength (s.gpr .x3).toNat := by rw [← hel, hHl]; omega
  rw [r (chkOut H.D Hs Gs s) ?_]
  · split <;> rfl
  rw [chkOut, ← hHl, RsaPss.verifyEncoding_bytes₂ Gs Hs hGv (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _)
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hel]) hfit, ← hel, expected_eq]
  exact ⟨fun h => ⟨fun h01 => absurd h01 (by decide), h⟩, fun h => h.2⟩

include hH hHs hHl hHv hGh hGl hGv hdo in
theorem code_ok {tsH tsG : List FnTable} {s : State} (hp : PreC H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) :
    WP isa (checkEncoding f H g) s (Post H.D Hs Gs s) := by
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  have hk2 := hp.k2
  unfold checkEncoding
  refine WP.alloc (by decide) (by have := fb_toNat hp; omega) ?_
  unfold chkBody seqs seqs seqs seqs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu sy => ?_
  refine WP.mono (tabSlots_ok hp hu (by rw [sy]; simp [allocated])) fun u₀ hu₀ => ?_
  refine WP.seq (WP.mono_syms (copyIn_okC hp hu₀.e) fun u₁ ⟨hu₁, hem, hf₁⟩ sy₁ => ?_)
  have hu₁' : AtCT s u₁ := hu₀.of hp hu₁ hf₁ sy₁
  refine WP.seq (WP.mono_syms (fitH_ok H hD (k := (s.gpr .x2).toNat)
    (by rw [hu₁.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)) fun u₂ ⟨O₂, x9₂, x10₂⟩ sy₂ => ?_)
  refine WP.seq (WP.mono (body_ok hH hGm hHs hHl hHv hGh hGl hGv hdo hp ht (hu₁'.only O₂ sy₂)
    (fun i hi => by rw [O₂.mem]; exact hem i hi) x9₂ x10₂) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, _⟩ =>
    ⟨habi, by rw [hx0]; exact r⟩

end

end VG.Proof.RsaPss.AArch64.Chk
