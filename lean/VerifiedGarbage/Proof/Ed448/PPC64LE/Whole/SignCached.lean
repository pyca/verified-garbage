module

import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignChallenge
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Prune
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignNonce
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.PPC64LE.Ladder
public import VerifiedGarbage.Spec.Ed448
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_ed448_sign_cached` on PPC64LE, with its frame as an argument

The setup (`frame_ok`, `signSetup_ok`), the steps (`expand_ok`, `nonce_ok`,
`challenge_ok`), then `F` from 16 to 384 zeroed (`wipe_ok`) and the
registers restored: `out` holds `R ‖ S`, the signature (`signCached_wp`, by
`Proof.Ed448.sign_pipeline`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea restore_ok restoreList)
open VG.Spec.Ed448 (bytesAt)

/-- After the stores of `wipe` from the first `k`. -/
structure WInv (t₀ : State) (F : Addr) (o n : Nat) (k : Nat) (u : State) : Prop where
  gpr : u.gpr = t₀.gpr
  rd : u.rd = t₀.rd
  wr : u.wr = t₀.wr
  sp : u.sp = t₀.sp
  frame : Frame [⟨F + BitVec.ofNat 64 o, 8 * n⟩] t₀.mem u.mem

/-- `wipe f o n`: the `n` doublewords from `o(F)` zeroed, only `r8` written. -/
theorem wipe_ok {t : State} {f : Reg} {F : Addr} {o n : Nat} (hf0 : f ≠ .r0) (hf8 : f ≠ .r8) (hF : t.gpr f = F)
    (hon : o + 8 * n < 2 ^ 15) (ho : o % 4 = 0)
    (hw : ∀ k < n, InRegions t.wr (F + BitVec.ofNat 64 (o + 8 * k)) 8) {rest : List Instr} {Q : State → Prop}
    (K : ∀ u, Frame [⟨F + BitVec.ofNat 64 o, 8 * n⟩] t.mem u.mem → u.rd = t.rd → u.wr = t.wr → u.sp = t.sp →
      (∀ r, r ≠ .r8 → u.gpr r = t.gpr r) → WP isa (.block rest) u Q) :
    WP isa (.block (wipe f o n ++ rest)) t Q := by
  unfold wipe
  rw [List.cons_append]
  refine wp_li (by decide) fun u₁ h₁ => ?_
  rw [List.map_eq_flatMap, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (WInv u₁ F o n) (fun k u hk h => ?_) n (Nat.le_refl _) u₁
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩) fun u h => ?_
  · have hf : u.gpr f = F := by rw [h.gpr, h₁.other _ hf8, hF]
    refine wp_stdd (a := F + BitVec.ofNat 64 (o + 8 * k)) hf0 ⟨by omega, by omega⟩ (by rw [hf])
      (by rw [h.wr, h₁.wr]; exact hw k hk) fun u' h' => WP.block_nil ⟨by rw [h'.gpr, h.gpr], by rw [h'.rd, h.rd],
        by rw [h'.wr, h.wr], by rw [h'.sp, h.sp], ?_⟩
    rw [h'.mem]
    refine h.frame.writeW List.mem_cons_self _ ?_
    rw [← Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  · refine K u (by rw [← h₁.mem]; exact h.frame) (by rw [h.rd, h₁.rd]) (by rw [h.wr, h₁.wr])
      (by rw [h.sp, h₁.sp]) fun r hr => by rw [h.gpr, h₁.other r hr]

theorem bytesAt_split114 (m : Mem) (p : Addr) :
    bytesAt m p 114 = bytesAt m p 57 ++ bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [← bytesAt_take57, ← bytesAt_drop57, List.take_append_drop]

theorem signCached_wp (hl : Proof.Ed448.BaseLadder2Ok) {s : State} (hp : SignPre s) :
    WP isa signCached s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 114 = Spec.Ed448.sign (seedB s) (ctxB s) (msgB s) := by
  unfold signCached
  refine WP.seq (frame_ok hp fun u hu hlr => WP.block_nil ?_)
  refine WP.seq (WP.mono (signSetup_ok hp hu hlr) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (expand_ok hp h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (nonce_ok hl hp h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (challenge_ok hp h₃) fun t₄ h₄ => ?_)
  obtain ⟨σ, hσ, hS⟩ := h₄.S
  have g30 : t₄.gpr .r21 = sF s := h₄.inv.regs _ (by decide)
  have hFw : (fR s) ∈ t₄.wr := fF hp h₄.inv
  refine wipe_ok (f := .r21) (o := 16) (n := 46) (by decide) (by decide) g30 (by decide) (by decide)
    (fun k hk => in_base hFw (by omega) (by omega)) fun u uf urd uwr usp ug => ?_
  have h₅ : SInv s u := h₄.inv.step signRegs_pres urd uwr usp (fun r hr => ug r fun e => by revert hr; rw [e]; decide)
    uf (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨fR s, by simp, fsub (by decide)⟩)
    fun r hr => by rw [List.mem_singleton.mp hr]; exact fslot (by decide)
  have hrl : ∀ p ∈ restoreList 384 signRegs, p.2 + 8 ≤ 464 := by decide
  refine restore_ok h₅ (by decide) (h₅.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p (hp' : p ∈ restoreList 384 signRegs) => show InRegions (u.rd ++ u.wr) (sF s + BitVec.ofNat 64 p.2) 8 by
      rw [h₅.rd, h₅.wr, hp.rd, hp.wr]
      exact ⟨fR s, by simp, Offset.contains_base _ (hrl p hp') (by have := hrl p hp'; omega)⟩)
    fun t₆ g₆ sp₆ lr₆ m₆ _ => ⟨g₆, sp₆, lr₆, ?_⟩
  have kO : bytesAt t₆.mem (s.gpr .r3) 114 = bytesAt t₄.mem (s.gpr .r3) 114 := by
    rw [m₆]
    exact bytes_keep uf (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.oF.sub_right (fsub (by decide))
  rw [kO, bytesAt_split114, h₄.R, hS]
  exact Proof.Ed448.sign_pipeline _ _ _ _ σ hp.pk hσ

end VG.Proof.Ed448.PPC64LE.Whole
