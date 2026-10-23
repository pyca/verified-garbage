module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.VerifyHash
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyVerified
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_verify` on PPC64LE, with its frame as an argument

The challenge (`verifyHash_ok`), the call of `vg_ed25519_verify_equation`
(`verCall_ok`) and the restores: `r3` then holds `verify`'s result
(`verifyMessage_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

/-- `verify`'s result on the inputs on entry. -/
abbrev verResult (s : State) : BitVec 32 :=
  if Spec.Ed25519.verify (bytesAt s.mem (s.gpr .r3) 32) (vmsgB s) (bytesAt s.mem (s.gpr .r6) 64) then 1 else 0

theorem ver_pk {s t : State} (hp : VerPre s) (h : VerInv s t) :
    bytesAt t.mem (s.gpr .r3) 32 = bytesAt s.mem (s.gpr .r3) 32 :=
  ver_input h (by decide) hp.pC hp.pF hp.bP.symm

theorem ver_sig {s t : State} (hp : VerPre s) (h : VerInv s t) :
    bytesAt t.mem (s.gpr .r6) 64 = bytesAt s.mem (s.gpr .r6) 64 :=
  ver_input h (by decide) hp.sC hp.sF hp.bS.symm

/-- The narrowed state `verify_equation` starts in. -/
theorem verCall_pre {s t : State} (hp : VerPre s) (ha : VerArgs s t) :
    verifyPPC.pre (t.callEntry.withRegions [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r6, 64⟩, ⟨s.gpr .r8, 64⟩]
      [⟨s.gpr .r7, 8192⟩]) := by
  have ce : ∀ q, q ∉ linkRegs → (t.callEntry.withRegions [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r6, 64⟩, ⟨s.gpr .r8, 64⟩]
      [⟨s.gpr .r7, 8192⟩]).gpr q = t.gpr q := fun q hq => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  refine ⟨by rw [State.withRegions_rd, ce _ (by decide), ce _ (by decide), ce _ (by decide), ha.r3, ha.r4, ha.r5],
    by rw [State.withRegions_wr, ce _ (by decide), ha.r6], by rw [ce _ (by decide), ce _ (by decide), ha.r3, ha.r6]; exact hp.pC,
    by rw [ce _ (by decide), ce _ (by decide), ha.r4, ha.r6]; exact hp.sC,
    by rw [ce _ (by decide), ce _ (by decide), ha.r5, ha.r6]; exact hp.cF.symm.sub_left (Region.sub_prefix (by decide))⟩

theorem verCall_covers {s t : State} (hp : VerPre s) (ha : VerArgs s t) :
    Covers ([⟨s.gpr .r3, 32⟩, ⟨s.gpr .r6, 64⟩, ⟨s.gpr .r8, 64⟩] ++ [⟨s.gpr .r7, 8192⟩]) (t.rd ++ t.wr) ∧
      Covers [⟨s.gpr .r7, 8192⟩] t.wr := by
  rw [ha.inv.rd, ha.inv.wr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .r3, 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .r6, 64⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .r8, 192⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .r7, 8192⟩, by simp, 0, by simp, by simp⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨⟨s.gpr .r7, 8192⟩, by simp, 0, by simp, by simp⟩

theorem verifyEquation_noFrames : Impl.Ed25519.PPC64LE.verifyEquation.noFrames = true := by decide +kernel

/-- The call of `verify_equation`. -/
theorem verCall_ok {s t : State} (hp : VerPre s) (ha : VerArgs s t) :
    WP isa (.call "vg_ed25519_verify_equation" Impl.Ed25519.PPC64LE.verifyEquation) t fun t' =>
      VerInv s t' ∧ (t'.gpr .r3).setWidth 32 = verResult s := by
  obtain ⟨hc, hw⟩ := verCall_covers hp ha
  refine WP.call (k := verifyPPC) verify_ok' (verCall_pre hp ha) hc hw (fun t' a b c f g _ hpost => ?_)
    verifyEquation_noFrames
  have hp' : (t'.gpr .r3).setWidth 32 = if Spec.Ed25519.verifyEquation (bytesAt t.mem (t.gpr .r3) 32)
      (bytesAt t.mem (t.gpr .r4) 64) (bytesAt t.mem (t.gpr .r5) 64) then 1 else 0 := hpost
  rw [ha.r3, ha.r4, ha.r5, ha.ch, ver_pk hp ha.inv, ver_sig hp ha.inv] at hp'
  refine ⟨verStep hp ha.inv a b c g f fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl rfl, hp'.trans ?_⟩
  unfold verResult Spec.Ed25519.verify
  rw [Proof.Ed25519.signatureBytes_take]

theorem verifyMessage_wp (C : ShaOK) {s : State} (hp : VerPre s) :
    WP isa verifyMessage s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      (t.gpr .r3).setWidth 32 = verResult s := by
  unfold verifyMessage
  refine WP.seq (WP.mono (verifyHash_ok C hp) fun t ha => ?_)
  refine WP.seq (WP.mono (verCall_ok hp ha) fun t' ⟨h', hr⟩ => ?_)
  have hFw : (⟨s.gpr .r8, 192⟩ : Region) ∈ t'.rd ++ t'.wr := List.mem_append_right _ (ver_Fw hp h')
  have hrl : ∀ p ∈ restoreList 128 verifyRegs, p.2 + 8 ≤ 192 := by decide
  refine restore_ok h' (by decide) (h'.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega))
    fun t₅ g₅ sp₅ lr₅ _ o₅ => ⟨g₅, sp₅, lr₅, ?_⟩
  rw [o₅ _ (by decide) (by decide), hr]

end VG.Proof.Ed25519.PPC64LE.Whole
