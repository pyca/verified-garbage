module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyHash
public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyVerified
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_verify` on RISC-V, with its frame as an argument

The challenge (`verifyHash_ok`), the call of `vg_ed25519_verify_equation` on
the copies of `pk` and the signature (`verCall_ok`) and the restores: `a0`
then holds `verify`'s result (`verifyMessage_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)

/-- `verify`'s result on the inputs on entry. -/
abbrev verResult (s : State) : BitVec 32 :=
  if Spec.Ed25519.verify (bytesAt s.mem (s.gpr .a0) 32) (vmsgB s) (bytesAt s.mem (s.gpr .a3) 64) then 1 else 0

/-- The inputs of `verify_equation`: the copies of `pk` and the signature, and the challenge, in `F`. -/
abbrev verRd (s : State) : List Region :=
  [⟨s.gpr .a5 + BitVec.ofNat 64 192, 32⟩, ⟨s.gpr .a5 + BitVec.ofNat 64 128, 64⟩, ⟨s.gpr .a5, 64⟩]

/-- The narrowed state `verify_equation` starts in. -/
theorem verCall_pre {s t : State} (hp : VerPre s) (ha : VerArgs s t) :
    verifyRV.pre (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]) := by
  have ce : ∀ q, q ∉ linkRegs → (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]).gpr q = t.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  refine ⟨by rw [State.withRegions_rd, ce _ (by decide), ce _ (by decide), ce _ (by decide), ha.a0, ha.a1, ha.a2],
    by rw [State.withRegions_wr, ce _ (by decide), ha.a3], by rw [ce _ (by decide), ha.a3]; exact hp.alC,
    by rw [ce _ (by decide), ce _ (by decide), ha.a0, ha.a3]; exact hp.cF.symm.sub_left (Offset.sub_base _ (by decide)),
    by rw [ce _ (by decide), ce _ (by decide), ha.a1, ha.a3]; exact hp.cF.symm.sub_left (Offset.sub_base _ (by decide)),
    by rw [ce _ (by decide), ce _ (by decide), ha.a2, ha.a3]; exact hp.cF.symm.sub_left (Region.sub_prefix (by decide))⟩

theorem verCall_covers {s t : State} (hp : VerPre s) (ha : VerArgs s t) :
    Covers (verRd s ++ [⟨s.gpr .a4, 8192⟩]) (t.rd ++ t.wr) ∧ Covers [⟨s.gpr .a4, 8192⟩] t.wr := by
  rw [ha.inv.rd, ha.inv.wr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, 192, rfl, show 192 + 32 ≤ 272 by decide⟩
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, 128, rfl, show 128 + 64 ≤ 272 by decide⟩
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .a4, 8192⟩, by simp, 0, by simp, by simp⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨⟨s.gpr .a4, 8192⟩, by simp, 0, by simp, by simp⟩

theorem verifyEquation_noFrames : Impl.Ed25519.RISCV64.verifyEquation.noFrames = true := by decide +kernel

/-- The call of `verify_equation`. -/
theorem verCall_ok {s t : State} (hp : VerPre s) (ha : VerArgs s t) :
    WP isa (.call "vg_ed25519_verify_equation" Impl.Ed25519.RISCV64.verifyEquation) t fun t' =>
      VerInv s t' ∧ (t'.gpr .a0).setWidth 32 = verResult s := by
  obtain ⟨hc, hw⟩ := verCall_covers hp ha
  refine WP.call (k := verifyRV) verify_ok' (verCall_pre hp ha) hc hw (fun t' a b c f g _ hpost => ?_)
    verifyEquation_noFrames
  have hp' : (t'.gpr .a0).setWidth 32 = if Spec.Ed25519.verifyEquation (bytesAt t.mem (t.gpr .a0) 32)
      (bytesAt t.mem (t.gpr .a1) 64) (bytesAt t.mem (t.gpr .a2) 64) then 1 else 0 := hpost
  rw [ha.a0, ha.a1, ha.a2, ha.ch, ha.pk, ha.sig] at hp'
  refine ⟨verStep hp ha.inv a b c g f fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl rfl, hp'.trans ?_⟩
  unfold verResult Spec.Ed25519.verify
  rw [Proof.Ed25519.signatureBytes_take]

theorem verifyMessage_wp (C : ShaOK) {s : State} (hp : VerPre s) :
    WP isa verifyMessage s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ (t.gpr .a0).setWidth 32 = verResult s := by
  unfold verifyMessage
  refine WP.seq (WP.mono (verifyHash_ok C hp) fun t ha => ?_)
  refine WP.seq (WP.mono (verCall_ok hp ha) fun t' ⟨h', hr⟩ => ?_)
  have hFw : (⟨s.gpr .a5, 272⟩ : Region) ∈ t'.rd ++ t'.wr := List.mem_append_right _ (ver_Fw hp h')
  have hrl : ∀ p ∈ restoreList 224 verifyRegs, p.2 + 8 ≤ 272 := by decide
  refine restore_ok h' hp.alF (h'.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega))
    fun t₅ g₅ sp₅ ra₅ _ o₅ => ⟨g₅, sp₅, ra₅, ?_⟩
  rw [o₅ _ (by decide) (by decide), hr]

end VG.Proof.Ed25519.RISCV64.Whole
