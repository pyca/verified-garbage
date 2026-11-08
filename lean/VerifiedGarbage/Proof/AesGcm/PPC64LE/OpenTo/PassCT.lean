module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Pass
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.CT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Pass
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_open_split`'s data pass is constant time

Untrusted: everything here is checked by Lean. From states whose arguments
are the same (`PI`): `wholeArgs` by the taint analysis, the call of
`vg_aes_gcm_decrypt_blocks_to` with the same arguments in both runs
(`RelCT.callEx`), the last bytes by `open`'s tail (`cryptTailWith_ct`),
`absorb` and `finTag` (`pass_ct`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Pass

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Spec.Gcm (blockAt)

/-- Before the data's pass, with the arguments of both runs. -/
def PI (c st w sp : Addr) (R : Nat) (A S N : BitVec 64) (D : Addr) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r22 = A ∧ V .r27 = S ∧ V .r23 = N ∧
    WholeIn V sp R D s

/-- After `wholeArgs`. -/
def AI (c st w sp : Addr) (R : Nat) (A S N : BitVec 64) (D : Addr) (t : State) : Prop :=
  ∃ V s, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r22 = A ∧ V .r27 = S ∧ V .r23 = N ∧
    WholeIn V sp R D s ∧ ArgsOut V R D s t

/-- After `whole`. -/
def QI (c st w sp : Addr) (R : Nat) (A S N : BitVec 64) (D : Addr) (t : State) : Prop :=
  ∃ V s, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r22 = A ∧ V .r27 = S ∧ V .r23 = N ∧
    WholeIn V sp R D s ∧ WholeOut V sp R D s t

/-- After `partArgs`. -/
def P2 (c st w sp : Addr) (R : Nat) (A S N : BitVec 64) (D : Addr) (t : State) : Prop :=
  ∃ V s s₁, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r22 = A ∧ V .r27 = S ∧ V .r23 = N ∧
    WholeIn V sp R D s ∧ WholeOut V sp R D s s₁ ∧ PartOut V D s₁ t

/-- After the last bytes: the source still to absorb. -/
def EI (c st w sp : Addr) (R : Nat) (A S N : BitVec 64) (t : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = BitVec.ofNat 64 R ∧ V .r22 = A ∧
    V .r27 = S ∧ V .r23 = N ∧ Env V sp t ∧ DataOk st w t S N.toNat

section
variable {c st w sp : Addr} {R : Nat} {A S N : BitVec 64} {D : Addr}

theorem wholeArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r23, .r27, .r28, .r29, .r30, .r31]) (.block wholeArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem partArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r23, .r26, .r27]) (.block partArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem tailSetup_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r23, .r27]) (.block SealFused.tailSetup) h).isSome = true := ⟨_, by taint_decide⟩

theorem whole_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (L : Lay c st w) : CT (PI c st w sp R A S N D) whole := by
  obtain ⟨_, hc⟩ := wholeArgs_taint
  refine CT.seq (J := AI c st w sp R A S N D) ?_
    (fun s ⟨V, a, b, d, e, f, g, h⟩ => WP.mono (argsOut h) fun t ht => ⟨V, s, a, b, d, e, f, g, h, ht⟩) ?_
  · refine CT.taint _ (fun s₁ s₂ ⟨V₁, a₁, b₁, d₁, _, f₁, g₁, h₁⟩ ⟨V₂, a₂, b₂, d₂, _, f₂, g₂, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.env.fr .r23 (by decide), h₂.env.fr .r23 (by decide), g₁, g₂]
    · rw [h₁.env.fr .r27 (by decide), h₂.env.fr .r27 (by decide), f₁, f₂]
    · rw [h₁.env.fr .r28 (by decide), h₂.env.fr .r28 (by decide), h₁.r28, h₂.r28]
    · rw [h₁.env.r29, h₂.env.r29, a₁, a₂]
    · rw [h₁.env.r30, h₂.env.r30, b₁, b₂]
    · rw [h₁.env.r31, h₂.env.r31, d₁, d₂]
  · refine RelCT.callEx SplitBlocks.decryptTo_correct SplitBlocks.decryptTo_ct
      fun t₁ t₂ ⟨⟨V₁, s₁, a₁, b₁, d₁, _, f₁, g₁, h₁, o₁⟩, ⟨V₂, s₂, a₂, b₂, d₂, _, f₂, g₂, h₂, o₂⟩⟩ => ?_
    obtain ⟨p₁, r₁, w₁⟩ := whole_call (L.v a₁ b₁ d₁) h₁ o₁
    obtain ⟨p₂, r₂, w₂⟩ := whole_call (L.v a₂ b₂ d₂) h₂ o₂
    refine ⟨callRd V₁, callWr V₁ D, callRd V₂, callWr V₂ D, p₁, p₂, ?_, r₁, w₁, r₂, w₂⟩
    have sp₁ : t₁.sp = sp := o₁.keeps.sp.trans h₁.env.sp
    have sp₂ : t₂.sp = sp := o₂.keeps.sp.trans h₂.env.sp
    sig_eval [Proof.Gcm.decryptBlocksToContract, Proof.Gcm.decryptBlocksToSig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [o₁.r3, o₁.r4, o₁.r5, o₁.r6, o₁.r7, o₁.r8, o₁.r9, o₁.r10,
      o₂.r3, o₂.r4, o₂.r5, o₂.r6, o₂.r7, o₂.r8, o₂.r9, o₂.r10, a₁, a₂, b₁, b₂, d₁, d₂, f₁, f₂,
      Q, g₁, g₂, sp₁, sp₂]
    trivial

theorem whole_qi [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] (L : Lay c st w)
    {s : State} (hs : PI c st w sp R A S N D s) : WP isa whole s (QI c st w sp R A S N D) := by
  obtain ⟨V, a, b, d, e, f, g, h⟩ := hs
  exact WP.mono (whole_ok (L.v a b d) h) fun t ht => ⟨V, s, a, b, d, e, f, g, h, ht⟩

theorem partArgs_p2 {s : State} (hs : QI c st w sp R A S N D s) :
    WP isa (.block partArgs) s (P2 c st w sp R A S N D) := by
  obtain ⟨V, s₀, a, b, d, e, f, g, h, hw⟩ := hs
  exact WP.mono (partArgs_ok hw.env hw.r26) fun t ⟨a24, a25, a26, g₂, k₂⟩ =>
    ⟨V, s₀, s, a, b, d, e, f, g, h, hw, ⟨a24, a25, a26, g₂, k₂⟩⟩

theorem p2_tail (L : Lay c st w) {s : State} (hs : P2 c st w sp R A S N D s) :
    TailI true c st w sp R (S + BitVec.ofNat 64 (16 * (N.toNat / 16)))
      (D + BitVec.ofNat 64 (16 * (N.toNat / 16))) (N.toNat - 16 * (N.toNat / 16)) s := by
  obtain ⟨V, s₀, s₁, a, b, d, _, f, g, h, hw, p⟩ := hs
  have t := tail_in (L.v a b d) h hw p
  simp only [Q, f, g] at t
  exact ⟨V, _, _, _, _, a, b, d, t⟩

theorem tail_ei (L : Lay c st w) {s : State} (hs : P2 c st w sp R A S N D s) :
    WP isa (cryptTailWith true) s (EI c st w sp R A S N) := by
  obtain ⟨V, s₀, s₁, a, b, d, e, f, g, h, hw, p⟩ := hs
  have hk : (V .r23).toNat - 16 * Q V < 16 := by show _ - 16 * ((V .r23).toNat / 16) < 16; omega
  refine WP.mono (WP.with_rdwr (cryptTailWith_ok (L.v a b d) (tail_in (L.v a b d) h hw p) hk))
    fun t ⟨o, rd, wr, _⟩ => ⟨V, a, b, d, h.r28, e, f, g, o.env, ?_⟩
  rw [← b, ← d, ← f, ← g]
  exact h.src.of_eq (rd.trans (p.keeps.rd.trans hw.rd)) (wr.trans (p.keeps.wr.trans hw.wr))

theorem tailSetup_abs {s : State} (hs : EI c st w sp R A S N s) :
    WP isa (.block SealFused.tailSetup) s fun t =>
      AbsI c st w sp 16 (S + BitVec.ofNat 64 (16 * (N.toNat / 16))) (N.toNat % 16) 0 t ∧
      EI c st w sp R A S N t := by
  obtain ⟨V, a, b, d, e, f, g, i, he, hd⟩ := hs
  refine WP.mono (SealFused.tailSetup_ok he) fun t ⟨h24, h25, h26, hg, hk⟩ => ?_
  have het := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  have hds := hd.drop (j := 16 * (N.toNat / 16)) (by omega)
  rw [show N.toNat - 16 * (N.toNat / 16) = N.toNat % 16 by omega] at hds
  refine ⟨⟨V, blockAt t.mem (V .r29 + BitVec.ofNat 64 240), [], a, b, d, rfl,
    ⟨het, by rw [h24, g, i], by rw [h25, i], h26, by rw [b, d]; exact hds.of_eq hk.rd hk.wr, rfl⟩⟩,
    ⟨V, a, b, d, e, f, g, i, het, hd.of_eq hk.rd hk.wr⟩⟩

theorem abs_fti [VG.Proof.Gcm.PPC64LE.GhashLaw] (L : Lay c st w) {s : State}
    (hs : AbsI c st w sp 16 (S + BitVec.ofNat 64 (16 * (N.toNat / 16))) (N.toNat % 16) 0 s ∧
      EI c st w sp R A S N s) :
    WP isa (absorb 16) s (FTI c st w sp R A N) := by
  obtain ⟨⟨V', H, x, a', b', d', _, ai⟩, ⟨V, a, b, d, e, f, g, i, he, _⟩⟩ := hs
  refine WP.mono (absorb_ok (L.v a' b' d') (.inr rfl) ai) fun t ab => ⟨V, a, b, d, e, f, i, ?_⟩
  have hV : ∀ r ∈ frozen, V r = V' r := fun r hr => (he.fr r hr).symm.trans (ai.env.fr r hr)
  exact ⟨fun r hr => (ab.env.fr r hr).trans (hV r hr).symm, ab.env.sp,
    by rw [hV .r29 (by decide), hV .r30 (by decide), hV .r31 (by decide)]; exact ab.env.perm⟩

theorem passData_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] (L : Lay c st w)
    {s : State} (hs : PI c st w sp R A S N D s) : WP isa passData s (FTI c st w sp R A N) :=
  WP.seq (WP.mono (whole_qi L hs) fun _ ht => WP.seq (WP.seq (WP.mono (partArgs_p2 ht) fun _ hu =>
    WP.mono (tail_ei L hu) fun _ hv => WP.seq (WP.mono (tailSetup_abs hv) fun _ hx => abs_fti L hx))))

theorem pass_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] (L : Lay c st w)
    (hv : R = 10 ∨ R = 12 ∨ R = 14) : CT (PI c st w sp R A S N D) (.seq passData (finTag 112)) := by
  refine CT.seq (J := FTI c st w sp R A N) ?_ (fun s hs => passData_wp L hs) (finTag_ct L (.inr rfl) hv)
  refine CT.seq (J := QI c st w sp R A S N D) (whole_ct L) (fun s hs => whole_qi L hs) ?_
  refine CT.seq (J := EI c st w sp R A S N) ?_
    (fun s hs => WP.seq (WP.mono (partArgs_p2 hs) fun t ht => tail_ei L ht)) ?_
  · refine CT.seq (J := P2 c st w sp R A S N D) ?_ (fun s hs => partArgs_p2 hs)
      ((cryptTailWith_ct L).mono fun s hs => p2_tail L hs)
    obtain ⟨_, hc⟩ := partArgs_taint
    refine CT.taint _ (fun s₁ s₂ ⟨V₁, _, _, _, _, _, f₁, g₁, _, hw₁⟩ ⟨V₂, _, _, _, _, _, f₂, g₂, _, hw₂⟩ =>
      ⟨hw₁.env.sp.trans hw₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hw₁.env.fr .r23 (by decide), hw₂.env.fr .r23 (by decide), g₁, g₂]
    · rw [hw₁.r26, hw₂.r26]
    · rw [hw₁.env.fr .r27 (by decide), hw₂.env.fr .r27 (by decide), f₁, f₂]
  · refine CT.seq (J := fun s => AbsI c st w sp 16 (S + BitVec.ofNat 64 (16 * (N.toNat / 16))) (N.toNat % 16) 0 s ∧
      EI c st w sp R A S N s) ?_ (fun s hs => tailSetup_abs hs)
      ((absorb_ct L (.inr rfl) (q := 0) (by decide)).mono fun s hs => hs.1)
    obtain ⟨_, hc⟩ := tailSetup_taint
    refine CT.taint _ (fun s₁ s₂ ⟨V₁, _, _, _, _, _, g₁, i₁, he₁, _⟩ ⟨V₂, _, _, _, _, _, g₂, i₂, he₂, _⟩ =>
      ⟨he₁.sp.trans he₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [he₁.fr .r23 (by decide), he₂.fr .r23 (by decide), i₁, i₂]
    · rw [he₁.fr .r27 (by decide), he₂.fr .r27 (by decide), g₁, g₂]

end

end VG.Proof.AesGcm.PPC64LE.Pass
