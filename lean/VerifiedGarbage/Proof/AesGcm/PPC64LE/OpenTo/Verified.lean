module

public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Fn
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Split
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTSeal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Split
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Pass
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.CT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Pass
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Sig

/-! ### `AesGcm.PPC64LE.OpenTo.SplitCT`, which only this module used -/

section

/-! ### `AesGcm.PPC64LE.OpenTo.PassCT`, which only this module used -/

section

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
  have hk : (V .r23).toNat - 16 * Q V < 16 := by show _ - 16 * ((V .r23).toNat / 16) < 16; omega_using []
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
  have hds := hd.drop (j := 16 * (N.toNat / 16)) (by omega_using [])
  rw [show N.toNat - 16 * (N.toNat / 16) = N.toNat % 16 by omega_using []] at hds
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

end

end

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_open_split` is constant time

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_split`
branches on the tag length, which is public, and on the data's length; it
does not branch on whether the tags are equal. Its entry and the tag
length are `open`'s (`CTOpen.lean`); after them, `oneAad` and `recv` are
`open`'s, the data's pass is `pass_ct` (`PassCT.lean`), from what the entry
leaves of the destination (`DstX`), and `cmp 112` is checked by the taint
analysis (`passRest_ct`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- What the data's pass needs of the destination `Dst` (at `sp + 120`). -/
def DstX (c W sp : Addr) (S Ln : BitVec 64) (Dst : Addr) (s : State) : Prop :=
  DataW c (W + BitVec.ofNat 64 16) W s Dst Ln.toNat ∧ (⟨S, Ln.toNat⟩ : Region).Disjoint ⟨Dst, Ln.toNat⟩ ∧
    InRegions (s.rd ++ s.wr) (sp + BitVec.ofNat 64 120) 8 ∧ s.mem.readW (sp + BitVec.ofNat 64 120) 64 = Dst ∧
    (⟨sp + BitVec.ofNat 64 120, 8⟩ : Region).Disjoint ⟨W, 2560⟩

abbrev DOk : Addr → Addr → Addr → State → Addr → Nat → Prop := fun _ st w s D n => DataOk st w s D n

theorem DstX.frame {c W sp : Addr} {S Ln : BitVec 64} {Dst : Addr} {s t : State} (h : DstX c W sp S Ln Dst s)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hW : ∀ r ∈ rs, ∃ r' ∈ [(⟨W, 2560⟩ : Region)], Region.Sub r r') : DstX c W sp S Ln Dst t := by
  obtain ⟨hd, hsd, hi, hv, hA⟩ := h
  refine ⟨hd.of_eq hrd hwr, hsd, by rw [hrd, hwr]; exact hi, ?_, hA⟩
  rw [Frame.readW hf (Region.contains_self _ _) (fun r hr => by
    obtain ⟨r', hr', hs⟩ := hW r hr
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hA.sub_right hs) (by decide)]
  exact hv

section
variable {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A S Ln T TL : BitVec 64} {Dst : Addr}
  (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTd : (⟨T, TL.toNat⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) (t1 : 1 ≤ TL.toNat) (t16 : TL.toNat ≤ 16)
include L hR hTd t1 t16

/-- `vg_aes_gcm_open_split` from `oneAad` on, once the tag length is allowed. -/
theorem passRest_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    CT (fun s => (OneOP DOk c W sp R Np n Ad A S Ln T TL s ∧ s.gpr .r24 = Np ∧
      s.gpr .r25 = BitVec.ofNat 64 n) ∧ DstX c W sp S Ln Dst s)
    (.seq oneAad (.seq recv (.seq (.ite (.zero .d .r23) (oneTag 112) (.seq passData (finTag 112)))
      (cmp 112)))) := by
  have hP := dataOk_ok
  let J₁ : State → Prop := fun s => OneOP DOk c W sp R Np n Ad A S Ln T TL s ∧ OneAbs c W A s ∧
    DstX c W sp S Ln Dst s
  -- `oneAad`
  refine CT.seq (J := J₁) ((oneAad_ctP L hP).mono fun s h => ⟨h.1.1.1, h.1.2⟩) (fun s ⟨⟨hT, h24, h25⟩, hX⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, g, i]; exact hA))) fun s' ⟨oa, rd, wr, _⟩ => ⟨OneOP.keep hP hT (fun r hr => (he.fr r hr).symm)
        oa.env rd wr, ⟨blockAt s.mem (V .r29 + BitVec.ofNat 64 240), bytesAt s.mem (V .r21) (V .r22).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩, hX.frame rd wr oa.frame ?_⟩
    rw [b, d]; exact inW_j0
  -- `recv`
  refine CT.seq (J := J₁) ?_ (fun s ⟨hT, hab, hX⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨⟨_, _, _, d₁, _, _, _, _, _, _, h₁, _⟩, a₁, b₁, _⟩, _⟩
      ⟨⟨⟨_, _, _, d₂, _, _, _, _, _, _, h₂, _⟩, a₂, b₂, _⟩, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [a₁, a₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    have h19 : V .r19 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    have h20 : V .r20 = T := by rw [← he.fr _ (by decide), hT.2.1]
    refine WP.mono (recv_ok he h19 t1 t16 (by rw [h20]; exact hT.2.2.2) (by rw [h20, d]; exact hTd))
      fun s' ⟨_, hf, g', k'⟩ => ?_
    have he' := he.keep (fun r hr => g' r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k'.sp k'.rd k'.wr
    rw [d] at hf
    obtain ⟨H, x, hH, hl, hx⟩ := hab
    have hst : ∀ {e k : Nat}, e + k ≤ 80 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 e, k⟩ : Region).Disjoint r := by
      intro e k hek r hr; simp only [List.mem_singleton] at hr; subst hr
      exact L.st_w hek (.inr ⟨by decide, by decide⟩)
    refine ⟨OneOP.keep hP hT (fun r hr => (he.fr r hr).symm) he' k'.rd k'.wr, ⟨H, x, ?_, hl, ?_⟩,
      hX.frame k'.rd k'.wr hf (inW_at (d := 256) (by decide))⟩
    · rw [blockAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.wSub (by decide)))]
      exact hH
    · refine hx.congr (blockAt_frame hf (hst (by decide))) (bytesAt_frame hf (hst ?_) (by omega_using []))
      have := Nat.mod_lt (x ++ zeros (padLen x.length)).length (by decide : 0 < 16)
      omega_using []
  -- the data and its tag
  refine CT.seq (J := OneOP DOk c W sp R Np n Ad A S Ln T TL) ?_ (fun s ⟨hT, hab, hX⟩ => ?_) ?_
  · have ev : ∀ s, J₁ s → isa.eval (.zero .d .r23) s = some (decide (Ln.toNat = 0)) :=
      fun s ⟨⟨⟨_, _, _, _, _, _, _, _, _, k, he, _⟩, _⟩, _⟩ =>
        eval_zero (by rw [he.ofNat (r := .r23) (by decide), k]) Ln.isLt
    refine CT.ite _ ev (fun _ => (oneTag_ctP L hP (.inr rfl) hR).mono fun s h => h.1.1)
      (fun _ => (Pass.pass_ct (sp := sp) (A := A) (S := S) (N := Ln) (D := Dst) L hR).mono fun s ⟨hT, _, hX⟩ => ?_)
    obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    obtain ⟨hd, hsd, hi, hv, _⟩ := hX
    exact ⟨V, a, b, d, i, j, k, ⟨he, e, hR, by rw [b, d, j, k]; exact hD, by rw [a, b, d, k]; exact hd,
      by rw [j, k]; exact hsd, hi, hv⟩⟩
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    obtain ⟨H, x, hH, hl, hx⟩ := hab
    refine WP.ite _ (eval_zero (by rw [he.ofNat (r := .r23) (by decide), k]) Ln.isLt) (fun _ => ?_) (fun hb => ?_)
    · exact WP.mono (WP.with_rdwr (oneTag_ok (L.v a b d) (o := 112) (.inr rfl) (H := H) (a := x) he e hR
        (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hx) (by rw [b, d, j, k]; exact hD)))
        fun s' ⟨ot, rd, wr, _⟩ => OneOP.keep hP hT (fun r hr => (he.fr r hr).symm) ot.env rd wr
    · have hpos : 0 < (V .r23).toNat := by rw [k]; have := of_decide_eq_false hb; omega_using [this]
      obtain ⟨hd, hsd, hi, hv, _⟩ := hX
      have wi : Pass.WholeIn V sp R Dst s :=
        ⟨he, e, hR, by rw [b, d, j, k]; exact hD, by rw [a, b, d, k]; exact hd, by rw [j, k]; exact hsd, hi, hv⟩
      refine WP.mono (Pass.pass_ok (L.v a b d) wi (by rw [i]; exact hl) hpos ?_) fun s' po =>
        OneOP.keep hP hT (fun r hr => (he.fr r hr).symm) po.env po.rd po.wr
      rw [ctxH_eq, a, b]; exact hH ▸ hx
  -- `cmp 112`
  obtain ⟨_, hc⟩ := cmp112_taint
  refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, _, _, h₁, _⟩, _, b₁, _⟩
    ⟨⟨_, _, _, d₂, _, _, _, _, _, _, h₂, _⟩, _, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [b₁, b₂]
  · rw [h₁.r31, h₂.r31, d₁, d₂]

end

/-- After the entry (and `r25` restored), what the pieces up to the
comparison of the tags need. -/
theorem split_one {t₀ s : State} (h : splitPre t₀) (h1 : SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s)
    (h19 : s.gpr .r19 = stackArg t₀ 1) :
    OneOP DOk (t₀.gpr .r3) (stackArg t₀ 2) t₀.sp (t₀.gpr .r4).toNat
      (t₀.gpr .r5) (t₀.gpr .r6).toNat (t₀.gpr .r7) (t₀.gpr .r8) (t₀.gpr .r9) (t₀.gpr .r10) (stackArg t₀ 0)
      (stackArg t₀ 1) s := by
  have hp := HeadPre.of_split h
  have hk₁ := h1.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine ⟨⟨s.gpr, h1.r29, h1.r30, h1.r31, by rw [h1.r28]; exact toN, by rw [h1.r18]; exact toN, h1.r21,
    h1.r22, h1.r27, h1.r23, one_env h1 hp.ctx hp.w, ?_, ?_, ?_⟩, h1.r20, h19, ?_⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.nonce, (t₀.gpr .r6).isLt, hp.fn,
      hp.dnW.sub_right (Lay.wSub (by decide)), hp.dnW⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.aad, (t₀.gpr .r8).isLt, hp.fa,
      hp.daW.sub_right (Lay.wSub (by decide)), hp.daW⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.data, (t₀.gpr .r10).isLt, hp.fd,
      hp.ddW.sub_right (Lay.wSub (by decide)), hp.ddW⟩
  · rw [hk₁.rd, hk₁.wr]; exact hp.tag

/-- After the entry, what the data's pass needs of the destination. -/
theorem split_dstx {t₀ s : State} (h : splitPre t₀) (h1 : SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s) :
    DstX (t₀.gpr .r3) (stackArg t₀ 2) t₀.sp (t₀.gpr .r9) (t₀.gpr .r10) (stackArg t₀ 3) s := by
  have hh := h
  obtain ⟨hrd, hwr, _, _, _, _, _, dWA, dcD, dsD, dDW, _, _, _, _, _, _, fD, _, _⟩ := hh
  have hk₁ := h1.en.keeps
  have hw : Covers [⟨stackArg t₀ 3, (t₀.gpr .r10).toNat⟩] s.wr := by rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  have hA : Covers [args t₀ 4] (t₀.rd ++ t₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hc : Region.Sub ⟨t₀.sp + BitVec.ofNat 64 120, 8⟩ (args t₀ 4) := by
    have := Offset.sub_base (stackArgAddr t₀ 0) (d := 24) (n := 8) (k := 8 * 4) (by decide)
    rwa [stackArgAddr_0, add_ofNat_assoc] at this
  refine ⟨⟨⟨covers_left hw, (t₀.gpr .r10).isLt, fD, dDW.sub_right (Lay.wSub (by decide)), dDW⟩, hw, dcD⟩, dsD,
    ?_, dst_at h (h1.en.frame.sub inW_saved), fun x hx₁ hx₂ => dWA x hx₂ (hc x hx₁)⟩
  rw [hk₁.rd, hk₁.wr]
  have := in_off hA (d := 24) (n := 8) (by decide) (by decide)
  rwa [stackArgAddr_0, add_ofNat_assoc] at this

theorem split_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    ConstantTime isa splitPPC64LE.pre splitPPC64LE.pub openSplit := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : splitPre σ₁ := h₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := h₁'
  let I₀ : State → Prop := fun s => splitPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.gpr .r10 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ (openRes s).isSome = (openRes σ₁).isSome ∧
    stackArg s 3 = stackArg σ₁ 3
  have i₁ : I₀ σ₁ := ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨I₀, i₁, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm,
    (qa 0 (by decide)).symm, (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, (qres hR).symm,
    (qa 3 (by decide)).symm⟩, ?_⟩
  clear q3 q4 q5 q6 q7 q8 q9 q10 qsp qa qres
  have hσ₁ := i₁
  have h0 : ∀ s, I₀ s → HeadPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧ s.gpr .r5 = σ₁.gpr .r5 ∧
      s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧ s.gpr .r9 = σ₁.gpr .r9 ∧
      s.gpr .r10 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧ stackArg s 1 = stackArg σ₁ 1 ∧
      stackArg s 2 = stackArg σ₁ 2 ∧ (openRes s).isSome = (openRes σ₁).isSome :=
    fun s ⟨hp, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres, _⟩ =>
      ⟨HeadPre.of_split hp, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩
  unfold openSplit
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s ∧
    s.gpr .r19 = stackArg t₀ 1
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openEntry_wp (h0 s hs).1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .r12 then stackArg σ₁ 2 else σ₁.gpr r
    have hl : openEntry = [.addSp .r12 0, .load .d .r12 .r12 112] ++ (save .r12 ++
        (([mov .r29 .r3, mov .r28 .r4, .addi .r30 .r31 16, mov .r24 .r5, mov .r25 .r6, mov .r18 .r6,
          mov .r21 .r7, mov .r22 .r8, mov .r27 .r9, mov .r23 .r10, .addSp .r12 0, .load .d .r20 .r12 96] :
          List Instr) ++ ([.load .d .r19 .r12 104] : List Instr))) := by
      rw [openEntry, oneEntry, List.append_assoc, List.append_assoc]
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := openHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s hs => ⟨(h0 s hs).2.2.2.2.2.2.2.2.2.1, by simp⟩) hc
    · intro s hs
      obtain ⟨hp, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, _, ea2, _⟩ := h0 s hs
      refine WP.mono (oneA_ok (W := stackArg s 2) (.inr rfl) (args_in hp.stk (by decide) (i := 2) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea2, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s₂ ∧
    s₂.gpr .r19 = stackArg t₀ 1 ∧ (∀ r, r ≠ .r0 → r ≠ .r25 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .r25 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 1) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.en.keeps.sp.trans (h0 t₀ ht).2.2.2.2.2.2.2.2.2.1, by simp [h19, (h0 t₀ ht).2.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .r19 = BitVec.ofNat 64 (stackArg t₀ 1).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 1).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, (h0 t₀ ht).2.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches, then `restore`
  have ev : ∀ s, J₂ s → isa.eval (.zero .d .r25) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have hpσ₁ := (h0 σ₁ hσ₁).1
  have L₀ := oneLay hpσ₁.fc hpσ₁.fW hpσ₁.dcW
  refine CT.seq (J := fun s => s.gpr .r31 = stackArg σ₁ 2 ∧ s.sp = σ₁.sp) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_))
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [.li .r3 0] (.inl rfl)
    exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
      ⟨k.sp.trans (h1.en.keeps.sp.trans (h0 t₀ ht).2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
  · have hok : ok = true := by
      cases e : ok
      · simp [e] at hb
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    unfold openPass
    refine CT.seq ?_ (fun s ⟨t₀, s₂, ht, h1, h19, g, k, _⟩ => ?_)
      (passRest_ct (sp := σ₁.sp) (Np := σ₁.gpr .r5) (n := (σ₁.gpr .r6).toNat) (Ad := σ₁.gpr .r7)
        (A := σ₁.gpr .r8) (S := σ₁.gpr .r9) (Ln := σ₁.gpr .r10) (T := stackArg σ₁ 0) (TL := stackArg σ₁ 1)
        (Dst := stackArg σ₁ 3) L₀ hpσ₁.hR (hpσ₁.dtW.sub_right (Lay.wSub (by decide))) t1 t16)
    · obtain ⟨_, hc⟩ := nil_taint [mov .r25 .r18] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.en.keeps.sp.trans (h0 t₀ ht).2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩ := h0 t₀ ht
      refine WP.of_runBlock ⟨_, rfl, ?_⟩
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k
      have o := split_one ht.1 h4 (h19₄.trans h19)
      have x := split_dstx ht.1 h4
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea1, ea2, esp] at o
      obtain ⟨_, _, _, _, _, _, _, e9', e10', esp', _, _, ea2', _, ea3'⟩ := ht
      rw [e3, e9', e10', ea2', ea3', esp'] at x
      refine ⟨⟨o, ?_, ?_⟩, x⟩
      · rw [h4.r24, e5]
      · rw [h4.r25, e6]; simp
  · obtain ⟨t₀, s₂, ht, h1, h19, g, k, h25⟩ := hs
    obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩ := h0 t₀ ht
    refine WP.ite _ (ev s ⟨t₀, s₂, ht, h1, h19, g, k, h25⟩) (fun ht' => ?_) (fun hf => ?_)
    · have h₀ : WP isa (.block [.li .r3 0]) s fun s' => (∀ r, r ≠ .r3 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₀ fun s' ⟨g', k'⟩ => ⟨by rw [g' _ (by decide), g _ (by decide) (by decide), h1.r31, ea2],
        by rw [k'.sp, k.sp, h1.en.keeps.sp, esp]⟩
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 1).toNat = true := by rw [ea1]; exact hok
      unfold openPass
      refine WP.seq (WP.of_runBlock ⟨_, rfl, ?_⟩)
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k
      exact WP.mono (pass_good ht.1 h4 (h19₄.trans h19) hok₀) fun s' oo =>
        ⟨by rw [oo.r31, ea2], by rw [oo.sp, esp]⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 2) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc


end VG.Proof.AesGcm.PPC64LE

end

end

/-!
# AES-GCM decryption out of place, in one pass, PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_open_to`, with the 2720 bytes of stack below the stack pointer
that its frame uses (`Proof.AesGcm.openToRoundsContract`), implies the one
the proof is written against (`toK`, `to_implies`), and so the code, calling
`vg_aes_gcm_open_split` by its contract (`split_correct`, `split_ct`), is
`Verified` against it (`openTo_verified`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.PPC64LE.OpenTo

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo

/-- `vg_aes_gcm_open_split` satisfies its contract. -/
theorem split_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] : SplitOk := fun _ hs => split_wp hs

theorem openTo_correct (hv : SplitOk) (s : State) (hs : toK.pre s) :
    ∃ t s', Exec isa openTo s t s' ∧ abiPreserved s s' ∧ toK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := openTo_wp hv hs
  exact ⟨t, s', he, ha, hp⟩

theorem toPre_of_spec {s : State} (h : (Proof.AesGcm.openToRoundsContract PPC64LE.abi 2720).pre s) : ToPre s := by
  sig_pre [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre, PPC64LE.abi, PPC64LE.argRegs,
    List.getD, List.range, List.range.loop] at h
  obtain ⟨w₁, w₂, rd, wr, kd, nd, ad, sd, dt, da, bk, bn, ba, bs, bd, bt, barg, ok, on, oa, os, od, ot, hR, dl⟩ := h
  rw [dl] at wr kd nd ad sd dt da bd od
  exact ⟨w₁, w₂, rd, wr, kd, nd, ad, sd, dt, da, bk, bn, ba, bs, bd, bt, barg, ok, on, oa, os, od, ot, hR, dl⟩

theorem toPost_of {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.openToRoundsContract PPC64LE.abi 2720).post s s' := by
  sig_post [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Proof.AesGcm.openToRoundsPost, PPC64LE.abi,
    PPC64LE.argRegs, List.range, List.range.loop]
  intro _
  exact h

theorem toPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.openToRoundsContract PPC64LE.abi 2720).pub s₁ s₂) :
    toPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToLeak, PPC64LE.abi,
    PPC64LE.argRegs, List.range, List.range.loop] at hp
  obtain ⟨qsp, ql, q3, q4, q5, q6, q7, q8, q9, q10, a0, a1, a2, a3⟩ := hp
  refine ⟨qsp, ql, q3, q4, q5, q6, q7, q8, q9, q10, fun i hi => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3]

/-- A state satisfying the precondition of `vg_aes_gcm_open_to`: no nonce,
additional data, text or tag, and all four stack arguments 0. -/
def toSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x9060, 32⟩]
  wr := [⟨0, 0⟩]

theorem toSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract PPC64LE.abi 2720).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr,
    List.getD, List.range, List.range.loop]
    [toSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using toSat

theorem to_implies : toK.Implies (Proof.AesGcm.openToRoundsContract PPC64LE.abi 2720) :=
  ⟨fun _ h => toPre_of_spec h, fun _ _ _ h => toPost_of h, fun _ _ _ _ h => toPub_of h, toSat_pre⟩

/-- `vg_aes_gcm_open_to`, calling `vg_aes_gcm_open_split` by its contract. -/
theorem openTo_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target openTo (Proof.AesGcm.openToRoundsContract PPC64LE.abi 2720) :=
  Verified.of_correct (k := toK) (openTo_correct split_correct) (openTo_ct split_correct split_ct)
    to_implies

end VG.Proof.AesGcm.PPC64LE.OpenTo
