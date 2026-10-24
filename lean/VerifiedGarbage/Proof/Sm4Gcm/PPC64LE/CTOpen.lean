module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTOne
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Open
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTSeal
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Seal
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTOne
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTSeal
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Open
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.InitCT
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Seal
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_open` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTOpen.lean`): `open` branches on the tag length, which
is public, and on whether the tags are equal, which it may leak (its
contract's `pub`: whether it succeeds). The invariants of the pieces up to
that comparison carry what the rest of each run reaches (`CT.seqG`, from
`open_head`): the result in `r19`, which is then the same in both runs.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov oneAad recv cmp tagLenOk save restore)
open VG.Proof.AesGcm.PPC64LE (CT ct_of CT.seqG Env Env.self Lay Keeps DataW frozen covers_mem covers_left
  covers_off covers_prefix oneLay args_in oneAad_ok length_bytesAt recv_ok cmp_ok tagLenOk_ok tagLenOk_bounds
  eval_zero recv_taint tagLenOk_taint' cmp112_taint nil_taint Res WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

theorem openRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (stackArg t 0).toNat = true) :
    (openRes t).isSome = decide (openTagOk t) := by
  have e : openRes t = if openTagOk t then
      some (Spec.Gcm.gctr (Spec.Sm4.Gcm.ctxCiph t.mem (t.gpr .r3))
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (t.gpr .r3)) (bytesAt t.mem (t.gpr .r4) (t.gpr .r5).toNat)))
        (bytesAt t.mem (t.gpr .r8) (t.gpr .r9).toNat)) else none := by
    simp only [openRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : openTagOk t
  · simp only [eq_true h, ite_true, decide_true, Option.isSome_some]
  · simp only [eq_false h, ite_false, decide_false, Option.isSome_none]

theorem openHead_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [])
    (.block [.addSp .r12 0, .load .d .r12 .r12 104]) h).isSome = true := ⟨_, by taint_decide⟩

theorem openRest_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12])
    (.block (save .r12 ++ (([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5,
      mov .r21 .r6, mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10, .addSp .r12 0,
      .load .d .r28 .r12 (104 + 8)] : List Instr) ++
      ([.addSp .r12 0, .load .d .r19 .r12 96] : List Instr)))) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `OneI`, with the tag's address `T` and length `TL` in `r20` and `r19`. -/
def OneO (c W x sp : Addr) (Np : Addr) (n : Nat) (Ad A D Ln T TL : BitVec 64) (s : State) : Prop :=
  OneI c W x sp Np n Ad A D Ln s ∧ s.gpr .r20 = T ∧ s.gpr .r19 = TL ∧ Covers [⟨T, TL.toNat⟩] (s.rd ++ s.wr)

section
variable {c W x sp : Addr} {Np : Addr} {n : Nat} {Ad A D Ln T TL : BitVec 64}

theorem OneO.keep {s s' : State} (h : OneO c W x sp Np n Ad A D Ln T TL s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    OneO c W x sp Np n Ad A D Ln T TL s' :=
  ⟨h.1.keep hV he hrd hwr, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.2.1), by rw [hrd, hwr]; exact h.2.2.2⟩

/-- `OneI` after a step that changes only `r19` among the registers it pins. -/
theorem OneI.self {s s' : State} (h : OneI c W x sp Np n Ad A D Ln s) (hg : ∀ r, r ≠ .r19 → s'.gpr r = s.gpr r)
    (hk : Keeps s s') : OneI c W x sp Np n Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := h
  have q : ∀ r ∈ frozen, r ≠ .r19 → s'.gpr r = V r := fun r hr h19 => (hg r h19).trans (he.fr r hr)
  refine ⟨s'.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Env.self he hg hk, hN.of_eq hk.rd hk.wr, hA.of_eq hk.rd hk.wr,
    hD.of_eq hk.rd hk.wr⟩
  · rw [q _ (by decide) (by decide), a]
  · rw [q _ (by decide) (by decide), b]
  · rw [q _ (by decide) (by decide), d]
  · rw [q _ (by decide) (by decide), e]
  · rw [q _ (by decide) (by decide), f]
  · rw [q _ (by decide) (by decide), g]
  · rw [q _ (by decide) (by decide), i]
  · rw [q _ (by decide) (by decide), j]
  · rw [q _ (by decide) (by decide), k]

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (X : XOk c (W + BitVec.ofNat 64 16) W x)
  (hTd : (⟨T, TL.toNat⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) (t1 : 1 ≤ TL.toNat) (t16 : TL.toNat ≤ 16)
  (b : Bool)
include L X hTd t1 t16

/-- `open` from `oneAad` on, once the tag length is allowed, with what the
comparison of the tags gives (`Res b`). -/
theorem openGood_ct : CT (fun s => (OneO c W x sp Np n Ad A D Ln T TL s ∧ s.gpr .r24 = Np ∧
    s.gpr .r25 = BitVec.ofNat 64 n) ∧ WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112)
      (.seq (.block [mov .r19 .r3]) (.block [])))))) s (Res b))
    (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3])
      (.seq (.ite (.zero .d .r19) (.block []) oneCrypt) (.block [mov .r3 .r19]))))))) := by
  -- `oneAad`
  refine CT.seqG (J := fun s => OneO c W x sp Np n Ad A D Ln T TL s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, g, i]; exact hA))) fun s' ⟨oa, rd, wr, _⟩ => ⟨hT.keep (fun r hr => (he.fr r hr).symm) oa.env rd wr,
        blockAt s.mem (V .r29 + BitVec.ofNat 64 240), bytesAt s.mem (V .r21) (V .r22).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneTag 112`
  refine CT.seqG (J := OneO c W x sp Np n Ad A D Ln T TL) ((oneTag_ct L X (.inr rfl)).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    have X' : XOk (V .r29) (V .r30) (V .r31) (V .r28) := by rw [a, b, d, e]; exact X
    exact WP.mono (WP.with_rdwr (oneTag_ok (L.v a b d) X' (o := 112) (.inr rfl) (H := H) (a := x) he
      (by rw [e]; exact hD.xw) (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab)
      (by rw [b, d, j, k]; exact hD.dw.ok)))
      fun s' ⟨ot, rd, wr, _⟩ => hT.keep (fun r hr => (he.fr r hr).symm) ot.env rd wr
  -- `recv`
  refine CT.seqG (J := OneO c W x sp Np n Ad A D Ln T TL) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, _, _, h₁, _⟩, a₁, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, _, _, h₂, _⟩, a₂, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [a₁, a₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    have h19 : V .r19 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    have h20 : V .r20 = T := by rw [← he.fr _ (by decide), hT.2.1]
    exact WP.mono (recv_ok he h19 t1 t16 (by rw [h20]; exact hT.2.2.2) (by rw [h20, d]; exact hTd))
      fun s' ⟨_, _, g', k'⟩ => hT.keep (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr
  -- `cmp 112`
  refine CT.seqG (J := OneO c W x sp Np n Ad A D Ln T TL) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := cmp112_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, _, _, h₁, _⟩, _, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, _, _, h₂, _⟩, _, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [b₁, b₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    have h19 : V .r19 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    exact WP.mono (cmp_ok he (o := 112) (.inr rfl) h19 t1 t16)
      fun s' ⟨_, _, g', k'⟩ => hT.keep (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr
  -- the result into `r19`
  refine CT.seqG (J := OneI c W x sp Np n Ad A D Ln) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [mov .r19 .r3] (.inr (.inr (.inl rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨⟨_, _, _, _, _, _, _, _, _, _, h₁, _⟩, _⟩ => ⟨h₁.sp, by simp⟩) hc
  · refine WP.of_runBlock ⟨_, rfl, hT.1.self (fun r hr => ?_) ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    simp [State.write, hr]
  -- the data decrypted only if the tags are equal, which both runs agree on
  have ev : ∀ s, OneI c W x sp Np n Ad A D Ln s ∧ WP isa (.block []) s (Res b) →
      isa.eval (.zero .d .r19) s = some (decide ((if b then 1 else 0) = 0)) := fun s h =>
    eval_zero (WP.block_nil_iff.mp h.2) (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .r31 = W ∧ s.sp = sp)
    (CT.ite _ ev (fun _ => CT.skip) (fun _ => (oneCrypt_ct L X).mono fun s h => h.1)) (fun s h => ?_) ?_
  · obtain ⟨V, a, b', d, e, f, g, i, j, k, he, hN, hA, hD⟩ := h.1
    refine WP.ite _ (ev s h) (fun _ => WP.block_nil_iff.mpr ⟨by rw [he.r31, d], he.sp⟩) (fun _ => ?_)
    have X' : XOk (V .r29) (V .r30) (V .r31) (V .r28) := by rw [a, b', d, e]; exact X
    exact WP.mono (oneCrypt_ok (L.v a b' d) X' he (by rw [a, b', d, j, k]; exact hD.dw) (by rw [e]; exact hD.xw)
      (by rw [j, k, e]; exact hD.dx) rfl)
      fun s' oc => ⟨by rw [oc.env.r31, d], oc.env.sp⟩
  · obtain ⟨_, hc⟩ := nil_taint [mov .r3 .r19] (.inr (.inr (.inr rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨_, hsp⟩ => ⟨hsp, by simp⟩) hc

end

/-- `mov r25 r18` after `tagLenOk`: the entry's registers again. -/
theorem mov25_so1 {W X : Addr} {t₀ s₂ s₃ : State} (h2 : SO1 W X t₀ s₂)
    (g : ∀ r, r ≠ .r0 → r ≠ .r25 → s₃.gpr r = s₂.gpr r) (k : Keeps s₂ s₃) :
    SO1 W X t₀ (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)) ∧
      (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)).gpr .r19 = s₂.gpr .r19 := by
  have e19 : (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)).gpr .r19 = s₃.gpr .r19 := by simp [State.write]
  refine ⟨h2.keep (fun r h0 _ _ => ?_) ⟨k.mem, k.rd, k.wr, k.sp, k.lr⟩, by rw [e19, g _ (by decide) (by decide)]⟩
  by_cases e : r = .r25
  · subst e
    have : (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)).gpr .r25 = s₃.gpr .r18 := by simp [State.write]
    rw [this, g _ (by decide) (by decide), h2.r18, h2.r25]
  · have : (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)).gpr r = s₃.gpr r := by simp [State.write, e]
    rw [this, g r h0 e]

/-- After the entry (and `r25` restored), what the pieces need. -/
theorem open_one {t₀ s : State} (h : openPre t₀) (h1 : SO1 (stackArg t₀ 1) (stackArg t₀ 2) t₀ s)
    (h19 : s.gpr .r19 = stackArg t₀ 0) :
    OneO (t₀.gpr .r3) (stackArg t₀ 1) (stackArg t₀ 2) t₀.sp (t₀.gpr .r4) (t₀.gpr .r5).toNat (t₀.gpr .r6)
        (t₀.gpr .r7) (t₀.gpr .r8) (t₀.gpr .r9) (t₀.gpr .r10) (stackArg t₀ 0) s ∧
      s.gpr .r24 = t₀.gpr .r4 ∧ s.gpr .r25 = BitVec.ofNat 64 (t₀.gpr .r5).toNat := by
  obtain ⟨hrd, hwr, dcd, -, -, dnW, -, daW, -, ddW, -, -, -, -, fn, fa, fd, -, -, -, -, -, -, ddx, -, -, -, -⟩ := h
  have hC : Covers [⟨t₀.gpr .r3, 256⟩] (t₀.rd ++ t₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW' : Covers [⟨stackArg t₀ 1, scrBytes⟩] t₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hW : Covers [⟨stackArg t₀ 1, 2560⟩] t₀.wr := covers_prefix hW' (by decide)
  have hk₁ := h1.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨t₀.gpr .r8, (t₀.gpr .r9).toNat⟩] s.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  have hX₁ : Covers [xR (stackArg t₀ 2)] s.wr := by rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  refine ⟨⟨⟨s.gpr, h1.r29, h1.r30, h1.r31, h1.r28, by rw [h1.r18]; exact toN, h1.r21,
    h1.r22, h1.r27, h1.r23, one_env h1 hC hW, ?_, ?_, ⟨⟨⟨covers_left hDw, (t₀.gpr .r9).isLt, fd,
      ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw, dcd⟩, hX₁, ddx⟩⟩, h1.r20, h19, ?_⟩, h1.r24,
    by rw [h1.r25]; exact toN⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .r5).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .r7).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  · rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))

theorem open_ct : ConstantTime isa openPPC64LE.pre openPPC64LE.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : openPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, _, fW, _, dcx, _, _, _, _, dwx, _, fx⟩ := h₁'
  let I₀ : State → Prop := fun s => openPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.gpr .r10 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ (openRes s).isSome = (openRes σ₁).isSome
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm,
    q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm,
    (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, qres.symm⟩, ?_⟩
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO1 (stackArg t₀ 1) (stackArg t₀ 2) t₀ s ∧
    s.gpr .r19 = stackArg t₀ 0
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openEntry_wp hs.1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .r12 then stackArg σ₁ 1 else σ₁.gpr r
    have hl : openEntry = [.addSp .r12 0, .load .d .r12 .r12 104] ++ (save .r12 ++
        (([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5,
          mov .r21 .r6, mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10, .addSp .r12 0,
          .load .d .r28 .r12 (104 + 8)] : List Instr) ++ ([.addSp .r12 0, .load .d .r19 .r12 96] : List Instr))) := by
      rw [openEntry, oneEntry, List.append_assoc, List.append_assoc]
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := openHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, ea1, _, _⟩
      have hA : Covers [args s 3] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      refine WP.mono (oneA_ok (W := stackArg s 1) (.inr rfl) (args_in hA (by decide) (i := 1) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea1, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 0).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO1 (stackArg t₀ 1) (stackArg t₀ 2) t₀ s₂ ∧
    s₂.gpr .r19 = stackArg t₀ 0 ∧ (∀ r, r ≠ .r0 → r ≠ .r25 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .r25 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 0) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.en.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1, by simp [h19, ht.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .r19 = BitVec.ofNat 64 (stackArg t₀ 0).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 0).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, ht.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches, then `restore`
  have ev : ∀ s, J₂ s → isa.eval (.zero .d .r25) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have L₀ := oneLay fc fW dcW
  have X₀ := oneX fx dcx dwx
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine CT.seq (J := fun s => s.gpr .r31 = stackArg σ₁ 1 ∧ s.sp = σ₁.sp) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_))
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [.li .r3 0] (.inl rfl)
    exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
      ⟨k.sp.trans (h1.en.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
  · have hok : ok = true := by
      cases e : ok
      · simp [e] at hb
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    refine CT.seq ?_ (fun s ⟨t₀, s₂, ht, h1, h19, g, k, _⟩ => ?_)
      (openGood_ct (sp := σ₁.sp) (Np := σ₁.gpr .r4) (n := (σ₁.gpr .r5).toNat) (Ad := σ₁.gpr .r6) (A := σ₁.gpr .r7)
        (D := σ₁.gpr .r8) (Ln := σ₁.gpr .r9) L₀ X₀ (dtW.sub_right (Lay.wSub (by decide))) t1 t16
        (openRes σ₁).isSome)
    · obtain ⟨_, hc⟩ := nil_taint [mov .r25 .r18] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.en.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩ := ht
      refine WP.of_runBlock ⟨_, rfl, ?_⟩
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 0).toNat = true := by rw [ea0]; exact hok
      have o := open_one hpre h4 (h19₄.trans h19)
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea1, ea2, esp] at o
      refine ⟨o, open_head hpre h4 (h19₄.trans h19) hok₀ (T := .block []) fun s₉ om => WP.block_nil_iff.mpr ?_⟩
      show s₉.gpr .r19 = _
      rw [om.r19, ← eres, openRes_isSome hok₀]
      by_cases hx : openTagOk t₀
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  · obtain ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩, h1, h19, g, k, h25⟩ := hs
    refine WP.ite _ (ev s ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩, h1, h19, g, k, h25⟩)
      (fun ht => ?_) (fun hf => ?_)
    · have h₀ : WP isa (.block [.li .r3 0]) s fun s' => (∀ r, r ≠ .r3 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₀ fun s' ⟨g', k'⟩ => ⟨by rw [g' _ (by decide), g _ (by decide) (by decide), h1.r31, ea1],
        by rw [k'.sp, k.sp, h1.en.keeps.sp, esp]⟩
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 0).toNat = true := by rw [ea0]; exact hok
      refine WP.seq (WP.of_runBlock ⟨_, rfl, ?_⟩)
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k
      exact WP.mono (open_good hpre h4 (h19₄.trans h19) hok₀) fun s' oo =>
        ⟨by rw [oo.r31, ea1], by rw [oo.sp, esp]⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 1) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.PPC64LE
