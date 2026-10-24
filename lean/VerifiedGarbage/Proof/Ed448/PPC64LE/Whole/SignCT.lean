module

import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignCached
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.HashCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignCached
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.HashCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignChallenge
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignChallenge
meta import VerifiedGarbage.Proof.Ed448.Ref
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignNonce
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.PPC64LE.Ladder

/-!
# `vg_ed448_sign_cached` on PPC64LE in constant time

Two runs from states that satisfy `SignPre` and agree on the arguments (the
registers, the stack pointer and the stack argument, `SPub`) leak the same
trace (`sign_ct`). Each piece of the body is related from the invariants the
correctness proof gives each run (`S1`–`S4`): the hashes by `hash_ct`, the
code between them by the taint analysis (`ct_prog`) from the registers the
invariants give the same values in both runs, the callees' bodies included
(the Ed448 functions save and restore other registers than these).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv)
open VG.Proof.X25519.PPC64LE (Upd)

/-! ## Combinators -/

/-- Code the taint analysis checks from the registers `rs`, on which the runs agree. -/
theorem ct_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.PPC64LE.taint.T} (h : (VG.PPC64LE.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- A hash, then code the taint analysis checks from registers `rs` that the hash keeps (callee-saved), on which
the runs agree. -/
theorem hash_then {sc f : Reg} {o : Nat} {ps : List Piece} {P : State → State → Prop} {c : Prog isa}
    {hint : VG.Taint.Hint VG.PPC64LE.taint.T}
    (hz : (VG.PPC64LE.taint.check (Taint.ofRegs [sc]) (.block (Impl.MlKem.PPC64LE.zeroState sc)) hint).isSome =
      true)
    (hP : ∀ a b, P a b → HashOk sc f o ps a ∧ HashOk sc f o ps b ∧ a.sp = b.sp ∧
      ∀ r ∈ hashRegs sc f ps, a.gpr r = b.gpr r)
    (rs : List Reg) (hrs : ∀ a b, P a b → ∀ r ∈ rs, r ∈ preserved ∧ a.gpr r = b.gpr r)
    {hint₂ : VG.Taint.Hint VG.PPC64LE.taint.T} (hc : (VG.PPC64LE.taint.check (Taint.ofRegs rs) c hint₂).isSome = true) :
    RelCT isa P (.seq (hash sc ps f o) c) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ P x.1 x.2)
    (RelCT.exists_ fun ⟨t₁, t₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : P t₁ t₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨h₁, h₂, hsp, -⟩ := hP _ _ hH
  refine RelCT.mono (P := fun a b => a = t₁ ∧ b = t₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have hP' : ∀ a b, (a = t₁ ∧ b = t₂) → HashOk sc f o ps a ∧ HashOk sc f o ps b ∧ a.sp = b.sp ∧
      ∀ r ∈ hashRegs sc f ps, a.gpr r = b.gpr r := fun a b h => by
    obtain ⟨rfl, rfl⟩ := h; exact hP _ _ hH
  have hw : ∀ t, HashOk sc f o ps t → WP isa (hash sc ps f o) t (Rg t) := fun t ht =>
    WP.mono (hash_ok ht.psc ht.pf ht.po rfl rfl ht.env ht.ne ht.ins ht.w ht.dsc ht.dsp)
      fun _ ⟨k, _⟩ => ⟨k.rd, k.wr, k.sp, k.cs⟩
  refine RelCT.seq (R := fun a b => Rg t₁ a ∧ Rg t₂ b)
    (RelCT.mono (relct_wp (hash_ct hz hP') fun a b hab => ⟨by rw [hab.1]; exact hw _ h₁, by rw [hab.2]; exact hw _ h₂⟩)
      (fun _ _ h => h) (fun _ _ h => h)) ?_
  exact ct_prog rs (fun a b hab => hab.1.sp.trans (hsp.trans hab.2.sp.symm)) (fun a b hab r hr => by
    obtain ⟨hp, he⟩ := hrs _ _ hH r hr
    rw [hab.1.cs r hp, hab.2.cs r hp, he]) hc

/-! ## The runs' agreement -/

/-- What two runs agree on: the arguments. -/
def SPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem signV_eq {s₁ s₂ : State} (hp : SPub s₁ s₂) : ∀ r ∈ signRegs, signV s₁ r = signV s₂ r := by
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, p10, -, pf⟩ := hp
  intro r hr
  simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [p3, p10, p4, p5, p6, p7, p8, p9, pf]

theorem inv_regs {s₁ s₂ a b : State} (hp : SPub s₁ s₂) (ha : SInv s₁ a) (hb : SInv s₂ b) :
    ∀ r ∈ signRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((signV_eq hp r hr).trans (hb.regs r hr).symm)

theorem inv_sp {s₁ s₂ a b : State} (hp : SPub s₁ s₂) (ha : SInv s₁ a) (hb : SInv s₂ b) : a.sp = b.sp :=
  ha.sp.trans (hp.2.2.2.2.2.2.2.2.1.trans hb.sp.symm)

/-- From what the hashes keep. -/
theorem rg_regs {s₁ s₂ t₁ t₂ a b : State} (hp : SPub s₁ s₂) (h₁ : SInv s₁ t₁) (h₂ : SInv s₂ t₂) (ha : Rg t₁ a)
    (hb : Rg t₂ b) : ∀ r ∈ signRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.cs r (signRegs_pres r hr)).trans ((inv_regs hp h₁ h₂ r hr).trans (hb.cs r (signRegs_pres r hr)).symm)

theorem rg_sp {s₁ s₂ t₁ t₂ a b : State} (hp : SPub s₁ s₂) (h₁ : SInv s₁ t₁) (h₂ : SInv s₂ t₂) (ha : Rg t₁ a)
    (hb : Rg t₂ b) : a.sp = b.sp := ha.sp.trans ((inv_sp hp h₁ h₂).trans hb.sp.symm)

theorem sub_regs {rs : List Reg} (h : ∀ r ∈ rs, r ∈ signRegs) {g₁ g₂ : Reg → BitVec 64}
    (he : ∀ r ∈ signRegs, g₁ r = g₂ r) : ∀ r ∈ rs, g₁ r = g₂ r := fun r hr => he r (h r hr)

/-! ## The hashes' preconditions -/

section
variable {s : State} (hp : SignPre s)
include hp

theorem hashOk_of {t : State} (h : SInv s t) {o : Nat} (ho : o + 114 ≤ 464) (ho' : o < 2 ^ 15) {ps : List Piece}
    (hne : ps ≠ []) (hps : ∀ p ∈ ps, PieceOk (s.gpr .r10) t p) : HashOk .r22 .r21 o ps t := by
  have g29 : t.gpr .r22 = s.gpr .r10 := h.regs _ (by decide)
  have g30 : t.gpr .r21 = sF s := h.regs _ (by decide)
  exact ⟨by decide, by decide, ho', hne, by rw [g29]; exact kenv hp h, by rw [g29]; exact hps,
    by rw [g30]; exact cov_in (fF hp h) ho, by rw [g30, g29]; exact fsc hp ho,
    by rw [g30, h.sp]; exact fbelow hp ho⟩

theorem S1.hashOk {t : State} (h : S1 s t) : HashOk .r22 .r21 136 [⟨.r23, 0, .imm 57⟩] t := by
  have g21 : t.gpr .r23 = s.gpr .r4 := h.inv.regs _ (by decide)
  refine hashOk_of hp h.inv (by decide) (by decide) (by simp) fun p hp' => ?_
  rw [List.mem_singleton.mp hp']
  exact pieceOk_of (R := sdR s) (by simp only [Piece.R, Piece.addr, Len.val, g21, BitVec.add_zero]) (by decide)
    (by decide) (show 57 < 2 ^ 15 by decide)
    (by rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
    hp.cS.symm (by rw [h.inv.sp]; exact hp.bS)

theorem S2.hashOk {t : State} (h : S2 s t) :
    HashOk .r22 .r21 16 (dom4Pieces .r21 .r25 .r28 ++ [⟨.r21, 193, .imm 57⟩, ⟨.r29, 0, .reg .r30⟩]) t := by
  refine hashOk_of hp h.inv (by decide) (by decide) (by simp [dom4Pieces]) fun p hp' => ?_
  simp only [dom4Pieces, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl
  · exact (fPiece0 hp h.inv).1
  · exact (ctxPiece hp h.inv).1
  · exact (fPiece hp h.inv (d := 193) (n := 57) (by decide) (by decide) (by decide)).1
  · exact (msgPiece hp h.inv).1

theorem S3.hashOk {t : State} (h : S3 s t) :
    HashOk .r22 .r21 16 (dom4Pieces .r21 .r25 .r28 ++ [⟨.r20, 0, .imm 57⟩, ⟨.r24, 0, .imm 57⟩, ⟨.r29, 0, .reg .r30⟩])
      t := by
  have g20 : t.gpr .r20 = s.gpr .r3 := h.inv.regs _ (by decide)
  have g22 : t.gpr .r24 = s.gpr .r5 := h.inv.regs _ (by decide)
  have hO57 : Region.Sub ⟨s.gpr .r3, 57⟩ (oR s) := Region.sub_prefix (by decide)
  refine hashOk_of hp h.inv (by decide) (by decide) (by simp [dom4Pieces]) fun p hp' => ?_
  simp only [dom4Pieces, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · exact (fPiece0 hp h.inv).1
  · exact (ctxPiece hp h.inv).1
  · exact pieceOk_of (R := ⟨s.gpr .r3, 57⟩) (by simp only [Piece.R, Piece.addr, Len.val, g20, BitVec.add_zero])
      (by decide) (by decide) (show 57 < 2 ^ 15 by decide) (cov_right (cov_in0 (fO hp h.inv) (by decide)))
      (hp.oC.sub_left hO57) (by rw [h.inv.sp]; exact hp.bO.sub_right hO57)
  · exact pieceOk_of (R := pkR s) (by simp only [Piece.R, Piece.addr, Len.val, g22, BitVec.add_zero])
      (by decide) (by decide) (show 57 < 2 ^ 15 by decide)
      (by rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
      hp.cP.symm (by rw [h.inv.sp]; exact hp.bP)
  · exact (msgPiece hp h.inv).1

end

/-! ## The pieces -/

section
variable {s₁ s₂ : State} (hp₁ : SignPre s₁) (hp₂ : SignPre s₂) (hpub : SPub s₁ s₂)
include hp₁ hp₂ hpub

theorem expand_ct : RelCT isa (fun a b => S1 s₁ a ∧ S1 s₂ b) signExpand fun _ _ => True :=
  hash_then (by taint_decide) (fun a b h => ⟨h.1.hashOk hp₁, h.2.hashOk hp₂, inv_sp hpub h.1.inv h.2.inv,
    sub_regs (by decide) (inv_regs hpub h.1.inv h.2.inv)⟩) [.r21] (fun a b h r hr =>
      ⟨signRegs_pres r (by revert r; decide), inv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
    (by taint_decide)

theorem nonce_ct : RelCT isa (fun a b => S2 s₁ a ∧ S2 s₂ b) signNonce fun _ _ => True :=
  hash_then (by taint_decide) (fun a b h => ⟨h.1.hashOk hp₁, h.2.hashOk hp₂, inv_sp hpub h.1.inv h.2.inv,
    sub_regs (by decide) (inv_regs hpub h.1.inv h.2.inv)⟩) [.r20, .r22, .r21] (fun a b h r hr =>
      ⟨signRegs_pres r (by revert r; decide), inv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
    (by taint_decide)

theorem challenge_ct : RelCT isa (fun a b => S3 s₁ a ∧ S3 s₂ b) signChallenge fun _ _ => True :=
  hash_then (by taint_decide) (fun a b h => ⟨h.1.hashOk hp₁, h.2.hashOk hp₂, inv_sp hpub h.1.inv h.2.inv,
    sub_regs (by decide) (inv_regs hpub h.1.inv h.2.inv)⟩) [.r20, .r22, .r21] (fun a b h r hr =>
      ⟨signRegs_pres r (by revert r; decide), inv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
    (by taint_decide)

end

/-! ## The whole body -/

theorem signCached_ct (hl : Proof.Ed448.BaseLadder2Ok) :
    ConstantTime isa SignPre SPub signCached := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ SignPre x.1 ∧ SignPre x.2 ∧
    SPub x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : SignPre s₁ ∧ SignPre s₂ ∧ SPub s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hp₁, hp₂, hpub⟩ := hH
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have pub := hpub
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, p10, psp, pf⟩ := pub
  unfold signCached
  -- `F`.
  let F₁ := fun u => Upd s₁ u .r12 (sF s₁) ∧ u.lr = s₁.lr
  let F₂ := fun u => Upd s₂ u .r12 (sF s₂) ∧ u.lr = s₂.lr
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b)
    (RelCT.mono (relct_wp (taint_block [] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact frame_ok hp₁ fun u hu hl => WP.block_nil ⟨hu, hl⟩,
       by rw [hab.2]; exact frame_ok hp₂ fun u hu hl => WP.block_nil ⟨hu, hl⟩⟩) (fun _ _ h => h) fun _ _ h => h) ?_
  -- The setup.
  refine RelCT.seq (R := fun a b => S1 s₁ a ∧ S1 s₂ b)
    (relct_wp (ct_prog [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12] (fun a b hab => by
      rw [hab.1.1.sp, hab.2.1.sp, psp]) (fun a b hab r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (hab.1.1.gpr.trans pf).trans hab.2.1.gpr.symm
        | rw [hab.1.1.other _ (by decide), hab.2.1.other _ (by decide)]; assumption) (by taint_decide))
      fun a b hab => ⟨signSetup_ok hp₁ hab.1.1 hab.1.2, signSetup_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- The steps.
  refine RelCT.seq (R := fun a b => S2 s₁ a ∧ S2 s₂ b)
    (relct_wp (expand_ct hp₁ hp₂ hpub) fun a b hab => ⟨expand_ok hp₁ hab.1, expand_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => S3 s₁ a ∧ S3 s₂ b)
    (relct_wp (nonce_ct hp₁ hp₂ hpub) fun a b hab => ⟨nonce_ok hl hp₁ hab.1, nonce_ok hl hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => S4 s₁ a ∧ S4 s₂ b)
    (relct_wp (challenge_ct hp₁ hp₂ hpub) fun a b hab => ⟨challenge_ok hp₁ hab.1, challenge_ok hp₂ hab.2⟩) ?_
  -- The wipe and the restores.
  exact ct_prog [.r21] (fun a b hab => inv_sp hpub hab.1.inv hab.2.inv)
    (fun a b hab => sub_regs (by decide) (inv_regs hpub hab.1.inv hab.2.inv)) (by taint_decide)

end VG.Proof.Ed448.PPC64LE.Whole
