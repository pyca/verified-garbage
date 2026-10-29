module

public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignNonce
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.HashCT
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignChallenge
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Common
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignNonce
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.HashCT
meta import VerifiedGarbage.Proof.Ed448.Ref
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignCached
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignChallenge
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit

/-!
# `vg_ed448_sign_cached` on RISC-V in constant time

As on PPC64LE (`Proof/Ed448/PPC64LE/Whole/SignCT.lean`): two runs from
states that satisfy `SignPre` and agree on the arguments (the registers, the
stack pointer and the stack argument, `SPub`) leak the same trace
(`signCached_ct`). Each piece of the body is related from the invariants the
correctness proof gives each run (`S1`–`S4`): the hashes by `hash_ct`, the
code between them by the taint analysis (`ct_prog`) from the registers the
invariants give the same values in both runs, the callees' bodies included
(the Ed448 functions save and restore other registers than these).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64.Whole
open VG.Proof.Ed25519.RISCV64.Whole (Inv)
open VG.RISCV64.Steps (Upd)

/-! ## Combinators -/

/-- Code the taint analysis checks from the registers `rs`, on which the runs agree. -/
theorem ct_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- A hash, then code the taint analysis checks from registers `rs` that the hash keeps (callee-saved), on which
the runs agree. -/
theorem hash_then {sc f : Reg} {o : Nat} {ps : List Piece} {P : State → State → Prop} {c : Prog isa}
    {hint : VG.Taint.Hint taint.T}
    (hz : (taint.check (Taint.ofRegs [sc]) (.block (Impl.Sha3.RISCV64.zeroState sc)) hint).isSome = true)
    (hP : ∀ a b, P a b → HashOk sc f o ps a ∧ HashOk sc f o ps b ∧ a.sp = b.sp ∧
      ∀ r ∈ hashRegs sc f ps, a.gpr r = b.gpr r)
    (rs : List Reg) (hrs : ∀ a b, P a b → ∀ r ∈ rs, r ∈ preserved ∧ a.gpr r = b.gpr r)
    {hint₂ : VG.Taint.Hint taint.T} (hc : (taint.check (Taint.ofRegs rs) c hint₂).isSome = true) :
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
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem signV_eq {s₁ s₂ : State} (hp : SPub s₁ s₂) : ∀ r ∈ signRegs, signV s₁ r = signV s₂ r := by
  obtain ⟨p0, p1, -, p3, p4, p5, p6, p7, -, pf⟩ := hp
  intro r hr
  simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [p0, p7, p1, p3, p4, p5, p6, pf]

theorem inv_regs {s₁ s₂ a b : State} (hp : SPub s₁ s₂) (ha : SInv s₁ a) (hb : SInv s₂ b) :
    ∀ r ∈ signRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((signV_eq hp r hr).trans (hb.regs r hr).symm)

theorem inv_sp {s₁ s₂ a b : State} (hp : SPub s₁ s₂) (ha : SInv s₁ a) (hb : SInv s₂ b) : a.sp = b.sp :=
  ha.sp.trans (hp.2.2.2.2.2.2.2.2.1.trans hb.sp.symm)

theorem sub_regs {rs : List Reg} (h : ∀ r ∈ rs, r ∈ signRegs) {g₁ g₂ : Reg → BitVec 64}
    (he : ∀ r ∈ signRegs, g₁ r = g₂ r) : ∀ r ∈ rs, g₁ r = g₂ r := fun r hr => he r (h r hr)

/-! ## The hashes' preconditions -/

section
variable {s : State} (hp : SignPre s)
include hp

theorem hashOk_of {t : State} (h : SInv s t) {o : Nat} (ho : o + 114 ≤ 520) (ho' : o < 2048) {ps : List Piece}
    (hne : ps ≠ []) (hps : ∀ p ∈ ps, PieceOk (s.gpr .a7) t p) : HashOk .s1 .s11 o ps t := by
  have g29 : t.gpr .s1 = s.gpr .a7 := h.regs _ (by decide)
  have g30 : t.gpr .s11 = sF s := h.regs _ (by decide)
  exact ⟨by decide, by decide, ho', hne, by rw [g29]; exact kenv hp h, by rw [g29]; exact hps,
    by rw [g30]; exact cov_in (fF hp h) ho, by rw [g30, g29]; exact fsc hp ho,
    by rw [g30, h.sp]; exact fbelow hp ho⟩

theorem S1.hashOk {t : State} (h : S1 s t) : HashOk .s1 .s11 136 [⟨.s2, 0, .imm 57⟩] t := by
  have g21 : t.gpr .s2 = s.gpr .a1 := h.inv.regs _ (by decide)
  refine hashOk_of hp h.inv (by decide) (by decide) (by simp) fun p hp' => ?_
  rw [List.mem_singleton.mp hp']
  exact pieceOk_of (R := sdR s) (by simp only [Piece.R, Piece.addr, Len.val, g21, BitVec.add_zero]) (by decide)
    (by decide) (show 57 < 2048 by decide)
    (by rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
    hp.cS.symm (by rw [h.inv.sp]; exact hp.bS)

theorem S2.hashOk {t : State} (h : S2 s t) :
    HashOk .s1 .s11 16 (dom4Pieces .s11 .s7 .s8 ++ [⟨.s11, 193, .imm 57⟩, ⟨.s9, 0, .reg .s10⟩]) t := by
  refine hashOk_of hp h.inv (by decide) (by decide) (by simp [dom4Pieces]) fun p hp' => ?_
  simp only [dom4Pieces, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl
  · exact (fPiece0 hp h.inv).1
  · exact (ctxPiece hp h.inv).1
  · exact (fPiece hp h.inv (d := 193) (n := 57) (by decide) (by decide) (by decide)).1
  · exact (msgPiece hp h.inv).1

theorem S3.hashOk {t : State} (h : S3 s t) :
    HashOk .s1 .s11 16 (dom4Pieces .s11 .s7 .s8 ++ [⟨.s0, 0, .imm 57⟩, ⟨.s11, 384, .imm 57⟩, ⟨.s9, 0, .reg .s10⟩])
      t := by
  have g20 : t.gpr .s0 = s.gpr .a0 := h.inv.regs _ (by decide)
  have hO57 : Region.Sub ⟨s.gpr .a0, 57⟩ (oR s) := Region.sub_prefix (by decide)
  refine hashOk_of hp h.inv (by decide) (by decide) (by simp [dom4Pieces]) fun p hp' => ?_
  simp only [dom4Pieces, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · exact (fPiece0 hp h.inv).1
  · exact (ctxPiece hp h.inv).1
  · exact pieceOk_of (R := ⟨s.gpr .a0, 57⟩) (by simp only [Piece.R, Piece.addr, Len.val, g20, BitVec.add_zero])
      (by decide) (by decide) (show 57 < 2048 by decide) (cov_right (cov_in0 (fO hp h.inv) (by decide)))
      (hp.oC.sub_left hO57) (by rw [h.inv.sp]; exact hp.bO.sub_right hO57)
  · exact (fPiece hp h.inv (d := 384) (n := 57) (by decide) (by decide) (by decide)).1
  · exact (msgPiece hp h.inv).1

end

/-! ## The pieces -/

section
variable {s₁ s₂ : State} (hp₁ : SignPre s₁) (hp₂ : SignPre s₂) (hpub : SPub s₁ s₂)
include hp₁ hp₂ hpub

theorem expand_ct : RelCT isa (fun a b => S1 s₁ a ∧ S1 s₂ b) signExpand fun _ _ => True :=
  hash_then (by taint_decide) (fun a b h => ⟨h.1.hashOk hp₁, h.2.hashOk hp₂, inv_sp hpub h.1.inv h.2.inv,
    sub_regs (by decide) (inv_regs hpub h.1.inv h.2.inv)⟩) [.s11] (fun a b h r hr =>
      ⟨signRegs_pres r (by revert r; decide), inv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
    (by taint_decide)

theorem nonce_ct : RelCT isa (fun a b => S2 s₁ a ∧ S2 s₂ b) signNonce fun _ _ => True :=
  hash_then (by taint_decide) (fun a b h => ⟨h.1.hashOk hp₁, h.2.hashOk hp₂, inv_sp hpub h.1.inv h.2.inv,
    sub_regs (by decide) (inv_regs hpub h.1.inv h.2.inv)⟩) [.s0, .s1, .s11] (fun a b h r hr =>
      ⟨signRegs_pres r (by revert r; decide), inv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
    (by taint_decide)

theorem challenge_ct : RelCT isa (fun a b => S3 s₁ a ∧ S3 s₂ b) signChallenge fun _ _ => True :=
  hash_then (by taint_decide) (fun a b h => ⟨h.1.hashOk hp₁, h.2.hashOk hp₂, inv_sp hpub h.1.inv h.2.inv,
    sub_regs (by decide) (inv_regs hpub h.1.inv h.2.inv)⟩) [.s0, .s1, .s11] (fun a b h r hr =>
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
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, psp, pf⟩ := pub
  unfold signCached
  -- `F`.
  refine RelCT.seq (R := fun a b => Upd s₁ a .t0 (sF s₁) ∧ Upd s₂ b .t0 (sF s₂))
    (RelCT.mono (relct_wp (taint_block [] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact frame_ok hp₁ fun u hu => WP.block_nil hu,
       by rw [hab.2]; exact frame_ok hp₂ fun u hu => WP.block_nil hu⟩) (fun _ _ h => h) fun _ _ h => h) ?_
  -- The setup.
  refine RelCT.seq (R := fun a b => S1 s₁ a ∧ S1 s₂ b)
    (relct_wp (ct_prog [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0] (fun a b hab => by
      rw [hab.1.sp, hab.2.sp, psp]) (fun a b hab r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (hab.1.gpr.trans pf).trans hab.2.gpr.symm
        | (rw [hab.1.other _ (by decide), hab.2.other _ (by decide)]; assumption)) (by taint_decide))
      fun a b hab => ⟨signSetup_ok hp₁ hab.1, signSetup_ok hp₂ hab.2⟩) ?_
  -- The steps.
  refine RelCT.seq (R := fun a b => S2 s₁ a ∧ S2 s₂ b)
    (relct_wp (expand_ct hp₁ hp₂ hpub) fun a b hab => ⟨expand_ok hp₁ hab.1, expand_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => S3 s₁ a ∧ S3 s₂ b)
    (relct_wp (nonce_ct hp₁ hp₂ hpub) fun a b hab => ⟨nonce_ok hl hp₁ hab.1, nonce_ok hl hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => S4 s₁ a ∧ S4 s₂ b)
    (relct_wp (challenge_ct hp₁ hp₂ hpub) fun a b hab => ⟨challenge_ok hp₁ hab.1, challenge_ok hp₂ hab.2⟩) ?_
  -- The wipe and the restores.
  exact ct_prog [.s11] (fun a b hab => inv_sp hpub hab.1.inv hab.2.inv)
    (fun a b hab => sub_regs (by decide) (inv_regs hpub hab.1.inv hab.2.inv)) (by taint_decide)

end VG.Proof.Ed448.RISCV64.Whole
