module

import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Sha512OK
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowRhs
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.VerifyWindow
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowDigit
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Ed25519.WindowNibble
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyCT
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowRhs
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyPoints
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowDigit
meta import VerifiedGarbage.Proof.Ed25519.Window
meta import VerifiedGarbage.Proof.Ed25519.WindowNibble
meta import VerifiedGarbage.Proof.Ed25519.Group.Decode
meta import VerifiedGarbage.Proof.Ed25519.ScalarBytes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.Challenge
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Verify
public import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Sha512OK
meta import VerifiedGarbage.Impl.Ed25519.PPC64LE.VerifyWindow
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Prune
meta import VerifiedGarbage.Proof.Ed25519.Challenge
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Impl.Ed25519.PPC64LE.Verify
meta import VerifiedGarbage.Spec.Ed25519.Contract

/-! ### `Ed25519.PPC64LE.Whole.VerifyMsg`, which only this module used -/

section

/-! ### `Ed25519.PPC64LE.Whole.VerifyHash`, which only this module used -/

section

/-!
# `vg_ed25519_verify` on PPC64LE: the challenge

`pk` in `r3`, the message in `r4` (`len` in `r5`), the signature in `r6`,
`scratch` in `r7` and the frame `F` (192 bytes) in `r8`. The registers saved
at `128(F)`, `R ‖ A ‖ M` hashed into `64(F)`, the digest reduced into `0(F)`
by a call of `vg_ed25519_scalar_reduce` and its upper half zeroed, and the
arguments of `verify_equation` set (`verifyHash_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

/-- The message. -/
abbrev vmsgR (s : State) : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩

/-- The static of the cached `-[1]B … -[15]B`, which `verify_equation` reads. -/
abbrev vtbR (s : State) : Region := ⟨s.syms Impl.Ed25519.PPC64LE.bSym, 1920⟩

/-- The precondition, by register, with the static `vtbR` of `verify_equation`. -/
structure VerPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 32⟩, vmsgR s, ⟨s.gpr .r6, 64⟩, vtbR s]
  wr : s.wr = [⟨s.gpr .r7, 8192⟩, ⟨s.gpr .r8, 192⟩]
  pC : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r7, 8192⟩
  pF : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r8, 192⟩
  mC : Region.Disjoint (vmsgR s) ⟨s.gpr .r7, 8192⟩
  mF : Region.Disjoint (vmsgR s) ⟨s.gpr .r8, 192⟩
  sC : Region.Disjoint ⟨s.gpr .r6, 64⟩ ⟨s.gpr .r7, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .r6, 64⟩ ⟨s.gpr .r8, 192⟩
  cF : Region.Disjoint ⟨s.gpr .r7, 8192⟩ ⟨s.gpr .r8, 192⟩
  sp : 48 ≤ s.sp.toNat
  bP : (below s.sp 48).Disjoint ⟨s.gpr .r3, 32⟩
  bM : (below s.sp 48).Disjoint (vmsgR s)
  bS : (below s.sp 48).Disjoint ⟨s.gpr .r6, 64⟩
  bC : (below s.sp 48).Disjoint ⟨s.gpr .r7, 8192⟩
  bF : (below s.sp 48).Disjoint ⟨s.gpr .r8, 192⟩
  tfit : (s.syms Impl.Ed25519.PPC64LE.bSym).toNat + 1920 ≤ 2 ^ 64
  twords : ∀ q < 240, s.mem.readW (s.syms Impl.Ed25519.PPC64LE.bSym + BitVec.ofNat 64 (8 * q)) 64 =
    Impl.Ed25519.PPC64LE.bWord q
  tC : (vtbR s).Disjoint ⟨s.gpr .r7, 8192⟩
  tF : (vtbR s).Disjoint ⟨s.gpr .r8, 192⟩
  tB : (vtbR s).Disjoint (below s.sp 48)

/-- What the body may write. -/
abbrev verW (s : State) : List Region := [⟨s.gpr .r7, 8192⟩, ⟨s.gpr .r8, 192⟩, below s.sp 48]

/-- The values in `r20`–`r25`. -/
def verV (s : State) : Reg → BitVec 64
  | .r20 => s.gpr .r3 | .r21 => s.gpr .r4 | .r22 => s.gpr .r5 | .r23 => s.gpr .r6 | .r24 => s.gpr .r7
  | .r25 => s.gpr .r8 | _ => 0

abbrev VerInv (s : State) : State → Prop := Inv s (s.gpr .r8) 128 verifyRegs (verV s) (verW s)

theorem verifyRegs_pres : ∀ r ∈ verifyRegs, r ∈ preserved := by decide

theorem verV_r22 (s : State) : verV s .r22 = s.gpr .r5 := rfl
theorem verV_r24 (s : State) : verV s .r24 = s.gpr .r7 := rfl
theorem verV_r25 (s : State) : verV s .r25 = s.gpr .r8 := rfl

/-- The regions a step may write: the scratch space, the callees' frames, or the frame below the
slots. -/
def VerWr (s : State) (r : Region) : Prop :=
  r = ⟨s.gpr .r7, 8192⟩ ∨ r = below s.sp 48 ∨ ∃ d n, d + n ≤ 128 ∧ r = ⟨s.gpr .r8 + BitVec.ofNat 64 d, n⟩

theorem verStep {s t t' : State} (hp : VerPre s) (h : VerInv s t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {Wc : List Region}
    (hf : Frame Wc t.mem t'.mem) (hW : ∀ r ∈ Wc, VerWr s r) : VerInv s t' := by
  obtain hs : Region.Sub (slotArea (s.gpr .r8) 128 verifyRegs) ⟨s.gpr .r8, 192⟩ := Offset.sub_base _ (by decide)
  refine Inv.step h verifyRegs_pres hrd hwr hsp hg hf (fun r hr => ?_) fun r hr => ?_
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨s.gpr .r8, 192⟩, by simp, Offset.sub_base _ (by omega_using [hdn])⟩
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact hp.cF.symm.sub_left hs
    · exact hp.bF.symm.sub_left hs
    · exact Offset.disjoint _ (.inr hdn) (by decide) (by omega_using [hdn])

/-- An input, while the body runs. -/
theorem ver_input {s t : State} (h : VerInv s t) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hC : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .r7, 8192⟩) (hF : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .r8, 192⟩)
    (hB : Region.Disjoint ⟨p, n⟩ (below s.sp 48)) : bytesAt t.mem p n = bytesAt s.mem p n :=
  bytes_keep h.frame hn fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hC
    · exact hF
    · exact hB

theorem ver_env {s t : State} (hp : VerPre s) (h : VerInv s t) : ScEnv (s.gpr .r7) t :=
  ⟨by rw [h.wr, hp.wr]; simp, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

theorem ver_Fw {s t : State} (hp : VerPre s) (h : VerInv s t) : (⟨s.gpr .r8, 192⟩ : Region) ∈ t.wr := by
  rw [h.wr, hp.wr]; simp

/-- The setup: the registers saved, the pointers moved to `r20`–`r25`. -/
theorem verSetup_ok {s : State} (hp : VerPre s) :
    WP isa (.block (saveRegs .r8 128 verifyRegs ++
      [mov .r20 .r3, mov .r21 .r4, mov .r22 .r5, mov .r23 .r6, mov .r24 .r7, mov .r25 .r8])) s (VerInv s) := by
  obtain hF : (⟨s.gpr .r8, 192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hsl : ∀ p ∈ slots 128 verifyRegs, p.2 + 8 ≤ 192 := by decide
  refine save_ok (by decide) (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega_using [this])) fun u hu _ hsv hfr => ?_
  unfold mov
  refine wp_addi (by decide) (by decide) fun u₁ h₁ => wp_addi (by decide) (by decide) fun u₂ h₂ =>
    wp_addi (by decide) (by decide) fun u₃ h₃ => wp_addi (by decide) (by decide) fun u₄ h₄ =>
    wp_addi (by decide) (by decide) fun u₅ h₅ => wp_addi (by decide) (by decide) fun u₆ h₆ => WP.block_nil ?_
  obtain m₆ : u₆.mem = u.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  obtain g₆ : ∀ r, r ∉ verifyRegs → u₆.gpr r = u.gpr r := fun r hr => by
    simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, f⟩ := hr
    rw [h₆.other _ f, h₅.other _ e, h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  obtain gu : ∀ r, r ≠ .r0 → u.gpr r = s.gpr r := fun r h => hu.gpr r (by simpa using h)
  refine ⟨by rw [h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd],
    by rw [h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr],
    by rw [h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp], fun r hr => ?_, fun r hr hn => ?_, m₆ ▸ hsv,
    m₆ ▸ (hfr.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨⟨s.gpr .r8, 192⟩, by simp, Offset.sub_base _ (by decide)⟩)⟩
  · simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.gpr, BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.gpr, h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr,
        h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
        h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
  · rw [g₆ r hn, gu r fun e => r0_pres (e ▸ hr)]

/-- The message's bytes, and `verify`'s challenge. -/
abbrev vmsgB (s : State) : List Byte := bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat

abbrev vChallenge (s : State) : List Byte :=
  Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE (Spec.Sha512.sha512
    (bytesAt s.mem (s.gpr .r6) 32 ++ bytesAt s.mem (s.gpr .r3) 32 ++ vmsgB s)) % Spec.Ed25519.L)

/-- After the challenge: the arguments of `verify_equation`. -/
structure VerArgs (s t : State) : Prop where
  inv : VerInv s t
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r6
  r5 : t.gpr .r5 = s.gpr .r8
  r6 : t.gpr .r6 = s.gpr .r7
  ch : bytesAt t.mem (s.gpr .r8) 64 = vChallenge s

theorem verifyHash_ok (C : ShaOK) {s : State} (hp : VerPre s) : WP isa verifyHash s (VerArgs s) := by
  obtain hlen : (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64 := len_add_le (Nat.le_of_lt (s.gpr .r5).isLt) (by decide) hp.mC
  obtain scW : ∀ {t : State}, VerInv s t → ∀ r ∈ [(⟨s.gpr .r7, 8192⟩ : Region), below t.sp 48], VerWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  obtain S32 : Region.Sub ⟨s.gpr .r6, 32⟩ ⟨s.gpr .r6, 64⟩ := Region.sub_prefix (by decide)
  obtain F0 : Region.Sub ⟨s.gpr .r8, 32⟩ ⟨s.gpr .r8, 192⟩ := Region.sub_prefix (by decide)
  obtain F64 : Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 64, 64⟩ ⟨s.gpr .r8, 192⟩ := Offset.sub_base _ (by decide)
  obtain inRd : ∀ {t : State}, VerInv s t → ∀ {r : Region}, r ∈ s.rd → Covers [r] (t.rd ++ t.wr) :=
    fun h r hr a n hi => by
      obtain ⟨r', hr', hc⟩ := hi
      rw [List.mem_singleton.mp hr'] at hc
      exact ⟨r, List.mem_append_left _ (by rw [h.rd]; exact hr), hc⟩
  unfold verifyHash
  refine WP.seq (WP.mono (verSetup_ok hp) fun t₁ h₁ => ?_)
  refine WP.seq (hashInit_ok C (sr := .r24) (by decide) (h₁.regs _ (by decide)) (ver_env hp h₁)
    fun t₂ a b c f₂ g hr₂ => ?_)
  obtain h₂ := verStep hp h₁ a b c g f₂ (scW h₁)
  -- `R`, the signature's first half.
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r23) (off := 0) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 0) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₂)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, h₂.rd, hp.rd]
      exact ⟨⟨s.gpr .r6, 64⟩, by simp, 0, by simp, by simp⟩)
    (hp.sC.sub_left S32) (by rw [h₂.sp]; exact hp.bS.sub_right S32) fun t₃ a b c f₃ g hr₃ => ?_)
  obtain h₃ := verStep hp h₂ a b c g f₃ (scW h₂)
  obtain r₃ : Repr t₃.mem (s.gpr .r7) (bytesAt s.mem (s.gpr .r6) 32) := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, ver_input h₂ (by decide) (hp.sC.sub_left S32) (hp.sF.sub_left S32)
      (hp.bS.symm.sub_left S32)] at this
  -- `A`.
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r20) (off := 0) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 32) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₃) (inRd h₃ (by rw [hp.rd]; simp))
    hp.pC (by rw [h₃.sp]; exact hp.bP) fun t₄ a b c f₄ g hr₄ => ?_)
  obtain h₄ := verStep hp h₃ a b c g f₄ (scW h₃)
  obtain r₄ : Repr t₄.mem (s.gpr .r7) (bytesAt s.mem (s.gpr .r6) 32 ++ bytesAt s.mem (s.gpr .r3) 32) := by
    have := hr₄ _ r₃ (by simp [bytesAt])
    rwa [ver_input h₃ (by decide) hp.pC hp.pF hp.bP.symm] at this
  -- The message.
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r21) (off := 0) (len := (s.gpr .r5).toNat) (by decide)
    (by decide) (by decide) (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 64) (by decide)) (Sets.addi (d := .r6) (n := .r22) (k := 0) (by decide) (by decide))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .r22 (by decide) (by decide) (by decide)])
    (by rw [BitVec.add_zero, h₄.regs _ (by decide)]; rfl) (ver_env hp h₄) (inRd h₄ (by rw [hp.rd]; simp))
    hp.mC (by rw [h₄.sp]; exact hp.bM) fun t₅ a b c f₅ g hr₅ => ?_)
  obtain h₅ := verStep hp h₄ a b c g f₅ (scW h₄)
  obtain r₅ : Repr t₅.mem (s.gpr .r7)
      (bytesAt s.mem (s.gpr .r6) 32 ++ bytesAt s.mem (s.gpr .r3) 32 ++ vmsgB s) := by
    have := hr₅ _ r₄ (by simp [bytesAt])
    rwa [ver_input h₄ (s.gpr .r5).isLt hp.mC hp.mF hp.bM.symm] at this
  refine WP.seq (hashFinalize_ok C (sr := .r24) (f := .r25) (o := 64) (out := s.gpr .r8 + BitVec.ofNat 64 64)
    (vc := fun g => g .r22 + BitVec.ofNat 64 64)
    (by decide) (by decide) (by decide) (by decide) (by decide) (h₅.regs _ (by decide))
    (by rw [h₅.regs _ (by decide)]; rfl)
    (Sets.addi (d := .r4) (n := .r22) (k := 64) (by decide) (by decide)) (fun g g' hg => by rw [hg .r22 (by decide)])
    (ver_env hp h₅)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, ver_Fw hp h₅, 64, rfl, show 64 + 64 ≤ 192 by decide⟩)
    (hp.cF.symm.sub_left F64) (by rw [h₅.sp]; exact hp.bF.sub_right F64) fun t₆ a b c f₆ g hd₆ => ?_)
  obtain h₆ := verStep hp h₅ a b c g f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr ⟨64, 64, by decide, rfl⟩)
    · exact .inr (.inl (by rw [h₅.sp])))
  obtain dg : bytesAt t₆.mem (s.gpr .r8 + BitVec.ofNat 64 64) 64 =
      Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .r6) 32 ++ bytesAt s.mem (s.gpr .r3) 32 ++ vmsgB s) :=
    hd₆ _ r₅ (by simp [bytesAt]; omega_using [hlen])
      (by rw [h₅.regs _ (by decide), cnt_eq, verV_r22]; simp [bytesAt]; congr 1; omega_using [])
  -- `scalar_reduce`.
  obtain ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  obtain hFw := ver_Fw hp h₆
  obtain hCw : (⟨s.gpr .r7, 8192⟩ : Region) ∈ t₆.wr := (ver_env hp h₆).w
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun t₇ k₇ c3 c4 c5 => ?_)
  rw [h₆.regs _ (by decide), verV_r25, BitVec.add_zero] at c3
  rw [h₆.regs _ (by decide), verV_r25] at c4
  rw [h₆.regs _ (by decide), BitVec.add_zero, verV_r24] at c5
  refine WP.seq (WP.call (k := reducePPC) reduce_ok' (rd := [⟨s.gpr .r8 + BitVec.ofNat 64 64, 64⟩])
    (wr := [⟨s.gpr .r8, 32⟩, ⟨s.gpr .r7, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact Offset.base_disjoint _ (by decide) (by decide),
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F0,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F64⟩
    (Covers.of_sub fun r hr => by
      rw [k₇.rd, k₇.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 64 ≤ 192 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₇.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 0, by simp, by simp⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₈ a b c f₈ g _ hpost => ?_) (by decide +kernel))
  simp only [reducePPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    c3, c4, k₇.mem, dg] at hpost
  obtain h₈ := verStep hp h₆ (a.trans k₇.rd) (b.trans k₇.wr) (c.trans k₇.sp)
    (fun r hr => (g r hr).trans (k₇.pres r hr)) (k₇.mem ▸ f₈) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr ⟨0, 32, by decide, by simp⟩)
      · exact .inl rfl
  -- The upper half zeroed, and the arguments.
  obtain hFw₈ : (⟨s.gpr .r8, 192⟩ : Region) ∈ t₈.wr := ver_Fw hp h₈
  obtain e25 : t₈.gpr .r25 = s.gpr .r8 := h₈.regs _ (by decide)
  obtain inF : ∀ (u : State), u.wr = t₈.wr → ∀ d, d + 8 ≤ 192 → InRegions u.wr (s.gpr .r8 + BitVec.ofNat 64 d) 8 :=
    fun u hu d hd => by rw [hu]; exact in_base hFw₈ hd (by omega_using [hd])
  refine wp_li (d := .r8) (imm := 0) (by decide) fun u₁ e₁ => ?_
  refine wp_stdd (a := s.gpr .r8 + BitVec.ofNat 64 32) (by decide) ⟨by decide, by decide⟩
    (by rw [e₁.other _ (by decide), e25]) (inF _ e₁.wr 32 (by decide)) fun u₂ e₂ => ?_
  refine wp_stdd (a := s.gpr .r8 + BitVec.ofNat 64 40) (by decide) ⟨by decide, by decide⟩
    (by rw [e₂.gpr, e₁.other _ (by decide), e25]) (inF _ (by rw [e₂.wr, e₁.wr]) 40 (by decide)) fun u₃ e₃ => ?_
  refine wp_stdd (a := s.gpr .r8 + BitVec.ofNat 64 48) (by decide) ⟨by decide, by decide⟩
    (by rw [e₃.gpr, e₂.gpr, e₁.other _ (by decide), e25]) (inF _ (by rw [e₃.wr, e₂.wr, e₁.wr]) 48 (by decide))
    fun u₄ e₄ => ?_
  refine wp_stdd (a := s.gpr .r8 + BitVec.ofNat 64 56) (by decide) ⟨by decide, by decide⟩
    (by rw [e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e25])
    (inF _ (by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr]) 56 (by decide)) fun u₅ e₅ => ?_
  refine wp_addi (by decide) (by decide) fun v₁ g₁ => wp_addi (by decide) (by decide) fun v₂ g₂ =>
    wp_addi (by decide) (by decide) fun v₃ g₃ => wp_addi (by decide) (by decide) fun v₄ g₄ => WP.block_nil ?_
  have z₁ : u₁.gpr .r8 = 0 := e₁.gpr
  obtain z₂ : u₂.gpr .r8 = 0 := by rw [e₂.gpr, z₁]
  obtain z₃ : u₃.gpr .r8 = 0 := by rw [e₃.gpr, z₂]
  obtain z₄ : u₄.gpr .r8 = 0 := by rw [e₄.gpr, z₃]
  obtain mv : v₄.mem = ((((t₈.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW
      (s.gpr .r8 + BitVec.ofNat 64 40) (0 : BitVec 64)).writeW (s.gpr .r8 + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW
      (s.gpr .r8 + BitVec.ofNat 64 56) (0 : BitVec 64)) := by
    rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem, e₁.mem, z₁, z₂, z₃, z₄]
  obtain gp : ∀ r ∈ preserved, v₄.gpr r = t₈.gpr r := fun r hr => by
    obtain ⟨p3, p4, p5, p6, -⟩ := pres_args hr
    rw [g₄.other _ p6, g₃.other _ p5, g₂.other _ p4, g₁.other _ p3, e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr,
      e₁.other _ (by revert hr; cases r <;> decide)]
  obtain cont : ∀ d, 32 ≤ d → d + 8 ≤ 64 → Region.Contains ⟨s.gpr .r8 + BitVec.ofNat 64 32, 32⟩
      (s.gpr .r8 + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])
  obtain fv : Frame [⟨s.gpr .r8 + BitVec.ofNat 64 32, 32⟩] t₈.mem v₄.mem := by
    rw [mv]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cont 32 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cont 40 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cont 48 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (cont 56 (by decide) (by decide))
  obtain rr : ∀ (x : Mem) (i j : Nat) (v : BitVec 64), i + 8 ≤ j ∨ j + 8 ≤ i → i + 8 ≤ 192 → j + 8 ≤ 192 →
      (x.writeW (s.gpr .r8 + BitVec.ofNat 64 j) v).readW (s.gpr .r8 + BitVec.ofNat 64 i) 64 =
        x.readW (s.gpr .r8 + BitVec.ofNat 64 i) 64 :=
    fun x i j v h hi hj => Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [hi]) (by omega_using [hj])) (by decide)
  obtain hz : ∀ k < 4, v₄.mem.readW (s.gpr .r8 + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * k)) 64 = 0 := by
    intro k hk
    rw [mv, Offset.add_add]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl
    · rw [show 32 + 8 * 0 = 32 from rfl, rr _ 32 56 _ (by decide) (by decide) (by decide),
        rr _ 32 48 _ (by decide) (by decide) (by decide), rr _ 32 40 _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 1 = 40 from rfl, rr _ 40 56 _ (by decide) (by decide) (by decide),
        rr _ 40 48 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 2 = 48 from rfl, rr _ 48 56 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 3 = 56 from rfl, Mem.readW_writeW_self64]
  obtain g₃' : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r8 → v₄.gpr r = t₈.gpr r :=
    fun r a b c d e => by
      rw [g₄.other _ d, g₃.other _ c, g₂.other _ b, g₁.other _ a, e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ e]
  refine ⟨verStep hp h₈ (by rw [g₄.rd, g₃.rd, g₂.rd, g₁.rd, e₅.rd, e₄.rd, e₃.rd, e₂.rd, e₁.rd])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, e₁.wr])
    (by rw [g₄.sp, g₃.sp, g₂.sp, g₁.sp, e₅.sp, e₄.sp, e₃.sp, e₂.sp, e₁.sp]) gp fv fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨32, 32, by decide, rfl⟩), ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.other _ (by decide), g₁.gpr, BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), h₈.regs _ (by decide)]; rfl
  · rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), h₈.regs _ (by decide)]; rfl
  · rw [g₄.other _ (by decide), g₃.gpr, g₂.other _ (by decide), g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e25]
  · rw [g₄.gpr, g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), h₈.regs _ (by decide)]; rfl
  · have low : bytesAt v₄.mem (s.gpr .r8) 32 = bytesAt t₈.mem (s.gpr .r8) 32 :=
      bytes_keep fv (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by decide) (by decide)
    rw [Proof.Ed25519.signatureBytes_split, low, hpost, bytes32_zero hz, ← Proof.Ed25519.reduced_challenge]

end VG.Proof.Ed25519.PPC64LE.Whole

end

end

/-! ### `Ed25519.PPC64LE.VerifyVerified`, which only this module used -/

section

/-!
# `vg_ed25519_verify_equation` on PPC64LE, by register

The function meets a contract of its facts by register (`verifyPPC`), with
no stack, and the static of the cached `-[1]B … -[15]B` (`bSym`, `bWord`):
the callers in this library call it through it. It saves and restores the
nonvolatile registers it writes, and `lr`, which its calls and `adrSym`
overwrite (`verify_ok'`), given the windows' proof (`RhsOk`). The contract
declares the inputs and the static's address public, and two runs on the
same inputs leak the same trace (`verifyEquation_rel`, `verify_ct`), given
the windows' constant time (`RhsCT`). What a caller's contract under
`abi.withConsts bConsts` says of the static: `bstat_of_consts`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE

/-- `vg_ed25519_verify_equation`'s contract by register, an internal function's. -/
def verifyPPC : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 32⟩
    let sig : Region := ⟨s.gpr .r4, 64⟩
    let ch : Region := ⟨s.gpr .r5, 64⟩
    let ws : Region := ⟨s.gpr .r6, 8192⟩
    let tb : Region := ⟨s.syms bSym, 1920⟩
    s.rd = [pk, sig, ch, tb] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws ∧
      (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧ tb.Disjoint ws
  post s s' := (s'.gpr .r3).setWidth 32 = if Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .r3) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .r4) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .r5) 64) then 1 else 0
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r3) 32 ++ Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r4) 64 ++
      Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r5) 64).map (·.toNat) =
    (Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .r3) 32 ++ Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .r4) 64 ++
      Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .r5) 64).map (·.toNat) ∧ s₁.syms bSym = s₂.syms bSym

theorem verifyPPC_pre {s : State} (hs : verifyPPC.pre s) : VerifyPre s :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  ⟨h1, h2, h3, h4, h5, ⟨by rw [h1]; simp, h6, h7, h8⟩⟩

theorem verify_ok' (hR : RhsOk) (s : State) (hs : verifyPPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.PPC64LE.verifyEquation s t s' ∧ abiPreserved s s' ∧
      verifyPPC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hlr, hr⟩ := verify_ok hR (verifyPPC_pre hs)
  refine ⟨t, s', he, ⟨hg, hsp, hlr⟩, ?_⟩
  show (s'.gpr .r3).setWidth 32 = _
  rw [hr]
  split <;> rfl

theorem bytes_of_leak {a₁ b₁ c₁ a₂ b₂ c₂ : List Byte} (ha : a₁.length = a₂.length) (hb : b₁.length = b₂.length)
    (h : (a₁ ++ b₁ ++ c₁).map (·.toNat) = (a₂ ++ b₂ ++ c₂).map (·.toNat)) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  obtain e : a₁ ++ b₁ ++ c₁ = a₂ ++ b₂ ++ c₂ := by
    have := congrArg (List.map fun n => BitVec.ofNat 8 n) h
    simpa [List.map_map, Function.comp_def] using this
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [ha, hb])
  obtain ⟨e3, e4⟩ := List.append_inj e1 ha
  exact ⟨e3, e4, e2⟩

theorem verify_ct (hR : RhsOk) (hRC : RhsCT) :
    ConstantTime isa verifyPPC.pre verifyPPC.pub Impl.Ed25519.PPC64LE.verifyEquation := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨p3, p4, p5, p6, psp, pl, psy⟩ := hp
  obtain hl : ∀ (s : State) (p : Addr) (n : Nat), (Spec.Ed25519.bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [Spec.Ed25519.bytesAt]
  obtain ⟨b3, b4, b5⟩ := bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl]) pl
  refine verifyEquation_rel hR hRC (b := s₁.gpr .r6) (sp := s₁.sp) (pk := s₁.gpr .r3) (sig := s₁.gpr .r4)
    (ch := s₁.gpr .r5) (T := s₁.syms bSym) (PK := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r3) 32)
    (SG := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r4) 64) (CH := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r5) 64)
    _ _ _ _ _ _ ⟨⟨verifyPPC_pre h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨verifyPPC_pre h₂, psy.symm, p3.symm, p4.symm, p5.symm, p6.symm, psp.symm, by rw [b3, p3], by rw [b4, p4],
        by rw [b5, p5]⟩⟩ e₁ e₂

theorem bWords_length : bWords.length = 240 := by simp [bWords]

theorem bWords_getD {q : Nat} (hq : q < 240) : bWords.getD q 0 = bWord q := by
  simp [bWords, hq]

/-- What `abi.withConsts [(bSym, ws)]` says of the static, for words `ws` of `bWord`. -/
theorem bstat_of_consts' {st : Nat} {s : State} {ws : List (BitVec 64)} (hl : ws.length = 240)
    (hg : ∀ q < 240, ws.getD q 0 = bWord q) (h : ConstsOk [(bSym, ws)] st s) :
    (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r) ∧
      ∀ r ∈ PPC64LE.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 1920⟩ r := by
  obtain hrd := h.mem_rd List.mem_cons_self
  obtain hfit := h.fit List.mem_cons_self
  obtain hd : (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 8 * ws.length⟩ r) ∧
      ∀ r ∈ PPC64LE.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 8 * ws.length⟩ r :=
    (h.2.2.1 _ List.mem_cons_self).2
  rw [hl] at hrd hfit hd
  refine ⟨hrd, hfit, fun q hq => ?_, hd.1, hd.2⟩
  rw [h.readW List.mem_cons_self (by rw [hl]; exact hq), hg q hq]

/-- What `abi.withConsts bConsts` says of the static. -/
theorem bstat_of_consts {st : Nat} {s : State} (h : ConstsOk bConsts st s) :
    (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r) ∧
      ∀ r ∈ PPC64LE.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 1920⟩ r :=
  bstat_of_consts' bWords_length (fun _ hq => bWords_getD hq) h

/-- The readable regions under `abi.withConsts [(bSym, ws)]`: those without it, then the static. -/
theorem rd_of_bconsts' {st : Nat} {s : State} {ws : List (BitVec 64)} {L : List Region}
    (hl : ws.length = 240) (h : ConstsOk [(bSym, ws)] st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [⟨s.syms bSym, 1920⟩] := by
  have h1 := h.1
  simp only [List.length_singleton, constRegs, Abi.constRegions, List.map_cons, List.map_nil, hl] at h1
  calc s.rd = s.rd.take (s.rd.length - 1) ++ s.rd.drop (s.rd.length - 1) := (List.take_append_drop _ _).symm
    _ = L ++ [⟨s.syms bSym, 1920⟩] := by rw [hL, h1]

theorem rd_of_bconsts {st : Nat} {s : State} {L : List Region} (h : ConstsOk bConsts st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [⟨s.syms bSym, 1920⟩] :=
  rd_of_bconsts' bWords_length h hL

end VG.Proof.Ed25519.PPC64LE

end

end


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

/-- The inputs of `verify_equation`: `pk`, the signature, the challenge in `F`, and the static. -/
abbrev verRd (s : State) : List Region := [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r6, 64⟩, ⟨s.gpr .r8, 64⟩, vtbR s]

/-- The narrowed state `verify_equation` starts in. -/
theorem verCall_pre {s t : State} (hp : VerPre s) (ha : VerArgs s t) (sy : t.syms = s.syms) :
    verifyPPC.pre (t.callEntry.withRegions (verRd s) [⟨s.gpr .r7, 8192⟩]) := by
  obtain ce : ∀ q, q ∉ linkRegs → (t.callEntry.withRegions (verRd s) [⟨s.gpr .r7, 8192⟩]).gpr q = t.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have cy : (t.callEntry.withRegions (verRd s) [⟨s.gpr .r7, 8192⟩]).syms = s.syms := sy
  obtain cm : (t.callEntry.withRegions (verRd s) [⟨s.gpr .r7, 8192⟩]).mem = t.mem := by
    rw [State.withRegions_mem, State.callEntry_mem]
  refine ⟨by rw [State.withRegions_rd, ce _ (by decide), ce _ (by decide), ce _ (by decide), ha.r3, ha.r4, ha.r5, cy],
    by rw [State.withRegions_wr, ce _ (by decide), ha.r6], by rw [ce _ (by decide), ce _ (by decide), ha.r3, ha.r6]; exact hp.pC,
    by rw [ce _ (by decide), ce _ (by decide), ha.r4, ha.r6]; exact hp.sC,
    by rw [ce _ (by decide), ce _ (by decide), ha.r5, ha.r6]; exact hp.cF.symm.sub_left (Region.sub_prefix (by decide)),
    by rw [cy]; exact hp.tfit, fun q hq => ?_, by rw [cy, ce _ (by decide), ha.r6]; exact hp.tC⟩
  rw [cy, cm, ← hp.twords q hq]
  refine ha.inv.frame.readW (r := vtbR s) (Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])) (fun r hr => ?_) (by decide)
  simp only [verW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.tC
  · exact hp.tF
  · exact hp.tB

theorem verCall_covers {s t : State} (hp : VerPre s) (ha : VerArgs s t) :
    Covers (verRd s ++ [⟨s.gpr .r7, 8192⟩]) (t.rd ++ t.wr) ∧ Covers [⟨s.gpr .r7, 8192⟩] t.wr := by
  rw [ha.inv.rd, ha.inv.wr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .r3, 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .r6, 64⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .r8, 192⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨vtbR s, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .r7, 8192⟩, by simp, 0, by simp, by simp⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨⟨s.gpr .r7, 8192⟩, by simp, 0, by simp, by simp⟩

theorem verifyEquation_noFrames : Impl.Ed25519.PPC64LE.verifyEquation.noFrames = true := by decide +kernel

/-- The call of `verify_equation`. -/
theorem verCall_ok (hR : RhsOk) {s t : State} (hp : VerPre s) (ha : VerArgs s t) (sy : t.syms = s.syms) :
    WP isa (.call "vg_ed25519_verify_equation" Impl.Ed25519.PPC64LE.verifyEquation) t fun t' =>
      VerInv s t' ∧ (t'.gpr .r3).setWidth 32 = verResult s := by
  obtain ⟨hc, hw⟩ := verCall_covers hp ha
  refine WP.call (k := verifyPPC) (verify_ok' hR) (verCall_pre hp ha sy) hc hw (fun t' a b c f g _ hpost => ?_)
    verifyEquation_noFrames
  have hp' : (t'.gpr .r3).setWidth 32 = if Spec.Ed25519.verifyEquation (bytesAt t.mem (t.gpr .r3) 32)
      (bytesAt t.mem (t.gpr .r4) 64) (bytesAt t.mem (t.gpr .r5) 64) then 1 else 0 := hpost
  rw [ha.r3, ha.r4, ha.r5, ha.ch, ver_pk hp ha.inv, ver_sig hp ha.inv] at hp'
  refine ⟨verStep hp ha.inv a b c g f fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl rfl, hp'.trans ?_⟩
  unfold verResult Spec.Ed25519.verify
  rw [Proof.Ed25519.signatureBytes_take]

theorem verifyMessage_wp (C : ShaOK) (hR : RhsOk) {s : State} (hp : VerPre s) :
    WP isa verifyMessage s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      (t.gpr .r3).setWidth 32 = verResult s := by
  unfold verifyMessage
  refine WP.seq (WP.mono_syms (verifyHash_ok C hp) fun t ha sy => ?_)
  refine WP.seq (WP.mono (verCall_ok hR hp ha sy) fun t' ⟨h', hr⟩ => ?_)
  obtain hFw : (⟨s.gpr .r8, 192⟩ : Region) ∈ t'.rd ++ t'.wr := List.mem_append_right _ (ver_Fw hp h')
  obtain hrl : ∀ p ∈ restoreList 128 verifyRegs, p.2 + 8 ≤ 192 := by decide
  refine restore_ok h' (by decide) (h'.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega_using [this]))
    fun t₅ g₅ sp₅ lr₅ _ o₅ => ⟨g₅, sp₅, lr₅, ?_⟩
  rw [o₅ _ (by decide) (by decide), hr]

end VG.Proof.Ed25519.PPC64LE.Whole

end

end

/-! ### `Ed25519.PPC64LE.WindowCT`, which only this module used -/

section

/-!
# Verification's windows on PPC64LE leak only the inputs

`verifyRhs` branches, and addresses its tables, on digits it loads from the
challenge and the signature, which the taint analysis takes as secret: each
such branch and address is related by correctness instead, as both runs load
the same digit of the same scalars (`addA_ct`, `addB_ct`, `windowB_ct`). The
code between them is the taint analysis's (`ctRegs`). The windows' count is
the challenge's (`windowCount_ok`), and the comparison branches on the group
elements the two sums represent, the same in both runs (`pointEqualRep_ct`).
Together: `rhs_ct`, which is `RhsCT`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.Ed25519 (Rep RepP baseAff dZ)
open VG.Spec.Ed25519 (decodeLE bytesAt)
open Edwards

/-- An `ite` whose condition each run evaluates to the same `v`. -/
theorem ct_ite {A : State → Prop} {c : isa.Cond} {th el : Prog isa} (v : Bool)
    (hv : ∀ s, A s → isa.eval c s = some v) (ht : v = true → RelCT isa (Both A) th fun _ _ => True)
    (he : v = false → RelCT isa (Both A) el fun _ _ => True) :
    RelCT isa (Both A) (.ite c th el) fun _ _ => True := by
  refine RelCT.ite (fun _ _ h => by rw [hv _ h.1, hv _ h.2]) ?_ ?_
  · cases v
    · exact RelCT.of_false fun _ _ h => by have e := h.2; rw [hv _ h.1.1] at e; cases e
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases v
    · exact (he rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => by have e := h.2; rw [hv _ h.1.1] at e; cases e

/-- Two pieces, with what the first gives each run. -/
theorem ct_seq {A B : State → Prop} {c₁ c₂ : Prog isa} (h₁ : RelCT isa (Both A) c₁ fun _ _ => True)
    (hw : ∀ s, A s → WP isa c₁ s B) (h₂ : RelCT isa (Both B) c₂ fun _ _ => True) :
    RelCT isa (Both A) (.seq c₁ c₂) fun _ _ => True :=
  RelCT.seq (ctBoth h₁ hw) h₂

section
variable {b sp : Addr}

/-! ## The comparison, by the group elements -/

/-- Before the comparison: slots 0–3 and 4–7 representing `P` and `Q`. -/
def EqRepPre (b sp : Addr) (P Q : EPoint dZ) (s : State) : Prop :=
  Pin b sp s ∧ RepP (point (env s.mem b) 0 1 2 3) P ∧ RepP (point (env s.mem b) 4 5 6 7) Q

theorem pointEqualRep_ct (P Q : EPoint dZ) :
    RelCT isa (Both (EqRepPre b sp P Q)) Impl.Ed25519.PPC64LE.pointEqual fun _ _ => True := by
  unfold Impl.Ed25519.PPC64LE.pointEqual
  let E (t : State) : Prop := Pin b sp t ∧ (env t.mem b 8 = env t.mem b 9 ↔ P.x = Q.x) ∧
    (env t.mem b 10 = env t.mem b 11 ↔ P.y = Q.y)
  have h1 := ctBoth (ctRegs [.r6] (A := EqRepPre b sp P Q) (c := fieldCode pointEqualOps)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide)) (B := E) fun s h =>
      WP.mono (fieldCode_ok _ h.1.1.ctx) fun t ⟨k, e⟩ => by
        refine ⟨h.1.of_rest k.rest (by decide), ?_, ?_⟩
        · rw [e]; exact Proof.Ed25519.repP_cross_x h.2.1 h.2.2
        · rw [e]; exact Proof.Ed25519.repP_cross_y h.2.1 h.2.2
  let E' (t : State) : Prop := Pin b sp t ∧ (env t.mem b 10 = env t.mem b 11 ↔ P.y = Q.y)
  have h2 := ctBoth (ctRegs [.r6] (A := E) (c := fieldEqual 8 9) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => E' t ∧ (t.gpr .r5 = 0 ↔ P.x = Q.x)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx 8 9) fun t ⟨k, e, z⟩ =>
        ⟨⟨h.1.of_rest k.rest (by decide), by rw [e]; exact h.2.2⟩, z.trans h.2.1⟩
  have h3 := ctBoth (ctRegs [.r6] (A := E') (c := fieldEqual 10 11) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => Pin b sp t ∧ (t.gpr .r5 = 0 ↔ P.y = Q.y)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx 10 11) fun t ⟨k, _, z⟩ =>
        ⟨h.1.of_rest k.rest (by decide), z.trans h.2⟩
  refine RelCT.seq h1 (RelCT.seq h2 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_))
  · refine RelCT.seq (h3.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
      (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
    · exact (ctRegs [.r6] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)).mono
        (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

end

section
variable {b sp pk sig ch T : Addr} {A : Spec.Ed25519.Point} {K S : Nat}

/-! ## A window -/

/-- The registers both runs agree on, within a window. -/
theorem wregs {s₁ s₂ : State} (h₁ : WCtx b pk sig ch T A K S s₁) (h₂ : WCtx b pk sig ch T A K S s₂)
    (p₁ : s₁.sp = sp) (p₂ : s₂.sp = sp) {x : BitVec 64} (e₁ : s₁.gpr .r15 = x) (e₂ : s₂.gpr .r15 = x) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r6, .r15, .r19, .r30, .r31], s₁.gpr r = s₂.gpr r := by
  refine ⟨p₁.trans p₂.symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.vc.ctx.r6, h₂.vc.ctx.r6]
  · rw [e₁, e₂]
  · rw [h₁.r19, h₂.r19]
  · rw [h₁.vc.r30, h₂.vc.r30]
  · rw [h₁.vc.r31, h₂.vc.r31]

/-- `wregs`, with the digit in `a2`. -/
theorem wregs2 {s₁ s₂ : State} (h₁ : WCtx b pk sig ch T A K S s₁) (h₂ : WCtx b pk sig ch T A K S s₂)
    (p₁ : s₁.sp = sp) (p₂ : s₂.sp = sp) {x y : BitVec 64} (e₁ : s₁.gpr .r15 = x) (e₂ : s₂.gpr .r15 = x)
    (a₁ : s₁.gpr .r9 = y) (a₂ : s₂.gpr .r9 = y) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r9, .r6, .r15, .r19, .r30, .r31], s₁.gpr r = s₂.gpr r := by
  refine ⟨p₁.trans p₂.symm, fun r hr => ?_⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [a₁, a₂]
  · exact (wregs h₁ h₂ p₁ p₂ e₁ e₂).2 r hr

/-- Within window `c`, the sum representing `v`. -/
def WM (b sp pk sig ch T : Addr) (A : Spec.Ed25519.Point) (K S c : Nat) (v : EPoint dZ) (t : State) : Prop :=
  WCtx b pk sig ch T A K S t ∧ t.sp = sp ∧ env t.mem b 16 = Spec.Ed25519.d ∧
    t.gpr .r15 = BitVec.ofNat 64 c ∧ Rep (point (env t.mem b) 0 1 2 3) v

/-- `WM`, with digit `dg` in `a2`. -/
def WD (b sp pk sig ch T : Addr) (A : Spec.Ed25519.Point) (K S c : Nat) (v : EPoint dZ) (dg : Nat)
    (t : State) : Prop :=
  WM b sp pk sig ch T A K S c v t ∧ t.gpr .r9 = BitVec.ofNat 64 dg

theorem WD.regs {c dg : Nat} {v : EPoint dZ} {s₁ s₂ : State} (h₁ : WD b sp pk sig ch T A K S c v dg s₁)
    (h₂ : WD b sp pk sig ch T A K S c v dg s₂) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r9, .r6, .r15, .r19, .r30, .r31], s₁.gpr r = s₂.gpr r :=
  wregs2 h₁.1.1 h₂.1.1 h₁.1.2.1 h₂.1.2.1 h₁.1.2.2.2.1 h₂.1.2.2.2.1 h₁.2 h₂.2

theorem WM.regs {c : Nat} {v v' : EPoint dZ} {s₁ s₂ : State} (h₁ : WM b sp pk sig ch T A K S c v s₁)
    (h₂ : WM b sp pk sig ch T A K S c v' s₂) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r6, .r15, .r19, .r30, .r31], s₁.gpr r = s₂.gpr r :=
  wregs h₁.1 h₂.1 h₁.2.1 h₂.2.1 h₁.2.2.2.1 h₂.2.2.2.1

theorem addA_ct {c dg : Nat} (hdg : dg < 16) {v : EPoint dZ} :
    RelCT isa (Both (WD b sp pk sig ch T A K S c v dg)) addA fun _ _ => True := by
  unfold addA
  refine ct_ite (decide (dg ≠ 0)) (fun s h => eval_nz_ofNat s .r9 (by omega_using [hdg]) h.2) (fun _ => ?_) (fun _ => ?_)
  · exact ctRegs [.r9, .r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)
  · exact ctRegs [.r9, .r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

theorem addB_ct {c dg : Nat} (hdg : dg < 16) {v : EPoint dZ} :
    RelCT isa (Both (WD b sp pk sig ch T A K S c v dg)) addB fun _ _ => True := by
  unfold addB
  refine ct_ite (decide (dg ≠ 0)) (fun s h => eval_nz_ofNat s .r9 (by omega_using [hdg]) h.2) (fun _ => ?_) (fun _ => ?_)
  · exact ctRegs [.r9, .r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)
  · exact ctRegs [.r9, .r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

/-- `WM` through a `Rest` that keeps the pointers and `r15`, a frame of `FA`, and slots 0–3 and 16. -/
theorem WM.of {c : Nat} {v : EPoint dZ} {s t : State} {R : List Reg} (h : WM b sp pk sig ch T A K S c v s)
    (hr : Rest R s t) (hR : ∀ r ∈ [Reg.r6, .r29, .r30, .r31], r ∉ R) (h5 : Reg.r19 ∉ R) (h1 : Reg.r15 ∉ R)
    (hf : Frame [FA b] s.mem t.mem) {v' : EPoint dZ} (hp : Rep (point (env t.mem b) 0 1 2 3) v')
    (hd : env t.mem b 16 = env s.mem b 16) : WM b sp pk sig ch T A K S c v' t :=
  ⟨h.1.of hr hR h5 hf, by rw [hr.sp, h.2.1], by rw [hd, h.2.2.1], by rw [hr.gpr _ h1, h.2.2.2.1], hp⟩

theorem windowB_ct {c : Nat} (hc : c < 128) {v : EPoint dZ} :
    RelCT isa (Both (WM b sp pk sig ch T A K S c v)) windowB fun _ _ => True := by
  unfold windowB
  refine ct_seq (B := fun t => WM b sp pk sig ch T A K S c v t ∧ (t.gpr .r7 == 0) = decide (c < 64))
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide))
    (fun s h => wp_lsr (by decide) fun t u2 => WP.block_nil ⟨?_, ?_⟩) ?_
  · have r2 : Rest [.r7] s t := u2.rest (by decide)
    exact h.of r2 (by decide) (by decide) (by decide) (by rw [u2.mem]; exact Frame.refl _ _)
      (by rw [u2.mem]; exact h.2.2.2.2) (by rw [u2.mem])
  · rw [u2.gpr, h.2.2.2.1]; exact lsr6_fact c hc
  refine ct_ite (decide (c < 64)) (fun s h => by rw [eval_zero, h.2]) (fun hb => ?_) (fun _ => ?_)
  swap
  · exact ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide)
  have hc64 : c < 64 := of_decide_eq_true hb
  refine ct_seq (B := WD b sp pk sig ch T A K S c v (S / 16 ^ c % 16))
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
    (fun s h => WP.mono (digitS_ok h.1.1 hc64 h.1.2.2.2.1) fun t ⟨rt, mt, et⟩ =>
      ⟨h.1.of rt (by decide) (by decide) (by decide) (by rw [mt]; exact Frame.refl _ _)
        (by rw [mt]; exact h.1.2.2.2.2) (by rw [mt]), et⟩) (addB_ct (Nat.mod_lt _ (by decide)))

/-- The windows' invariant in each run, with `n` windows left. -/
def WinCT (b sp pk sig ch T : Addr) (A : Spec.Ed25519.Point) (K S : Nat) (Aa : EPoint dZ) (n : Nat)
    (t : State) : Prop :=
  1 ≤ n ∧ n ≤ 128 ∧ WCtx b pk sig ch T A K S t ∧ t.sp = sp ∧ env t.mem b 16 = Spec.Ed25519.d ∧
    t.gpr .r15 = BitVec.ofNat 64 n ∧
    RepP (point (env t.mem b) 0 1 2 3) ((K / 16 ^ n) • Aa + (S / 16 ^ n) • (-baseAff))

theorem windowStep_ct {Aa : EPoint dZ} (hA : Rep A Aa) {c : Nat} (hc : c < 128) :
    RelCT isa (Both (WinCT b sp pk sig ch T A K S Aa (c + 1))) windowStep fun _ _ => True := by
  have hS : ∀ t, WCtx b pk sig ch T A K S t → S < 256 ^ 32 := fun t h => h.sc ▸ Proof.Ed25519.decodeLE_lt32 _ _
  let v1 := (K / 16 ^ (c + 1)) • Aa + (S / 16 ^ (c + 1)) • (-baseAff)
  let M1 (t : State) : Prop := WCtx b pk sig ch T A K S t ∧ t.sp = sp ∧ env t.mem b 16 = Spec.Ed25519.d ∧
    t.gpr .r15 = BitVec.ofNat 64 c ∧ RepP (point (env t.mem b) 0 1 2 3) v1
  unfold windowStep
  refine ct_seq (B := M1)
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ =>
      wregs h₁.2.2.1 h₂.2.2.1 h₁.2.2.2.1 h₂.2.2.2.1 h₁.2.2.2.2.2.1 h₂.2.2.2.2.2.1) (by taint_decide))
    (fun s h => wp_subi (imm := 1) (by decide) (by decide) fun t u => WP.block_nil ?_) ?_
  · obtain ⟨_, _, hw, hsp, hd, h1, hv⟩ := h
    have r1 : Rest [.r15] s t := u.rest (by decide)
    refine ⟨hw.of r1 (by decide) (by decide) (by rw [u.mem]; exact Frame.refl _ _), by rw [r1.sp, hsp],
      by rw [u.mem, hd], ?_, by rw [u.mem]; exact hv⟩
    rw [u.gpr, h1, BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
  refine ct_seq (B := WM b sp pk sig ch T A K S c ((16 : Nat) • v1))
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ =>
      wregs h₁.1 h₂.1 h₁.2.1 h₂.2.1 h₁.2.2.2.1 h₂.2.2.2.1) (by taint_decide))
    (fun s h => WP.mono (dbl4_ok h.1.vc.ctx) fun t ⟨k, f, e, e16⟩ =>
      ⟨h.1.of k (by decide) (by decide) f, by rw [k.sp, h.2.1], by rw [e16, h.2.2.1],
        by rw [k.gpr _ (by decide), h.2.2.2.1], by rw [e]; exact dbl4_rep h.2.2.2.2⟩) ?_
  refine ct_seq (B := WD b sp pk sig ch T A K S c ((16 : Nat) • v1) (K / 16 ^ c % 16))
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide))
    (fun s h => WP.mono (digitK_ok h.1 hc h.2.2.2.1) fun t ⟨rt, mt, et⟩ =>
      ⟨h.of rt (by decide) (by decide) (by decide) (by rw [mt]; exact Frame.refl _ _)
        (by rw [mt]; exact h.2.2.2.2) (by rw [mt]), et⟩) ?_
  refine ct_seq (B := WM b sp pk sig ch T A K S c ((16 : Nat) • v1 + (K / 16 ^ c % 16) • Aa))
    (addA_ct (Nat.mod_lt _ (by decide)))
    (fun s h => WP.mono (addA_ok h.1.1 hA (Nat.mod_lt _ (by decide)) h.2 h.1.2.2.2.2) fun t ⟨rt, ft, pt, dt⟩ =>
      h.1.of rt (by decide) (by decide) (by decide) ft pt dt) (windowB_ct hc)

/-- **The windows**, from `W` left. -/
theorem windows_ct {Aa : EPoint dZ} (hA : Rep A Aa) (W : Nat) :
    RelCT isa (Both (WinCT b sp pk sig ch T A K S Aa W)) windows fun _ _ => True := by
  unfold windows
  refine RelCT.loop (M := isa) (fun n => Both (WinCT b sp pk sig ch T A K S Aa n)) (fun n => ?_) W
  rcases n with _ | c
  · exact RelCT.of_false fun _ _ h => absurd h.1.1 (by omega_using [])
  by_cases hc : c < 128
  · refine (ctBoth (windowStep_ct hA hc) (B := WM b sp pk sig ch T A K S c
        ((K / 16 ^ c) • Aa + (S / 16 ^ c) • (-baseAff))) fun s h => WP.mono
        (windowStep_ok h.2.2.1 h.2.2.2.2.1 hA (h.2.2.1.sc ▸ Proof.Ed25519.decodeLE_lt32 _ _) hc h.2.2.2.2.2.1
          h.2.2.2.2.2.2) fun t ⟨ht, dt, et, vt, rt, _⟩ => ⟨ht, by rw [rt.sp, h.2.2.2.1], dt, et, vt⟩).mono
      (fun _ _ h => h) fun s₁ s₂ h => ⟨?_, fun _ => trivial, fun he => ⟨c, by omega_using [], ?_⟩⟩
    · rw [eval_nz_ofNat s₁ .r15 (by omega_using [hc]) h.1.2.2.2.1, eval_nz_ofNat s₂ .r15 (by omega_using [hc]) h.2.2.2.2.1]
    · rw [eval_nz_ofNat s₁ .r15 (by omega_using [hc]) h.1.2.2.2.1] at he
      have hc0 : c ≠ 0 := by simpa using he
      exact ⟨⟨by omega_using [hc0], by omega_using [hc], h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, rep_repP h.1.2.2.2.2⟩,
        ⟨by omega_using [hc0], by omega_using [hc], h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, rep_repP h.2.2.2.2.2⟩⟩
  · exact RelCT.of_false fun _ _ h => absurd h.1.2.1 (by omega_using [hc])

end

/-! ## `verifyRhs` -/

/-- **`verifyRhs` leaks only its inputs.** -/
theorem rhs_ct : RhsCT := by
  intro b sp pk sig ch T PK RS CH SS a r ha hr
  obtain ⟨Aa, hA⟩ := Proof.Ed25519.decodePoint_rep ha
  obtain ⟨Ra, hR⟩ := Proof.Ed25519.decodePoint_rep hr
  have dR : ∀ r' ∈ [FA b, (⟨b + BitVec.ofNat 64 TA, 1920⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 7904, 128⟩ r' := fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using []) (by omega_using [])
    · exact Offset.disjoint _ (.inr (by rw [TA_eq]; omega_using [])) (by omega_using []) (by rw [TA_eq]; omega_using [])
  have dR1 : ∀ r' ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 7904, 128⟩ r' := fun r' hr' =>
    dR r' (by simp only [List.mem_singleton] at hr'; simp [hr'])
  have sigD : ∀ {t : State}, VCtx b pk sig ch t →
      (⟨sig + BitVec.ofNat 64 32, 32⟩ : Region).Disjoint ⟨b, 8192⟩ := fun h =>
    h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide))
  unfold verifyRhs
  -- `A` into slots 0–3.
  let R1 (t : State) : Prop := VCtx b pk sig ch t ∧ t.sp = sp ∧ BStat b T t ∧ t.syms bSym = T ∧
    point (env t.mem b) 0 1 2 3 = a ∧ tableAt t.mem b 7904 = r ∧ bytesAt t.mem ch 64 = CH ∧
    bytesAt t.mem (sig + BitVec.ofNat 64 32) 32 = SS
  have c1 := ctBoth (ctRegs [.r6] (A := RhsPre b sp pk sig ch T a r CH SS) (c := .block (pointTableRead 7776))
    (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, fun x hx => by
      rw [List.mem_singleton.mp hx, h₁.1.ctx.r6, h₂.1.ctx.r6]⟩) (by taint_decide)) (B := R1) fun s h =>
    WP.mono_syms (rhsRead_ok h.1.ctx) fun t ⟨rt, ft, pt⟩ sy =>
      ⟨h.1.of_rest rt (by decide), by rw [rt.sp, h.2.1], h.2.2.1.of_frame rt.rd ft fa_sub,
        by rw [sy]; exact h.2.2.2.1, by rw [pt, h.2.2.2.2.1], by rw [tableAt_keep ft dR1, h.2.2.2.2.2.1],
        by rw [bytesAt_ws ft fa_sub h.1.chD (by decide), h.2.2.2.2.2.2.1],
        by rw [bytesAt_ws ft fa_sub (sigD h.1) (by decide), h.2.2.2.2.2.2.2]⟩
  -- The preparation.
  let R2 (t : State) : Prop := WCtx b pk sig ch T a (decodeLE CH) (decodeLE SS) t ∧ t.sp = sp ∧
    env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 = Spec.Ed25519.identity ∧
    tableAt t.mem b 7904 = r ∧ bytesAt t.mem ch 64 = CH
  have c2 := ctBoth (RelCT.taint (A := taintSym [bSym]) (Taint.ofRegs [.r6]) (P := Both R1) (c := strausPrep)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨⟨h₁.2.1.trans h₂.2.1.symm, fun x hx => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hx
      subst hx; rw [h₁.1.ctx.r6, h₂.1.ctx.r6]⟩, fun n hn => by
        rw [List.mem_singleton.mp hn, h₁.2.2.2.1, h₂.2.2.2.1]⟩) (by taint_decide)) (B := R2) fun s h =>
    WP.mono (strausPrep_ok h.1 h.2.2.1 h.2.2.2.1) fun t ⟨wt, dt, it, rt, ft⟩ => by
      rw [h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2] at wt
      exact ⟨wt, by rw [rt.sp, h.2.1], dt, it, by rw [tableAt_keep ft dR, h.2.2.2.2.2.1],
        by rw [bytesAt_ws ft prepW_sub h.1.chD (by decide), h.2.2.2.2.2.2.1]⟩
  -- The count.
  let R3 (W : Nat) (t : State) : Prop := (W = 64 ∨ W = 128) ∧
    (W = 64 ↔ ∀ i < 32, CH.getD (32 + i) 0 = 0) ∧
    WinCT b sp pk sig ch T a (decodeLE CH) (decodeLE SS) Aa W t ∧ tableAt t.mem b 7904 = r
  have c3 : RelCT isa (Both R2) windowCount fun s₁ s₂ => ∃ W, Both (R3 W) s₁ s₂ := by
    unfold windowCount
    have hch := RelCT.seq (ctBoth (ctRegs [.r6, .r31] (A := R2) (c := .block challengeHigh)
      (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rw [h₁.1.vc.ctx.r6, h₂.1.vc.ctx.r6]
        · rw [h₁.1.vc.r31, h₂.1.vc.r31]⟩) (by taint_decide))
      (B := fun t => R2 t ∧ (t.gpr .r8 = 0 ↔ ∀ i < 32, CH.getD (32 + i) 0 = 0)) fun s h =>
        WP.mono (challengeHigh_ok h.1.vc.r31 fun i hi => in_base (List.mem_append_left _ h.1.vc.chR)
          (by omega_using [hi]) (by omega_using [hi])) fun t ⟨rt, mt, et⟩ => ⟨by
            refine ⟨h.1.of rt (by decide) (by decide) (by rw [mt]; exact Frame.refl _ _), by rw [rt.sp, h.2.1],
              by rw [mt]; exact h.2.2.1, by rw [mt]; exact h.2.2.2.1, by rw [mt]; exact h.2.2.2.2.1,
              by rw [mt]; exact h.2.2.2.2.2⟩, by
            rw [et, ← h.2.2.2.2.2]
            exact forall_congr' fun i => imp_congr_right fun hi => by rw [bytesAt_getD _ _ (by omega_using [hi])]⟩)
      (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2)
        ((ctRegs [] (A := R2) (c := .block [.li .r15 64]) (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, by simp⟩)
          (by taint_decide)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
        ((ctRegs [] (A := R2) (c := .block [.li .r15 128]) (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, by simp⟩)
          (by taint_decide)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h))
    refine (ctBoth hch (B := fun t => ∃ W, R3 W t) fun s h => WP.mono (windowCount_ok h.1.vc)
      fun t ⟨rt, mt, W, hW, hW64, et, hK⟩ => ⟨W, hW, ?_, ⟨by omega_using [hW], by omega_using [hW],
        h.1.of rt (by decide) (by decide) (by rw [mt]; exact Frame.refl _ _), by rw [rt.sp, h.2.1],
        by rw [mt]; exact h.2.2.1, et, ?_⟩, by rw [mt]; exact h.2.2.2.2.1⟩).mono (fun _ _ h => h) ?_
    · rw [hW64, ← h.2.2.2.2.2]
      exact forall_congr' fun i => imp_congr_right fun hi => by rw [bytesAt_getD _ _ (by omega_using [hi])]
    · have hS : decodeLE SS < 256 ^ 32 := h.1.sc ▸ Proof.Ed25519.decodeLE_lt32 _ _
      rw [h.2.2.2.2.2] at hK
      rw [Nat.div_eq_of_lt hK, Proof.Ed25519.nibble_high_zero hS (by omega_using [hW]), zero_nsmul, zero_nsmul, add_zero,
        mt, h.2.2.2.1]
      exact rep_repP Proof.Ed25519.identity_rep
    · rintro s₁ s₂ ⟨⟨W₁, h₁⟩, ⟨W₂, h₂⟩⟩
      have e : W₁ = W₂ := by
        rcases h₁.1 with rfl | rfl <;> rcases h₂.1 with rfl | rfl
        · rfl
        · exact absurd (h₂.2.1.mpr (h₁.2.1.mp rfl)) (by decide)
        · exact absurd (h₁.2.1.mpr (h₂.2.1.mp rfl)) (by decide)
        · rfl
      subst e
      exact ⟨W₁, h₁, h₂⟩
  -- The windows, `-R` and the comparison.
  have tail : ∀ W, RelCT isa (Both (R3 W)) (.seq windows (.seq negR Impl.Ed25519.PPC64LE.pointEqual))
      fun _ _ => True := fun W => by
    let R4 (t : State) : Prop := Ctx8 b t ∧ t.sp = sp ∧
      Rep (point (env t.mem b) 0 1 2 3) (decodeLE CH • Aa + decodeLE SS • (-baseAff)) ∧
      tableAt t.mem b 7904 = r
    have c4 := ctBoth (A := R3 W) ((windows_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (T := T) (A := a)
      (K := decodeLE CH) (S := decodeLE SS) hA W).mono (fun _ _ h => ⟨h.1.2.2.1, h.2.2.2.1⟩) fun _ _ h => h)
      (B := R4) fun s h => WP.mono (windows_ok h.2.2.1.1 h.2.2.1.2.1 h.2.2.1.2.2.1 h.2.2.1.2.2.2.2.1 hA
        (h.2.2.1.2.2.1.sc ▸ Proof.Ed25519.decodeLE_lt32 _ _) h.2.2.1.2.2.2.2.2.1 h.2.2.1.2.2.2.2.2.2)
        fun t ⟨wt, rt, ft, vt⟩ => ⟨wt.vc.ctx, by rw [rt.sp, h.2.2.1.2.2.2.1], vt,
          by rw [tableAt_keep ft dR1, h.2.2.2]⟩
    have c5 := ctBoth (ctRegs [.r6] (A := R4) (c := negR) (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm,
      fun x hx => by rw [List.mem_singleton.mp hx, h₁.1.r6, h₂.1.r6]⟩) (by taint_decide))
      (B := EqRepPre b sp (decodeLE CH • Aa + decodeLE SS • (-baseAff)) (-Ra)) fun s h =>
        WP.mono (negR_ok h.1) fun t ⟨rt, _, ct, qt, pt⟩ =>
          ⟨⟨ct, by rw [rt.sp, h.2.1]⟩, by rw [pt]; exact rep_repP h.2.2.1,
            by rw [qt, h.2.2.2]; exact rep_repP hR.neg⟩
    exact RelCT.seq c4 (RelCT.seq c5 (pointEqualRep_ct _ _))
  refine RelCT.seq c1 (RelCT.seq c2 (RelCT.seq c3 ?_))
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨W, hW⟩ e₁ e₂ => tail W s₁ s₂ t₁ t₂ s₁' s₂' hW e₁ e₂

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# `vg_ed25519_verify` on PPC64LE, verified

The code meets `verifyContract` under `abi.withConsts bConsts` (the static of
the cached `-[1]B … -[15]B`, which `verify_equation` reads) with the frame as
one more argument (`Sig.scratchContract`) and 48 bytes of stack for the
callees' frames: the proof against the contract's facts by register (`verC`:
`verR` without the static, and what the static adds), which it implies
(`bconsts_implies`), with the windows' proofs (`rhs_ok`, `rhs_ct`), and a
state satisfying it, with the static at `0x100000` (`bMem`). In a frame of
224 bytes (`Verified.stackScratchLC`), it meets the contract itself. The
contract declares the inputs public. Two runs on the same inputs leak the
same trace (`ver_ct`): the taint analysis checks the challenge's computation
(only the pointers and the length matter to it) and the restores, and the
call of `verify_equation` leaks the same trace in both runs by its own
constant time, since its arguments, the challenge and the static's address
included, are the same in both (`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.PPC64LE (bSym bWords bConsts)
open VG.Proof.Ed25519.PPC64LE (bWords_length bstat_of_consts rd_of_bconsts rhs_ok rhs_ct RhsOk RhsCT)

/-- The contract by register: `pk` in `r3`, the message in `r4` (`len` in `r5`), the signature in
`r6`, `scratch` in `r7`, the frame in `r8`. -/
def verR : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 32⟩
    let msg : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    let sig : Region := ⟨s.gpr .r6, 64⟩
    let sc : Region := ⟨s.gpr .r7, 8192⟩
    let fr : Region := ⟨s.gpr .r8, 192⟩
    s.rd = [pk, msg, sig] ∧ s.wr = [sc, fr] ∧ pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧
      msg.Disjoint fr ∧ sig.Disjoint sc ∧ sig.Disjoint fr ∧ sc.Disjoint fr ∧ 48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint pk ∧ (below s.sp 48).Disjoint msg ∧ (below s.sp 48).Disjoint sig ∧
      (below s.sp 48).Disjoint sc ∧ (below s.sp 48).Disjoint fr
  post s s' := (s'.gpr .r3).setWidth 32 = verResult s
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.sp = s₂.sp ∧
    (bytesAt s₁.mem (s₁.gpr .r3) 32 ++ bytesAt s₁.mem (s₁.gpr .r4) (s₁.gpr .r5).toNat ++
      bytesAt s₁.mem (s₁.gpr .r6) 64).map (·.toNat) =
    (bytesAt s₂.mem (s₂.gpr .r3) 32 ++ bytesAt s₂.mem (s₂.gpr .r4) (s₂.gpr .r5).toNat ++
      bytesAt s₂.mem (s₂.gpr .r6) 64).map (·.toNat)

/-- `verR` with the static of `verify_equation` (`abi.withConsts bConsts`). -/
def verC : Contract isa where
  pre s := verR.pre (stripConsts bConsts s) ∧ ConstsOk bConsts 48 s
  post := verR.post
  pub s₁ s₂ := verR.pub s₁ s₂ ∧ s₁.syms bSym = s₂.syms bSym

theorem verC_pre {s : State} (h : verC.pre s) : VerPre s := by
  obtain ⟨⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o⟩, hk⟩ := h
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at *
  obtain ⟨-, tfit, words, twr, tres⟩ := bstat_of_consts hk
  have hrd : s.rd = [⟨s.gpr .r3, 32⟩, vmsgR s, ⟨s.gpr .r6, 64⟩, vtbR s] := rd_of_bconsts hk a
  have hB : below s.sp 48 ∈ PPC64LE.abi.reserved 48 s := by
    show _ ∈ stackBelow s.sp 48
    rw [stackBelow_pos _ (by decide)]; simp
  exact ⟨hrd, b, c, d, e, f, g, h', i, j, k, l, m, n, o, tfit, words, twr _ (by rw [b]; simp),
    twr _ (by rw [b]; simp), tres _ hB⟩

theorem ver_ok (hR : RhsOk) (s : State) (hs : verC.pre s) :
    ∃ t s', Exec isa verifyMessage s t s' ∧ abiPreserved s s' ∧ verC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ := verifyMessage_wp sha512OK hR (verC_pre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

/-- Two runs on the same public data, as `RelCT.constantTime` relates them. -/
abbrev VP (s₁ s₂ : State) : Prop := verC.pre s₁ ∧ verC.pre s₂ ∧ verC.pub s₁ s₂

/-- The inputs agree in two such runs. -/
theorem vp_bytes {s₁ s₂ : State} (h : VP s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .r3) 32 = bytesAt s₂.mem (s₂.gpr .r3) 32 ∧ vmsgB s₁ = vmsgB s₂ ∧
      bytesAt s₁.mem (s₁.gpr .r6) 64 = bytesAt s₂.mem (s₂.gpr .r6) 64 := by
  obtain ⟨-, -, ⟨-, -, p5, -, -, -, -, pl⟩, -⟩ := h
  have hl : ∀ (s : State) (p : Addr) (n : Nat), (bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [bytesAt]
  exact bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl, p5]) pl

/-- The restores, with `F` in `r25` in both runs. -/
theorem restore_ct {P : State → State → Prop}
    (hp : ∀ t₁ t₂, P t₁ t₂ → t₁.sp = t₂.sp ∧ t₁.gpr .r25 = t₂.gpr .r25) :
    RelCT isa P (.block (restoreRegs .r25 128 verifyRegs)) fun _ _ => True :=
  RelCT.taint (A := vectorTaint) (Taint.ofRegs [.r25]) (fun t₁ t₂ h => ⟨(hp _ _ h).1, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr; exact (hp _ _ h).2⟩) (by taint_decide)

/-- Two runs' entry states. -/
abbrev VPair : Type := {σ : State × State // VP σ.1 σ.2}

theorem ver_ct (hR : RhsOk) (hRC : RhsCT) : ConstantTime isa verC.pre verC.pub verifyMessage := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold verifyMessage
  refine RelCT.seq (R := fun (t₁ t₂ : State) => ∃ σ : VPair, (VerArgs σ.1.1 t₁ ∧ t₁.syms = σ.1.1.syms) ∧
    (VerArgs σ.1.2 t₂ ∧ t₂.syms = σ.1.2.syms)) ?_ <|
    RelCT.seq (R := fun t₁ t₂ => ∃ σ : VPair, VerInv σ.1.1 t₁ ∧ VerInv σ.1.2 t₂) ?_ ?_
  · refine ((RelCT.taint (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) (fun s₁ s₂ h => ?_)
      (by taint_decide)).wpDep (F := fun (s t : State) => VerArgs s t ∧ t.syms = s.syms) fun s₁ s₂ h =>
        ⟨WP.mono_syms (verifyHash_ok sha512OK (verC_pre h.1)) fun _ a sy => ⟨a, sy⟩,
          WP.mono_syms (verifyHash_ok sha512OK (verC_pre h.2.1)) fun _ a sy => ⟨a, sy⟩⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨⟨(σ₁, σ₂), hp⟩, a₁, a₂⟩
    obtain ⟨-, -, ⟨p3, p4, p5, p6, p7, p8, psp, -⟩, -⟩ := h
    refine ⟨psp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ => ?_
    refine ((RelCT.callEx (k := Proof.Ed25519.PPC64LE.verifyPPC) (Proof.Ed25519.PPC64LE.verify_ok' hR)
      (Proof.Ed25519.PPC64LE.verify_ct hR hRC) fun t₁ t₂ ⟨⟨a₁, y₁⟩, ⟨a₂, y₂⟩⟩ => ?_).wp
      (F₁ := VerInv σ.1.1) (F₂ := VerInv σ.1.2) fun t₁ t₂ ⟨⟨a₁, y₁⟩, ⟨a₂, y₂⟩⟩ =>
        ⟨WP.mono (verCall_ok hR (verC_pre σ.2.1) a₁ y₁) fun _ h => h.1,
          WP.mono (verCall_ok hR (verC_pre σ.2.2.1) a₂ y₂) fun _ h => h.1⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, i₁, i₂⟩ => ⟨σ, i₁, i₂⟩
    have hp₁ := verC_pre σ.2.1
    have hp₂ := verC_pre σ.2.2.1
    obtain ⟨c₁, w₁⟩ := verCall_covers hp₁ a₁
    obtain ⟨c₂, w₂⟩ := verCall_covers hp₂ a₂
    refine ⟨_, _, _, _, verCall_pre hp₁ a₁ y₁, verCall_pre hp₂ a₂ y₂, ?_, c₁, w₁, c₂, w₂⟩
    obtain ⟨-, -, ⟨p3, p4, p5, p6, p7, p8, psp, -⟩, psy⟩ := σ.2
    obtain ⟨b3, bm, b6⟩ := vp_bytes σ.2
    have ch : vChallenge σ.1.1 = vChallenge σ.1.2 := by
      unfold vChallenge
      rw [← Proof.Ed25519.signatureBytes_take, ← Proof.Ed25519.signatureBytes_take σ.1.2.mem, b6, b3, bm]
    simp only [Proof.Ed25519.PPC64LE.verifyPPC, State.withRegions_gpr, State.withRegions_sp,
      State.withRegions_mem, State.callEntry_sp,
      State.callEntry_mem, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide)]
    rw [a₁.r3, a₂.r3, a₁.r4, a₂.r4, a₁.r5, a₂.r5, a₁.r6, a₂.r6, a₁.inv.sp, a₂.inv.sp, a₁.ch, a₂.ch,
      ver_pk hp₁ a₁.inv, ver_pk hp₂ a₂.inv, ver_sig hp₁ a₁.inv, ver_sig hp₂ a₂.inv, b3, b6, ch]
    exact ⟨p3, p6, p8, p7, psp, rfl, by
      show t₁.syms bSym = t₂.syms bSym
      rw [y₁, y₂]; exact psy⟩
  · exact RelCT.exists_ fun σ => restore_ct fun t₁ t₂ ⟨i₁, i₂⟩ => by
      obtain ⟨-, -, ⟨-, -, -, -, -, p8, psp, -⟩, -⟩ := σ.2
      exact ⟨by rw [i₁.sp, i₂.sp]; exact psp, by
        rw [i₁.regs .r25 (by decide), i₂.regs .r25 (by decide), verV_r25, verV_r25]
        exact p8⟩

/-- A contract by register `kR` without the static implies the signature's contract under
`abi`; so does it with the static, under `abi.withConsts bConsts`. -/
theorem bconsts_implies {kR : Contract isa} {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {st : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (h : kR.Implies (sig.contract abi pre post wa st leak))
    (hpost : ∀ s s', kR.post s s' → kR.post (stripConsts bConsts s) s')
    (hpub : ∀ s₁ s₂, kR.pub (stripConsts bConsts s₁) (stripConsts bConsts s₂) → kR.pub s₁ s₂)
    (hsat : ∃ s, (sig.contract (abi.withConsts bConsts) pre post wa st leak).pre s) :
    Contract.Implies (M := isa)
      { pre := fun s => kR.pre (stripConsts bConsts s) ∧ ConstsOk bConsts st s
        post := kR.post
        pub := fun s₁ s₂ => kR.pub s₁ s₂ ∧ s₁.syms bSym = s₂.syms bSym }
      (sig.contract (abi.withConsts bConsts) pre post wa st leak) where
  pre _ hs := ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (post_stripConsts.mp (h.post (stripConsts bConsts s) s'
    (pre_consts.mp hs).1 (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := ⟨hpub _ _ (h.pub (stripConsts bConsts s₁) (stripConsts bConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)),
    (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

/-- A state satisfying the precondition, without the static. -/
def verSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r7 => 0x4000 | .r8 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 0⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8000, 192⟩]

theorem verR_implies : verR.Implies (Sig.scratchContract PPC64LE.abi Spec.Ed25519.verifySig "frame" .u8 192
    (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true 48
    (some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))) := by
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.verifyPost, Proof.Ed25519.WholeLocal.verifyLeak, verR,
    verResult, PPC64LE.abi, PPC64LE.argRegs] [verSat] using verSat

/-- The static at `0x100000`. -/
@[irreducible] def bMem : Mem := constMem 0x100000 bWords

theorem bMem_held : ∀ i < bWords.length,
    bMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0 := by
  have h := constMem_held 0x100000 bWords (by rw [bWords_length]; decide)
  unfold bMem
  exact h

/-- `verSat` with the static. -/
def verSatC : State :=
  { verSat with mem := bMem, rd := verSat.rd ++ [⟨0x100000, 1920⟩], syms := fun _ => 0x100000 }

theorem verC_sat : (Sig.scratchContract (PPC64LE.abi.withConsts bConsts) Spec.Ed25519.verifySig "frame"
    .u8 192 (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true
    48 (some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))).pre verSatC := by
  have hl := bWords_length
  have held := bMem_held
  dsimp only [bConsts]
  generalize bWords = W' at hl held ⊢
  generalize e : verSatC = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x4000, 8192⟩ : Region), ⟨0x8000, 192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem verC_implies : verC.Implies (Sig.scratchContract (PPC64LE.abi.withConsts bConsts)
    Spec.Ed25519.verifySig "frame" .u8 192 (Curry.const (fun _ => True) _)
    (Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true 48
    (some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))) :=
  bconsts_implies (kR := verR) verR_implies (fun _ _ h => h) (fun _ _ h => h) ⟨verSatC, verC_sat⟩

theorem verify_verified :
    Verified PPC64LE.target verifyMessage (Sig.scratchContract (PPC64LE.abi.withConsts bConsts)
      Spec.Ed25519.verifySig "frame" .u8 192 (Curry.const (fun _ => True) _)
      (Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true 48
      (some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))) :=
  Verified.of_correct (ver_ok rhs_ok) (ver_ct rhs_ok rhs_ct) verC_implies

/-- A state satisfying `vg_ed25519_verify`'s precondition, without the frame. -/
def verFrameSat : State := { verSatC with wr := [⟨0x4000, 8192⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Ed25519.verifyContract (PPC64LE.abi.withConsts bConsts) (48 + 224)).pre s := by
  refine ⟨verFrameSat, ?_⟩
  have hl := bWords_length
  have held := bMem_held
  dsimp only [bConsts]
  generalize bWords = W' at hl held ⊢
  generalize e : verFrameSat = s
  sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig, Spec.Ed25519.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x4000, 8192⟩ : Region)] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 224 bytes. -/
theorem verify_framed :
    Verified PPC64LE.target verifyCode (Spec.Ed25519.verifyContract (PPC64LE.abi.withConsts bConsts) (48 + 224)) :=
  Verified.stackScratchLC (sig := Spec.Ed25519.verifySig) (nm := "frame") (e := .u8) (n := 192)
    (post := Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 224)
    (leak := some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits)) verify_verified (by decide)
    (by decide)
    (fun vs _ m₂ _ _ _ => (congrFun (Curry.apply_const (fun _ : Mem => True)
      (Spec.Ed25519.verifySig.words PPC64LE.abi.ptrBits) vs) m₂).mpr trivial)
    (Proof.Ed25519.WholeLocal.verifyPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Ed25519.WholeLocal.verifyPostOut_local _ vs m m₁ m₂ r hl)
    (Proof.Ed25519.WholeLocal.verifyLeak_local _) verFrameSat_pre

end VG.Proof.Ed25519.PPC64LE.Whole
