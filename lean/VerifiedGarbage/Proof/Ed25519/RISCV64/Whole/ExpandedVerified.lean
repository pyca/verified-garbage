module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Comb
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.Expanded
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Sha512OK
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarBase
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Comb
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.Contract
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.Comb

/-! ### `Ed25519.RISCV64.Whole.PublicKeyCT`, which only this module used -/

section

/-!
# `vg_ed25519_public_key_expanded` on RISC-V, with its frame as an argument: constant time

Only the pointers are public: they stay in `s7`–`s10`, which no function
called writes, so the taint analysis (`taint_decide`) sees them public
throughout, callees included. So is the address of the comb's table
(`taintSym`), which `vg_ed25519_scalar_base` reads.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole

theorem publicKeyExpanded_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ (∀ r ∈ [Reg.a0, .a1, .a2, .a3], s₁.gpr r = s₂.gpr r) ∧
        s₁.syms Impl.Ed25519.RISCV64.combSym = s₂.syms Impl.Ed25519.RISCV64.combSym) :
    ConstantTime isa Pre Pub publicKeyExpanded :=
  VG.Taint.constantTime (A := taintSym [Impl.Ed25519.RISCV64.combSym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr, hsy⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨⟨hsp, fun r h => hr r (by simpa using h)⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

end VG.Proof.Ed25519.RISCV64.Whole

end

end

/-! ### `Ed25519.RISCV64.Whole.SignNonce`, which only this module used -/

section

/-! ### `Ed25519.RISCV64.Whole.SignExpand`, which this module and modules that import it used -/

section

/-! ### `Ed25519.RISCV64.Whole.SignSetup`, which this module and modules that import it used -/

section

/-!
# `vg_ed25519_sign_expanded` on RISC-V: the setup

`out` in `a0`, `expanded` in `a1`, `pk` in `a2`, the message in `a3` (`len` in
`a4`), `scratch` in `a5` and the frame `F` (288 bytes) in `a6`. The setup
saves the registers at `224(F)`, moves what lives across calls to `s7`–`s11`
and `expanded` to `s1`, and copies `pk` to `192(F)` (`signSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (combSym combWord)

variable {sl : Nat}

/-- The message. -/
abbrev msgR (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩

/-- What the body may write. -/
abbrev signW (s : State) : List Region := [⟨s.gpr .a0, 64⟩, ⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6, 288⟩, below s.sp 208]

/-- The precondition, by register, for `sl` bytes at `a1` (the seed's digest, so 64). That `pk` is
the seed's public key is a hypothesis of its own (`signExpanded_wp`). -/
structure SignPre (sl : Nat) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, sl⟩, ⟨s.gpr .a2, 32⟩, msgR s, TBL (s.syms combSym)]
  wr : s.wr = [⟨s.gpr .a0, 64⟩, ⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6, 288⟩]
  alC : (s.gpr .a5).toNat % 8 = 0
  alF : (s.gpr .a6).toNat % 8 = 0
  oS : Region.Disjoint ⟨s.gpr .a0, 64⟩ ⟨s.gpr .a1, sl⟩
  oP : Region.Disjoint ⟨s.gpr .a0, 64⟩ ⟨s.gpr .a2, 32⟩
  oM : Region.Disjoint ⟨s.gpr .a0, 64⟩ (msgR s)
  oC : Region.Disjoint ⟨s.gpr .a0, 64⟩ ⟨s.gpr .a5, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .a0, 64⟩ ⟨s.gpr .a6, 288⟩
  sC : Region.Disjoint ⟨s.gpr .a1, sl⟩ ⟨s.gpr .a5, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .a1, sl⟩ ⟨s.gpr .a6, 288⟩
  pC : Region.Disjoint ⟨s.gpr .a2, 32⟩ ⟨s.gpr .a5, 8192⟩
  pF : Region.Disjoint ⟨s.gpr .a2, 32⟩ ⟨s.gpr .a6, 288⟩
  mC : Region.Disjoint (msgR s) ⟨s.gpr .a5, 8192⟩
  mF : Region.Disjoint (msgR s) ⟨s.gpr .a6, 288⟩
  cF : Region.Disjoint ⟨s.gpr .a5, 8192⟩ ⟨s.gpr .a6, 288⟩
  spal : s.sp.toNat % 16 = 0
  sp : 208 ≤ s.sp.toNat
  bO : (below s.sp 208).Disjoint ⟨s.gpr .a0, 64⟩
  bS : (below s.sp 208).Disjoint ⟨s.gpr .a1, sl⟩
  bP : (below s.sp 208).Disjoint ⟨s.gpr .a2, 32⟩
  bM : (below s.sp 208).Disjoint (msgR s)
  bC : (below s.sp 208).Disjoint ⟨s.gpr .a5, 8192⟩
  bF : (below s.sp 208).Disjoint ⟨s.gpr .a6, 288⟩
  tal : (s.syms combSym).toNat % 8 = 0
  tfit : (s.syms combSym).toNat + 49152 ≤ 2 ^ 64
  words : ∀ q < 64 * 96, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q
  tW : ∀ r ∈ signW s, (TBL (s.syms combSym)).Disjoint r

/-- The values in `s1` and `s7`–`s11`. -/
def signV (s : State) : Reg → BitVec 64
  | .s1 => s.gpr .a1 | .s7 => s.gpr .a0 | .s8 => s.gpr .a3 | .s9 => s.gpr .a4 | .s10 => s.gpr .a5
  | .s11 => s.gpr .a6 | _ => 0

abbrev SignInv (s : State) : State → Prop := Inv s (s.gpr .a6) 224 signRegs (signV s) (signW s)

theorem signRegs_pres : ∀ r ∈ signRegs, r ∈ preserved := by decide

/-- The slots are apart from everything but the frame's first 224 bytes. -/
theorem sign_slot {s : State} (hp : SignPre sl s) :
    (slotArea (s.gpr .a6) 224 signRegs).Disjoint ⟨s.gpr .a0, 64⟩ ∧
    (slotArea (s.gpr .a6) 224 signRegs).Disjoint ⟨s.gpr .a5, 8192⟩ ∧
    (slotArea (s.gpr .a6) 224 signRegs).Disjoint (below s.sp 208) ∧
    ∀ d n, d + n ≤ 224 → (slotArea (s.gpr .a6) 224 signRegs).Disjoint ⟨s.gpr .a6 + BitVec.ofNat 64 d, n⟩ := by
  have hs : Region.Sub (slotArea (s.gpr .a6) 224 signRegs) ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega_using [h])

theorem signV_s7 (s : State) : signV s .s7 = s.gpr .a0 := rfl
theorem signV_s10 (s : State) : signV s .s10 = s.gpr .a5 := rfl
theorem signV_s11 (s : State) : signV s .s11 = s.gpr .a6 := rfl

/-- The setup: the registers saved, the pointers moved, `pk` copied to `192(F)`. -/
theorem signSetup_ok {s : State} (hp : SignPre sl s) :
    WP isa (.block signSetup) s fun t => SignInv s t ∧
      bytesAt t.mem (s.gpr .a6 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a2) 32 := by
  have hF : (⟨s.gpr .a6, 288⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsl : ∀ p ∈ slots 224 signRegs, p.2 + 8 ≤ 288 := by decide
  unfold signSetup
  refine save_ok hp.alF (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega_using [this])) fun u hu hsv hfr => ?_
  unfold mov
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ =>
    wp_mv fun u₅ h₅ => wp_mv fun u₆ h₆ => ?_
  have m₆ : u₆.mem = u.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g₆ : ∀ r, r ∉ signRegs → u₆.gpr r = u.gpr r := fun r hr => by
    simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, f⟩ := hr
    rw [h₆.other _ f, h₅.other _ e, h₄.other _ d, h₃.other _ c, h₂.other _ a, h₁.other _ b]
  have gu : ∀ r, u.gpr r = s.gpr r := fun r => hu.gpr r (by simp)
  have rd₆ : u₆.rd = s.rd := by rw [h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd]
  have wr₆ : u₆.wr = s.wr := by rw [h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr]
  have sp₆ : u₆.sp = s.sp := by rw [h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp]
  have e2 : u₆.gpr .a2 = s.gpr .a2 := by rw [g₆ _ (by decide), gu]
  have e11 : u₆.gpr .s11 = s.gpr .a6 := by rw [h₆.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), gu]
  have hP : (⟨s.gpr .a2, 32⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  rw [← List.append_nil (copyIn .a2 .s11 192)]
  refine copyIn_ok (P := s.gpr .a2) (F := s.gpr .a6) (o := 192) (by decide) (by decide) e2 e11 (by decide)
    (fun i hi => by rw [rd₆, wr₆]; exact in_base (List.mem_append_left _ hP) (by omega_using [hi]) (by omega_using [hi]))
    (fun i hi => by rw [wr₆]; exact in_base hF (by omega_using [hi]) (by omega_using [hi]))
    (hp.pF.sub_right (Offset.sub_base _ (by decide))) fun t ht hft hb => WP.block_nil ?_
  have fin : Frame [slotArea (s.gpr .a6) 224 signRegs, ⟨s.gpr .a6 + BitVec.ofNat 64 192, 32⟩] s.mem t.mem :=
    (hfr.mono (by simp)).trans (by rw [m₆] at hft; exact hft.mono (by simp))
  refine ⟨⟨by rw [ht.rd, rd₆], by rw [ht.wr, wr₆], by rw [ht.sp, sp₆], fun r hr => ?_, fun r hr hn => ?_, ?_,
    fin.sub fun r hr => ?_⟩, ?_⟩
  · rw [ht.gpr r (by revert hr; decide +revert)]
    simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.gpr, h₁.other _ (by decide), gu]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.gpr, gu]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [h₆.other _ (by decide), h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [e11]; rfl
  · have h5 : r ∉ [Reg.a5] := by
      simp only [List.mem_singleton]; intro e; rw [e] at hr; exact absurd hr (by decide)
    rw [ht.gpr r h5, g₆ r hn, gu r]
  · refine (hsv.frame_in (slots_in 224 signRegs) (m₆ ▸ hft) fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    exact (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨s.gpr .a6, 288⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨s.gpr .a6, 288⟩, by simp, Offset.sub_base _ (by decide)⟩
  · rw [hb]
    simp only [Spec.Ed25519.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [m₆]
    exact hfr _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc => (hp.pF.sub_right (Offset.sub_base _ (by decide))) _
        (Offset.contains_base _ (by omega_using [hi']) (by omega_using [hi'])) hc

/-- The regions a step of the body may write: the scratch space, the callees' frames, `out`, its
halves, or the frame below the slots. -/
def SignWr (s : State) (r : Region) : Prop :=
  r = ⟨s.gpr .a5, 8192⟩ ∨ r = below s.sp 208 ∨ r = ⟨s.gpr .a0, 64⟩ ∨ r = ⟨s.gpr .a0 + BitVec.ofNat 64 32, 32⟩ ∨
    r = ⟨s.gpr .a0, 32⟩ ∨ ∃ d n, d + n ≤ 224 ∧ r = ⟨s.gpr .a6 + BitVec.ofNat 64 d, n⟩

theorem signStep {s t t' : State} (hp : SignPre sl s) (h : SignInv s t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {Wc : List Region}
    (hf : Frame Wc t.mem t'.mem) (hW : ∀ r ∈ Wc, SignWr s r) : SignInv s t' := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := sign_slot hp
  refine Inv.step h signRegs_pres hrd hwr hsp hg hf (fun r hr => ?_) fun r hr => ?_
  · rcases hW r hr with rfl | rfl | rfl | rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨s.gpr .a0, 64⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨s.gpr .a0, 64⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨s.gpr .a6, 288⟩, by simp, Offset.sub_base _ (by omega_using [hdn])⟩
  · rcases hW r hr with rfl | rfl | rfl | rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact h₂
    · exact h₃
    · exact h₁
    · exact h₁.sub_right (Offset.sub_base _ (by decide))
    · exact h₁.sub_right (Region.sub_prefix (by decide))
    · exact h₄ d n hdn

end VG.Proof.Ed25519.RISCV64.Whole

end

end

/-!
# `vg_ed25519_sign_expanded` on RISCV64: the secret scalar and the nonce's prefix

The seed's digest, at `expanded`, copied to `128(F)` (`signCopy_ok`); then,
after any first step that leaves the digest there, its first half pruned
into `0(F)` and its second half copied to `32(F)` (`signExpandWith_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt decodeLE encodeLE)

variable {sl : Nat}

theorem sign_env {s t : State} (hp : SignPre sl s) (h : SignInv s t) : ScEnv (s.gpr .a5) t :=
  ⟨by rw [h.wr, hp.wr]; simp, by rw [h.sp]; exact hp.spal, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

theorem sign_Fw {s t : State} (hp : SignPre sl s) (h : SignInv s t) : (⟨s.gpr .a6, 288⟩ : Region) ∈ t.wr := by
  rw [h.wr, hp.wr]; simp

theorem sign_inF {s t : State} (hp : SignPre sl s) (h : SignInv s t) {d : Nat} (hd : d + 8 ≤ 288) :
    InRegions t.wr (s.gpr .a6 + BitVec.ofNat 64 d) 8 := in_base (sign_Fw hp h) hd (by omega_arith)

theorem sign_inF' {s t : State} (hp : SignPre sl s) (h : SignInv s t) {d : Nat} (hd : d + 8 ≤ 288) :
    InRegions (t.rd ++ t.wr) (s.gpr .a6 + BitVec.ofNat 64 d) 8 :=
  in_base (List.mem_append_right _ (sign_Fw hp h)) hd (by omega_arith)

/-- An input, while the body runs. -/
theorem sign_input {s t : State} (h : SignInv s t) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hO : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a0, 64⟩) (hC : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a5, 8192⟩)
    (hF : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a6, 288⟩) (hB : Region.Disjoint ⟨p, n⟩ (below s.sp 208)) :
    bytesAt t.mem p n = bytesAt s.mem p n :=
  bytes_keep h.frame hn fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hO
    · exact hC
    · exact hF
    · exact hB

/-- What the first step and the expansion write: the scratch space, the frame below its copy of
`pk`, the callees' frames. -/
abbrev expW (s : State) : List Region := [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6, 192⟩, below s.sp 208]

/-- The seed's digest, at `expanded`, copied to `128(F)`. -/
theorem signCopy_ok {s t : State} (hp : SignPre 64 s) (h : SignInv s t) :
    WP isa signCopy t fun t' => SignInv s t' ∧ Frame (expW s) t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .a6 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a1) 64 := by
  have hS : (⟨s.gpr .a1, 64⟩ : Region) ∈ t.rd := by rw [h.rd, hp.rd]; simp
  unfold signCopy
  rw [← List.append_nil (copyIn .s1 .s11 128 64)]
  refine copyIn_ok (P := s.gpr .a1) (F := s.gpr .a6) (o := 128) (n := 64) (by decide) (by decide)
    (h.regs _ (by decide)) (h.regs _ (by decide)) (by decide)
    (fun i hi => in_base (List.mem_append_left _ hS) (by omega_using [hi]) (by omega_using [hi]))
    (fun i hi => in_base (sign_Fw hp h) (by omega_using [hi]) (by omega_using [hi]))
    (hp.sF.sub_right (Offset.sub_base _ (by decide))) fun u hu hfu hb => WP.block_nil ?_
  refine ⟨signStep hp h hu.rd hu.wr hu.sp (fun r hr => hu.gpr r (by revert hr; cases r <;> decide)) hfu
      fun r hr => by
        rw [List.mem_singleton.mp hr]; exact .inr (.inr (.inr (.inr (.inr ⟨128, 64, by decide, rfl⟩)))),
    hfu.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨⟨s.gpr .a6, 192⟩, by simp, Offset.sub_base _ (by decide)⟩, ?_⟩
  rw [hb, sign_input h (by decide) hp.oS.symm hp.sC hp.sF hp.bS.symm]

/-- The pruning of the digest `D` at `128(F)` into `0(F)` and the copy of its second half to
`32(F)`, after the first step, which leaves `D` there. -/
theorem signExpandWith_ok {first : Prog isa} {D : List Byte} {s t : State} (hp : SignPre sl s)
    (hf : WP isa first t fun t' => SignInv s t' ∧ Frame (expW s) t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .a6 + BitVec.ofNat 64 128) 64 = D) :
    WP isa (signExpandWith first) t fun t' => SignInv s t' ∧ Frame (expW s) t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .a6) 32 = encodeLE 32 (Spec.Ed25519.prune D) ∧
      bytesAt t'.mem (s.gpr .a6 + BitVec.ofNat 64 32) 32 = D.drop 32 := by
  unfold signExpandWith
  refine WP.seq (WP.mono hf fun t₄ ⟨h₄, f₄, dg⟩ => ?_)
  -- The pruning, and the copy of the second half.
  refine prune_ok (f := .s11) (F := s.gpr .a6) (d := 128) (o := 0) (by decide) (h₄.regs _ (by decide)) hp.alF
    (by decide) (by decide) (by decide) (fun k hk => sign_inF' hp h₄ (by omega_arith)) (fun k hk => sign_inF hp h₄ (by omega_arith))
    fun u hu hfu hpr => ?_
  have hu' : SignInv s u := signStep hp h₄ hu.rd hu.wr hu.sp
    (fun r hr => hu.gpr r (by revert hr; cases r <;> decide)) hfu fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr (.inr (.inr (.inr ⟨0, 32, by decide, rfl⟩))))
  rw [← List.append_nil (copy32 .s11 160 32)]
  refine copy_ok (A := s.gpr .a6) (B := s.gpr .a6) (da := fun k => 160 + 8 * k) (db := fun k => 32 + 8 * k)
    (R := ⟨s.gpr .a6 + BitVec.ofNat 64 32, 32⟩) (by decide) (by decide)
    (hu'.regs _ (by decide)) (hu'.regs _ (by decide)) (fun k hk => ⟨by omega_arith, Spill.al8 hp.alF (by omega_arith)⟩)
    (fun k hk => ⟨by omega_arith, Spill.al8 hp.alF (by omega_arith)⟩) (fun k hk => sign_inF' hp hu' (by omega_arith)) (fun k hk => sign_inF hp hu' (by omega_arith))
    (fun k hk => Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi j hj => Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi j hj hij => Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) fun v hv hfv hw => WP.block_nil ?_
  have hv' : SignInv s v := signStep hp hu' hv.rd hv.wr hv.sp
    (fun r hr => hv.gpr r (by revert hr; cases r <;> decide)) hfv fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr (.inr (.inr (.inr ⟨32, 32, by decide, rfl⟩))))
  have F0 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 0, 32⟩ ⟨s.gpr .a6, 192⟩ := Offset.sub_base _ (by decide)
  have F32 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 32, 32⟩ ⟨s.gpr .a6, 192⟩ := Offset.sub_base _ (by decide)
  refine ⟨hv', ?_, ?_, ?_⟩
  · -- The writes: the first step's, the scalar's and the prefix's.
    refine f₄.trans <| (hfu.sub fun r hr => ?_).trans (hfv.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F0⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F32⟩
  · have e₁ : bytesAt v.mem (s.gpr .a6) 32 = bytesAt u.mem (s.gpr .a6) 32 :=
      bytes_keep hfv (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by decide) (by decide)
    have hdec : decodeLE (bytesAt u.mem (s.gpr .a6) 32) = Spec.Ed25519.prune D := by
      have := hpr
      rwa [BitVec.add_zero, dg] at this
    rw [e₁, Proof.Ed25519.bytesAt_encodeLE, hdec]
  · have e₁ : bytesAt v.mem (s.gpr .a6 + BitVec.ofNat 64 32) 32 =
        bytesAt u.mem (s.gpr .a6 + BitVec.ofNat 64 160) 32 :=
      bytes32_of_words fun k hk => by rw [Offset.add_add, Offset.add_add]; exact hw k hk
    have e₂ : bytesAt u.mem (s.gpr .a6 + BitVec.ofNat 64 160) 32 =
        bytesAt t₄.mem (s.gpr .a6 + BitVec.ofNat 64 160) 32 :=
      bytes_keep hfu (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    rw [e₁, e₂, show s.gpr .a6 + BitVec.ofNat 64 160 = s.gpr .a6 + BitVec.ofNat 64 128 + BitVec.ofNat 64 32 by
      rw [Offset.add_add], ← Proof.Ed25519.signatureBytes_drop, dg]

end VG.Proof.Ed25519.RISCV64.Whole

end

end

/-!
# `vg_ed25519_sign_expanded` on RISCV64: the nonce, and `R`

The prefix at `32(F)` and the message hashed into `128(F)`, the digest
reduced into the nonce at `64(F)` by a call of `vg_ed25519_scalar_reduce`,
and `R = [r]B` encoded into `out` by a call of `vg_ed25519_scalar_base`
(`signNonce_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (combSym)

variable {sl : Nat}

/-- The message's bytes. -/
abbrev msgB (s : State) : List Byte := bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat

theorem msgB_length (s : State) : (msgB s).length = (s.gpr .a4).toNat := by simp [bytesAt]

theorem sign_msg {s t : State} (hp : SignPre sl s) (h : SignInv s t) :
    bytesAt t.mem (s.gpr .a3) (s.gpr .a4).toNat = msgB s :=
  sign_input h (s.gpr .a4).isLt hp.oM.symm hp.mC hp.mF hp.bM.symm

theorem sign_msg_cov {s t : State} (hp : SignPre sl s) (h : SignInv s t) : Covers [msgR s] (t.rd ++ t.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := hi
    rw [h.rd, hp.rd]
    exact ⟨r, List.mem_append_left _ (by rw [List.mem_singleton.mp hr]; simp), hc⟩

/-- The message fits beside the scratch space. -/
theorem sign_len {s : State} (hp : SignPre sl s) : (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64 :=
  len_add_le (Nat.le_of_lt (s.gpr .a4).isLt) (by decide) hp.mC

theorem signNonce_ok (C : ShaOK) (B : BaseOk) {s t : State} (hp : SignPre sl s) (h : SignInv s t) {P : List Byte}
    (hP : bytesAt t.mem (s.gpr .a6 + BitVec.ofNat 64 32) 32 = P) (hsy : t.syms combSym = s.syms combSym) :
    WP isa signNonce t fun t' => SignInv s t' ∧
      Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩]
        t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .a6 + BitVec.ofNat 64 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (P ++ msgB s)) ∧
      bytesAt t'.mem (s.gpr .a0) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (P ++ msgB s))) := by
  obtain hPl : P.length = 32 := by rw [← hP]; simp [bytesAt]
  obtain hlen := sign_len hp
  -- The hashes write the scratch space and the callees' frames.
  obtain toL : ∀ {m m' : Mem} {sp : Addr}, sp = s.sp → Frame [⟨s.gpr .a5, 8192⟩, below sp 208] m m' →
      Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩] m m' :=
    fun e hf => by subst e; exact hf.mono (by simp)
  obtain scW : ∀ {t : State}, SignInv s t → ∀ r ∈ [(⟨s.gpr .a5, 8192⟩ : Region), below t.sp 208], SignWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  obtain F32 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 32, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  obtain F64 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  obtain F128 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  unfold signNonce
  refine WP.seq (WP.of_syms <| hashInit_ok C (sr := .s10) (h.regs _ (by decide)) (sign_env hp h)
    fun t₂ a b c f₂ g hr₂ sy₂ => ?_)
  obtain h₂ := signStep hp h a b c g f₂ (scW h)
  refine WP.seq (WP.of_syms <| hashUpdate_ok C (sr := .s10) (src := .s11) (off := 32) (len := 32) (by decide)
    (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 0) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₂)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ (sign_Fw hp h₂), 32, rfl, show 32 + 32 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F32) (by rw [h₂.sp]; exact hp.bF.sub_right F32) fun t₃ a b c f₃ g hr₃ sy₃ => ?_)
  obtain h₃ := signStep hp h₂ a b c g f₃ (scW h₂)
  obtain P₂ : bytesAt t₂.mem (s.gpr .a6 + BitVec.ofNat 64 32) 32 = P := by
    rw [← hP]
    exact bytes_keep f₂ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.cF.symm.sub_left F32
      · rw [h.sp]; exact hp.bF.symm.sub_left F32
  obtain r₃ : Repr t₃.mem (s.gpr .a5) P := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, P₂] at this
  refine WP.seq (WP.of_syms <| hashUpdate_ok C (sr := .s10) (src := .s8) (off := 0) (len := (s.gpr .a4).toNat) (by decide)
    (by decide) (by decide) (h₃.regs _ (by decide))
    (by rw [h₃.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 32) (by decide)) (Sets.mov (d := .a3) (n := .s9))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .s9 (by decide) (by decide) (by decide)])
    (by rw [h₃.regs _ (by decide)]; rfl) (sign_env hp h₃) (sign_msg_cov hp h₃)
    hp.mC (by rw [h₃.sp]; exact hp.bM) fun t₄ a b c f₄ g hr₄ sy₄ => ?_)
  obtain h₄ := signStep hp h₃ a b c g f₄ (scW h₃)
  obtain r₄ : Repr t₄.mem (s.gpr .a5) (P ++ msgB s) := by
    have := hr₄ P r₃ (by rw [hPl])
    rwa [sign_msg hp h₃] at this
  refine WP.seq (WP.of_syms <| hashFinalize_ok C (sr := .s10) (f := .s11) (o := 128) (out := s.gpr .a6 + BitVec.ofNat 64 128)
    (vc := fun g => g .s9 + BitVec.ofNat 64 32)
    (by decide) (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide)]; rfl)
    (Sets.addi (d := .a1) (n := .s9) (k := 32) (by decide)) (fun g g' hg => by rw [hg .s9 (by decide)])
    (sign_env hp h₄)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, sign_Fw hp h₄, 128, rfl, show 128 + 64 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F128) (by rw [h₄.sp]; exact hp.bF.sub_right F128) fun t₅ a b c f₅ g hd₅ sy₅ => ?_)
  obtain h₅ := signStep hp h₄ a b c g f₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inr (.inr (.inr ⟨128, 64, by decide, rfl⟩))))
    · exact .inr (.inl (by rw [h₄.sp])))
  obtain dg : bytesAt t₅.mem (s.gpr .a6 + BitVec.ofNat 64 128) 64 = Spec.Sha512.sha512 (P ++ msgB s) :=
    hd₅ _ r₄ (by rw [List.length_append, hPl, msgB_length]; omega_using [hlen])
      (by rw [h₄.regs _ (by decide), List.length_append, hPl, msgB_length, cnt_eq]; rfl)
  -- The nonce: `scalar_reduce`.
  obtain sF : Region.Disjoint ⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩ :=
    Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  obtain hFw := sign_Fw hp h₅
  obtain hCw : (⟨s.gpr .a5, 8192⟩ : Region) ∈ t₅.wr := (sign_env hp h₅).w
  obtain hOw : (⟨s.gpr .a0, 64⟩ : Region) ∈ t₅.wr := by rw [h₅.wr, hp.wr]; simp
  unfold mov
  refine WP.seq (WP.of_syms <| args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) fun t₆ k₆ c3 c4 c5 sy₆ => ?_)
  rw [h₅.regs _ (by decide), signV_s11] at c3 c4
  rw [h₅.regs _ (by decide), BitVec.add_zero, signV_s10] at c5
  obtain ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  refine WP.seq (WP.of_syms <| WP.call (k := reduceRISCV64) reduce_ok' (rd := [⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩])
    (wr := [⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩, ⟨s.gpr .a5, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact sF,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F64,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F128⟩
    (Covers.of_sub fun r hr => by
      rw [k₆.rd, k₆.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 128, rfl, show 128 + 64 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₆.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 64, rfl, show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₇ a b c f₇ g _ hpost sy₇ => ?_) (by decide +kernel))
  simp only [reduceRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    c3, c4, k₆.mem, dg] at hpost
  obtain h₇ := signStep hp h₅ (a.trans k₆.rd) (b.trans k₆.wr) (c.trans k₆.sp)
    (fun r hr => (g r hr).trans (k₆.pres r hr)) (k₆.mem ▸ f₇) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inr ⟨64, 32, by decide, rfl⟩))))
      · exact .inl rfl
  -- `R`: `scalar_base`.
  refine WP.seq (WP.of_syms <| args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) fun t₈ k₈ d3 d4 d5 sy₈ => ?_)
  rw [h₇.regs _ (by decide), BitVec.add_zero] at d3 d5
  rw [signV_s7] at d3
  rw [signV_s10] at d5
  rw [h₇.regs _ (by decide), signV_s11] at d4
  obtain sy : t₈.syms combSym = s.syms combSym := by rw [sy₈, sy₇, sy₆, sy₅, sy₄, sy₃, sy₂, hsy]
  obtain wd₈ : ∀ q < 64 * 96, t₈.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 =
      Impl.Ed25519.RISCV64.combWord q := fun q hq => by
    rw [← hp.words q hq, k₈.mem]
    exact h₇.frame.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])) hp.tW
      (by decide)
  refine WP.call (k := baseRV) B (rd := [⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩, TBL (s.syms combSym)])
    (wr := [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a5, 8192⟩])
    (basePre_call d3 d4 d5 sy hp.alC (hp.oC.sub_left (Region.sub_prefix (by decide))) (hp.cF.symm.sub_left F64)
      hp.tal hp.tfit wd₈ (hp.tW _ (by simp)))
    (Covers.of_sub fun r hr => by
      rw [k₈.rd, k₈.wr, h₇.wr, h₇.rd]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨s.gpr .a6, 288⟩, List.mem_append_right _ (by rw [hp.wr]; simp), 64, rfl,
          show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨TBL (s.syms combSym), List.mem_append_left _ (by rw [hp.rd]; simp), 0, by simp, by simp⟩
      · exact ⟨⟨s.gpr .a0, 64⟩, List.mem_append_right _ (by rw [hp.wr]; simp), 0, by simp, by simp⟩
      · exact ⟨⟨s.gpr .a5, 8192⟩, List.mem_append_right _ (by rw [hp.wr]; simp), 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₈.wr, h₇.wr, hp.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s.gpr .a0, 64⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨s.gpr .a5, 8192⟩, by simp, 0, by simp, by simp⟩) (fun t₉ a b c f₉ g _ hpost' => ?_) (by decide +kernel)
  simp only [baseRV, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    d3, d4, k₈.mem] at hpost'
  obtain h₉ := signStep hp h₇ (a.trans k₈.rd) (b.trans k₈.wr) (c.trans k₈.sp)
    (fun r hr => (g r hr).trans (k₈.pres r hr)) (k₈.mem ▸ f₉) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inl rfl))))
      · exact .inl rfl
  obtain keepN : bytesAt t₉.mem (s.gpr .a6 + BitVec.ofNat 64 64) 32 = bytesAt t₇.mem (s.gpr .a6 + BitVec.ofNat 64 64) 32 := by
    rw [← k₈.mem]
    exact bytes_keep f₉ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.oF.symm.sub_left F64 |>.sub_right (Region.sub_prefix (by decide))
      · exact hp.cF.symm.sub_left F64
  refine ⟨h₉, ?_, by rw [keepN, hpost], by rw [hpost', hpost]⟩
  -- The writes.
  obtain L64 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩ :=
    Region.sub_prefix (by decide)
  obtain L128 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩ := by
    have := Offset.sub (s.gpr .a6) (d := 128) (n := 64) (e := 64) (k := 128) (by decide) (by decide)
    exact this
  obtain g₅ : Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩]
      t₄.mem t₅.mem := f₅.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, by simp, L128⟩
    · exact ⟨below s.sp 208, by simp, by rw [h₄.sp]; exact fun _ h => h⟩
  obtain g₇ : Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩]
      t₅.mem t₇.mem := by
    rw [← k₆.mem]
    exact f₇.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, L64⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  obtain g₉ : Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩]
      t₇.mem t₉.mem := by
    rw [← k₈.mem]
    exact f₉.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  exact (toL h.sp f₂).trans <| (toL h₂.sp f₃).trans <| (toL h₃.sp f₄).trans <| g₅.trans <| g₇.trans g₉

end VG.Proof.Ed25519.RISCV64.Whole

end

end

/-! ### `Ed25519.RISCV64.Whole.ByRegister`, which only this module used -/

section

/-! ### `Ed25519.RISCV64.Whole.PublicKey`, which only this module used -/

section

/-!
# `vg_ed25519_public_key_expanded` on RISCV64, with its frame as an argument

`out` in `a0`, `expanded` (the seed's digest) in `a1`, `scratch` in `a2` and
the frame `F` (144 bytes) in `a3`: the registers saved at `96(F)`, the digest
copied into `F` (`pkCopy_ok`), its first half pruned into `64(F)`, and `[s]B`
encoded into `out` by a call of `vg_ed25519_scalar_base`
(`publicKeyExpanded_wp`). The body is proven for any first step that leaves
the digest in `F` (`publicKeyWith_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Impl.Ed25519.RISCV64 (combSym combWord)
open VG.Spec.Ed25519 (bytesAt decodeLE)

/-- What the body may write. -/
abbrev pkW (s : State) : List Region := [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩, ⟨s.gpr .a3, 144⟩, below s.sp 208]

variable {sl : Nat}

/-- The precondition, by register, for `sl` bytes at `a1` (the seed's digest, so 64). -/
structure PkPre (sl : Nat) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, sl⟩, TBL (s.syms combSym)]
  wr : s.wr = [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩, ⟨s.gpr .a3, 144⟩]
  oS : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a1, sl⟩
  oC : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a2, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a3, 144⟩
  sC : Region.Disjoint ⟨s.gpr .a1, sl⟩ ⟨s.gpr .a2, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .a1, sl⟩ ⟨s.gpr .a3, 144⟩
  cF : Region.Disjoint ⟨s.gpr .a2, 8192⟩ ⟨s.gpr .a3, 144⟩
  alC : (s.gpr .a2).toNat % 8 = 0
  alF : (s.gpr .a3).toNat % 8 = 0
  spal : s.sp.toNat % 16 = 0
  sp : 208 ≤ s.sp.toNat
  bO : (below s.sp 208).Disjoint ⟨s.gpr .a0, 32⟩
  bS : (below s.sp 208).Disjoint ⟨s.gpr .a1, sl⟩
  bC : (below s.sp 208).Disjoint ⟨s.gpr .a2, 8192⟩
  bF : (below s.sp 208).Disjoint ⟨s.gpr .a3, 144⟩
  tal : (s.syms combSym).toNat % 8 = 0
  tfit : (s.syms combSym).toNat + 49152 ≤ 2 ^ 64
  words : ∀ q < 64 * 96, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q
  tW : ∀ r ∈ pkW s, (TBL (s.syms combSym)).Disjoint r

/-- The values in `s7`–`s10`. -/
def pkV (s : State) : Reg → BitVec 64
  | .s7 => s.gpr .a0 | .s8 => s.gpr .a1 | .s9 => s.gpr .a2 | .s10 => s.gpr .a3 | _ => 0

abbrev PkInv (s : State) : State → Prop := Inv s (s.gpr .a3) 96 pkRegs (pkV s) (pkW s)

theorem pkRegs_pres : ∀ r ∈ pkRegs, r ∈ preserved := by decide

/-- The slots are apart from everything but the frame's first 96 bytes. -/
theorem pk_slot {s : State} (hp : PkPre sl s) :
    (slotArea (s.gpr .a3) 96 pkRegs).Disjoint ⟨s.gpr .a0, 32⟩ ∧
    (slotArea (s.gpr .a3) 96 pkRegs).Disjoint ⟨s.gpr .a2, 8192⟩ ∧
    (slotArea (s.gpr .a3) 96 pkRegs).Disjoint (below s.sp 208) ∧
    ∀ d n, d + n ≤ 96 → (slotArea (s.gpr .a3) 96 pkRegs).Disjoint ⟨s.gpr .a3 + BitVec.ofNat 64 d, n⟩ := by
  obtain hs : Region.Sub (slotArea (s.gpr .a3) 96 pkRegs) ⟨s.gpr .a3, 144⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega_using [h])

/-- The setup: the registers saved, the pointers moved to `s7`–`s10`. -/
theorem pkSetup_ok {s : State} (hp : PkPre sl s) :
    WP isa (.block (saveRegs .a3 96 pkRegs ++
      [mov .s7 .a0, mov .s8 .a1, mov .s9 .a2, mov .s10 .a3])) s (PkInv s) := by
  obtain hF : (⟨s.gpr .a3, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hsl : ∀ p ∈ slots 96 pkRegs, p.2 + 8 ≤ 144 := by decide
  refine save_ok hp.alF (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega_using [this])) fun u hu hsv hfr => ?_
  unfold mov
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => WP.block_nil ?_
  obtain m : u₄.mem = u.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  obtain g : ∀ r, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → u₄.gpr r = u.gpr r := fun r a b c d => by
    rw [h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  obtain gu : ∀ r, u.gpr r = s.gpr r := fun r => hu.gpr r (by simp)
  refine ⟨by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd], by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr],
    by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp], fun r hr => ?_, fun r hr hn => ?_, m ▸ hsv,
    m ▸ (hfr.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨⟨s.gpr .a3, 144⟩, by simp, Offset.sub_base _ (by decide)⟩)⟩
  · simp only [pkRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, gu]; rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), gu]; rfl
    · rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
  · simp only [pkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨a, b, c, d⟩ := hn
    rw [g r a b c d, gu r]

/-- The bytes at `a1`, while the body runs. -/
theorem pk_seed {s t : State} (hp : PkPre sl s) (h : PkInv s t) (hn : sl < 2 ^ 64) :
    bytesAt t.mem (s.gpr .a1) sl = bytesAt s.mem (s.gpr .a1) sl :=
  bytes_keep h.frame hn fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.oS.symm
    · exact hp.sC
    · exact hp.sF
    · exact hp.bS.symm

/-- Region facts for `Inv.step`. -/
theorem pk_inW {s : State} : (⟨s.gpr .a2, 8192⟩ : Region) ∈ pkW s ∧ (⟨s.gpr .a0, 32⟩ : Region) ∈ pkW s ∧
    (⟨s.gpr .a3, 144⟩ : Region) ∈ pkW s ∧ below s.sp 208 ∈ pkW s := by simp

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- The seed's digest, at `expanded`, copied to `0(F)`. -/
theorem pkCopy_ok {s t : State} (hp : PkPre 64 s) (h : PkInv s t) :
    WP isa pkCopy t fun u => PkInv s u ∧ bytesAt u.mem (s.gpr .a3) 64 = bytesAt s.mem (s.gpr .a1) 64 := by
  obtain ⟨-, -, -, hsl₄⟩ := pk_slot hp
  obtain hFw : (⟨s.gpr .a3, 144⟩ : Region) ∈ t.wr := by rw [h.wr, hp.wr]; simp
  obtain hS : (⟨s.gpr .a1, 64⟩ : Region) ∈ t.rd := by rw [h.rd, hp.rd]; simp
  unfold pkCopy
  rw [← List.append_nil (copyIn .s8 .s10 0 64)]
  refine copyIn_ok (P := s.gpr .a1) (F := s.gpr .a3) (o := 0) (n := 64) (by decide) (by decide)
    (h.regs _ (by decide)) (h.regs _ (by decide)) (by decide)
    (fun i hi => in_base (List.mem_append_left _ hS) (by omega_using [hi]) (by omega_using [hi]))
    (fun i hi => in_base hFw (by omega_using [hi]) (by omega_using [hi]))
    (hp.sF.sub_right (Offset.sub_base _ (by decide))) fun u hu hfu hb => WP.block_nil ?_
  refine ⟨h.step pkRegs_pres hu.rd hu.wr hu.sp (fun r hr => hu.gpr r (by revert hr; cases r <;> decide)) hfu
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, pk_inW.2.2.1, Offset.sub_base _ (by decide)⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hsl₄ 0 64 (by decide)), ?_⟩
  rw [BitVec.add_zero] at hb
  rw [hb, pk_seed hp h (by decide)]

/-- The body, from a first step that leaves the digest `D` at `0(F)`. -/
theorem publicKeyWith_wp (B : BaseOk) {first : Prog isa} {D : List Byte} {s : State} (hp : PkPre sl s)
    (hfirst : ∀ t, PkInv s t → WP isa first t fun u => PkInv s u ∧ bytesAt u.mem (s.gpr .a3) 64 = D) :
    WP isa (publicKeyWith first) s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ bytesAt t.mem (s.gpr .a0) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul (Spec.Ed25519.prune D) Spec.Ed25519.basePoint) := by
  obtain ⟨hsl₁, hsl₂, -, hsl₄⟩ := pk_slot hp
  obtain ⟨wC, wO, wF, -⟩ := pk_inW (s := s)
  obtain hFw : (⟨s.gpr .a3, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hCw : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hOw : (⟨s.gpr .a0, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold publicKeyWith
  refine WP.seq (WP.mono_syms (pkSetup_ok hp) fun t₁ h₁ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (hfirst t₁ h₁) fun t₄ ⟨h₄, dg⟩ sy₄ => ?_)
  -- The pruning, and the arguments of `scalar_base`.
  obtain hFr : ∀ d, d + 8 ≤ 144 → InRegions (t₄.rd ++ t₄.wr) (s.gpr .a3 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base (List.mem_append_right _ hFw) hd (by omega_using [hd])
  obtain hFw' : ∀ d, d + 8 ≤ 144 → InRegions t₄.wr (s.gpr .a3 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base hFw hd (by omega_using [hd])
  refine WP.seq (WP.of_syms <| prune_ok (f := .s10) (F := s.gpr .a3) (d := 0) (o := 64) (by decide) (h₄.regs _ (by decide)) hp.alF
    (by decide) (by decide) (by decide) (fun k hk => hFr _ (by omega_using [hk])) (fun k hk => hFw' _ (by omega_using [hk]))
    fun u hu hfu hpr => ?_)
  unfold mov
  refine wp_mv fun v₁ e₁ => wp_addi (by decide) fun v₂ e₂ =>
    wp_mv fun t₅ e₃ => WP.block_nil fun sy₅ => ?_
  obtain g₅ : ∀ r ∈ preserved, t₅.gpr r = t₄.gpr r := fun r hr => by
    obtain ⟨p3, p4, p5, -, -⟩ := pres_args hr
    rw [e₃.other _ p5, e₂.other _ p4, e₁.other _ p3, hu.gpr _ (by revert hr; cases r <;> decide)]
  obtain m₅ : t₅.mem = u.mem := by rw [e₃.mem, e₂.mem, e₁.mem]
  obtain h₅ : PkInv s t₅ := h₄.step pkRegs_pres (by rw [e₃.rd, e₂.rd, e₁.rd, hu.rd])
    (by rw [e₃.wr, e₂.wr, e₁.wr, hu.wr]) (by rw [e₃.sp, e₂.sp, e₁.sp, hu.sp]) g₅ (m₅ ▸ hfu)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, wF, Offset.sub_base _ (by decide)⟩)
    fun r hr => by rw [List.mem_singleton.mp hr]; exact hsl₄ 64 32 (by decide)
  obtain c3 : t₅.gpr .a0 = s.gpr .a0 := by
    rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, hu.gpr _ (by decide),
      h₄.regs _ (by decide)]; rfl
  obtain c4 : t₅.gpr .a1 = s.gpr .a3 + BitVec.ofNat 64 64 := by
    rw [e₃.other _ (by decide), e₂.gpr, e₁.other _ (by decide), hu.gpr _ (by decide), h₄.regs _ (by decide)]; rfl
  obtain c5 : t₅.gpr .a2 = s.gpr .a2 := by
    rw [e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), hu.gpr _ (by decide),
      h₄.regs _ (by decide)]; rfl
  obtain hdec : decodeLE (bytesAt t₅.mem (s.gpr .a3 + BitVec.ofNat 64 64) 32) = Spec.Ed25519.prune D := by
    rw [m₅, hpr, BitVec.add_zero, dg]
  -- `scalar_base`.
  obtain sc4 : Region.Sub ⟨s.gpr .a3 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a3, 144⟩ := Offset.sub_base _ (by decide)
  obtain sy : t₅.syms combSym = s.syms combSym := by rw [sy₅, sy₄, sy₁]
  obtain wd₅ : ∀ q < 64 * 96, t₅.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q :=
    fun q hq => by
      rw [← hp.words q hq]
      exact h₅.frame.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])) hp.tW
        (by decide)
  refine WP.seq (WP.call (k := baseRV) B (rd := [⟨s.gpr .a3 + BitVec.ofNat 64 64, 32⟩, TBL (s.syms combSym)])
    (wr := [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩]) (basePre_call c3 c4 c5 sy hp.alC hp.oC
      (hp.cF.symm.sub_left sc4) hp.tal hp.tfit wd₅ (hp.tW _ (by simp)))
    (Covers.of_sub fun r hr => by
      rw [h₅.rd, h₅.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 32 ≤ 144 by decide⟩
      · exact ⟨TBL (s.syms combSym), List.mem_append_left _ (by rw [hp.rd]; simp), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hOw, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (fun a n ⟨r, hr, hc⟩ => by
      rw [h₅.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hOw, hc⟩
      · exact ⟨_, hCw, hc⟩) (fun t₆ a b c hf hg _ hpost => ?_) (by decide +kernel))
  simp only [baseRV, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    c3, c4] at hpost
  obtain h₆ : PkInv s t₆ := h₅.step pkRegs_pres a b c hg hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, wO, sub_refl _⟩
      · exact ⟨_, wC, sub_refl _⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hsl₁
      · exact hsl₂
  -- The restores.
  obtain hrl : ∀ p ∈ restoreList 96 pkRegs, p.2 + 8 ≤ 144 := by decide
  refine restore_ok h₆ hp.alF (h₆.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => by rw [h₆.wr]; exact in_base (List.mem_append_right _ hFw) (hrl p hp') (by have := hrl p hp'; omega_using [this]))
    fun t₇ g₇ sp₇ ra₇ m₇ _ => ⟨g₇, sp₇, ra₇, ?_⟩
  rw [m₇, hpost, Spec.Ed25519.scalarBase, hdec]

/-- From the seed's digest at `expanded`: the public key of every seed with that digest. -/
theorem publicKeyExpanded_wp (B : BaseOk) {s : State} (hp : PkPre 64 s) :
    WP isa publicKeyExpanded s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ ∀ seed : List Byte, bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed →
        bytesAt t.mem (s.gpr .a0) 32 = Spec.Ed25519.publicKey seed :=
  WP.mono (publicKeyWith_wp B (D := bytesAt s.mem (s.gpr .a1) 64) hp fun _ h => pkCopy_ok hp h) fun _ ⟨g, sp, ra, ho⟩ =>
    ⟨g, sp, ra, fun _ hs => by rw [ho, hs]; rfl⟩

end VG.Proof.Ed25519.RISCV64.Whole

end

end

/-! ### `Ed25519.RISCV64.Whole.SignCached`, which only this module used -/

section

/-! ### `Ed25519.RISCV64.Whole.SignChallenge`, which only this module used -/

section

/-!
# `vg_ed25519_sign_expanded` on RISCV64: the challenge, and `S`

`R` (in `out`), the copy of `pk` at `192(F)` and the message hashed into
`128(F)`, the digest reduced into the challenge at `96(F)` by a call of
`vg_ed25519_scalar_reduce`, and `S = (r + k s) mod L` into `out + 32` by a
call of `vg_ed25519_scalar_mul_add` (`signChallenge_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)

variable {sl : Nat}

/-- What the challenge's steps write. -/
abbrev chW (s : State) : List Region :=
  [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 96, 96⟩, below s.sp 208, ⟨s.gpr .a0 + BitVec.ofNat 64 32, 32⟩]

theorem signChallenge_ok (C : ShaOK) {s t : State} (hp : SignPre sl s) (h : SignInv s t) {Rb Nb Sb Kb : List Byte}
    (hR : bytesAt t.mem (s.gpr .a0) 32 = Rb) (hN : bytesAt t.mem (s.gpr .a6 + BitVec.ofNat 64 64) 32 = Nb)
    (hS : bytesAt t.mem (s.gpr .a6) 32 = Sb) (hK : bytesAt t.mem (s.gpr .a6 + BitVec.ofNat 64 192) 32 = Kb) :
    WP isa signChallenge t fun t' => SignInv s t' ∧ bytesAt t'.mem (s.gpr .a0) 32 = Rb ∧
      bytesAt t'.mem (s.gpr .a0 + BitVec.ofNat 64 32) 32 =
        Spec.Ed25519.scalarMulAdd Nb (Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (Rb ++ Kb ++ msgB s))) Sb := by
  obtain hRl : Rb.length = 32 := by rw [← hR]; simp [bytesAt]
  obtain hKl : Kb.length = 32 := by rw [← hK]; simp [bytesAt]
  obtain hlen := sign_len hp
  obtain toL : ∀ {m m' : Mem} {sp : Addr}, sp = s.sp → Frame [⟨s.gpr .a5, 8192⟩, below sp 208] m m' →
      Frame (chW s) m m' := fun e hf => by subst e; exact hf.mono (by simp)
  obtain scW : ∀ {t : State}, SignInv s t → ∀ r ∈ [(⟨s.gpr .a5, 8192⟩ : Region), below t.sp 208], SignWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  obtain F0 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 0, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  obtain F64 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  obtain F96 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 96, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  obtain F128 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  obtain F192 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  obtain O32 : Region.Sub ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a0, 64⟩ := Region.sub_prefix (by decide)
  obtain O32' : Region.Sub ⟨s.gpr .a0 + BitVec.ofNat 64 32, 32⟩ ⟨s.gpr .a0, 64⟩ := Offset.sub_base _ (by decide)
  -- What the steps keep.
  obtain keep : ∀ {m m' : Mem} {p : Addr}, Frame (chW s) m m' → Region.Sub ⟨p, 32⟩ ⟨s.gpr .a0, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .a6 + BitVec.ofNat 64 d) ∨ p = s.gpr .a6 + BitVec.ofNat 64 192 →
      bytesAt m' p 32 = bytesAt m p 32 := by
    intro m m' p hf hpr
    refine bytes_keep hf (by decide) fun r hr => ?_
    obtain hF : Region.Sub ⟨p, 32⟩ ⟨s.gpr .a6, 288⟩ ∨ Region.Sub ⟨p, 32⟩ ⟨s.gpr .a0, 32⟩ := by
      rcases hpr with h | ⟨d, hd, rfl⟩ | rfl
      · exact .inr h
      · exact .inl (Offset.sub_base _ (by omega_using [hd]))
      · exact .inl F192
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hF with hF | hF
      · exact hp.cF.symm.sub_left hF
      · exact (hp.oC.sub_left O32).sub_left hF
    · rcases hpr with h | ⟨d, hd, rfl⟩ | rfl
      · exact (hp.oF.sub_left O32).sub_left h |>.sub_right (Offset.sub_base _ (by decide))
      · exact Offset.disjoint _ (.inl hd) (by omega_using [hd]) (by decide)
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · rcases hF with hF | hF
      · exact hp.bF.symm.sub_left hF
      · exact (hp.bO.symm.sub_left O32).sub_left hF
    · rcases hF with hF | hF
      · exact hp.oF.symm.sub_left hF |>.sub_right O32'
      · exact ((Offset.base_disjoint _ (by decide) (by decide) : Region.Disjoint ⟨s.gpr .a0, 32⟩
          ⟨s.gpr .a0 + BitVec.ofNat 64 32, 32⟩)).sub_left hF
  obtain kR : ∀ {m m' : Mem}, Frame (chW s) m m' → bytesAt m' (s.gpr .a0) 32 = bytesAt m (s.gpr .a0) 32 :=
    fun hf => keep hf (.inl fun _ h => h)
  obtain kF : ∀ {m m' : Mem} {d : Nat}, Frame (chW s) m m' → d + 32 ≤ 96 →
      bytesAt m' (s.gpr .a6 + BitVec.ofNat 64 d) 32 = bytesAt m (s.gpr .a6 + BitVec.ofNat 64 d) 32 :=
    fun hf hd => keep hf (.inr (.inl ⟨_, hd, rfl⟩))
  unfold signChallenge
  refine WP.seq (hashInit_ok C (sr := .s10) (h.regs _ (by decide)) (sign_env hp h)
    fun t₂ a b c f₂ g hr₂ => ?_)
  obtain h₂ := signStep hp h a b c g f₂ (scW h)
  obtain hOw : (⟨s.gpr .a0, 64⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  refine WP.seq (hashUpdate_ok C (sr := .s10) (src := .s7) (off := 0) (len := 32) (by decide)
    (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 0) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₂)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, h₂.rd, h₂.wr]
      exact ⟨_, List.mem_append_right _ hOw, 0, by simp, by simp⟩)
    (hp.oC.sub_left O32) (by rw [h₂.sp]; exact hp.bO.sub_right O32) fun t₃ a b c f₃ g hr₃ => ?_)
  obtain h₃ := signStep hp h₂ a b c g f₃ (scW h₂)
  obtain e₂ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .a0, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .a6 + BitVec.ofNat 64 d) ∨ p = s.gpr .a6 + BitVec.ofNat 64 192 →
      bytesAt t₂.mem p 32 = bytesAt t.mem p 32 := fun hpr => keep (toL h.sp f₂) hpr
  obtain r₃ : Repr t₃.mem (s.gpr .a5) Rb := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, e₂ (.inl fun _ h => h), hR] at this
  obtain e₃ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .a0, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .a6 + BitVec.ofNat 64 d) ∨ p = s.gpr .a6 + BitVec.ofNat 64 192 →
      bytesAt t₃.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep (toL h₂.sp f₃) hpr).trans (e₂ hpr)
  refine WP.seq (hashUpdate_ok C (sr := .s10) (src := .s11) (off := 192) (len := 32) (by decide)
    (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 32) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₃)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ (sign_Fw hp h₃), 192, rfl, show 192 + 32 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F192) (by rw [h₃.sp]; exact hp.bF.sub_right F192) fun t₄ a b c f₄ g hr₄ => ?_)
  obtain h₄ := signStep hp h₃ a b c g f₄ (scW h₃)
  obtain r₄ : Repr t₄.mem (s.gpr .a5) (Rb ++ Kb) := by
    have := hr₄ Rb r₃ (by rw [hRl])
    rwa [e₃ (.inr (.inr rfl)), hK] at this
  obtain e₄ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .a0, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .a6 + BitVec.ofNat 64 d) ∨ p = s.gpr .a6 + BitVec.ofNat 64 192 →
      bytesAt t₄.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep (toL h₃.sp f₄) hpr).trans (e₃ hpr)
  refine WP.seq (hashUpdate_ok C (sr := .s10) (src := .s8) (off := 0) (len := (s.gpr .a4).toNat) (by decide)
    (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 64) (by decide)) (Sets.mov (d := .a3) (n := .s9))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .s9 (by decide) (by decide) (by decide)])
    (by rw [h₄.regs _ (by decide)]; rfl) (sign_env hp h₄) (sign_msg_cov hp h₄)
    hp.mC (by rw [h₄.sp]; exact hp.bM) fun t₅ a b c f₅ g hr₅ => ?_)
  obtain h₅ := signStep hp h₄ a b c g f₅ (scW h₄)
  obtain r₅ : Repr t₅.mem (s.gpr .a5) (Rb ++ Kb ++ msgB s) := by
    have := hr₅ (Rb ++ Kb) r₄ (by rw [List.length_append, hRl, hKl])
    rwa [sign_msg hp h₄] at this
  obtain e₅ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .a0, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .a6 + BitVec.ofNat 64 d) ∨ p = s.gpr .a6 + BitVec.ofNat 64 192 →
      bytesAt t₅.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep (toL h₄.sp f₅) hpr).trans (e₄ hpr)
  refine WP.seq (hashFinalize_ok C (sr := .s10) (f := .s11) (o := 128) (out := s.gpr .a6 + BitVec.ofNat 64 128)
    (vc := fun g => g .s9 + BitVec.ofNat 64 64)
    (by decide) (by decide) (by decide) (h₅.regs _ (by decide))
    (by rw [h₅.regs _ (by decide)]; rfl)
    (Sets.addi (d := .a1) (n := .s9) (k := 64) (by decide)) (fun g g' hg => by rw [hg .s9 (by decide)])
    (sign_env hp h₅)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, sign_Fw hp h₅, 128, rfl, show 128 + 64 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F128) (by rw [h₅.sp]; exact hp.bF.sub_right F128) fun t₆ a b c f₆ g hd₆ => ?_)
  obtain h₆ := signStep hp h₅ a b c g f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inr (.inr (.inr ⟨128, 64, by decide, rfl⟩))))
    · exact .inr (.inl (by rw [h₅.sp])))
  obtain dg : bytesAt t₆.mem (s.gpr .a6 + BitVec.ofNat 64 128) 64 = Spec.Sha512.sha512 (Rb ++ Kb ++ msgB s) :=
    hd₆ _ r₅ (by rw [List.length_append, List.length_append, hRl, hKl, msgB_length]; omega_using [hlen])
      (by rw [h₅.regs _ (by decide), List.length_append, List.length_append, hRl, hKl, msgB_length, cnt_eq]; rfl)
  obtain f₆' : Frame (chW s) t₅.mem t₆.mem := f₆.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨s.gpr .a6 + BitVec.ofNat 64 96, 96⟩, by simp,
        Offset.sub (s.gpr .a6) (d := 128) (n := 64) (e := 96) (k := 96) (by decide) (by decide)⟩
    · exact ⟨below s.sp 208, by simp, by rw [h₅.sp]; exact fun _ h => h⟩
  obtain e₆ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .a0, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .a6 + BitVec.ofNat 64 d) ∨ p = s.gpr .a6 + BitVec.ofNat 64 192 →
      bytesAt t₆.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep f₆' hpr).trans (e₅ hpr)
  obtain ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  obtain hFw := sign_Fw hp h₆
  obtain hCw : (⟨s.gpr .a5, 8192⟩ : Region) ∈ t₆.wr := (sign_env hp h₆).w
  -- The challenge: `scalar_reduce`.
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) fun t₇ k₇ c3 c4 c5 => ?_)
  rw [h₆.regs _ (by decide), signV_s11] at c3 c4
  rw [h₆.regs _ (by decide), BitVec.add_zero, signV_s10] at c5
  refine WP.seq (WP.call (k := reduceRISCV64) reduce_ok' (rd := [⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩])
    (wr := [⟨s.gpr .a6 + BitVec.ofNat 64 96, 32⟩, ⟨s.gpr .a5, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F96,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F128⟩
    (Covers.of_sub fun r hr => by
      rw [k₇.rd, k₇.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 128, rfl, show 128 + 64 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 96, rfl, show 96 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₇.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 96, rfl, show 96 + 32 ≤ 288 by decide⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₈ a b c f₈ g _ hpost => ?_) (by decide +kernel))
  simp only [reduceRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    c3, c4, k₇.mem, dg] at hpost
  obtain h₈ := signStep hp h₆ (a.trans k₇.rd) (b.trans k₇.wr) (c.trans k₇.sp)
    (fun r hr => (g r hr).trans (k₇.pres r hr)) (k₇.mem ▸ f₈) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inr ⟨96, 32, by decide, rfl⟩))))
      · exact .inl rfl
  obtain f₈' : Frame (chW s) t₆.mem t₈.mem := by
    rw [← k₇.mem]
    exact f₈.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s.gpr .a6 + BitVec.ofNat 64 96, 96⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  obtain e₈ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .a0, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .a6 + BitVec.ofNat 64 d) ∨ p = s.gpr .a6 + BitVec.ofNat 64 192 →
      bytesAt t₈.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep f₈' hpr).trans (e₆ hpr)
  -- `S`: `scalar_mul_add`.
  refine WP.seq (args5_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun t₉ k₉ d3 d4 d5 d6 d7 => ?_)
  rw [h₈.regs _ (by decide), signV_s7] at d3
  rw [h₈.regs _ (by decide), signV_s11] at d4 d5
  rw [h₈.regs _ (by decide), signV_s11, BitVec.add_zero] at d6
  rw [h₈.regs _ (by decide), signV_s10, BitVec.add_zero] at d7
  obtain hOw' : (⟨s.gpr .a0, 64⟩ : Region) ∈ t₉.wr := by rw [k₉.wr, h₈.wr, hp.wr]; simp
  obtain hFw' : (⟨s.gpr .a6, 288⟩ : Region) ∈ t₉.wr := by rw [k₉.wr]; exact sign_Fw hp h₈
  obtain hCw' : (⟨s.gpr .a5, 8192⟩ : Region) ∈ t₉.wr := by rw [k₉.wr]; exact (sign_env hp h₈).w
  refine WP.call (k := mulAddRISCV64) mulAdd_ok'
    (rd := [⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 96, 32⟩, ⟨s.gpr .a6, 32⟩])
    (wr := [⟨s.gpr .a0 + BitVec.ofNat 64 32, 32⟩, ⟨s.gpr .a5, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), ce _ _ (by decide), ce _ _ (by decide), d4, d5, d6],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), d3, d7],
      by rw [ce _ _ (by decide), ce _ _ (by decide), d3, d7]; exact hp.oC.sub_left O32',
      by rw [ce _ _ (by decide), ce _ _ (by decide), d4, d7]; exact hp.cF.symm.sub_left F64,
      by rw [ce _ _ (by decide), ce _ _ (by decide), d5, d7]; exact hp.cF.symm.sub_left F96,
      by rw [ce _ _ (by decide), ce _ _ (by decide), d6, d7]
         exact hp.cF.symm.sub_left (Region.sub_prefix (by decide))⟩
    (Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw', 64, rfl, show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw', 96, rfl, show 96 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw', 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hOw', 32, rfl, show 32 + 32 ≤ 64 by decide⟩
      · exact ⟨_, List.mem_append_right _ hCw', 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hOw', 32, rfl, show 32 + 32 ≤ 64 by decide⟩
      · exact ⟨_, hCw', 0, by simp, by simp⟩) (fun t₁₀ a b c f₁₀ g _ hpost' => ?_) (by decide +kernel)
  simp only [mulAddRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide),
    d3, d4, d5, d6, k₉.mem] at hpost'
  obtain h₁₀ := signStep hp h₈ (a.trans k₉.rd) (b.trans k₉.wr) (c.trans k₉.sp)
    (fun r hr => (g r hr).trans (k₉.pres r hr)) (k₉.mem ▸ f₁₀) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inl rfl)))
      · exact .inl rfl
  obtain f₁₀' : Frame (chW s) t₈.mem t₁₀.mem := by
    rw [← k₉.mem]
    exact f₁₀.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  refine ⟨h₁₀, by rw [kR f₁₀', e₈ (.inl fun _ h => h), hR], ?_⟩
  rw [hpost', e₈ (.inr (.inl ⟨64, by decide, rfl⟩)), hN, hpost,
    show s.gpr .a6 = s.gpr .a6 + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm, e₈ (.inr (.inl ⟨0, by decide, rfl⟩)),
    ← show s.gpr .a6 = s.gpr .a6 + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm, hS]

end VG.Proof.Ed25519.RISCV64.Whole

end

end


/-!
# `vg_ed25519_sign_expanded` on RISCV64, with its frame as an argument

The setup, the three phases and the restores, from any first step that leaves
the seed's digest `D` at `128(F)` (`signWith_wp`): `out` then holds `R ‖ S`
(`signFrom`), which is RFC 8032's signature (`Proof.Ed25519.sign_pipeline`) for
the seed when `pk` is its public key. The first step copies the digest at
`expanded` (`signExpanded_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)

variable {sl : Nat}

/-- `R ‖ S` from the seed's digest `D`, the public key `pk` and the message. -/
def signFrom (D pk msg : List Byte) : List Byte :=
  let nonce := Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (D.drop 32 ++ msg))
  let r := Spec.Ed25519.scalarBase nonce
  r ++ Spec.Ed25519.scalarMulAdd nonce (Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (r ++ pk ++ msg)))
    (Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune D))

theorem signFrom_sha512 (seed pk msg : List Byte) (hpk : pk = Spec.Ed25519.publicKey seed) :
    signFrom (Spec.Sha512.sha512 seed) pk msg = Spec.Ed25519.sign seed msg :=
  Proof.Ed25519.sign_pipeline seed pk msg hpk

theorem signWith_wp (C : ShaOK) (B : BaseOk) {first : Prog isa} {D : List Byte} {s : State} (hp : SignPre sl s)
    (hfirst : ∀ t, SignInv s t → WP isa first t fun t' => SignInv s t' ∧ Frame (expW s) t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .a6 + BitVec.ofNat 64 128) 64 = D) :
    WP isa (signWith first) s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ bytesAt t.mem (s.gpr .a0) 64 = signFrom D (bytesAt s.mem (s.gpr .a2) 32) (msgB s) := by
  obtain F192 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  obtain F0 : Region.Sub ⟨s.gpr .a6, 32⟩ ⟨s.gpr .a6, 288⟩ := Region.sub_prefix (by decide)
  unfold signWith
  refine WP.seq (WP.mono_syms (signSetup_ok hp) fun t₁ ⟨h₁, hk₁⟩ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (signExpandWith_ok hp (hfirst t₁ h₁)) fun t₂ ⟨h₂, f₂, hs₂, hp₂⟩ sy₂ => ?_)
  obtain hk₂ : bytesAt t₂.mem (s.gpr .a6 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a2) 32 := by
    rw [← hk₁]
    exact bytes_keep f₂ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.cF.symm.sub_left F192
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact hp.bF.symm.sub_left F192
  refine WP.seq (WP.mono (signNonce_ok C B hp h₂ hp₂ (by rw [sy₂, sy₁])) fun t₃ ⟨h₃, f₃, hn₃, hr₃⟩ => ?_)
  obtain keep₃ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .a6, 288⟩ →
      (Region.Disjoint ⟨p, 32⟩ ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩) →
      bytesAt t₃.mem p 32 = bytesAt t₂.mem p 32 := fun hs hd =>
    bytes_keep f₃ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.cF.symm.sub_left hs
      · exact hd
      · exact hp.bF.symm.sub_left hs
      · exact (hp.oF.symm.sub_left hs).sub_right (Region.sub_prefix (by decide))
  obtain hk₃ := (keep₃ F192 (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))).trans hk₂
  obtain hs₃ := (keep₃ F0 (Offset.base_disjoint _ (by decide) (by decide))).trans hs₂
  refine WP.seq (WP.mono (signChallenge_ok C hp h₃ hr₃ hn₃ hs₃ hk₃) fun t₄ ⟨h₄, hR, hS⟩ => ?_)
  obtain hFw : (⟨s.gpr .a6, 288⟩ : Region) ∈ t₄.rd ++ t₄.wr := List.mem_append_right _ (sign_Fw hp h₄)
  obtain hrl : ∀ p ∈ restoreList 224 signRegs, p.2 + 8 ≤ 288 := by decide
  refine restore_ok h₄ hp.alF (h₄.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega_using [this]))
    fun t₅ g₅ sp₅ ra₅ m₅ _ => ⟨g₅, sp₅, ra₅, ?_⟩
  rw [m₅, Proof.Ed25519.signatureBytes_split, hR, hS]
  rfl

/-- From the seed's digest at `expanded`: the signature of every seed with that digest, given
that `pk` is the public key of one. -/
theorem signExpanded_wp (C : ShaOK) (B : BaseOk) {s : State} (hp : SignPre 64 s)
    (hk : ∃ seed : List Byte, bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed ∧
      bytesAt s.mem (s.gpr .a2) 32 = Spec.Ed25519.publicKey seed) :
    WP isa signExpanded s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ ∀ seed : List Byte, bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed →
        bytesAt t.mem (s.gpr .a0) 64 = Spec.Ed25519.sign seed (msgB s) :=
  WP.mono (signWith_wp C B (D := bytesAt s.mem (s.gpr .a1) 64) hp fun _ h => signCopy_ok hp h) fun _ ⟨g, sp, ra, ho⟩ =>
    ⟨g, sp, ra, fun seed hs => by
      obtain ⟨s₀, h₀, hk₀⟩ := hk
      rw [ho, hs]
      exact signFrom_sha512 _ _ _ (hk₀.trans (Proof.Ed25519.publicKey_of_sha512_eq (h₀.symm.trans hs)))⟩

end VG.Proof.Ed25519.RISCV64.Whole

end

end


/-!
# Ed25519's public key and signing on RISC-V, by register

Each function, with its frame as one more argument, meets a contract of its
facts by register (`pkCE`, `signCE`), from an aligned `scratch` and frame, and
208 bytes of stack below the stack pointer for the callees' frames
(`pkE_ok`, `signE_ok`). Their constant time is `publicKeyExpanded_ct` and
`signExpanded_ct`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (combSym combConsts)

/-- The stack the contract reserves. -/
theorem below_reserved (s : State) : below s.sp 208 ∈ RISCV64.abi.reserved 208 s := by
  show _ ∈ stackBelow s.sp 208
  rw [stackBelow_pos _ (by decide)]; simp

/-- The contract by register: `out` in `a0`, `expanded` (the seed's digest, 64 bytes) in `a1`,
`scratch` in `a2`, the frame in `a3`; without the comb's table. -/
def pkRE : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 32⟩
    let ex : Region := ⟨s.gpr .a1, 64⟩
    let sc : Region := ⟨s.gpr .a2, 8192⟩
    let fr : Region := ⟨s.gpr .a3, 144⟩
    s.rd = [ex] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint ex ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      ex.Disjoint sc ∧ ex.Disjoint fr ∧ sc.Disjoint fr ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a3).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧
      (below s.sp 208).Disjoint out ∧ (below s.sp 208).Disjoint ex ∧ (below s.sp 208).Disjoint sc ∧
      (below s.sp 208).Disjoint fr ∧
      ∃ seed : List Byte, seed.length = 32 ∧ bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed
  post s s' := ∀ seed : List Byte, seed.length = 32 → bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed →
    bytesAt s'.mem (s.gpr .a0) 32 = Spec.Ed25519.publicKey seed
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `pkRE` with the comb's table (`abi.withConsts`): `pkRE` for the state without it, and what the
table adds. -/
def pkCE : Contract isa where
  pre s := pkRE.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 208 s
  post := pkRE.post
  pub s₁ s₂ := pkRE.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem pkE_ok (B : BaseOk) (s : State) (hs : pkCE.pre s) :
    ∃ t s', Exec isa publicKeyExpanded s t s' ∧ abiPreserved s s' ∧ pkCE.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, -⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at *
  obtain ⟨-, tal, tfit, words, twr, tres⟩ := tbl_of_consts hk
  obtain hrd : s.rd = [⟨s.gpr .a1, 64⟩, TBL (s.syms combSym)] := rd_of_consts hk a
  obtain tW : ∀ r ∈ pkW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [pkW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := publicKeyExpanded_wp B
    ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, tal, tfit, words, tW⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, fun seed _ hs => hq seed hs⟩

/-- The contract by register: `out` in `a0`, `expanded` (the seed's digest, 64 bytes) in `a1`,
`pk` in `a2`, the message in `a3` (`len` in `a4`), `scratch` in `a5`, the frame in `a6`; without the
comb's table. -/
def signRE : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 64⟩
    let ex : Region := ⟨s.gpr .a1, 64⟩
    let pk : Region := ⟨s.gpr .a2, 32⟩
    let msg : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let sc : Region := ⟨s.gpr .a5, 8192⟩
    let fr : Region := ⟨s.gpr .a6, 288⟩
    s.rd = [ex, pk, msg] ∧ s.wr = [out, sc, fr] ∧ (s.gpr .a5).toNat % 8 = 0 ∧ (s.gpr .a6).toNat % 8 = 0 ∧
      out.Disjoint ex ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      ex.Disjoint sc ∧ ex.Disjoint fr ∧ pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧
      msg.Disjoint fr ∧ sc.Disjoint fr ∧ s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧
      (below s.sp 208).Disjoint out ∧ (below s.sp 208).Disjoint ex ∧ (below s.sp 208).Disjoint pk ∧
      (below s.sp 208).Disjoint msg ∧ (below s.sp 208).Disjoint sc ∧ (below s.sp 208).Disjoint fr ∧
      ∃ seed : List Byte, seed.length = 32 ∧ bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed ∧
        bytesAt s.mem (s.gpr .a2) 32 = Spec.Ed25519.publicKey seed
  post s s' := ∀ seed : List Byte, seed.length = 32 → bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed →
    bytesAt s'.mem (s.gpr .a0) 64 = Spec.Ed25519.sign seed (bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
    s₁.sp = s₂.sp

/-- `signRE` with the comb's table (`abi.withConsts`). -/
def signCE : Contract isa where
  pre s := signRE.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 208 s
  post := signRE.post
  pub s₁ s₂ := signRE.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem signE_ok (B : BaseOk) (s : State) (hs : signCE.pre s) :
    ∃ t s', Exec isa signExpanded s t s' ∧ abiPreserved s s' ∧ signCE.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, x, y, z, z'⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp, stripConsts_mem] at *
  obtain ⟨-, tal, tfit, words, twr, tres⟩ := tbl_of_consts hk
  obtain hrd : s.rd = [⟨s.gpr .a1, 64⟩, ⟨s.gpr .a2, 32⟩, msgR s, TBL (s.syms combSym)] := rd_of_consts hk a
  obtain tW : ∀ r ∈ signW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [signW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨s₀, -, h₀, hk₀⟩ := z'
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ :=
    signExpanded_wp sha512OK B ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, x, y, z,
      tal, tfit, words, tW⟩ ⟨s₀, h₀, hk₀⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, fun seed _ hs => hq seed hs⟩

end VG.Proof.Ed25519.RISCV64.Whole

end

end


/-!
# `vg_ed25519_public_key_expanded` and `vg_ed25519_sign_expanded` on RISC-V, verified

Each code meets its contract under `abi.withConsts combConsts` (the comb's
table, which `vg_ed25519_scalar_base` reads) with the frame (18 or 36
doublewords, so aligned as the contract's `u64` buffers are) as one more
argument (`Sig.scratchContract`) and 208 bytes of stack for the callees'
frames: the proof against the contract's facts by register (`pkCE`,
`signCE`: `pkRE`, `signRE` without the table, and what the table adds),
which it implies (`consts_implies`), and a state satisfying it, whose memory
holds a seed's digest at `0x2000`, its public key at `0x2100` (`satMemE`)
and the table at `0x100000` (`tblMem`). In its frame on the stack, which it
wipes before returning (`Verified.stackScratchWipedC`), it meets the
contract itself. Their contracts read the memory on return only at `out`
(`pkEPostOut_local`, `signEPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt signExpandedSig)
open VG.Proof.Ed25519 (publicKeyExpandedSig)
open VG.Impl.Ed25519.RISCV64 (combSym combWords combConsts)
open VG.Proof.Ed25519.RISCV64 (combWords_length)
open VG.Proof.Ed25519.WholeLocal (satSeed satKey bytesAt_congr)

/-! ## The contracts' conditions, and their locality -/

section
variable (pb : Nat)

/-- `publicKeyExpandedContract`'s precondition and postcondition. -/
def pkEPre : Curry (publicKeyExpandedSig.words pb) (Mem → Prop) :=
  fun _out expanded _scratch m =>
    ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m expanded 64 = Spec.Sha512.sha512 seed

def pkEPost : publicKeyExpandedSig.Post pb :=
  fun out expanded _scratch m m' _ =>
    ∀ seed : List Byte, seed.length = 32 → bytesAt m expanded 64 = Spec.Sha512.sha512 seed →
      bytesAt m' out 32 = Spec.Ed25519.publicKey seed

theorem pkEPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (publicKeyExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs publicKeyExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (publicKeyExpandedSig.words pb) (pkEPost pb) vs m m₁ r →
    Curry.apply (publicKeyExpandedSig.words pb) (pkEPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [o, ex, sc], _ =>
    simp only [publicKeyExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m ex 64 = Spec.Sha512.sha512 seed →
      bytesAt m₁ o 32 = Spec.Ed25519.publicKey seed at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m ex 64 = Spec.Sha512.sha512 seed →
      bytesAt m₂ o 32 = Spec.Ed25519.publicKey seed
    intro seed hl hs
    rw [bytesAt_congr hb.1]
    exact h seed hl hs

/-- `signExpandedContract`'s precondition and postcondition. -/
def signEPre : Curry (signExpandedSig.words pb) (Mem → Prop) :=
  fun _out expanded pk _message _len _scratch m =>
    ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m expanded 64 = Spec.Sha512.sha512 seed ∧
      bytesAt m pk 32 = Spec.Ed25519.publicKey seed

def signEPost : signExpandedSig.Post pb :=
  fun out expanded _pk message len _scratch m m' _ =>
    ∀ seed : List Byte, seed.length = 32 → bytesAt m expanded 64 = Spec.Sha512.sha512 seed →
      bytesAt m' out 64 = Spec.Ed25519.sign seed (bytesAt m message len.toNat)

theorem signEPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (signExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs signExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (signExpandedSig.words pb) (signEPost pb) vs m m₁ r →
    Curry.apply (signExpandedSig.words pb) (signEPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [o, ex, pk, msg, l, sc], _ =>
    simp only [signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m ex 64 = Spec.Sha512.sha512 seed →
      bytesAt m₁ o 64 = Spec.Ed25519.sign seed (bytesAt m msg (l.setWidth pb).toNat) at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m ex 64 = Spec.Sha512.sha512 seed →
      bytesAt m₂ o 64 = Spec.Ed25519.sign seed (bytesAt m msg (l.setWidth pb).toNat)
    intro seed hl hs
    rw [bytesAt_congr hb.1]
    exact h seed hl hs

end

/-! ## A memory with a seed's digest and its public key -/

def satDigestE : List Byte := Spec.Sha512.sha512 satSeed

theorem satSeed_length : satSeed.length = 32 := by
  simp only [satSeed, bytesAt, List.length_map, List.length_range]

/-- The digest of `satSeed` at `0x2000` and its public key at `0x2100`. -/
def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0
  else if a.toNat < 0x2100 then satDigestE[a.toNat - 0x2000]?.getD 0
  else satKey[a.toNat - 0x2100]?.getD 0

theorem sat_digestE : bytesAt satMemE 0x2000 64 = Spec.Sha512.sha512 satSeed := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_map, List.length_range, Proof.Ed25519.sha512_length]
  · intro i hi hj
    obtain hi' : i < 64 := by simpa only [bytesAt, List.length_map, List.length_range] using hi
    obtain ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega_using [hi']
    simp only [bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega_using [], show 0x2000 + i < 0x2100 from by omega_using [hi'], ite_false, ite_true,
      Nat.add_sub_cancel_left, satDigestE, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_keyE : bytesAt satMemE 0x2100 32 = satKey := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_map, List.length_range, Proof.Ed25519.WholeLocal.satKey_length]
  · intro i hi hj
    obtain hi' : i < 32 := by simpa only [bytesAt, List.length_map, List.length_range] using hi
    obtain ha : ((0x2100 : Addr) + BitVec.ofNat 64 i).toNat = 0x2100 + i := by
      change (0x2100 + i % 2 ^ 64) % 2 ^ 64 = 0x2100 + i
      omega_using [hi']
    simp only [bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2100 + i < 0x2000 from by omega_using [], show ¬ 0x2100 + i < 0x2100 from by omega_using [], ite_false,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

/-- The comb's table at `0x100000`. -/
@[irreducible] def tblMem : Mem := constMem 0x100000 combWords

theorem tblMem_held : ∀ i < combWords.length,
    tblMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  obtain h := constMem_held 0x100000 combWords (by rw [combWords_length]; decide)
  unfold tblMem
  exact h

/-- `satMemE` below `0x100000`, the comb's table above. -/
@[irreducible] def satMemTE : Mem := fun a => if a.toNat < 0x100000 then satMemE a else tblMem a

theorem satMemTE_held : ∀ i < combWords.length,
    satMemTE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  rw [combWords_length] at hi
  rw [← tblMem_held i (by rw [combWords_length]; exact hi)]
  refine Mem.readW_congr fun j hj => ?_
  obtain e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = 0x100000 + 8 * i + j := by
    rw [show (0x100000 : Addr) = BitVec.ofNat 64 0x100000 from rfl]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [hi, hj]
  simp only [satMemTE, e, show ¬ 0x100000 + 8 * i + j < 0x100000 by omega_using [], ↓reduceIte]

theorem satMemTE_bytes {p : Addr} {n : Nat} (h : p.toNat + n ≤ 0x100000) :
    bytesAt satMemTE p n = bytesAt satMemE p n := by
  unfold bytesAt
  refine List.map_congr_left fun i hi => ?_
  obtain hi' := List.mem_range.mp hi
  obtain e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [h, hi']
  simp only [satMemTE, e, show p.toNat + i < 0x100000 by omega_using [h, hi'], ↓reduceIte]

theorem satMemTE_pre : ∃ seed : List Byte, seed.length = 32 ∧
    bytesAt satMemTE 0x2000 64 = Spec.Sha512.sha512 seed ∧ bytesAt satMemTE 0x2100 32 = Spec.Ed25519.publicKey seed :=
  ⟨satSeed, satSeed_length, by rw [satMemTE_bytes (by decide), sat_digestE],
    by rw [satMemTE_bytes (by decide), sat_keyE]; rfl⟩

/-! ## `vg_ed25519_public_key_expanded` -/

/-- A state satisfying the precondition, with memory `m`, without the table. -/
def pkSatE (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | .a3 => 0x8000 | _ => 0
  sp := 0x10000
  mem := m
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩]

theorem pkRE_implies : pkRE.Implies (Sig.scratchContract RISCV64.abi publicKeyExpandedSig "frame" .u64 18
    (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208) :=
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, RISCV64.abi,
          RISCV64.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        obtain ⟨m, hm⟩ : ∃ m : Mem, ∃ seed : List Byte, seed.length = 32 ∧
            bytesAt m 0x2000 64 = Spec.Sha512.sha512 seed :=
          ⟨satMemE, satSeed, satSeed_length, sat_digestE⟩
        refine ⟨pkSatE m, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, RISCV64.abi, RISCV64.argRegs, pkSatE]
        sig_and_intros
        all_goals first
          | exact hm
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- `pkSatE` with the table. -/
def pkSatCE : State :=
  { pkSatE satMemTE with rd := (pkSatE satMemTE).rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem pkCE_sat : (Sig.scratchContract (RISCV64.abi.withConsts combConsts) publicKeyExpandedSig "frame" .u64 18
    (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208).pre pkSatCE := by
  have hl := combWords_length
  have held := satMemTE_held
  obtain ⟨seed, hsl, hm, -⟩ := satMemTE_pre
  change (Sig.scratchContract (RISCV64.abi.withConsts [(combSym, combWords)]) publicKeyExpandedSig "frame"
    .u64 18 (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208).pre pkSatCE
  generalize combWords = W' at hl held ⊢
  generalize e : pkSatCE = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions_cons, Abi.constRegions_nil, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨seed, hsl, hm⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem pkCE_implies : pkCE.Implies (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
    publicKeyExpandedSig "frame" .u64 18 (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208) :=
  consts_implies (kR := pkRE) pkRE_implies (fun _ _ h => h) (fun _ _ h => h) ⟨pkSatCE, pkCE_sat⟩

theorem publicKeyExpanded_verified :
    Verified RISCV64.target publicKeyExpanded (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
      publicKeyExpandedSig "frame" .u64 18 (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208) :=
  Verified.of_correct (pkE_ok base_ok) (publicKeyExpanded_ct fun _ _ _ _ ⟨⟨h0, h1, h2, h3, hsp⟩, hsy⟩ =>
    ⟨hsp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption, hsy⟩) pkCE_implies

/-- A state satisfying `vg_ed25519_public_key_expanded`'s precondition, without the frame. -/
def pkFrameSatE : State := { pkSatCE with wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSatE_pre : ∃ s, (Proof.Ed25519.publicKeyExpandedContract (RISCV64.abi.withConsts combConsts)
    (208 + 144)).pre s := by
  refine ⟨pkFrameSatE, ?_⟩
  have hl := combWords_length
  have held := satMemTE_held
  obtain ⟨seed, hsl, hm, -⟩ := satMemTE_pre
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkFrameSatE = s
  sig_pre [Proof.Ed25519.publicKeyExpandedContract, publicKeyExpandedSig, Spec.Ed25519.scratchWords,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions_cons, Abi.constRegions_nil, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨seed, hsl, hm⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 144 bytes, whose first 136 it zeroes before returning. -/
theorem publicKeyExpanded_framed :
    Verified RISCV64.target publicKeyExpandedCode
      (Proof.Ed25519.publicKeyExpandedContract (RISCV64.abi.withConsts combConsts) (208 + 144)) :=
  Verified.stackScratchWipedC (sig := publicKeyExpandedSig) (nm := "frame") (e := .u64) (n := 18)
    (pre := pkEPre RISCV64.abi.ptrBits) (post := pkEPost RISCV64.abi.ptrBits) (wa := true) (stack := 208)
    (bytes := 144) (words := 17) publicKeyExpanded_verified (by decide) (by decide) (by decide)
    (pkEPostOut_local _) pkFrameSatE_pre

/-! ## `vg_ed25519_sign_expanded` -/

/-- A state satisfying the precondition, with memory `m`, without the table. -/
def signSatE (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x2100 | .a3 => 0x3000 | .a5 => 0x4000 | .a6 => 0x8000 | _ => 0
  sp := 0x10000
  mem := m
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 32⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩]

theorem signRE_implies : signRE.Implies (Sig.scratchContract RISCV64.abi signExpandedSig "frame" .u64 36
    (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208) :=
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          signExpandedSig, Spec.Ed25519.scratchWords, signEPre, signEPost, signRE, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          signExpandedSig, Spec.Ed25519.scratchWords, signEPre, signEPost, signRE, RISCV64.abi,
          RISCV64.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          signExpandedSig, Spec.Ed25519.scratchWords, signEPre, signEPost, signRE, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        refine ⟨signSatE satMemTE, ?_⟩
        have hm := satMemTE_pre
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          signExpandedSig, Spec.Ed25519.scratchWords, signEPre, RISCV64.abi, RISCV64.argRegs, signSatE]
        sig_and_intros
        all_goals first
          | exact hm
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- `signSatE` with the table. -/
def signSatCE : State :=
  { signSatE satMemTE with rd := (signSatE satMemTE).rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem signCE_sat : (Sig.scratchContract (RISCV64.abi.withConsts combConsts) signExpandedSig "frame" .u64 36
    (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208).pre signSatCE := by
  have hl := combWords_length
  have held := satMemTE_held
  have hm := satMemTE_pre
  change (Sig.scratchContract (RISCV64.abi.withConsts [(combSym, combWords)]) signExpandedSig "frame"
    .u64 36 (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208).pre signSatCE
  generalize combWords = W' at hl held ⊢
  generalize e : signSatCE = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    signExpandedSig, Spec.Ed25519.scratchWords, signEPre,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions_cons, Abi.constRegions_nil, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact hm
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem signCE_implies : signCE.Implies (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
    signExpandedSig "frame" .u64 36 (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208) :=
  consts_implies (kR := signRE) signRE_implies (fun _ _ h => h) (fun _ _ h => h) ⟨signSatCE, signCE_sat⟩

theorem signExpanded_verified :
    Verified RISCV64.target signExpanded (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
      signExpandedSig "frame" .u64 36 (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208) :=
  Verified.of_correct (signE_ok base_ok) (signExpanded_ct fun _ _ _ _ ⟨⟨h0, h1, h2, h3, h4, h5, h6, hsp⟩, hsy⟩ =>
    ⟨hsp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption, hsy⟩) signCE_implies

/-- A state satisfying `vg_ed25519_sign_expanded`'s precondition, without the frame. -/
def signFrameSatE : State := { signSatCE with wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩] }

theorem signFrameSatE_pre : ∃ s, (Spec.Ed25519.signExpandedContract (RISCV64.abi.withConsts combConsts)
    (208 + 288)).pre s := by
  refine ⟨signFrameSatE, ?_⟩
  have hl := combWords_length
  have held := satMemTE_held
  have hm := satMemTE_pre
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : signFrameSatE = s
  sig_pre [Spec.Ed25519.signExpandedContract, signExpandedSig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs, Abi.withConsts, Abi.constRegions_cons, Abi.constRegions_nil, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact hm
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 288 bytes, whose first 224 it zeroes before returning. -/
theorem signExpanded_framed :
    Verified RISCV64.target signExpandedCode
      (Spec.Ed25519.signExpandedContract (RISCV64.abi.withConsts combConsts) (208 + 288)) :=
  Verified.stackScratchWipedC (sig := signExpandedSig) (nm := "frame") (e := .u64) (n := 36)
    (pre := signEPre RISCV64.abi.ptrBits) (post := signEPost RISCV64.abi.ptrBits) (wa := true) (stack := 208)
    (bytes := 288) (words := 28) signExpanded_verified (by decide) (by decide) (by decide)
    (signEPostOut_local _) signFrameSatE_pre

end VG.Proof.Ed25519.RISCV64.Whole
