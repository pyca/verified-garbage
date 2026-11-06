module

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Open
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.OpenKey.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.OpenKey.Route
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.SealKey.Main
import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Branch
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Pad
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.OpenPad
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ContractPost
public import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.ContractPost
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Open
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Branch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Lit

/-!
# ChaCha20-Poly1305 on AArch64: `Verified`

Correctness (`Correct.lean`, and `Stitched/` for the eight-block stream's
own code), constant time, and a state satisfying the precondition: of the
code with its working space as its last argument (`sealScratchContract`,
`openZeroScratchContract`), and then of the functions, which allocate it in a
frame of 1280 bytes (`seal`) or 1296 (`open`, which also saves `data` and
`len` after the context) on the stack and wipe its first 768 after the code
(`Verified.stackScratchWiped`). `open`'s code is proven with permission to
write only the data, the context and those 16 bytes, which its working space
covers (`RegionModel.verified_narrowTo`).

The taint analysis runs through the callees' code: it knows `x21`–`x25`
(the context, the data, the additional data and their lengths) for public
after each call because no callee writes them (unlike `x19` and `x20`, which
`vg_chacha20_xor` restores from memory, and which the analysis therefore
treats as secret afterwards). The address of `tag`, which no register can
keep through the eight-block stream's code, is saved in the context, so the
analysis, which knows nothing of memory, checks the code up to the tag
(`sealMainCode`, `openMainCode`) and the rest (`sealTail`, `openTail`)
separately: between them, correctness says that both runs load the same
address, from the same place (`MainS`, `MainO`), and the rest is checked with
it public.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Spec.Poly1305 (bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (macData)

/-! ## Relating two runs -/

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hsp : σ₁.sp = σ₂.sp)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) (hc : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hsp, fun r h => hr r (VG.AArch64.Taint.mem_ofRegs.mp h)⟩) hc

/-! ## Correctness -/

theorem sealCode_eq (c : Impl.ChaCha20.AArch64.XorCallee) (stitched : Bool) :
    sealCode c stitched = .seq (sealMainCode c stitched) sealTail := by
  cases stitched <;> rfl

theorem openCode_eq (c : Impl.ChaCha20.AArch64.XorCallee) (stitched : Bool) :
    openCode c stitched = .seq (.block saveData) (.seq (openMainCode c stitched) openTail) := by
  cases stitched <;> rfl

theorem sealMainCode_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealMainCode v.callee v.stitched) s₀ (MainS s₀) := by
  unfold sealMainCode
  refine WP.seq (WP.mono (Short.check_ok v.callee.sve s₀) fun s₁ ⟨ag, x9⟩ => ?_)
  have hp₁ := Short.APre.agree ag hp
  refine WP.ite (decide (Short.lo v.callee.sve ≤ L s₀ ∧ L s₀ ≤ 511)) (Short.check_eval x9) (fun h => ?_) (fun hn => ?_)
  · have hlo : 1 ≤ L s₁ := by
      have := (of_decide_eq_true h).1
      have : 1 ≤ Short.lo v.callee.sve := by cases v.callee.sve <;> decide
      rw [L, ag.gpr .x5 (by decide) (by decide)]; simp only [L] at *; omega
    have h511 : L s₁ ≤ 511 := by
      have := (of_decide_eq_true h).2
      rw [L, ag.gpr .x5 (by decide) (by decide)]; simp only [L] at *; omega
    exact WP.mono (Pad.sealRoute_ok v hp₁ hlo h511) fun _ h => Short.MainS.agree ag h
  · split
    · refine WP.seq (WP.mono (OpenKey.routeKey_ok v.callee.sve true s₁) fun s₂ ⟨ag₂, x9₂, x10₂⟩ => ?_)
      have hp₂ := Short.APre.agree ag₂ hp₁
      refine WP.ite (decide (Short.inRoute v.callee.sve true (L s₁))) (Short.route_eval x9₂)
        (fun h => ?_) (fun _ => ?_)
      rotate_left
      · have hL₂ : L s₂ = L s₁ := by rw [L, L, ag₂.gpr .x5 (by decide) (by decide)]
        refine WP.iteCold_iff.mpr (WP.ite (decide (keyLo v.callee.sve true ≤ L s₁ ∧ L s₁ ≤ 704))
          (OpenKey.key_eval x10₂) (fun hk => ?_) (fun _ => ?_))
        · have hk' := of_decide_eq_true hk
          have h513 : 513 ≤ keyLo v.callee.sve true := by cases v.callee.sve <;> decide
          exact WP.mono (SealKey.sealMain_ok v hp₂ (by omega) (by omega))
            fun _ h => Short.MainS.agree ag (Short.MainS.agree ag₂ h)
        · exact WP.mono (sealStitchedMain_ok v hp₂) fun _ h => Short.MainS.agree ag (Short.MainS.agree ag₂ h)
      · have hr := of_decide_eq_true h
        have hL : 512 ≤ L s₂ := by
          have hlo : 256 ≤ wideLo v.callee.sve true := by cases v.callee.sve <;> decide
          have hs : Short.lo v.callee.sve ≤ 64 := by cases v.callee.sve <;> decide
          have hn' := of_decide_eq_false hn
          simp only [Short.inRoute] at hr
          have e1 := ag.gpr .x5 (by decide) (by decide)
          have e2 := ag₂.gpr .x5 (by decide) (by decide)
          simp only [L, e1, e2] at hr hn' ⊢
          omega
        exact WP.mono (sealWideMain_ok v hp₂ hL) fun _ h => Short.MainS.agree ag (Short.MainS.agree ag₂ h)
    · exact WP.mono (sealMain_ok v hp₁) fun _ h => Short.MainS.agree ag h

theorem openMainCode_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openMainCode v.callee v.stitched) s₀ (MainO s₀) := by
  unfold openMainCode
  refine WP.seq (WP.mono (Short.check_ok v.callee.sve s₀) fun s₁ ⟨ag, x9⟩ => ?_)
  have hp₁ := Short.APre.agree ag hp
  refine WP.ite (decide (Short.lo v.callee.sve ≤ L s₀ ∧ L s₀ ≤ 511)) (Short.check_eval x9) (fun h => ?_) (fun hn => ?_)
  · have hlo : 1 ≤ L s₁ := by
      have := (of_decide_eq_true h).1
      have : 1 ≤ Short.lo v.callee.sve := by cases v.callee.sve <;> decide
      rw [L, ag.gpr .x5 (by decide) (by decide)]; simp only [L] at *; omega
    have h511 : L s₁ ≤ 511 := by
      have := (of_decide_eq_true h).2
      rw [L, ag.gpr .x5 (by decide) (by decide)]; simp only [L] at *; omega
    exact WP.mono (OpenPad.openRoute_ok v hp₁ hlo h511) fun _ h => Short.MainO.agree ag h
  · split
    · refine WP.seq (WP.mono (OpenKey.routeKey_ok v.callee.sve false s₁) fun s₂ ⟨ag₂, x9₂, x10₂⟩ => ?_)
      have hp₂ := Short.APre.agree ag₂ hp₁
      refine WP.ite (decide (Short.inRoute v.callee.sve false (L s₁))) (Short.route_eval x9₂)
        (fun h => ?_) (fun _ => ?_)
      rotate_left
      · have hL₂ : L s₂ = L s₁ := by rw [L, L, ag₂.gpr .x5 (by decide) (by decide)]
        refine WP.iteCold_iff.mpr (WP.ite (decide (keyLo v.callee.sve false ≤ L s₁ ∧ L s₁ ≤ 704)) (OpenKey.key_eval x10₂)
          (fun hk => ?_) (fun _ => ?_))
        · have hk' := of_decide_eq_true hk
          have h513 : 513 ≤ keyLo v.callee.sve false := by cases v.callee.sve <;> decide
          exact WP.mono (OpenKey.openMain_ok v hp₂ (by omega) (by omega))
            fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)
        · exact WP.mono (openStitchedMain_ok v hp₂) fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)
      · have hr := of_decide_eq_true h
        have hL : 512 ≤ L s₂ := by
          have hlo : 256 ≤ wideLo v.callee.sve false := by cases v.callee.sve <;> decide
          have hs : Short.lo v.callee.sve ≤ 64 := by cases v.callee.sve <;> decide
          have hn' := of_decide_eq_false hn
          simp only [Short.inRoute] at hr
          have e1 := ag.gpr .x5 (by decide) (by decide)
          have e2 := ag₂.gpr .x5 (by decide) (by decide)
          simp only [L, e1, e2] at hr hn' ⊢
          omega
        exact WP.mono (openWideMain_ok v hp₂ hL) fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)
    · exact WP.mono (openMain_ok v hp₁) fun _ h => Short.MainO.agree ag h

theorem seal_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa (sealCode v.callee v.stitched) s t s' ∧
      abiPreserved s s' ∧ sealAArch64.post s s' := by
  rw [sealCode_eq]
  exact WP.seq (WP.mono (sealMainCode_ok v (APre.of s hs)) fun _ h => sealTail_ok (APre.of s hs) h)

/-! ### `open`'s `saveData` -/

/-- `saveData`: `data` and `len` after the context, nothing else written. -/
theorem saveData_ok {σ : State} (hp : APre false σ) :
    WP isa (.block saveData) σ fun s => s.gpr = σ.gpr ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
      Frame [slotR σ] σ.mem s.mem ∧ s.mem.readW (off (cx σ) 1280) 64 = dp σ ∧
      s.mem.readW (off (cx σ) 1288) 64 = σ.gpr .x5 := by
  have hw := (hp.slot rfl).wrap_s
  have hc : ∀ d, 1280 ≤ d → d + 8 ≤ 1296 → (slotR σ).Contains (off (cx σ) d) 8 := fun d h1 h2 =>
    Offset.contains (cx σ) h1 (by omega) (by decide)
  have hin : slotR σ ∈ σ.wr := by rw [hp.wr]; simp
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_str (a := off (cx σ) 1280) (by decide) rfl
    ⟨_, hin, hc 1280 (Nat.le_refl _) (by decide)⟩ fun s₁ m₁ =>
    VG.Proof.ChaCha20.AArch64.Xor.wp_str (a := off (cx σ) 1288) (by decide) (by rw [m₁.gpr])
    ⟨_, by rw [m₁.wr]; exact hin, hc 1288 (by decide) (by decide)⟩ fun s₂ m₂ => WP.block_nil
    ⟨by rw [m₂.gpr, m₁.gpr], by rw [m₂.rd, m₁.rd], by rw [m₂.wr, m₁.wr], ?_, ?_, ?_⟩
  · rw [m₂.mem, m₁.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 1280 (Nat.le_refl _) (by decide))).writeW
      (List.mem_singleton_self _) _ (hc 1288 (by decide) (by decide))
  · rw [m₂.mem, m₁.mem, Mem.readW_writeW_sep (Offset.sep (cx σ) (.inl (by decide)) (by omega) (by omega))
      (by decide), Mem.readW_writeW_self64]
  · rw [m₂.mem, m₁.gpr, Mem.readW_writeW_self64]

/-- The precondition, of a state whose registers and permissions are `σ`'s. -/
theorem APre.of_gpr {e : Bool} {σ s : State} (h : APre e σ) (hg : s.gpr = σ.gpr) (hrd : s.rd = σ.rd)
    (hwr : s.wr = σ.wr) : APre e s := by
  have g : ∀ r, s.gpr r = σ.gpr r := fun r => by rw [hg]
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun he => ?_⟩
  rotate_right
  · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := p18 he
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [slotR, sub, off, kR, nR, aR, dR, tR, kp, np, ad, AL, dp, L, tp, cx, g] <;>
      with_reducible assumption
  all_goals
    simp only [kR, nR, aR, dR, tR, ctxR, slotR, sub, off, kp, np, ad, AL, dp, L, tp, cx, hrd, hwr, g]
    with_reducible assumption

/-- `saveData`'s stores are outside the arguments `open` reads. -/
theorem slot_bytes {σ : State} (hp : APre false σ) {m : Mem} (hf : Frame [slotR σ] σ.mem m) :
    bytesAt m (kp σ) 32 = K σ ∧ bytesAt m (np σ) 12 = N σ ∧ bytesAt m (ad σ) (AL σ) = A σ ∧
      bytesAt m (dp σ) (L σ) = D σ ∧ bytesAt m (tp σ) 16 = T0 σ := by
  have hs := hp.slot rfl
  have one : ∀ {r : Region}, (slotR σ).Disjoint r → ∀ q ∈ [slotR σ], r.Disjoint q := fun h q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact h.symm
  exact ⟨bytesAt_frame hf (one hs.s_k) (by decide), bytesAt_frame hf (one hs.s_n) (by decide),
    bytesAt_frame hf (one hs.s_a) (Nat.le_of_lt (σ.gpr .x3).isLt),
    bytesAt_frame hf (one hs.s_d) (Nat.le_of_lt (σ.gpr .x5).isLt), bytesAt_frame hf (one hs.s_t) (by decide)⟩

theorem post_of_save {σ s₁ s' : State} (hp : APre false σ) (hg : s₁.gpr = σ.gpr)
    (hf : Frame [slotR σ] σ.mem s₁.mem) (h : openAArch64.post s₁ s') : openAArch64.post σ s' := by
  obtain ⟨bk, bn, ba, bd, bt⟩ := slot_bytes hp hf
  rw [openAArch64, Contract.post_mk] at h ⊢
  rw [hg] at h
  rw [show bytesAt s₁.mem (σ.gpr .x0) 32 = _ from bk, show bytesAt s₁.mem (σ.gpr .x1) 12 = _ from bn,
    show bytesAt s₁.mem (σ.gpr .x2) (σ.gpr .x3).toNat = _ from ba,
    show bytesAt s₁.mem (σ.gpr .x4) (σ.gpr .x5).toNat = _ from bd,
    show bytesAt s₁.mem (σ.gpr .x6) 16 = _ from bt] at h
  exact h

theorem ok_of_save {σ s₁ : State} (hp : APre false σ) (hg : s₁.gpr = σ.gpr)
    (hf : Frame [slotR σ] σ.mem s₁.mem) : okAArch64 s₁ = okAArch64 σ := by
  obtain ⟨bk, bn, ba, bd, bt⟩ := slot_bytes hp hf
  unfold okAArch64
  rw [hg, show bytesAt s₁.mem (σ.gpr .x0) 32 = _ from bk, show bytesAt s₁.mem (σ.gpr .x1) 12 = _ from bn,
    show bytesAt s₁.mem (σ.gpr .x2) (σ.gpr .x3).toNat = _ from ba,
    show bytesAt s₁.mem (σ.gpr .x4) (σ.gpr .x5).toNat = _ from bd,
    show bytesAt s₁.mem (σ.gpr .x6) 16 = _ from bt]

theorem abi_of_save {σ s₁ s' : State} (hg : s₁.gpr = σ.gpr) (hsp : s₁.sp = σ.sp)
    (hv : ∀ r ∈ preservedV, (s₁.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64)
    (h : abiPreserved s₁ s') : abiPreserved σ s' :=
  ⟨fun r hr => by rw [h.1 r hr, hg], by rw [h.2.1, hsp], fun r hr => (h.2.2 r hr).trans (hv r hr)⟩

theorem open_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa (openCode v.callee v.stitched) s t s' ∧
      abiPreserved s s' ∧ openAArch64.post s s' := by
  have hp := APre.of s hs
  rw [openCode_eq]
  refine WP.seq (WP.mono (WP.withSp (WP.preservedV (saveData_ok hp) (by lit_decide)))
    fun s₁ ⟨⟨⟨g₁, rd₁, wr₁, f₁, d₁, l₁⟩, v₁⟩, sp₁⟩ => ?_)
  have hp₁ : APre false s₁ := hp.of_gpr g₁ rd₁ wr₁
  refine WP.seq (WP.mono (openMainCode_ok v hp₁) fun s₂ h₂ => ?_)
  have ge : ∀ r, s₁.gpr r = s.gpr r := fun r => by rw [g₁]
  refine WP.mono (openTail_ok hp₁ h₂ (by show _ = s₁.gpr .x4; rw [show cx s₁ = cx s from ge .x7, ge .x4]; exact d₁)
    (by rw [show cx s₁ = cx s from ge .x7, ge .x5]; exact l₁))
    fun s₃ ⟨ha, hq⟩ => ⟨abi_of_save g₁ sp₁ v₁ ha, post_of_save hp g₁ f₁ hq⟩

/-! ## Constant time -/

theorem sealLoad_taint : ∃ h, (taint.check (Taint.ofRegs [.x21])
    (.block [.ldr .x .x2 .x21 624]) h).isSome = true := ⟨_, by taint_decide⟩

theorem sealRest_taint : ∃ h, (taint.check (Taint.ofRegs [.x2, .x21])
    (.seq finalizeTag (.block restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem openLoad_taint : ∃ h, (taint.check (Taint.ofRegs [.x21])
    (.block [.ldr .x .x12 .x21 624]) h).isSome = true := ⟨_, by taint_decide⟩

theorem saveData_taint : ∃ h, (taint.check (Taint.ofRegs [.x7]) (.block saveData) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem compare_taint : ∃ h, (taint.check (Taint.ofRegs [.x12, .x21]) (.block compare) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem zeroLoad_taint : ∃ h, (taint.check (Taint.ofRegs [.x21]) (.block zeroLoad) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem zeroLoop_taint : ∃ h, (taint.check (Taint.ofRegs [.x9, .x10]) zeroLoop h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.x21]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem skip_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem pub_regs {s₁ s₂ : State} (hq : pubAArch64 s₁ s₂) :
    ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], s₁.gpr r = s₂.gpr r := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_ct (v : Proof.ChaCha20.AArch64.XorImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub
    (sealCode v.callee v.stitched) := by
  rw [sealCode_eq]
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  have hp₁ := APre.of _ h₁
  have hp₂ := APre.of _ h₂
  obtain ⟨-, -, -, -, -, -, p6, p7, psp⟩ := id hq
  refine (rel_seq (rel_taint _ psp (pub_regs hq) v.sealTaint) (sealMainCode_ok v hp₁)
    (sealMainCode_ok v hp₂) (fun τ₁ τ₂ m₁ m₂ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  have sp : τ₁.sp = τ₂.sp := by rw [m₁.inv.sp, m₂.inv.sp, psp]
  refine rel_seq (rel_taint [.x21] sp (by
      simp only [List.mem_singleton, forall_eq, m₁.inv.x21, m₂.inv.x21, cx, p7]) sealLoad_taint)
    (tagPtr_ok hp₁ m₁.inv.x21 m₁.inv.saved m₁.inv.rd m₁.inv.wr (by decide))
    (tagPtr_ok hp₂ m₂.inv.x21 m₂.inv.saved m₂.inv.rd m₂.inv.wr (by decide))
    fun u₁ u₂ ⟨x2₁, k₁⟩ ⟨x2₂, k₂⟩ => rel_taint [.x2, .x21] (by rw [k₁.sp, k₂.sp, sp]) ?_ sealRest_taint
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x2₁, x2₂, tp, tp, p6]
  · rw [k₁.cs _ (pres .x21) (pres30 .x21), k₂.cs _ (pres .x21) (pres30 .x21), m₁.inv.x21, m₂.inv.x21, cx,
      cx, p7]

theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- `openTail`, in two runs from the states `openMainCode_ok` describes:
the branch to `zeroData` is on the result, which the two runs' leaks say
agree (`hok`), and `zeroData`'s loop on `len`, which correctness says it
loads from where `saveData` saved it. -/
theorem tail_rel {τ₁ τ₂ ρ₁ ρ₂ : State} (hp₁ : APre false τ₁) (hp₂ : APre false τ₂)
    (m₁ : MainO τ₁ ρ₁) (m₂ : MainO τ₂ ρ₂)
    (d₁ : τ₁.mem.readW (off (cx τ₁) 1280) 64 = dp τ₁) (l₁ : τ₁.mem.readW (off (cx τ₁) 1288) 64 = τ₁.gpr .x5)
    (d₂ : τ₂.mem.readW (off (cx τ₂) 1280) 64 = dp τ₂) (l₂ : τ₂.mem.readW (off (cx τ₂) 1288) 64 = τ₂.gpr .x5)
    (ecx : cx τ₁ = cx τ₂) (edp : dp τ₁ = dp τ₂) (el : τ₁.gpr .x5 = τ₂.gpr .x5) (etp : tp τ₁ = tp τ₂)
    (hok : okAArch64 τ₁ = okAArch64 τ₂) (sp : ρ₁.sp = ρ₂.sp) :
    RelCT isa (Eq2 ρ₁ ρ₂) openTail TT := by
  unfold openTail
  refine rel_seq (rel_taint [.x21] sp (by simp only [List.mem_singleton, forall_eq, m₁.inv.x21, m₂.inv.x21, ecx])
      openLoad_taint)
    (tagPtr_ok hp₁ m₁.inv.x21 m₁.inv.saved m₁.inv.rd m₁.inv.wr (by decide))
    (tagPtr_ok hp₂ m₂.inv.x21 m₂.inv.saved m₂.inv.rd m₂.inv.wr (by decide))
    fun u₁ u₂ ⟨x12₁, k₁⟩ ⟨x12₂, k₂⟩ => ?_
  have x21₁ : u₁.gpr .x21 = cx τ₁ := by rw [k₁.cs _ (pres .x21) (pres30 .x21), m₁.inv.x21]
  have x21₂ : u₂.gpr .x21 = cx τ₂ := by rw [k₂.cs _ (pres .x21) (pres30 .x21), m₂.inv.x21]
  have spu : u₁.sp = u₂.sp := by rw [k₁.sp, k₂.sp, sp]
  refine rel_seq (rel_taint [.x12, .x21] spu (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [x12₁, x12₂, etp]
      · rw [x21₁, x21₂, ecx]) compare_taint)
    (WP.withSp (compare_ok hp₁ x21₁ x12₁ (by rw [k₁.rd, m₁.inv.rd]) (by rw [k₁.wr, m₁.inv.wr])))
    (WP.withSp (compare_ok hp₂ x21₂ x12₂ (by rw [k₂.rd, m₂.inv.rd]) (by rw [k₂.wr, m₂.inv.wr])))
    fun w₁ w₂ ⟨⟨rax₁, g₁, _, mm₁, rd₁, wr₁⟩, sp₁⟩ ⟨⟨rax₂, g₂, _, mm₂, rd₂, wr₂⟩, sp₂⟩ => ?_
  obtain ⟨c₁, t₁⟩ := m₁.tags hp₁ k₁.mem_eq
  obtain ⟨c₂, t₂⟩ := m₂.tags hp₂ k₂.mem_eq
  rw [c₁, t₁] at rax₁
  rw [c₂, t₂] at rax₂
  have hb : (w₁.gpr .x0).setWidth 32 = (w₂.gpr .x0).setWidth 32 := by
    rw [rax₁, rax₂]
    by_cases h₁ : okAArch64 τ₁ = true
    · have h₂ : okAArch64 τ₂ = true := hok ▸ h₁
      simp only [(ok_iff τ₁).mp h₁, (ok_iff τ₂).mp h₂, ↓reduceIte]
    · have h₂ : ¬okAArch64 τ₂ = true := hok ▸ h₁
      simp only [show ¬mac (otk τ₁) (macData (A τ₁) (D τ₁)) = T0 τ₁ from fun h' => h₁ ((ok_iff τ₁).mpr h'),
        show ¬mac (otk τ₂) (macData (A τ₂) (D τ₂)) = T0 τ₂ from fun h' => h₂ ((ok_iff τ₂).mpr h'),
        ↓reduceIte]
  have x21w₁ : w₁.gpr .x21 = cx τ₁ := by rw [g₁ _ (pres .x21), x21₁]
  have x21w₂ : w₂.gpr .x21 = cx τ₂ := by rw [g₂ _ (pres .x21), x21₂]
  have rdw₁ : w₁.rd = τ₁.rd := by rw [rd₁, k₁.rd, m₁.inv.rd]
  have rdw₂ : w₂.rd = τ₂.rd := by rw [rd₂, k₂.rd, m₂.inv.rd]
  have wrw₁ : w₁.wr = τ₁.wr := by rw [wr₁, k₁.wr, m₁.inv.wr]
  have wrw₂ : w₂.wr = τ₂.wr := by rw [wr₂, k₂.wr, m₂.inv.wr]
  have mw₁ : w₁.mem = ρ₁.mem := by rw [mm₁, k₁.mem_eq]
  have mw₂ : w₂.mem = ρ₂.mem := by rw [mm₂, k₂.mem_eq]
  have dw₁ : w₁.mem.readW (off (cx τ₁) 1280) 64 = dp τ₁ := by
    rw [mw₁, m₁.slot hp₁ (Nat.le_refl _) (by decide), d₁]
  have dw₂ : w₂.mem.readW (off (cx τ₂) 1280) 64 = dp τ₂ := by
    rw [mw₂, m₂.slot hp₂ (Nat.le_refl _) (by decide), d₂]
  have lw₁ : w₁.mem.readW (off (cx τ₁) 1288) 64 = τ₁.gpr .x5 := by
    rw [mw₁, m₁.slot hp₁ (by decide) (by decide), l₁]
  have lw₂ : w₂.mem.readW (off (cx τ₂) 1288) 64 = τ₂.gpr .x5 := by
    rw [mw₂, m₂.slot hp₂ (by decide) (by decide), l₂]
  have spw : w₁.sp = w₂.sp := by rw [sp₁, sp₂, spu]
  refine rel_seq ?_ (zeroIte_ok hp₁ x21w₁ rdw₁ wrw₁ dw₁ lw₁) (zeroIte_ok hp₂ x21w₂ rdw₂ wrw₂ dw₂ lw₂)
    fun z₁ z₂ ⟨x21z₁, spz₁⟩ ⟨x21z₂, spz₂⟩ => rel_taint [.x21] (by rw [spz₁, spz₂, spw])
      (by simp only [List.mem_singleton, forall_eq, x21z₁, x21z₂, x21w₁, x21w₂, ecx]) restore_taint
  refine RelCT.ite (fun a b ⟨ea, eb⟩ => by rw [ea, eb, eval_zero_w, eval_zero_w, hb]) ?_ ?_
  · refine (?_ : RelCT isa (Eq2 w₁ w₂) zeroData TT).mono (fun _ _ h => h.1) fun _ _ h => h
    unfold zeroData
    exact rel_seq (rel_taint [.x21] spw (by simp only [List.mem_singleton, forall_eq, x21w₁, x21w₂, ecx])
        zeroLoad_taint)
      (WP.withSp (zeroLoad_ok hp₁ x21w₁ rdw₁ wrw₁ dw₁ lw₁)) (WP.withSp (zeroLoad_ok hp₂ x21w₂ rdw₂ wrw₂ dw₂ lw₂))
      fun y₁ y₂ ⟨⟨x9₁, x10₁, _⟩, spy₁⟩ ⟨⟨x9₂, x10₂, _⟩, spy₂⟩ =>
        rel_taint [.x9, .x10] (by rw [spy₁, spy₂, spw]) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [x9₁, x9₂, edp]
          · rw [x10₁, x10₂, el]) zeroLoop_taint
  · exact (rel_taint [] spw (by simp) skip_taint).mono (fun _ _ h => h.1) fun _ _ h => h

theorem open_ct (v : Proof.ChaCha20.AArch64.XorImpl) : ConstantTime isa openAArch64.pre openAArch64.pub
    (openCode v.callee v.stitched) := by
  rw [openCode_eq]
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  have hp₁ := APre.of _ h₁
  have hp₂ := APre.of _ h₂
  obtain ⟨hq, hl⟩ := hq
  obtain ⟨-, -, -, -, p4, p5, p6, p7, psp⟩ := id hq
  have hok : okAArch64 σ₁ = okAArch64 σ₂ := leak_bool hl
  refine (rel_seq (rel_taint [.x7] psp (by simp only [List.mem_singleton, forall_eq, p7]) saveData_taint)
    (WP.withSp (saveData_ok hp₁)) (WP.withSp (saveData_ok hp₂))
    (fun τ₁ τ₂ ⟨⟨g₁, rd₁, wr₁, f₁, d₁, l₁⟩, sp₁⟩ ⟨⟨g₂, rd₂, wr₂, f₂, d₂, l₂⟩, sp₂⟩ => ?_)
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  have hpτ₁ := hp₁.of_gpr g₁ rd₁ wr₁
  have hpτ₂ := hp₂.of_gpr g₂ rd₂ wr₂
  have ge₁ : ∀ r, τ₁.gpr r = σ₁.gpr r := fun r => by rw [g₁]
  have ge₂ : ∀ r, τ₂.gpr r = σ₂.gpr r := fun r => by rw [g₂]
  have spτ : τ₁.sp = τ₂.sp := by rw [sp₁, sp₂, psp]
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] spτ
      (fun r hr => by rw [ge₁, ge₂]; exact pub_regs hq r hr) v.openTaint)
    (openMainCode_ok v hpτ₁) (openMainCode_ok v hpτ₂) fun ρ₁ ρ₂ mo₁ mo₂ => ?_
  exact tail_rel hpτ₁ hpτ₂ mo₁ mo₂
    (by show _ = τ₁.gpr .x4; rw [show cx τ₁ = cx σ₁ from ge₁ .x7, ge₁ .x4]; exact d₁)
    (by rw [show cx τ₁ = cx σ₁ from ge₁ .x7, ge₁ .x5]; exact l₁)
    (by show _ = τ₂.gpr .x4; rw [show cx τ₂ = cx σ₂ from ge₂ .x7, ge₂ .x4]; exact d₂)
    (by rw [show cx τ₂ = cx σ₂ from ge₂ .x7, ge₂ .x5]; exact l₂)
    (by simp only [cx, ge₁, ge₂, p7]) (by simp only [dp, ge₁, ge₂, p4]) (by rw [ge₁, ge₂, p5])
    (by simp only [tp, ge₁, ge₂, p6]) (by rw [ok_of_save hp₁ g₁ f₁, ok_of_save hp₂ g₂ f₂, hok])
    (by rw [mo₁.inv.sp, mo₂.inv.sp, spτ])

/-! ## `Verified` -/

/-- A state satisfying `seal`'s precondition (with no additional data and no
data). -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x1100 | .x2 => 0x2000 | .x4 => 0x2100 | .x6 => 0x3000 | .x7 => 0x4000
    | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x4000, 1280⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read,
and its whole working space of 1296 bytes writable). -/
def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x1100 | .x2 => 0x2000 | .x4 => 0x2100 | .x6 => 0x3000 | .x7 => 0x4000
    | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x2100, 0⟩, ⟨0x4000, 1296⟩]

theorem seal_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (sealCode v.callee v.stitched) (sealScratchContract AArch64.abi 160) :=
  Verified.of_correct (seal_ok v) (seal_ct v) (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealAArch64,
      Proof.ChaCha20Poly1305.preAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      [sealSat] using sealSat)

open VG.AArch64 in
/-- `open`'s precondition with its whole working space, `work` (1296 bytes),
writable: what its contract gives, whose regions cover `preAArch64 false`'s,
the context and `slotR` (`preOpenW_narrow`). -/
def preOpenW (s : AArch64.State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let data : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let tag : Region := ⟨s.gpr .x6, 16⟩
  let work : Region := ⟨s.gpr .x7, 1296⟩
  s.rd = [key, nonce, aad, tag] ∧ s.wr = [data, work] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint data ∧
  work.Disjoint tag ∧
  data.Disjoint key ∧ data.Disjoint nonce ∧ data.Disjoint aad ∧ data.Disjoint tag ∧
  (s.gpr .x7).toNat + 1296 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64

/-- `openAArch64`, with `preOpenW`. -/
def openW : Contract AArch64.isa where
  pre := preOpenW
  post := openAArch64.post
  pub := openAArch64.pub

/-- The regions `preAArch64 false` permits writing: the data, the context and
`slotR`. -/
def openWr (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 1280⟩, ⟨s.gpr .x7 + BitVec.ofNat 64 1280, 16⟩]

theorem preOpenW_narrow {s : State} (h : preOpenW s) : preAArch64 false (s.withRegions s.rd (openWr s)) := by
  obtain ⟨hrd, -, c_k, c_n, c_a, c_d, c_t, d_k, d_n, d_a, d_t, wc, wa, wd, wt, wk, wn⟩ := h
  have sc : Region.Sub ⟨s.gpr .x7, 1280⟩ ⟨s.gpr .x7, 1296⟩ := Region.sub_prefix (by decide)
  have ss : Region.Sub ⟨s.gpr .x7 + BitVec.ofNat 64 1280, 16⟩ ⟨s.gpr .x7, 1296⟩ := sub_off _ (by decide)
  exact ⟨hrd, rfl, c_k.sub_left sc, c_n.sub_left sc, c_a.sub_left sc, c_d.sub_left sc, c_t.sub_left sc,
    d_k, d_n, d_a, d_t, show (s.gpr .x7).toNat + 1280 ≤ 2 ^ 64 by omega, wa, wd, wt, wk, wn,
    c_k.sub_left ss, c_n.sub_left ss, c_a.sub_left ss, c_d.sub_left ss, c_t.sub_left ss, wc⟩

theorem openWr_covers {s : State} (h : preOpenW s) : Covers (openWr s) s.wr := by
  rw [h.2.1]
  refine Covers.of_sub fun r hr => ?_
  simp only [openWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 0, (BitVec.add_zero _).symm,
      show 0 + 1280 ≤ 1296 by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 1280, rfl, show 1280 + 16 ≤ 1296 by decide⟩

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem openW_implies : openW.Implies (openZeroScratchContract AArch64.abi 162) :=
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakAArch64, openW, preOpenW,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi,
          AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, AArch64.abi, AArch64.argRegs]
        simp only [openW, Proof.ChaCha20Poly1305.openAArch64] at h
        -- The two `decrypt` terms are equal only up to unfolding numerals.
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakAArch64, openW, preOpenW,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi,
          AArch64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakAArch64, openW, preOpenW,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi,
          AArch64.argRegs]
          [openSat] using openSat }

/-- `open` against `openAArch64`, whose precondition permits writing only the
context and `slotR` of the working space. -/
theorem open_verifiedN (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openCode v.callee v.stitched) openAArch64 :=
  ⟨open_ok v, open_ct v, openW_implies.sat_left.elim fun _ hs => ⟨_, preOpenW_narrow hs⟩⟩

/-- Then against `openW`, which permits writing all of it: the code runs as it
does with fewer permissions (`RegionModel.verified_narrowTo`). -/
theorem open_verifiedW (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openCode v.callee v.stitched) openW :=
  regionModel.verified_narrowTo (T := AArch64.target) (fun _ _ _ _ h => h) (open_verifiedN v)
    (fun s => s.rd) openWr (fun _ hs => preOpenW_narrow hs)
    (fun _ hs => (Covers.refl _).append (openWr_covers hs)) (fun _ hs => openWr_covers hs)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) openW_implies.sat_left

theorem open_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openCode v.callee v.stitched) (openZeroScratchContract AArch64.abi 162) :=
  Verified.of_implies (open_verifiedW v) openW_implies

/-! ## The frame -/

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State := { sealSat with wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract AArch64.abi 1280).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, AArch64.abi, AArch64.argRegs] [sealFrameSat, sealSat]
    using sealFrameSat

theorem seal_framed (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 1280 .x7 96 (sealCode v.callee v.stitched))
      (Spec.ChaCha20Poly1305.sealContract AArch64.abi 1280) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 160) (post := Spec.ChaCha20Poly1305.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1280) (words := 96) (seal_verified v) (by decide) (by decide) (by decide)
    (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State := { openSat with wr := [⟨0x2100, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openZeroContract AArch64.abi 1296).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, AArch64.abi, AArch64.argRegs]
    [openFrameSat, openSat] using openFrameSat

theorem open_framed (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 1296 .x7 96 (openCode v.callee v.stitched))
      (Spec.ChaCha20Poly1305.openZeroContract AArch64.abi 1296) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 162) (post := Spec.ChaCha20Poly1305.openZeroPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (leak := some (Spec.ChaCha20Poly1305.openLeak AArch64.abi.ptrBits))
    (bytes := 1296) (words := 96) (open_verified v) (by decide) (by decide) (by decide)
    (openZeroPost_out _) openFrameSat_pre

end VG.Proof.ChaCha20Poly1305.AArch64
