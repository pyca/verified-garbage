module

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Open
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.OpenKey.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.OpenKey.Route
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.SealKey.Main
import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
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
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
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
own code), constant time, and a state satisfying the precondition: of `seal`
and of `open`'s body (`openCode`), which decrypts from the source (`x4`) to
the destination (`x8`), and of the functions: `open` (`openInPlace`, the
destination the data) and `open_to` (`openTo`, the destination from `x6` and
`tag` and `work` from the stack). Each is proven with its working space as its
last argument (`sealScratchContract`, `openZeroScratchContract`,
`openToScratchContract`), and then of the functions, which allocate it in a
frame of 1280 bytes (`seal`) or 1312 (`open` and `open_to`, which also save
the destination, `len` and our caller's `x28` after the context) on the stack
and wipe its first 768 after the code (`Verified.stackScratchWiped`,
`Verified.stackArgScratchWipedPre`). `open`'s and `open_to`'s code is proven
with permission to write only the destination, the context and those 32
bytes, which their working space covers (`RegionModel.verified_narrowTo`).

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
open VG.Spec.ChaCha20Poly1305 (macData decrypt)
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd)

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

/-! ### `open`'s body -/

/-- The 32 bytes after `open`'s context. -/
abbrev slotOf (σ : State) : Region := ⟨off (σ.gpr .x7) 1280, 32⟩

/-- `saveData`: the destination, `len` and our caller's `x28` after the
context, and `x28` set to the destination's distance from the data. -/
theorem saveData_ok {σ : State} (hp : preOpenAArch64 σ) :
    WP isa (.block saveData) σ fun s => (∀ r, r ≠ .x28 → s.gpr r = σ.gpr r) ∧
      s.gpr .x28 = σ.gpr .x8 - σ.gpr .x4 ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
      Frame [slotOf σ] σ.mem s.mem ∧
      s.mem.readW (off (σ.gpr .x7) 1280) 64 = σ.gpr .x8 ∧
      s.mem.readW (off (σ.gpr .x7) 1288) 64 = σ.gpr .x5 ∧
      s.mem.readW (off (σ.gpr .x7) 1296) 64 = σ.gpr .x28 := by
  obtain ⟨-, -, -, -, -, hw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, wc, -⟩ := hp
  have hc : ∀ d, 1280 ≤ d → d + 8 ≤ 1312 → (slotOf σ).Contains (off (σ.gpr .x7) d) 8 := fun d h1 h2 =>
    Offset.contains (σ.gpr .x7) h1 (by omega) (by omega)
  have hin : slotOf σ ∈ σ.wr := by rw [hw]; simp
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_str (a := off (σ.gpr .x7) 1280) (by decide) rfl
    ⟨_, hin, hc 1280 (Nat.le_refl _) (by decide)⟩ fun s₁ m₁ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_str (a := off (σ.gpr .x7) 1288) (by decide) (by rw [m₁.gpr])
    ⟨_, by rw [m₁.wr]; exact hin, hc 1288 (by decide) (by decide)⟩ fun s₂ m₂ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_str (a := off (σ.gpr .x7) 1296) (by decide)
    (by rw [m₂.gpr, m₁.gpr]) ⟨_, by rw [m₂.wr, m₁.wr]; exact hin, hc 1296 (by decide) (by decide)⟩
    fun s₃ m₃ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_sub fun s₄ u₄ => WP.block_nil ⟨fun r hr => ?_, ?_,
    by rw [u₄.rd, m₃.rd, m₂.rd, m₁.rd], by rw [u₄.wr, m₃.wr, m₂.wr, m₁.wr], ?_, ?_, ?_, ?_⟩
  · rw [u₄.other r hr, m₃.gpr, m₂.gpr, m₁.gpr]
  · rw [u₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr]
  · rw [u₄.mem, m₃.mem, m₂.mem, m₁.mem, m₂.gpr, m₁.gpr]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 1280 (Nat.le_refl _) (by decide))).writeW
      (List.mem_singleton_self _) _ (hc 1288 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hc 1296 (by decide) (by decide))
  · rw [u₄.mem, m₃.mem, m₂.mem, m₁.mem, readW64_off _ _ _ (by decide) (by decide) (by decide),
      readW64_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [u₄.mem, m₃.mem, m₂.mem, readW64_off _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64, m₁.gpr]
  · rw [u₄.mem, m₃.mem, Mem.readW_writeW_self64, m₂.gpr, m₁.gpr]

/-- `op false s`, after `saveData`: the destination. -/
theorem op_ofOpen {σ s : State} (hg : ∀ r, r ≠ .x28 → s.gpr r = σ.gpr r)
    (h28 : s.gpr .x28 = σ.gpr .x8 - σ.gpr .x4) : op false s = σ.gpr .x8 := by
  rw [op_false]
  show s.gpr .x4 + s.gpr .x28 = _
  rw [hg .x4 (by decide), h28, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The main code's precondition, after `saveData`. -/
theorem APre.ofOpen {σ s : State} (h : preOpenAArch64 σ) (hg : ∀ r, r ≠ .x28 → s.gpr r = σ.gpr r)
    (h28 : s.gpr .x28 = σ.gpr .x8 - σ.gpr .x4) (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) :
    APre false s := by
  obtain ⟨hk, hn, ha, ht, hd, hw, ck, cn, ca, cd, ct, cq, qk, qn, qa, qt, qd, sk, sn, sa, sd, st, sq,
    wc, wa, wd, wq, wt, wk, wn⟩ := h
  have g0 := hg .x0 (by decide); have g1 := hg .x1 (by decide); have g2 := hg .x2 (by decide)
  have g3 := hg .x3 (by decide); have g4 := hg .x4 (by decide); have g5 := hg .x5 (by decide)
  have g6 := hg .x6 (by decide); have g7 := hg .x7 (by decide)
  have eL : L s = (σ.gpr .x5).toNat := by simp only [L, g5]
  have ekR : kR s = ⟨σ.gpr .x0, 32⟩ := by simp only [kR, kp, g0]
  have enR : nR s = ⟨σ.gpr .x1, 12⟩ := by simp only [nR, np, g1]
  have eaR : aR s = ⟨σ.gpr .x2, (σ.gpr .x3).toNat⟩ := by simp only [aR, ad, AL, g2, g3]
  have edR : dR s = ⟨σ.gpr .x4, (σ.gpr .x5).toNat⟩ := by simp only [dR, dp, L, g4, g5]
  have etR : tR s = ⟨σ.gpr .x6, 16⟩ := by simp only [tR, tp, g6]
  have ecR : ctxR s = ⟨σ.gpr .x7, 1280⟩ := by simp only [ctxR, cx, g7]
  have esR : slotR s = ⟨σ.gpr .x7 + BitVec.ofNat 64 1280, 32⟩ := by simp only [slotR, sub, off, cx, g7]
  have eop := op_ofOpen hg h28
  have eqR : qR s = ⟨σ.gpr .x8, (σ.gpr .x5).toNat⟩ := by
    rw [← eL, ← eop, op_false]
  have eo : (⟨op false s, L s⟩ : Region) = ⟨σ.gpr .x8, (σ.gpr .x5).toNat⟩ := by rw [eop, eL]
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hrd]
    simp only [rdR, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [ekR]; exact hk
    · rw [enR]; exact hn
    · rw [eaR]; exact ha
    · rw [etR]; exact ht
  · rw [hwr, hw, eqR, ecR, esR]; rfl
  · rw [edR, hrd, hwr]; exact hd
  · rw [ecR, ekR]; exact ck
  · rw [ecR, enR]; exact cn
  · rw [ecR, eaR]; exact ca
  · rw [ecR, edR]; exact cd
  · rw [ecR, etR]; exact ct
  · rw [eo, hwr, hw]; simp
  · rw [eop, eL]; exact wq
  · rw [eo, ecR]; exact cq
  · rw [eo, ekR]; exact qk.symm
  · rw [eo, enR]; exact qn.symm
  · rw [eo, eaR]; exact qa.symm
  · rw [eo, etR]; exact qt.symm
  · rcases qd with e | e
    · left; rw [eop, e]; exact g4.symm
    · right; rw [eo, edR]; exact e
  · simp only [cx, g7]; omega
  · simp only [ad, AL, g2, g3]; exact wa
  · rw [show dp s = σ.gpr .x4 from g4, eL]; exact wd
  · simp only [tp, g6]; exact wt
  · simp only [kp, g0]; exact wk
  · simp only [np, g1]; exact wn
  · rw [esR, ekR]; exact sk
  · rw [esR, enR]; exact sn
  · rw [esR, eaR]; exact sa
  · rw [esR, edR]; exact sd
  · rw [esR, etR]; exact st
  · rw [esR, eqR]; exact sq
  · simp only [cx, g7]; exact wc

/-- `saveData`'s stores are outside the arguments the body reads. -/
theorem slot_bytes {σ : State} (hp : preOpenAArch64 σ) {m : Mem} (hf : Frame [slotOf σ] σ.mem m) :
    bytesAt m (σ.gpr .x0) 32 = bytesAt σ.mem (σ.gpr .x0) 32 ∧
      bytesAt m (σ.gpr .x1) 12 = bytesAt σ.mem (σ.gpr .x1) 12 ∧
      bytesAt m (σ.gpr .x2) (σ.gpr .x3).toNat = bytesAt σ.mem (σ.gpr .x2) (σ.gpr .x3).toNat ∧
      bytesAt m (σ.gpr .x4) (σ.gpr .x5).toNat = bytesAt σ.mem (σ.gpr .x4) (σ.gpr .x5).toNat ∧
      bytesAt m (σ.gpr .x6) 16 = bytesAt σ.mem (σ.gpr .x6) 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, sk, sn, sa, sd, st, -⟩ := hp
  have one : ∀ {r : Region}, (slotOf σ).Disjoint r → ∀ q ∈ [slotOf σ], r.Disjoint q := fun h q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact h.symm
  exact ⟨bytesAt_frame hf (one sk) (by decide), bytesAt_frame hf (one sn) (by decide),
    bytesAt_frame hf (one sa) (Nat.le_of_lt (σ.gpr .x3).isLt),
    bytesAt_frame hf (one sd) (Nat.le_of_lt (σ.gpr .x5).isLt), bytesAt_frame hf (one st) (by decide)⟩

theorem post_of_save {σ s₁ s' : State} (hp : preOpenAArch64 σ) (hg : ∀ r, r ≠ .x28 → s₁.gpr r = σ.gpr r)
    (hf : Frame [slotOf σ] σ.mem s₁.mem) (h : openAArch64.post s₁ s') : openAArch64.post σ s' := by
  obtain ⟨bk, bn, ba, bd, bt⟩ := slot_bytes hp hf
  rw [openAArch64, Contract.post_mk] at h ⊢
  rw [hg .x0 (by decide), hg .x1 (by decide), hg .x2 (by decide), hg .x3 (by decide), hg .x4 (by decide),
    hg .x5 (by decide), hg .x6 (by decide), hg .x8 (by decide), bk, bn, ba, bd, bt] at h
  exact h

theorem ok_of_save {σ s₁ : State} (hp : preOpenAArch64 σ) (hg : ∀ r, r ≠ .x28 → s₁.gpr r = σ.gpr r)
    (hf : Frame [slotOf σ] σ.mem s₁.mem) : okAArch64 s₁ = okAArch64 σ := by
  obtain ⟨bk, bn, ba, bd, bt⟩ := slot_bytes hp hf
  unfold okAArch64
  rw [hg .x0 (by decide), hg .x1 (by decide), hg .x2 (by decide), hg .x3 (by decide), hg .x4 (by decide),
    hg .x5 (by decide), hg .x6 (by decide), bk, bn, ba, bd, bt]

/-- `open`'s body, from the source (`x4`) to the destination (`x8`). -/
theorem openBody_ok (v : Proof.ChaCha20.AArch64.XorImpl) (σ : State) (hs : preOpenAArch64 σ) :
    WP isa (openCode v.callee v.stitched) σ fun s' => abiPreserved σ s' ∧ openAArch64.post σ s' := by
  rw [openCode_eq]
  refine WP.seq (WP.mono (WP.withSp (WP.preservedV (saveData_ok hs) (by lit_decide)))
    fun s₁ ⟨⟨⟨g₁, x28₁, rd₁, wr₁, f₁, d₁, l₁, c₁⟩, v₁⟩, sp₁⟩ => ?_)
  have hp₁ : APre false s₁ := APre.ofOpen hs g₁ x28₁ rd₁ wr₁
  have eop := op_ofOpen g₁ x28₁
  have e7 : cx s₁ = σ.gpr .x7 := g₁ .x7 (by decide)
  refine WP.seq (WP.mono (openMainCode_ok v hp₁) fun s₂ h₂ => ?_)
  refine WP.mono (openTail_ok (σ := σ) hp₁ h₂ (by rw [e7, d₁, eop]) (by rw [e7, l₁, g₁ .x5 (by decide)])
    (by rw [e7, c₁]) g₁ sp₁ v₁ (by rw [eop, g₁ .x8 (by decide)]))
    fun s₃ ⟨ha, hq⟩ => ⟨ha, post_of_save hs g₁ f₁ hq⟩

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

theorem restore28_taint : ∃ h, (taint.check (Taint.ofRegs [.x21])
    (.block (.ldr .x .x28 .x21 1296 :: restore)) h).isSome = true := ⟨_, by taint_decide⟩

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
    (d₁ : τ₁.mem.readW (off (cx τ₁) 1280) 64 = op false τ₁)
    (l₁ : τ₁.mem.readW (off (cx τ₁) 1288) 64 = τ₁.gpr .x5)
    (d₂ : τ₂.mem.readW (off (cx τ₂) 1280) 64 = op false τ₂)
    (l₂ : τ₂.mem.readW (off (cx τ₂) 1288) 64 = τ₂.gpr .x5)
    (ecx : cx τ₁ = cx τ₂) (eop : op false τ₁ = op false τ₂) (el : τ₁.gpr .x5 = τ₂.gpr .x5)
    (etp : tp τ₁ = tp τ₂) (hok : okAArch64 τ₁ = okAArch64 τ₂) (sp : ρ₁.sp = ρ₂.sp) :
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
  have dw₁ : w₁.mem.readW (off (cx τ₁) 1280) 64 = op false τ₁ := by
    rw [mw₁, m₁.slot hp₁ (Nat.le_refl _) (by decide), d₁]
  have dw₂ : w₂.mem.readW (off (cx τ₂) 1280) 64 = op false τ₂ := by
    rw [mw₂, m₂.slot hp₂ (Nat.le_refl _) (by decide), d₂]
  have lw₁ : w₁.mem.readW (off (cx τ₁) 1288) 64 = τ₁.gpr .x5 := by
    rw [mw₁, m₁.slot hp₁ (by decide) (by decide), l₁]
  have lw₂ : w₂.mem.readW (off (cx τ₂) 1288) 64 = τ₂.gpr .x5 := by
    rw [mw₂, m₂.slot hp₂ (by decide) (by decide), l₂]
  have spw : w₁.sp = w₂.sp := by rw [sp₁, sp₂, spu]
  refine rel_seq ?_ (zeroIte_ok hp₁ x21w₁ rdw₁ wrw₁ dw₁ lw₁) (zeroIte_ok hp₂ x21w₂ rdw₂ wrw₂ dw₂ lw₂)
    fun z₁ z₂ ⟨x21z₁, spz₁⟩ ⟨x21z₂, spz₂⟩ => rel_taint [.x21] (by rw [spz₁, spz₂, spw])
      (by simp only [List.mem_singleton, forall_eq, x21z₁, x21z₂, x21w₁, x21w₂, ecx]) restore28_taint
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
          · rw [x9₁, x9₂, eop]
          · rw [x10₁, x10₂, el]) zeroLoop_taint
  · exact (rel_taint [] spw (by simp) skip_taint).mono (fun _ _ h => h.1) fun _ _ h => h

/-- `open`'s body, in two runs from states that agree on its arguments and on
whether the tag is right. -/
theorem openBody_rel (v : Proof.ChaCha20.AArch64.XorImpl) {σ₁ σ₂ : State} (h₁ : preOpenAArch64 σ₁)
    (h₂ : preOpenAArch64 σ₂)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8], σ₁.gpr r = σ₂.gpr r)
    (psp : σ₁.sp = σ₂.sp) (hok : okAArch64 σ₁ = okAArch64 σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (openCode v.callee v.stitched) TT := by
  rw [openCode_eq]
  have p4 := hq .x4 (by simp); have p5 := hq .x5 (by simp); have p6 := hq .x6 (by simp)
  have p7 := hq .x7 (by simp); have p8 := hq .x8 (by simp)
  refine rel_seq (rel_taint [.x7] psp (by simp only [List.mem_singleton, forall_eq, p7]) saveData_taint)
    (WP.withSp (saveData_ok h₁)) (WP.withSp (saveData_ok h₂))
    (fun τ₁ τ₂ ⟨⟨g₁, x28₁, rd₁, wr₁, f₁, d₁, l₁, _⟩, sp₁⟩ ⟨⟨g₂, x28₂, rd₂, wr₂, f₂, d₂, l₂, _⟩, sp₂⟩ => ?_)
  have hpτ₁ := APre.ofOpen h₁ g₁ x28₁ rd₁ wr₁
  have hpτ₂ := APre.ofOpen h₂ g₂ x28₂ rd₂ wr₂
  have eop₁ := op_ofOpen g₁ x28₁
  have eop₂ := op_ofOpen g₂ x28₂
  have spτ : τ₁.sp = τ₂.sp := by rw [sp₁, sp₂, psp]
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x28] spτ
      (fun r hr => ?_) v.openTaint)
    (openMainCode_ok v hpτ₁) (openMainCode_ok v hpτ₂) fun ρ₁ ρ₂ mo₁ mo₂ => ?_
  · by_cases h28 : r = .x28
    · subst h28; rw [x28₁, x28₂, p8, p4]
    · have hs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x28], r ≠ .x28 →
          r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8] := by decide
      rw [g₁ r h28, g₂ r h28]
      exact hq r (hs r hr h28)
  · exact tail_rel hpτ₁ hpτ₂ mo₁ mo₂
      (by rw [show cx τ₁ = σ₁.gpr .x7 from g₁ .x7 (by decide), d₁, eop₁])
      (by rw [show cx τ₁ = σ₁.gpr .x7 from g₁ .x7 (by decide), l₁, g₁ .x5 (by decide)])
      (by rw [show cx τ₂ = σ₂.gpr .x7 from g₂ .x7 (by decide), d₂, eop₂])
      (by rw [show cx τ₂ = σ₂.gpr .x7 from g₂ .x7 (by decide), l₂, g₂ .x5 (by decide)])
      (by simp only [cx, g₁ .x7 (by decide), g₂ .x7 (by decide), p7]) (by rw [eop₁, eop₂, p8])
      (by rw [g₁ .x5 (by decide), g₂ .x5 (by decide), p5])
      (by simp only [tp, g₁ .x6 (by decide), g₂ .x6 (by decide), p6])
      (by rw [ok_of_save h₁ g₁ f₁, ok_of_save h₂ g₂ f₂, hok])
      (by rw [mo₁.inv.sp, mo₂.inv.sp, spτ])

/-! ## `open`, in place

The function moves the data's address to the destination (`mov x8, x4`) and
runs the body. -/

open VG.AArch64 in
/-- `open`'s precondition with permission to write only the data, the
context and the 32 bytes after it (`openWr`). -/
def preInAArch64 (s : AArch64.State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let data : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let tag : Region := ⟨s.gpr .x6, 16⟩
  let work : Region := ⟨s.gpr .x7, 1280⟩
  let slot : Region := ⟨s.gpr .x7 + BitVec.ofNat 64 1280, 32⟩
  key ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ tag ∈ s.rd ∧ s.wr = [data, work, slot] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint data ∧
  work.Disjoint tag ∧
  data.Disjoint key ∧ data.Disjoint nonce ∧ data.Disjoint aad ∧ data.Disjoint tag ∧
  slot.Disjoint key ∧ slot.Disjoint nonce ∧ slot.Disjoint aad ∧ slot.Disjoint data ∧
  slot.Disjoint tag ∧
  (s.gpr .x7).toNat + 1312 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64

open VG.AArch64 in
/-- `vg_chacha20_poly1305_open(key, nonce, aad, aad_len, data, len, tag, work) -> u32`
(`preInAArch64`): zeros at `data` if the tag is wrong; it may leak whether it
is (`openLeakAArch64`). -/
def openInAArch64 : Contract AArch64.isa where
  pre := preInAArch64
  post s s' :=
    match decrypt (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 12)
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (bytesAt s.mem (s.gpr .x6) 16) with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = List.replicate (s.gpr .x5).toNat 0
  pub s₁ s₂ := pubAArch64 s₁ s₂ ∧ openLeakAArch64 s₁ = openLeakAArch64 s₂

/-- `mov x8, x4`. -/
theorem movIn_ok (σ : State) :
    WP isa (.block [mov .x8 .x4]) σ fun u => (∀ r, r ≠ .x8 → u.gpr r = σ.gpr r) ∧
      u.gpr .x8 = σ.gpr .x4 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.sp = σ.sp ∧ u.v = σ.v :=
  VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun _ hu hsp hv =>
    WP.block_nil ⟨hu.other, hu.gpr, hu.mem, hu.rd, hu.wr, hsp, hv⟩

theorem movIn_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block [mov .x8 .x4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The body's precondition, after `mov x8, x4`. -/
theorem preIn_body {s u : State} (h : preInAArch64 s) (hg : ∀ r, r ≠ .x8 → u.gpr r = s.gpr r)
    (h8 : u.gpr .x8 = s.gpr .x4) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) : preOpenAArch64 u := by
  obtain ⟨hk, hn, ha, ht, hw, ck, cn, ca, cd, ct, dk, dn, da, dt, sk, sn, sa, sd, st, wc, wa, wd, wt, wk,
    wn⟩ := h
  simp only [preOpenAArch64]
  rw [hg .x0 (by decide), hg .x1 (by decide), hg .x2 (by decide), hg .x3 (by decide), hg .x4 (by decide),
    hg .x5 (by decide), hg .x6 (by decide), hg .x7 (by decide), h8, hrd, hwr]
  exact ⟨hk, hn, ha, ht, List.mem_append_right _ (by rw [hw]; simp), hw, ck, cn, ca, cd, ct, cd, dk, dn, da, dt,
    .inl rfl, sk, sn, sa, sd, st, sd, wc, wa, wd, wd, wt, wk, wn⟩

theorem openIn_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : openInAArch64.pre s) :
    ∃ t s', Exec isa (openInPlace v.callee v.stitched) s t s' ∧
      abiPreserved s s' ∧ openInAArch64.post s s' := by
  show WP isa (.seq (.block [mov .x8 .x4]) (openCode v.callee v.stitched)) s _
  refine WP.seq (WP.mono (movIn_ok s) fun u ⟨hg, h8, hm, hrd, hwr, hsp, hv⟩ => ?_)
  refine WP.mono (openBody_ok v u (preIn_body hs hg h8 hrd hwr)) fun s' ⟨ha, hq⟩ => ⟨?_, ?_⟩
  · exact ⟨fun r hr => by rw [ha.1 r hr, hg r (by rintro rfl; simp [preserved] at hr)], by rw [ha.2.1, hsp],
      fun r hr => by rw [ha.2.2 r hr, hv]⟩
  · rw [openAArch64, Contract.post_mk] at hq
    rw [openInAArch64, Contract.post_mk]
    rw [hm, hg .x0 (by decide), hg .x1 (by decide), hg .x2 (by decide), hg .x3 (by decide),
      hg .x4 (by decide), hg .x5 (by decide), hg .x6 (by decide), h8] at hq
    exact hq

theorem openIn_ct (v : Proof.ChaCha20.AArch64.XorImpl) :
    ConstantTime isa openInAArch64.pre openInAArch64.pub (openInPlace v.callee v.stitched) := by
  show ConstantTime isa _ _ (.seq (.block [mov .x8 .x4]) (openCode v.callee v.stitched))
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨hq, hl⟩ := hq
  have hr := pub_regs hq
  obtain ⟨-, -, -, -, -, -, -, -, psp⟩ := id hq
  have hok : okAArch64 σ₁ = okAArch64 σ₂ := leak_bool hl
  refine (rel_seq (rel_taint [] psp (by simp) movIn_taint) (movIn_ok σ₁) (movIn_ok σ₂) ?_
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  rintro u₁ u₂ ⟨g₁, x8₁, m₁, rd₁, wr₁, sp₁, -⟩ ⟨g₂, x8₂, m₂, rd₂, wr₂, sp₂, -⟩
  have hs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8], r ≠ .x8 →
      r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] := by decide
  refine openBody_rel v (preIn_body h₁ g₁ x8₁ rd₁ wr₁) (preIn_body h₂ g₂ x8₂ rd₂ wr₂) (fun r hr' => ?_)
    (by rw [sp₁, sp₂, psp]) ?_
  · by_cases h8 : r = .x8
    · subst h8; rw [x8₁, x8₂]; exact hr .x4 (by simp)
    · rw [g₁ r h8, g₂ r h8]; exact hr r (hs r hr' h8)
  · unfold okAArch64
    rw [m₁, m₂, g₁ .x0 (by decide), g₁ .x1 (by decide), g₁ .x2 (by decide), g₁ .x3 (by decide),
      g₁ .x4 (by decide), g₁ .x5 (by decide), g₁ .x6 (by decide), g₂ .x0 (by decide), g₂ .x1 (by decide),
      g₂ .x2 (by decide), g₂ .x3 (by decide), g₂ .x4 (by decide), g₂ .x5 (by decide), g₂ .x6 (by decide)]
    exact hok

/-! ## `open_to`

The function moves the destination to `x8` (`mov x8, x6`), loads `tag` and
`work` from the stack into `x6` and `x7`, and runs the body. -/

open VG.AArch64 in
/-- `open_to`'s precondition with permission to write only the destination,
the context and the 32 bytes after it (`toWr`), and `dst_len = len`. -/
def preToN (s : AArch64.State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let src : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let dst : Region := ⟨s.gpr .x6, (s.gpr .x5).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 1280⟩
  let slot : Region := ⟨stackArg s 1 + BitVec.ofNat 64 1280, 32⟩
  let args : Region := ⟨stackArgAddr s 0, 16⟩
  key ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ tag ∈ s.rd ∧ src ∈ s.rd ∧ args ∈ s.rd ∧
  s.wr = [dst, work, slot] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint src ∧
  work.Disjoint tag ∧ work.Disjoint dst ∧
  dst.Disjoint key ∧ dst.Disjoint nonce ∧ dst.Disjoint aad ∧ dst.Disjoint tag ∧ src.Disjoint dst ∧
  slot.Disjoint key ∧ slot.Disjoint nonce ∧ slot.Disjoint aad ∧ slot.Disjoint src ∧
  slot.Disjoint tag ∧ slot.Disjoint dst ∧
  (stackArg s 1).toNat + 1312 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧
  (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64 ∧ s.sp.toNat + 16 ≤ 2 ^ 64

open VG.AArch64 in
/-- `open_to`'s result: `decrypt` of the source, with the tag at the first
stack argument. -/
def openToRes (s : AArch64.State) : Option (List Byte) :=
  decrypt (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 12)
    (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (bytesAt s.mem (stackArg s 0) 16)

open VG.AArch64 in
/-- What `open_to` may leak: whether the message is authenticated. -/
def openToLeakAArch64 (s : AArch64.State) : List Nat := [if (openToRes s).isSome then 1 else 0]

open VG.AArch64 in
def pubToAArch64 (s₁ s₂ : AArch64.State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
  s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
  s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
  stackArg s₁ 1 = stackArg s₂ 1

open VG.AArch64 in
/-- `vg_chacha20_poly1305_open_to(key, nonce, aad, aad_len, src, len, dst, dst_len, tag, work) -> u32`
(`preToN`): decrypts from `src` to `dst`, zeros at `dst` if the tag is wrong;
it may leak whether it is (`openToLeakAArch64`). -/
def openToN : Contract AArch64.isa where
  pre := preToN
  post s s' :=
    match openToRes s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x5).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x6) (s.gpr .x5).toNat = List.replicate (s.gpr .x5).toNat 0
  pub s₁ s₂ := pubToAArch64 s₁ s₂ ∧ openToLeakAArch64 s₁ = openToLeakAArch64 s₂

/-- An `ldr` from the stack, keeping the stack pointer and the vector registers. -/
theorem wp_ldrSp64 {s : State} {t : Reg} {off : Nat} {is : List Instr} {Q : State → Prop}
    (ho : off % 8 = 0 ∧ off < 32768) (h : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8)
    (k : ∀ s', Upd s s' t (s.mem.readW (s.sp + BitVec.ofNat 64 off) 64) → s'.sp = s.sp → s'.v = s.v →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (exec_ldrSp ho h) (k _ (Upd.write64 _ _ _) rfl rfl)

/-- `open_to`'s moves. -/
theorem toEntry_ok {σ : State} (ha : (⟨stackArgAddr σ 0, 16⟩ : Region) ∈ σ.rd)
    (_hsp : σ.sp.toNat + 16 ≤ 2 ^ 64) :
    WP isa (.block [mov .x8 .x6, .ldrSp .x6 0, .ldrSp .x7 8]) σ fun u =>
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → u.gpr r = σ.gpr r) ∧ u.gpr .x8 = σ.gpr .x6 ∧
      u.gpr .x6 = stackArg σ 0 ∧ u.gpr .x7 = stackArg σ 1 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧
      u.wr = σ.wr ∧ u.sp = σ.sp ∧ u.v = σ.v := by
  have ha' : (⟨σ.sp, 16⟩ : Region) ∈ σ.rd := by
    have e : stackArgAddr σ 0 = σ.sp := by simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    rw [← e]; exact ha
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, List.mem_append_left _ ha', Offset.contains_base _ hd (by omega)⟩
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun u₁ v₁ sp₁ w₁ => ?_
  refine wp_ldrSp64 (by decide) (by rw [v₁.rd, v₁.wr, sp₁]; exact hin 0 (by decide)) fun u₂ v₂ sp₂ w₂ => ?_
  refine wp_ldrSp64 (by decide) (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, sp₂, sp₁]; exact hin 8 (by decide))
    fun u₃ v₃ sp₃ w₃ => WP.block_nil ⟨fun r h6 h7 h8 => by rw [v₃.other r h7, v₂.other r h6, v₁.other r h8],
      by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr],
      by rw [v₃.other _ (by decide), v₂.gpr, v₁.mem, sp₁]; rfl,
      by rw [v₃.gpr, v₂.mem, v₁.mem, sp₂, sp₁]; rfl,
      by rw [v₃.mem, v₂.mem, v₁.mem], by rw [v₃.rd, v₂.rd, v₁.rd], by rw [v₃.wr, v₂.wr, v₁.wr],
      by rw [sp₃, sp₂, sp₁], by rw [w₃, w₂, w₁]⟩

theorem toEntry_taint : ∃ h, (taint.check (Taint.ofRegs [])
    (.block [mov .x8 .x6, .ldrSp .x6 0, .ldrSp .x7 8]) h).isSome = true := ⟨_, by taint_decide⟩

/-- The body's precondition, after `open_to`'s moves. -/
theorem preTo_body {s u : State} (h : preToN s)
    (hg : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → u.gpr r = s.gpr r) (h8 : u.gpr .x8 = s.gpr .x6)
    (h6 : u.gpr .x6 = stackArg s 0) (h7 : u.gpr .x7 = stackArg s 1) (hrd : u.rd = s.rd)
    (hwr : u.wr = s.wr) : preOpenAArch64 u := by
  obtain ⟨hk, hn, ha, ht, hd, -, hw, ck, cn, ca, cd, ct, cq, qk, qn, qa, qt, dq, sk, sn, sa, sd, st, sq,
    wc, wa, wd, wq, wt, wk, wn, -⟩ := h
  simp only [preOpenAArch64]
  rw [hg .x0 (by decide) (by decide) (by decide), hg .x1 (by decide) (by decide) (by decide),
    hg .x2 (by decide) (by decide) (by decide), hg .x3 (by decide) (by decide) (by decide),
    hg .x4 (by decide) (by decide) (by decide), hg .x5 (by decide) (by decide) (by decide), h6, h7, h8,
    hrd, hwr]
  exact ⟨hk, hn, ha, ht, List.mem_append_left _ hd, hw, ck, cn, ca, cd, ct, cq, qk, qn, qa, qt, .inr dq,
    sk, sn, sa, sd, st, sq, wc, wa, wd, wq, wt, wk, wn⟩

theorem openTo_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : openToN.pre s) :
    ∃ t s', Exec isa (openTo v.callee v.stitched) s t s' ∧ abiPreserved s s' ∧ openToN.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, -, -, ha, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsp⟩ := hs'
  show WP isa (.seq (.block [mov .x8 .x6, .ldrSp .x6 0, .ldrSp .x7 8]) (openCode v.callee v.stitched)) s _
  refine WP.seq (WP.mono (toEntry_ok ha hsp) fun u ⟨hg, h8, h6, h7, hm, hrd, hwr, hsp', hv⟩ => ?_)
  refine WP.mono (openBody_ok v u (preTo_body hs hg h8 h6 h7 hrd hwr)) fun s' ⟨ha', hq⟩ => ⟨?_, ?_⟩
  · exact ⟨fun r hr => by
      rw [ha'.1 r hr, hg r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
        (by rintro rfl; simp [preserved] at hr)], by rw [ha'.2.1, hsp'], fun r hr => by rw [ha'.2.2 r hr, hv]⟩
  · rw [openAArch64, Contract.post_mk] at hq
    rw [openToN, Contract.post_mk, openToRes]
    rw [hm, hg .x0 (by decide) (by decide) (by decide), hg .x1 (by decide) (by decide) (by decide),
      hg .x2 (by decide) (by decide) (by decide), hg .x3 (by decide) (by decide) (by decide),
      hg .x4 (by decide) (by decide) (by decide), hg .x5 (by decide) (by decide) (by decide), h6, h8] at hq
    exact hq

theorem openTo_ct (v : Proof.ChaCha20.AArch64.XorImpl) :
    ConstantTime isa openToN.pre openToN.pub (openTo v.callee v.stitched) := by
  show ConstantTime isa _ _ (.seq (.block [mov .x8 .x6, .ldrSp .x6 0, .ldrSp .x7 8]) (openCode v.callee v.stitched))
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨psp, p0, p1, p2, p3, p4, p5, p6, p7, a0, a1⟩, hl⟩ := hq
  have hok : (openToRes σ₁).isSome = (openToRes σ₂).isSome := leak_bool hl
  have h₁' := h₁
  have h₂' := h₂
  obtain ⟨-, -, -, -, -, ha₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsp₁⟩ := h₁'
  obtain ⟨-, -, -, -, -, ha₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsp₂⟩ := h₂'
  refine (rel_seq (rel_taint [] psp (by simp) toEntry_taint) (toEntry_ok ha₁ hsp₁) (toEntry_ok ha₂ hsp₂) ?_
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  rintro u₁ u₂ ⟨g₁, x8₁, x6₁, x7₁, m₁, rd₁, wr₁, sp₁, -⟩ ⟨g₂, x8₂, x6₂, x7₂, m₂, rd₂, wr₂, sp₂, -⟩
  have hg (r : Reg) (h : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5]) : u₁.gpr r = u₂.gpr r := by
    have h' : r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 := by revert r; decide
    rw [g₁ r h'.1 h'.2.1 h'.2.2, g₂ r h'.1 h'.2.1 h'.2.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  refine openBody_rel v (preTo_body h₁ g₁ x8₁ x6₁ x7₁ rd₁ wr₁) (preTo_body h₂ g₂ x8₂ x6₂ x7₂ rd₂ wr₂)
    (fun r hr => ?_) (by rw [sp₁, sp₂, psp]) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [x6₁, x6₂, a0]
    · rw [x7₁, x7₂, a1]
    · rw [x8₁, x8₂, p6]
  · unfold okAArch64
    rw [m₁, m₂, g₁ .x0 (by decide) (by decide) (by decide), g₁ .x1 (by decide) (by decide) (by decide),
      g₁ .x2 (by decide) (by decide) (by decide), g₁ .x3 (by decide) (by decide) (by decide),
      g₁ .x4 (by decide) (by decide) (by decide), g₁ .x5 (by decide) (by decide) (by decide), x6₁,
      g₂ .x0 (by decide) (by decide) (by decide), g₂ .x1 (by decide) (by decide) (by decide),
      g₂ .x2 (by decide) (by decide) (by decide), g₂ .x3 (by decide) (by decide) (by decide),
      g₂ .x4 (by decide) (by decide) (by decide), g₂ .x5 (by decide) (by decide) (by decide), x6₂]
    exact hok

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
and its whole working space of 1312 bytes writable). -/
def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x1100 | .x2 => 0x2000 | .x4 => 0x2100 | .x6 => 0x3000 | .x7 => 0x4000
    | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x2100, 0⟩, ⟨0x4000, 1312⟩]

theorem seal_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (sealCode v.callee v.stitched) (sealScratchContract AArch64.abi 160) :=
  Verified.of_correct (seal_ok v) (seal_ct v) (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealAArch64,
      Proof.ChaCha20Poly1305.preAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      [sealSat] using sealSat)

open VG.AArch64 in
/-- `open`'s precondition with its whole working space, `work` (1312 bytes),
writable: what its contract gives, whose regions cover `preInAArch64`'s, the
context and the 32 bytes after it (`preOpenW_narrow`). -/
def preOpenW (s : AArch64.State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let data : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let tag : Region := ⟨s.gpr .x6, 16⟩
  let work : Region := ⟨s.gpr .x7, 1312⟩
  s.rd = [key, nonce, aad, tag] ∧ s.wr = [data, work] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint data ∧
  work.Disjoint tag ∧
  data.Disjoint key ∧ data.Disjoint nonce ∧ data.Disjoint aad ∧ data.Disjoint tag ∧
  (s.gpr .x7).toNat + 1312 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64

/-- `openInAArch64`, with `preOpenW`. -/
def openW : Contract AArch64.isa where
  pre := preOpenW
  post := openInAArch64.post
  pub := openInAArch64.pub

/-- The regions `preInAArch64` permits writing: the data, the context and the
32 bytes after it. -/
def openWr (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 1280⟩, ⟨s.gpr .x7 + BitVec.ofNat 64 1280, 32⟩]

theorem preOpenW_narrow {s : State} (h : preOpenW s) : preInAArch64 (s.withRegions s.rd (openWr s)) := by
  obtain ⟨hrd, -, c_k, c_n, c_a, c_d, c_t, d_k, d_n, d_a, d_t, wc, wa, wd, wt, wk, wn⟩ := h
  have sc : Region.Sub ⟨s.gpr .x7, 1280⟩ ⟨s.gpr .x7, 1312⟩ := Region.sub_prefix (by decide)
  have ss : Region.Sub ⟨s.gpr .x7 + BitVec.ofNat 64 1280, 32⟩ ⟨s.gpr .x7, 1312⟩ := sub_off _ (by decide)
  have m0 : (⟨s.gpr .x0, 32⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have m1 : (⟨s.gpr .x1, 12⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have m2 : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have m6 : (⟨s.gpr .x6, 16⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  exact ⟨m0, m1, m2, m6, rfl, c_k.sub_left sc, c_n.sub_left sc, c_a.sub_left sc,
    c_d.sub_left sc, c_t.sub_left sc, d_k, d_n, d_a, d_t,
    c_k.sub_left ss, c_n.sub_left ss, c_a.sub_left ss, c_d.sub_left ss, c_t.sub_left ss, wc, wa, wd, wt, wk, wn⟩

theorem openWr_covers {s : State} (h : preOpenW s) : Covers (openWr s) s.wr := by
  rw [h.2.1]
  refine Covers.of_sub fun r hr => ?_
  simp only [openWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 0, (BitVec.add_zero _).symm,
      show 0 + 1280 ≤ 1312 by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 1280, rfl, show 1280 + 32 ≤ 1312 by decide⟩

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem openW_implies : openW.Implies (openZeroScratchContract AArch64.abi 164) :=
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakAArch64, openW, preOpenW,
          openInAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, AArch64.abi, AArch64.argRegs]
        simp only [openW, openInAArch64] at h
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
          openInAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakAArch64, openW, preOpenW,
          openInAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
          [openSat] using openSat }

/-- `open` against `openInAArch64`, whose precondition permits writing only the
data, the context and the 32 bytes after it. -/
theorem open_verifiedN (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openInPlace v.callee v.stitched) openInAArch64 :=
  ⟨openIn_ok v, openIn_ct v, openW_implies.sat_left.elim fun _ hs => ⟨_, preOpenW_narrow hs⟩⟩

/-- Then against `openW`, which permits writing all of `work`: the code runs as
it does with fewer permissions (`RegionModel.verified_narrowTo`). -/
theorem open_verifiedW (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openInPlace v.callee v.stitched) openW :=
  regionModel.verified_narrowTo (T := AArch64.target) (fun _ _ _ _ h => h) (open_verifiedN v)
    (fun s => s.rd) openWr (fun _ hs => preOpenW_narrow hs)
    (fun _ hs => (Covers.refl _).append (openWr_covers hs)) (fun _ hs => openWr_covers hs)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) openW_implies.sat_left

theorem open_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openInPlace v.callee v.stitched) (openZeroScratchContract AArch64.abi 164) :=
  Verified.of_implies (open_verifiedW v) openW_implies

open VG.AArch64 in
/-- `open_to`'s precondition with its whole working space, `work` (1312
bytes), writable: what its contract gives (`tag` and `work` on the stack). -/
def preToW (s : AArch64.State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let src : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let dst : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 1312⟩
  let args : Region := ⟨stackArgAddr s 0, 16⟩
  s.rd = [key, nonce, aad, src, tag, args] ∧ s.wr = [dst, work] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint src ∧
  work.Disjoint dst ∧ work.Disjoint tag ∧
  dst.Disjoint key ∧ dst.Disjoint nonce ∧ dst.Disjoint aad ∧ dst.Disjoint src ∧ dst.Disjoint tag ∧
  (stackArg s 1).toNat + 1312 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
  (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64 ∧
  s.sp.toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat = (s.gpr .x5).toNat

/-- `openToN`, with `preToW`. -/
def openToW : Contract AArch64.isa where
  pre := preToW
  post := openToN.post
  pub := openToN.pub

/-- The regions `preToN` permits writing: the destination, the context and the
32 bytes after it. -/
def toWr (s : State) : List Region :=
  [⟨s.gpr .x6, (s.gpr .x5).toNat⟩, ⟨stackArg s 1, 1280⟩, ⟨stackArg s 1 + BitVec.ofNat 64 1280, 32⟩]

theorem preToW_narrow {s : State} (h : preToW s) : preToN (s.withRegions s.rd (toWr s)) := by
  obtain ⟨hrd, -, ck, cn, ca, cs, cq, ct, qk, qn, qa, qs, qt, wc, wa, ws, wq, wt, wk, wn, wsp, h75⟩ := h
  have sc : Region.Sub ⟨stackArg s 1, 1280⟩ ⟨stackArg s 1, 1312⟩ := Region.sub_prefix (by decide)
  have ss : Region.Sub ⟨stackArg s 1 + BitVec.ofNat 64 1280, 32⟩ ⟨stackArg s 1, 1312⟩ := sub_off _ (by decide)
  have eq : (⟨s.gpr .x6, (s.gpr .x5).toNat⟩ : Region) = ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ := by rw [h75]
  have m0 : (⟨s.gpr .x0, 32⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have m1 : (⟨s.gpr .x1, 12⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have m2 : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have m4 : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have mt : (⟨stackArg s 0, 16⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have ma : (⟨stackArgAddr s 0, 16⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  rw [← eq] at cq qk qn qa qt qs
  rw [h75] at wq
  exact ⟨m0, m1, m2, mt, m4, ma, rfl, ck.sub_left sc, cn.sub_left sc,
    ca.sub_left sc, cs.sub_left sc, ct.sub_left sc, cq.sub_left sc, qk, qn, qa, qt, qs.symm,
    ck.sub_left ss, cn.sub_left ss, ca.sub_left ss, cs.sub_left ss, ct.sub_left ss,
    cq.sub_left ss, wc, wa, ws, wq, wt, wk, wn, wsp⟩

theorem toWr_covers {s : State} (h : preToW s) : Covers (toWr s) s.wr := by
  obtain ⟨-, hw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h75⟩ := h
  rw [hw]
  refine Covers.of_sub fun r hr => ?_
  simp only [toWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, by simp only [h75]; omega⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 0, (BitVec.add_zero _).symm,
      show 0 + 1280 ≤ 1312 by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 1280, rfl, show 1280 + 32 ≤ 1312 by decide⟩

/-- The indices of `open_to`'s two stack arguments, for the calling
convention's evaluation. -/
theorem range2 : List.range 2 = [0, 1] := rfl

/-- A state satisfying `open_to`'s precondition (as `sealSat`, with no source
and no destination): the stack arguments at `0x9000`, `tag` (`0x3000`) and
`work` (`0x4000`). -/
def openToSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x1100 | .x2 => 0x2000 | .x4 => 0x2100 | .x6 => 0x2200
    | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x30 else bif Nat.beq a.toNat 0x9009 then 0x40 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x2200, 0⟩, ⟨0x4000, 1312⟩]

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem openToW_implies : openToW.Implies (openToScratchContract AArch64.abi 164) :=
    { pre := by
        intro s h
        sig_pre [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil] at h
        sig_split h
        -- The facts of the stack arguments' regions, which `sig_split` leaves together.
        rename_i hc _ _ _ _ _ _ _ _
        simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
          Bool.false_or, Bool.true_or, List.cons_append, List.nil_append,
          Sig.conj_cons_cons, Sig.conj_single] at hc
        obtain ⟨-, hta, -⟩ := hc
        sig_reduce [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil]
        sig_simp [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil] []
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | sig_disjoint_symm
          | omega
          | (sig_simp_only [Nat.mul_comm] at *
             first | with_reducible assumption | sig_disjoint_symm)
          | simp only [*, List.mem_cons, List.mem_singleton, true_or, or_true]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
          Spec.ChaCha20Poly1305.openToPost, AArch64.abi, AArch64.argRegs, range2]
        simp only [openToW, openToN, openToRes] at h
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
        intro s₁ s₂ _ _ h
        sig_pub [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil] at h
        sig_split h
        rename_i hsp hl h0 h1 h2 h3 h4 h5 h6 h7 a0
        exact ⟨⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7, a0, h⟩, hl⟩
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil]
          [openToSat, AArch64.stackArg, AArch64.stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax]
          using openToSat }

/-- `open_to` against `openToN`, whose precondition permits writing only the
destination, the context and the 32 bytes after it. -/
theorem openTo_verifiedN (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openTo v.callee v.stitched) openToN :=
  ⟨openTo_ok v, openTo_ct v, openToW_implies.sat_left.elim fun _ hs => ⟨_, preToW_narrow hs⟩⟩

theorem openTo_verifiedW (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openTo v.callee v.stitched) openToW :=
  regionModel.verified_narrowTo (T := AArch64.target) (fun _ _ _ _ h => h) (openTo_verifiedN v)
    (fun s => s.rd) toWr (fun _ hs => preToW_narrow hs)
    (fun _ hs => (Covers.refl _).append (toWr_covers hs)) (fun _ hs => toWr_covers hs)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) openToW_implies.sat_left

theorem openTo_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openTo v.callee v.stitched) (openToScratchContract AArch64.abi 164) :=
  Verified.of_implies (openTo_verifiedW v) openToW_implies

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

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openZeroContract AArch64.abi 1312).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, AArch64.abi, AArch64.argRegs]
    [openFrameSat, openSat] using openFrameSat

theorem open_framed (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 1312 .x7 96 (openInPlace v.callee v.stitched))
      (Spec.ChaCha20Poly1305.openZeroContract AArch64.abi 1312) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 164) (post := Spec.ChaCha20Poly1305.openZeroPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (leak := some (Spec.ChaCha20Poly1305.openLeak AArch64.abi.ptrBits))
    (bytes := 1312) (words := 96) (open_verified v) (by decide) (by decide) (by decide)
    (openZeroPost_out _) openFrameSat_pre

/-- A state satisfying `open_to`'s precondition, without the working space:
the stack argument `tag` (`0x3000`) at `0x9000`. -/
def openToFrameSat : State :=
  { openToSat with mem a := bif Nat.beq a.toNat 0x9001 then 0x30 else 0,
                   rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x9000, 8⟩],
                   wr := [⟨0x2200, 0⟩] }

theorem openToFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openToContract AArch64.abi 1328).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openToContract, Spec.ChaCha20Poly1305.openToSig,
    Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
    AArch64.abi, AArch64.argRegs]
    [openToFrameSat, openToSat, AArch64.stackArg, AArch64.stackArgAddr, Mem.readW, Mem.read,
      Spec.ChaCha20Poly1305.pMax]
    using openToFrameSat

theorem openTo_framed (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratchWiped 1328 1 96 (openTo v.callee v.stitched))
      (Spec.ChaCha20Poly1305.openToContract AArch64.abi 1328) :=
  AArch64.Verified.stackArgScratchWipedPre (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work")
    (e := .u64) (n := 164) (pre := Spec.ChaCha20Poly1305.openToPre AArch64.abi.ptrBits)
    (post := Spec.ChaCha20Poly1305.openToPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (leak := some (Spec.ChaCha20Poly1305.openToLeak AArch64.abi.ptrBits))
    (bytes := 1328) (words := 96) (openTo_verified v) (by decide) (by decide) (by decide)
    (openToPre_local _) (openToPost_local _) (openToPost_out _) openToFrameSat_pre
    (hleak := openToLeak_local _)

end VG.Proof.ChaCha20Poly1305.AArch64
