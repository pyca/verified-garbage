module
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.RsaKeyGen.Table

import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds

/-!
# An FFDH parameter candidate on AArch64: a draw

`draw_ok`: the next `⌈mb / 8⌉` octets of the tape, cut to `mb` bits (the
witness `wA` of `drawWitness`), rejected (`kStat := 4`) unless in
`[2, N − 2]`, else the round (`round_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The modulus `N` of `mb` bits, its `w` words and its `K` checks. -/
structure MrDims (p : PP) (w N mb K : Nat) : Prop where
  hw : w = mW mb
  mb1 : 511 ≤ mb
  mb2 : mb ≤ 8192
  eZ : slot w aE + 8 * (w + 2) ≤ p.Z
  odd : N % 2 = 1
  n3 : 3 ≤ N
  bl : Spec.RsaKeyGen.bitLength (N - 1) = mb
  k : K < 2 ^ 62
  hL : p.L ≤ p.r.length
  mbb : mb ≤ p.bits

/-- What the witnesses of `N` keep. -/
structure MrFix (p : PP) (w N mb K : Nat) (s : State) : Prop where
  st : PSt p w s
  ctx : ∃ bm, MrCtx s p.B p.Z w N bm
  ex : ECtx s.mem p.B w N
  r2 : wv s.mem p.B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  len : word s.mem p.B (8 * kLen) = BitVec.ofNat 64 (mLen mb)
  top : word s.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK mb - 1)
  chk : word s.mem p.B (8 * fChecks) = BitVec.ofNat 64 K
  msk : word s.mem p.B (8 * Public.sMask) = mask true

/-- The witness drawn at offset `u`. -/
def wA (mb : Nat) (r : List Byte) (u : Nat) : Nat := Spec.Rsa.os2ip ((r.drop u).take (mLen mb)) % 2 ^ mb

/-- `kStat` after a draw. -/
def dStat (N K i a : Nat) : Nat :=
  if 2 ≤ a ∧ a < N - 1 then (if Spec.Ffdh.mrRound N a then (if i + 1 < K then 4 else 1) else 2) else 4

/-- `fIdx` after a draw. -/
def dIdx (N i a : Nat) : Nat := if 2 ≤ a ∧ a < N - 1 ∧ Spec.Ffdh.mrRound N a = true then i + 1 else i

theorem MrFix.of_frm {p : PP} {w N mb K : Nat} {s t : State} (h : MrFix p w N mb K s)
    (hEZ : slot w aE + 8 * (w + 2) ≤ p.Z) {rs : List (Nat × Nat)} (hf : Frm p.B rs s.mem t.mem) (hm : ∀ r ∈ rs, KMut r) (hp : ∀ r ∈ rs, PMut r) (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv)
    (dN : ∀ r ∈ rs, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN)
    (dB : ∀ r ∈ rs, slot w aB + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aB)
    (d1 : ∀ r ∈ rs, slot w aR1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR1)
    (dm : ∀ r ∈ rs, slot w aRm1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aRm1)
    (d2 : ∀ r ∈ rs, slot w aR2 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR2)
    (dE : ∀ r ∈ rs, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE)
    (dM : ∀ r ∈ rs, 8 * Public.sMask + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * Public.sMask)
    (dL : ∀ r ∈ rs, 8 * kLen + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * kLen)
    (dT : ∀ r ∈ rs, 8 * fTop + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * fTop)
    (dC : ∀ r ∈ rs, 8 * fChecks + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * fChecks) : MrFix p w N mb K t := by
  obtain ⟨bm, hc⟩ := h.ctx
  have hn := hc.ws.scr.nowrap
  have hZ' := hc.ws.hZ
  have h256 := hc.ws.h256
  have hc' := hc.of_frm hf hm k hr dI dN dB d1 dm
  have sR2 : slot w aR2 + 8 * (w + 2) ≤ p.Z := by
    have := VG.Proof.Rsa.slot_lt (w := w) (show aR2 < 16 by decide); omega_using [hZ', this]
  have sE : p.B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by omega_using [hEZ, hn]
  refine ⟨h.st.step hc'.ws hf hp hZ k, ⟨bm, hc'⟩, h.ex.of_frm hf dE sE, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.wv_eq d2 (by omega_using [hn, sR2])]; exact h.r2
  · rw [hf.word_eq dL (by simp only [kLen, sK, sFn]; omega_using [hn, h256])]; exact h.len
  · rw [hf.word_eq dT (by simp only [fTop]; omega_using [hn, h256])]; exact h.top
  · rw [hf.word_eq dC (by simp only [fChecks]; omega_using [hn, h256])]; exact h.chk
  · rw [hf.word_eq dM (by simp only [Public.sMask, sFn]; omega_using [hn, h256])]; exact h.msk

theorem mr_round_eq {N : Nat} (a : Nat) (hN : 3 ≤ N) (ho : N % 2 = 1) :
    Proof.MillerRabin.Round.round N a = Spec.Ffdh.mrRound N a := by
  simpa only [Proof.MillerRabin.Round.round] using VG.Proof.Ffdh.rsa_round_eq a hN ho

/-- The draw before its test. -/
def drawHead : List (Prog isa) := (draw (fun _ _ _ => .block []) []).take 9

theorem draw_eq (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) :
    draw mul roundCode = drawHead ++ ([.ite (.zero .x .x9) (.block [movi .x3 4, sth .x3 kStat])
      (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.round mul roundCode))] : List (Prog isa)) := rfl

/-- After `drawHead`, from `s₀`, with `i` witnesses passed and `u` octets
read before it. -/
structure DrawMid (p : PP) (w N mb K i u : Nat) (s₀ s : State) : Prop where
  fix : MrFix p w N mb K s
  used : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u + mLen mb)
  x9 : s.gpr .x9 = mask (decide (2 ≤ wA mb p.r u ∧ wA mb p.r u < N - 1))
  ax : wv s.mem p.B (slot w aX) w = wA mb p.r u
  idx : word s.mem p.B (8 * fIdx) = BitVec.ofNat 64 i
  isc : InScr p.B p.Z s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- `drawHead`: the witness and its range's mask. -/
theorem drawHead_ok {p : PP} {w N mb K i u : Nat} {s : State} (d : MrDims p w N mb K)
    (h : MrFix p w N mb K s) (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u)
    (hI : word s.mem p.B (8 * fIdx) = BitVec.ofNat 64 i) (hroom : u + mLen mb ≤ p.r.length) :
    WP isa (seqs drawHead) s (DrawMid p w N mb K i u s) := by
  have hws := h.st.ws
  have hn := hws.scr.nowrap
  have hEZ := d.eZ
  have hZ := hws.hZ
  have hw : w = mW mb := d.hw
  have hmb1 := d.mb1
  have hmb2 := d.mb2
  have hw8 : 8 ≤ w := by rw [hw]; simp only [mW]; omega_arith
  have hw128 : w ≤ 128 := by rw [hw]; simp only [mW]; omega_arith
  have hlw : mLen mb ≤ 8 * w := by rw [hw]; simp only [mLen, mW]; omega_arith
  have hl1 : 1 ≤ mLen mb := by simp only [mLen]; omega_arith
  have hk : mK mb ≤ 64 := by simp only [mK, mW]; omega_arith
  have hcut : 64 * (w - 1) + mK mb = mb := by rw [hw]; simp only [mK, mW]; omega_arith
  have sX : slot w aX + 8 * (w + 2) ≤ p.Z := by
    have := VG.Proof.Rsa.slot_lt (w := w) (show aX < 16 by decide); omega_using [hZ, this]
  unfold drawHead
  refine wp_seqs_append (a := [_, _, _]) (by simp) (by simp) ?_
  -- The octets.
  have hsrc := src_take (src_drop h.st.src u) (mLen mb)
  refine WP.mono (drawLoad_ok hws h.st.args.rand hU h.len hl1 hlw hsrc (by
    simp only [List.length_take, List.length_drop]; omega_arith)) fun s₁ ⟨hx₁, hu₁, f₁, ws₁, k₁⟩ => ?_
  have h₁ : MrFix p w N mb K s₁ := h.of_frm hEZ f₁ (by kmut)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact PMut.ofSlot _ _ _
      · exact PMut.hdr (by simp only [kUsed, sFn]; omega_arith))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sX
      · simp only [kUsed, sFn]; have := hws.h256; omega_arith)
    k₁ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
  have hI₁ : word s₁.mem p.B (8 * fIdx) = BitVec.ofNat 64 i := by
    rw [f₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [fIdx]; omega_arith)]; exact hI
  -- The cut.
  refine wp_seqs_append (a := [_]) (by simp) (by simp) ?_
  rw [seqs_one]
  refine WP.mono (drawCut_ok h₁.st.ws hk h₁.top) fun s₂ ⟨hx₂, f₂, k₂⟩ => ?_
  rw [hx₁, hcut] at hx₂
  have h₂ : MrFix p w N mb K s₂ := h₁.of_frm hEZ f₂ (by kmut)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact sX)
    k₂ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
  have hI₂ : word s₂.mem p.B (8 * fIdx) = BitVec.ofNat 64 i := by
    rw [f₂.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [fIdx]; omega_arith)]; exact hI₁
  have hu₂ : word s₂.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u + mLen mb) := by
    rw [f₂.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_arith)]; exact hu₁
  -- The range.
  obtain ⟨bm₂, hc₂⟩ := h₂.ctx
  refine WP.mono (drawRange_ok h₂.st.ws hx₂) fun s₃ ⟨h9₃, hm₃, k₃⟩ => ?_
  rw [hc₂.n] at h9₃
  have h₃ : MrFix p w N mb K s₃ := h₂.of_frm (rs := []) hEZ (by rw [hm₃]; exact Frm.refl _ _ _) (by simp) (by simp)
    (by simp) k₃ (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp)
  have hwa : wA mb p.r u = Spec.Rsa.os2ip ((p.r.drop u).take (mLen mb)) % 2 ^ mb := rfl
  rw [← hwa] at h9₃ hx₂
  have hacc : ∀ a, (decide (2 ≤ a) && decide (a + (1 - a % 2) < N)) = decide (2 ≤ a ∧ a < N - 1) := fun a => by
    rw [← Bool.decide_and]; exact decide_eq_decide.mpr (and_congr Iff.rfl (or1_lt_iff d.odd))
  rw [hacc] at h9₃
  have hU256 : 8 * kUsed + 8 ≤ p.Z := by simp only [kUsed, sFn]; have := hws.h256; omega_arith
  have hS₃ : InScr p.B p.Z s.mem s₃.mem := by
    rw [hm₃]
    refine (InScr.of_frm f₁ fun r hr => ?_).trans (InScr.of_frm f₂ fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sX
      · exact hU256
    · rw [List.mem_singleton.mp hr]; exact sX
  exact ⟨h₃, by rw [hm₃]; exact hu₂, h9₃, by rw [hm₃]; exact hx₂, by rw [hm₃]; exact hI₂, hS₃,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- A draw. -/
theorem draw_ok (M : Mont) (R : Kernel) {p : PP} {w N mb K i u : Nat} {s : State} (d : MrDims p w N mb K)
    (h : MrFix p w N mb K s) (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u)
    (hI : word s.mem p.B (8 * fIdx) = BitVec.ofNat 64 i) (hi : i < 2 ^ 62) (hroom : u + mLen mb ≤ p.r.length) :
    WP isa (seqs (draw M.mm R.run)) s fun t => MrFix p w N mb K t ∧
      word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u + mLen mb) ∧
      word t.mem p.B (8 * kStat) = BitVec.ofNat 64 (dStat N K i (wA mb p.r u)) ∧
      word t.mem p.B (8 * fIdx) = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) ∧ InScr p.B p.Z s.mem t.mem ∧
      Keep mmRegs s t := by
  have hEZ := d.eZ
  have hZ := h.st.ws.hZ
  have hw : w = mW mb := d.hw
  have hmb1 := d.mb1
  have hmb2 := d.mb2
  have hw8 : 8 ≤ w := by rw [hw]; simp only [mW]; omega_arith
  have hw128 : w ≤ 128 := by rw [hw]; simp only [mW]; omega_arith
  have hle : ∀ r ∈ rdRanges w, r.1 + r.2 ≤ p.Z := fun r hr => by
    have := rdRanges_lt w r hr; omega_using [this, hEZ]
  rw [draw_eq]
  refine wp_seqs_append (by simp [drawHead, draw]) (by simp) ?_
  refine WP.mono (drawHead_ok d h hU hI hroom) fun s₃ hd => ?_
  rw [seqs_one]
  have h₃ := hd.fix
  have hu₂ := hd.used
  have h9₃ := hd.x9
  have hx₃ := hd.ax
  have hI₃ := hd.idx
  have hS₃ := hd.isc
  have k₁₃ := hd.keep
  generalize wA mb p.r u = a at h9₃ hx₃ ⊢
  have hs₃ := h₃.st.ws.scr
  have h0₃ : s₃.gpr .x0 = p.B := h₃.st.ws.x0
  refine WP.ite (!decide (2 ≤ a ∧ a < N - 1)) (by rw [eval_zero, h9₃]; cases decide (2 ≤ a ∧ a < N - 1) <;> decide)
    (fun hb => ?_) (fun hb => ?_)
  · -- Rejected.
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₃.mem.writeW (off p.B (8 * kStat)) (BitVec.ofNat 64 4)) (by
      have h256 := h₃.st.ws.h256
      brun [h0₃, hdr_enc (show kStat < 32 by decide), hs₃.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega_arith)]
      rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
    have ft : Frm p.B [(8 * kStat, 8)] s₃.mem t.mem := by
      rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
    refine ⟨h₃.of_frm hEZ ft (by kmut) (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [kStat, sFn]; have := h₃.st.ws.h256; omega_arith)
      k (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
      (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl), ?_, ?_, ?_,
      hS₃.trans (InScr.of_frm ft fun r hr => by
        rw [List.mem_singleton.mp hr]; simp only [kStat, sFn]; have := h₃.st.ws.h256; omega_arith),
      (k₁₃.trans k).mono (by decide)⟩
    · rw [ft.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_arith)]; exact hu₂
    · rw [hm, word_writeW_self]; simp only [dStat, hb, ↓reduceIte]
    · rw [ft.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [fIdx]; omega_arith), hI₃]
      have hnot : ¬(2 ≤ a ∧ a < N - 1 ∧ Spec.Ffdh.mrRound N a = true) := fun h' => hb ⟨h'.1, h'.2.1⟩
      simp only [dIdx, hnot, ↓reduceIte]
  · -- The round.
    simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    obtain ⟨bm₃, hc₃⟩ := h₃.ctx
    have hn3 := d.n3
    have hw4 : 4 ≤ w := by omega_arith
    have haN : a < N := by omega_arith
    refine WP.mono (round_ok (a := a) (i := i) (K := K) M R hw4 hw128 hEZ hc₃ h₃.ex h₃.r2 d.odd d.n3 hx₃
      haN hI₃ h₃.chk hi d.k) fun t ⟨⟨bm', hct⟩, het, hst, hix, ft, k⟩ => ?_
    rw [mr_round_eq a d.n3 d.odd] at hst hix
    have hn' := hct.ws.scr.nowrap
    have hr2 : wv t.mem p.B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
      have := VG.Proof.Rsa.slot_lt (w := w) (show aR2 < 16 by decide)
      rw [ft.wv_eq (fun r hr => by have := rdRanges_arr w (j := aR2) (by decide) r hr; omega_arith)
        (by omega_using [hn', hZ, this])]
      exact h₃.r2
    have hw' : ∀ {j : Nat}, j ∈ [0, 2, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27] →
        word t.mem p.B (8 * j) = word s₃.mem p.B (8 * j) := fun hj =>
      ft.word_eq (rdRanges_hdr w hj) (by
        have h256 := hct.ws.h256
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        omega_using [hj, h256, hn'])
    refine ⟨⟨h₃.st.step hct.ws ft (rdRanges_pmut w) hle k, ⟨bm', hct⟩, het, hr2,
      (hw' (j := kLen) (by decide)).trans h₃.len, (hw' (j := fTop) (by decide)).trans h₃.top,
      (hw' (j := fChecks) (by decide)).trans h₃.chk, (hw' (j := Public.sMask) (by decide)).trans h₃.msk⟩, ?_, ?_, ?_,
      hS₃.trans (InScr.of_frm ft hle), (k₁₃.trans k).mono (by decide)⟩
    · rw [hw' (j := kUsed) (by decide)]; exact hu₂
    · rw [hst]; simp only [dStat, hb, and_self, ↓reduceIte]
    · rw [hix]; simp only [dIdx, hb, true_and]

end VG.Proof.Ffdh.AArch64.ParameterCandidate
