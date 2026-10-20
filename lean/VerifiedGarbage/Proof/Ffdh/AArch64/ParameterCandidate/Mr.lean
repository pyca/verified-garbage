module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MrDraw
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# An FFDH parameter candidate on AArch64: Miller–Rabin

`millerRabin_ok`: the loop of draws (`draw_ok`) is `checkWitnesses` for the
`K` checks of `N` from the tape's offset `u`: `kStat` 0 when the tape runs
out, else 1 or 2 for the result, with `kUsed` the octets read.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses drawWitness_eq)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-! ## The witnesses, one draw at a time -/

theorem cw_short {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : r.length < u + mLen mb) : checkWitnesses N (n + 1) (r.drop u) = none := by
  have hw : Spec.Ffdh.witnessOctets N = mLen mb := by simp only [Spec.Ffdh.witnessOctets, hbl]
  have hd : Spec.Ffdh.drawWitness N (r.drop u) = none := by
    rw [drawWitness_eq (by rw [hw]; simp only [mLen]; omega_using [hm]), hw]
    have : ¬(mLen mb ≤ (r.drop u).length) := by rw [List.length_drop]; simp only [mLen] at h ⊢; omega
    simp only [this, ↓reduceIte]
  simp only [checkWitnesses, hd, Option.bind_eq_bind, Option.bind_none]

theorem cw_step {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : u + mLen mb ≤ r.length) :
    checkWitnesses N (n + 1) (r.drop u) =
      if 2 ≤ wA mb r u ∧ wA mb r u < N - 1 then
        (if Spec.Ffdh.mrRound N (wA mb r u) then checkWitnesses N n (r.drop (u + mLen mb))
          else some (false, r.drop (u + mLen mb)))
      else checkWitnesses N (n + 1) (r.drop (u + mLen mb)) := by
  have hw : Spec.Ffdh.witnessOctets N = mLen mb := by simp only [Spec.Ffdh.witnessOctets, hbl]
  have hl : mLen mb ≤ (r.drop u).length := by rw [List.length_drop]; simp only [mLen] at h ⊢; omega
  have hd := drawWitness_eq (w := N) (by rw [hw]; simp only [mLen]; omega_using [hm]) (r.drop u)
  rw [hw, hbl] at hd
  simp only [hl, ↓reduceIte, List.drop_drop] at hd
  have ha : Spec.Rsa.os2ip ((r.drop u).take (mLen mb)) % 2 ^ mb = wA mb r u := rfl
  rw [ha] at hd
  by_cases hr : 2 ≤ wA mb r u ∧ wA mb r u < N - 1
  · simp only [hr, and_self, ↓reduceIte] at hd ⊢
    simp only [checkWitnesses, hd, Option.bind_eq_bind, Option.bind_some]
  · simp only [hr, ↓reduceIte] at hd ⊢
    simp only [checkWitnesses, hd, Option.bind_eq_bind]

/-! ## The loop -/

theorem MrFix.same {p : PP} {w N mb K : Nat} {s t : State} (h : MrFix p w N mb K s) (hEZ : slot w aE + 8 * (w + 2) ≤ p.Z)
    (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : MrFix p w N mb K t :=
  h.of_frm (rs := []) hEZ (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) (by simp) k hr (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

/-- At the head of the loop: `i` witnesses passed, `u` octets read. -/
structure MrSt (p : PP) (w N mb K : Nat) (s₀ : State) (res : Option (Bool × List Byte)) (i u : Nat) (s : State) :
    Prop where
  fix : MrFix p w N mb K s
  used : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u
  idx : word s.mem p.B (8 * fIdx) = BitVec.ofNat 64 i
  ul : u ≤ p.r.length
  ik : i < K
  rest : checkWitnesses N (K - i) (p.r.drop u) = res
  isc : InScr p.B p.Z s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- After the loop. -/
abbrev MrEnd (p : PP) (w N mb K : Nat) (s₀ : State) (res : Option (Bool × List Byte)) (s : State) : Prop :=
  MrFix p w N mb K s ∧ (res = none → word s.mem p.B (8 * kStat) = BitVec.ofNat 64 0) ∧
  (∀ b rest, res = some (b, rest) → word s.mem p.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
    ∃ u, u ≤ p.r.length ∧ rest = p.r.drop u ∧ word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u) ∧
  InScr p.B p.Z s₀.mem s.mem ∧ Keep mmRegs s₀ s

/-- The iterations of the loop from `i` passing witnesses and `u` octets
read, with fuel for `f` of them. -/
def mrIters (N K mb : Nat) (r : List Byte) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | f + 1, i, u =>
    if r.length < u + mLen mb then 1
    else if 2 ≤ wA mb r u ∧ wA mb r u < N - 1 then
      (if Spec.Ffdh.mrRound N (wA mb r u) = true ∧ i + 1 < K then mrIters N K mb r f (i + 1) (u + mLen mb) + 1
        else 1)
    else mrIters N K mb r f i (u + mLen mb) + 1

/-- One iteration. -/
theorem mrIter_ok (M : Mont) (R : Kernel) {p : PP} {w N mb K : Nat} (d : MrDims p w N mb K)
    {s₀ : State} {res : Option (Bool × List Byte)} {i u : Nat} {s : State} (h : MrSt p w N mb K s₀ res i u s) :
    WP isa (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (draw M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) s fun t =>
      (isa.eval (.zero .x .x3) t = some false ∧ MrEnd p w N mb K s₀ res t ∧
        ∀ f, mrIters N K mb p.r (f + 1) i u = 1) ∨
      (isa.eval (.zero .x .x3) t = some true ∧ ∃ i', MrSt p w N mb K s₀ res i' (u + mLen mb) t ∧
        ∀ f, mrIters N K mb p.r (f + 1) i u = mrIters N K mb p.r f i' (u + mLen mb) + 1) := by
  have hEZ := d.eZ
  have hmb1 := d.mb1
  have hmb2 := d.mb2
  have hK := d.k
  have hik := h.ik
  have hul := h.ul
  have hl1 : 1 ≤ mLen mb := by simp only [mLen]; omega
  have hws := h.fix.st.ws
  have hrl := h.fix.st.dims.rl
  obtain ⟨n, hn⟩ : ∃ n, K - i = n + 1 := ⟨K - i - 1, by omega⟩
  have hres := h.rest
  rw [hn] at hres
  simp only [seqs]
  refine WP.seq (WP.mono (roomHead_ok hws (len := mLen mb) (by simp only [mLen]; omega) hrl hul h.fix.len
    h.fix.st.args.rlen h.used) fun s₁ ⟨hz₁, hm₁, k₁⟩ => ?_)
  have h₁ := h.fix.same hEZ hm₁ k₁ (by decide)
  refine WP.seq (WP.ite (decide (p.r.length < u + mLen mb)) hz₁ (fun hb => ?_) (fun hb => ?_))
  · -- Out of octets.
    simp only [decide_eq_true_eq] at hb
    have hs₁ := h₁.st.ws.scr
    have h256 := h₁.st.ws.h256
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₁.mem.writeW (off p.B (8 * kStat)) (BitVec.ofNat 64 0)) (by
      brun [h₁.st.ws.x0, hdr_enc (show kStat < 32 by decide),
        hs₁.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega)]
      rfl) (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨hm₂, k₂⟩ => ?_
    have ft : Frm p.B [(8 * kStat, 8)] s₁.mem s₂.mem := by
      rw [hm₂]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
    have h₂ : MrFix p w N mb K s₂ := h₁.of_frm hEZ ft (by kmut)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [kStat, sFn]; omega)
      k₂ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
      (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    refine WP.mono (statCmp_ok h₂.st.ws (v := 0) (by decide) (by rw [hm₂, word_writeW_self]))
      fun t ⟨hz, hm, k⟩ => Or.inl ⟨hz.trans rfl, ⟨h₂.same hEZ hm k (by decide), ?_⟩,
        fun f => by simp only [mrIters, hb, ↓reduceIte]⟩
    have hnone : res = none := hres.symm.trans (cw_short d.bl (by omega) hb)
    refine ⟨fun _ => by rw [hm, hm₂, word_writeW_self], fun b rest h' => ?_, ?_,
      (((h.keep.trans k₁).trans k₂).trans k).mono (by decide)⟩
    · rw [hnone] at h'; cases h'
    · rw [hm]
      exact (h.isc.trans (by rw [hm₁]; exact InScr.refl _ _ _)).trans (InScr.of_frm ft fun r hr => by
        rw [List.mem_singleton.mp hr]; simp only [kStat, sFn]; omega)
  · -- A draw.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
    have hnb : ¬ p.r.length < u + mLen mb := by omega
    refine WP.mono (draw_ok (i := i) (u := u) M R d h₁ (by rw [hm₁]; exact h.used) (by rw [hm₁]; exact h.idx) (by omega) hb)
      fun s₂ ⟨h₂, hu₂, hst₂, hix₂, hi₂, k₂⟩ => ?_
    have hstep := cw_step (n := n) d.bl (by omega) hb
    rw [hres] at hstep
    have hit0 : ∀ f, mrIters N K mb p.r (f + 1) i u = if 2 ≤ wA mb p.r u ∧ wA mb p.r u < N - 1 then
        (if Spec.Ffdh.mrRound N (wA mb p.r u) = true ∧ i + 1 < K then mrIters N K mb p.r f (i + 1) (u + mLen mb) + 1
          else 1)
        else mrIters N K mb p.r f i (u + mLen mb) + 1 := fun f => by simp only [mrIters, hnb, ↓reduceIte]
    generalize wA mb p.r u = a at hstep hst₂ hix₂ hit0
    have hv : dStat N K i a < 2 ^ 63 := by unfold dStat; split <;> (try split) <;> (try split) <;> decide
    refine WP.mono (statCmp_ok h₂.st.ws hv hst₂) fun t ⟨hz, hm, k⟩ => ?_
    have ht := h₂.same hEZ hm k (by decide)
    have hut : word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u + mLen mb) := by rw [hm]; exact hu₂
    have hit : word t.mem p.B (8 * fIdx) = BitVec.ofNat 64 (dIdx N i a) := by rw [hm]; exact hix₂
    have hst : word t.mem p.B (8 * kStat) = BitVec.ofNat 64 (dStat N K i a) := by rw [hm]; exact hst₂
    have hisc : InScr p.B p.Z s₀.mem t.mem := by
      rw [hm]; exact (h.isc.trans (by rw [hm₁]; exact InScr.refl _ _ _)).trans hi₂
    have hkp : Keep mmRegs s₀ t := (((h.keep.trans k₁).trans k₂).trans k).mono (by decide)
    by_cases hr : 2 ≤ a ∧ a < N - 1
    · by_cases hpass : Spec.Ffdh.mrRound N a = true
      · by_cases hlast : i + 1 < K
        · -- On to the next witness.
          have h4 : dStat N K i a = 4 := by simp only [dStat, hr, hpass, hlast, and_self, ↓reduceIte]
          refine Or.inr ⟨hz.trans (by rw [h4]; rfl), i + 1, ⟨ht, hut, ?_, hb, hlast, ?_, hisc, hkp⟩,
            fun f => by rw [hit0]; simp only [hr, hpass, hlast, and_self, ↓reduceIte]⟩
          · rw [hit]; simp only [dIdx, hr, hpass, and_self, ↓reduceIte]
          · simp only [hr, hpass, and_self, ↓reduceIte] at hstep
            rw [show K - (i + 1) = n by omega]; exact hstep.symm
        · -- The last check passed.
          have h1 : dStat N K i a = 1 := by simp only [dStat, hr, hpass, hlast, and_self, ↓reduceIte]
          have hn0 : n = 0 := by omega
          subst hn0
          simp only [hr, hpass, and_self, ↓reduceIte, checkWitnesses] at hstep
          refine Or.inl ⟨hz.trans (by rw [h1]; rfl), ⟨ht, (fun h0 => by rw [h0] at hstep; cases hstep),
            fun b rest h' => ?_, hisc, hkp⟩, fun f => by rw [hit0]; simp only [hr, hpass, hlast, and_false, and_self, ↓reduceIte]⟩
          rw [h'] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          exact ⟨by rw [hst, h1]; rfl, u + mLen mb, hb, rfl, hut⟩
      · -- A failing witness.
        have hpf : Spec.Ffdh.mrRound N a = false := Bool.eq_false_iff.mpr hpass
        have h2 : dStat N K i a = 2 := by simp only [dStat, hr, hpf, and_self, Bool.false_eq_true, ↓reduceIte]
        simp only [hr, hpf, and_self, Bool.false_eq_true, ↓reduceIte] at hstep
        refine Or.inl ⟨hz.trans (by rw [h2]; rfl), ⟨ht, (fun h0 => by rw [h0] at hstep; cases hstep),
          fun b rest h' => ?_, hisc, hkp⟩, fun f => by rw [hit0]; simp only [hr, hpf, Bool.false_eq_true, false_and,
            and_self, ↓reduceIte]⟩
        rw [h'] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        exact ⟨by rw [hst, h2]; rfl, u + mLen mb, hb, rfl, hut⟩
    · -- A rejected draw.
      have h4 : dStat N K i a = 4 := by simp only [dStat, hr, ↓reduceIte]
      have hnot : ¬(2 ≤ a ∧ a < N - 1 ∧ Spec.Ffdh.mrRound N a = true) := fun h' => hr ⟨h'.1, h'.2.1⟩
      simp only [hr, ↓reduceIte] at hstep
      refine Or.inr ⟨hz.trans (by rw [h4]; rfl), i, ⟨ht, hut, ?_, hb, hik, ?_, hisc, hkp⟩,
        fun f => by rw [hit0]; simp only [hr, ↓reduceIte]⟩
      · rw [hit]; simp only [dIdx, hnot, ↓reduceIte]
      · rw [hn]; exact hstep.symm

/-- `millerRabin`: the `K` checks of `N` from offset `u`. -/
theorem millerRabin_ok (M : Mont) (R : Kernel) {p : PP} {w N mb K : Nat} (d : MrDims p w N mb K) {u : Nat}
    {s : State} (h : MrFix p w N mb K s) (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u)
    (hul : u ≤ p.r.length) (hK1 : 1 ≤ K) :
    WP isa (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run)) s
      (MrEnd p w N mb K s (checkWitnesses N K (p.r.drop u))) := by
  have hEZ := d.eZ
  have hs := h.st.ws.scr
  have h256 := h.st.ws.h256
  unfold VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off p.B (8 * fIdx)) (BitVec.ofNat 64 0))
    (by
      brun [h.st.ws.x0, hdr_enc (show fIdx < 32 by decide), hs.st (d := 8 * fIdx) (by simp only [fIdx]; omega)]
      rfl) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨hm₁, k₁⟩ => ?_)
  have ft : Frm p.B [(8 * fIdx, 8)] s.mem s₁.mem := by
    rw [hm₁]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  have h₁ : MrFix p w N mb K s₁ := h.of_frm hEZ ft (by kmut)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
    (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fIdx]; omega)
    k₁ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
  have hst : MrSt p w N mb K s (checkWitnesses N K (p.r.drop u)) 0 u s₁ :=
    ⟨h₁, by rw [ft.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega)]; exact hU,
      by rw [hm₁, word_writeW_self], hul, by omega, by rw [Nat.sub_zero],
      InScr.of_frm ft fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fIdx]; omega, k₁.mono (by decide)⟩
  exact WP.loop (fun n t => ∃ i u', n = p.r.length - u' ∧ MrSt p w N mb K s (checkWitnesses N K (p.r.drop u)) i u' t)
    (fun n t ⟨i, u', hn, hI⟩ => WP.mono (mrIter_ok M R d hI) fun t' h' => h'.imp (fun h'' => ⟨h''.1, h''.2.1⟩)
      fun ⟨he, i', hI', _⟩ => ⟨he, p.r.length - (u' + mLen mb), by
        have := hI'.ul; have := d.mb1; simp only [mLen] at *; omega, i', u' + mLen mb, rfl, hI'⟩)
    (p.r.length - u) s₁ ⟨0, u, rfl, hst⟩

end VG.Proof.Ffdh.AArch64.ParameterCandidate
