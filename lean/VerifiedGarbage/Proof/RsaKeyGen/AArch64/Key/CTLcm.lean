import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTUnits
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Lcm
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front

/-!
# An RSA key from its primes on AArch64: constant time, `lcm(p − 1, q − 1)`

The product (`mulTo_ct0`, `phi_ct`), the copies of `p − 1` and `q − 1`
(`zc_ct`, which leave their top words zero, as the halving and `inverse`
need of `u`), the halving's loop (`twos_ct`, by `two_loop` over the steps,
whose count `x6` correctness ties to the public `W`), `gcdUV` (`gcdUV_ct`)
and the division; the facts after `lcmPart` from `lcm_k` (`lcmPart_ct`, to
`KG LF`).

`halfIf`'s two halves each reload `w` and the stride: the first is checked
from `KG`, the second from `KS` after the first (`shrHalf_k`), and the
facts after both come from `halfIf_k`.
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## The product -/

theorem mulTo_eq (o a b : Nat) : seqs (mulTo o a b) = .seq (zeroA o) (.seq (.block (ws ++ (base b .x9 ++
    (base o .x8 ++ (base a .x16 ++ ([mov .x11 .x16, .lsr .x .x12 .x12 1, mov .x13 .x12, movi .x7 0] :
      List Instr)))))) VG.Impl.Rsa.AArch64.Crt.mulRows) := by
  simp only [mulTo, seqs, List.append_assoc]

/-- `[o] := [a] [b]`, as `phi` and `nPart` compute it, with no
postcondition. -/
theorem mulTo_ct0 {F : KIn → State → Prop} {o a b : Nat} (ho : o < 16) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base o .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base b .x9 ++ (base o .x8 ++ (base a .x16 ++
      ([mov .x11 .x16, .lsr .x .x12 .x12 1, mov .x13 .x12, movi .x7 0] : List Instr)))))
      VG.Impl.Rsa.AArch64.Crt.mulRows) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (mulTo o a b)) fun _ _ => True := by
  rw [mulTo_eq]
  exact kg_then (G := NF) (zeroA_ct0 ht₁) (fun I _ s h _ _ => WP.mono (zeroA_k h ho) fun _ ⟨ht, _⟩ =>
    ⟨ht, trivial⟩) (kg_ws0 ht₂)

theorem lt_pow_half {I : KIn} {x : Nat} (hx : x < 2 ^ (64 * (I.pl / 8))) (y : Nat) :
    x - y < 2 ^ (64 * (I.pl / 8)) :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) hx

/-- `phi`, from the front, with word `W` of `φ` zero. -/
theorem phi_ct : RelCT isa (Two (KG PF)) (seqs phi) (Two (KG (TopZ aL))) :=
  kg_ct (mulTo_ct0 (by decide) (by taint_decide) (by taint_decide)) fun I _ s h L ⟨_, _, hPm, hQm, _⟩ => by
    have hPw := lt_pow_half L.P_lt 1
    have hQw := lt_pow_half L.Q_lt 1
    have hW := L.W
    refine WP.mono (phi_k h hW hPm hQm hPw hQw) fun t ⟨ht, _, v⟩ => ⟨ht, lcm_topZero ?_⟩
    rw [v, hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hPw (by omega) (Nat.two_pow_pos _)

/-! ## The halving -/

/-- The registers `halfIf` changes. -/
abbrev hfRegs : List Reg := [.x3, .x4, .x11, .x12, .x14, .x16, .x17]

theorem halfIf_eq (j : Nat) : seqs (halfIf j) = .seq (.block (ws ++ (([mov .x14 .x12] : List Instr) ++
    (base j .x16 ++ base aT .x17)))) (.seq (countLoop .x14 shrBody) (.seq (.block (ws ++
      (([mov .x14 .x12] : List Instr) ++ (base aT .x16 ++ base j .x17)))) VG.Impl.Rsa.AArch64.Crt.selLoop)) := by
  simp only [halfIf, seqs, List.append_assoc]

/-- `halfIf`'s first half: `[aT] := [j] / 2`. -/
theorem shrHalf_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) (hjT : j ≠ aT) :
    WP isa (.seq (.block (ws ++ (([mov .x14 .x12] : List Instr) ++ (base j .x16 ++ base aT .x17))))
      (countLoop .x14 shrBody)) s (KS I s₀) := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have sT := h.ws.sl (j := aT) (by decide)
  have sp := slot_sep (w := I.W) hjT
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  rw [← List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsMov_ok h.ws) fun s₁ ⟨⟨_, h11, h14, m₁, _⟩, k₁⟩ =>
    WP.mono (base2_ok j aT .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11)
      fun s₂ ⟨⟨h16, h17, m₂, _⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.mono (shr_ok (h.ws.scr.congr k12.wr) h16 h17 ((k₂.gpr .x14 (by decide)).trans h14) hw1
    (by omega) (by omega) (by omega) (by omega)) fun s₃ ⟨_, _, o₃, k₃⟩ => ?_
  rw [m₂, m₁] at o₃
  have f₃ := KF.arr1 (B := I.B) (W := I.W) (j := aT) o₃ (Nat.le_refl _) (by omega)
  exact h.step f₃ (all_mut_arr (by decide)) (k12.trans k₃)

theorem halfIf_ct0 {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base j .x16 ++ base aT .x17))) (countLoop .x14 shrBody)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base aT .x16 ++ base j .x17))) VG.Impl.Rsa.AArch64.Crt.selLoop) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (halfIf j)) fun _ _ => True := by
  rw [halfIf_eq]
  exact RelCT.assoc (kg_then (G := NF) (kg_ws0 ht₁) (fun I _ s h _ _ => WP.mono (shrHalf_k h hj hjT) fun t ht =>
    ⟨ht, trivial⟩) (kg_ws0 ht₂))

/-- `halfIf j`, from a mask in `x15` and word `W` of `[j]` zero, for facts
`F` that its changes keep. -/
theorem halfIf_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    (h0 : ∀ I s, F I s → X15M I s ∧ TopZ j I s)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → KF I.B I.W [.arr j, .arr aT] s.mem t.mem → Keep hfRegs s t →
      TopZ j I t → F I t)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base j .x16 ++ base aT .x17))) (countLoop .x14 shrBody)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base aT .x16 ++ base j .x17))) VG.Impl.Rsa.AArch64.Crt.selLoop) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (halfIf j)) (Two (KG F)) :=
  kg_ct (halfIf_ct0 hj hjT ht₁ ht₂) fun I _ s h _ hf => by
    obtain ⟨⟨_, h15⟩, t0⟩ := h0 I s hf
    exact WP.mono (halfIf_k h hj hjT h15 t0) fun t ⟨ht, f, _, tj, k⟩ => ⟨ht, hFG I s t h.hZ hf f k tj⟩

/-- Words `W` of `u`, `v` and `φ` zero: what a step of the halving needs. -/
abbrev TwB : KIn → State → Prop := fun I t => TopZ aU I t ∧ TopZ aV I t ∧ TopZ aL I t

/-- `TwB` and a mask in `x15`: between the parts of a step. -/
abbrev TwM : KIn → State → Prop := fun I t => TwB I t ∧ X15M I t

theorem twb_mem {I : KIn} {s t : State} (h : TwB I s) (hm : t.mem = s.mem) : TwB I t := by
  obtain ⟨a, b, c⟩ := h
  have e : ∀ j, atop I t.mem j = atop I s.mem j := fun j => by rw [hm]
  exact ⟨(e aU).trans a, (e aV).trans b, (e aL).trans c⟩

/-- `TwM` after `halfIf j`. -/
theorem twm_step {j : Nat} (hj : j < 16) :
    ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → TwM I s → KF I.B I.W [.arr j, .arr aT] s.mem t.mem → Keep hfRegs s t →
      TopZ j I t → TwM I t := fun I s t hZ ⟨⟨tU, tV, tL⟩, c, h15⟩ f k tj => by
  have hok : [Rc.arr j, Rc.arr aT].all Rc.ok = true := by
    simp only [List.all_cons, List.all_nil, Rc.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hj, by decide⟩
  have top : ∀ i, i < 16 → i ≠ aT → atop I s.mem i = 0 → atop I t.mem i = 0 := fun i hi hiT h0 =>
    if e : i = j then by rw [e]; exact tj else (f.at hok hi (by simp [e, hiT]) hZ).trans h0
  exact ⟨⟨top aU (by decide) (by decide) tU, top aV (by decide) (by decide) tV, top aL (by decide) (by decide) tL⟩,
    c, (k.gpr .x15 (by decide)).trans h15⟩

theorem twoStep_eq : twoStep = seqs (([.block (ws ++ (base aU .x16 ++ (base aV .x17 ++ ([ld .x3 .x16, ld .x4 .x17,
    .logic .orr .x .x3 .x3 .x4, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr))))] :
    List (Prog isa)) ++ (halfIf aU ++ (halfIf aV ++ (halfIf aL ++
      ([.block [.subImm .x .x6 .x6 1]] : List (Prog isa)))))) := by
  simp only [twoStep, List.append_assoc]

/-- A step of the halving, with no postcondition. -/
theorem twoStep_ct0 : RelCT isa (Two (KG TwB)) twoStep fun _ _ => True := by
  rw [twoStep_eq]
  refine rs_app (R := Two (KG TwM)) (by simp) (by simp [halfIf])
    (show RelCT isa _ (seqs [.block _]) _ from kg_wsb (by taint_decide) fun I _ s h _ hf =>
      WP.mono (twoMask_k h) fun t ⟨⟨hm, h15⟩, k⟩ => ⟨h.regs hm k, twb_mem hf hm, _, h15⟩) ?_
  refine rs_app (by simp [halfIf]) (by simp [halfIf]) (halfIf_ct (by decide) (by decide)
    (fun _ _ ⟨⟨t, _⟩, c⟩ => ⟨c, t⟩) (twm_step (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [halfIf]) (by simp [halfIf]) (halfIf_ct (by decide) (by decide)
    (fun _ _ ⟨⟨_, t, _⟩, c⟩ => ⟨c, t⟩) (twm_step (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [halfIf]) (by simp) (halfIf_ct (by decide) (by decide)
    (fun _ _ ⟨⟨_, _, t⟩, c⟩ => ⟨c, t⟩) (twm_step (by decide)) (by taint_decide) (by taint_decide)) ?_
  exact (two_taint [.x0] (pins_kg TwM) (by taint_decide) :
    RelCT isa _ (.block [.subImm .x .x6 .x6 1]) fun _ _ => True)

/-- Before step `j` of the halving: `TwB`, and `64 W − j` steps left in `x6`. -/
abbrev TwX (j : Nat) : KIn → State → Prop := fun I t => TwB I t ∧ t.gpr .x6 = BitVec.ofNat 64 (64 * I.W - j)

theorem twos_eq : seqs twos = .seq (.block (ws ++ ([.lsl .x .x6 .x12 6] : List Instr)))
    (.loop twoStep (.nonzero .x .x6)) := rfl

theorem ofNat_sub_one_k {p : Nat} (hp : 1 ≤ p) (hp' : p < 2 ^ 64) :
    BitVec.ofNat 64 p - BitVec.ofNat 64 1 = BitVec.ofNat 64 (p - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp',
    Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show p - 1 < 2 ^ 64 by omega)]
  omega

/-- The halving's loop: `64 W` steps, a public count. -/
theorem twosLoop_ct : RelCT isa (Two (KG (TwX 0))) (.loop twoStep (.nonzero .x .x6)) (Two (KG (TopZ aU))) := by
  refine (two_loop (Φ := fun p j s => KG (TwX j) p s) (Ψ := KG (TopZ aU)) (fun p : KP => 64 * p.q.W)
    (two_map Prod.fst (fun _ _ h => h.2.imp fun _ h => h.1) twoStep_ct0) ?_).mono ?_ fun _ _ h => h
  · intro p j s hj ⟨I, s₀, he, hst, hk, L, O, ⟨tU, tV, tL⟩, h6⟩
    have hW := KIn.pub_W he
    have hw2 := hk.ws.w2
    refine WP.mono (twoStep_k hk tU tV tL) fun t ⟨⟨ht, _, tU', tV', tL'⟩, h6', _⟩ => ?_
    have e6 : t.gpr .x6 = BitVec.ofNat 64 (64 * I.W - (j + 1)) := by
      rw [h6', h6, ofNat_sub_one_k (by omega) (by omega), Nat.sub_sub]
    refine ⟨?_, fun _ => ⟨I, s₀, he, hst, ht, L, O, ⟨tU', tV', tL'⟩, e6⟩,
      fun _ => ⟨I, s₀, he, hst, ht, L, O, tU'⟩⟩
    rw [eval_nonzero, e6, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · intro s₁ s₂ h
    refine two_mono (fun p s h => ⟨?_, h⟩) h
    obtain ⟨I, _, he, -, hk, -⟩ := h
    have := hk.ws.w1
    rw [← KIn.pub_W he]; omega

/-- The halving: `x6 := 64 W`, then the loop. -/
theorem twos_ct : RelCT isa (Two (KG TwB)) (seqs twos) (Two (KG (TopZ aU))) := by
  rw [twos_eq]
  exact RelCT.seq (kg_wsb (G := TwX 0) (by taint_decide) fun I _ s h _ hf =>
    WP.mono (twosInit_k h) fun t ⟨⟨h6, hm⟩, k⟩ => ⟨h.regs hm k, twb_mem hf hm, by rw [h6, Nat.sub_zero]⟩)
    twosLoop_ct

/-! ## `gcd(u, v)` -/

/-- `x15`'s mask into `kOk`. -/
theorem stOk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {c : Bool} (h15 : s.gpr .x15 = mask c) :
    WP isa (.block [sth .x15 kOk]) s fun t => KS I s₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask c ∧ Keep [] s t := by
  have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk)) (mask c))
    (by brun [h.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15]) rfl rfl rfl) fun t ⟨hm, k⟩ => ?_
  obtain ⟨ht, f, hw⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k
  exact ⟨ht, f, hw, k⟩

/-- `stOk_k`, for facts `F` that survive it. -/
theorem stOk_ct {F : KIn → State → Prop} (hF : Stab F [.hdr kOk] []) :
    RelCT isa (Two (KG fun I t => F I t ∧ X15M I t)) (.block [sth .x15 kOk])
      (Two (KG fun I t => F I t ∧ KokM I t)) :=
  kg_x0 (by taint_decide) fun I _ s h _ ⟨hf, _, h15⟩ => WP.mono (stOk_k h h15) fun t ⟨ht, f, hw, k⟩ =>
    ⟨ht, hF I s t h.hZ hf f k, _, hw⟩

/-- `ldOk_k`, for facts `F`: `kOk`'s mask into `x15`. -/
theorem ldOk_ct {F : KIn → State → Prop} (hF : ∀ I s t, F I s → t.mem = s.mem → Keep [.x15] s t → F I t) :
    RelCT isa (Two (KG fun I t => F I t ∧ KokM I t)) (.block [ldh .x15 kOk])
      (Two (KG fun I t => (F I t ∧ KokM I t) ∧ X15M I t)) :=
  kg_x0 (by taint_decide) fun I _ s h _ ⟨hf, c, hk⟩ => WP.mono (ldOk_k h hk) fun t ⟨ht, hm, h15, k⟩ =>
    ⟨ht, ⟨hF I s t hf hm k, c, by rw [hm]; exact hk⟩, _, h15⟩

/-- `inverse`'s start from the copy into `[o]` of `[a]`: `x₁ := 1`,
`x₂ := 0`. -/
theorem invStart_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (ho1 : o ≠ aX₁) (ho2 : o ≠ aX₂) (ha1 : a ≠ aX₁) (ha2 : a ≠ aX₂) (hF : Stab F [.arr o, .arr aX₁, .arr aX₂] allR)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs [copyA o a, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂])
      (Two (KG fun I t => F I t ∧ AvEq o a I t ∧ AvIs aX₁ 1 I t ∧ AvIs aX₂ 0 I t)) := by
  have sE : ∀ (cs : List Rc), cs.all Rc.ok = true → .arr o ∉ cs → .arr a ∉ cs → Stab (AvEq o a) cs allR :=
    fun _ hok h1 h2 => stab_aveq _ ho ha hok h1 h2
  have ok1 : [Rc.arr aX₁].all Rc.ok = true := by decide
  have ok2 : [Rc.arr aX₂].all Rc.ok = true := by decide
  simp only [seqs]
  refine RelCT.seq (R := Two (KG fun I t => F I t ∧ AvEq o a I t)) (kg_ct (copyA_ct0 ht) fun I _ s h _ hf =>
    WP.mono (copyA_k h ho ha hoa) fun t ⟨ht, f, v, _, k⟩ =>
      ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)),
        by dsimp only [AvEq]; rw [v, f.av (by simp [Rc.ok, ho]) ha (by simp [hoa.symm]) h.hZ]⟩) ?_
  refine RelCT.seq (zeroAZ_ct (F := fun I t => F I t ∧ AvEq o a I t) (by decide)
    (stab_and (hF.mono (by simp) (by decide)) ((sE [.arr aX₁] ok1 (by simp [ho1]) (by simp [ha1])).sub))
    (by taint_decide)) ?_
  refine RelCT.seq (setOne_ct (G := fun I t => F I t ∧ AvEq o a I t ∧ AvIs aX₁ 1 I t) (by decide)
    (fun I s t hZ _ ⟨hf, he⟩ f k v =>
    ⟨hF I s t hZ hf (f.mono (by simp)) (k.mono (by decide)),
      sE [.arr aX₁] ok1 (by simp [ho1]) (by simp [ha1]) I s t hZ he f (k.mono (by decide)), v⟩) (by taint_decide)) ?_
  exact kg_ct (zeroA_ct0 (by taint_decide)) fun I _ s h _ ⟨hf, he, h1⟩ => WP.mono (zeroA_k h (j := aX₂) (by decide))
    fun t ⟨ht, f, z, _, k⟩ => ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)),
      sE [.arr aX₂] ok2 (by simp [ho2]) (by simp [ha2]) I s t h.hZ he f (k.mono (by decide)),
      stab_av _ (by decide) (by decide) (by decide) I s t h.hZ h1 f k, av_of_full z (Nat.two_pow_pos _)⟩

theorem gcdSwap_eq : evenMaskOf aV ++ (([mov .x14 .x12] : List Instr) ++ (base aU .x16 ++ base aV .x17)) =
    ws ++ (base aV .x16 ++ (([ld .x3 .x16, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] :
      List Instr) ++ (([mov .x14 .x12] : List Instr) ++ (base aU .x16 ++ base aV .x17)))) := by
  simp only [evenMaskOf, List.append_assoc]

theorem gcdUV_eq2 : gcdUV = ([.block (evenMaskOf aV ++ (([mov .x14 .x12] : List Instr) ++ (base aU .x16 ++ base aV .x17))),
    countLoop .x14 cswapBody] : List (Prog isa)) ++ (constA 2 ++ (ltA aV aC ++
    (([.block [sth .x15 kOk]] : List (Prog isa)) ++ (constA 3 ++ (([.block [ldh .x15 kOk]] : List (Prog isa)) ++
    (selC aV ++ (([zeroA aM, copyA aM aV, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂, inverse aU aV aX₁ aX₂ aM aT] :
      List (Prog isa)) ++ (constA 1 ++ (([.block [ldh .x15 kOk]] : List (Prog isa)) ++ selC aV))))))))) := by
  simp only [gcdUV, List.append_assoc]

/-- `gcdUV`, from word `W` of `u` zero. -/
theorem gcdUV_ct : RelCT isa (Two (KG (TopZ aU))) (seqs gcdUV) (Two (KG NF)) := by
  have sT : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .arr aU ∉ cs → Stab (TopZ aU) cs rs :=
    fun _ rs hok hn => stab_top rs (by decide) hok hn
  have sK : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .hdr kOk ∉ cs → Stab KokM cs rs :=
    fun _ rs hok hn => stab_kok rs hok hn
  rw [gcdUV_eq2]
  -- `v` made odd by a swap.
  refine rs_app (R := Two (KG (TopZ aU))) (by simp) (by simp [constA])
    (show RelCT isa _ (seqs [.block _, countLoop .x14 cswapBody]) _ from by
      show RelCT isa _ (.seq (.block _) (countLoop .x14 cswapBody)) _
      rw [gcdSwap_eq]
      exact kg_ws (by taint_decide) fun I _ s h _ hf => by
        rw [← gcdSwap_eq]
        exact WP.mono (gcdSwap_k h) fun t ⟨ht, _, _, _, tt⟩ => ⟨ht, tt.trans hf⟩) ?_
  -- The mask of `v < 2` into `kOk`.
  refine rs_app (by simp [constA]) (by simp [ltA, cmpA]) (constA_ct 2 (by decide)
    (sT [.arr aC] _ (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => TopZ aU I t ∧ X15M I t)) (by simp [ltA, cmpA]) (by simp)
    (ltA_ct (by decide) (by decide) (fun I s t _ hf hm _ h15 => ⟨by dsimp only [TopZ, atop] at hf ⊢; rw [hm]; exact hf,
      _, h15⟩) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block [sth .x15 kOk]]) _ from
    stOk_ct (sT [.hdr kOk] [] (by decide) (by decide))) ?_
  -- `[aV] := 3` for `v < 2`.
  refine rs_app (by simp [constA]) (by simp) (constA_ct 3 (by decide)
    (stab_and (sT [.arr aC] _ (by decide) (by decide)) (sK [.arr aC] _ (by decide) (by decide)))
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [selC]) (show RelCT isa _ (seqs [.block [ldh .x15 kOk]]) _ from
    ldOk_ct (F := TopZ aU) fun I s t hf hm _ => by dsimp only [TopZ, atop] at hf ⊢; rw [hm]; exact hf) ?_
  refine rs_app (by simp [selC]) (by simp) (selC_ct (by decide) (by decide)
    (stab_and (sT [.arr aV] _ (by decide) (by decide)) (sK [.arr aV] _ (by decide) (by decide))) (by taint_decide)) ?_
  -- `inverse` modulo `[aM] = v`.
  refine rs_app (R := Two (KG KokM)) (by simp) (by simp [constA]) ?_ ?_
  · show RelCT isa _ (seqs ([zeroA aM] ++ ([copyA aM aV, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂] ++
      [inverse aU aV aX₁ aX₂ aM aT]))) _
    refine rs_app (by simp) (by simp) (zeroA_ct (by decide)
      (stab_and (sT [.arr aM] _ (by decide) (by decide)) (sK [.arr aM] _ (by decide) (by decide))) (by taint_decide)) ?_
    refine rs_app (by simp) (by simp) (invStart_ct (o := aM) (a := aV) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (stab_and (sT [.arr aM, .arr aX₁, .arr aX₂] _ (by decide) (by decide))
        (sK [.arr aM, .arr aX₁, .arr aX₂] _ (by decide) (by decide))) (by taint_decide)) ?_
    exact (inverse_ct (F := KokM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (sK _ _ (by decide) (by decide))
      (by taint_decide)).mono (fun _ _ h => two_kg (fun _ _ ⟨⟨tU, hk⟩, he, h1, h2⟩ => ⟨hk, tU, he.symm, h1, h2⟩) h)
      fun _ _ h => h
  -- The result 1 for `v < 2`.
  refine rs_app (by simp [constA]) (by simp) (constA_ct 1 (by decide) (sK [.arr aC] _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [selC]) (show RelCT isa _ (seqs [.block [ldh .x15 kOk]]) _ from
    (ldOk_ct (F := NF) fun _ _ _ _ _ _ => trivial).mono (fun _ _ h => two_kg (fun _ _ h => ⟨trivial, h⟩) h)
      fun _ _ h => h) ?_
  exact (selC_ct (F := NF) (by decide) (by decide) (stab_nf _ _) (by taint_decide)).mono
    (fun _ _ h => two_kg (fun _ _ ⟨⟨_, _⟩, c⟩ => ⟨trivial, c⟩) h) fun _ _ h => h

/-! ## The lcm -/

/-- After `lcmPart`: the front's facts, and `L` in `aL`. -/
abbrev LF : KIn → State → Prop := fun I t => PF I t ∧ av I t.mem aL = I.L

/-- `lcmPart` leaks the same in runs with the same public data, and leaves
`LF` (`lcm_k`). -/
theorem lcmPart_ct : RelCT isa (Two (KG PF)) (seqs lcmPart) (Two (KG LF)) := by
  refine kg_ct ?_ fun I _ s h L hf => by
    have hPw := lt_pow_half L.P_lt 1
    have hQw := lt_pow_half L.Q_lt 1
    refine WP.mono (lcm_k h L.W hf.2.2.1 hf.2.2.2.1 hPw hQw) fun t ⟨ht, f, v⟩ => ⟨ht, ?_, v⟩
    exact PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f
  rw [lcmPart_eq]
  refine RelCT.drop (Q := Two (KG NF)) (rs_app (by simp [phi, mulTo]) (by simp) phi_ct ?_)
  refine rs_app (R := Two (KG TwB)) (by simp) (by simp [twos]) ?_ ?_
  · show RelCT isa _ (seqs ([zeroA aU, copyA aU aPm] ++ [zeroA aV, copyA aV aQm])) _
    refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [zeroA aU, copyA aU aPm]) _ from
      zc_ct (by decide) (by decide) (by decide) (stab_top _ (by decide) (by decide) (by decide))
        (by taint_decide) (by taint_decide)) ?_
    exact (show RelCT isa _ (seqs [zeroA aV, copyA aV aQm]) _ from
      zc_ct (by decide) (by decide) (by decide) (stab_and (stab_top _ (by decide) (by decide) (by decide))
        (stab_top _ (by decide) (by decide) (by decide))) (by taint_decide) (by taint_decide)).mono
      (fun _ _ h => h) fun _ _ h => two_kg (fun _ _ ⟨⟨tL, tU⟩, tV⟩ => ⟨tU, tV, tL⟩) h
  refine rs_app (by simp [twos]) (by simp [gcdUV]) twos_ct ?_
  refine rs_app (by simp [gcdUV]) (by simp) gcdUV_ct ?_
  exact divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (stab_nf _ _) (by taint_decide) (by taint_decide)

end VG.Proof.RsaKeyGen.AArch64.Key
