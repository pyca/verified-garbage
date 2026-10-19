module
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGLanes
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGHash
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Gh
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemMask
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# Decryption: the blocks after the last group, hashed between the rounds

`ldGD_ok`: `StitchZH.ldGD last i` loads four powers at `rax + 64 i` into
`zmm12` and four ciphertext blocks at `rdx + 64 i` into `zmm7`, through the
mask of the last register's `c` blocks if `last`, the other lanes zero, and
writes (`i = 0`, with `Y` added to the first block) or adds each lane's
product. `gD_ok`: the loads of `k` registers after rounds 1–`k` and the
reduction after round 5 (`StitchZH.gD k`) leave in `Y` the four lanes'
products of the `r` blocks with their powers (`laneAccG`), reduced and
added, as `QGD` says after each round.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchZ (fin)
open VG.Impl.Gcm.X86_64.StitchZH (ldGD gD)
open VG.Proof.Gcm.X86_64.StitchZ (ldInit ldAcc ldAcc_ok fin_ok gRegs)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block)

/-- The lane-wise instructions of `ldGD`. -/
abbrev restGD (i : Nat) : List Instr :=
  ([.zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0)] : List Instr) ++
    (if i = 0 then [.zop (.zbin .vpxord .xmm7 .xmm7 .xmm2)] else []) ++
    (if i = 0 then Impl.Gcm.X86_64.StitchZ.accInit .xmm7 .xmm12 else Impl.Gcm.X86_64.StitchZ.acc .xmm7 .xmm12)

theorem ldGD_eq (last : Bool) (i : Nat) :
    ldGD last i = (if last then ([.kLoad .r10 .xmm12 (at_ .rax (64 * i)), .kLoad .r10 .xmm7 (at_ .rdx (64 * i))] :
      List Instr) else [.vmovdqu32Load .xmm12 (at_ .rax (64 * i)), .vmovdqu32Load .xmm7 (at_ .rdx (64 * i))]) ++
      restGD i := by
  simp only [ldGD, restGD, List.append_assoc]

/-- The SSE block of the first load's lane-wise instructions, `Y` added. -/
def ldY : List Instr :=
  ([.xop (.bin .pshufb .xmm7 .xmm0), .xop (.bin .pxor .xmm7 .xmm2)] : List Instr) ++ ldInit.tail

theorem lane_restGD (i : Nat) : zlaneSseBlock (restGD i) = some (if i = 0 then ldY else ldAcc false) := by
  by_cases h : i = 0 <;> simp only [restGD, h, ↓reduceIte] <;> rfl

theorem ldY_ok (t : State) :
    WP isa (.block ldY) t fun t' =>
      prod t' = Prod.zero.acc (t.xmm .xmm2 ^^^ XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0)) (t.xmm .xmm12) ∧
      Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  apply WP.of_runBlock
  simp only [ldY, ldInit, List.tail_cons, List.cons_append, List.nil_append, reduceCtorEq, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm, Pclmul.eval_pxor, eval_movdqa,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [prod, Prod.acc, Prod.zero, Stitch.zero_xor_b, reduceCtorEq, ↓reduceIte, BitVec.xor_comm (t.xmm .xmm2)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- The lane-wise products of a load, written (`i = 0`, `Y` added) or added. -/
theorem restGD_ok (i : Nat) (t : State) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask) :
    WP isa (.block (restGD i)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = (if i = 0 then Prod.zero else prod (t.zproj l)).acc
        ((if i = 0 then t.zlane .xmm2 l else 0) ^^^ XBinOp.eval .pshufb (t.zlane .xmm7 l) revMask)
        (t.zlane .xmm12 l)) ∧
      ZFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  refine WP.mono (WP.zlanes (lane_restGD i) fun l _ => (?_ : WP isa (.block (if i = 0 then ldY else ldAcc false))
      (t.zproj l) fun t' => prod t' = (if i = 0 then Prod.zero else prod (t.zproj l)).acc
        ((if i = 0 then (t.zproj l).xmm .xmm2 else 0) ^^^
          XBinOp.eval .pshufb ((t.zproj l).xmm .xmm7) ((t.zproj l).xmm .xmm0)) ((t.zproj l).xmm .xmm12) ∧
        Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] (t.zproj l) t'))
    fun t' ⟨hk, hq⟩ => ⟨fun l hl => ?_, ⟨hk.gpr, hk.mem, hk.rd, hk.wr, fun r hr l hl => ?_⟩⟩
  · by_cases h : i = 0
    · simp only [h, ↓reduceIte]; exact ldY_ok _
    · simp only [h, ↓reduceIte]
      refine WP.mono (ldAcc_ok false _) fun t' ⟨p', o'⟩ => ⟨?_, o'⟩
      rw [p']; rfl
  · rw [(hq l hl).1]; simp only [State.zproj_xmm, h0 l hl]
  · have := (hq l hl).2.xmm r hr
    simpa only [State.zproj_xmm] using this

/-- After the loads of `ldGD`: the products of the lanes loaded. -/
theorem restGD_after (i : Nat) {t t₂ : State} (V7 V12 : Nat → BitVec 128)
    (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask) (l7 : ∀ l < 4, t₂.zlane .xmm7 l = V7 l)
    (l12 : ∀ l < 4, t₂.zlane .xmm12 l = V12 l) (f₂ : ZFrame [.xmm12, .xmm7] t t₂) :
    WP isa (.block (restGD i)) t₂ fun t' =>
      (∀ l < 4, prod (t'.zproj l) = (if i = 0 then Prod.zero else prod (t.zproj l)).acc
        ((if i = 0 then t.zlane .xmm2 l else 0) ^^^ XBinOp.eval .pshufb (V7 l) revMask) (V12 l)) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  refine WP.mono (restGD_ok i t₂ fun l hl => by rw [f₂.zlane _ (by decide) l hl, h0 l hl])
    fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, (f₂.comp f').mono (by decide)⟩
  have hp : prod (t₂.zproj l) = prod (t.zproj l) := by
    simp only [prod, State.zproj_xmm, f₂.zlane .xmm8 (by decide) l hl, f₂.zlane .xmm9 (by decide) l hl,
      f₂.zlane .xmm10 (by decide) l hl]
  rw [p' l hl, hp, l7 l hl, l12 l hl, f₂.zlane .xmm2 (by decide) l hl]

/-- Load `i`: four powers at `rax + 64 i` and four ciphertext blocks at
`rdx + 64 i`, through the mask of `c` blocks if `last` (the other lanes
zero), and each lane's product written (`i = 0`, `Y` added) or added. -/
theorem ldGD_ok (last : Bool) (i : Nat) (t : State) {c : Nat} (hc : c ≤ 4)
    (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask)
    (hk : last = true → State.qOn (t.gpr .r10) = List.range (2 * c))
    (hbk : last = true → ∀ j < 8, (t.gpr .r10).getLsbD j = decide (j < 2 * c))
    (hinW : InRegions (t.rd ++ t.wr) (t.gpr .rax + BitVec.ofNat 64 (64 * i)) (if last then 16 * c else 64))
    (hinA : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofNat 64 (64 * i)) (if last then 16 * c else 64)) :
    WP isa (.block (ldGD last i)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = (if i = 0 then Prod.zero else prod (t.zproj l)).acc
        ((if i = 0 then t.zlane .xmm2 l else 0) ^^^ XBinOp.eval .pshufb
          (if last = false ∨ l < c then
            t.mem.readW (t.gpr .rdx + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (16 * l)) 128 else 0) revMask)
        (if last = false ∨ l < c then
          t.mem.readW (t.gpr .rax + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (16 * l)) 128 else 0)) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  rw [ldGD_eq]
  cases last with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hinW hinA ⊢
    rw [show ([.vmovdqu32Load .xmm12 (at_ .rax (64 * i)), .vmovdqu32Load .xmm7 (at_ .rdx (64 * i))] : List Instr) =
      [.vmovdqu32Load .xmm12 (at_ .rax (64 * i))] ++ [.vmovdqu32Load .xmm7 (at_ .rdx (64 * i))] from rfl,
      WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ld512_ok .xmm12 .rax (64 * i) t hinW) fun t₁ ⟨l₁, f₁⟩ => ?_
    refine WP.mono (ld512_ok .xmm7 .rdx (64 * i) t₁ (by rw [f₁.rd, f₁.wr, f₁.gpr]; exact hinA))
      fun t₂ ⟨l₂, f₂⟩ => ?_
    rw [f₁.gpr, f₁.mem] at l₂
    refine WP.mono (restGD_after i _ (fun l => t.mem.readW (t.gpr .rax + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (16 * l)) 128) h0 l₂ (fun l hl => by rw [f₂.zlane _ (by decide) l hl, l₁ l hl])
      (f₁.comp f₂)) fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, f'⟩
    simp only [true_or, ↓reduceIte]
    exact p' l hl
  | true =>
    simp only [↓reduceIte] at hinW hinA ⊢
    rw [show ([.kLoad .r10 .xmm12 (at_ .rax (64 * i)), .kLoad .r10 .xmm7 (at_ .rdx (64 * i))] : List Instr) =
      [.kLoad .r10 .xmm12 (at_ .rax (64 * i))] ++ [.kLoad .r10 .xmm7 (at_ .rdx (64 * i))] from rfl,
      WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ld512K_ok .xmm12 .rax (64 * i) t hc (hk rfl) (hbk rfl) hinW) fun t₁ ⟨l₁, f₁⟩ => ?_
    refine WP.mono (ld512K_ok .xmm7 .rdx (64 * i) t₁ hc (by rw [f₁.gpr]; exact hk rfl)
      (by rw [f₁.gpr]; exact hbk rfl) (by rw [f₁.rd, f₁.wr, f₁.gpr]; exact hinA)) fun t₂ ⟨l₂, f₂⟩ => ?_
    rw [f₁.gpr, f₁.mem] at l₂
    refine WP.mono (restGD_after i _ (fun l => if l < c then t.mem.readW (t.gpr .rax + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (16 * l)) 128 else 0) h0 l₂ (fun l hl => by rw [f₂.zlane _ (by decide) l hl, l₁ l hl])
      (f₁.comp f₂)) fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, f'⟩
    simp only [Bool.true_eq_false, false_or]
    exact p' l hl

/-- What the GHASH of the `r = 4 (k - 1) + c` blocks at `A` with the powers
at `W` needs between the rounds: the blocks `X` (byte-reversed) and the
powers `T`, those after the `r` zero. -/
structure GEnvD (k c : Nat) (A W : Addr) (X : Nat → Block) (T : Nat → BitVec 128) (s : State) : Prop where
  rdx : s.gpr .rdx = A
  rax : s.gpr .rax = W
  qk : State.qOn (s.gpr .r10) = List.range (2 * c)
  bk : ∀ j < 8, (s.gpr .r10).getLsbD j = decide (j < 2 * c)
  inA : ∀ i < k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (64 * i)) (if i + 1 = k then 16 * c else 64)
  inW : ∀ i < k, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (64 * i)) (if i + 1 = k then 16 * c else 64)
  xs : ∀ i < k, ∀ l < 4, (i + 1 < k ∨ l < c) →
    XBinOp.eval .pshufb (s.mem.readW (A + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (16 * l)) 128) revMask =
      X (4 * i + l)
  ts : ∀ i < k, ∀ l < 4, T (4 * i + l) =
    if i + 1 < k ∨ l < c then s.mem.readW (W + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (16 * l)) 128 else 0
  m0 : ∀ l < 4, s.zlane .xmm0 l = revMask

theorem GEnvD.zframe {k c : Nat} {A W : Addr} {X : Nat → Block} {T : Nat → BitVec 128} {s s' : State}
    {rs : List XReg} (h : GEnvD k c A W X T s) (f : ZFrame rs s s') (h0 : .xmm0 ∉ rs) : GEnvD k c A W X T s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.rax, by rw [f.gpr]; exact h.qk, by rw [f.gpr]; exact h.bk,
    fun i hi => by rw [f.rd, f.wr]; exact h.inA i hi, fun i hi => by rw [f.rd, f.wr]; exact h.inW i hi,
    fun i hi l hl ho => by rw [f.mem]; exact h.xs i hi l hl ho, fun i hi l hl => by rw [f.mem]; exact h.ts i hi l hl,
    fun l hl => by rw [f.zlane _ h0 l hl]; exact h.m0 l hl⟩

/-- `Y` from the four lanes' products of the first `n` blocks, reduced and added. -/
abbrev yLanes (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (n : Nat) : Block :=
  (reduceB (laneAccG X T y 0 n) ^^^ reduceB (laneAccG X T y 2 n)) ^^^
    (reduceB (laneAccG X T y 1 n) ^^^ reduceB (laneAccG X T y 3 n))

/-- What holds before the instructions after round `j` of the rounds of the
`k` registers. -/
def QGD (k c : Nat) (A W : Addr) (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (j : Nat) (s : State) :
    Prop :=
  GEnvD k c A W X T s ∧ (∀ l < 4, s.zlane .xmm1 l = poly) ∧
  (if 5 < j then s.zlane .xmm2 0 = yLanes X T y (4 * k) ∧ ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0
   else (1 < j → ∀ l < 4, prod (s.zproj l) = laneAccG X T y l (4 * min (j - 1) k)) ∧
     ∀ l < 4, s.zlane .xmm2 l = if l = 0 then y else 0)

theorem QGD.zframe {k c : Nat} {A W : Addr} {X : Nat → Block} {T : Nat → BitVec 128} {y : Block} {j : Nat}
    {s s' : State} {rs : List XReg} (h : QGD k c A W X T y j s) (f : ZFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    QGD k c A W X T y j s' := by
  obtain ⟨hE, h1, h2⟩ := h
  have kz : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 4, s'.zlane r l = s.zlane r l :=
    fun r hr l hl => f.zlane r (fun h => hrs r h hr) l hl
  have kp : ∀ l < 4, prod (s'.zproj l) = prod (s.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, kz .xmm8 (by decide) l hl, kz .xmm9 (by decide) l hl,
      kz .xmm10 (by decide) l hl]
  refine ⟨hE.zframe f (fun h => hrs _ h (by decide)), fun l hl => by rw [kz .xmm1 (by decide) l hl]; exact h1 l hl, ?_⟩
  by_cases h5 : 5 < j
  · rw [ite_eq_left h5] at h2 ⊢
    exact ⟨by rw [kz .xmm2 (by decide) 0 (by decide)]; exact h2.1,
      fun l h1 h4 => by rw [kz .xmm2 (by decide) l h4]; exact h2.2 l h1 h4⟩
  · rw [ite_eq_right h5] at h2 ⊢
    exact ⟨fun hj l hl => by rw [kp l hl]; exact h2.1 hj l hl,
      fun l hl => by rw [kz .xmm2 (by decide) l hl]; exact h2.2 l hl⟩

/-- A product with zero adds nothing, whatever the block. -/
theorem Prod.acc_zero_any (p : Prod) (a b : BitVec 128) : p.acc a 0 = p.acc b 0 := by
  rw [Prod.acc_zero_right, Prod.acc_zero_right]

/-- The GHASH work between the rounds of the `k` registers. -/
theorem gD_ok {k c : Nat} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hc4 : c ≤ 4) {A W : Addr} {X : Nat → Block}
    {T : Nat → BitVec 128} {y : Block} :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, QGD k c A W X T y j s →
      WP isa (.block (gD k j)) s fun s' => QGD k c A W X T y (j + 1) s' ∧ ZFrame gRegs s s' := by
  intro j hj1 hj9 s ⟨hE, h1, h2⟩
  by_cases hjk : j ≤ k
  · -- Load `j - 1`.
    rw [ite_eq_right (show ¬ 5 < j by omega)] at h2
    have hg : gD k j = ldGD (j == k) (j - 1) := by
      simp only [gD, show 1 ≤ j ∧ j ≤ k from ⟨hj1, hjk⟩, and_self, ite_true]
    have hl : (j == k) = true ↔ j - 1 + 1 = k := by simp only [beq_iff_eq]; omega
    have hin : ∀ a : Addr, (∀ i < k, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (64 * i))
        (if i + 1 = k then 16 * c else 64)) →
        InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (64 * (j - 1))) (if (j == k) then 16 * c else 64) :=
      fun a h => by
        have := h (j - 1) (by omega)
        by_cases hjk' : j = k
        · rw [ite_eq_left (show j - 1 + 1 = k by omega)] at this
          rwa [ite_eq_left (show (j == k) = true by simpa using hjk')]
        · rw [ite_eq_right (show ¬ j - 1 + 1 = k by omega)] at this
          rwa [ite_eq_right (show ¬ (j == k) = true by simpa using hjk')]
    rw [hg]
    refine WP.mono (ldGD_ok (j == k) (j - 1) s hc4 hE.m0 (fun _ => hE.qk) (fun _ => hE.bk)
        (by rw [hE.rax]; exact hin W hE.inW) (by rw [hE.rdx]; exact hin A hE.inA))
      fun s' ⟨p', f'⟩ => ⟨⟨hE.zframe f' (by decide), fun l hl => by
        rw [f'.zlane _ (by decide) l hl]; exact h1 l hl, ?_⟩, f'.mono (by decide)⟩
    rw [ite_eq_right (show ¬ 5 < j + 1 by omega)]
    refine ⟨fun _ l hl => ?_, fun l hl => by rw [f'.zlane _ (by decide) l hl]; exact h2.2 l hl⟩
    rw [p' l hl, show min (j + 1 - 1) k = j - 1 + 1 by omega, hE.rdx, hE.rax]
    have hp : j - 1 ≠ 0 → prod (s.zproj l) = laneAccG X T y l (4 * (j - 1)) := fun h => by
      rw [h2.1 (by omega) l hl, show min (j - 1) k = j - 1 by omega]
    have hy : s.zlane .xmm2 l = if l = 0 then y else 0 := h2.2 l hl
    have ht := hE.ts (j - 1) (by omega) l hl
    by_cases ho : (j == k) = false ∨ l < c
    · have ho' : j - 1 + 1 < k ∨ l < c := by
        rcases ho with h | h
        · left; have : ¬ j = k := by simpa using h
          omega
        · exact .inr h
      rw [ite_eq_left ho, ite_eq_left ho]
      rw [ite_eq_left ho'] at ht
      exact hashStep_eq (X := X) (T := T) (y := y) (j := j - 1) hl _ _ _ _ hp hy (hE.xs (j - 1) (by omega) l hl ho').symm ht
    · have ho' : ¬ (j - 1 + 1 < k ∨ l < c) := fun h => ho (by
        rcases h with h | h
        · left; simp only [beq_eq_false_iff_ne]; omega
        · exact .inr h)
      rw [ite_eq_right ho'] at ht
      have e := hashStep_eq (X := X) (T := T) (y := y) (j := j - 1) hl (prod (s.zproj l)) (s.zlane .xmm2 l)
        (X (4 * (j - 1) + l)) 0 hp hy rfl ht
      rw [ite_eq_right ho, ite_eq_right ho, ← e]
      exact Prod.acc_zero_any _ _ _
  · by_cases h5 : j = 5
    · -- The reduction.
      subst h5
      rw [ite_eq_right (show ¬ 5 < 5 by omega)] at h2
      have hg : gD k 5 = fin := by simp only [gD, show ¬ (1 ≤ 5 ∧ 5 ≤ k) by omega, ite_false, ite_true]
      rw [hg]
      refine WP.mono (fin_ok s h1) fun s' ⟨y0, y1, f'⟩ =>
        ⟨⟨hE.zframe f' (by decide), fun l hl => by rw [f'.zlane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
          f'.mono (by decide)⟩
      rw [ite_eq_left (show 5 < 5 + 1 by omega)]
      refine ⟨?_, y1⟩
      rw [y0, h2.1 (by decide) 0 (by decide), h2.1 (by decide) 1 (by decide), h2.1 (by decide) 2 (by decide),
        h2.1 (by decide) 3 (by decide), show min (5 - 1) k = k by omega]
    · -- Nothing.
      have hg : gD k j = [] := by
        simp only [gD, show ¬ (1 ≤ j ∧ j ≤ k) by omega, ite_false, h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE, h1, ?_⟩, ZFrame.refl _ _⟩
      by_cases h6 : 5 < j
      · rw [ite_eq_left h6] at h2; rw [ite_eq_left (show 5 < j + 1 by omega)]; exact h2
      · rw [ite_eq_right h6] at h2; rw [ite_eq_right (show ¬ 5 < j + 1 by omega)]
        refine ⟨fun _ l hl => ?_, h2.2⟩
        rw [h2.1 (by omega) l hl, show min (j - 1) k = k by omega, show min (j + 1 - 1) k = k by omega]

end VG.Proof.Gcm.X86_64.StitchZH
