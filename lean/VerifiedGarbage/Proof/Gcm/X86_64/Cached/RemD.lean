module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGKs
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemMask
import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Gcm.X86_64.Cached.RemGD`, which this module and modules that import it used -/

section

/-! ### `Gcm.X86_64.Cached.RemGDHash`, which only this module used -/

section

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
  obtain hp : prod (t₂.zproj l) = prod (t.zproj l) := by
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
  obtain kz : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 4, s'.zlane r l = s.zlane r l :=
    fun r hr l hl => f.zlane r (fun h => hrs r h hr) l hl
  obtain kp : ∀ l < 4, prod (s'.zproj l) = prod (s.zproj l) := fun l hl => by
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
    rw [ite_eq_right (show ¬ 5 < j by omega_arith)] at h2
    obtain hg : gD k j = ldGD (j == k) (j - 1) := by
      simp only [gD, show 1 ≤ j ∧ j ≤ k from ⟨hj1, hjk⟩, and_self, ite_true]
    obtain hl : (j == k) = true ↔ j - 1 + 1 = k := by simp only [beq_iff_eq]; omega_arith
    obtain hin : ∀ a : Addr, (∀ i < k, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (64 * i))
        (if i + 1 = k then 16 * c else 64)) →
        InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (64 * (j - 1))) (if (j == k) then 16 * c else 64) :=
      fun a h => by
        have := h (j - 1) (by omega_arith)
        by_cases hjk' : j = k
        · rw [ite_eq_left (show j - 1 + 1 = k by omega_arith)] at this
          rwa [ite_eq_left (show (j == k) = true by simpa using hjk')]
        · rw [ite_eq_right (show ¬ j - 1 + 1 = k by omega_arith)] at this
          rwa [ite_eq_right (show ¬ (j == k) = true by simpa using hjk')]
    rw [hg]
    refine WP.mono (ldGD_ok (j == k) (j - 1) s hc4 hE.m0 (fun _ => hE.qk) (fun _ => hE.bk)
        (by rw [hE.rax]; exact hin W hE.inW) (by rw [hE.rdx]; exact hin A hE.inA))
      fun s' ⟨p', f'⟩ => ⟨⟨hE.zframe f' (by decide), fun l hl => by
        rw [f'.zlane _ (by decide) l hl]; exact h1 l hl, ?_⟩, f'.mono (by decide)⟩
    rw [ite_eq_right (show ¬ 5 < j + 1 by omega_arith)]
    refine ⟨fun _ l hl => ?_, fun l hl => by rw [f'.zlane _ (by decide) l hl]; exact h2.2 l hl⟩
    rw [p' l hl, show min (j + 1 - 1) k = j - 1 + 1 by omega_arith, hE.rdx, hE.rax]
    obtain hp : j - 1 ≠ 0 → prod (s.zproj l) = laneAccG X T y l (4 * (j - 1)) := fun h => by
      rw [h2.1 (by omega_arith) l hl, show min (j - 1) k = j - 1 by omega_arith]
    obtain hy : s.zlane .xmm2 l = if l = 0 then y else 0 := h2.2 l hl
    obtain ht := hE.ts (j - 1) (by omega_arith) l hl
    by_cases ho : (j == k) = false ∨ l < c
    · have ho' : j - 1 + 1 < k ∨ l < c := by
        rcases ho with h | h
        · left; have : ¬ j = k := by simpa using h
          omega_arith
        · exact .inr h
      rw [ite_eq_left ho, ite_eq_left ho]
      rw [ite_eq_left ho'] at ht
      exact hashStep_eq (X := X) (T := T) (y := y) (j := j - 1) hl _ _ _ _ hp hy (hE.xs (j - 1) (by omega_arith) l hl ho').symm ht
    · have ho' : ¬ (j - 1 + 1 < k ∨ l < c) := fun h => ho (by
        rcases h with h | h
        · left; simp only [beq_eq_false_iff_ne]; omega_arith
        · exact .inr h)
      rw [ite_eq_right ho'] at ht
      obtain e := hashStep_eq (X := X) (T := T) (y := y) (j := j - 1) hl (prod (s.zproj l)) (s.zlane .xmm2 l)
        (X (4 * (j - 1) + l)) 0 hp hy rfl ht
      rw [ite_eq_right ho, ite_eq_right ho, ← e]
      exact Prod.acc_zero_any _ _ _
  · by_cases h5 : j = 5
    · -- The reduction.
      subst h5
      rw [ite_eq_right (show ¬ 5 < 5 by omega_arith)] at h2
      obtain hg : gD k 5 = fin := by simp only [gD, show ¬ (1 ≤ 5 ∧ 5 ≤ k) by omega_arith, ite_false, ite_true]
      rw [hg]
      refine WP.mono (fin_ok s h1) fun s' ⟨y0, y1, f'⟩ =>
        ⟨⟨hE.zframe f' (by decide), fun l hl => by rw [f'.zlane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
          f'.mono (by decide)⟩
      rw [ite_eq_left (show 5 < 5 + 1 by omega_arith)]
      refine ⟨?_, y1⟩
      rw [y0, h2.1 (by decide) 0 (by decide), h2.1 (by decide) 1 (by decide), h2.1 (by decide) 2 (by decide),
        h2.1 (by decide) 3 (by decide), show min (5 - 1) k = k by omega_arith]
    · -- Nothing.
      obtain hg : gD k j = [] := by
        simp only [gD, show ¬ (1 ≤ j ∧ j ≤ k) by omega_arith, ite_false, h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE, h1, ?_⟩, ZFrame.refl _ _⟩
      by_cases h6 : 5 < j
      · rw [ite_eq_left h6] at h2; rw [ite_eq_left (show 5 < j + 1 by omega_arith)]; exact h2
      · rw [ite_eq_right h6] at h2; rw [ite_eq_right (show ¬ 5 < j + 1 by omega_arith)]
        refine ⟨fun _ l hl => ?_, h2.2⟩
        rw [h2.1 (by omega_arith) l hl, show min (j - 1) k = k by omega_arith, show min (j + 1 - 1) k = k by omega_arith]

end VG.Proof.Gcm.X86_64.StitchZH

end

end


/-!
# Decryption: the blocks after the last group, as a masked group

`ksBatchGD_ok`: `StitchZH.ksBatchGD k` puts the mask of the last register's
blocks in `r10` (`remMaskG_ok`), encrypts the counters `c …` in the lanes of
`k` registers while it hashes the `r` ciphertext blocks at `rdx` between the
rounds (`gD_ok`), and adds the blocks to the keystream and stores them
(`xorG_ok`): the blocks decrypted in place, and `Y` their `GHASH` lanes,
reduced and added (`yLanes`). `ksSelGD_ok` runs it for the `⌈r / 4⌉`
registers the `r` blocks take, from `r10 = 16 r`. `remGD_ok`: once the
decryption loop stops with `r = nb mod 16` blocks left (`DInv`, the groups
already hashed and decrypted), `StitchZH.remGD` stores the counter after all
the blocks (`remSetup_ok`), decrypts the `r` blocks as a masked group, and
stores `Y`, for powers whose products add up to `GHASH` (`RemOkG`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH (remMaskG xorG gD ksBatchGD)
open VG.Proof.Gcm.X86_64.StitchZ (aregs_ok gRegs gRegs_ok)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Proof.Gcm.X86_64.Stitch (SPre DPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀
  addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep')
open VG.Impl.Gcm.X86_64.Stitch (storeY)
open VG.Impl.Gcm.X86_64.StitchZH (ksSelGD remGD remSetup)
open VG.Proof.Gcm.X86_64.StitchZ (DInv AInv)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (blocksAt ghashFrom)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq)
open VG.Proof.Gcm.X86_64.Pclmul (toNat_ofNat_lt)
open VG.Spec.Gcm (Block blockAt inc32)

theorem remMaskG_noCalls : remMaskG.noCalls = true := rfl
theorem remMaskG_keeps : remMaskG.all Instr.keepsH = true := rfl

/-- The `r` ciphertext blocks at `A` (`rdx`) as a group of `k` registers:
their counters `c …` encrypted while the blocks are hashed between the
rounds with the powers at `W` (`rax`), from `Y` in lane 0 of `xmm2`, and the
blocks decrypted in place. -/
theorem ksBatchGD_ok {s₀ : State} (hp : SPre s₀) {k r : Nat} (hk4 : k ≤ 4) (hr1 : 1 ≤ r) (hr15 : r ≤ 15)
    (hrk : r ≤ 4 * k) (hkr : 4 * k < r + 4) {A W : Addr} {T : Nat → BitVec 128} {y : Block} {c : Nat}
    {s : State}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hA : s.gpr .rdx = A) (hW : s.gpr .rax = W)
    (hT : ∀ n < r, s.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinA : InRegions s.wr A (16 * r)) (hinW : InRegions (s.rd ++ s.wr) W (16 * r))
    (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) (h2 : ∀ l < 4, s.zlane .xmm2 l = if l = 0 then y else 0)
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask) (hinc : ∀ l < 4, s.zlane .xmm15 l = four)
    (hrdi : s.gpr .rdi = kp s₀) (hrsi : s.gpr .rsi = s₀.gpr .rsi)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hfr : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s.mem)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (ksBatchGD k) s fun s' =>
      (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
        blockAt s.mem (A + BitVec.ofNat 64 (16 * n)) ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
      Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
      s'.zlane .xmm2 0 = yLanes (fun n => blockAt s.mem (A + BitVec.ofNat 64 (16 * n))) T y r ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm14, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
  have hwp := hp.wrap_p
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  obtain hnd' : (aregs.take k).Nodup := hnd.sublist (List.take_sublist _ _)
  obtain hx' : ∀ r ∈ aregs.take k, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := fun r hr => hx r (List.mem_of_mem_take hr)
  obtain h13' : .xmm13 ∉ aregs.take k := fun h => h13 (List.mem_of_mem_take h)
  obtain hlen : (aregs.take k).length = k := by simp [aregs]; omega_arith
  obtain hk1 : 1 ≤ k := by omega_arith
  let c' := (r - 1) % 4 + 1
  obtain hc : 4 * (k - 1) + c' = r := by omega_arith
  obtain ⟨mq, mb⟩ := maskG_ok c' (by omega_arith) (by omega_arith)
  obtain hK : Keys (nr s₀) (sch s₀) s := keys_of hp hrdi hrd hwr hfr
  -- The mask.
  refine WP.seq (WP.mono (WP.hkeepCode remMaskG_noCalls remMaskG_keeps (remMaskG_ok s hr1 (by omega_arith) h9))
    fun t ⟨⟨a₀, g₀, l₀, m₀, rd₀, wr₀⟩, hh₀⟩ => ?_)
  obtain hK₀ : Keys (nr s₀) (sch s₀) t :=
    keys_of hp (by rw [g₀ _ (by decide)]; exact hrdi) (by rw [rd₀]; exact hrd) (by rw [wr₀]; exact hwr)
      (by rw [m₀]; exact hfr)
  obtain hCache₀ := hCache.keep hh₀ hK₀
  -- The counters.
  refine WP.seq (WP.mono (WP.hkeep (ctrsZ_keeps _ _ _ _) (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide)
    (aregs.take k) t (cb s₀) c hnd' hx' (fun l hl => by rw [l₀]; exact hctr l hl)
    (fun l hl => by rw [l₀]; exact hmsk l hl) (fun l hl => by rw [l₀]; exact hinc l hl)))
    fun s₁ ⟨⟨e₁, c₁, f₁⟩, hh₁⟩ => ?_)
  obtain hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys hK₀ f₁
  obtain hCache₁ := hCache₀.keep hh₁ hK₁
  -- The GHASH environment of the rounds.
  let X' : Nat → Block := fun n => blockAt s.mem (A + BitVec.ofNat 64 (16 * n))
  let T' : Nat → BitVec 128 := fun n => if n < r then T n else 0
  obtain kz₁ : ∀ x, x ≠ .xmm14 → x ∉ aregs.take k → ∀ l < 4, s₁.zlane x l = s.zlane x l := fun x h14 hx l hl => by
    rw [f₁.zlane x (by simp only [List.mem_cons, not_or]; exact ⟨h14, hx⟩) l hl, l₀]
  obtain nA : ∀ x, x ∉ aregs → x ∉ aregs.take k := fun x hx h => hx (List.mem_of_mem_take h)
  obtain hm₁ : s₁.mem = s.mem := by rw [f₁.mem, m₀]
  obtain hrw₁ : s₁.rd ++ s₁.wr = s.rd ++ s.wr := by rw [f₁.rd, f₁.wr, rd₀, wr₀]
  obtain hsub : ∀ a : Addr, InRegions (s.rd ++ s.wr) a (16 * r) → ∀ i < k,
      InRegions (s₁.rd ++ s₁.wr) (a + BitVec.ofNat 64 (64 * i)) (if i + 1 = k then 16 * c' else 64) :=
    fun a h i hi => by
      rw [hrw₁]
      by_cases hik : i + 1 = k
      · rw [ite_eq_left hik]
        exact CallLay.inRegions_sub (off := 64 * i) (l := 16 * c') h (by omega_arith) (by omega_arith)
      · rw [ite_eq_right hik]
        exact CallLay.inRegions_sub (off := 64 * i) (l := 64) h (by omega_arith) (by omega_arith)
  obtain hE₁ : GEnvD k c' A W X' T' s₁ :=
    { rdx := by rw [f₁.gpr, g₀ _ (by decide)]; exact hA
      rax := by rw [f₁.gpr, g₀ _ (by decide)]; exact hW
      qk := by rw [f₁.gpr, a₀]; exact mq
      bk := by rw [f₁.gpr, a₀]; exact mb
      inA := hsub A (in_rdwr hinA)
      inW := hsub W hinW
      xs := fun i hi l hl _ => by
        show _ = blockAt s.mem (A + BitVec.ofNat 64 (16 * (4 * i + l)))
        rw [hm₁, blockAt_eq, Offset.add_add, show 64 * i + 16 * l = 16 * (4 * i + l) by omega_arith]
      ts := fun i hi l hl => by
        show (if 4 * i + l < r then T (4 * i + l) else 0) = _
        by_cases ho : i + 1 < k ∨ l < c'
        · rw [ite_eq_left (show 4 * i + l < r by omega_arith), ite_eq_left ho, hm₁, ← hT _ (by omega_arith), Offset.add_add,
            show 64 * i + 16 * l = 16 * (4 * i + l) by omega_arith]
        · rw [ite_eq_right (show ¬ 4 * i + l < r by omega_arith), ite_eq_right ho]
      m0 := fun l hl => by rw [kz₁ _ (by decide) (nA _ (by decide)) l hl]; exact hmsk l hl }
  obtain hQ₁ : QGD k c' A W X' T' y 1 s₁ :=
    ⟨hE₁, fun l hl => by rw [kz₁ _ (by decide) (nA _ (by decide)) l hl]; exact h1 l hl, by
      rw [ite_eq_right (show ¬ 5 < 1 by omega_arith)]
      exact ⟨fun h => absurd h (by decide), fun l hl => by rw [kz₁ _ (by decide) (nA _ (by decide)) l hl]; exact h2 l hl⟩⟩
  -- The rounds, the blocks hashed between them.
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 (aregs.take k) hnd' h13' hp.rounds (gD k) gRegs
    (fun r h hm => (gRegs_ok r h).1 (List.mem_of_mem_take hm)) (QGD k c' A W X' T' y)
    (fun j hj h9 t _ hq => WP.mono (WP.hkeep (gD_keeps k j) (gD_ok hk1 hk4 (by omega_arith) j hj h9 t hq))
      fun _ ⟨⟨hq', hf⟩, hh⟩ => ⟨hq', hf, hh⟩)
    (fun j s s' h f => h.zframe f.toZFrame fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · have := List.mem_of_mem_take hr
        simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl | rfl <;> decide) s₁ hCache₁ hQ₁
    (by rw [f₁.gpr, g₀ _ (by decide), hrsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  obtain ⟨_, _, hY⟩ := hQ₂
  rw [ite_eq_left (show 5 < 10 by omega_arith)] at hY
  -- The keystream blocks.
  obtain ks : ∀ n < r, XBinOp.eval .pshufb (s₂.zlane ((aregs.take k).getD (n / 4) .xmm0) (n % 4)) revMask =
      ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀)) := fun n hn => by
    obtain h : n / 4 < (aregs.take k).length := by rw [hlen]; omega_arith
    rw [← List.getElem_eq_getD (h := h),
      (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) _ (by omega_arith), e₁ _ h _ (by omega_arith)])).symm,
      show c + 4 * (n / 4) + n % 4 = c + n by omega_arith]
  obtain hg₂ : ∀ q, q ≠ .r10 → s₂.gpr q = s.gpr q := fun q hq => by rw [f₂.gpr, f₁.gpr, g₀ q hq]
  obtain hm₂ : s₂.mem = s.mem := by rw [f₂.mem, hm₁]
  obtain hrd₂ : s₂.rd = s.rd := by rw [f₂.rd, f₁.rd, rd₀]
  obtain hwr₂ : s₂.wr = s.wr := by rw [f₂.wr, f₁.wr, wr₀]
  obtain e0 : ∀ a : Addr, a + BitVec.ofNat 64 (64 * 0) = a := fun a => BitVec.add_zero a
  obtain hc16 : 64 * ((aregs.take k).length - 1) + 16 * c' = 16 * r := by rw [hlen]; omega_arith
  obtain hc4 : 4 * ((aregs.take k).length - 1) + c' = r := by rw [hlen]; omega_arith
  obtain hA₂ : s₂.gpr .rdx = A := by rw [hg₂ _ (by decide)]; exact hA
  -- The blocks decrypted.
  refine WP.mono (xorG_ok .rdx (aregs.take k) 0 s₂ (c := c') (by
      intro h; rw [h] at hlen; simp at hlen; omega_arith) hnd' h13' (by omega_arith)
      (by rw [f₂.gpr, f₁.gpr, a₀]; exact mq) (by rw [f₂.gpr, f₁.gpr, a₀]; exact mb)
      (by rw [hA₂, e0, hc16, hrd₂, hwr₂]; exact in_rdwr hinA)
      (by rw [hA₂, e0, hc16, hwr₂]; exact hinA)
      (fun n q' hq hn => by
        rw [hA₂, Nat.mul_zero, Nat.zero_add, Nat.zero_add]
        rw [show A + BitVec.ofNat 64 (64 * q') = A + BitVec.ofNat 64 (16 * (4 * q')) by rw [← Nat.mul_assoc]]
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
      (by rw [hlen]; omega_arith)) fun s' ⟨b', z', f', g', rd', wr', k'⟩ => ?_
  rw [hc4, hA₂] at b' z'
  rw [hc16, hA₂, e0] at f'
  simp only [Nat.mul_zero, Nat.zero_add] at b' z'
  obtain hy₂ : ∀ l < 4, s'.zlane .xmm2 l = s₂.zlane .xmm2 l := fun l hl =>
    k' _ (fun h => by
      have := List.mem_of_mem_take h
      simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h | h <;> cases h) (by decide) l hl
  refine ⟨fun n hn => ?_, by rw [← hm₂]; exact f', ?_, fun l h1 h4 => by rw [hy₂ l h4]; exact hY.2 l h1 h4,
    fun q hq => by rw [g', hg₂ q hq], by rw [rd', hrd₂], by rw [wr', hwr₂], fun x hx hx' l hl => ?_⟩
  · rw [b' n hn, hm₂, ks n hn]
  · rw [hy₂ 0 (by decide), hY.1]
    simp only [yLanes]
    rw [laneAccG_pad X' T y 0 r (4 * k) hrk, laneAccG_pad X' T y 1 r (4 * k) hrk,
      laneAccG_pad X' T y 2 r (4 * k) hrk, laneAccG_pad X' T y 3 r (4 * k) hrk]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    obtain ⟨n13, n14, n12, n7, n8, n9, n10, n11, n2⟩ := hx'
    rw [k' x (nA x hx) n13 l hl, f₂.zlane x (by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
      exact ⟨n13, nA x hx, n12, n7, n8, n9, n10, n11, n2⟩) l hl, kz₁ x n14 (nA x hx) l hl]

/-- `add r9, 16`. -/
theorem add9_ok (s : State) :
    WP isa (.block [.alu .add .r9 (.imm 16)]) s fun s' =>
      s'.gpr .r9 = s.gpr .r9 + 16 ∧ (∀ q, q ≠ .r9 → s'.gpr q = s.gpr q) ∧ (∀ x l, s'.zlane x l = s.zlane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    State.setReg, e16, ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `ksBatchGD` of `⌈r / 4⌉` registers, from `r10 = 16 r`. -/
theorem ksSelGD_ok {s₀ : State} (hp : SPre s₀) {r : Nat} (hr1 : 1 ≤ r) (hr15 : r ≤ 15)
    {A W : Addr} {T : Nat → BitVec 128} {y : Block} {c : Nat} {s : State}
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hA : s.gpr .rdx = A) (hW : s.gpr .rax = W)
    (hT : ∀ n < r, s.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinA : InRegions s.wr A (16 * r)) (hinW : InRegions (s.rd ++ s.wr) W (16 * r))
    (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) (h2 : ∀ l < 4, s.zlane .xmm2 l = if l = 0 then y else 0)
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask) (hinc : ∀ l < 4, s.zlane .xmm15 l = four)
    (hrdi : s.gpr .rdi = kp s₀) (hrsi : s.gpr .rsi = s₀.gpr .rsi)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hfr : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s.mem)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa ksSelGD s fun s' =>
      (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
        blockAt s.mem (A + BitVec.ofNat 64 (16 * n)) ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
      Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
      s'.zlane .xmm2 0 = yLanes (fun n => blockAt s.mem (A + BitVec.ofNat 64 (16 * n))) T y r ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm14, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
  obtain br : ∀ k, r ≤ 4 * k → 4 * k < r + 4 → k ≤ 4 → ∀ t : State, t.gpr = s.gpr →
      (∀ x l, t.zlane x l = s.zlane x l) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → HKeep s t →
      WP isa (ksBatchGD k) t fun s' =>
        (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
          blockAt s.mem (A + BitVec.ofNat 64 (16 * n)) ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
        Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
        s'.zlane .xmm2 0 = yLanes (fun n => blockAt s.mem (A + BitVec.ofNat 64 (16 * n))) T y r ∧
        (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
        (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm14, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
    intro k hrk hkr hk4 t hg' hl hm hrd' hwr' hh
    obtain hm' : ∀ a : Addr, blockAt t.mem a = blockAt s.mem a := fun a => by rw [hm]
    refine WP.mono (ksBatchGD_ok hp hk4 hr1 hr15 hrk hkr (A := A) (W := W) (T := T) (y := y) (c := c)
      (by rw [hg']; exact h9) (by rw [hg']; exact hA) (by rw [hg']; exact hW) (fun n hn => by rw [hm]; exact hT n hn)
      (by rw [hwr']; exact hinA) (by rw [hrd', hwr']; exact hinW)
      (fun l hl' => by rw [hl]; exact h1 l hl') (fun l hl' => by rw [hl]; exact h2 l hl')
      (fun l hl' => by rw [hl]; exact hctr l hl') (fun l hl' => by rw [hl]; exact hmsk l hl')
      (fun l hl' => by rw [hl]; exact hinc l hl') (by rw [hg']; exact hrdi) (by rw [hg']; exact hrsi)
      (by rw [hrd']; exact hrd) (by rw [hwr']; exact hwr) (by rw [hm]; exact hfr)
      (hCache.keep hh (Keys.mk (by rw [hg', hm]; exact (hCache.base).sched) hCache.base.le
        (by rw [hrd', hwr', hg']; exact hCache.base.keys))))
      fun s' ⟨b', f', y', y1', g', rd', wr', z'⟩ => ⟨fun n hn => by rw [b' n hn, hm' _], by rw [← hm]; exact f',
        by rw [y']; simp only [hm'], y1', fun q hq => by rw [g' q hq, hg'], by rw [rd', hrd'], by rw [wr', hwr'],
        fun x h1 h2 l hl' => by rw [z' x h1 h2 l hl', hl]⟩
  obtain c65 : BitVec.signExtend 64 (65 : BitVec 32) = BitVec.ofNat 64 65 := by decide
  obtain c129 : BitVec.signExtend 64 (129 : BitVec 32) = BitVec.ofNat 64 129 := by decide
  obtain c193 : BitVec.signExtend 64 (193 : BitVec 32) = BitVec.ofNat 64 193 := by decide
  obtain t16 : (s.gpr .r10).toNat = 16 * r := by rw [h10, toNat_ofNat_lt (by omega_arith)]
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s 65 65 c65)) fun s₁ ⟨⟨cf₁, g₁, l₁, m₁, rd₁, wr₁⟩, hh₁⟩ => ?_)
  rw [t16, show (BitVec.ofNat 64 65).toNat = 65 from rfl] at cf₁
  refine WP.ite (decide (16 * r < 65)) (by simp only [eval, cf₁]) (fun h => ?_) (fun h => ?_)
  · exact br 1 (by simp at h; omega_arith) (by simp at h; omega_arith) (by decide) s₁ g₁ l₁ m₁ rd₁ wr₁ hh₁
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s₁ 129 129 c129))
    fun s₂ ⟨⟨cf₂, g₂, l₂, m₂, rd₂, wr₂⟩, hh₂⟩ => ?_)
  rw [g₁, t16, show (BitVec.ofNat 64 129).toNat = 129 from rfl] at cf₂
  refine WP.ite (decide (16 * r < 129)) (by simp only [eval, cf₂]) (fun h' => ?_) (fun h' => ?_)
  · exact br 2 (by simp at h'; omega_arith) (by simp at h h'; omega_arith) (by decide) s₂ (by rw [g₂, g₁])
      (fun x l => by rw [l₂, l₁]) (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (hh₁.trans hh₂)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s₂ 193 193 c193))
    fun s₃ ⟨⟨cf₃, g₃, l₃, m₃, rd₃, wr₃⟩, hh₃⟩ => ?_)
  rw [g₂, g₁, t16, show (BitVec.ofNat 64 193).toNat = 193 from rfl] at cf₃
  refine WP.ite (decide (16 * r < 193)) (by simp only [eval, cf₃]) (fun h'' => ?_) (fun h'' => ?_)
  · exact br 3 (by simp at h''; omega_arith) (by simp at h' h''; omega_arith) (by decide) s₃ (by rw [g₃, g₂, g₁])
      (fun x l => by rw [l₃, l₂, l₁]) (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
      ((hh₁.trans hh₂).trans hh₃)
  · exact br 4 (by omega_arith) (by simp at h''; omega_arith) (by decide) s₃ (by rw [g₃, g₂, g₁])
      (fun x l => by rw [l₃, l₂, l₁]) (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
      ((hh₁.trans hh₂).trans hh₃)

theorem remGD_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hr : RemOkG (hk s₀) P) {e : Nat}
    {s : State} (hI : DInv s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq (.block [.alu .add .r9 (.imm 16)]) remGD) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have hle := hI.a.le
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  obtain hr1 : 1 ≤ r := by omega_arith
  obtain hr15 : r ≤ 15 := by omega_arith
  refine WP.seq (WP.mono (WP.hkeep (by decide) (add9_ok s)) fun s' ⟨⟨a9, ga, la, ma, rda, wra⟩, hha⟩ => ?_)
  obtain hr9 : s'.gpr .r9 = BitVec.ofNat 64 (16 + r) := by
    rw [a9, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
    congr 1; omega_arith
  obtain hrax : s'.gpr .rax = cp s₀ := by rw [ga _ (by decide)]; exact hI.rax
  obtain hr11 : s'.gpr .r11 = pp s₀ := by
    rw [ga _ (by decide)]; exact hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  obtain hA' : AInv s₀ (16 * e) s' :=
    ⟨hI.a.le, fun l hl => by rw [la]; exact hI.a.ctr l hl, fun l hl => by rw [la]; exact hI.a.msk l hl,
      fun l hl => by rw [la]; exact hI.a.inc l hl, by rw [ga _ (by decide)]; exact hI.a.rdi,
      by rw [ga _ (by decide)]; exact hI.a.rsi, by rw [ga _ (by decide)]; exact hI.a.r10,
      by rw [ma]; exact hI.a.frame, fun k hk => by rw [ma]; exact hI.a.blocks k hk, by rw [rda]; exact hI.a.rd,
      by rw [wra]; exact hI.a.wr⟩
  obtain hCache' := hCache.keep hha (hA'.keys hp)
  rw [show remGD = .seq (.block remSetup) (.seq ksSelGD (.block storeY)) from rfl]
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (remSetup_ok s' hr1 hr15 hr9
    (by rw [← State.zlane_lt2 _ _ (by decide), la]; exact hI.a.msk 0 (by decide))
    (by rw [hrax, wra, hI.a.wr]; exact in_sub_int hp.c_in (by omega_arith))))
    fun s₁ ⟨⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  obtain e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hrax, e0, ma] at m₁
  rw [hr11] at ax₁
  obtain gk₁ : ∀ q, q ≠ .r10 → q ≠ .rax → q ≠ .r9 → s₁.gpr q = s.gpr q := fun q h1 h2 h3 => by
    rw [g₁ q h1 h2, ga q h3]
  obtain zk₁ : ∀ x, x ≠ .xmm13 → ∀ l < 4, s₁.zlane x l = s.zlane x l := fun x h l hl => by rw [z₁ x h l hl, la]
  obtain cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  obtain hfr₁ : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  obtain hrd₁ : s₁.rd = s₀.rd := by rw [rd₁, rda]; exact hI.a.rd
  obtain hwr₁ : s₁.wr = s₀.wr := by rw [wr₁, wra]; exact hI.a.wr
  obtain hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [gk₁ _ (by decide) (by decide) (by decide)]; exact hI.a.rdi
  obtain hCache₁ := hCache'.keep hh₁ (keys_of hp hrdi₁ hrd₁ hwr₁ hfr₁)
  -- The `r` blocks, hashed between the rounds and decrypted.
  let A := bAddr s₀ (16 * e)
  let W := pp s₀ + BitVec.ofNat 64 (256 - 16 * r)
  obtain hA : s₁.gpr .rdx = A := by
    rw [gk₁ _ (by decide) (by decide) (by decide), hI.rdx]
    show dp s₀ + BitVec.ofNat 64 (256 * e) = dp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [show 256 * e = 16 * (16 * e) by omega_arith]
  let y := ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))
  refine WP.seq (WP.mono (ksSelGD_ok hp hr1 hr15 (A := A) (W := W)
    (T := fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128) (y := y) (c := 16 * e) a10₁
    (by rw [g₁ _ (by decide) (by decide)]; exact hr9) hA ax₁ (fun _ _ => rfl)
    (by rw [hwr₁, show A = dp s₀ + BitVec.ofNat 64 (16 * (16 * e)) from rfl]; exact in_sub hp.d_in (by omega_arith))
    (by rw [hrd₁, hwr₁]; exact in_rdwr (in_sub hp.p_in (by omega_arith)))
    (fun l hl => by rw [zk₁ _ (by decide) l hl]; exact hI.m1 l hl)
    (fun l hl => by
      rw [zk₁ _ (by decide) l hl]
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · exact hI.y
      · rw [ite_eq_right_iff.2 (fun h => absurd h (by omega_arith))]; exact hI.y1 l hl0 hl)
    (fun l hl => by rw [zk₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [zk₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [zk₁ _ (by decide) l hl]; exact hI.a.inc l hl) hrdi₁
    (by rw [gk₁ _ (by decide) (by decide) (by decide)]; exact hI.a.rsi) hrd₁ hwr₁ hfr₁ hCache₁)
    fun s₂ ⟨b₂, f₂, y₂, _, g₂, rd₂, wr₂, z₂⟩ => ?_)
  -- `Y` stored.
  obtain hrcx : s₂.gpr .rcx = yp s₀ := by
    rw [g₂ _ (by decide), gk₁ _ (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  obtain m0₂ : s₂.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), z₂ _ (by decide) (by decide) 0 (by decide), zk₁ _ (by decide) 0 (by decide)]
    exact hI.a.msk 0 (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (Gcm.X86_64.StitchZ.store16Z_ok .xmm2 .xmm2 .rcx s₂ m0₂
    (by rw [hrcx, wr₂, hwr₁]; exact hp.y_in))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx] at m₆
  obtain hnb : nb s₀ = 16 * e + r := by omega_arith
  obtain eA : ∀ j, A + BitVec.ofNat 64 (16 * j) = bAddr s₀ (16 * e + j) := fun j => by
    show bAddr s₀ (16 * e) + _ = _
    rw [Offset.add_add, ← Nat.mul_add]
  -- What the setup keeps of the memory before it.
  obtain toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) → blockAt s₁.mem p = blockAt s.mem p := fun p hc => by
    rw [m₁, show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  obtain cP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hS : ∀ j < r, blockAt s₁.mem (A + BitVec.ofNat 64 (16 * j)) = blk s₀ (16 * e + j) := fun j hj => by
    obtain hk : 16 * e + j < nb s₀ := by omega_arith
    rw [eA, toS _ (cP _ hk), hI.a.blocks _ hk]
    simp only [show ¬ 16 * e + j < 16 * e by omega_arith, ite_false]
  -- The blocks.
  obtain hb₂ : ∀ k < nb s₀, blockAt s₂.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame f₂ (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        toS _ (cP k hk), hI.a.blocks k hk]
      simp only [hke, ite_true]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_arith⟩
      obtain hj : j < r := by omega_arith
      rw [← eA, b₂ j hj, hS j hj]
  obtain hT : ∀ j < r, s₁.mem.readW (W + BitVec.ofNat 64 (16 * j)) 128 = P ((16 - r + j) / 4) ((16 - r + j) % 4) :=
    fun j hj => by
      obtain hm : 16 - r + j < 16 := by omega_arith
      rw [Offset.add_add, show 256 - 16 * r + 16 * j = 64 * ((16 - r + j) / 4) + 16 * ((16 - r + j) % 4) by omega_arith,
        m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega_arith))).sep
            (Region.contains_self _ _) cw) (by decide)]
      exact hI.pw _ (by omega_arith) _ (by omega_arith)
  obtain yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hb : ∀ k < nb s₀, blockAt s₆.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yD k hk) rfl, hb₂ k hk]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₆.mem (cp s₀) = _
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.d_c.symm.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), la, hI.a.ctr 0 (by decide),
      Nat.add_zero, VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₆.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
    have hbl : blocksAt s₀.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (blk s₀) := rfl
    obtain cg : ∀ l, laneAccG (fun n => blockAt s₁.mem (A + BitVec.ofNat 64 (16 * n)))
        (fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128) y l r =
        laneAccG (fun j => blk s₀ (16 * e + j)) (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y l r :=
      fun l => laneAccG_congr _ l r hS hT
    rw [hbl, m₆, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (show 0 < 2 by decide), y₂]
    simp only [yLanes]
    rw [cg 0, cg 1, cg 2, cg 3, hr r hr1 hr15, hnb, List.range_add, List.map_append, List.map_map]
    simp only [y, ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₆.mem
    obtain F0 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    obtain F1 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    obtain F2 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₁.mem s₂.mem := f₂.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith)⟩
    rw [m₆]
    exact ((F0.trans F1).trans F2).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4
    show s₆.gpr q = _
    rw [g₆, g₂ q h4, gk₁ q h4 h1 h3]
    exact hI.gpr q h1 h2 h3 h4
  · show s₆.rd = _
    rw [rd₆, rd₂]; exact hrd₁
  · show s₆.wr = _
    rw [wr₆, wr₂]; exact hwr₁

end VG.Proof.Gcm.X86_64.StitchZH

end

end

/-!
# The blocks after the last group, decrypted

`loopDR_ok`: the decryption loop, for any number of blocks, stops with
fewer than 16 left (`DInv`). `decTailRG_ok` is `decR` after its setup for any
number of blocks from 16 on: the blocks after the last group, if any, by
`remGD_ok`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre DPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀
  addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep' ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZH (remGD dbody)
open VG.Proof.Gcm.X86_64.StitchZ (DInv DInvM DInv.toM AInv FinOk Ready cmp_ok dfinal_ok)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- `test r9, r9`. -/
theorem test99_ok (s : State) :
    WP isa (.block [.alu .test .r9 (.reg .r9)]) s fun s' =>
      s'.zf = some (s.gpr .r9 &&& s.gpr .r9 == 0) ∧ s'.gpr = s.gpr ∧ (∀ x l, s'.zlane x l = s.zlane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The decryption loop, for any number of blocks: it stops with fewer than 16 left. -/
theorem loopDRM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    {s : State} (hI : DInvM ix s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * e < 16)))
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.ite .b (.block []) (.loop (dbody ix) .ae)) s fun s' => ∃ e, nb s₀ - 16 * e < 16 ∧ DInvM ix s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hle := hI.a.le
  refine WP.ite (decide (nb s₀ - 16 * e < 16)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨e, by simpa using h, hI, hCache⟩
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ DInvM ix s₀ P e s ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s
    have hstep : ∀ m s, I m s → WP isa (dbody ix) s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * e < 16 ∧ DInvM ix s₀ P e s' ∧
          VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI, hCI⟩
      refine WP.mono (dbodyM_ok hp hf he hI hCI) fun s' ⟨hI', hcf', hCI'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * (e + 1) < 16
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          e + 1, hlt, hI', hCI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by omega_using [he], e + 1, rfl, by omega_using [hlt], hI', hCI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e) s ⟨e, rfl, by simp at h; omega_using [h], hI, hCache⟩

theorem loopDR_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    {s : State} (hI : DInv s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * e < 16)))
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.ite .b (.block []) (.loop dbody .ae)) s fun s' => ∃ e, nb s₀ - 16 * e < 16 ∧ DInv s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (loopDRM_ok (Stitch.SPre.toM hp) hf hI.toM hcf hCache) fun _ ⟨e, he, h, hk⟩ => ⟨e, he, h.toDInv, hk⟩

/-- `decR` after the setup, for any number of blocks from 16 on. -/
theorem decTailRG_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOkG (hk s₀) P)
    {bigC : Prog isa} {i : BitVec 32} (t : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 t)
    (ht : t < 2 ^ 64) (hbig : ∀ s, t ≤ nb s₀ → DInv s₀ P 0 s → VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s →
      WP isa bigC s fun s' => ∃ e, DInv s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s')
    {s : State} (hR : Ready s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq (.block [.alu .cmp .r9 (.imm i)]) (.seq (.ite .b (.block []) bigC)
      (.seq (.block [.alu .cmp .r9 (.imm 16)])
        (.seq (.ite .b (.block []) (.loop dbody .ae))
          (.seq (.block [.alu .test .r9 (.reg .r9)])
            (.ite .e (.block (storeCtr ++ storeY)) (.seq (.block [.alu .add .r9 (.imm 16)]) remGD))))))) s
      (DPost s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hI₁ : DInv s₀ P 0 s :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩
  refine WP.seq (WP.mono (WP.hkeep rfl (cmp_ok s i t hi))
    fun s₂ ⟨⟨hcf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₂ := hI₁.of_eq g l m rd wr
  have hCache₂ := hCache.keep hh (hI₂.a.keys hp)
  rw [hI₁.r9, toNat_ofNat_lt (by omega_using [hn]), toNat_ofNat_lt ht] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, DInv s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * 0 < t))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨0, hI₂, hCache₂⟩)
    (fun h => hbig _ (by simp at h; omega_using [h]) hI₂ hCache₂)) fun s₃ ⟨e, hI₃, hCache₃⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp_ok s₃ 16 16 (by decide)))
    fun s₄ ⟨⟨hcf₄, g₄, l₄, m₄, rd₄, wr₄⟩, hh₄⟩ => ?_)
  have hI₄ := hI₃.of_eq g₄ l₄ m₄ rd₄ wr₄
  have hle := hI₃.a.le
  rw [hI₃.r9, toNat_ofNat_lt (by omega_using [hn]), toNat_ofNat_lt (by decide)] at hcf₄
  refine WP.seq (WP.mono (loopDR_ok hp hf hI₄ hcf₄ (hCache₃.keep hh₄ (hI₄.a.keys hp))) fun s₅ ⟨e, hlt, hI₅, hC₅⟩ => ?_)
  have hle₅ := hI₅.a.le
  refine WP.seq (WP.mono (WP.hkeep (by decide) (test99_ok s₅)) fun s₆ ⟨⟨z₆, g₆, l₆, m₆, rd₆, wr₆⟩, hh₆⟩ => ?_)
  have hI₆ := hI₅.of_eq g₆ (fun x l => l₆ x l) m₆ rd₆ wr₆
  have hz : (s₅.gpr .r9 &&& s₅.gpr .r9 == 0) = decide (nb s₀ = 16 * e) := by
    rw [BitVec.and_self, hI₅.r9]
    by_cases h : nb s₀ = 16 * e
    · rw [show nb s₀ - 16 * e = 0 by omega_using [h], decide_eq_true h]; rfl
    · have : BitVec.ofNat 64 (nb s₀ - 16 * e) ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega_using [hle₅, h, this, h0]
      rw [beq_false_of_ne this, decide_eq_false h]
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, z₆, hz]) (fun h => ?_) (fun h => ?_)
  · exact dfinal_ok hp (by simpa using h) hI₆
  · exact remGD_ok hp hr hI₆ hlt (by simpa using h) (hC₅.keep hh₆ (hI₆.a.keys hp))

end VG.Proof.Gcm.X86_64.StitchZH
