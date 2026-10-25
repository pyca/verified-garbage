module

public import VerifiedGarbage.Proof.Dsa.X86.PowMulTiming
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming
import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks
import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.Dsa.X86.PowSteps

/-! # The trace of DSA's exponentiation core

Two runs of the core leak the same trace from the same stack pointer. What
each piece needs of a run (`Wk`: the core's state `St`, the counter where the
code uses it, and the slots that a later call takes as its second operand
below the modulus) each piece keeps: the pieces between calls are checked by
the taint analysis, which needs `edi` (and `esi`, the counter) to agree, and
the calls are related by `mul_relCT`.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

section
variable {n : Nat} {base : Addr} {sp : BitVec 32}

/-- A run of the core: its state `St` from a start at `sp`, the counter
`cnt` in `esi` where known, and the slots `bs` below the modulus. -/
def Wk (n : Nat) (base : Addr) (sp : BitVec 32) (cnt : Option Nat) (bs : List Nat) (u : State) : Prop :=
  ∃ size m s₀, St n m size base s₀ u ∧ s₀.gpr .esp = sp ∧
    (∀ c, cnt = some c → u.gpr .esi = BitVec.ofNat 32 c) ∧
    ∀ b ∈ bs, VG.Proof.Mont.wordsVal u.mem base (slot n b) n < m

theorem Wk.agree {cnt : Option Nat} {bs : List Nat} {s t : State} (W₁ : Wk n base sp cnt bs s)
    (W₂ : Wk n base sp cnt bs t) : VG.X86.Taint.Agree (workspaceTaint cnt.isSome) s t := by
  obtain ⟨_, _, _, S₁, _, c₁, _⟩ := W₁
  obtain ⟨_, _, _, S₂, _, c₂, _⟩ := W₂
  have edi : s.gpr .edi = t.gpr .edi :=
    BitVec.eq_of_toNat_eq (S₁.ctx.scr.edi_toNat.trans S₂.ctx.scr.edi_toNat.symm)
  cases cnt with
  | none => exact agree_regs (rs := [.edi]) fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact edi
  | some c =>
    refine agree_regs (rs := [.edi, .esi]) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact edi
    · rw [c₁ c rfl, c₂ c rfl]

/-- A piece the taint analysis checks, which keeps what `F` says of a run. -/
theorem wk_taint {cnt : Option Nat} {bs : List Nat} {c : Prog isa} {F : State → Prop}
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (hT : (VG.Taint.check taint (workspaceTaint cnt.isSome) c hc).isSome = true)
    (hw : ∀ u, Wk n base sp cnt bs u → WP isa c u F) : RelCT isa (Both (Wk n base sp cnt bs)) c (Both F) :=
  relCT_both (RelCT.taint _ (fun _ _ h => Wk.agree h.1 h.2) hT) hw

/-- `wk_taint` for a run that also meets `X`. -/
theorem wk_taintX {cnt : Option Nat} {bs : List Nat} {c : Prog isa} {X F : State → Prop}
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (hT : (VG.Taint.check taint (workspaceTaint cnt.isSome) c hc).isSome = true)
    (hw : ∀ u, Wk n base sp cnt bs u → X u → WP isa c u F) :
    RelCT isa (Both fun u => Wk n base sp cnt bs u ∧ X u) c (Both F) :=
  relCT_both (RelCT.taint _ (fun _ _ h => Wk.agree h.1.1 h.2.1) hT) fun u h => hw u h.1 h.2

/-- A piece that keeps the core's state, the counter and the slots `bs`. -/
theorem Wk.next {cnt : Option Nat} {bs : List Nat} {u v : State} (W : Wk n base sp cnt bs u)
    (hS : ∀ size m s₀, St n m size base s₀ u → St n m size base s₀ v) (hi : v.gpr .esi = u.gpr .esi)
    (hb : ∀ b ∈ bs, ∀ k ≤ 2 * n, val32 v.mem base (slot n b) k = val32 u.mem base (slot n b) k) :
    Wk n base sp cnt bs v := by
  obtain ⟨size, m, s₀, S, e, c, B⟩ := W
  refine ⟨size, m, s₀, hS _ _ _ S, e, fun c' h => by rw [hi]; exact c c' h, fun b hb' => ?_⟩
  rw [wordsVal_eq_val32, hb b hb' _ (Nat.le_refl _), ← wordsVal_eq_val32]
  exact B b hb'

theorem wk_mul {cnt : Option Nat} {bs bs' : List Nat} (hn : 2 ≤ n) {o a b : Nat}
    (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7) (hb4 : 4 ≤ b) (hb7 : b ≤ 7) (hb : b ∈ bs)
    (hbs : ∀ x ∈ bs, 4 ≤ x ∧ x < 9) (hbs' : ∀ x ∈ bs', x = o ∨ (x ∈ bs ∧ x ≠ o)) :
    RelCT isa (Both (Wk n base sp cnt bs)) (VG.Impl.Dsa.X86.Pow.mul n o a b) (Both (Wk n base sp cnt bs')) := by
  refine relCT_both ((mul_relCT (base := base) sp hn ho ho7 ha ha7 hb4 hb7).mono (fun _ _ h => ⟨?_, ?_⟩) fun _ _ h => h) ?_
  · obtain ⟨size, m, s₀, S, e, _, B⟩ := h.1
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B b hb⟩
  · obtain ⟨size, m, s₀, S, e, _, B⟩ := h.2
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B b hb⟩
  intro u ⟨size, m, s₀, S, e, c, B⟩
  refine WP.mono (mulSt_ok S hn ho ho7 ha ha7 hb4 hb7 (B b hb)) fun v ⟨Sv, iv, L, _, V, _⟩ =>
    ⟨size, m, s₀, Sv, e, fun c' h => by rw [iv]; exact c c' h, fun x hx => ?_⟩
  rcases hbs' x hx with rfl | ⟨hx', hxo⟩
  · exact L
  · have := hbs x hx'
    rw [wordsVal_eq_val32, V x this.1 this.2 hxo _ (Nat.le_refl _), ← wordsVal_eq_val32]
    exact B x hx'

theorem wk_one {cnt : Option Nat} {bs : List Nat} {i : Nat} (hi1 : 1 ≤ i) (hi : i < 9)
    (hbs : ∀ x ∈ bs, x < 9 ∧ x ≠ i) :
    RelCT isa (Both (Wk n base sp cnt bs)) (one n (slot n i)) (Both (Wk n base sp cnt (i :: bs))) :=
  wk_taint (hc := oneHint cnt.isSome) (by rw [one_check]; rfl) fun u ⟨size, m, s₀, S, e, c, B⟩ =>
    WP.mono (oneSt_ok S hi1 hi) fun v ⟨Sv, iv, O, V⟩ =>
      ⟨size, m, s₀, Sv, e, fun c' h => by rw [iv]; exact c c' h, fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [O]; exact S.ctx.gt_one
        · have := hbs x hx
          rw [wordsVal_eq_val32, V x this.1 this.2 _ (Nat.le_refl _), ← wordsVal_eq_val32]
          exact B x hx⟩

/-- `k` squarings of slot 4. -/
theorem wk_squarings (hn : 2 ≤ n) :
    ∀ k, RelCT isa (Both (Wk n base sp none [4])) (squarings n k) (Both (Wk n base sp none [4]))
  | 0 => RelCT.nil fun _ _ h => h
  | k + 1 => VG.RelCT.seq (wk_squarings hn k)
      (wk_mul hn (o := 4) (a := 4) (b := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (List.mem_singleton_self _) (fun x hx => by rw [List.mem_singleton.mp hx]; decide)
        (fun x hx => .inl (List.mem_singleton.mp hx)))

/-- What the core needs of a run on entry. -/
def CoreIn (n : Nat) (base : Addr) (sp : BitVec 32) (u : State) : Prop :=
  ∃ size m, Scr u base size ∧ CallRoom sp base size ∧ u.gpr .esp = sp ∧ contextBytes n ≤ size ∧
    VG.Proof.Mont.wordsVal u.mem base (slot n 0) n = m ∧ 1 < m ∧ m % 2 = 1

theorem setupRanges_core (n : Nat) :
    ∀ r ∈ setupRanges n, ∃ c ∈ coreRanges n, c.1 ≤ r.1 ∧ r.1 + r.2 ≤ c.1 + c.2 := by
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b8
  intro r hr
  simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0, 8), List.mem_cons_self .., by decide, by decide⟩
  all_goals exact in_core (by decide) (by simp only [contextBytes, slot_lin] at b8 ⊢; omega_arith)

theorem contextSeed_check (n bits : Nat) :
    VG.Taint.check taint (workspaceTaint false) (contextSeed n bits) contextSetupHint = some counterEndTaint :=
  exponent_check_seq taint
    (exponent_check_seq taint (setupInverse_taint false (slot n 0) 0) (by rfl)
      (one_check false n (slot n 3))) (by rfl)
    (powerTwo_check (contextMod n) (slot n 2) (slot n 4) bits)

theorem wk_seed (hn : 2 ≤ n) (hn48 : n ≤ 48) :
    RelCT isa (Both (CoreIn n base sp)) (contextSeed n (65 * n)) (Both (Wk n base sp none [4])) := by
  refine relCT_both (RelCT.taint (A := taint) (hc := contextSetupHint) (workspaceTaint false) (fun s t h => ?_)
    (by rw [contextSeed_check]; rfl)) ?_
  · obtain ⟨_, _, h₁, -⟩ := h.1
    obtain ⟨_, _, h₂, -⟩ := h.2
    exact agree_regs (rs := [.edi]) fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact BitVec.eq_of_toNat_eq (h₁.edi_toNat.trans h₂.edi_toNat.symm)
  · intro u ⟨size, m, hs, R, e, hz, hv, hm1, hodd⟩
    refine WP.mono (contextSeed_ok (bits := 65 * n) hs (by omega_arith) (by omega_arith) (by omega_arith) hz hv hm1 hodd)
      fun v ⟨Cv, _, Xv, Ov, Kv⟩ => ?_
    rw [← e] at R
    refine ⟨size, m, u, ⟨Cv, R, Kv, (OutsS.of_outs Ov).core (setupRanges_core n)⟩, e, ?_, fun b hb => ?_⟩
    · intro c h; cases h
    · rw [List.mem_singleton.mp hb, Xv]
      exact Nat.mod_lt _ (by omega_arith)

theorem wk_encode (hn : 2 ≤ n) :
    RelCT isa (Both (Wk n base sp none [4])) (encode n) (Both (Wk n base sp none [5])) := by
  unfold encode
  refine VG.RelCT.seq (wk_one (bs := [4]) (i := 7) (by decide) (by decide)
    (fun x hx => by rw [List.mem_singleton.mp hx]; decide)) ?_
  refine VG.RelCT.seq (wk_mul (bs' := [4]) hn (o := 6) (a := 4) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp)) ?_
  exact wk_mul hn (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by simp) (by simp)

theorem wk_start (e : Nat) :
    RelCT isa (Both (Wk n base sp none [5])) (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * e)))])
      (Both (Wk n base sp (some (32 * e)) [5])) :=
  wk_taint (hc := .block []) rfl fun u W => wp_movS rfl fun v U _ => WP.block_nil (by
    obtain ⟨size, m, s₀, S, e', _, B⟩ := W
    have K : Keeps powerClob u v := U.keeps.mono (by decide)
    refine ⟨size, m, s₀, ⟨⟨S.ctx.scr.of_keeps K (by decide), S.ctx.size_le, U.mem ▸ S.ctx.modulus, S.ctx.gt_one,
      U.mem ▸ S.ctx.inverse⟩, S.room, S.keeps.trans K, U.mem ▸ S.mem⟩, e', fun c h => ?_, fun b hb => ?_⟩
    · cases h; exact U.gpr
    · rw [U.mem]; exact B b hb)

/-- The header's mask word is a mask. -/
def MaskOk (base : Addr) (u : State) : Prop :=
  ∃ bit : Bool, u.mem.readW (off base 4) 32 = if bit then BitVec.allOnes 32 else 0

theorem wk_mulMask {cnt : Option Nat} (hn : 2 ≤ n) :
    RelCT isa (Both fun u => Wk n base sp cnt [5] u ∧ MaskOk base u) (VG.Impl.Dsa.X86.Pow.mul n 7 6 5)
      (Both fun u => Wk n base sp cnt [5] u ∧ MaskOk base u) := by
  refine relCT_both ((mul_relCT (base := base) sp hn (o := 7) (a := 6) (b := 5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).mono (fun _ _ h => ⟨?_, ?_⟩) fun _ _ h => h) ?_
  · obtain ⟨⟨size, m, s₀, S, e, _, B⟩, _⟩ := h.1
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B 5 (by simp)⟩
  · obtain ⟨⟨size, m, s₀, S, e, _, B⟩, _⟩ := h.2
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B 5 (by simp)⟩
  intro u ⟨⟨size, m, s₀, S, e, c, B⟩, bit, hm⟩
  refine WP.mono (mulSt_ok S hn (o := 7) (a := 6) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (B 5 (by simp))) fun v ⟨Sv, iv, _, _, V, M⟩ =>
    ⟨⟨size, m, s₀, Sv, e, fun c' h => by rw [iv]; exact c c' h, fun x hx => ?_⟩, bit, by rw [M, hm]⟩
  rw [List.mem_singleton.mp hx, wordsVal_eq_val32, V 5 (by decide) (by decide) (by decide) _ (Nat.le_refl _),
    ← wordsVal_eq_val32]
  exact B 5 (by simp)

theorem wk_step {e j : Nat} (hn : 2 ≤ n) (he : 2 ≤ e) (hen : e ≤ 2 * n) (hj : 0 < j) (hj32 : j < 2 ^ 32) :
    RelCT isa (Both (Wk n base sp (some j) [5])) (step n e)
      (Both fun u => Wk n base sp (some (j - 1)) [5] u ∧ u.zf = some (decide (j = 1))) := by
  have keep5 : ∀ {u v : State} {size m : Nat} {s₀ : State}, St n m size base s₀ v →
      v.gpr .esi = u.gpr .esi → (∀ k ≤ 2 * n, val32 v.mem base (slot n 5) k = val32 u.mem base (slot n 5) k) →
      Wk n base sp (some j) [5] u → (∀ b ∈ [5], VG.Proof.Mont.wordsVal u.mem base (slot n b) n < m) →
      s₀.gpr .esp = sp → (∀ c, some j = some c → u.gpr .esi = BitVec.ofNat 32 c) →
      Wk n base sp (some j) [5] v := by
    intro u v size m s₀ Sv iv V _ B e c
    refine ⟨size, m, s₀, Sv, e, fun c' h => by rw [iv]; exact c c' h, fun x hx => ?_⟩
    rw [List.mem_singleton.mp hx, wordsVal_eq_val32, V _ (Nat.le_refl _), ← wordsVal_eq_val32]
    exact B 5 (by simp)
  unfold step
  refine VG.RelCT.seq (wk_taint (hc := .block []) (F := fun u => Wk n base sp (some j) [5] u ∧ MaskOk base u)
    ((congrArg Option.isSome (exponentMask_taint (slot n 8) 4)).trans rfl)
    fun u W => ?_) ?_
  · obtain ⟨size, m, s₀, S, e', c, B⟩ := W
    exact WP.mono (maskSt_ok S) fun v ⟨Sv, iv, M, V⟩ =>
      ⟨keep5 Sv iv (V 5 (by decide)) ⟨size, m, s₀, S, e', c, B⟩ B e' c,
        decide (w32 u.mem base (slot n 8) % 2 = 1), by rw [M]; simp only [decide_eq_true_eq]⟩
  refine VG.RelCT.seq (wk_mulMask hn) ?_
  refine VG.RelCT.seq (wk_taintX (cnt := some j) (hc := selectHint) (F := Wk n base sp (some j) [5])
    ((congrArg Option.isSome (selectProduct_check (contextMod n) (slot n 6) (slot n 7) 4)).trans rfl)
    fun u W ⟨bit, M⟩ => ?_) ?_
  · obtain ⟨size, m, s₀, S, e', c, B⟩ := W
    exact WP.mono (selectSt_ok S M) fun v ⟨Sv, iv, _, V⟩ =>
      keep5 Sv iv (V 5 (by decide) (by decide)) ⟨size, m, s₀, S, e', c, B⟩ B e' c
  refine VG.RelCT.seq (wk_mul (bs' := [5]) hn (o := 5) (a := 5) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp)) ?_
  refine VG.RelCT.seq (wk_taint (cnt := some j) (hc := shiftDownHint) (F := Wk n base sp (some j) [5])
    ((congrArg Option.isSome (shiftDown_check e (slot n 8))).trans rfl) fun u W => ?_) ?_
  · obtain ⟨size, m, s₀, S, e', c, B⟩ := W
    exact WP.mono (shiftSt_ok S he hen) fun v ⟨Sv, iv, _, V⟩ =>
      keep5 Sv iv (V 5 (by decide) (by decide)) ⟨size, m, s₀, S, e', c, B⟩ B e' c
  refine wk_taint (cnt := some j) (hc := .block []) rfl fun u W => ?_
  obtain ⟨size, m, s₀, S, e', c, B⟩ := W
  have hc := c j rfl
  refine wp_subS rfl fun v uv _ => ?_
  refine wp_cmpS rfl fun w fw zw => WP.block_nil ?_
  have mw : w.mem = u.mem := fw.mem.trans uv.mem
  have kw : Keeps powerClob u w := (uv.keeps.mono (by decide)).trans (fw.keeps _)
  refine ⟨⟨size, m, s₀, ⟨⟨S.ctx.scr.of_keeps kw (by decide), S.ctx.size_le, mw ▸ S.ctx.modulus, S.ctx.gt_one,
    mw ▸ S.ctx.inverse⟩, S.room, S.keeps.trans kw, mw ▸ S.mem⟩, e', fun c' h => ?_, fun b hb => ?_⟩, ?_⟩
  · cases h; rw [fw.gpr, uv.gpr, hc, counter_sub hj32 hj]
  · rw [mw]; exact B b hb
  · rw [zw, uv.gpr, hc, counter_sub hj32 hj, counter_zero hj32 hj]

theorem wk_loop {e : Nat} (hn : 2 ≤ n) (he : 2 ≤ e) (hen : e ≤ 2 * n) (j : Nat) :
    RelCT isa (fun s t => 0 < j ∧ j < 2 ^ 32 ∧ Both (Wk n base sp (some j) [5]) s t) (.loop (step n e) .ne)
      (Both (Wk n base sp (some 0) [5])) := by
  refine VG.RelCT.loop (M := isa) (I := fun j s t => 0 < j ∧ j < 2 ^ 32 ∧ Both (Wk n base sp (some j) [5]) s t)
    (fun j => ?_) j
  by_cases hj : 0 < j ∧ j < 2 ^ 32
  · refine (wk_step hn he hen hj.1 hj.2).mono (fun _ _ h => h.2.2) ?_
    rintro s t ⟨⟨W₁, z₁⟩, ⟨W₂, z₂⟩⟩
    have e₁ : isa.eval .ne s = some (!decide (j = 1)) := by show s.zf.map (!·) = _; rw [z₁]; rfl
    have e₂ : isa.eval .ne t = some (!decide (j = 1)) := by show t.zf.map (!·) = _; rw [z₂]; rfl
    refine ⟨e₁.trans e₂.symm, fun h => ?_, fun h => ?_⟩
    · rw [e₁] at h
      have d : j = 1 := by simpa using h
      rw [d] at W₁ W₂
      exact ⟨W₁, W₂⟩
    · rw [e₁] at h
      have : j ≠ 1 := by simpa using h
      exact ⟨j - 1, by omega_arith, by omega_arith, by omega_arith, W₁, W₂⟩
  · exact VG.RelCT.of_false fun _ _ h => hj ⟨h.1, h.2.1⟩

theorem wk_finish {cnt : Option Nat} (hn : 2 ≤ n) :
    RelCT isa (Both (Wk n base sp cnt [])) (finish n) (fun _ _ => True) := by
  unfold finish
  refine VG.RelCT.seq (wk_one (bs := []) (i := 7) (by decide) (by decide) (by simp)) ?_
  refine (mul_relCT (base := base) sp hn (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono (fun _ _ h => ⟨?_, ?_⟩) fun _ _ h => h
  · obtain ⟨size, m, s₀, S, e, _, B⟩ := h.1
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B 7 (by simp)⟩
  · obtain ⟨size, m, s₀, S, e, _, B⟩ := h.2
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B 7 (by simp)⟩

theorem core_relCT {e : Nat} (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n) :
    RelCT isa (Both (CoreIn n base sp)) (core n e) (fun _ _ => True) := by
  unfold core setup
  refine VG.RelCT.seq (VG.RelCT.seq (wk_seed hn hn48) (wk_squarings hn 6)) ?_
  refine VG.RelCT.seq (wk_encode hn) ?_
  refine VG.RelCT.seq (wk_start e) ?_
  refine VG.RelCT.seq ((wk_loop hn he hen (32 * e)).mono (fun _ _ h => ⟨by omega_arith, by omega_arith, h⟩) fun _ _ h => h) ?_
  refine (wk_finish (base := base) (sp := sp) (cnt := some 0) hn).mono (fun _ _ h => ⟨?_, ?_⟩) fun _ _ h => h
  · obtain ⟨size, m, s₀, S, e', c, _⟩ := h.1
    exact ⟨size, m, s₀, S, e', c, fun _ h => nomatch h⟩
  · obtain ⟨size, m, s₀, S, e', c, _⟩ := h.2
    exact ⟨size, m, s₀, S, e', c, fun _ h => nomatch h⟩

end

end VG.Proof.Dsa.X86.Pow
