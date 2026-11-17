module

import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ZCore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! ### `Bignum.X86_64.Ifma.Tab`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.Ifma.Sel`, which this module and modules that import it used -/

section

/-!
# RSA with AVX512_IFMA on x86-64, any size: reading an entry of the table

`select l p` reads the digit `v` (below `T = 2^w`), the
quadword at `oV` of prime `p`'s region, and copies entry `v` of the table
(`NB` bytes at `oTab + NB v`) to `oS`, reading every entry and keeping entry
`v` under a mask (`select_ok`). The vector part of an iteration is run by
`ESym` and checked for each layout (`checkSel`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (Ctx Keeps selMask selMask_ok selMask_and zero_or64 or_zero64
  wrList wrList_outside' word_wrList_unique off_add setOff)
open VG.Proof.MlKem.X86_64 (Keep)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

theorem ea_rG {s : State} {r : Reg} {a : Addr} (h : s.gpr r = a) (d : Nat) :
    s.ea (at_ r d) = a + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, h]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem vreg_lo : ∀ k < 16, ∃ x, vreg k = .lo x := by
  intro k hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | exact ⟨_, rfl⟩ | omega_arith

theorem qv_lo {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) {k : Nat} (hk : k < 16) (j : Nat) :
    qv s' (vreg k) j = qv s (vreg k) j := by
  obtain ⟨x, e⟩ := vreg_lo k hk
  rw [e]; simp only [qv, State.vy, State.ymm, hx, hy]

/-- Any of the thirty-two registers, through writes that keep all three banks. -/
theorem qv_all {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) (hH : s'.ymmH = s.ymmH) {k : Nat}
    (j : Nat) : qv s' (vreg k) j = qv s (vreg k) j := by
  cases h : vreg k with
  | lo x => simp only [qv, State.vy, State.ymm, hx, hy]
  | hi x => simp only [qv, State.vy, hH]

/-! ## The vector part of an iteration -/

/-- The loads under the mask (in `vreg R`), OR'ed into the accumulators. -/
def selVec (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  [.eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] ++
  ((List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .r8 (32 * k)),
    .eop (.vpternlogq (vreg k) (vreg (l.R + 1)) (vreg l.R) 0xF8)])

def selLim (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Reg → Nat := fun b => if b = .r8 then l.NB else 0

def selTerm (k : Nat) : T := .or (.reg k) (.and (.ld .r8 (32 * k)) (.bc (.lane0 (.gpr .rax))))

def checkSel (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Bool :=
  match ESym.init.run (selLim l) (selVec l) with
  | some σ => (List.range l.R).all fun k => decide (σ.reg k = selTerm k)
  | none => false

theorem checkSel_ok (hl : AmmOk l) : checkSel l = true := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem selVec_ok (hl : AmmOk l) {s : State} (hc : Ctx (selLim l) s) :
    WP isa (.block (selVec l)) s fun s' =>
      (∀ k < l.R, ∀ j < 4, qv s' (vreg k) j =
        qv s (vreg k) j ||| (s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (32 * k + 8 * j)) 64 &&& s.gpr .rax)) ∧
      Keeps s s' := by
  obtain ⟨_, hR10⟩ := hl.bounds
  have h := checkSel_ok hl
  unfold checkSel at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok hc (SRel.init s) hσ) fun s' hs => ⟨fun k hk j hj => ?_,
      ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    · rw [hs.reg _ j hj, vi_vreg k (by omega_arith), h k hk]
      simp only [selTerm, T.eval, ite_true, AmmSym.G.eval]
  · cases h

/-! ## An iteration -/

theorem NB_lt (hl : AmmOk l) : l.NB < 2 ^ 31 := by
  have := hl.D_bounds; omega_arith

/-- The table's entries: `T = 2^w`, 16 or 32. -/
theorem AmmOk.T_bounds (hl : AmmOk l) : 16 ≤ l.T ∧ l.T ≤ 32 := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The entry's end: the next entry, `ZF` after the last. -/
theorem selTail_ok (hl : AmmOk l) {s : State} {base : Addr} {i : Nat} (hi : i < l.T)
    (h8 : s.gpr .r8 = base + BitVec.ofNat 64 (l.NB * i)) (hc : s.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .add .r8 (.imm (BitVec.ofNat 32 l.NB)), .alu .add .rcx (.imm 1),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 l.T))])
      s fun s' =>
      s'.gpr .r8 = base + BitVec.ofNat 64 (l.NB * (i + 1)) ∧ s'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧
      s'.zf = some (decide (i + 1 = l.T)) ∧ Keep [.r8, .rcx] s s' ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr ∧ s'.ymmH = s.ymmH := by
  have sx := AmmSym.se_ofNat (NB_lt hl)
  have hT := hl.T_bounds
  have tx := AmmSym.se_ofNat (show l.T < 2 ^ 31 by omega_arith)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .rcx] (Q := fun s' =>
    s'.gpr .r8 = base + BitVec.ofNat 64 (l.NB * (i + 1)) ∧ s'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧
      s'.zf = some (decide (i + 1 = l.T)) ∧ s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧
      s'.mxcsr = s.mxcsr ∧ s'.ymmH = s.ymmH) (by
    xrun [h8, hc, sx, tx, ofNat_add_one]
    and_intros
    any_goals rfl
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [ofNat_sub_beq (by omega_arith) (by omega_arith)]) rfl)
    fun s' ⟨⟨a, b, c, d, e, f, g, h⟩, k⟩ => ⟨a, b, c, k, d, e, f, g, h⟩

/-- After entries below `i` of the table at `base`, `v` the entry to read. -/
structure SelInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (t₀ : State) (base : Addr) (v i : Nat) (t : State) : Prop where
  r8 : t.gpr .r8 = base + BitVec.ofNat 64 (l.NB * i)
  rcx : t.gpr .rcx = BitVec.ofNat 64 i
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → t.gpr r = t₀.gpr r
  mem : t.mem = t₀.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mxcsr : t.mxcsr = t₀.mxcsr
  acc : ∀ k < l.R, ∀ j < 4, qv t (vreg k) j =
    if v < i then t₀.mem.readW (base + BitVec.ofNat 64 (l.NB * v + 32 * k + 8 * j)) 64 else 0

def selBody (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  [.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] ++
  ((List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .r8 (32 * k)),
    .eop (.vpternlogq (vreg k) (vreg (l.R + 1)) (vreg l.R) 0xF8)]) ++
  [.alu .add .r8 (.imm (BitVec.ofNat 32 l.NB)), .alu .add .rcx (.imm 1), .alu .cmp .rcx (.imm (BitVec.ofNat 32 l.T))]

/-- Entry `i`. -/
theorem selIter_ok (hl : AmmOk l) {t₀ t : State} {base : Addr} {v i : Nat} (hv : v < l.T) (hi : i < l.T)
    (hd : t₀.gpr .rdx = BitVec.ofNat 64 v)
    (hin : ∀ i < l.T, ∀ d n, 0 < n → d + n ≤ l.NB →
      InRegions (t₀.rd ++ t₀.wr) (base + BitVec.ofNat 64 (l.NB * i + d)) n)
    (h : SelInv l t₀ base v i t) :
    WP isa (.block (selBody l)) t fun t' => SelInv l t₀ base v (i + 1) t' ∧ t'.zf = some (decide (i + 1 = l.T)) := by
  obtain ⟨_, hR10⟩ := hl.bounds
  have hT := hl.T_bounds
  rw [show selBody l = [.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
    .alu .sbb .rax (.reg .rax)] ++ (selVec l ++ [.alu .add .r8 (.imm (BitVec.ofNat 32 l.NB)), .alu .add .rcx (.imm 1),
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 l.T))]) by simp only [selBody, selVec, List.cons_append, List.nil_append],
    WP.block_append_iff]
  have hdx : t.gpr .rdx = BitVec.ofNat 64 v := (h.gpr _ (by decide) (by decide) (by decide)).trans hd
  refine WP.mono (selMask_ok (by omega_arith) (by omega_arith) h.rcx hdx) fun t₁ ⟨m₁, k₁, me₁, x₁, y₁, mx₁, h₁⟩ => ?_
  have r8₁ : t₁.gpr .r8 = base + BitVec.ofNat 64 (l.NB * i) := by rw [k₁.gpr (by decide)]; exact h.r8
  have hc : Ctx (selLim l) t₁ := fun b d n hn hdn => by
    by_cases b8 : b = .r8
    · subst b8
      simp only [selLim, ite_true] at hdn
      rw [r8₁, k₁.2.1, k₁.2.2, h.rd, h.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hin i hi d n hn hdn
    · simp only [selLim, b8, ite_false] at hdn; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (selVec_ok hl hc) fun t₂ ⟨v₂, k₂⟩ => ?_
  refine WP.mono (selTail_ok (base := base) hl hi (by rw [k₂.gpr _ (by decide)]; exact r8₁)
    (by rw [k₂.gpr _ (by decide), k₁.gpr (by decide)]; exact h.rcx))
    fun t₄ ⟨r8₄, rcx₄, z₄, k₄, me₄, x₄, y₄, mx₄, h₄⟩ => ⟨⟨r8₄, rcx₄, fun r r1 r2 r3 => ?_, ?_, ?_, ?_, ?_,
      fun k hk j hj => ?_⟩, z₄⟩
  · rw [k₄.gpr (by simp [r2, r3]), k₂.gpr _ r1, k₁.gpr (by simp [r1])]; exact h.gpr r r1 r2 r3
  · rw [me₄, k₂.mem, me₁, h.mem]
  · rw [k₄.2.1, k₂.rd, k₁.2.1, h.rd]
  · rw [k₄.2.2, k₂.wr, k₁.2.2, h.wr]
  · rw [mx₄, k₂.mxcsr, mx₁, h.mxcsr]
  · rw [qv_all x₄ y₄ h₄, v₂ k hk j hj, qv_all x₁ y₁ h₁, m₁, h.acc k hk j hj, me₁, h.mem, r8₁,
      selMask_and]
    by_cases hiv : i = v
    · subst hiv
      simp only [Nat.lt_irrefl, ite_false, decide_true, ite_true, Nat.lt_succ_self, zero_or64]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
    · simp only [hiv, decide_false, Bool.false_eq_true, ite_false, or_zero64]
      by_cases hlt : v < i
      · simp only [hlt, show v < i + 1 by omega_arith, ite_true]
      · simp only [hlt, show ¬ v < i + 1 by omega_arith, ite_false]

/-- The loop over the `T` entries, from entry `T - n`. -/
theorem selLoop_ok (hl : AmmOk l) {t₀ : State} {base : Addr} {v : Nat} (hv : v < l.T)
    (hd : t₀.gpr .rdx = BitVec.ofNat 64 v)
    (hin : ∀ i < l.T, ∀ d n, 0 < n → d + n ≤ l.NB →
      InRegions (t₀.rd ++ t₀.wr) (base + BitVec.ofNat 64 (l.NB * i + d)) n) :
    ∀ n t, 1 ≤ n → n ≤ l.T → SelInv l t₀ base v (l.T - n) t →
      WP isa (.loop (.block (selBody l)) .ne) t (SelInv l t₀ base v l.T) := by
  intro n t h1 h16 hI
  refine WP.loop (M := isa) (body := .block (selBody l)) (c := .ne) (Q := SelInv l t₀ base v l.T)
    (fun n t => 1 ≤ n ∧ n ≤ l.T ∧ SelInv l t₀ base v (l.T - n) t) ?_ n t ⟨h1, h16, hI⟩
  intro n t ⟨h1, h16, hI⟩
  refine WP.mono (selIter_ok hl hv (by omega_arith) hd hin hI) fun t' ⟨hI', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · rw [show l.T - 1 + 1 = l.T by omega_arith] at hI'
    exact .inl ⟨by simp only [show l.T - 1 + 1 = l.T by omega_arith, decide_true, Bool.not_true], hI'⟩
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (l.T - n + 1 = l.T) by omega_arith), Bool.not_false], n - 1,
      by omega_arith, by omega_arith, by omega_arith, by rw [show l.T - (n - 1) = l.T - n + 1 by omega_arith]; exact hI'⟩

/-! ## The whole selection -/

/-- The zeroing of the `R` accumulators. -/
def zerosR (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  (List.range l.R).map fun k => .eop (.bin .vpxorq (vreg k) (vreg k) (vreg k))

def checkZerosR (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Bool :=
  match ESym.init.run (fun _ => 0) (zerosR l) with
  | some σ => (List.range l.R).all fun r => decide (σ.reg r = .zero)
  | none => false

theorem checkZerosR_ok (hl : AmmOk l) : checkZerosR l = true := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem zerosR_ok (hl : AmmOk l) {s : State} :
    WP isa (.block (zerosR l)) s fun s' => (∀ r < l.R, ∀ t < 4, qv s' (vreg r) t = 0) ∧ Keeps s s' := by
  obtain ⟨_, hR10⟩ := hl.bounds
  have h := checkZerosR_ok hl
  unfold checkZerosR at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok (fun b d n hn hd => absurd hd (by omega_arith)) (SRel.init s) hσ) fun s' hs =>
      ⟨fun r hr t ht => ?_, ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    rw [hs.reg _ t ht, vi_vreg r (by omega_arith), h r hr]; rfl
  · cases h

/-- The digit `select` reads: the quadword at `oV`. -/
def nib (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (p : Nat) : Nat := (word m B (l.D * p + l.oV)).toNat

theorem oV_bounds (hl : AmmOk l) : l.oTab + l.T * l.NB ≤ l.oV ∧ l.oS + l.NB ≤ l.oTab ∧ l.oV + 8 ≤ l.D := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `[S] := T_v` for prime `p`. -/
theorem select_ok (hl : AmmOk l) {s : State} {B : Addr} {p : Nat} (hp : p < l.nl) (hB : s.gpr .rbx = B)
    (hs : Scr s B (l.nl * l.D)) (hv : nib l s.mem B p < l.T) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (select l p)) s fun s' =>
      (∀ q < l.L, limb l s'.mem B (l.D * p + l.oS) q = limb l s.mem B (l.D * p + l.oTab + l.NB * nib l s.mem B p) q) ∧
      Outside B (l.D * p + l.oS) l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3⟩ := oV_bounds hl
  have hn := hs.nowrap
  have hDp : l.D * p ≤ l.D ∧ l.D * p + l.D ≤ l.nl * l.D ∧ l.nl * l.D ≤ 2 * l.D := ⟨D_le hl hp, lane_end hl hp, (nlD_le hl).2⟩
  have hle := lane_end hl hp
  have rdS : ∀ d n, 0 < n → d + n ≤ l.nl * l.D → InRegions (s.rd ++ s.wr) (off B d) n := fun d n hn hd =>
    let ⟨_, h, c⟩ := hs.region hd hn; ⟨_, List.mem_append_right _ h, c⟩
  let v := nib l s.mem B p
  have hT := hl.T_bounds
  let base := off B (l.D * p + l.oTab)
  refine WP.seq ?_
  rw [List.append_assoc]
  refine setOff (c := l.D * p + l.oTab) (by omega_arith) fun s₁ u₁ => ?_
  rw [hB] at u₁
  change WP isa (.block (([.mov .rdx (.mem (at_ .rbx (l.D * p + l.oV))),
    .mov32 .rcx (.imm 0)] : List Instr) ++ zerosR l)) s₁ _
  rw [WP.block_append_iff]
  have rbx₁ : s₁.gpr .rbx = B := by rw [u₁.other _ (by decide), hB]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 v ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧ t.xmm = s₁.xmm ∧ t.ymmHi = s₁.ymmHi ∧ t.mxcsr = s.mxcsr) (by
    have hld : InRegions (s₁.rd ++ s₁.wr) (B + BitVec.ofNat 64 (l.D * p + l.oV)) 8 := by
      rw [u₁.rd, u₁.wr]; exact rdS _ 8 (by decide) (by omega_arith)
    xrun [ea_rG rbx₁, hld, u₁.mem]
    and_intros
    any_goals rfl
    · simp only [v, nib, word, off, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · exact u₁.mxcsr) rfl) fun s₂ ⟨⟨dx₂, cx₂, me₂, x₂, y₂, mx₂⟩, k₂⟩ => ?_
  refine WP.mono (zerosR_ok hl) fun s₃ ⟨z₃, k₃⟩ => ?_
  have hin : ∀ i < l.T, ∀ d n, 0 < n → d + n ≤ l.NB →
      InRegions (s₃.rd ++ s₃.wr) (base + BitVec.ofNat 64 (l.NB * i + d)) n := fun i hi d n hn hdn => by
    rw [k₃.rd, k₃.wr, k₂.2.1, k₂.2.2, u₁.rd, u₁.wr, off_add]
    have : l.NB * i + l.NB ≤ l.T * l.NB := by
      rw [Nat.mul_comm l.T, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    exact rdS _ n hn (by omega_arith)
  have dx₃ : s₃.gpr .rdx = BitVec.ofNat 64 v := by rw [k₃.gpr _ (by decide)]; exact dx₂
  have i₀ : SelInv l s₃ base v (l.T - l.T) s₃ := Nat.sub_self l.T ▸ ⟨by
      rw [k₃.gpr _ (by decide), k₂.gpr (by decide), u₁.self]; exact (BitVec.add_zero _).symm,
    by rw [k₃.gpr _ (by decide)]; exact cx₂, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl,
    fun k hk j hj => by rw [z₃ k hk j hj]; simp⟩
  refine WP.seq (WP.mono (selLoop_ok hl hv dx₃ hin l.T s₃ (by omega_arith) (Nat.le_refl _) i₀) fun s₄ h₄ => ?_)
  let Ls : List (Nat × VReg) := (List.range l.R).map fun k => (l.D * p + l.oS + 32 * k, vreg k)
  have rbx₄ : s₄.gpr .rbx = B := by
    rw [h₄.gpr _ (by decide) (by decide) (by decide), k₃.gpr _ (by decide), k₂.gpr (by decide), rbx₁]
  have wr₄ : s₄.wr = s.wr := by rw [h₄.wr, k₃.wr, k₂.2.2, u₁.wr]
  have rd₄ : s₄.rd = s.rd := by rw [h₄.rd, k₃.rd, k₂.2.1, u₁.rd]
  have me₄ : s₄.mem = s.mem := by rw [h₄.mem, k₃.mem, me₂]
  rw [show ((List.range l.R).map fun k => Instr.evStore (at_ .rbx (l.D * p + l.oS + 32 * k)) (vreg k)) =
    storeCode .rbx Ls by simp only [storeCode, Ls, List.map_map, Function.comp_def]]
  have hL : ∀ x ∈ Ls, l.D * p + l.oS ≤ x.1 ∧ x.1 + 32 ≤ l.D * p + l.oS + l.NB := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hk; dsimp only; simp only [Lay.NB]; omega_arith
  refine WP.mono (stores_gen Ls s₄ rbx₄ fun x hx => by
    have := hL x hx
    rw [wr₄]; exact let ⟨_, h, c⟩ := hs.region (d := x.1) (n := 32) (by omega_arith) (by decide);
      ⟨_, h, c⟩) fun s' hs' => ?_
  subst hs'
  refine ⟨fun q hq => ?_, ?_, fun r r1 r2 r3 r4 => ?_, rd₄, wr₄, ?_⟩
  · have hk : q % l.R < l.R := Nat.mod_lt _ (by omega_arith)
    have ht : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    have e := word_wrList_unique B (e := l.D * p + l.oS + 32 * (q % l.R)) (t := q / l.R)
      (v := s₄.vy (vreg (q % l.R))) ht (by simp only [Lay.NB] at *; omega_arith)
      (Ls.map fun x => (x.1, s₄.vy x.2)) s₄.mem
      (List.mem_map.2 ⟨(l.D * p + l.oS + 32 * (q % l.R), vreg (q % l.R)),
        List.mem_map.2 ⟨q % l.R, List.mem_range.2 hk, rfl⟩, rfl⟩)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hy
        rw [List.mem_range] at hk'; dsimp only; simp only [Lay.NB] at *; omega_arith)
      (fun x hx he => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hy
        rw [List.mem_range] at hk'; dsimp only at he ⊢
        rw [show k = q % l.R by omega_arith])
    have qq := h₄.acc (q % l.R) hk (q / l.R) ht
    simp only [hv, ite_true] at qq
    show (word (wrList s₄.mem B _) B (l.D * p + l.oS + l.off q)).toNat = _
    rw [show l.D * p + l.oS + l.off q = l.D * p + l.oS + 32 * (q % l.R) + 8 * (q / l.R) by
      unfold Lay.off; omega_arith, e]
    refine congrArg BitVec.toNat (qq.trans ?_)
    rw [k₃.mem, me₂, off_add]
    exact congrArg (fun d => s.mem.readW (off B d) 64) (by unfold Lay.off; omega_arith)
  · have o := wrList_outside' B (o := l.D * p + l.oS) (n := l.NB) (by omega_arith)
      (Ls.map fun x => (x.1, s₄.vy x.2)) s₄.mem fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hL y hy
    exact fun x hx => (o x hx).trans (congrFun me₄ x)
  · show s₄.gpr r = _
    rw [h₄.gpr _ r1 r2 r4, k₃.gpr _ r1, k₂.gpr (by simp [r2, r3]), u₁.other _ r4]
  · show s₄.mxcsr = _
    rw [h₄.mxcsr, k₃.mxcsr, mx₂]

end VG.Proof.Bignum.X86_64.Ifma

end

end

/-! ### `Bignum.X86_64.Ifma.Area`, which this module and modules that import it used -/

section

/-!
# RSA with AVX512_IFMA on x86-64, any size: the regions as numbers

The facts about each prime's region that every
multiplication needs (`Ar`: the modulus `M p` at `oM` in `4 R` limbs of 52
bits, with `4 M p ≤ 2^(208 R)`, and `k₀` at `oK0`); numbers below `2 M p`
in limbs of 52 bits (`Good`); and both kept by writes elsewhere
(`Out2.word_at`, `Ar.of_out2`, `Good.of_out2`). `amm2_ok` is `amm_ok` in
these terms.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (setOff)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The facts of both regions about their moduli. -/
structure Ar0 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M k : Nat → Nat) : Prop where
  mlt : ∀ p < l.nl, ∀ j < l.L, limb l m B (l.D * p + oM) j < 2 ^ 52
  mv : ∀ p < l.nl, val52 l m B (l.D * p + oM) = M p
  kw : ∀ p < l.nl, ∀ t < 4, word m B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p)
  klt : ∀ p < l.nl, k p < 2 ^ 52
  k0 : ∀ p < l.nl, (limb l m B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0
  bnd : ∀ p < l.nl, 4 * M p ≤ 2 ^ (52 * l.S)

/-- With `ammCoreZ`: the number `m` at `oMs`, of at most `4 R - 2` limbs, for
which the multiplications reduce by `2¹⁰⁴ m - 1`, a multiple of the modulus
`M p` that is at most `2^(52 S - 16)`. -/
structure ArZ (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M : Nat → Nat) : Prop where
  lt : ∀ p < l.nl, ∀ j < l.L, limb l m B (l.D * p + l.oMs) j < 2 ^ 52
  top : ∀ p < l.nl, limb l m B (l.D * p + l.oMs) (l.L - 2) = 0 ∧ limb l m B (l.D * p + l.oMs) (l.L - 1) = 0
  pos : ∀ p < l.nl, 1 ≤ val52 l m B (l.D * p + l.oMs)
  dvd : ∀ p < l.nl, M p ∣ 2 ^ 104 * val52 l m B (l.D * p + l.oMs) - 1
  bnd : ∀ p < l.nl, 2 ^ 104 * val52 l m B (l.D * p + l.oMs) ≤ 2 ^ (52 * l.S - 16)

/-- The facts every multiplication of the exponentiations needs: `Ar0`, and
with `ammCoreZ` those of the multiples of the moduli (`ArZ`). -/
structure Ar (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M k : Nat → Nat) : Prop
    extends Ar0 l m B M k where
  zs : l.z = true → ArZ l m B M

/-- The bound of the exponentiations' numbers, halved: the modulus, or with
`ammCoreZ`, whose multiplications reduce by a multiple of it, `2^(52 S - 15)`. -/
def gb (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (M : Nat) : Nat := if l.z then 2 ^ (52 * l.S - 15) else M

theorem gb_eq (hz : l.z = false) (M : Nat) : gb l M = M := by
  unfold gb; rw [hz, ite_eq_right (by decide)]

/-- The number at offset `c` of prime `p`'s region: limbs of 52 bits, below
`2 gb`. -/
structure Good (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M : Nat → Nat) (c p : Nat) : Prop where
  lt : ∀ j < l.L, limb l m B (l.D * p + c) j < 2 ^ 52
  v : val52 l m B (l.D * p + c) < 2 * gb l (M p)

/-- The number at offset `c` of prime `p`'s region: limbs of 52 bits, below
`2 M p`. -/
structure GoodS (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M : Nat → Nat) (c p : Nat) : Prop where
  lt : ∀ j < l.L, limb l m B (l.D * p + c) j < 2 ^ 52
  v : val52 l m B (l.D * p + c) < 2 * M p

theorem GoodS.good {m : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : GoodS l m B M c p)
    (h : M p ≤ gb l (M p)) : Good l m B M c p := ⟨g.lt, by have := g.v; omega_using [h, this]⟩

theorem Good.strong {m : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : Good l m B M c p) (hz : l.z = false) :
    GoodS l m B M c p := ⟨g.lt, by have := g.v; rwa [gb_eq hz] at this⟩

/-- The layouts' multiplication: `ammCoreZ`'s, or the others'. -/
theorem AmmOk.zcases (hl : AmmOk l) : l.z = false ∨ ZOk l := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
  case inl.inr.inr.inr => exact .inr rfl
  all_goals exact .inl rfl

theorem ZOk.z (hz : ZOk l) : l.z = true := by rw [hz]; rfl

theorem D_mul {p : Nat} (hp : p < 2) : l.D * p = 0 ∨ l.D * p = l.D := by
  rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl <;> simp

/-- A word of a region outside the windows. -/
theorem Out2.word_at (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p c : Nat}
    (hp : p < l.nl) (hc : c + 8 ≤ o ∨ o + n ≤ c) (hcD : c + 8 ≤ l.D) (hoD : o + n ≤ l.D) :
    word m' B (l.D * p + c) = word m B (l.D * p + c) := by
  have hD := hl.D_bounds
  refine (Mem.readW_congr fun i hi => (h _ fun p' hp' => ?_).symm).symm
  rw [ofs_off B (by rcases D_mulN hl hp with h | h <;> omega_using [hcD, hD, hi, h])]
  have : i < 8 := hi
  rcases D_mulN hl hp with h1 | h1 <;> rcases D_mulN hl hp' with h2 | h2 <;> omega_arith

theorem Out2.limb (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p c : Nat}
    (hp : p < l.nl) (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D) (hoD : o + n ≤ l.D) {j : Nat}
    (hj : j < l.L) : limb l m' B (l.D * p + c) j = limb l m B (l.D * p + c) j := by
  have := off_ltN hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, h.word_at hl hp (by omega_using [hc, this]) (by omega_using [hcD, this]) hoD]

theorem Out2.val (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p c : Nat}
    (hp : p < l.nl) (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D) (hoD : o + n ≤ l.D) :
    val52 l m' B (l.D * p + c) = val52 l m B (l.D * p + c) := by
  unfold val52; exact lval_congr fun j hj => h.limb hl hp hc hcD hoD hj

theorem oFin_le (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : l.oFin + l.NB ≤ l.D := by
  simp only [Lay.D]; omega_using []

theorem Ar0.of_out2 (hl : AmmOk l) {m m' : Mem} {B : Addr} {M k : Nat → Nat} (a : Ar0 l m B M k) {o n : Nat}
    (h : Out2 l B o n m m') (ho : l.oY ≤ o) (hoD : o + n ≤ l.D) : Ar0 l m' B M k := by
  have hD' := hl.D_ge
  have hc : ∀ c, c + l.NB ≤ l.NB → c + l.NB ≤ o ∨ o + n ≤ c := fun c hc => .inl (by simp only [Lay.oY] at ho; omega_using [ho, hc])
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp t ht => ?_, a.klt, fun p hp => ?_, a.bnd⟩
  · rw [h.limb hl hp (hc _ (by simp [oM])) (by simp only [oM]; omega_using [hD']) hoD hj]; exact a.mlt p hp j hj
  · rw [h.val hl hp (hc _ (by simp [oM])) (by simp only [oM]; omega_using [hD']) hoD]; exact a.mv p hp
  · rw [Nat.add_assoc, h.word_at hl hp (by simp only [Lay.oK0, Lay.oY] at *; omega_using [ho, ht])
      (by simp only [Lay.oK0] at *; omega_using [hD', ht]) hoD, ← Nat.add_assoc]
    exact a.kw p hp t ht
  · rw [h.limb hl hp (hc _ (by simp [oM])) (by simp only [oM]; omega_using [hD']) hoD
      (by have := hl.bounds; simp only [Lay.L]; omega_using [this])]
    exact a.k0 p hp

theorem ArZ.of_out2 (hz : ZOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} (az : ArZ l m B M) {o n : Nat}
    (h : Out2 l B o n m m') (hcz : l.oMs + l.NB ≤ o ∨ o + n ≤ l.oMs) (hoD : o + n ≤ l.D) : ArZ l m' B M := by
  have hl := hz.amm
  have hM := hz.offs.1
  have hL := hz.L
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [h.limb hl hp hcz (by omega_using [hM]) hoD hj]; exact az.lt p hp j hj
  · rw [h.limb hl hp hcz (by omega_using [hM]) hoD (by omega_using [hL]), h.limb hl hp hcz (by omega_using [hM]) hoD (by omega_using [hL])]
    exact az.top p hp
  · rw [h.val hl hp hcz (by omega_using [hM]) hoD]; exact az.pos p hp
  · rw [h.val hl hp hcz (by omega_using [hM]) hoD]; exact az.dvd p hp
  · rw [h.val hl hp hcz (by omega_using [hM]) hoD]; exact az.bnd p hp

theorem Ar.of_out2 (hl : AmmOk l) {m m' : Mem} {B : Addr} {M k : Nat → Nat} (a : Ar l m B M k) {o n : Nat}
    (h : Out2 l B o n m m') (ho : l.oY ≤ o) (hoF : o + n ≤ l.oFin + l.NB) : Ar l m' B M k := by
  have hoD : o + n ≤ l.D := Nat.le_trans hoF (oFin_le l)
  refine ⟨a.toAr0.of_out2 hl h ho hoD, fun hz => ?_⟩
  have zk : ZOk l := by rcases hl.zcases with h0 | h0 <;> [exact absurd hz (by rw [h0]; decide); exact h0]
  exact (a.zs hz).of_out2 zk h (.inr (by simp only [Lay.oMs]; omega_using [hoF])) hoD

theorem Good.of_out2 (hl : AmmOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : Good l m B M c p)
    (hp : p < l.nl) {o n : Nat} (h : Out2 l B o n m m') (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D)
    (hoD : o + n ≤ l.D) : Good l m' B M c p :=
  ⟨fun j hj => by rw [h.limb hl hp hc hcD hoD hj]; exact g.lt j hj, by rw [h.val hl hp hc hcD hoD]; exact g.v⟩

/-- A multiplication's operands: `r8`, `r9` and `r11` at offsets `a`, `b` and `o` of the area. -/
theorem ammOps_ok {s : State} {B : Addr} {o a b : Nat} {c : Prog isa} {Q : State → Prop} (hB : s.gpr .rbx = B)
    (ho : o < 2 ^ 31) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (h : ∀ s₃ : State, s₃.gpr .rbx = B → s₃.gpr .r8 = off B a → s₃.gpr .r9 = off B b → s₃.gpr .r11 = off B o →
      s₃.mem = s.mem → s₃.rd = s.rd → s₃.wr = s.wr → s₃.mxcsr = s.mxcsr →
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → s₃.gpr r = s.gpr r) → WP isa c s₃ Q) :
    WP isa (.seq (.block (ammOps o a b)) c) s Q := by
  refine WP.seq ?_
  refine setOff ha fun s₁ u₁ => setOff hb fun s₂ u₂ => setOff ho fun s₃ u₃ => WP.block_nil ?_
  rw [u₁.other _ (by decide), hB] at u₂
  rw [u₂.other _ (by decide), u₁.other _ (by decide), hB] at u₃
  exact h s₃ (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.self, hB])
    (by rw [u₃.other _ (by decide), u₂.self]) u₃.self
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.mxcsr, u₂.mxcsr, u₁.mxcsr]) fun r h8 h9 h11 => by rw [u₃.other _ h11, u₂.other _ h9, u₁.other _ h8]

/-- With `ammCoreZ`, `ammMul` with `r8`, `r9`, `r11` at offsets `a`, `b`, `o`: the result times `2^(52 S)`
is the product plus a multiple of `X = 2¹⁰⁴ m - 1`, `m` the number at `oMs`, when the second operand is below
`2^(52 S)` and the product fits. -/
theorem ammCoreZ2_ok (hz : ZOk l) {s : State} {B : Addr} {o a b : Nat} {M : Nat → Nat}
    (hB : s.gpr .rbx = B) (h8 : s.gpr .r8 = off B a) (h9 : s.gpr .r9 = off B b) (h11 : s.gpr .r11 = off B o)
    (hs : Scr s B (l.nl * l.D)) (az : ArZ l s.mem B M)
    (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + b) j < 2 ^ 52) :
    WP isa (ammMul l) s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (val52 l s.mem B (l.D * p + b) < 2 ^ (52 * l.S) →
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) +
          (2 ^ 104 * val52 l s.mem B (l.D * p + l.oMs) - 1) * 2 ^ (52 * l.S) < 2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
        ∃ Q, Q < 2 ^ (52 * l.S) ∧ val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) +
            (2 ^ 104 * val52 l s.mem B (l.D * p + l.oMs) - 1) * Q)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rw [show ammMul l = ammCoreZ l by unfold ammMul; rw [hz.z, ite_eq_left rfl]]
  refine WP.mono (ammCoreZSpec_ok hz hB h8 h9 h11 hs ho ha hb
    (fun p hp j hj => ⟨(hlt p hp j hj).1, (hlt p hp j hj).2, az.lt p hp j hj⟩) az.top)
    fun s' ⟨hv, rest⟩ => ⟨fun p hp => ⟨(hv p hp).1, fun hb' hfit =>
      (hv p hp).2 _ (by have := az.pos p hp; omega_using [this]) hb' hfit⟩, rest⟩

/-- `ammCoreZ2_ok` for `amm o a b`. -/
theorem ammZ_ok (hz : ZOk l) {s : State} {B : Addr} {o a b : Nat} {M : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (az : ArZ l s.mem B M)
    (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + b) j < 2 ^ 52) :
    WP isa (amm l o a b) s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (val52 l s.mem B (l.D * p + b) < 2 ^ (52 * l.S) →
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) +
          (2 ^ 104 * val52 l s.mem B (l.D * p + l.oMs) - 1) * 2 ^ (52 * l.S) < 2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
        ∃ Q, Q < 2 ^ (52 * l.S) ∧ val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) +
            (2 ^ 104 * val52 l s.mem B (l.D * p + l.oMs) - 1) * Q)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD := hz.offs.2.1
  refine ammOps_ok hB (by omega_using [ho, hD]) (by omega_using [ha, hD]) (by omega_using [hb, hD]) fun s₃ rbx₃ r8₃ r9₃ r11₃ m₃ rd₃ wr₃ x₃ g₃ => ?_
  rw [← m₃] at az hlt ⊢
  refine WP.mono (ammCoreZ2_ok hz rbx₃ r8₃ r9₃ r11₃ (hs.congr wr₃) az ho ha hb hlt)
    fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ => ⟨hv, hf, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_,
      hrd.trans rd₃, hwr.trans wr₃, hx.trans x₃⟩
  rw [hg r h1 h2 h3 h4 h6 h7 h9, g₃ r h5 h6 h8]

/-- `amm` modulo the primes, by `ammCore`: the result times `2^(52 S)` is the product plus a multiple
of the prime, when the second operand is below `2^(52 S)` and the product fits. -/
theorem ammP_ok (hl : AmmOk l) {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (ar : Ar0 l s.mem B M k)
    (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + b) j < 2 ^ 52) :
    WP isa (ammP l o a b) s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (val52 l s.mem B (l.D * p + b) < 2 ^ (52 * l.S) →
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) + M p * 2 ^ (52 * l.S) <
          2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
        ∃ U, U < 2 ^ (52 * l.S) ∧ val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) + M p * U)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  have hD' := hl.D_ge
  have hnD := nlD hl
  have hnl := hl.nl_le
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by omega_using [hnl])
  refine ammOps_ok hB (by omega_using [ho, hD]) (by omega_using [ha, hD]) (by omega_using [hb, hD]) fun s₃ rbx₃ r8₃ r9₃ r11₃ m₃ rd₃ wr₃ x₃ g₃ => ?_
  rw [← m₃] at ar hlt ⊢
  refine WP.mono (ammCoreSpecN_eq hl (ammCore_core hl) rbx₃ r8₃ r9₃ r11₃ (hs.congr wr₃) (by omega_using [hD', hnD]) (by omega_using [hD, hnD, hDn])
    (by omega_using [ho, hnD]) (by omega_using [ha, hnD]) (by omega_using [hb, hnD])
    (fun p hp j hj => ⟨(hlt p hp j hj).1, (hlt p hp j hj).2, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0)
    fun s' ⟨hv, hf, hg, _, hrd, hwr, hx⟩ => ⟨fun p hp => ⟨(hv p hp).1, fun hb' hfit => ?_⟩, hf.out2,
      fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_, hrd.trans rd₃, hwr.trans wr₃, hx.trans x₃⟩
  · have := (hv p hp).2 hb' (by rw [ar.mv p hp]; exact hfit)
    rwa [ar.mv p hp] at this
  · rw [hg r h1 h2 h3 h4 h6 h7 h9, g₃ r h5 h6 h8]

/-- The size of a multiplication's result from its equation. -/
theorem zbound' {V A B X Q R H : Nat} (h : V * R = A * B + X * Q) (hQ : Q < R) (hAB : A * B < R * H) :
    V < H + X := by
  have h2 : X * Q ≤ X * R := Nat.mul_le_mul_left _ (Nat.le_of_lt hQ)
  have h3 : R * V < R * (H + X) := by rw [Nat.mul_add, Nat.mul_comm R X, Nat.mul_comm R V]; omega_using [h, hAB, h2]
  exact Nat.lt_of_mul_lt_mul_left h3

theorem zbound {V A B X Q R G H : Nat} (h : V * R = A * B + X * Q) (hQ : Q < R) (hA : A < G) (hB : B < G)
    (hG : G * G ≤ R * H) : V < H + X :=
  zbound' h hQ (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hA hB) hG)

/-- A product fits, with a multiple of `X`. -/
theorem zfit' {A B X R H T : Nat} (hAB : A * B < R * H) (hX : H + X ≤ T) : A * B + X * R < R * T := by
  have h2 : R * (H + X) ≤ R * T := Nat.mul_le_mul_left _ hX
  rw [Nat.mul_add, Nat.mul_comm R X] at h2
  omega_using [hAB, h2]

theorem zfit {A B X R G H T : Nat} (hA : A < G) (hB : B < G) (hG : G * G ≤ R * H) (hX : H + X ≤ T) :
    A * B + X * R < R * T :=
  zfit' (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hA hB) hG) hX

/-- The sizes of `ammCoreZ`'s numbers: twice their bound squared is `2^(52 S)` times `2^(52 S - 28)`,
which with the modulus is below the bound, and they are below `2^(52 S)`. -/
theorem ZOk.sizes (hz : ZOk l) (M : Nat) :
    2 * gb l M * (2 * gb l M) ≤ 2 ^ (52 * l.S) * 2 ^ (52 * l.S - 28) ∧
      2 ^ (52 * l.S - 28) + 2 ^ (52 * l.S - 16) ≤ 2 * gb l M ∧ 2 * gb l M ≤ 2 ^ (52 * l.S) ∧
      2 * gb l M ≤ 2 ^ (52 * l.L) := by
  rw [gb, hz.z, ite_eq_left rfl, hz]
  exact ⟨Nat.le_of_ble_eq_true (by kernel_rfl), Nat.le_of_ble_eq_true (by kernel_rfl),
    Nat.le_of_ble_eq_true (by kernel_rfl), Nat.le_of_ble_eq_true (by kernel_rfl)⟩

/-- A multiplication's result with `ammCoreZ`, from its equation: good, and congruent to the product
over `2^(52 S)` modulo each `M p`. -/
theorem zgood (hz : ZOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} {o a b p : Nat} (az : ArZ l m B M)
    (hp : p < l.nl) (ga : Good l m B M a p) (gb' : Good l m B M b p)
    (hlt : ∀ j < l.L, limb l m' B (l.D * p + o) j < 2 ^ 52)
    (hv : val52 l m B (l.D * p + b) < 2 ^ (52 * l.S) →
      val52 l m B (l.D * p + a) * val52 l m B (l.D * p + b) +
        (2 ^ 104 * val52 l m B (l.D * p + l.oMs) - 1) * 2 ^ (52 * l.S) < 2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
      ∃ Q, Q < 2 ^ (52 * l.S) ∧ val52 l m' B (l.D * p + o) * 2 ^ (52 * l.S) =
        val52 l m B (l.D * p + a) * val52 l m B (l.D * p + b) + (2 ^ 104 * val52 l m B (l.D * p + l.oMs) - 1) * Q) :
    Good l m' B M o p ∧ val52 l m' B (l.D * p + o) * 2 ^ (52 * l.S) % M p =
      val52 l m B (l.D * p + a) * val52 l m B (l.D * p + b) % M p := by
  obtain ⟨s1, s2, s3, s4⟩ := hz.sizes (M p)
  have hX := az.bnd p hp
  have hpos := az.pos p hp
  obtain ⟨Q, hQ, he⟩ := hv (Nat.lt_of_lt_of_le gb'.v s3)
    (zfit ga.v gb'.v s1 (Nat.le_trans (by omega_using [s2, hX]) s4))
  have hb := zbound he hQ ga.v gb'.v s1
  refine ⟨⟨hlt, by omega_using [s2, hX, hb]⟩, ?_⟩
  obtain ⟨c, hc⟩ := az.dvd p hp
  rw [he, hc, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- `amm o a b` on good numbers. -/
theorem amm2_ok (hl : AmmOk l) {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (ar : Ar l s.mem B M k)
    (ho' : l.oY ≤ o) (hoF : o ≤ l.oFin) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (ga : ∀ p < l.nl, Good l s.mem B M a p) (gb' : ∀ p < l.nl, Good l s.mem B M b p) :
    WP isa (amm l o a b) s fun s' =>
      (∀ p < l.nl, Good l s'.mem B M o p ∧
        val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % M p =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % M p) ∧
      Out2 l B o l.NB s.mem s'.mem ∧ Ar l s'.mem B M k ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have ho : o + l.NB ≤ l.D := Nat.le_trans (Nat.add_le_add_right hoF _) (oFin_le l)
  rcases hl.zcases with hz | hz
  · have e := gb_eq (l := l) hz
    refine WP.mono (amm_ok hl hz (k := k) hB hs (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb])
      (fun p hp j hj => ⟨(ga p hp).lt j hj, (gb' p hp).lt j hj, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0
      (fun p hp => by rw [ar.mv p hp, ← e (M p)]; exact (ga p hp).v)
      (fun p hp => by rw [ar.mv p hp, ← e (M p)]; exact (gb' p hp).v)
      (fun p hp => by rw [ar.mv p hp]; exact ar.bnd p hp)) fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ =>
        ⟨fun p hp => ?_, hf, ar.of_out2 hl hf ho' (by omega_using [hoF]), hg, hrd, hwr, hx⟩
    obtain ⟨lt, v, e'⟩ := hv p hp
    rw [ar.mv p hp] at v e'
    exact ⟨⟨lt, by rw [e]; exact v⟩, e'⟩
  · have az := ar.zs hz.z
    refine WP.mono (ammZ_ok hz hB hs az ho ha hb fun p hp j hj => ⟨(ga p hp).lt j hj, (gb' p hp).lt j hj⟩)
      fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ => ⟨fun p hp =>
        zgood hz az hp (ga p hp) (gb' p hp) (hv p hp).1 (hv p hp).2, hf, ar.of_out2 hl hf ho' (by omega_using [hoF]), hg, hrd, hwr, hx⟩

/-- The layout's multiplication on good numbers, `r8`, `r9`, `r11` at `a`, `b`, `o`. -/
theorem ammCore2_ok (hl : AmmOk l) {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (h8 : s.gpr .r8 = off B a) (h9 : s.gpr .r9 = off B b) (h11 : s.gpr .r11 = off B o)
    (hs : Scr s B (l.nl * l.D)) (ar : Ar l s.mem B M k)
    (ho' : l.oY ≤ o) (hoF : o ≤ l.oFin) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (ga : ∀ p < l.nl, Good l s.mem B M a p) (gb' : ∀ p < l.nl, Good l s.mem B M b p) :
    WP isa (ammMul l) s fun s' =>
      (∀ p < l.nl, Good l s'.mem B M o p ∧
        val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % M p =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % M p) ∧
      Out2 l B o l.NB s.mem s'.mem ∧ Ar l s'.mem B M k ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have ho : o + l.NB ≤ l.D := Nat.le_trans (Nat.add_le_add_right hoF _) (oFin_le l)
  rcases hl.zcases with hz | hz
  · have e := gb_eq (l := l) hz
    refine WP.mono (ammCoreSpec_ok hl hz (k := k) hB h8 h9 h11 hs (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb])
      (fun p hp j hj => ⟨(ga p hp).lt j hj, (gb' p hp).lt j hj, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0
      (fun p hp => by rw [ar.mv p hp, ← e (M p)]; exact (ga p hp).v)
      (fun p hp => by rw [ar.mv p hp, ← e (M p)]; exact (gb' p hp).v)
      (fun p hp => by rw [ar.mv p hp]; exact ar.bnd p hp)) fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ =>
        ⟨fun p hp => ?_, hf, ar.of_out2 hl hf ho' (by omega_using [hoF]), hg, hrd, hwr, hx⟩
    obtain ⟨lt, v, e'⟩ := hv p hp
    rw [ar.mv p hp] at v e'
    exact ⟨⟨lt, by rw [e]; exact v⟩, e'⟩
  · have az := ar.zs hz.z
    refine WP.mono (ammCoreZ2_ok hz hB h8 h9 h11 hs az ho ha hb
      fun p hp j hj => ⟨(ga p hp).lt j hj, (gb' p hp).lt j hj⟩)
      fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ => ⟨fun p hp =>
        zgood hz az hp (ga p hp) (gb' p hp) (hv p hp).1 (hv p hp).2, hf, ar.of_out2 hl hf ho' (by omega_using [hoF]), hg, hrd, hwr, hx⟩

theorem GoodS.of_out2 (hl : AmmOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : GoodS l m B M c p)
    (hp : p < l.nl) {o n : Nat} (h : Out2 l B o n m m') (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D)
    (hoD : o + n ≤ l.D) : GoodS l m' B M c p :=
  ⟨fun j hj => by rw [h.limb hl hp hc hcD hoD hj]; exact g.lt j hj, by rw [h.val hl hp hc hcD hoD]; exact g.v⟩

theorem Good.of_limbs {m m' : Mem} {B : Addr} {M : Nat → Nat} {c c' p : Nat} (g : Good l m B M c p)
    (h : ∀ q < l.L, limb l m' B (l.D * p + c') q = limb l m B (l.D * p + c) q) : Good l m' B M c' p :=
  ⟨fun j hj => by rw [h j hj]; exact g.lt j hj, by
    rw [show val52 l m' B (l.D * p + c') = val52 l m B (l.D * p + c) from lval_congr h]; exact g.v⟩

theorem GoodS.of_limbs {m m' : Mem} {B : Addr} {M : Nat → Nat} {c c' p : Nat} (g : GoodS l m B M c p)
    (h : ∀ q < l.L, limb l m' B (l.D * p + c') q = limb l m B (l.D * p + c) q) : GoodS l m' B M c' p :=
  ⟨fun j hj => by rw [h j hj]; exact g.lt j hj, by
    rw [show val52 l m' B (l.D * p + c') = val52 l m B (l.D * p + c) from lval_congr h]; exact g.v⟩

theorem val52_of_limbs {m m' : Mem} {B : Addr} {d d' : Nat} (h : ∀ q < l.L, limb l m' B d' q = limb l m B d q) :
    val52 l m' B d' = val52 l m B d := lval_congr h

theorem Out2.mono {B : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Out2 l B o n m m') (h1 : o' ≤ o)
    (h2 : o + n ≤ o' + n') : Out2 l B o' n' m m' := fun x hx => h x fun p hp => by
  rcases hx p hp with h3 | h3 <;> omega_arith

end VG.Proof.Bignum.X86_64.Ifma

end

end

/-!
# RSA with AVX512_IFMA on x86-64, any size: the table

`copyN o a` copies the numbers at `a` to `o` in
both regions (`copyN_ok`); `convTab` puts `Y` and `X` into Montgomery form
for `R = 2^(208 R)` (times `K1 ≡ 2^(416 R - 64 W)`, as they hold `2^(64 W)`
and `x 2^(64 W)`; entries 0 and 1, `conv0_ok`, `conv1_ok`), then writes the
table of the powers of `x` in the same loop (`tabIter_ok`, `convTab_ok`):
`T_0 = Y`, `T_1 = X` and `T_i = T_(i-1) X / 2^(208 R)`, so `T_i ≡ x^i 2^(208 R)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (wrList writeW256_outside word_wrList_unique readW256_outside off_add se_ofNat
  mont_mul2 mont_into0 mont_into1)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The offsets of a region, in `NB`, the table's `T NB`, `XE`, and the
bytes `zx` of the numbers only `ammCoreZ`'s layouts have, at its end. -/
theorem lay_offs (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : l.oK0 = l.NB ∧ l.oY = l.NB + 32 ∧ l.oX = 2 * l.NB + 32 ∧ l.oS = 3 * l.NB + 32 ∧
    l.oTab = 4 * l.NB + 32 ∧ l.oE = 4 * l.NB + 32 + l.T * l.NB ∧ l.oK1 = 4 * l.NB + 32 + l.T * l.NB + l.XE ∧
    l.oV = 5 * l.NB + 32 + l.T * l.NB + l.XE ∧ l.oFin = 5 * l.NB + 64 + l.T * l.NB + l.XE ∧
    l.D = 6 * l.NB + 64 + l.T * l.NB + l.XE + l.zx := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Lay.D, Lay.oFin, Lay.oV, Lay.oK1, Lay.oE, Lay.oTab, Lay.oS, Lay.oX, Lay.oY, Lay.oK0] <;> omega_using []

/-- Entry `i` of the table ends within it. -/
theorem tab_le (hl : AmmOk l) {i : Nat} (hi : i < l.T) : l.NB * i + l.NB ≤ l.T * l.NB := by
  have := hl.T_bounds
  rw [Nat.mul_comm l.T, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-- An entry below 16 is in the table, and not its last. -/
theorem T_gt (hl : AmmOk l) {i : Nat} (h : i < 16) : i < l.T := by have := hl.T_bounds; omega_using [h, this]

theorem dec_T (hl : AmmOk l) {i : Nat} (h : i + 1 < 16) : decide (i + 1 = l.T) = false := by
  have := hl.T_bounds; exact decide_eq_false (by omega_using [h, this])

/-- Entries of the table at the same offset are the same. -/
theorem nb_mul_inj (hl : AmmOk l) {i j : Nat} (h : l.NB * i = l.NB * j) : i = j := by
  have : 0 < l.NB := by rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.eq_of_mul_eq_mul_left this h

theorem vy_setVy_self (s : State) (d : VReg) (v : BitVec 256) : (s.setVy d v).vy d = v := by
  cases d with
  | lo d => simp only [State.vy, State.setVy, State.ymm, State.setV, ite_true, StraightY.split_eq]
  | hi d => simp only [State.vy, State.setVy, ite_true]

/-- 32-byte copies at `rbx` plus offsets, from `x.1` to `x.2`, through register 0. -/
def copyCode (xs : List (Nat × Nat)) : List Instr :=
  xs.flatMap fun x => [.evLoad (vreg 0) (at_ .rbx x.1), .evStore (at_ .rbx x.2) (vreg 0)]

theorem copies_ok (hl : AmmOk l) {B : Addr} :
    ∀ (xs : List (Nat × Nat)) (s : State), s.gpr .rbx = B → Scr s B (l.nl * l.D) →
      (∀ x ∈ xs, x.1 + 32 ≤ l.nl * l.D ∧ x.2 + 32 ≤ l.nl * l.D) →
      (∀ x ∈ xs, ∀ y ∈ xs, y.1 + 32 ≤ x.2 ∨ x.2 + 32 ≤ y.1) →
      WP isa (.block (copyCode xs)) s fun s' =>
        s'.mem = wrList s.mem B (xs.map fun x => (x.2, s.mem.readW (off B x.1) 256)) ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | [], s, _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | (a, o) :: rest, s, hB, hs, hxs, hsep => by
    have hD := hl.D_bounds
    obtain ho := hxs (a, o) (List.mem_cons_self ..)
    have hn := hs.nowrap
    rw [copyCode, List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append, WP.block_cons_iff]
    obtain hld : InRegions (s.rd ++ s.wr) (off B a) 32 :=
      let ⟨_, h, c⟩ := hs.region (d := a) (n := 32) (by omega_using [ho]) (by decide); ⟨_, List.mem_append_right _ h, c⟩
    obtain hst : InRegions s.wr (off B o) 32 :=
      let ⟨_, h, c⟩ := hs.region (d := o) (n := 32) (by omega_using [ho]) (by decide); ⟨_, h, c⟩
    refine ⟨s.setVy (vreg 0) (s.mem.readW (off B a) 256),
      by simp only [exec, ea_rG hB, State.load256, hld, ite_true, Option.map_some], ?_⟩
    obtain y₁ := vy_setVy_self s (vreg 0) (s.mem.readW (off B a) 256)
    obtain e₁ : ∀ t : State, t = s.setVy (vreg 0) (s.mem.readW (off B a) 256) →
        t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
      rintro t rfl; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    generalize hs₁ : s.setVy (vreg 0) (s.mem.readW (off B a) 256) = s₁ at y₁ ⊢
    obtain ⟨g₁, m₁, rd₁, wr₁, x₁⟩ := e₁ s₁ hs₁.symm
    obtain hB₁ : s₁.gpr .rbx = B := by rw [g₁]; exact hB
    rw [WP.block_cons_iff]
    refine ⟨{ s₁ with mem := s₁.mem.writeW (off B o) (s₁.vy (vreg 0)) }, by
      simp only [exec, ea_rG hB₁, State.store256, wr₁, hst, ite_true], ?_⟩
    rw [y₁, m₁]
    refine WP.mono (copies_ok hl rest _ (by rw [← g₁] at hB; exact hB) (hs.congr wr₁)
      (fun x hx => hxs x (List.mem_cons_of_mem _ hx))
      (fun x hx y hy => hsep x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)))
      fun s' ⟨m', g', rd', wr', x'⟩ => ⟨?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁, x'.trans x₁⟩
    rw [m', List.map_cons, wrList]
    refine congrArg (wrList _ B) (List.map_congr_left fun y hy => ?_)
    have := hxs y (List.mem_cons_of_mem _ hy)
    obtain hs' := hsep (a, o) (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy)
    exact congrArg _ (readW256_outside (writeW256_outside _ B _ (by omega_arith)) (by omega_using [hs']) (by omega_using [hn, this]))

/-- The copies of `copyN o a`. -/
def cpList (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (o a : Nat) : List (Nat × Nat) :=
  (List.range l.nl).flatMap fun p => (List.range l.R).map fun k => (l.D * p + a + 32 * k, l.D * p + o + 32 * k)

theorem copyN_eq (o a : Nat) : copyN l o a = copyCode (cpList l o a) := by
  simp only [copyN, copyCode, cpList, List.flatMap_assoc, List.flatMap_map]

theorem mem_cpList {o a : Nat} {x : Nat × Nat} (h : x ∈ cpList l o a) :
    ∃ p < l.nl, ∃ k < l.R, x = (l.D * p + a + 32 * k, l.D * p + o + 32 * k) := by
  simp only [cpList, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨p, hp, k, hk, rfl⟩ := h
  exact ⟨p, hp, k, hk, rfl⟩

/-- `[o] := [a]` in both regions. -/
theorem copyN_ok (hl : AmmOk l) {s : State} {B : Addr} {o a : Nat} (hB : s.gpr .rbx = B)
    (hs : Scr s B (l.nl * l.D)) (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hoa : a + l.NB ≤ o ∨ o + l.NB ≤ a) :
    WP isa (.block (copyN l o a)) s fun s' =>
      (∀ p < l.nl, ∀ q < l.L, limb l s'.mem B (l.D * p + o) q = limb l s.mem B (l.D * p + a) q) ∧
      Out2 l B o l.NB s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, _⟩ := hl.bounds
  have hD := hl.D_bounds
  have hNB : l.NB = 32 * l.R := rfl
  rw [copyN_eq]
  refine WP.mono (copies_ok hl _ s hB hs (fun x hx => ?_) (fun x hx y hy => ?_))
    fun s' ⟨hm, hg, hrd, hwr, hx⟩ => ⟨fun p hp q hq => ?_, ?_, hg, hrd, hwr, hx⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := mem_cpList hx
    obtain hle := lane_end hl hp
    rcases D_mulN hl hp with h | h <;> dsimp only <;> omega_using [ho, ha, hNB, hk, h, hle]
  · obtain ⟨p, hp, k, hk, rfl⟩ := mem_cpList hx
    obtain ⟨p', hp', k', hk', rfl⟩ := mem_cpList hy
    rcases (lane01 hl hp) with rfl | rfl <;> rcases (lane01 hl hp') with rfl | rfl <;>
          dsimp only <;> simp only [Nat.mul_zero, Nat.mul_one] <;> omega_using [hoa, hNB, hk, hk', ho, ha]
  · have hk : q % l.R < l.R := Nat.mod_lt _ (by omega_using [hR])
    obtain ht : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    obtain e := word_wrList_unique B (e := l.D * p + o + 32 * (q % l.R)) (t := q / l.R)
      (v := s.mem.readW (off B (l.D * p + a + 32 * (q % l.R))) 256) ht
      (by have hle := lane_end hl hp; rcases D_mulN hl hp with h | h <;> omega_using [ho, hD, hNB, hk, h, hle])
      ((cpList l o a).map fun x => (x.2, s.mem.readW (off B x.1) 256)) s.mem
      (List.mem_map.2 ⟨(l.D * p + a + 32 * (q % l.R), l.D * p + o + 32 * (q % l.R)),
        by simp only [cpList, List.mem_flatMap, List.mem_map, List.mem_range]; exact ⟨p, hp, q % l.R, hk, rfl⟩, rfl⟩)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p', hp', k', hk', rfl⟩ := mem_cpList hy
        rcases (lane01 hl hp) with rfl | rfl <;> rcases (lane01 hl hp') with rfl | rfl <;>
          dsimp only <;> simp only [Nat.mul_zero, Nat.mul_one] <;> omega_using [ho, hD, hNB, hk', hk])
      (fun x hx he => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p', hp', k', hk', rfl⟩ := mem_cpList hy
        dsimp only at he ⊢
        have : p' = p ∧ k' = q % l.R := by
          rcases (lane01 hl hp) with rfl | rfl <;> rcases (lane01 hl hp') with rfl | rfl <;>
            simp only [Nat.mul_zero, Nat.mul_one] at he <;> omega_using [he, hD, hNB, hk, hk']
        rw [this.1, this.2])
    show (word s'.mem B _).toNat = (word s.mem B _).toNat
    obtain ex := readW_extract s.mem (off B (l.D * p + a + 32 * (q % l.R))) (w := 256) (k := 8 * (q / l.R)) (n := 8)
      (by omega_using [ht])
    rw [hm, show l.D * p + o + l.off q = l.D * p + o + 32 * (q % l.R) + 8 * (q / l.R) by unfold Lay.off; omega_using [], e,
      show 64 * (q / l.R) = 8 * (8 * (q / l.R)) by omega_using []]
    refine congrArg BitVec.toNat (ex.trans ?_)
    rw [off_add]
    exact congrArg (fun d => s.mem.readW (off B d) 64) (by unfold Lay.off; omega_using [])
  · rw [hm]
    exact wrList_out2 hl B (by omega_using [ho, hD]) _ s.mem fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨p, hp, k, hk, rfl⟩ := mem_cpList hy
      exact ⟨p, hp, by dsimp only; omega_using [], by dsimp only; omega_using [hNB, hk]⟩

theorem NB_le (hl : AmmOk l) : l.NB ≤ 640 ∧ 160 ≤ l.NB := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

theorem dbl_le (hl : AmmOk l) : l.cv ≤ 104 * l.S := by rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The base and 1 come times `R_X` to the exponentiations of the layouts without `ammCoreZ`. -/
theorem cv_eq (hz : l.z = false) : l.cv = 64 * l.W := by
  unfold Lay.cv; rw [hz, ite_eq_right (by decide)]

/-! ## The pieces of `convTabBody` -/

/-- `cmp r13, k`. -/
theorem cmp13_ok (s : State) {n k : Nat} (h13 : s.gpr .r13 = BitVec.ofNat 64 n) (hn : n < 2 ^ 31) (hk : k < 2 ^ 31) :
    WP isa (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.zf = some (decide (n = k)) ∧ t.cf = some (decide (n < k)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  xrun [h13, se_ofNat hk]
  refine ⟨ofNat_sub_beq (j := n) (N := k) (by omega_using [hn]) (by omega_using [hk]), ?_, rfl⟩
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [hn]),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [hk])]

/-- The operands of entry `i < 2`: `Y` or `X`, in place, and `K1`. -/
theorem convSetup_ok (hl : AmmOk l) {s : State} {B : Addr} {i : Nat}
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.block (convSetup l)) s fun s' =>
      s'.gpr .r8 = off B (l.oY + l.NB * i) ∧ s'.gpr .r9 = off B l.oK1 ∧
      s'.gpr .r11 = off B (l.oY + l.NB * i) ∧
      VG.Proof.MlKem.X86_64.Keep [.r8, .r9, .r11] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain e : off B (l.oY + l.NB * i) = B + BitVec.ofNat 64 (l.oTab + l.NB * i) - BitVec.ofNat 64 (l.oTab - l.oY) := by
    rw [VG.Offset.add_ofNat_sub _ (by omega_using [o2, o5])]
    exact congrArg (off B) (by omega_using [o2, o5])
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .r9, .r11] (Q := fun s' =>
    s'.gpr .r8 = off B (l.oY + l.NB * i) ∧ s'.gpr .r9 = off B l.oK1 ∧
      s'.gpr .r11 = off B (l.oY + l.NB * i) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) (by
    xrun [convSetup, hB, h13, se_ofNat (show l.oTab - l.oY < 2 ^ 31 by omega_using [hD, o2, o5]),
      se_ofNat (show l.oK1 < 2 ^ 31 by omega_using [hD, o7, o10])]
    exact ⟨e.symm, e.symm, rfl⟩) rfl)
    fun s' ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, k, d, e⟩

/-- The operands of entry `i ≥ 1` of the table: `T_(i-1)`, `X`, `T_i`. -/
theorem tabHead_ok (hl : AmmOk l) {s : State} {B : Addr} {i : Nat} (hi : 1 ≤ i) (_hi' : i < l.T)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.block (tabSetup l)) s fun s' =>
      s'.gpr .r8 = off B (l.oTab + l.NB * (i - 1)) ∧ s'.gpr .r9 = off B l.oX ∧
      s'.gpr .r11 = off B (l.oTab + l.NB * i) ∧
      VG.Proof.MlKem.X86_64.Keep [.r8, .r9, .r11] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain hNi : l.NB ≤ l.NB * i := Nat.le_mul_of_pos_right _ (by omega_using [hi])
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .r9, .r11] (Q := fun s' =>
    s'.gpr .r8 = off B (l.oTab + l.NB * (i - 1)) ∧ s'.gpr .r9 = off B l.oX ∧
      s'.gpr .r11 = off B (l.oTab + l.NB * i) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) (by
    xrun [tabSetup, hB, h13, se_ofNat (show l.NB < 2 ^ 31 by omega_using [hD]), se_ofNat (show l.oX < 2 ^ 31 by omega_using [hD, o3])]
    and_intros
    any_goals rfl
    · rw [VG.Offset.add_ofNat_sub _ (by omega_using [hNi])]
      exact congrArg (off B) (by rw [Nat.mul_sub_one]; omega_using [hNi])) rfl)
    fun s' ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, k, d, e⟩

/-- The next entry, `ZF` after the last. -/
theorem tabTail_ok (hl : AmmOk l) {s : State} {i : Nat} (hi : i < l.T)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
        .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.T * l.NB)))]) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * (i + 1)) ∧ s'.zf = some (decide (i + 1 = l.T)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain hNi : l.NB * i + l.NB ≤ l.T * l.NB := tab_le hl hi
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun s' =>
    s'.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * (i + 1)) ∧ s'.zf = some (decide (i + 1 = l.T)) ∧
      s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) (by
    xrun [h13, se_ofNat (show l.NB < 2 ^ 31 by omega_using [hD]),
      se_ofNat (show l.oTab + l.T * l.NB < 2 ^ 31 by omega_using [hD, o5, o10])]
    and_intros
    · rw [← BitVec.ofNat_add]; congr 1; rw [Nat.mul_succ]; omega_using []
    · rw [← BitVec.ofNat_add, ofNat_sub_beq (by omega_using [hD, o5, o10, hNi]) (by omega_using [hD, o5, o10])]
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
      · exact nb_mul_inj hl (by rw [Nat.mul_succ, Nat.mul_comm l.NB l.T]; omega_using [h])
      · rw [← h, Nat.succ_mul, Nat.mul_comm i]; omega_using []
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

/-- A state that differs from `s` only in the flags. -/
def Flags (s t : State) : Prop := t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr

/-- The head of entry `i`: the conversion's operands below 2, the table's
from 2. -/
theorem bodyHead_ok (hl : AmmOk l) {s : State} {i : Nat} (hi : i < l.T) {R : Prog isa} {Q : State → Prop}
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i))
    (hc : i < 2 → ∀ t, Flags s t → WP isa (.block (convSetup l)) t fun u => WP isa R u Q)
    (ht : 2 ≤ i → ∀ t, Flags s t → WP isa (.block (tabSetup l)) t fun u => WP isa R u Q) :
    WP isa (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + 2 * l.NB)))])
      (.seq (.ite .b (.block (convSetup l)) (.block (tabSetup l))) R)) s Q := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain hNi : l.NB * i + l.NB ≤ l.T * l.NB := tab_le hl hi
  refine WP.seq (WP.mono (cmp13_ok s h13 (by omega_using [hD, o5, o10, hNi]) (by omega_using [hD, o5, o10]))
    fun t ⟨_, hcf, hg, hm, hrd, hwr, hx⟩ => ?_)
  obtain hf : Flags s t := ⟨hg, hm, hrd, hwr, hx⟩
  obtain e : decide (l.oTab + l.NB * i < l.oTab + 2 * l.NB) = decide (i < 2) := by
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · by_contra h'
      have := Nat.mul_le_mul_left l.NB (show 2 ≤ i by omega_using [h'])
      omega_using [h, this]
    · have := Nat.mul_le_mul_left l.NB (show i ≤ 1 by omega_using [h])
      have := NB_le hl
      omega_arith
  rw [e] at hcf
  refine WP.seq (WP.ite (decide (i < 2)) hcf (fun h => hc (by simpa using h) t hf) (fun h => ht ?_ t hf))
  simp only [decide_eq_false_iff_not] at h
  omega_using [h]

/-- The end of entry `i ≠ 1`: no copies, then the next entry. -/
theorem bodyTail_ok (hl : AmmOk l) {s : State} {i : Nat} (hi : i < l.T) (h1 : i ≠ 1)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.NB)))])
      (.seq (.ite .e (.block (copyN l l.oTab l.oY ++ copyN l (l.oTab + l.NB) l.oX)) (.block []))
        (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
          .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.T * l.NB)))]))) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * (i + 1)) ∧ s'.zf = some (decide (i + 1 = l.T)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain hNi : l.NB * i + l.NB ≤ l.T * l.NB := tab_le hl hi
  refine WP.seq (WP.mono (cmp13_ok s h13 (by omega_using [hD, o5, o10, hNi]) (by omega_using [hD, o5, o10]))
    fun t ⟨hz, _, hg, hm, hrd, hwr, hx⟩ => ?_)
  obtain hne : l.oTab + l.NB * i ≠ l.oTab + l.NB := fun h => h1 (by
    have := NB_le hl
    exact Nat.eq_of_mul_eq_mul_left (show 0 < l.NB by omega_using [this]) (by rw [Nat.mul_one]; omega_using [h]))
  rw [decide_eq_false hne] at hz
  refine WP.seq (WP.ite false hz (fun h => by cases h) fun _ => WP.block_nil ?_)
  refine WP.mono (tabTail_ok hl hi (by rw [hg]; exact h13)) fun u ⟨a, b, k, c, d⟩ =>
    ⟨a, b, ⟨fun r hr => by rw [k.gpr hr, hg], by rw [k.2.1, hrd], by rw [k.2.2, hwr]⟩, by rw [c, hm], by rw [d, hx]⟩

/-! ## The loop -/

/-- After the entries below `i ≥ 2` of the table, from `s₀`: `Y` and `X` in
Montgomery form, and the table. -/
structure TabInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (i : Nat) (t : State) : Prop where
  rbx : t.gpr .rbx = B
  r13 : t.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)
  scr : Scr t B (l.nl * l.D)
  ar : Ar l t.mem B M k
  tab : ∀ j < i, ∀ p < l.nl, Good l t.mem B M (l.oTab + l.NB * j) p ∧
    (Q → val52 l t.mem B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.S) % M p)
  yg : ∀ p < l.nl, Good l t.mem B M l.oY p
  yv : Q → ∀ p < l.nl, val52 l t.mem B (l.D * p + l.oY) % M p = x p ^ 0 * 2 ^ (52 * l.S) % M p
  xg : ∀ p < l.nl, Good l t.mem B M l.oX p
  xv : Q → ∀ p < l.nl, val52 l t.mem B (l.D * p + l.oX) % M p = x p ^ 1 * 2 ^ (52 * l.S) % M p
  frame : Out2 l B l.oY (l.oTab + l.T * l.NB - l.oY) s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r13 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- Entry `i ≥ 2` of the table. -/
theorem tabIter_ok (hl : AmmOk l) {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {i : Nat}
    (hi : 2 ≤ i) (hi' : i < l.T) (hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : TabInv l s₀ B M k x Q i t) :
    WP isa (convTabBody l) t fun t' => TabInv l s₀ B M k x Q (i + 1) t' ∧ t'.zf = some (decide (i + 1 = l.T)) := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain hNi : l.NB * i + l.NB ≤ l.T * l.NB := tab_le hl hi'
  obtain hNi1 : l.NB * (i - 1) + l.NB = l.NB * i := by
    rw [← Nat.mul_succ, show (i - 1).succ = i by omega_using [hi]]
  unfold convTabBody
  refine bodyHead_ok hl hi' h.r13 (fun h' => absurd h' (by omega_using [hi])) fun _ t₀ hf => ?_
  obtain hB₀ : t₀.gpr .rbx = B := by rw [hf.1]; exact h.rbx
  obtain h13₀ : t₀.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i) := by rw [hf.1]; exact h.r13
  refine WP.mono (tabHead_ok hl (by omega_using [hi]) hi' hB₀ h13₀) fun t₁ ⟨h8, h9, h11, k₁, me₁, mx₁⟩ => ?_
  rw [hf.2.1] at me₁
  obtain rbx₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB₀
  obtain hg : ∀ p < l.nl, Good l t₁.mem B M (l.oTab + l.NB * (i - 1)) p := fun p hp => by
    rw [me₁]; exact (h.tab (i - 1) (by omega_using [hi]) p hp).1
  refine WP.seq (WP.mono (ammCore2_ok hl (o := l.oTab + l.NB * i) (k := k) rbx₁ h8 h9 h11
    (h.scr.congr (by rw [k₁.2.2, hf.2.2.2.1]))
    (by rw [me₁]; exact h.ar) (by omega_using [o2, o5]) (by omega_using [o5, o9, hNi])
        (by omega_using [o5, o10, hNi, hNi1]) (by omega_using [o3, o10]) hg
    (fun p hp => by rw [me₁]; exact h.xg p hp))
    fun t₂ ⟨hv₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  obtain r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁.gpr (by decide)]; exact h13₀
  refine WP.mono (bodyTail_ok hl hi' (by omega_using [hi]) r13₂) fun t₃ ⟨r13₃, z₃, k₃, me₃, mx₃⟩ => ⟨⟨?_, r13₃, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₃⟩
  · rw [k₃.gpr (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact rbx₁
  · exact h.scr.congr (by rw [k₃.2.2, wr₂, k₁.2.2, hf.2.2.2.1])
  · rw [me₃]; exact ar₂
  · have hoD : l.oTab + l.NB * i + l.NB ≤ l.D := by omega_using [o5, o10, hNi]
    intro j hj p hp
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
    · have hNj : l.NB * j + l.NB ≤ l.NB * i := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      obtain hc : l.oTab + l.NB * j + l.NB ≤ l.oTab + l.NB * i ∨ l.oTab + l.NB * i + l.NB ≤ l.oTab + l.NB * j :=
        .inl (by omega_using [hNj])
      obtain hcD : l.oTab + l.NB * j + l.NB ≤ l.D := by omega_using [hoD, hNj]
      obtain ⟨g, v⟩ := h.tab j hj p hp
      refine ⟨?_, fun hq => ?_⟩
      · have g₁ : Good l t₁.mem B M (l.oTab + l.NB * j) p := by rw [me₁]; exact g
        rw [me₃]; exact g₁.of_out2 hl hp f₂ hc hcD hoD
      · rw [me₃, f₂.val hl hp hc hcD hoD, me₁]; exact v hq
    · obtain ⟨g, v⟩ := hv₂ p hp
      refine ⟨by rw [me₃]; exact g, fun hq => ?_⟩
      rw [me₁] at v
      obtain e := mont_mul2 (R := 2 ^ (52 * l.S)) (hR p hp) ((h.tab (j - 1) (by omega_using [hi]) p hp).2 hq) (h.xv hq p hp) v
      rw [show j - 1 + 1 = j by omega_using [hi]] at e
      rw [me₃]; exact e
  · intro p hp
    rw [me₃]
    obtain g₁ : Good l t₁.mem B M l.oY p := by rw [me₁]; exact h.yg p hp
    exact g₁.of_out2 hl hp f₂ (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]) (by omega_using [o5, o10, hNi])
  · intro hq p hp
    rw [me₃, f₂.val hl hp (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]) (by omega_using [o5, o10, hNi]), me₁]
    exact h.yv hq p hp
  · intro p hp
    rw [me₃]
    obtain g₁ : Good l t₁.mem B M l.oX p := by rw [me₁]; exact h.xg p hp
    exact g₁.of_out2 hl hp f₂ (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) (by omega_using [o5, o10, hNi])
  · intro hq p hp
    rw [me₃, f₂.val hl hp (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) (by omega_using [o5, o10, hNi]), me₁]
    exact h.xv hq p hp
  · rw [me₃]
    exact h.frame.trans (me₁ ▸ f₂.mono (by omega_using [o2, o5]) (by omega_using [hNi, o2, o5]))
  · intro r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    rw [k₃.gpr (by simp [r10]), g₂ r r1 r2 r3 r4 r6 r7 r9, k₁.gpr (by simp [r5, r6, r8]), hf.1]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  · rw [k₃.2.1, rd₂, k₁.2.1, hf.2.2.1, h.rd]
  · rw [k₃.2.2, wr₂, k₁.2.2, hf.2.2.2.1, h.wr]
  · rw [mx₃, x₂, mx₁, hf.2.2.2.2, h.mxcsr]

/-- What `convTab` starts from, `s₀`: the area's numbers, `Y ≡ R_W`,
`X ≡ x R_W`, `K1 ≡ 2^(416 R) / R_W` (`R_W = 2^(64 W)`). -/
structure ConvPre (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) : Prop where
  rbx : s₀.gpr .rbx = B
  scr : Scr s₀ B (l.nl * l.D)
  ar : Ar l s₀.mem B M k
  hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p)
  gx : ∀ p < l.nl, Good l s₀.mem B M l.oX p
  gy : ∀ p < l.nl, Good l s₀.mem B M l.oY p
  gk : ∀ p < l.nl, Good l s₀.mem B M l.oK1 p
  vx : Q → ∀ p < l.nl, val52 l s₀.mem B (l.D * p + l.oX) % M p = x p * 2 ^ l.cv % M p
  vy : Q → ∀ p < l.nl, val52 l s₀.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ l.cv % M p
  vk : Q → ∀ p < l.nl, val52 l s₀.mem B (l.D * p + l.oK1) % M p = 2 ^ (104 * l.S - l.cv) % M p

/-- The state before entry 0, from `s₀`. -/
structure At0 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ t : State) : Prop where
  r13 : t.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 0)
  mem : t.mem = s₀.mem
  gpr : ∀ r, r ≠ .r13 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- After entry 0, `Y` in Montgomery form, from `s₀`. -/
structure At1 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k : Nat → Nat) (t : State) : Prop where
  r13 : t.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 1)
  ar : Ar l t.mem B M k
  yg : ∀ p < l.nl, Good l t.mem B M l.oY p
  yv : ∀ p < l.nl, val52 l t.mem B (l.D * p + l.oY) * 2 ^ (52 * l.S) % M p =
    val52 l s₀.mem B (l.D * p + l.oY) * val52 l s₀.mem B (l.D * p + l.oK1) % M p
  f : Out2 l B l.oY l.NB s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r13 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- Entry 0: `Y` into Montgomery form. -/
theorem conv0_ok (hl : AmmOk l) {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hc : ConvPre l s₀ B M k x Q) (h : At0 l s₀ t) :
    WP isa (convTabBody l) t fun t' => At1 l s₀ B M k t' ∧ t'.zf = some false := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  unfold convTabBody
  refine bodyHead_ok hl (T_gt hl (by decide)) h.r13 (fun _ t₀ hf => ?_) fun h' => absurd h' (by decide)
  obtain hB₀ : t₀.gpr .rbx = B := by rw [hf.1, h.gpr _ (by decide)]; exact hc.rbx
  obtain h13₀ : t₀.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 0) := by rw [hf.1]; exact h.r13
  refine WP.mono (convSetup_ok hl hB₀ h13₀) fun t₁ ⟨h8, h9, h11, k₁, me₁, mx₁⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at h8 h11
  obtain me : t₁.mem = s₀.mem := by rw [me₁, hf.2.1, h.mem]
  obtain rbx₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB₀
  refine WP.seq (WP.mono (ammCore2_ok hl (o := l.oY) (M := M) (k := k) rbx₁ h8 h9 h11
    (hc.scr.congr (by rw [k₁.2.2, hf.2.2.2.1, h.wr])) (by rw [me]; exact hc.ar) (by omega_using [])
    (by omega_using [o2, o9]) (by omega_using [o2, o10]) (by omega_using [o7, o10])
    (by rw [me]; exact hc.gy) (by rw [me]; exact hc.gk))
    fun t₂ ⟨hv₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  obtain r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 0) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁.gpr (by decide)]; exact h13₀
  refine WP.mono (bodyTail_ok hl (T_gt hl (by decide)) (by decide) r13₂) fun t₃ ⟨r13₃, z₃, k₃, me₃, mx₃⟩ =>
    ⟨⟨r13₃, by rw [me₃]; exact ar₂, fun p hp => by rw [me₃]; exact (hv₂ p hp).1,
      fun p hp => by rw [me₃, ← me]; exact (hv₂ p hp).2, by rw [me₃, ← me]; exact f₂,
      fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_, by rw [k₃.2.1, rd₂, k₁.2.1, hf.2.2.1, h.rd],
      by rw [k₃.2.2, wr₂, k₁.2.2, hf.2.2.2.1, h.wr], by rw [mx₃, x₂, mx₁, hf.2.2.2.2, h.mxcsr]⟩,
      z₃.trans (congrArg some (dec_T hl (by decide)))⟩
  rw [k₃.gpr (by simp [r10]), g₂ r r1 r2 r3 r4 r6 r7 r9, k₁.gpr (by simp [r5, r6, r8]), hf.1, h.gpr r r10]

/-- Entry 1: `X` into Montgomery form, then the table's first two entries. -/
theorem conv1_ok (hl : AmmOk l) {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hc : ConvPre l s₀ B M k x Q) (h : At1 l s₀ B M k t) :
    WP isa (convTabBody l) t fun t' => TabInv l s₀ B M k x Q 2 t' ∧ t'.zf = some false := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain e2 : 2 ^ l.cv * 2 ^ (104 * l.S - l.cv) = 2 ^ (52 * l.S) * 2 ^ (52 * l.S) := by
    have := dbl_le hl
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using [this]
  obtain hB : t.gpr .rbx = B := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hc.rbx
  -- `X` and `K1` as in `s₀`
  obtain gx : ∀ p < l.nl, Good l t.mem B M l.oX p := fun p hp =>
    (hc.gx p hp).of_out2 hl hp h.f (.inr (by omega_using [o2, o3])) (by omega_using [o3, o10]) (by omega_using [o2, o10])
  obtain gk : ∀ p < l.nl, Good l t.mem B M l.oK1 p := fun p hp =>
    (hc.gk p hp).of_out2 hl hp h.f (.inr (by omega_using [o2, o7])) (by omega_using [o7, o10]) (by omega_using [o2, o10])
  unfold convTabBody
  refine bodyHead_ok hl (T_gt hl (by decide)) h.r13 (fun _ t₀ hf => ?_) fun h' => absurd h' (by decide)
  obtain hB₀ : t₀.gpr .rbx = B := by rw [hf.1]; exact hB
  obtain h13₀ : t₀.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 1) := by rw [hf.1]; exact h.r13
  refine WP.mono (convSetup_ok hl hB₀ h13₀) fun t₁ ⟨h8, h9, h11, k₁, me₁, mx₁⟩ => ?_
  rw [show l.oY + l.NB * 1 = l.oX by omega_using [o2, o3]] at h8 h11
  obtain me : t₁.mem = t.mem := by rw [me₁, hf.2.1]
  obtain rbx₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB₀
  refine WP.seq (WP.mono (ammCore2_ok hl (o := l.oX) (M := M) (k := k) rbx₁ h8 h9 h11
    (hc.scr.congr (by rw [k₁.2.2, hf.2.2.2.1, h.wr])) (by rw [me]; exact h.ar) (by omega_using [o2, o3])
    (by omega_using [o3, o9]) (by omega_using [o3, o10]) (by omega_using [o7, o10])
    (by rw [me]; exact gx) (by rw [me]; exact gk))
    fun t₂ ⟨hv₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  rw [me] at hv₂ f₂
  obtain r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 1) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁.gpr (by decide)]; exact h13₀
  obtain hB₂ : t₂.gpr .rbx = B := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rbx₁
  obtain hs₂ : Scr t₂ B (l.nl * l.D) := hc.scr.congr (by rw [wr₂, k₁.2.2, hf.2.2.2.1, h.wr])
  -- the copies
  obtain hNB := NB_le hl
  refine WP.seq (WP.mono (cmp13_ok t₂ r13₂ (by omega_using [hD, o5]) (by omega_using [hD, o5]))
    fun t₃ ⟨hz, _, hg₃, hm₃, hrd₃, hwr₃, hx₃⟩ => ?_)
  rw [Nat.mul_one, decide_eq_true rfl] at hz
  obtain hB₃ : t₃.gpr .rbx = B := by rw [hg₃]; exact hB₂
  refine WP.seq (WP.ite true hz (fun _ => ?_) fun h' => by cases h')
  rw [WP.block_append_iff]
  refine WP.mono (copyN_ok hl hB₃ (hs₂.congr hwr₃) (by omega_using [o5, o10]) (by omega_using [o2, o10])
    (.inl (by omega_using [o2, o5]))) fun t₄ ⟨l₄, f₄, g₄, rd₄, wr₄, x₄⟩ => ?_
  obtain hB₄ : t₄.gpr .rbx = B := by rw [g₄]; exact hB₃
  refine WP.mono (copyN_ok hl hB₄ (hs₂.congr (by rw [wr₄, hwr₃])) (by omega_using [o5, o10]) (by omega_using [o3, o10])
    (.inl (by omega_using [o3, o5]))) fun t₅ ⟨l₅, f₅, g₅, rd₅, wr₅, x₅⟩ => ?_
  rw [hm₃] at l₄ f₄
  obtain r13₅ : t₅.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 1) := by rw [g₅, g₄, hg₃]; exact r13₂
  refine WP.mono (tabTail_ok hl (T_gt hl (by decide)) r13₅) fun t₆ ⟨r13₆, z₆, k₆, me₆, mx₆⟩ =>
    ⟨?_, z₆.trans (congrArg some (dec_T hl (by decide)))⟩
  obtain hoD : l.oTab + l.NB ≤ l.D := by omega_using [o5, o10]
  obtain hoD' : l.oTab + l.NB + l.NB ≤ l.D := by omega_using [o5, o10]
  -- `Y` and `X` in Montgomery form, after the conversions
  obtain vy₂ : Q → ∀ p < l.nl, val52 l t₂.mem B (l.D * p + l.oY) % M p = x p ^ 0 * 2 ^ (52 * l.S) % M p :=
    fun hq p hp => by
      rw [f₂.val hl hp (.inl (by omega_using [o2, o3])) (by omega_using [o2, o10]) (by omega_using [o3, o10])]
      exact mont_into0 (hc.hR p hp) (hc.vy hq p hp) (hc.vk hq p hp) e2 (h.yv p hp)
  obtain gy₂ : ∀ p < l.nl, Good l t₂.mem B M l.oY p := fun p hp =>
    (h.yg p hp).of_out2 hl hp f₂ (.inl (by omega_using [o2, o3])) (by omega_using [o2, o10]) (by omega_using [o3, o10])
  obtain vx₂ : Q → ∀ p < l.nl, val52 l t₂.mem B (l.D * p + l.oX) % M p = x p ^ 1 * 2 ^ (52 * l.S) % M p :=
    fun hq p hp => by
      obtain e := (hv₂ p hp).2
      rw [h.f.val hl hp (.inr (by omega_using [o2, o3])) (by omega_using [o3, o10]) (by omega_using [o2, o10]),
        h.f.val hl hp (.inr (by omega_using [o2, o7])) (by omega_using [o7, o10]) (by omega_using [o2, o10])] at e
      exact mont_into1 (hc.hR p hp) (hc.vx hq p hp) (hc.vk hq p hp) e2 e
  -- through the copies
  obtain keepY : ∀ {c : Nat}, c + l.NB ≤ l.oTab → ∀ p < l.nl, (Good l t₂.mem B M c p → Good l t₆.mem B M c p) ∧
      val52 l t₆.mem B (l.D * p + c) = val52 l t₂.mem B (l.D * p + c) := fun {c} hcT p hp => by
    obtain hcD : c + l.NB ≤ l.D := by omega_using [hcT, o5, o10]
    refine ⟨fun g => ?_, ?_⟩
    · rw [me₆]
      exact (g.of_out2 hl hp f₄ (.inl hcT) hcD hoD).of_out2 hl hp f₅ (.inl (by omega_using [hcT])) hcD hoD'
    · rw [me₆, f₅.val hl hp (.inl (by omega_using [hcT])) hcD hoD', f₄.val hl hp (.inl hcT) hcD hoD]
  refine ⟨?_, by rw [r13₆], hs₂.congr (by rw [k₆.2.2, wr₅, wr₄, hwr₃]), ?_, fun j hj p hp => ?_,
    fun p hp => (keepY (by omega_using [o2, o5]) p hp).1 (gy₂ p hp),
    fun hq p hp => by rw [(keepY (by omega_using [o2, o5]) p hp).2]; exact vy₂ hq p hp,
    fun p hp => (keepY (by omega_using [o3, o5]) p hp).1 (hv₂ p hp).1,
    fun hq p hp => by rw [(keepY (by omega_using [o3, o5]) p hp).2]; exact vx₂ hq p hp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₆.gpr (by decide), g₅, g₄, hg₃]; exact hB₂
  · rw [me₆]
    exact (ar₂.of_out2 hl f₄ (by omega_using [o2, o5]) (by omega_using [o5, o9])).of_out2 hl f₅
      (by omega_using [o2, o5]) (by omega_using [o5, o9])
  · rw [me₆]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
    · rw [Nat.mul_zero, Nat.add_zero]
      obtain g0 := ((gy₂ p hp).of_limbs (l₄ p hp)).of_out2 hl hp f₅ (.inl (by omega_using [])) (by omega_using [hoD']) hoD'
      refine ⟨g0, fun hq => ?_⟩
      rw [f₅.val hl hp (.inl (by omega_using [])) (by omega_using [hoD']) hoD', val52_of_limbs (l₄ p hp)]
      exact vy₂ hq p hp
    · rw [Nat.mul_one]
      obtain gx₄ : Good l t₄.mem B M l.oX p :=
        (hv₂ p hp).1.of_out2 hl hp f₄ (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) hoD
      refine ⟨gx₄.of_limbs (l₅ p hp), fun hq => ?_⟩
      rw [val52_of_limbs (l₅ p hp), f₄.val hl hp (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) hoD]
      exact vx₂ hq p hp
  · rw [me₆]
    obtain hT2 := tab_le hl (T_gt hl (show 1 < 16 by decide))
    exact (((h.f.mono (by omega_using []) (by omega_using [o2, o5, hT2])).trans
      (f₂.mono (by omega_using [o2, o3]) (by omega_using [o3, o5, hT2]))).trans
      (f₄.mono (by omega_using [o2, o5]) (by omega_using [o5, hT2]))).trans
      (f₅.mono (by omega_using [o2, o5]) (by omega_using [o5, hT2]))
  · intro r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    rw [k₆.gpr (by simp [r10]), g₅, g₄, hg₃, g₂ r r1 r2 r3 r4 r6 r7 r9, k₁.gpr (by simp [r5, r6, r8]), hf.1]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  · rw [k₆.2.1, rd₅, rd₄, hrd₃, rd₂, k₁.2.1, hf.2.2.1, h.rd]
  · rw [k₆.2.2, wr₅, wr₄, hwr₃, wr₂, k₁.2.2, hf.2.2.2.1, h.wr]
  · rw [mx₆, x₅, x₄, hx₃, x₂, mx₁, hf.2.2.2.2, h.mxcsr]

/-- The loop of `convTab`. -/
theorem convTabLoop_ok (hl : AmmOk l) {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hc : ConvPre l s₀ B M k x Q) (h : At0 l s₀ t) :
    WP isa (.loop (convTabBody l) .ne) t (TabInv l s₀ B M k x Q l.T) := by
  have hT := hl.T_bounds
  refine WP.loop (M := isa) (c := .ne) (Q := TabInv l s₀ B M k x Q l.T)
    (fun n t => (n = l.T ∧ At0 l s₀ t) ∨ (n = l.T - 1 ∧ At1 l s₀ B M k t) ∨
      (1 ≤ n ∧ n ≤ l.T - 2 ∧ TabInv l s₀ B M k x Q (l.T - n) t)) ?_ l.T t (.inl ⟨rfl, h⟩)
  rintro n t (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h1, h14, hI⟩)
  · refine WP.mono (conv0_ok hl hc h) fun t' ⟨h', hz⟩ =>
      .inr ⟨?_, l.T - 1, by omega_using [hT.1, hT.2], .inr (.inl ⟨rfl, h'⟩)⟩
    simp only [eval, hz, Option.map_some, Bool.not_false]
  · refine WP.mono (conv1_ok hl hc h) fun t' ⟨h', hz⟩ =>
      .inr ⟨?_, l.T - 2, by omega_using [hT.1, hT.2], .inr (.inr ⟨by omega_using [hT.1, hT.2], Nat.le_refl _,
        by rw [show l.T - (l.T - 2) = 2 by omega_using [hT.1, hT.2]]; exact h'⟩)⟩
    simp only [eval, hz, Option.map_some, Bool.not_false]
  · refine WP.mono (tabIter_ok hl (i := l.T - n) (by omega_using [h14, h1, hT.1]) (by omega_using [h1, hT.1]) hc.hR hI)
      fun t' ⟨hI', hz⟩ => ?_
    simp only [eval, hz, Option.map_some]
    rcases Nat.eq_or_lt_of_le h1 with rfl | hn
    · rw [show l.T - 1 + 1 = l.T by omega_using [hT.1, hT.2]] at hI'
      exact .inl ⟨by simp only [show l.T - 1 + 1 = l.T by omega_using [hT.1, hT.2], decide_true, Bool.not_true], hI'⟩
    · refine .inr ⟨by simp only [decide_eq_false (show ¬ (l.T - n + 1 = l.T) by omega_using [hn, h14]),
          Bool.not_false], n - 1,
        by omega_using [hn], .inr (.inr ⟨by omega_using [hn], by omega_using [h14],
          by rw [show l.T - (n - 1) = l.T - n + 1 by omega_using [h14, hn]]; exact hI'⟩)⟩

/-- `convTab`: `Y`, `X` in Montgomery form and the table `T_i ≡ x^i 2^(208 R)`. -/
theorem convTab_ok (hl : AmmOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hc : ConvPre l s B M k x Q) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (convTab l)) s (TabInv l s B M k x Q l.T) := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s.setReg32 .r13 (BitVec.ofNat 32 l.oTab), rfl, WP.block_nil ?_⟩
  refine convTabLoop_ok hl hc ⟨?_, rfl, fun r hr => by rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl⟩
  rw [State.setReg32, RegUpd.gpr_setReg_self, Nat.mul_zero, Nat.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := l.oTab) (b := 2 ^ 32) (by omega_using [hD, o5]),
    Nat.mod_eq_of_lt (a := l.oTab) (b := 2 ^ 64) (by omega_using [hD, o5])]

end VG.Proof.Bignum.X86_64.Ifma

end

end

/-!
# RSA with AVX512_IFMA on x86-64, any size: a window of the exponentiations

`ExpSt`: the regions' moduli (`Ar`), the table
(`T_j ≡ x^j R`) and `Y ≡ x^E R` for each prime, `R = 2^(208 R)`. A window
(`window_ok`) copies each prime's digit `v` (a byte at `oD`, below `T = 2^w`)
to its quadword at `oV` (`ldD_ok`), reads `T_v` into `S` (`select_ok`),
squares `Y` `w` times (`sq_ok`) and multiplies it by `S` (`mulS_ok`):
`Y ≡ x^(T E + v) R`. It writes only `Y`, `S` and `V` of each region
(`OutW`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (mont_mul2 r15Dec_ok ea_at' ea_idx wp_seqs_app se_ofNat ofs_off0)
open VG.Proof.Bignum.X86_64 (ofNat_sub_beq)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The state of the exponentiations: `Y ≡ x^E R`. -/
structure ExpSt (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (E : Nat → Nat) : Prop where
  ar : Ar l m B M k
  tab : ∀ j < l.T, ∀ p < l.nl, Good l m B M (l.oTab + l.NB * j) p ∧
    (Q → val52 l m B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.S) % M p)
  y : ∀ p < l.nl, Good l m B M l.oY p
  yv : Q → ∀ p < l.nl, val52 l m B (l.D * p + l.oY) % M p = x p ^ E p * 2 ^ (52 * l.S) % M p

/-- `m'` agrees with `m` but on `Y`, `S` and `V` of each region. -/
def OutW (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (m m' : Mem) : Prop :=
  ∀ a, (∀ p < l.nl, (ofs B a < l.D * p + l.oY ∨ l.D * p + l.oY + l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oS ∨ l.D * p + l.oS + l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oV ∨ l.D * p + l.oV + 8 ≤ ofs B a)) →
    m' a = m a

theorem OutW.refl (B : Addr) (m : Mem) : OutW l B m m := fun _ _ => rfl

theorem OutW.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : OutW l B m₁ m₂) (h₂ : OutW l B m₂ m₃) : OutW l B m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem OutW.ofY {B : Addr} {m m' : Mem} (h : Out2 l B l.oY l.NB m m') : OutW l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).1

theorem OutW.ofS {B : Addr} {m m' : Mem} (h : Out2 l B l.oS l.NB m m') : OutW l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).2.1

theorem OutW.ofV {B : Addr} {m m' : Mem} (h : Out2 l B l.oV 8 m m') : OutW l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).2.2

/-- The table after a write elsewhere. -/
theorem ExpSt.tab_of (hl : AmmOk l) {m m' : Mem} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (h : ExpSt l m B M k x Q E) {o n : Nat} (hf : Out2 l B o n m m')
    (ho : o + n ≤ l.oTab ∨ l.oTab + l.T * l.NB ≤ o) (hoD : o + n ≤ l.D) :
    ∀ j < l.T, ∀ p < l.nl, Good l m' B M (l.oTab + l.NB * j) p ∧
      (Q → val52 l m' B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.S) % M p) :=
  fun j hj p hp => by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain hNj : l.NB * j + l.NB ≤ l.T * l.NB := tab_le hl hj
  obtain hc : l.oTab + l.NB * j + l.NB ≤ o ∨ o + n ≤ l.oTab + l.NB * j := by
    rcases ho with ho | ho
    · exact .inr (by omega_using [ho])
    · exact .inl (by omega_using [hNj, ho])
  obtain hcD : l.oTab + l.NB * j + l.NB ≤ l.D := by omega_using [o5, o10, hNj]
  obtain ⟨g, v⟩ := h.tab j hj p hp
  exact ⟨g.of_out2 hl hp hf hc hcD hoD, fun hq => by rw [hf.val hl hp hc hcD hoD]; exact v hq⟩

/-- `Y := Y² / R`: `x^E R` becomes `x^(2E) R`. -/
theorem sq_ok (hl : AmmOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) :
    WP isa (amm l l.oY l.oY l.oY) s fun s' => ExpSt l s'.mem B M k x Q (fun p => 2 * E p) ∧
      Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (amm2_ok hl hB hs h.ar (by omega_using []) (by omega_using [o2, o9]) (by omega_using [o2, o10])
      (by omega_using [o2, o10]) h.y h.y)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hl hf (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
  exact VG.Proof.Bignum.mont_sq (hR p hp) (h.yv hq p hp) (hv p hp).2

/-- `Y := Y S / R`: `x^E R` and `S ≡ x^v R` give `x^(E+v) R`. -/
theorem mulS_ok (hl : AmmOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E v : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) (gs : ∀ p < l.nl, Good l s.mem B M l.oS p)
    (vs : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oS) % M p = x p ^ v p * 2 ^ (52 * l.S) % M p) :
    WP isa (amm l l.oY l.oY l.oS) s fun s' => ExpSt l s'.mem B M k x Q (fun p => E p + v p) ∧
      Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (amm2_ok hl hB hs h.ar (by omega_using []) (by omega_using [o2, o9]) (by omega_using [o2, o10])
      (by omega_using [o4, o10]) h.y gs)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hl hf (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
  exact mont_mul2 (hR p hp) (h.yv hq p hp) (vs hq p hp) (hv p hp).2

theorem eaG' (t : State) (r : Reg) (d : Nat) : t.ea (at_ r d) = t.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  exact congrArg _ (BitVec.ofInt_natCast ..)

/-- The byte that holds digit `i`: with windows of 4 bits, byte `i / 2` of
the padded exponent (two digits a byte); otherwise the digit's own, at `oD`. -/
def dAt (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (i : Nat) : Nat := if l.w = 4 then l.oE + i / 2 else l.oD + i

/-- Digit `i` from the byte `b` that holds it. -/
def nibOf (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (i b : Nat) : Nat :=
  if l.w = 4 then (if i % 2 = 0 then b / 16 else b % 16) else b

/-- Digit `i` of prime `p`'s exponent. -/
abbrev dig (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (p i : Nat) : Nat :=
  nibOf l i (m (off B (l.D * p + dAt l i))).toNat

/-- The digits, for windows of more than 4 bits, end before `K1`. -/
theorem lay_oD (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (hw : l.w ≠ 4) : l.oE + l.P ≤ l.oD ∧ l.oD + l.ND ≤ l.oK1 := by
  simp only [Lay.oD, Lay.oK1, Lay.XE, hw, ite_false]; omega_using []

/-- The padded exponent: `E ≤ P`, `P` in whole quadwords at most `XE` bytes. -/
theorem lay_P (hl : AmmOk l) : l.E ≤ l.P ∧ l.P ≤ 8 * ((l.P + 7) / 8) ∧ 8 * ((l.P + 7) / 8) ≤ l.XE ∧
    l.oD = l.oE + (l.P + 31) / 32 * 32 ∧ l.oE + l.XE = l.oK1 ∧ 8 * ((l.P + 7) / 8) ≤ (l.P + 31) / 32 * 32 := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The byte of each digit is in `[oE, oK1)`. -/
theorem lay_dAt (hl : AmmOk l) {i : Nat} (hi : i < l.ND) : l.oE ≤ dAt l i ∧ dAt l i < l.oK1 := by
  unfold dAt
  split
  · rename_i hw
    obtain ⟨p1, p2, p3, -, p5, -⟩ := lay_P hl
    obtain hND : l.ND = 8 * (l.P / 4) := by simp only [Lay.ND, hw]
    omega_arith
  · rename_i hw
    have := lay_oD l hw
    omega_arith

/-- The windows: `w` bits, 4 or 5. -/
theorem AmmOk.w_bounds (hl : AmmOk l) : 4 ≤ l.w ∧ l.w ≤ 5 := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Digit `i` of prime `p` into its quadword `V`. -/
theorem ldD_ok (hl : AmmOk l) (hw : l.w ≠ 4) {s : State} {B : Addr} {p i : Nat} (hp : p < l.nl) (hi : i < l.ND)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (l.nl * l.D)) :
    WP isa (.block [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * p + l.oD : Nat) : Int) },
        .store (at_ .rbx (l.D * p + l.oV)) .rax]) s fun s' =>
      s'.mem = s.mem.writeW (off B (l.D * p + l.oV)) (BitVec.ofNat 64 (s.mem (off B (l.D * p + l.oD + i))).toNat) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨d1, d2⟩ := lay_oD l hw
  obtain hDp : l.D * p ≤ l.D ∧ l.D * p + l.D ≤ l.nl * l.D ∧ l.nl * l.D ≤ 2 * l.D := ⟨D_le hl hp, lane_end hl hp, (nlD_le hl).2⟩
  obtain hle := lane_end hl hp
  obtain e : B + BitVec.ofNat 64 i + BitVec.ofNat 64 (l.D * p + l.oD) = off B (l.D * p + l.oD + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm i]
  obtain hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 i + BitVec.ofNat 64 (l.D * p + l.oD)) 1 := by
    rw [e]
    obtain ⟨r, h, c⟩ := hs.region (d := l.D * p + l.oD + i) (n := 1) (by omega_using [hi, d2, o7, o10, hDp, hle])
      (by decide)
    exact ⟨r, List.mem_append_right _ h, c⟩
  obtain hst : InRegions s.wr (B + BitVec.ofNat 64 (l.D * p + l.oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := l.D * p + l.oV) (n := 8) (by omega_using [o8, o10, hDp, hle]) (by decide); ⟨_, h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (l.D * p + l.oV)) (BitVec.ofNat 64 (s.mem (off B (l.D * p + l.oD + i))).toNat) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [ea_idx, eaG', hB, h13, hld, hst]
    rw [e, BitVec.ofNat_toNat]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

theorem ea_idx8 (t : State) (d : Nat) :
    t.ea { base := .rbx, index := some .r8, disp := ((d : Nat) : Int) } =
      t.gpr .rbx + t.gpr .r8 + BitVec.ofNat 64 d := by
  simp only [State.ea, BitVec.mul_one]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem ofNat_ushr1 {i : Nat} (hi : i < 2 ^ 64) : BitVec.ofNat 64 i >>> 1 = BitVec.ofNat 64 (i / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow, Nat.pow_one]

/-- `nibSel`'s value: the nibble of the byte `b` that digit `i` is. -/
theorem nib_val (hw : l.w = 4) (b : BitVec 8) (i : Nat) :
    (BitVec.setWidth 64 b &&& BitVec.signExtend 64 (15 : BitVec 32) ^^^
      (BitVec.setWidth 64 b >>> 4 ^^^ BitVec.setWidth 64 b &&& BitVec.signExtend 64 (15 : BitVec 32)) &&&
        ((BitVec.ofNat 64 i &&& 1) - 1)) = BitVec.ofNat 64 (nibOf l i b.toNat) := by
  obtain h15 : BitVec.signExtend 64 (15 : BitVec 32) = (15 : BitVec 64) := by decide
  have hb := b.isLt
  obtain hi : BitVec.ofNat 64 i &&& 1 = BitVec.ofNat 64 (i % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.and_one_is_mod]
    omega_arith
  rw [h15, hi]
  simp only [nibOf, hw, ite_true]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, show BitVec.ofNat 64 0 - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_comm (BitVec.setWidth 64 b &&& 15), BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    simp only [ite_true]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  · rw [h, show BitVec.ofNat 64 1 - 1 = 0#64 by decide, BitVec.and_zero, BitVec.xor_zero]
    simp only [Nat.one_ne_zero, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega_arith

/-- Each lane's digit `i` in its quadword `V`, and nothing else written. -/
structure DigOut (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (i : Nat) (m m' : Mem) : Prop where
  w : ∀ p < l.nl, word m' B (l.D * p + l.oV) = BitVec.ofNat 64 (dig l m B p i)
  f : Out2 l B l.oV 8 m m'

theorem AmmOk.nl12 (hl : AmmOk l) : l.nl = 1 ∨ l.nl = 2 := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

/-- One lane's digit, written. -/
theorem DigOut.of_one (hn : l.nl = 1) {B : Addr} {i : Nat} {m m' : Mem}
    (hm : m' = m.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l m B 0 i))) (hb : l.oV + 8 ≤ 2 ^ 63) :
    DigOut l B i m m' := by
  refine ⟨fun p hp => ?_, Out2.of_outside (p := 0) (by omega_arith) (by rw [hm]; exact writeW_outside _ B _ (by omega_using [hb]))⟩
  obtain rfl : p = 0 := by omega_arith
  rw [hm, VG.Proof.Bignum.word_writeW_self]

/-- Two lanes' digits, written. -/
theorem DigOut.of_two (hn : l.nl = 2) {B : Addr} {i : Nat} {m m' : Mem}
    (hm : m' = (m.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l m B 0 i))).writeW
        (off B (l.D * 1 + l.oV)) (BitVec.ofNat 64 (dig l m B 1 i)))
    (hb : l.D + l.oV + 8 ≤ 2 ^ 63) (hv : l.oV + 8 ≤ l.D) : DigOut l B i m m' := by
  obtain o₁ : Outside B (l.D * 0 + l.oV) 8 m (m.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l m B 0 i))) :=
    writeW_outside _ B _ (by omega_using [hb])
  obtain o₂ : Outside B (l.D * 1 + l.oV) 8
      (m.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l m B 0 i))) m' := by
    rw [hm]; exact writeW_outside _ B _ (by omega_using [hb])
  refine ⟨fun p hp => ?_, (Out2.of_outside (p := 0) (by omega_arith) o₁).trans (Out2.of_outside (p := 1) (by omega_arith) o₂)⟩
  rcases (by omega_arith : p = 0 ∨ p = 1) with rfl | rfl
  · rw [o₂.word (by omega_using [hv]) (by omega_using [hb]), VG.Proof.Bignum.word_writeW_self]
  · rw [hm, VG.Proof.Bignum.word_writeW_self]

/-- With windows of 4 bits and two lanes: both primes' digits `i`, nibbles of byte `i / 2`
of their padded exponents, into their quadwords `V`. -/
theorem digNib2_ok (hl : AmmOk l) (hn : l.nl = 2) (hw : l.w = 4) {s : State} {B : Addr} {i : Nat} (hi : i < l.ND)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (l.nl * l.D)) :
    WP isa (.block (digLoad l)) s fun s' =>
      s'.mem = (s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i))).writeW
        (off B (l.D * 1 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 1 i)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .r8] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨a1, a2⟩ := lay_dAt hl hi
  have hD := hl.D_bounds
  rw [hn] at hs
  obtain hdA : dAt l i = l.oE + i / 2 := by simp only [dAt, hw, ite_true]
  have hn' := hs.nowrap
  obtain hND : l.ND < 2 ^ 31 := by rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hsh : BitVec.ofNat 64 i >>> 1 = BitVec.ofNat 64 (i / 2) := ofNat_ushr1 (by omega_using [hi, hND])
  obtain e0 : B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 (l.D * 0 + l.oE) = off B (l.D * 0 + dAt l i) := by
    rw [hdA, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  obtain e1 : B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 (l.D * 1 + l.oE) = off B (l.D * 1 + dAt l i) := by
    rw [hdA, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  obtain r0 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 (l.D * 0 + l.oE)) 1 := by
    rw [e0]
    obtain ⟨r, h, c⟩ := hs.region (d := l.D * 0 + dAt l i) (n := 1) (by omega_using [a2, o7, o10, hD]) (by decide)
    exact ⟨r, List.mem_append_right _ h, c⟩
  obtain r1 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 (l.D * 1 + l.oE)) 1 := by
    rw [e1]
    obtain ⟨r, h, c⟩ := hs.region (d := l.D * 1 + dAt l i) (n := 1) (by omega_using [a2, o7, o10, hD]) (by decide)
    exact ⟨r, List.mem_append_right _ h, c⟩
  obtain w0 : InRegions s.wr (B + BitVec.ofNat 64 (l.D * 0 + l.oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := l.D * 0 + l.oV) (n := 8) (by omega_using [o8, o10, hD]) (by decide); ⟨_, h, c⟩
  obtain w1 : InRegions s.wr (B + BitVec.ofNat 64 (l.D * 1 + l.oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := l.D * 1 + l.oV) (n := 8) (by omega_using [o8, o10, hD]) (by decide); ⟨_, h, c⟩
  rw [show digLoad l = ([.mov .r8 (.reg .r13), .shift .shr .r8 1, .mov .rdx (.reg .r13), .alu .and .rdx (.imm 1),
      .alu .sub .rdx (.imm 1),
      .movzx8 .rax { base := .rbx, index := some .r8, disp := ((l.D * 0 + l.oE : Nat) : Int) },
      .movzx8 .rsi { base := .rbx, index := some .r8, disp := ((l.D * 1 + l.oE : Nat) : Int) }] : List Instr) ++
    nibSel .rax ++ ([.store (at_ .rbx (l.D * 0 + l.oV)) .rax] : List Instr) ++
    nibSel .rsi ++ ([.store (at_ .rbx (l.D * 1 + l.oV)) .rsi] : List Instr) by
      simp only [digLoad, hw, hn, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, dReg, ↓reduceIte, show (1 : Nat) ≠ 0 from by decide,
        List.append_assoc, List.cons_append, List.nil_append, List.append_nil]]
  simp only [nibSel, List.cons_append, List.nil_append]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rdx, .rsi, .r8] (Q := fun s' =>
    s'.mem = (s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i))).writeW
        (off B (l.D * 1 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 1 i)) ∧ s'.mxcsr = s.mxcsr) (by
    xrun [ea_idx8, eaG', hB, h13, hsh, r0, r1, w0, w1]
    refine ⟨?_, rfl⟩
    rw [e0, e1, nib_val hw, nib_val hw]) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

/-- With windows of 4 bits and one lane: its digit `i`, a nibble of byte `i / 2`
of its padded exponent, into its quadword `V`. -/
theorem digNib1_ok (hl : AmmOk l) (hn : l.nl = 1) (hw : l.w = 4) {s : State} {B : Addr} {i : Nat} (hi : i < l.ND)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (l.nl * l.D)) :
    WP isa (.block (digLoad l)) s fun s' =>
      s'.mem = s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .r8] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨a1, a2⟩ := lay_dAt hl hi
  have hD := hl.D_bounds
  rw [hn, Nat.one_mul] at hs
  obtain hdA : dAt l i = l.oE + i / 2 := by simp only [dAt, hw, ite_true]
  obtain hND : l.ND < 2 ^ 31 := by rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hsh : BitVec.ofNat 64 i >>> 1 = BitVec.ofNat 64 (i / 2) := ofNat_ushr1 (by omega_using [hi, hND])
  obtain e0 : B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 (l.D * 0 + l.oE) = off B (l.D * 0 + dAt l i) := by
    rw [hdA, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  obtain r0 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 (l.D * 0 + l.oE)) 1 := by
    rw [e0]
    obtain ⟨r, h, c⟩ := hs.region (d := l.D * 0 + dAt l i) (n := 1) (by omega_using [a2, o7, o10, hD]) (by decide)
    exact ⟨r, List.mem_append_right _ h, c⟩
  obtain w0 : InRegions s.wr (B + BitVec.ofNat 64 (l.D * 0 + l.oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := l.D * 0 + l.oV) (n := 8) (by omega_using [o8, o10, hD]) (by decide); ⟨_, h, c⟩
  rw [show digLoad l = ([.mov .r8 (.reg .r13), .shift .shr .r8 1, .mov .rdx (.reg .r13), .alu .and .rdx (.imm 1),
      .alu .sub .rdx (.imm 1),
      .movzx8 .rax { base := .rbx, index := some .r8, disp := ((l.D * 0 + l.oE : Nat) : Int) }] : List Instr) ++
    nibSel .rax ++ ([.store (at_ .rbx (l.D * 0 + l.oV)) .rax] : List Instr) by
      simp only [digLoad, hw, hn, show List.range 1 = [0] from rfl, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, dReg, ↓reduceIte, List.cons_append,
        List.nil_append, List.append_nil]]
  simp only [nibSel, List.cons_append, List.nil_append]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rdx, .rsi, .r8] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i)) ∧ s'.mxcsr = s.mxcsr) (by
    xrun [ea_idx8, eaG', hB, h13, hsh, r0, w0]
    refine ⟨?_, rfl⟩
    rw [e0, nib_val hw]) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

theorem Outside.limbG (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {c : Nat}
    (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hc' : c + l.NB ≤ 2 ^ 64) {j : Nat} (hj : j < l.L) :
    limb l m' B c j = limb l m B c j := by
  have := off_ltN hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [h.word (by omega_using [hc, this]) (by omega_using [hc', this])]

/-- `S := T_v` for both primes, with two lanes. -/
theorem sel2_ok (hl : AmmOk l) (hn2 : l.nl = 2) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (h : ExpSt l s.mem B M k x Q E)
    (hv : ∀ p < l.nl, nib l s.mem B p < l.T) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (select l 0 ++ select l 1))
      s fun s' => ExpSt l s'.mem B M k x Q E ∧
        (∀ p < l.nl, Good l s'.mem B M l.oS p ∧
          (Q → val52 l s'.mem B (l.D * p + l.oS) % M p = x p ^ nib l s.mem B p * 2 ^ (52 * l.S) % M p)) ∧
        (∀ p < l.nl, word s'.mem B (l.D * p + l.oV) = word s.mem B (l.D * p + l.oV)) ∧
        Out2 l B l.oS l.NB s.mem s'.mem ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hs2 := hs
  rw [hn2] at hs2
  have hn := hs2.nowrap
  refine wp_seqs_app (by simp [select]) (by simp [select])
    (WP.mono (select_ok hl (p := 0) (by omega_arith) hB hs (hv 0 (by omega_arith))) fun s₁ ⟨l₁, o₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  obtain hB₁ : s₁.gpr .rbx = B := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hB
  obtain v₁ : nib l s₁.mem B 1 = nib l s.mem B 1 := by
    unfold nib; rw [o₁.word (by omega_using [o4, o10]) (by omega_using [o8, o10, hn])]
  refine WP.mono (select_ok hl (p := 1) (by omega_arith) hB₁ (hs.congr wr₁) (by rw [v₁]; exact hv 1 (by omega_arith)))
    fun s₂ ⟨l₂, o₂, g₂, rd₂, wr₂, x₂⟩ => ?_
  obtain f₁ : Out2 l B l.oS l.NB s.mem s₁.mem := Out2.of_outside (p := 0) (by omega_arith) o₁
  obtain f₂ : Out2 l B l.oS l.NB s₁.mem s₂.mem := Out2.of_outside (p := 1) (by omega_arith) o₂
  obtain ex₁ := h.tab_of hl f₁ (.inl (by omega_using [o4, o5])) (by omega_using [o4, o10])
  -- entry 0 and entry 1
  obtain hv0 := hv 0 (by omega_arith)
  obtain hv1 := hv 1 (by omega_arith)
  obtain t0 := h.tab (nib l s.mem B 0) hv0 0 (by omega_arith)
  obtain t1 := ex₁ (nib l s.mem B 1) hv1 1 (by omega_arith)
  obtain L0 : ∀ q < l.L, limb l s₂.mem B (l.D * 0 + l.oS) q =
      limb l s.mem B (l.D * 0 + (l.oTab + l.NB * nib l s.mem B 0)) q := fun q hq => by
    rw [Outside.limbG hl o₂ (.inl (by omega_using [hD])) (by omega_using [o4, hD]) hq, l₁ q hq, Nat.add_assoc]
  obtain L1 : ∀ q < l.L, limb l s₂.mem B (l.D * 1 + l.oS) q =
      limb l s₁.mem B (l.D * 1 + (l.oTab + l.NB * nib l s.mem B 1)) q :=
    fun q hq => by rw [l₂ q hq, v₁, Nat.add_assoc]
  refine ⟨⟨?_, h.tab_of hl (f₁.trans f₂) (.inl (by omega_using [o4, o5])) (by omega_using [o4, o10]), fun p hp => ?_, fun hq p hp => ?_⟩,
    fun p hp => ?_, fun p hp => ?_, f₁.trans f₂, fun r r1 r2 r3 r4 => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [x₂, x₁]⟩
  · exact (h.ar.of_out2 hl f₁ (by omega_using [o2, o4]) (by omega_using [o4, o9])).of_out2 hl f₂
      (by omega_using [o2, o4]) (by omega_using [o4, o9])
  · exact (h.y p hp).of_out2 hl hp (f₁.trans f₂) (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  · rw [(f₁.trans f₂).val hl hp (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])]; exact h.yv hq p hp
  · rcases (lane01 hl hp) with rfl | rfl
    · exact ⟨t0.1.of_limbs L0, fun hq => by rw [val52_of_limbs L0]; exact t0.2 hq⟩
    · exact ⟨t1.1.of_limbs L1, fun hq => by rw [val52_of_limbs L1]; exact t1.2 hq⟩
  · rw [(f₁.trans f₂).word_at hl hp (.inr (by omega_using [o4, o8])) (by omega_using [o8, o10]) (by omega_using [o4, o10])]
  · rw [g₂ r r1 r2 r3 r4, g₁ r r1 r2 r3 r4]

/-- `S := T_v` for the lane, with one. -/
theorem sel1_ok (hl : AmmOk l) (hn : l.nl = 1) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (h : ExpSt l s.mem B M k x Q E)
    (hv : ∀ p < l.nl, nib l s.mem B p < l.T) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (select l 0))
      s fun s' => ExpSt l s'.mem B M k x Q E ∧
        (∀ p < l.nl, Good l s'.mem B M l.oS p ∧
          (Q → val52 l s'.mem B (l.D * p + l.oS) % M p = x p ^ nib l s.mem B p * 2 ^ (52 * l.S) % M p)) ∧
        (∀ p < l.nl, word s'.mem B (l.D * p + l.oV) = word s.mem B (l.D * p + l.oV)) ∧
        Out2 l B l.oS l.NB s.mem s'.mem ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  refine WP.mono (select_ok hl (p := 0) (by omega_arith) hB hs (hv 0 (by omega_arith)))
    fun s₁ ⟨l₁, o₁, g₁, rd₁, wr₁, x₁⟩ => ?_
  obtain f₁ : Out2 l B l.oS l.NB s.mem s₁.mem := Out2.of_outside (p := 0) (by omega_arith) o₁
  obtain t0 := h.tab (nib l s.mem B 0) (hv 0 (by omega_arith)) 0 (by omega_arith)
  obtain L0 : ∀ q < l.L, limb l s₁.mem B (l.D * 0 + l.oS) q =
      limb l s.mem B (l.D * 0 + (l.oTab + l.NB * nib l s.mem B 0)) q := fun q hq => by rw [l₁ q hq, Nat.add_assoc]
  refine ⟨⟨h.ar.of_out2 hl f₁ (by omega_using [o2, o4]) (by omega_using [o4, o9]),
      h.tab_of hl f₁ (.inl (by omega_using [o4, o5])) (by omega_using [o4, o10]), fun p hp => ?_, fun hq p hp => ?_⟩,
    fun p hp => ?_, fun p hp => ?_, f₁, g₁, rd₁, wr₁, x₁⟩
  · exact (h.y p hp).of_out2 hl hp f₁ (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  · rw [f₁.val hl hp (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])]; exact h.yv hq p hp
  · obtain rfl : p = 0 := by omega_arith
    exact ⟨t0.1.of_limbs L0, fun hq => by rw [val52_of_limbs L0]; exact t0.2 hq⟩
  · rw [f₁.word_at hl hp (.inr (by omega_using [o4, o8])) (by omega_using [o8, o10]) (by omega_using [o4, o10])]

/-- `S := T_v` for each lane. -/
theorem selAll_ok (hl : AmmOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (h : ExpSt l s.mem B M k x Q E)
    (hv : ∀ p < l.nl, nib l s.mem B p < l.T) :
    WP isa (VG.Impl.Bignum.X86_64.seqs ((List.range l.nl).flatMap (select l)))
      s fun s' => ExpSt l s'.mem B M k x Q E ∧
        (∀ p < l.nl, Good l s'.mem B M l.oS p ∧
          (Q → val52 l s'.mem B (l.D * p + l.oS) % M p = x p ^ nib l s.mem B p * 2 ^ (52 * l.S) % M p)) ∧
        (∀ p < l.nl, word s'.mem B (l.D * p + l.oV) = word s.mem B (l.D * p + l.oV)) ∧
        Out2 l B l.oS l.NB s.mem s'.mem ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rcases hl.nl12 with hn | hn
  · rw [show (List.range l.nl).flatMap (select l) = select l 0 by
      rw [hn, show List.range 1 = [0] from rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil]]
    exact sel1_ok hl hn hB hs h hv
  · rw [show (List.range l.nl).flatMap (select l) = select l 0 ++ select l 1 by
      rw [hn, show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]]
    exact sel2_ok hl hn hB hs h hv

theorem amm_winSetup (b : Nat) : amm l l.oY l.oY b = .seq (.block (winSetup l b)) (ammMul l) := rfl

/-- The comparison of `r15` with 1. -/
theorem r15Cmp_ok {s : State} {n : Nat} (hn : n ≤ 6) (h15 : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .r15 (.imm 1)]) s fun s' =>
      isa.eval .e s' = some (n == 1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  let t := arithFlags s (s.gpr .r15 - (1 : BitVec 32).signExtend 64)
    (decide ((s.gpr .r15).toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s.gpr .r15) ((1 : BitVec 32).signExtend 64) (s.gpr .r15 - (1 : BitVec 32).signExtend 64))
  refine WP.of_runBlock ⟨t, by rw [runBlock_cons]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t.zf = _
    simp only [t, VG.X86_64.RegUpd.zf_arithFlags, h15]
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> first | omega_arith | decide
  all_goals rfl

/-- The loop of a window with `n` multiplications left, from `s₀`. -/
structure MulInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k x : Nat → Nat)
    (Q : Prop) (E v : Nat → Nat) (n : Nat) (t : State) : Prop where
  r15 : t.gpr .r15 = BitVec.ofNat 64 n
  st : ExpSt l t.mem B M k x Q (fun p => E p * 2 ^ (l.w + 1 - n))
  gs : ∀ p < l.nl, Good l t.mem B M l.oS p ∧
    (Q → val52 l t.mem B (l.D * p + l.oS) % M p = x p ^ v p * 2 ^ (52 * l.S) % M p)
  frame : Out2 l B l.oY l.NB s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r15 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- The loop body of a window. -/
def mulBody (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prog isa :=
  .seq (.block [.alu .cmp .r15 (.imm 1)])
    (.seq (.ite .e (.block (winSetup l l.oS)) (.block (winSetup l l.oY)))
      (.seq (ammMul l) (.block [.alu .sub .r15 (.imm 1)])))

/-- The `w + 1` multiplications: `w` squarings, then `Y S`. `Y ≡ x^E R` and
`S ≡ x^v R` give `Y ≡ x^(T E + v) R`. -/
theorem mulLoop_ok (hl : AmmOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E v : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : MulInv l s B M k x Q E v (l.w + 1) s) :
    WP isa (.loop (mulBody l) .ne) s fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * l.T + v p) ∧ Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hw := hl.w_bounds
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ l.w + 1 ∧ MulInv l s B M k x Q E v n t) ?_ (l.w + 1) s
    ⟨by omega_using [], Nat.le_refl _, h⟩
  intro n t ⟨h1, h5, hI⟩
  obtain hB' : t.gpr .rbx = B := by
    rw [hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hB
  refine WP.seq (WP.mono (r15Cmp_ok (by omega_using [h5, hw.2]) hI.r15) fun t₀ ⟨e₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_)
  obtain hB₀ : t₀.gpr .rbx = B := by rw [g₀]; exact hB'
  obtain hs₀ : Scr t₀ B (l.nl * l.D) := hs.congr (by rw [wr₀, hI.wr])
  obtain st₀ : ExpSt l t₀.mem B M k x Q (fun p => E p * 2 ^ (l.w + 1 - n)) := by rw [m₀]; exact hI.st
  -- after the multiplication and the count
  obtain after : ∀ (t₁ : State) (E' : Nat → Nat), ExpSt l t₁.mem B M k x Q E' →
      Out2 l B l.oY l.NB t₀.mem t₁.mem →
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .r12 → t₁.gpr r = t₀.gpr r) → t₁.rd = t₀.rd → t₁.wr = t₀.wr → t₁.mxcsr = t₀.mxcsr →
      (n = 1 → E' = fun p => E p * l.T + v p) → (1 < n → E' = fun p => E p * 2 ^ (l.w + 1 - (n - 1))) →
      WP isa (.block [.alu .sub .r15 (.imm 1)]) t₁ fun t₂ =>
        (isa.eval .ne t₂ = some false ∧ (ExpSt l t₂.mem B M k x Q (fun p => E p * l.T + v p) ∧
          Out2 l B l.oY l.NB s.mem t₂.mem ∧
          (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
            r ≠ .r12 → r ≠ .r15 → t₂.gpr r = s.gpr r) ∧
          t₂.rd = s.rd ∧ t₂.wr = s.wr ∧ t₂.mxcsr = s.mxcsr)) ∨
        (isa.eval .ne t₂ = some true ∧ ∃ m < n, 1 ≤ m ∧ m ≤ l.w + 1 ∧ MulInv l s B M k x Q E v m t₂) := by
    intro t₁ E' st₁ f₁ g₁ rd₁ wr₁ x₁ hlast hmore
    obtain r15₁ : t₁.gpr .r15 = BitVec.ofNat 64 n := by
      rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), g₀]; exact hI.r15
    refine WP.mono (r15Dec_ok h1 (by omega_using [h5, hw.2]) r15₁) fun t₂ ⟨r15₂, z₂, k₂, me₂, x₂⟩ => ?_
    obtain f₀₁ : Out2 l B l.oY l.NB t.mem t₁.mem := by rw [← m₀]; exact f₁
    obtain f₂ : Out2 l B l.oY l.NB s.mem t₂.mem := by rw [me₂]; exact hI.frame.trans f₀₁
    obtain g₂ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .r12 → r ≠ .r15 → t₂.gpr r = s.gpr r := fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => by
      rw [k₂.gpr (by simp [r10]), g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₀]
      exact hI.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    obtain rd₂ : t₂.rd = s.rd := by rw [k₂.2.1, rd₁, rd₀, hI.rd]
    obtain wr₂ : t₂.wr = s.wr := by rw [k₂.2.2, wr₁, wr₀, hI.wr]
    obtain xx₂ : t₂.mxcsr = s.mxcsr := by rw [x₂, x₁, x₀, hI.mxcsr]
    simp only [eval, z₂, Option.map_some]
    rcases Nat.eq_or_lt_of_le h1 with rfl | hn
    · refine .inl ⟨by simp, ?_, f₂, g₂, rd₂, wr₂, xx₂⟩
      rw [me₂, ← hlast rfl]; exact st₁
    · refine .inr ⟨by simp only [decide_eq_false (show ¬ (n - 1 = 0) by omega_using [hn]),
        Bool.not_false], n - 1, by omega_using [hn], by omega_using [hn], by omega_using [h5],
        r15₂, ?_, ?_, f₂, g₂, rd₂, wr₂, xx₂⟩
      · rw [me₂, ← hmore hn]; exact st₁
      · intro p hp
        obtain hf : Out2 l B l.oY l.NB t.mem t₂.mem := by rw [me₂]; exact f₀₁
        obtain ⟨g, w⟩ := hI.gs p hp
        exact ⟨g.of_out2 hl hp hf (.inr (by omega_using [o2, o4])) (by omega_using [o4, o10]) (by omega_using [o2, o10]),
          fun hq => by rw [hf.val hl hp (.inr (by omega_using [o2, o4])) (by omega_using [o4, o10]) (by omega_using [o2, o10])]; exact w hq⟩
  refine WP.seq ?_
  by_cases h1' : n = 1
  · subst n
    refine WP.ite true e₀ (fun _ => ?_) (fun h => Bool.noConfusion h)
    obtain hm := mulS_ok hl (v := v) hB₀ hs₀ hR st₀
      (fun p hp => by rw [m₀]; exact (hI.gs p hp).1) (fun hq p hp => by rw [m₀]; exact (hI.gs p hp).2 hq)
    rw [amm_winSetup, WP.seq_iff] at hm
    refine WP.mono hm fun u hu => WP.seq (WP.mono hu fun t₁ ⟨st₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
    refine after t₁ _ st₁ f₁ g₁ rd₁ wr₁ x₁ (fun _ => ?_) (fun h => absurd h (by decide))
    funext p; simp only [Nat.add_sub_cancel, Lay.T]
  · refine WP.ite false (by rw [e₀]; simp [h1']) (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain hm := sq_ok hl hB₀ hs₀ hR st₀
    rw [amm_winSetup, WP.seq_iff] at hm
    refine WP.mono hm fun u hu => WP.seq (WP.mono hu fun t₁ ⟨st₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
    refine after t₁ _ st₁ f₁ g₁ rd₁ wr₁ x₁ (fun h => absurd h h1') (fun _ => ?_)
    funext p
    rw [show l.w + 1 - (n - 1) = (l.w + 1 - n) + 1 by omega_using [h1, h5, h1'], Nat.pow_succ]; grind

/-- The last window's setup: `S := Fin`, one multiplication. -/
def finCode (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  copyN l l.oS l.oFin ++ [.mov32 .r15 (.imm 1)]

/-- A window's usual setup: the digits into `V`, `S := T_v`, `w + 1` multiplications. -/
def normCode (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List (Prog isa) :=
  ([.block (digLoad l)] : List (Prog isa)) ++ (List.range l.nl).flatMap (select l) ++
    ([.block [.mov32 .r15 (.imm (BitVec.ofNat 32 (l.w + 1)))]] : List (Prog isa))

theorem window_eq : VG.Impl.Bignum.X86_64.seqs (window l) =
    .seq (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 l.ND))])
      (.ite .e (.block (finCode l)) (VG.Impl.Bignum.X86_64.seqs (normCode l)))) (.loop (mulBody l) .ne) := by
  simp only [window, normCode, finCode, List.append_assoc]; rfl

theorem ND_lt (hl : AmmOk l) : l.ND < 2 ^ 31 := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The comparison of `r13` (digit `i`) with `ND`. -/
theorem r13Cmp_ok (hl : AmmOk l) {s : State} {i : Nat} (hi : i ≤ l.ND) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 l.ND))]) s fun s' =>
      isa.eval .e s' = some (decide (i = l.ND)) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain hE := ND_lt hl
  let t := arithFlags s (s.gpr .r13 - (BitVec.ofNat 32 l.ND).signExtend 64)
    (decide ((s.gpr .r13).toNat < ((BitVec.ofNat 32 l.ND).signExtend 64).toNat))
    (subOverflow (s.gpr .r13) ((BitVec.ofNat 32 l.ND).signExtend 64) (s.gpr .r13 - (BitVec.ofNat 32 l.ND).signExtend 64))
  refine WP.of_runBlock ⟨t, by rw [runBlock_cons]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t.zf = _
    simp only [t, VG.X86_64.RegUpd.zf_arithFlags, h13, se_ofNat hE]
    rw [ofNat_sub_beq (by omega_using [hi, hE]) (by omega_using [hE])]
  all_goals rfl

/-- A byte outside the bytes that changed. -/
theorem Outside.byteAt {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {d : Nat}
    (hd : d + 1 ≤ o ∨ o + n ≤ d) (hd' : d < 2 ^ 64) : m' (off B d) = m (off B d) :=
  h _ (by rw [ofs_off0 B hd']; omega_using [hd])

/-- With windows of more than 4 bits: both primes' digits `i`, bytes at `oD`,
into their quadwords `V`. -/
theorem digByte_ok (hl : AmmOk l) (hw : l.w ≠ 4) {s : State} {B : Addr} {i : Nat} (hi : i < l.ND)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (l.nl * l.D)) :
    WP isa (.block (digLoad l)) s fun s' =>
      s'.mem = (s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i))).writeW
        (off B (l.D * 1 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 1 i)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .r8] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨d1, d2⟩ := lay_oD l hw
  obtain hnl : l.nl = 2 := by rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact absurd rfl hw
  obtain hn := (show Scr s B (2 * l.D) from hnl ▸ hs).nowrap
  obtain hdg : ∀ (m : Mem) p, dig l m B p i = (m (off B (l.D * p + l.oD + i))).toNat := fun m p => by
    simp only [dig, nibOf, dAt, hw, ite_false, Nat.add_assoc]
  rw [show digLoad l = ([.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * 0 + l.oD : Nat) : Int) },
      .store (at_ .rbx (l.D * 0 + l.oV)) .rax] : List Instr) ++
      [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * 1 + l.oD : Nat) : Int) },
      .store (at_ .rbx (l.D * 1 + l.oV)) .rax] by
        simp only [digLoad, hw, ite_false, hnl, show List.range 2 = [0, 1] from rfl, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append], WP.block_append_iff]
  refine WP.mono (ldD_ok hl hw (p := 0) (by omega_arith) hi hB h13 hs) fun s₁ ⟨m₁, k₁, x₁⟩ => ?_
  obtain hB₁ : s₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB
  obtain h13₁ : s₁.gpr .r13 = BitVec.ofNat 64 i := by rw [k₁.gpr (by decide)]; exact h13
  refine WP.mono (ldD_ok hl hw (p := 1) (by omega_arith) hi hB₁ h13₁ (hs.congr k₁.2.2)) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_
  obtain o₁ : Outside B (l.D * 0 + l.oV) 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ B _ (by omega_using [o8, o10, hn])
  obtain dg₁ : s₁.mem (off B (l.D * 1 + l.oD + i)) = s.mem (off B (l.D * 1 + l.oD + i)) :=
    Outside.byteAt o₁ (by simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]; omega_using [o8, o10, d1, d2, o6, o7, hi])
      (by omega_using [hn, o10, d2, o7, hi])
  refine ⟨?_, (k₁.trans k₂).mono fun r hr => by simp at hr ⊢; rcases hr with rfl | rfl <;> simp, x₂.trans x₁⟩
  rw [m₂, dg₁, m₁, hdg, hdg]

/-- Each lane's digit `i` into its quadword `V`. -/
theorem digLoad_ok (hl : AmmOk l) {s : State} {B : Addr} {i : Nat} (hi : i < l.ND)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (l.nl * l.D)) :
    WP isa (.block (digLoad l)) s fun s' => DigOut l B i s.mem s'.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .r8] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  by_cases hw : l.w = 4
  · rcases hl.nl12 with hn | hn
    · exact WP.mono (digNib1_ok hl hn hw hi hB h13 hs) fun s' ⟨m, k, x⟩ =>
        ⟨DigOut.of_one hn m (by omega_using [o8, o10, hD]), k, x⟩
    · exact WP.mono (digNib2_ok hl hn hw hi hB h13 hs) fun s' ⟨m, k, x⟩ =>
        ⟨DigOut.of_two hn m (by omega_using [o8, o10, hD]) (by omega_using [o8, o10]), k, x⟩
  · have hn : l.nl = 2 := by rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact absurd rfl hw
    exact WP.mono (digByte_ok hl hw hi hB h13 hs) fun s' ⟨m, k, x⟩ =>
      ⟨DigOut.of_two hn m (by omega_using [o8, o10, hD]) (by omega_using [o8, o10]), k, x⟩

/-- A window's usual setup and multiplications (digit `i < ND`): `Y ≡ x^E R`
becomes `x^(T E + v) R` for each prime's digit `v`, which `V` then holds. -/
theorem winNorm_ok (hl : AmmOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat} {i : Nat}
    (hi : i < l.ND) (h13 : s.gpr .r13 = BitVec.ofNat 64 i)
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) (hd : ∀ p < l.nl, dig l s.mem B p i < l.T) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (normCode l)) s fun t => WP isa (.loop (mulBody l) .ne) t fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * l.T + dig l s.mem B p i) ∧
      (∀ p < l.nl, word s'.mem B (l.D * p + l.oV) = BitVec.ofNat 64 (dig l s.mem B p i)) ∧
      OutW l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  have hw := hl.w_bounds
  -- the digits into `V`
  rw [normCode, List.append_assoc]
  refine wp_seqs_app (by simp) (by simp [select]) ?_
  dsimp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.mono (digLoad_ok hl hi hB h13 hs) fun s₂ ⟨⟨wv, f₂⟩, k₂, x₂⟩ => ?_
  obtain nv : ∀ p < l.nl, nib l s₂.mem B p = dig l s.mem B p i := fun p hp => by
    unfold nib; rw [wv p hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hd p hp; have := hl.T_bounds; omega_arith)]
  obtain hB₂ : s₂.gpr .rbx = B := by rw [k₂.gpr (by decide)]; exact hB
  obtain hs₂ : Scr s₂ B (l.nl * l.D) := hs.congr k₂.2.2
  obtain st₂ : ExpSt l s₂.mem B M k x Q E :=
    ⟨h.ar.of_out2 hl f₂ (by omega_using [o2, o8]) (by omega_using [o8, o9]),
      h.tab_of hl f₂ (.inr (by omega_using [o5, o6, o7, o8])) (by omega_using [o8, o10]),
      fun p hp => (h.y p hp).of_out2 hl hp f₂ (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10])
        (by omega_using [o8, o10]),
      fun hq p hp => by
        rw [f₂.val hl hp (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10]) (by omega_using [o8, o10])]
        exact h.yv hq p hp⟩
  -- the entries
  refine wp_seqs_app (by simp [select]; exact ⟨0, by have := hl.nl_le; omega_arith⟩) (by simp)
    (WP.mono (selAll_ok hl hB₂ hs₂ st₂ fun p hp => by rw [nv p hp]; exact hd p hp)
      fun s₃ ⟨st₃, gs₃, w₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_)
  obtain hB₃ : s₃.gpr .rbx = B := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hB₂
  obtain hs₃ : Scr s₃ B (l.nl * l.D) := hs₂.congr wr₃
  dsimp only [VG.Impl.Bignum.X86_64.seqs]
  rw [WP.block_cons_iff]
  refine ⟨s₃.setReg32 .r15 (BitVec.ofNat 32 (l.w + 1)), rfl, WP.block_nil ?_⟩
  let s₄ := s₃.setReg32 .r15 (BitVec.ofNat 32 (l.w + 1))
  obtain hB₄ : s₄.gpr .rbx = B := by
    change (s₃.setReg32 .r15 _).gpr .rbx = _
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₃
  obtain hI : MulInv l s₄ B M k x Q E (fun p => dig l s.mem B p i) (l.w + 1) s₄ := by
    refine ⟨?_, ?_, fun p hp => ?_, Out2.refl _ _ _ _, fun _ _ _ _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
    · change (s₃.setReg32 .r15 _).gpr .r15 = _
      rw [State.setReg32, RegUpd.gpr_setReg_self]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := l.w + 1) (b := 2 ^ 32) (by omega_using [hw.2]),
        Nat.mod_eq_of_lt (a := l.w + 1) (b := 2 ^ 64) (by omega_using [hw.2])]
    · rw [Nat.sub_self, Nat.pow_zero]; simp only [Nat.mul_one]; exact st₃
    · rw [← nv p hp]; exact gs₃ p hp
  refine WP.mono (mulLoop_ok hl hB₄ (hs₃.congr rfl) hR hI)
    fun s₆ ⟨st₆, f₆, g₆, rd₆, wr₆, x₆⟩ => ⟨st₆, fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_,
      by rw [rd₆]; change s₃.rd = _; rw [rd₃, k₂.2.1],
      by rw [wr₆]; change s₃.wr = _; rw [wr₃, k₂.2.2],
      by rw [x₆]; change s₃.mxcsr = _; rw [x₃, x₂]⟩
  · rw [f₆.word_at hl hp (.inr (by omega_using [o2, o8])) (by omega_using [o8, o10]) (by omega_using [o2, o10])]
    change word s₃.mem B _ = _
    rw [w₃ p hp, wv p hp]
  · exact ((OutW.ofV f₂).trans (OutW.ofS f₃)).trans (OutW.ofY f₆)
  · rw [g₆ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10]
    change (s₃.setReg32 .r15 _).gpr r = _
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ r10, g₃ r r1 r2 r3 r5, k₂.gpr (by simp [r1, r2, r3, r4, r5])]

/-- A window (digit `i < ND`): `Y ≡ x^E R` becomes `x^(T E + v) R` for each
prime's digit `v`, which `V` then holds. -/
theorem window_ok (hl : AmmOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat} {i : Nat}
    (hi : i < l.ND) (h13 : s.gpr .r13 = BitVec.ofNat 64 i)
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) (hd : ∀ p < l.nl, dig l s.mem B p i < l.T) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (window l)) s fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * l.T + dig l s.mem B p i) ∧
      (∀ p < l.nl, word s'.mem B (l.D * p + l.oV) = BitVec.ofNat 64 (dig l s.mem B p i)) ∧
      OutW l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rw [window_eq]
  refine WP.seq (WP.seq (WP.mono (r13Cmp_ok hl (Nat.le_of_lt hi) h13) fun s₀ ⟨e₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_))
  refine WP.ite false (by rw [e₀]; simp only [decide_eq_false (Nat.ne_of_lt hi)]) (fun h => Bool.noConfusion h)
    (fun _ => ?_)
  have := winNorm_ok hl (s := s₀) hi (by rw [g₀]; exact h13) (by rw [g₀]; exact hB) (hs.congr wr₀) hR (m₀ ▸ h)
    (by rw [m₀]; exact hd)
  rw [m₀, g₀, rd₀, wr₀, x₀] at this
  exact this

/-- `S` holds `Fin` and `r15` 1, from `s₀`. -/
structure FinSet (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (t : State) : Prop where
  s : ∀ p < l.nl, ∀ q < l.L, limb l t.mem B (l.D * p + l.oS) q = limb l s₀.mem B (l.D * p + l.oFin) q
  frame : Out2 l B l.oS l.NB s₀.mem t.mem
  r15 : t.gpr .r15 = BitVec.ofNat 64 1
  gpr : ∀ r, r ≠ .r15 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

theorem finCode_ok (hl : AmmOk l) {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) :
    WP isa (.block (finCode l)) s (FinSet l s B) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  rw [finCode, WP.block_append_iff]
  refine WP.mono (copyN_ok hl hB hs (by omega_using [o4, o10]) (by omega_using [o9, o10])
    (.inr (by omega_using [o4, o9]))) fun s₁ ⟨l₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁.setReg32 .r15 1, rfl, WP.block_nil ⟨l₁, f₁, ?_, fun r r1 => ?_, rd₁, wr₁, x₁⟩⟩
  · rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl
  · rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ r1, g₁]

/-- The last window (`r13 = ND`): `Y := Y Fin / R`. -/
theorem finWin_ok (hl : AmmOk l) {s : State} {B : Addr} {M k : Nat → Nat}
    (h13 : s.gpr .r13 = BitVec.ofNat 64 l.ND) (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D))
    (ar : Ar l s.mem B M k) (gy : ∀ p < l.nl, Good l s.mem B M l.oY p) (gf : ∀ p < l.nl, Good l s.mem B M l.oFin p) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (window l)) s fun s' =>
      (∀ p < l.nl, Good l s'.mem B M l.oY p ∧
        val52 l s'.mem B (l.D * p + l.oY) * 2 ^ (52 * l.S) % M p =
          val52 l s.mem B (l.D * p + l.oY) * val52 l s.mem B (l.D * p + l.oFin) % M p) ∧
      OutW l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  rw [window_eq]
  refine WP.seq (WP.seq (WP.mono (r13Cmp_ok hl (Nat.le_refl _) h13) fun s₀ ⟨e₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_))
  refine WP.ite true (by rw [e₀]; simp only [decide_true]) (fun _ => ?_) (fun h => Bool.noConfusion h)
  obtain hB₀ : s₀.gpr .rbx = B := by rw [g₀]; exact hB
  refine WP.mono (finCode_ok hl hB₀ (hs.congr wr₀)) fun u hu => ?_
  obtain hBu : u.gpr .rbx = B := by rw [hu.gpr _ (by decide)]; exact hB₀
  obtain hsu : Scr u B (l.nl * l.D) := hs.congr (by rw [hu.wr, wr₀])
  obtain fu : Out2 l B l.oS l.NB s.mem u.mem := by rw [← m₀]; exact hu.frame
  obtain gsu : ∀ p < l.nl, Good l u.mem B M l.oS p := fun p hp =>
    (gf p hp).of_limbs fun q hq => by rw [hu.s p hp q hq, m₀]
  obtain vsu : ∀ p < l.nl, val52 l u.mem B (l.D * p + l.oS) = val52 l s.mem B (l.D * p + l.oFin) := fun p hp =>
    val52_of_limbs fun q hq => by rw [hu.s p hp q hq, m₀]
  obtain gyu : ∀ p < l.nl, Good l u.mem B M l.oY p := fun p hp =>
    (gy p hp).of_out2 hl hp fu (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  obtain vyu : ∀ p < l.nl, val52 l u.mem B (l.D * p + l.oY) = val52 l s.mem B (l.D * p + l.oY) := fun p hp =>
    fu.val hl hp (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  obtain aru : Ar l u.mem B M k := ar.of_out2 hl fu (by omega_using [o2, o4]) (by omega_using [o4, o9])
  refine WP.loop (M := isa) (fun n t => n = 1 ∧ t = u) ?_ 1 u ⟨rfl, rfl⟩
  intro n t ⟨hn, ht⟩
  subst hn ht
  refine WP.seq (WP.mono (r15Cmp_ok (by decide) hu.r15) fun t₀ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  refine WP.seq (WP.ite true (by rw [e₁]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h))
  obtain hm := amm2_ok hl (o := l.oY) (a := l.oY) (b := l.oS) (by rw [g₁]; exact hBu) (hsu.congr wr₁) (m₁ ▸ aru)
    (by omega_using []) (by omega_using [o2, o9]) (by omega_using [o2, o10]) (by omega_using [o4, o10])
    (fun p hp => m₁ ▸ gyu p hp) (fun p hp => m₁ ▸ gsu p hp)
  rw [amm_winSetup, WP.seq_iff] at hm
  refine WP.mono hm fun w hw => WP.seq (WP.mono hw fun t₁ ⟨v₁, f₁, ar₁, g₂, rd₂, wr₂, x₂⟩ => ?_)
  obtain r15₁ : t₁.gpr .r15 = BitVec.ofNat 64 1 := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g₁]; exact hu.r15
  refine WP.mono (r15Dec_ok (by decide) (by decide) r15₁) fun t₂ ⟨r15₂, z₂, k₂, me₂, x₃⟩ => ?_
  simp only [eval, z₂, Option.map_some]
  refine .inl ⟨by simp, fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_, ?_, ?_, ?_⟩
  · rw [me₂, ← vyu p hp, ← vsu p hp, ← m₁]; exact v₁ p hp
  · rw [me₂, ← m₀]
    exact (OutW.ofS hu.frame).trans (OutW.ofY (m₁ ▸ f₁))
  · rw [k₂.gpr (by simp [r10]), g₂ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₁, hu.gpr r r10, g₀]
  · rw [k₂.2.1, rd₂, rd₁, hu.rd, rd₀]
  · rw [k₂.2.2, wr₂, wr₁, hu.wr, wr₀]
  · rw [x₃, x₂, x₁, hu.mxcsr, x₀]

end VG.Proof.Bignum.X86_64.Ifma
