module
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# ChaCha20 and Poly1305 together (x86-64): the counted loops of the tails

`Stitch.cntLoop r a` runs `r` and then `a` as many times as `rdi` says,
counting `rdi` down to 0 (`cntLoop_ok`): for an invariant that `r` and `a`
advance by one and keep `rdi`, and that `sub rdi, 1` keeps (`subRdi_ok`: it
writes only `rdi` and the flags).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch

set_option simprocs false in
theorem subRdi_ok (s : State) :
    WP isa (.block [.alu .sub .rdi (.imm 1)]) s fun s' =>
      s'.gpr .rdi = s.gpr .rdi - 1 ∧ (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧
      s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = some (s.gpr .rdi - 1 == 0) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    State.setReg, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨rfl, fun r hr => by simp [hr], trivial, trivial, trivial, trivial, trivial, rfl⟩

/-- What an instruction that writes only the register `d` (and maybe the
flags) keeps. -/
abbrev Only (d : Reg) (s s' : State) : Prop :=
  (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mem = s.mem ∧
    s'.rd = s.rd ∧ s'.wr = s.wr

set_option simprocs false in
theorem addImm_ok (d : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block [.alu .add d (.imm v)]) s fun s' => s'.gpr d = s.gpr d + v.signExtend 64 ∧ Only d s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    State.setReg, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl, rfl⟩

set_option simprocs false in
theorem subImm_ok (d : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block [.alu .sub d (.imm v)]) s fun s' => s'.gpr d = s.gpr d - v.signExtend 64 ∧ Only d s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    State.setReg, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl, rfl⟩

set_option simprocs false in
theorem mov32Imm_ok (d : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block [.mov32 d (.imm v)]) s fun s' => s'.gpr d = v.setWidth 64 ∧ Only d s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    State.setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl, rfl⟩

set_option simprocs false in
theorem movReg_ok (d r₀ : Reg) (s : State) :
    WP isa (.block [.mov d (.reg r₀)]) s fun s' => s'.gpr d = s.gpr r₀ ∧ Only d s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl, rfl⟩

/-- `cntLoop r a` from `rdi = c` (`0 < c`): `c` runs of `r` and `a`, each
advancing `Inv` by one and keeping `rdi`, with `rdi` 0 after. `Inv` must hold
through writes of `rdi` and the flags alone. -/
theorem cntLoop_ok {r : Prog isa} {a : List Instr} (Inv : Nat → State → Prop) {c : Nat} (hc : 0 < c)
    (hc64 : c < 2 ^ 64)
    (hstep : ∀ i, i < c → ∀ s, Inv i s → WP isa (.seq r (.block a)) s fun s' =>
      Inv (i + 1) s' ∧ s'.gpr .rdi = s.gpr .rdi)
    (hkeep : ∀ i s s', Inv i s → (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) → s'.xmm = s.xmm →
      s'.ymmHi = s.ymmHi → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Inv i s')
    {s : State} (h0 : Inv 0 s) (hr : s.gpr .rdi = BitVec.ofNat 64 c) :
    WP isa (cntLoop r a) s fun s' => Inv c s' ∧ s'.gpr .rdi = 0 := by
  let J : Nat → State → Prop := fun n s =>
    ∃ i, n = c - i ∧ i < c ∧ Inv i s ∧ s.gpr .rdi = BitVec.ofNat 64 (c - i)
  refine WP.loop (M := isa) J (fun n s ⟨i, hn, hi, hI, hd⟩ => ?_) c s ⟨0, by omega_arith, hc, h0, by simpa using hr⟩
  refine WP.seq (WP.mono (hstep i hi s hI) fun s₁ ⟨h₁, d₁⟩ => ?_)
  refine WP.mono (subRdi_ok s₁) fun s₂ ⟨d₂, g₂, x₂, y₂, m₂, rd₂, wr₂, z₂⟩ => ?_
  have I₂ := hkeep _ _ _ h₁ g₂ x₂ y₂ m₂ rd₂ wr₂
  have e : s₁.gpr .rdi - 1 = BitVec.ofNat 64 (c - (i + 1)) := by
    rw [d₁, hd, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith),
      Nat.sub_add_eq]
  have ez : (BitVec.ofNat 64 (c - (i + 1)) == 0) = decide (c - (i + 1) = 0) := by
    have hlt : c - (i + 1) < 2 ^ 64 := by omega_arith
    by_cases h : c - (i + 1) = 0
    · simp [h]
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
      exact h this
  rw [e, ez] at z₂
  rw [e] at d₂
  by_cases hlast : i + 1 = c
  · refine .inl ⟨by simp [eval, z₂, hlast], hlast ▸ I₂, by rw [d₂, hlast, Nat.sub_self]; rfl⟩
  · exact .inr ⟨by simp [eval, z₂]; omega_arith, c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, I₂, d₂⟩

/-- `roundsL r4 r0 k`, for an invariant `I n j` after `n` rounds of which
the first absorbed `j` blocks at `q`, that writes of `rsi`, `rdi` and the
flags keep: from `rsi = q`, `k / 4` rounds `r4`, each from `rsi` at the
next four blocks, then `10 - k / 4` rounds `r0`, all keeping `rsi` and
`rdi`; then `rsi` is back at `q` and `rdi` at `rcx - 64`. -/
theorem roundsL_ok {r4 r0 : Prog isa} {k : Nat} (I : Nat → Nat → State → Prop) {q : Addr}
    (h1 : 1 ≤ k / 4) (h10 : k / 4 < 10) (hk4 : 4 * (k / 4) = k)
    (sk : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * k)) = BitVec.ofNat 64 (16 * k))
    (hkeep : ∀ n j s s', I n j s → (∀ r, r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r) → s'.xmm = s.xmm →
      s'.ymmHi = s.ymmHi → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → I n j s')
    (h4 : ∀ n s, n < k / 4 → I n (4 * n) s → s.gpr .rsi = q + BitVec.ofNat 64 (16 * (4 * n)) →
      WP isa r4 s fun s' => I (n + 1) (4 * (n + 1)) s' ∧ s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi)
    (h0 : ∀ n s, k / 4 ≤ n → n < 10 → I n k s → s.gpr .rsi = q →
      WP isa r0 s fun s' => I (n + 1) k s' ∧ s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi)
    {s : State} (hI : I 0 0 s) (hq : s.gpr .rsi = q) :
    WP isa (roundsL r4 r0 k) s fun s' => I 10 k s' ∧ s'.gpr .rsi = q ∧ s'.gpr .rdi = s'.gpr .rcx - 64 := by
  have only2 : ∀ {d : Reg} {n j : Nat} {s s' : State}, d = .rsi ∨ d = .rdi → I n j s → Only d s s' →
      I n j s' := fun hd hI ⟨g, x, y, m, rd, wr⟩ =>
    hkeep _ _ _ _ hI (fun r h₁ h₂ => g r (by rcases hd with rfl | rfl; exacts [h₁, h₂])) x y m rd wr
  unfold roundsL
  refine WP.seq (WP.mono (mov32Imm_ok .rdi _ s) fun s₁ ⟨d₁, o₁⟩ => ?_)
  have rsi₁ : s₁.gpr .rsi = q := by rw [o₁.1 _ (by decide), hq]
  -- The rounds absorbing four blocks each.
  let A : Nat → State → Prop := fun n s => I n (4 * n) s ∧ s.gpr .rsi = q + BitVec.ofNat 64 (16 * (4 * n))
  refine WP.seq (WP.mono (cntLoop_ok A h1 (by omega_arith) (fun n hn s ⟨hA, hr⟩ => ?_)
    (fun n s s' ⟨hA, hr⟩ g x y m rd wr => ⟨hkeep _ _ _ _ hA (fun r h₁ _ => g r ‹_›) x y m rd wr,
      by rw [g _ (by decide), hr]⟩)
    ⟨only2 (.inr rfl) hI o₁, by rw [rsi₁]; simp⟩
    (by rw [d₁]; apply BitVec.eq_of_toNat_eq; simp; omega_arith)) fun s₂ ⟨⟨hA₂, hr₂⟩, d₂⟩ => ?_)
  · refine WP.seq (WP.mono (h4 n s hn hA hr) fun t ⟨ht, rt, dt⟩ => ?_)
    refine WP.mono (addImm_ok .rsi 64 t) fun t' ⟨r', o'⟩ => ⟨⟨only2 (.inl rfl) ht o', ?_⟩, ?_⟩
    · rw [r', rt, hr, show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide,
        Offset.add_add, show 16 * (4 * n) + 64 = 16 * (4 * (n + 1)) by omega_arith]
    · rw [o'.1 _ (by decide), dt]
  -- Back at `q`, and the other rounds.
  refine WP.seq (WP.block_append (WP.mono (subImm_ok .rsi _ s₂) fun s₃ ⟨r₃, o₃⟩ =>
    WP.mono (mov32Imm_ok .rdi _ s₃) fun s₄ ⟨d₄, o₄⟩ => ?_))
  have rsi₄ : s₄.gpr .rsi = q := by
    rw [o₄.1 _ (by decide), r₃, hr₂, sk, hk4, BitVec.add_sub_cancel]
  have I₄ : I (k / 4) k s₄ := only2 (.inr rfl) (only2 (.inl rfl) (by have := hA₂; rwa [hk4] at this) o₃) o₄
  let B : Nat → State → Prop := fun n s => I (k / 4 + n) k s ∧ s.gpr .rsi = q
  refine WP.seq (WP.mono (cntLoop_ok B (c := 10 - k / 4) (by omega_arith) (by omega_arith) (fun n hn s ⟨hB, hr⟩ => ?_)
    (fun n s s' ⟨hB, hr⟩ g x y m rd wr => ⟨hkeep _ _ _ _ hB (fun r h₁ _ => g r ‹_›) x y m rd wr,
      by rw [g _ (by decide), hr]⟩)
    ⟨I₄, rsi₄⟩ (by rw [d₄]; apply BitVec.eq_of_toNat_eq; simp; omega_arith)) fun s₅ ⟨⟨hB₅, hr₅⟩, _⟩ => ?_)
  · exact WP.seq (WP.mono (h0 (k / 4 + n) s (by omega_arith) (by omega_arith) hB hr) fun t ⟨ht, rt, dt⟩ =>
      WP.block_nil ⟨⟨ht, by rw [rt, hr]⟩, dt⟩)
  rw [show k / 4 + (10 - k / 4) = 10 by omega_arith] at hB₅
  refine WP.block_append (WP.mono (movReg_ok .rdi .rcx s₅) fun s₆ ⟨d₆, o₆⟩ =>
    WP.mono (subImm_ok .rdi 64 s₆) fun s₇ ⟨d₇, o₇⟩ => ⟨only2 (.inr rfl) (only2 (.inr rfl) hB₅ o₆) o₇,
      by rw [o₇.1 _ (by decide), o₆.1 _ (by decide), hr₅], ?_⟩)
  rw [d₇, d₆, o₇.1 _ (by decide), o₆.1 _ (by decide)]
  rfl

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
