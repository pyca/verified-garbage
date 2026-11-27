module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import Mathlib.Tactic.IntervalCases
meta import Mathlib.Tactic.IntervalCases
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.ChaCha20.Spec
public import VerifiedGarbage.Impl.ChaCha20.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.ChaCha20.Spec
meta import VerifiedGarbage.Impl.ChaCha20.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.ChaCha20
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.TCB.Artifact

/-! ### `ChaCha20.PPC64LE.Contract`, which this module and modules that import it used -/

section

/-!
# ChaCha20: the PPC64LE contract of the block function

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contract of the assembly
primitive `vg_chacha20_block` on PPC64LE, in terms of the specification in
`Spec/ChaCha20.lean`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open PPC64LE in
/-- PPC64LE contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read `state` (64 bytes) and read and write `buf` (256 bytes; its first 64
bytes hold the result on exit, and the rest is unspecified). `buf` may not
overlap `state`. The pointers are public; the state (key, counter and nonce)
is secret. -/
def blockPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 64⟩
    let buf : Region := ⟨s.gpr .r4, 256⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state
  post s s' := stateAt s'.mem (s.gpr .r4) = block (stateAt s.mem (s.gpr .r3))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

end

end

/-! ### `ChaCha20.PPC64LE.Rounds`, which only this module used -/

section

/-!
# ChaCha20 block function on PPC64LE: the rounds

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20.PPC64LE VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

theorem qr_ok {a b c d : Reg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (s : State) (va vb vc vd : Word)
    (ha : (s.gpr a).setWidth 32 = va) (hb : (s.gpr b).setWidth 32 = vb)
    (hc : (s.gpr c).setWidth 32 = vc) (hd : (s.gpr d).setWidth 32 = vd) :
    WP isa (.block (qr a b c d)) s fun s' =>
      (s'.gpr a).setWidth 32 = (quarterRound va vb vc vd).1 ∧
      (s'.gpr b).setWidth 32 = (quarterRound va vb vc vd).2.1 ∧
      (s'.gpr c).setWidth 32 = (quarterRound va vb vc vd).2.2.1 ∧
      (s'.gpr d).setWidth 32 = (quarterRound va vb vc vd).2.2.2 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [qr, runBlock_cons, runStep_some,
    runBlock_nil, exec_add, exec_logic,
    exec_rotr_w (show 16 < 32 by decide), exec_rotr_w (show 20 < 32 by decide),
    exec_rotr_w (show 24 < 32 by decide), exec_rotr_w (show 25 < 32 by decide), isa,
    State.write, hab, hac, had, hbc, hbd, hcd, hab.symm,
    hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm, Option.some.injEq,
    exists_eq_left', ↓reduceIte]
  simp only [lo32_add, BitVec.setWidth_xor,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, ha, hb, hc, hd, Nat.reduceLeDiff]
  and_intros
  all_goals first
    | simp only [quarterRound_eq]
    | (intro r h1 h2 h3 h4; simp [h1, h2, h3, h4])

/-! ## Where the words are -/

/-- The state `v` is in the registers. -/
def Holds (v : CState) (s : State) : Prop := ∀ k (hk : k < 16), (s.gpr (wreg k)).setWidth 32 = v[k]

/-- The registers that hold state words. -/
def Words (r : Reg) : Prop := ∃ k < 16, r = wreg k

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : CState) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem quarter_step {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {v : CState} {s₀ s : State} (h : RI v s₀ s) :
    WP isa (quarter x y z w) s (RI (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) := by
  have nd : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using hd
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd
  have ne : ∀ {i j}, i < 16 → j < 16 → i ≠ j → wreg i ≠ wreg j := fun hi hj hij e =>
    hij (wreg_inj hi hj e)
  refine WP.mono (qr_ok (ne hx hy nxy) (ne hx hz nxz) (ne hx hw nxw) (ne hy hz nyz)
    (ne hy hw nyw) (ne hz hw nzw) s _ _ _ _ (h.holds x hx) (h.holds y hy) (h.holds z hz)
    (h.holds w hw)) fun s' ⟨ha, hb, hc, hd, hr, hm, hrd, hwr⟩ =>
    ⟨fun k hk => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hr' => ?_⟩
  · rw [qround_get _ _ _ _ _ k hk]
    simp only
    by_cases ew : w = k
    · subst ew; simp only [ite_true]; exact hd
    by_cases ez : z = k
    · subst ez; simp only [ite_true, ew, ite_false]; exact hc
    by_cases ey : y = k
    · subst ey; simp only [ite_true, ew, ez, ite_false]; exact hb
    by_cases ex : x = k
    · subst ex; simp only [ite_true, ew, ez, ey, ite_false]; exact ha
    simp only [ew, ez, ey, ex, ite_false]
    rw [hr _ (ne hk hx (Ne.symm ex)) (ne hk hy (Ne.symm ey)) (ne hk hz (Ne.symm ez))
      (ne hk hw (Ne.symm ew))]
    exact h.holds k hk
  · have nw : ∀ i < 16, r ≠ wreg i := fun i hi e => hr' ⟨i, hi, e⟩
    rw [hr r (nw x hx) (nw y hy) (nw z hz) (nw w hw)]
    exact h.keep r hr'

theorem doubleRound_ok {v : CState} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (innerBlock v) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  exact WP.mono (quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₇) fun _ h => h

theorem rounds_ok {v : CState} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

end VG.Proof.ChaCha20.PPC64LE

end

end

/-!
# ChaCha20 block function on PPC64LE: the whole function

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20.PPC64LE VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .r3
abbrev buf : Addr := s₀.gpr .r4
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev bufR : Region := ⟨buf s₀, 256⟩
abbrev outR : Region := ⟨buf s₀, 64⟩
/-- Where the nonvolatile registers are saved. -/
abbrev savR : Region := ⟨buf s₀ + BitVec.ofNat 64 64, 64⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (st s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀]
  wr : s₀.wr = [bufR s₀]
  buf_st : (bufR s₀).Disjoint (stR s₀)

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockPPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_out {k : Nat} (hk : k < 16) : InRegions s₀.wr (buf s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_sav {i : Nat} (hi : i < 8) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (buf s₀ + BitVec.ofNat 64 (64 + 8 * i)) 8 :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by omega_using [hi]) (by omega_using [hi])⟩

theorem out_sav {i : Nat} (hi : i < 8) : InRegions s₀.wr (buf s₀ + BitVec.ofNat 64 (64 + 8 * i)) 8 :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by omega_using [hi]) (by omega_using [hi])⟩

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = (V s₀)[k] := by
  rw [hf.readW (r := stR s₀) (contains_off (by omega_using [hk]) (by omega_using [hk])) (by simpa using hp.buf_st.symm)
    (by decide)]
  simp only [V, stateAt, Vector.getElem_ofFn]

end Pre

theorem out_sep (p : Addr) {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 := by
  intro x hx hy
  bv_omega

theorem readW_writeW_out (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (out_sep p hj hk h) (by decide)

theorem sav_sep (p : Addr) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (64 + 8 * i)) 8 (p + BitVec.ofNat 64 (64 + 8 * j)) 8 := by
  intro x hx hy
  bv_omega

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bufR s₀) := by
  intro a h
  simp only [Region.Contains] at h ⊢
  bv_omega

theorem outR_sav (s₀ : State) : (outR s₀).Disjoint (savR s₀) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem wreg_ne_r0 {k : Nat} (hk : k < 16) : wreg k ≠ .r0 := by
  have key : ∀ k < 16, wreg k ≠ .r0 := by decide
  exact key k hk

theorem not_words_r3 : ¬ Words .r3 := by
  rintro ⟨k, hk, h⟩; interval_cases k <;> simp [wreg] at h
theorem not_words_r4 : ¬ Words .r4 := by
  rintro ⟨k, hk, h⟩; interval_cases k <;> simp [wreg] at h

theorem saved_words {i : Nat} (hi : i < 8) : Words (saved i) := by
  have key : ∀ i < 8, saved i = wreg (i + 8) := by decide
  exact ⟨i + 8, by omega_using [hi], key i hi⟩

theorem saved_inj {i j : Nat} (hi : i < 8) (hj : j < 8) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 8, ∀ j < 8, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne {i : Nat} (hi : i < 8) : saved i ≠ .r3 ∧ saved i ≠ .r4 := by
  have key : ∀ i < 8, saved i ≠ .r3 ∧ saved i ≠ .r4 := by decide
  exact key i hi

/-- A preserved register is saved, or not a word register (nor `r0`). -/
theorem preserved_cases {r : Reg} (hr : r ∈ preserved) :
    (∃ i < 8, r = saved i) ∨ (¬ Words r ∧ r ≠ .r0) := by
  have key : ∀ r ∈ preserved, (∃ i < 8, r = saved i) ∨ (∀ k < 16, r ≠ wreg k) ∧ r ≠ .r0 := by
    decide
  rcases key r hr with h | ⟨h, h0⟩
  · exact .inl h
  · exact .inr ⟨fun ⟨k, hk, e⟩ => h k hk e, h0⟩

/-! ## Saving the nonvolatile registers -/

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (buf s₀ + BitVec.ofNat 64 (64 + 8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 8) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .r4 (64 + 8 * n)]) s (SI s₀ (n + 1)) := by
  have hr4 : s.gpr .r4 = buf s₀ := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 (64 + 8 * n)) 8 := by
    rw [h.wr, hr4]; exact hp.out_sav hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (by decide) (show 64 + 8 * n < 2 ^ 15 ∧ (64 + 8 * n) % 4 = 0 by omega_using [hn]) hout,
    Option.some.injEq, exists_eq_left', hr4]
  refine ⟨h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _ ?_, fun i hi => ?_⟩
  · simp only [Region.Contains]; bv_omega
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_arith) hn (by omega_using [hi])) (by decide)]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-! ## Loading the state -/

/-- After loading `n` words. -/
structure LI (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → (s.gpr (wreg j)).setWidth 32 = (V s₀)[j]
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ n s) :
    WP isa (.block [.load .w (wreg n) .r3 (4 * n)]) s (LI s₀ (n + 1)) := by
  have hr3 : s.gpr .r3 = st s₀ := h.keep _ not_words_r3
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [h.rd, h.wr, hr3]; exact hp.in_st hn _
  have hv : s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * n)) 32 = (V s₀)[n] := by
    rw [h.mem]; exact hp.read_st (Frame.refl _ _) hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_w (by decide) (show 4 * n < 2 ^ 15 by omega_using [hn]) hin, isa,
    Option.some.injEq, exists_eq_left', hr3, hv]
  refine ⟨fun j hj hjn => ?_, h.mem, h.rd, h.wr, fun r hr => ?_⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e : wreg j ≠ wreg n := fun e => absurd (wreg_inj hj hn e) (by omega_using [hjn])
      simp only [e, ite_false]; exact h.loaded j hj hjn
    · simp
  · have e : r ≠ wreg n := fun e => hr ⟨n, hn, e⟩
    simp only [State.write, e, ite_false]; exact h.keep r hr

/-! ## Adding the input state -/

/-- After finishing words `0 … i - 1`: they are in the output, and words
`i … 15` of the rounds' result `R` are still in their registers. -/
structure FI (s₀ : State) (R : CState) (i : Nat) (s : State) : Prop where
  done : ∀ j (hj : j < 16), j < i →
    s.mem.readW (buf s₀ + BitVec.ofNat 64 (4 * j)) 32 = R[j] + (V s₀)[j]
  rest : ∀ j (hj : j < 16), i ≤ j → (s.gpr (wreg j)).setWidth 32 = R[j]
  frame : Frame [outR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .r0 → s.gpr r = s₀.gpr r

theorem add_step {s₀ : State} (hp : Pre s₀) {R : CState} {i : Nat} (hi : i < 16)
    {s : State} (h : FI s₀ R i s) :
    WP isa (.block (addWord i)) s (FI s₀ R (i + 1)) := by
  have hr3 : s.gpr .r3 = st s₀ := h.keep _ not_words_r3 (by decide)
  have hr4 : s.gpr .r4 = buf s₀ := h.keep _ not_words_r4 (by decide)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h.rd, h.wr, hr3]; exact hp.in_st hi _
  have hout : InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h.wr, hr4]; exact hp.out_out hi
  have hv := hp.read_st (h.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bufR s₀, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩) hi
  have hr := h.rest i hi le_rfl
  have hne : wreg i ≠ .r0 := wreg_ne_r0 hi
  have n4 : Reg.r4 ≠ wreg i := fun e => not_words_r4 ⟨_, hi, e⟩
  have n40 : Reg.r4 ≠ .r0 := by decide
  apply WP.of_runBlock
  simp only [addWord, runBlock_cons, runStep_some,
    exec_load_w (by decide) (show 4 * i < 2 ^ 15 by omega_using [hi]) hin, exec_add, isa, hr3, hv]
  simp only [State.write, hne, ite_false, ite_true]
  rw [exec_store_w (by decide) (show 4 * i < 2 ^ 15 by omega_using [hi])
    (by simpa [State.write, hne, n4, n40] using hout)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', ite_true, ite_false,
    hr4, n4, n40]
  have ho : (outR s₀).Contains (buf s₀ + BitVec.ofNat 64 (4 * i)) (32 / 8) :=
    contains_off (by omega_using [hi]) (by omega_using [hi])
  refine ⟨fun j hj hji => ?_, fun j hj hij => ?_, h.frame.writeW (List.mem_singleton_self _) _ ho,
    h.rd, h.wr, fun r hr' h0 => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hji | rfl
    · rw [readW_writeW_out _ _ _ hj hi (by omega_using [hji])]; exact h.done j hj hji
    · rw [Mem.readW_writeW_self32, lo32_add, hr, lo32_ext]
  · have e1 : wreg j ≠ wreg i := fun e => absurd (wreg_inj hj hi e) (by omega_using [hij])
    have e2 : wreg j ≠ .r0 := wreg_ne_r0 hj
    simp only [e1, e2, ite_false]; exact h.rest j hj (by omega_using [hij])
  · have e1 : r ≠ wreg i := fun e => hr' ⟨i, hi, e⟩
    simp only [e1, h0, ite_false]; exact h.keep r hr' h0

/-! ## Restoring the nonvolatile registers -/

/-- The first `n` registers are restored, from the state `sB` the
restoring starts in. -/
structure RI' (s₀ sB : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 8, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {s₀ sB : State} (hp : Pre s₀) (hr4 : sB.gpr .r4 = buf s₀)
    (hsav : ∀ i < 8, sB.mem.readW (buf s₀ + BitVec.ofNat 64 (64 + 8 * i)) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 8) {s : State} (h : RI' s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .r4 (64 + 8 * n)]) s (RI' s₀ sB (n + 1)) := by
  have hr4' : s.gpr .r4 = buf s₀ := by
    rw [h.others _ fun i hi e => (saved_ne hi).2 e.symm, hr4]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 (64 + 8 * n)) 8 := by
    rw [h.rd, h.wr, hr4']; exact hp.in_sav hn _
  have hv : s.mem.readW (buf s₀ + BitVec.ofNat 64 (64 + 8 * n)) 64 = s₀.gpr (saved n) := by
    rw [h.mem]; exact hsav n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (by decide) (show 64 + 8 * n < 2 ^ 15 ∧ (64 + 8 * n) % 4 = 0 by omega_using [hn]) hin,
    Option.some.injEq, exists_eq_left', hr4', hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e => absurd (saved_inj (by omega_arith) hn e) (by omega_using [hi])
      simp only [e, ite_false]; exact h.restored i hi
    · simp
  · simp only [State.write, hr n hn, ite_false]; exact h.others r hr

/-! ## The whole function -/

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

/-- The main part, from the state `s₁` after saving the registers. -/
theorem main_ok {s₁ : State} (hp : Pre s₁) :
    WP isa main s₁ fun s' =>
      (∀ j (hj : j < 16), s'.mem.readW (buf s₁ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₁)[j] + (V s₁)[j]) ∧
      Frame [outR s₁] s₁.mem s'.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, ¬ Words r → r ≠ .r0 → s'.gpr r = s₁.gpr r) := by
  have hl₀ : LI s₁ 0 s₁ := ⟨fun _ _ h => absurd h (by omega_using []), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hload : WP isa (.block load) s₁ (LI s₁ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₁) (fun k s hk h => load_step hp hk h) 16 le_rfl s₁ hl₀
  refine WP.seq (WP.mono hload fun s₂ h₂ => ?_)
  have hh₂ : Holds (V s₁) s₂ := fun k hk => h₂.loaded k hk hk
  refine WP.seq (WP.mono (rounds_ok hh₂ 10) fun s₃ h₃ => ?_)
  have hf₃ : FI s₁ (Rs s₁) 0 s₃ :=
    ⟨fun _ _ h => absurd h (by omega_using []), fun j hj _ => h₃.holds j hj,
      by rw [h₃.mem, h₂.mem]; exact Frame.refl _ _, h₃.rd.trans h₂.rd, h₃.wr.trans h₂.wr,
      fun r hr _ => (h₃.keep r hr).trans (h₂.keep r hr)⟩
  unfold finish
  exact WP.mono (wp_range_flatMap (M := isa) (FI s₁ (Rs s₁)) (fun i s hi h => add_step hp hi h) 16
    le_rfl s₃ hf₃) fun s' h => ⟨fun j hj => h.done j hj hj, h.frame, h.rd, h.wr, h.keep⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.ChaCha20.blockPPC64LE.post s₀ s' := by
  have hs₀ : SI s₀ 0 s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  have hsave : WP isa (.block save) s₀ (SI s₀ 8) := by
    unfold save
    exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 8 le_rfl s₀ hs₀
  refine WP.seq (WP.mono hsave fun s₁ h₁ => ?_)
  have hp₁ : Pre s₁ := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [stR, bufR, st, buf, h₁.gpr, h₁.rd, h₁.wr] <;>
      first | exact hp.rd | exact hp.wr | exact hp.buf_st
  have hV : V s₁ = V s₀ := by
    apply Vector.ext
    intro j hj
    simp only [V, stateAt, Vector.getElem_ofFn, st, h₁.gpr]
    rw [h₁.frame.readW (r := stR s₀) (contains_off (by omega_using [hj]) (by omega_using [hj]))
      (by simpa using Region.Disjoint.sub_right hp.buf_st.symm (savR_sub s₀)) (by decide)]
  have hbuf : buf s₁ = buf s₀ := by simp only [buf, h₁.gpr]
  refine WP.seq (WP.mono (main_ok hp₁) fun s₃ ⟨hout, hf, hrd, hwr, hk⟩ => ?_)
  have hf' : Frame [outR s₀] s₁.mem s₃.mem := by simpa only [outR, hbuf] using hf
  have hr4 : s₃.gpr .r4 = buf s₀ := by rw [hk _ not_words_r4 (by decide), h₁.gpr]
  have hsav : ∀ i < 8, s₃.mem.readW (buf s₀ + BitVec.ofNat 64 (64 + 8 * i)) 64 = s₀.gpr (saved i) :=
    fun i hi => by
      rw [hf'.readW (r := savR s₀) (by simp only [Region.Contains]; bv_omega)
        (by simpa using (outR_sav s₀).symm) (by decide)]
      exact h₁.saved i hi
  have hr₀ : RI' s₀ s₃ 0 s₃ :=
    ⟨fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, hrd.trans h₁.rd, hwr.trans h₁.wr⟩
  refine WP.mono (wp_range_flatMap (M := isa) (RI' s₀ s₃)
    (fun k s hk h => restore_step hp hr4 hsav hk h) 8 le_rfl s₃ hr₀) fun s' h => ⟨?_, ?_⟩
  · intro r hr
    rcases preserved_cases hr with ⟨i, hi, rfl⟩ | ⟨hw, h0⟩
    · exact h.restored i hi
    · rw [h.others r fun i hi e => hw (e ▸ saved_words hi), hk r hw h0, h₁.gpr]
  · show stateAt s'.mem (s₀.gpr .r4) = Spec.ChaCha20.block (stateAt s₀.mem (s₀.gpr .r3))
    rw [h.mem]
    have := block_post (m := s₃.mem) (p := buf s₁) (R := Rs s₁) (v := V s₁) hout
    rw [hbuf] at this
    simp only [Rs, hV] at this
    exact this

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 256⟩]

theorem block_verified :
    Verified PPC64LE.target Impl.ChaCha20.PPC64LE.block Proof.ChaCha20.blockPPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, rfl, rfl, ?_⟩
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.ChaCha20.PPC64LE
