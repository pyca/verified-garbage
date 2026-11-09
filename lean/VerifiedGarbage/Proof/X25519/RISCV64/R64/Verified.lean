module

public import VerifiedGarbage.Proof.X25519.Contract
public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Ladder
public import VerifiedGarbage.Proof.X25519.RISCV64.Invert
public import VerifiedGarbage.Proof.X25519.RISCV64.Main
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.X25519.RISCV64.Bits
import VerifiedGarbage.Proof.X25519.RISCV64.Freeze
public import VerifiedGarbage.Proof.X25519.RISCV64.Setup
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.X25519.RISCV64.R64
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.RISCV64.R64.CT
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# X25519 on RISC-V, 64-bit limbs: verified

The inversion: `invertChain` computes `z^(p-2)` into `R` for the element `z`
at `Z2` by ref10's addition chain, `VG.Proof.X25519.invert` (`invertChain_ok`):
each product updates the slots `A`–`D` (`chainMul`), each run of squarings
is a loop counted by `t1` (`chainSqn`).

Then the whole function: `vg_x25519` writes `X25519(k, u)` to `out`
(`x25519_correct`), against `Proof/X25519/RISCV64/Main.lean`'s contract,
with that file's decoding, bits and final reduction, and meets the shared
contract of `Spec/X25519/Contract.lean`: the code calls no function and
writes only caller-saved registers (`WP.keep`), so the ABI's obligations hold
of every execution.
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64.R64

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64.R64
open VG.Impl.X25519.RISCV64 (X1 X2 Z2 X3 Z3 A B C D R ACC BITS one)
open VG.Spec.X25519 (P Fe bytesAt)

section
variable {b : Addr}

/-! ## The inversion -/

theorem Cur.congr {s0 s : State} {a c : BitVec 64} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : Cur b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.t2, h.t1, (h.slots.mono hq).congr hv⟩

/-- A product of the chain, the slots then `qs'` with the elements `w`. -/
theorem chainMul {s0 : State} {a c : BitVec 64} {o x y : Nat} {qs qs' : List Nat} {v w : Nat → Fe}
    (hq : Sep8 o qs = true) (ho : o + 32 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs)
    (hqs : ∀ q ∈ qs', q ∈ o :: qs) (hw : ∀ q ∈ qs', upd v o (v x * v y) q = w q) {s : State}
    (h : Cur b s0 a c qs v s) : WP isa (mul o x y) s (Cur b s0 a c qs' w) :=
  WP.mono (opMul hq ho hx hy h) fun _ h' => h'.congr hqs hw

/-- `[x]` squared `n` times into `[o]`, the slots then `qs'` with the elements `w`; `t1` counts. -/
theorem chainSqn {s0 : State} {a c : BitVec 64} {o x n : Nat} {qs qs' : List Nat} {v w : Nat → Fe}
    (hq : Sep8 o qs = true) (hq' : Sep8 o (o :: qs) = true) (ho : o + 32 ≤ ACC) (hx : x ∈ qs)
    (hn : 2 ≤ n) (hn' : n ≤ 255) (hqs : ∀ q ∈ qs', q ∈ o :: qs)
    (hw : ∀ q ∈ qs', upd v o (VG.Proof.X25519.sqn (v x) n) q = w q) {s : State}
    (h : Cur b s0 a c qs v s) : WP isa (Impl.X25519.RISCV64.R64.sqn o x n) s fun s' => ∃ c', Cur b s0 a c' qs' w s' := by
  unfold Impl.X25519.RISCV64.R64.sqn
  refine WP.seq (WP.mono (opMul hq ho hx hx h) fun s1 h1 => ?_)
  refine WP.seq (wp_li (imm := n - 1) (by omega) fun s2 u2 => WP.block_nil ?_)
  have h2 : Cur b s0 a (BitVec.ofNat 64 (n - 1)) (o :: qs) (upd v o (VG.Proof.X25519.sqn (v x) (n - (n - 1)))) s2 := by
    rw [show n - (n - 1) = 1 by omega]
    exact ⟨h1.ctx.of_rest (u2.rest (ws := [.t1]) (by decide)) (by decide),
      h1.stp.trans (Stp.of_rest (u2.rest (ws := [.t1]) (by decide)) (by decide) u2.mem),
      by rw [u2.other _ (by decide), h1.t2], u2.gpr, by rw [u2.mem]; exact h1.slots⟩
  refine WP.mono (Q := fun t => Cur b s0 a (BitVec.ofNat 64 0) (o :: qs)
      (upd v o (VG.Proof.X25519.sqn (v x) n)) t) (WP.loop (M := isa)
    (fun m t => 1 ≤ m ∧ m ≤ n - 1 ∧
      Cur b s0 a (BitVec.ofNat 64 m) (o :: qs) (upd v o (VG.Proof.X25519.sqn (v x) (n - m))) t) ?_
    (n - 1) s2 ⟨by omega, Nat.le_refl _, h2⟩) fun t ht => ⟨_, ht.congr hqs hw⟩
  rintro m t ⟨hm1, hm, ht⟩
  refine WP.seq (WP.mono (opMul (o := o) (x := o) (y := o) hq' ho List.mem_cons_self List.mem_cons_self ht)
    fun t1 h1 => ?_)
  have h1' : Cur b s0 a (BitVec.ofNat 64 m) (o :: qs)
      (upd v o (VG.Proof.X25519.sqn (v x) (n - (m - 1)))) t1 := by
    refine h1.congr (fun q hq => List.mem_cons_of_mem _ hq) fun q _ => ?_
    by_cases hqo : q = o
    · subst hqo
      simp only [upd_self]
      rw [show n - (m - 1) = (n - m) + 1 by omega]
      rfl
    · rw [upd_of_ne _ _ hqo, upd_of_ne _ _ hqo, upd_of_ne _ _ hqo]
  refine wp_subi (by decide) fun t2 u2 => WP.block_nil ?_
  have e1 : t2.gpr .t1 = BitVec.ofNat 64 (m - 1) := by
    rw [u2.gpr, h1'.t1, ofNat_sub_one hm1 (by omega)]
  have h2' : Cur b s0 a (BitVec.ofNat 64 (m - 1)) (o :: qs)
      (upd v o (VG.Proof.X25519.sqn (v x) (n - (m - 1)))) t2 :=
    ⟨h1'.ctx.of_rest (u2.rest (ws := [.t1]) (by decide)) (by decide),
      h1'.stp.trans (Stp.of_rest (u2.rest (ws := [.t1]) (by decide)) (by decide) u2.mem),
      by rw [u2.other _ (by decide), h1'.t2], e1, by rw [u2.mem]; exact h1'.slots⟩
  rw [eval_nonzero_ofNat t2 .t1 (by omega) e1]
  by_cases hm0 : m - 1 = 0
  · refine .inl ⟨by simp [hm0], ?_⟩
    rw [show n - (m - 1) = n by omega, hm0] at h2'
    exact h2'
  · exact .inr ⟨by simp [hm0], m - 1, by omega, by omega, by omega, h2'⟩

/-- The chain's slots: `z` at `Z2`, `x2` at `X2` and `t0`–`t3` at `A`–`D`. -/
def cv (z x2 t0 t1 t2 t3 : Fe) (q : Nat) : Fe :=
  if q = Z2 then z else if q = X2 then x2 else if q = A then t0 else if q = B then t1 else if q = C then t2
  else t3

/-- **The inversion**: `[R] = [Z2]^(p-2)` by ref10's chain (`VG.Proof.X25519.invert`). -/
theorem invertChain_ok {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b [Z2, X2] v) (h0 : s.gpr .t2 = a) :
    WP isa invertChain s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b IQ (upd v R (VG.Proof.X25519.pw (v Z2) (P - 2))) := by
  have hR : R = 480 := rfl
  let z := v Z2
  let x2 := v X2
  have h : Cur b s a (s.gpr .t1) [Z2, X2] (cv z x2 0 0 0 0) s :=
    ⟨hc, Stp.refl _ _, h0, rfl, hS.congr fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl⟩
  unfold invertChain
  let t0 := z * z
  refine WP.seq (WP.mono (chainMul (o := A) (x := Z2) (y := Z2) (qs' := [A, Z2, X2]) (w := cv z x2 t0 0 0 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h) fun s1 h1 => ?_)
  let t1a := t0 * t0
  refine WP.seq (WP.mono (chainMul (o := B) (x := A) (y := A) (qs' := [B, A, Z2, X2])
    (w := cv z x2 t0 t1a 0 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h1)
    fun s2 h2 => ?_)
  let t1b := t1a * t1a
  refine WP.seq (WP.mono (chainMul (o := B) (x := B) (y := B) (qs' := [B, A, Z2, X2])
    (w := cv z x2 t0 t1b 0 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h2)
    fun s3 h3 => ?_)
  let t1c := z * t1b
  refine WP.seq (WP.mono (chainMul (o := B) (x := Z2) (y := B) (qs' := [B, A, Z2, X2])
    (w := cv z x2 t0 t1c 0 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h3)
    fun s4 h4 => ?_)
  let t0' := t0 * t1c
  refine WP.seq (WP.mono (chainMul (o := A) (x := A) (y := B) (qs' := [B, A, Z2, X2])
    (w := cv z x2 t0' t1c 0 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h4)
    fun s5 h5 => ?_)
  let t2a := t0' * t0'
  refine WP.seq (WP.mono (chainMul (o := C) (x := A) (y := A) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1c t2a 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h5)
    fun s6 h6 => ?_)
  let t1d := t1c * t2a
  refine WP.seq (WP.mono (chainMul (o := B) (x := B) (y := C) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1d t2a 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h6)
    fun s7 h7 => ?_)
  let t2b := VG.Proof.X25519.sqn t1d 5
  refine WP.seq (WP.mono (chainSqn (o := C) (x := B) (n := 5) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1d t2b 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h7) fun s8 ⟨_, h8⟩ => ?_)
  let t1e := t2b * t1d
  refine WP.seq (WP.mono (chainMul (o := B) (x := C) (y := B) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2b 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h8)
    fun s9 h9 => ?_)
  let t2c := VG.Proof.X25519.sqn t1e 10
  refine WP.seq (WP.mono (chainSqn (o := C) (x := B) (n := 10) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2c 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h9) fun s10 ⟨_, h10⟩ => ?_)
  let t2d := t2c * t1e
  refine WP.seq (WP.mono (chainMul (o := C) (x := C) (y := B) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2d 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h10)
    fun s11 h11 => ?_)
  let t3a := VG.Proof.X25519.sqn t2d 20
  refine WP.seq (WP.mono (chainSqn (o := D) (x := C) (n := 20) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2d t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h11) fun s12 ⟨_, h12⟩ => ?_)
  let t2e := t3a * t2d
  refine WP.seq (WP.mono (chainMul (o := C) (x := D) (y := C) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2e t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h12)
    fun s13 h13 => ?_)
  let t2f := VG.Proof.X25519.sqn t2e 10
  refine WP.seq (WP.mono (chainSqn (o := C) (x := C) (n := 10) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2f t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h13) fun s14 ⟨_, h14⟩ => ?_)
  let t1f := t2f * t1e
  refine WP.seq (WP.mono (chainMul (o := B) (x := C) (y := B) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2f t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h14)
    fun s15 h15 => ?_)
  let t2g := VG.Proof.X25519.sqn t1f 50
  refine WP.seq (WP.mono (chainSqn (o := C) (x := B) (n := 50) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2g t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h15) fun s16 ⟨_, h16⟩ => ?_)
  let t2h := t2g * t1f
  refine WP.seq (WP.mono (chainMul (o := C) (x := C) (y := B) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2h t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h16)
    fun s17 h17 => ?_)
  let t3b := VG.Proof.X25519.sqn t2h 100
  refine WP.seq (WP.mono (chainSqn (o := D) (x := C) (n := 100) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2h t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h17) fun s18 ⟨_, h18⟩ => ?_)
  let t2i := t3b * t2h
  refine WP.seq (WP.mono (chainMul (o := C) (x := D) (y := C) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2i t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h18)
    fun s19 h19 => ?_)
  let t2j := VG.Proof.X25519.sqn t2i 50
  refine WP.seq (WP.mono (chainSqn (o := C) (x := C) (n := 50) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2j t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h19) fun s20 ⟨_, h20⟩ => ?_)
  let t1g := t2j * t1f
  refine WP.seq (WP.mono (chainMul (o := B) (x := C) (y := B) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1g t2j t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h20)
    fun s21 h21 => ?_)
  let t1h := VG.Proof.X25519.sqn t1g 5
  refine WP.seq (WP.mono (chainSqn (o := B) (x := B) (n := 5) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1h t2j t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h21) fun s22 ⟨_, h22⟩ => ?_)
  have hinv : t1h * t0' = VG.Proof.X25519.pw (v Z2) (P - 2) := by
    rw [← VG.Proof.X25519.pow_pw, ← VG.Proof.X25519.invert_eq]
    rfl
  refine WP.mono (chainMul (o := R) (x := B) (y := A) (qs' := IQ) (w := upd v R (VG.Proof.X25519.pw (v Z2) (P - 2)))
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ h22) fun s' h' =>
    ⟨h'.stp, h'.ctx, h'.slots⟩
  intro q hq
  simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · rw [upd_of_ne _ _ (by decide), upd_of_ne _ _ (by decide)]; rfl
  · rw [upd_self, upd_self]; exact hinv
  · rw [upd_of_ne _ _ (by decide), upd_of_ne _ _ (by decide)]; rfl

theorem lastSwap_ok {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h0 : s.gpr .t2 = BitVec.ofNat 64 sw) {v : Nat → Fe} (hS : SlotsOk s.mem b LQ v) :
    WP isa (.block lastSwap) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b LQ (swapV Z2 Z3 sw (swapV X2 X3 sw v)) := by
  simp only [lastSwap, mask, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_sub fun s2 u2 => ?_
  have hr2 : Rest [.t0] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have e11 : s2.gpr .t0 = 0 - BitVec.ofNat 64 sw := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), h0]; rfl
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (cswapS (v := v) (qs := LQ) (by decide) (by decide) (by decide) (by decide) (by decide) hc2
    hsw e11 (by rw [hm2]; exact hS)) fun s3 ⟨hr3, hf3, hS3⟩ => ?_
  have hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine WP.mono (cswapS (by decide) (by decide) (by decide) (by decide) (by decide) hc3 hsw
    (by rw [hr3.gpr _ (by decide), e11]) hS3) fun s4 ⟨hr4, hf4, hS4⟩ =>
    ⟨⟨(hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
      by rw [← hm2]; exact hf3.trans hf4⟩, hc3.of_rest hr4 (by decide), hS4⟩

end

theorem x25519_correct {s : State} (hp : XPre s) :
    WP isa x25519 s fun s' => x25519RISCV64.post s s' := by
  have hB : BITS = 608 := rfl
  have hsc_in : (⟨s.gpr .a1, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  unfold x25519
  have hsub : Region.Sub ⟨wsBase s, 2048⟩ ⟨s.gpr .a3, 4096⟩ := by
    have := wsBase_sub s (o := 0) (n := 2048) (by decide)
    rwa [BitVec.add_zero] at this
  refine WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, hf1, hS1, hr1⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok hc1 (hr1.gpr .a1 (by decide)) (by rw [hr1.rd, hr1.wr]; exact hsc_in)
    (hp.sc_ws.sub_right hsub)) fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  have hS2 := hS1.bits (by decide) hf2
  refine WP.seq (WP.mono (ladder_ok hc2 hb2 hS2) fun s3 ⟨hst3, hc3, h0, hS3⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hc3 (ladderAfter_swap_le _ _ (by decide)) h0 hS3)
    fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  refine WP.seq (WP.mono (invertChain_ok hc4 (hS4.mono (by decide)) rfl) fun s5 ⟨hst5, hc5, hS5⟩ => ?_)
  refine WP.seq (WP.mono (mulS (o := X2) (x := X2) (y := R) (by decide) (by decide) (by decide)
    (by decide) hc5 hS5) fun s6 ⟨hr6, hf6, hS6⟩ => ?_)
  -- The registers and regions along the way.
  have hst6 : Stp (wsBase s) s2 s6 := hst3.trans (hst4.trans (hst5.trans ⟨hr6.mono (by decide), hf6⟩))
  have h3' : s6.gpr .a0 = s.gpr .a0 := by
    rw [hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide), hr1.gpr _ (by decide)]
  have hwr6 : s6.wr = s.wr := by rw [hst6.rest.wr, hr2.wr, hr1.wr]
  have hc6 : Ctx (wsBase s) s6 := hc5.of_rest hr6 (by decide)
  refine WP.mono (freeze_ok hc6 h3' (by rw [hwr6, hp.wr]; simp) (hp.out_ws.sub_right hsub).symm)
    fun s7 ⟨hbytes, _, _⟩ => ?_
  -- The result.
  show bytesAt s7.mem _ 32 = _
  rw [hbytes, VG.Proof.X25519.x25519_eq]
  -- The scalar, as read by `bits`.
  have hk : bytesAt s1.mem (s.gpr .a1) 32 = bytesAt s.mem (s.gpr .a1) 32 :=
    bytesAt_frame hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.sc_ws
  rw [hk] at hS3 h0 hS4 hS5 hS6
  have e6 : FS s6.mem (wsBase s) X2 = _ := hS6 X2 (by decide)
  rw [← VG.Proof.X25519.toFe_val, ← VG.Proof.X25519.encodeUCoordinate_eq]
  change VG.Spec.X25519.encodeUCoordinate (FS s6.mem (wsBase s) X2) = _
  rw [e6]
  simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X25519.invert_eq, VG.Proof.X25519.pow_pw, cswap_fst,
    uOf, X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

end

section

open VG VG.RISCV64

theorem x25519_ok (s : State) (hs : x25519RISCV64.pre s) :
    ∃ t s', Exec isa Impl.X25519.RISCV64.R64.x25519 s t s' ∧ abiPreserved s s' ∧
      x25519RISCV64.post s s' := by
  obtain ⟨t, s', he, h, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (x25519_correct (XPre.of hs)) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), h⟩

theorem x25519_ct' :
    ConstantTime isa x25519RISCV64.pre x25519RISCV64.pub Impl.X25519.RISCV64.R64.x25519 :=
  x25519_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying the precondition. -/
def x25519Sat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_verified :
    Verified RISCV64.target Impl.X25519.RISCV64.R64.x25519 (Proof.X25519.x25519Contract RISCV64.abi) :=
  Verified.of_correct x25519_ok x25519_ct' (by
    contract_implies [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, Proof.X25519.RISCV64.x25519RISCV64,
      RISCV64.abi, RISCV64.argRegs] [Proof.X25519.RISCV64.R64.x25519Sat]
      using Proof.X25519.RISCV64.R64.x25519Sat)

end

end VG.Proof.X25519.RISCV64.R64
