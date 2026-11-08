module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Ladder
public import VerifiedGarbage.Proof.X25519.Chain250
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on PPC64LE: the inversion

`invert` computes `z^(p-2)` into `R` for the element `z` at `Z2` by ref10's
addition chain, `VG.Proof.X25519.invert` (`invert_ok`): each product updates
the slots `A`–`D` (`chainMul`), each run of squarings is a loop counted by
`r12` (`chainSqn`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P Fe)

theorem iteT {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

section
variable {b : Addr}

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]

theorem Cur.congr {s0 s : State} {a c : BitVec 64} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : Cur b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.r0, h.r12, (h.slots.mono hq).congr hv⟩

/-- A product of the chain, the slots then `qs'` with the elements `w`. -/
theorem chainMul {s0 : State} {a c : BitVec 64} {o x y : Nat} {qs qs' : List Nat} {v w : Nat → Fe}
    (hq : Sep1 o qs = true) (hal : Al4 o qs = true) (ho : o + 32 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs)
    (hqs : ∀ q ∈ qs', q ∈ o :: qs) (hw : ∀ q ∈ qs', upd v o (v x * v y) q = w q) {s : State}
    (h : Cur b s0 a c qs v s) : WP isa (mul o x y) s (Cur b s0 a c qs' w) :=
  WP.mono (opMul hq hal ho hx hy h) fun _ h' => h'.congr hqs hw

/-- `[x]` squared `n` times into `[o]`, the slots then `qs'` with the elements `w`; `t1` counts. -/
theorem chainSqn {s0 : State} {a c : BitVec 64} {o x n : Nat} {qs qs' : List Nat} {v w : Nat → Fe}
    (hq : Sep1 o qs = true) (hal : Al4 o qs = true) (hq' : Sep1 o (o :: qs) = true)
    (hal' : Al4 o (o :: qs) = true) (ho : o + 32 ≤ ACC) (hx : x ∈ qs)
    (hn : 2 ≤ n) (hn' : n ≤ 255) (hqs : ∀ q ∈ qs', q ∈ o :: qs)
    (hw : ∀ q ∈ qs', upd v o (VG.Proof.X25519.sqn (v x) n) q = w q) {s : State}
    (h : Cur b s0 a c qs v s) : WP isa (Impl.X25519.PPC64LE.sqn o x n) s fun s' => ∃ c', Cur b s0 a c' qs' w s' := by
  unfold Impl.X25519.PPC64LE.sqn
  refine WP.seq (WP.mono (opMul hq hal ho hx hx h) fun s1 h1 => ?_)
  refine WP.seq (wp_li (imm := n - 1) (by omega) fun s2 u2 => WP.block_nil ?_)
  have h2 : Cur b s0 a (BitVec.ofNat 64 (n - 1)) (o :: qs) (upd v o (VG.Proof.X25519.sqn (v x) (n - (n - 1)))) s2 := by
    rw [show n - (n - 1) = 1 by omega]
    exact ⟨h1.ctx.of_rest (u2.rest (ws := [.r12]) (by decide)) (by decide),
      h1.stp.trans (Stp.of_rest (u2.rest (ws := [.r12]) (by decide)) (by decide) u2.mem),
      by rw [u2.other _ (by decide), h1.r0], u2.gpr, by rw [u2.mem]; exact h1.slots⟩
  refine WP.mono (Q := fun t => Cur b s0 a (BitVec.ofNat 64 0) (o :: qs)
      (upd v o (VG.Proof.X25519.sqn (v x) n)) t) (WP.loop (M := isa)
    (fun m t => 1 ≤ m ∧ m ≤ n - 1 ∧
      Cur b s0 a (BitVec.ofNat 64 m) (o :: qs) (upd v o (VG.Proof.X25519.sqn (v x) (n - m))) t) ?_
    (n - 1) s2 ⟨by omega, Nat.le_refl _, h2⟩) fun t ht => ⟨_, ht.congr hqs hw⟩
  rintro m t ⟨hm1, hm, ht⟩
  refine WP.seq (WP.mono (opMul (o := o) (x := o) (y := o) hq' hal' ho List.mem_cons_self List.mem_cons_self ht)
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
  refine wp_subi (by decide) (by decide) fun t2 u2 => WP.block_nil ?_
  have e1 : t2.gpr .r12 = BitVec.ofNat 64 (m - 1) := by
    rw [u2.gpr, h1'.r12, ofNat_sub_one hm1 (by omega)]
  have h2' : Cur b s0 a (BitVec.ofNat 64 (m - 1)) (o :: qs)
      (upd v o (VG.Proof.X25519.sqn (v x) (n - (m - 1)))) t2 :=
    ⟨h1'.ctx.of_rest (u2.rest (ws := [.r12]) (by decide)) (by decide),
      h1'.stp.trans (Stp.of_rest (u2.rest (ws := [.r12]) (by decide)) (by decide) u2.mem),
      by rw [u2.other _ (by decide), h1'.r0], e1, by rw [u2.mem]; exact h1'.slots⟩
  rw [eval_nonzero, e1, ofNat_ne_zero (by omega)]
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
theorem invert_ok {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b [Z2, X2] v) (h0 : s.gpr .r0 = a) :
    WP isa Impl.X25519.PPC64LE.invert s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b IQ (upd v R (VG.Proof.X25519.pw (v Z2) (P - 2))) := by
  have hR : R = 480 := rfl
  let z := v Z2
  let x2 := v X2
  have h : Cur b s a (s.gpr .r12) [Z2, X2] (cv z x2 0 0 0 0) s :=
    ⟨hc, Stp.refl _ _, h0, rfl, hS.congr fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl⟩
  unfold Impl.X25519.PPC64LE.invert
  let t0 := z * z
  refine WP.seq (WP.mono (chainMul (o := A) (x := Z2) (y := Z2) (qs' := [A, Z2, X2]) (w := cv z x2 t0 0 0 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h) fun s1 h1 => ?_)
  let t1a := t0 * t0
  refine WP.seq (WP.mono (chainMul (o := B) (x := A) (y := A) (qs' := [B, A, Z2, X2])
    (w := cv z x2 t0 t1a 0 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h1)
    fun s2 h2 => ?_)
  let t1b := t1a * t1a
  refine WP.seq (WP.mono (chainMul (o := B) (x := B) (y := B) (qs' := [B, A, Z2, X2])
    (w := cv z x2 t0 t1b 0 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h2)
    fun s3 h3 => ?_)
  let t1c := z * t1b
  refine WP.seq (WP.mono (chainMul (o := B) (x := Z2) (y := B) (qs' := [B, A, Z2, X2])
    (w := cv z x2 t0 t1c 0 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h3)
    fun s4 h4 => ?_)
  let t0' := t0 * t1c
  refine WP.seq (WP.mono (chainMul (o := A) (x := A) (y := B) (qs' := [B, A, Z2, X2])
    (w := cv z x2 t0' t1c 0 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h4)
    fun s5 h5 => ?_)
  let t2a := t0' * t0'
  refine WP.seq (WP.mono (chainMul (o := C) (x := A) (y := A) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1c t2a 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h5)
    fun s6 h6 => ?_)
  let t1d := t1c * t2a
  refine WP.seq (WP.mono (chainMul (o := B) (x := B) (y := C) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1d t2a 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h6)
    fun s7 h7 => ?_)
  let t2b := VG.Proof.X25519.sqn t1d 5
  refine WP.seq (WP.mono (chainSqn (o := C) (x := B) (n := 5) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1d t2b 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h7) fun s8 ⟨_, h8⟩ => ?_)
  let t1e := t2b * t1d
  refine WP.seq (WP.mono (chainMul (o := B) (x := C) (y := B) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2b 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h8)
    fun s9 h9 => ?_)
  let t2c := VG.Proof.X25519.sqn t1e 10
  refine WP.seq (WP.mono (chainSqn (o := C) (x := B) (n := 10) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2c 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h9) fun s10 ⟨_, h10⟩ => ?_)
  let t2d := t2c * t1e
  refine WP.seq (WP.mono (chainMul (o := C) (x := C) (y := B) (qs' := [C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2d 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h10)
    fun s11 h11 => ?_)
  let t3a := VG.Proof.X25519.sqn t2d 20
  refine WP.seq (WP.mono (chainSqn (o := D) (x := C) (n := 20) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2d t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h11) fun s12 ⟨_, h12⟩ => ?_)
  let t2e := t3a * t2d
  refine WP.seq (WP.mono (chainMul (o := C) (x := D) (y := C) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2e t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h12)
    fun s13 h13 => ?_)
  let t2f := VG.Proof.X25519.sqn t2e 10
  refine WP.seq (WP.mono (chainSqn (o := C) (x := C) (n := 10) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1e t2f t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h13) fun s14 ⟨_, h14⟩ => ?_)
  let t1f := t2f * t1e
  refine WP.seq (WP.mono (chainMul (o := B) (x := C) (y := B) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2f t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h14)
    fun s15 h15 => ?_)
  let t2g := VG.Proof.X25519.sqn t1f 50
  refine WP.seq (WP.mono (chainSqn (o := C) (x := B) (n := 50) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2g t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h15) fun s16 ⟨_, h16⟩ => ?_)
  let t2h := t2g * t1f
  refine WP.seq (WP.mono (chainMul (o := C) (x := C) (y := B) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2h t3a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h16)
    fun s17 h17 => ?_)
  let t3b := VG.Proof.X25519.sqn t2h 100
  refine WP.seq (WP.mono (chainSqn (o := D) (x := C) (n := 100) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2h t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h17) fun s18 ⟨_, h18⟩ => ?_)
  let t2i := t3b * t2h
  refine WP.seq (WP.mono (chainMul (o := C) (x := D) (y := C) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2i t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h18)
    fun s19 h19 => ?_)
  let t2j := VG.Proof.X25519.sqn t2i 50
  refine WP.seq (WP.mono (chainSqn (o := C) (x := C) (n := 50) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1f t2j t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h19) fun s20 ⟨_, h20⟩ => ?_)
  let t1g := t2j * t1f
  refine WP.seq (WP.mono (chainMul (o := B) (x := C) (y := B) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1g t2j t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h20)
    fun s21 h21 => ?_)
  let t1h := VG.Proof.X25519.sqn t1g 5
  refine WP.seq (WP.mono (chainSqn (o := B) (x := B) (n := 5) (qs' := [D, C, B, A, Z2, X2])
    (w := cv z x2 t0' t1h t2j t3b) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) h21) fun s22 ⟨_, h22⟩ => ?_)
  have hinv : t1h * t0' = VG.Proof.X25519.pw (v Z2) (P - 2) := by
    rw [← VG.Proof.X25519.pow_pw, ← VG.Proof.X25519.invert_eq]
    rfl
  refine WP.mono (chainMul (o := R) (x := B) (y := A) (qs' := IQ) (w := upd v R (VG.Proof.X25519.pw (v Z2) (P - 2)))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ h22) fun s' h' =>
    ⟨h'.stp, h'.ctx, h'.slots⟩
  intro q hq
  simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · rw [upd_of_ne _ _ (by decide), upd_of_ne _ _ (by decide)]; rfl
  · rw [upd_self, upd_self]; exact hinv
  · rw [upd_of_ne _ _ (by decide), upd_of_ne _ _ (by decide)]; rfl

end

end VG.Proof.X25519.PPC64LE
