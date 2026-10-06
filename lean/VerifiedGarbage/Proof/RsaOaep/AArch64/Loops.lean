import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash

/-!
# RSAES-OAEP on AArch64: counted loops over bytes

A loop counting down in a register to zero (`count_loop`), and the loops of
the code that XOR, copy and clear bytes of our working space, as functions
of its view `V`: `xorLoop_ok` XORs the `n` bytes at `a` into those at `b`
(`xorV`), as MGF1 does with the digest.
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)

/-! ## Counters -/

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  show eval (.nonzero .x r) s = _
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]

/-- A down-counter in `cr`: after `k` of `n` iterations it is `n - k`. -/
theorem count_loop {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ (s'.gpr cr != 0) = decide (k + 1 ≠ n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero .x cr) s' = some (decide (k + 1 ≠ n)) := by rw [eval_nonzero, hc]
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-- The counter after one more iteration. -/
theorem counter_step {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n - k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n - (k + 1) < 2 ^ 64 by omega),
    show (1 : Nat) % 2 ^ 64 = 1 from rfl]
  rw [show 2 ^ 64 - 1 + (n - k) = (n - (k + 1)) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- Whether the counter is zero. -/
theorem counter_ne {n k : Nat} (hk : k + 1 ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (k + 1)) != 0) = decide (k + 1 ≠ n) := by
  have : BitVec.ofNat 64 (n - (k + 1)) = 0 ↔ k + 1 = n := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    · intro h; rw [h, Nat.sub_self]; rfl
  by_cases h : k + 1 = n
  · simp [h]
  · have h' : ¬ BitVec.ofNat 64 (n - (k + 1)) = 0 := fun e => h (this.mp e)
    rw [decide_eq_true h, bne_iff_ne]
    exact h'

/-- The carry of `subs a, c`: no borrow. -/
theorem carry_sub (a c : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + (~~~c).toNat + true.toNat) = decide (c.toNat ≤ a.toNat) := by
  have hn : (~~~c).toNat = 2 ^ 64 - 1 - c.toNat := BitVec.toNat_not
  have := c.isLt
  rw [hn]
  simp only [Bool.toNat_true, decide_eq_decide]
  omega

/-! ## XORing bytes -/

/-- The `j` bytes at `b` XORed with those at `a`. -/
def xorV (V : Nat → Byte) (a b j : Nat) (x : Nat) : Byte :=
  if b ≤ x ∧ x < b + j then V x ^^^ V (a + (x - b)) else V x

theorem xorStep_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a b j : Nat} (ha : a + j < oRsa) (hb : b + j < oRsa)
    (h11 : u.gpr .x11 = off S (a + j)) (h12 : u.gpr .x12 = off S (b + j)) (ws : List Region) :
    WP isa (.block Impl.RsaOaep.AArch64.Mgf1.xorBody) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S (upd V (b + j) (V (b + j) ^^^ V (a + j))) W ∧ u'.gpr .x11 = off S (a + j + 1) ∧
      u'.gpr .x12 = off S (b + j + 1) ∧ u'.gpr .x14 = u.gpr .x14 - BitVec.ofNat 64 1 := by
  have r1 : InRegions (u.rd ++ u.wr) (off S (a + j)) 1 := L.sld (by omega)
  have r2 : InRegions (u.rd ++ u.wr) (off S (b + j)) 1 := L.sld (by omega)
  have w2 : InRegions u.wr (off S (b + j)) 1 := L.sst (by omega)
  have v1 : u.mem (off S (a + j)) = V (a + j) := R.scr _ ha
  have v2 : u.mem (off S (b + j)) = V (b + j) := R.scr _ hb
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off S (b + j)) 1 (V (b + j) ^^^ V (a + j)) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S (a + j) + BitVec.ofNat 64 1 ∧
      u'.gpr .x12 = off S (b + j) + BitVec.ofNat 64 1 ∧ u'.gpr .x14 = u.gpr .x14 - BitVec.ofNat 64 1) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x14⟩ => ?_
  · oaep_run [Impl.RsaOaep.AArch64.Mgf1.xorBody, h11, h12, BitVec.add_zero, r1, r2, w2, read_one, byte64, v1, v2,
      byte_xor]
    oaep_fin
  have R' : Rep u'.mem F S (upd V (b + j) (V (b + j) ^^^ V (a + j))) W := by rw [hm]; exact R.wb L.geo hb _
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R', ?_, ?_, x14⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  · rw [hm]; exact frame_wb (Frame.refl _ _) hb _
  · exact x11.trans (off_off S (a + j) 1)
  · exact x12.trans (off_off S (b + j) 1)

theorem xorV_succ (V : Nat → Byte) {a b j n : Nat} (hj : j < n) (hab : a + n ≤ b ∨ b + n ≤ a) :
    upd (xorV V a b j) (b + j) (xorV V a b j (b + j) ^^^ xorV V a b j (a + j)) = xorV V a b (j + 1) := by
  funext x
  simp only [upd, xorV]
  by_cases hx : x = b + j
  · subst hx
    rw [ifp rfl, ifn (by omega), ifn (by omega), ifp (by omega), Nat.add_sub_cancel_left]
  · rw [ifn hx]
    by_cases h : b ≤ x ∧ x < b + j
    · rw [ifp h, ifp (by omega)]
    · rw [ifn h, ifn (by omega)]

/-- The `n` bytes at `a` XORed into the `n` bytes at `b` (`x11`, `x12`, the
count in `x14`). -/
theorem xorLoop_ok {u₀ : State} {F S : Addr} (L : Lay u₀ F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u₀.mem F S V W) {a b n : Nat} (hn : 0 < n) (ha : a + n ≤ oRsa) (hb : b + n ≤ oRsa)
    (hab : a + n ≤ b ∨ b + n ≤ a) (h11 : u₀.gpr .x11 = off S a) (h12 : u₀.gpr .x12 = off S b)
    (h14 : u₀.gpr .x14 = BitVec.ofNat 64 n) (ws : List Region) :
    WP isa (.loop (.block Impl.RsaOaep.AArch64.Mgf1.xorBody) (.nonzero .x .x14)) u₀ fun u =>
      Lay u F S ∧ Step F S ws u₀ u ∧ Rep u.mem F S (xorV V a b n) W := by
  have : oRsa = 8192 := rfl
  refine WP.mono (count_loop hn (fun j u => Lay u F S ∧ Step F S ws u₀ u ∧ Rep u.mem F S (xorV V a b j) W ∧
      u.gpr .x11 = off S (a + j) ∧ u.gpr .x12 = off S (b + j) ∧ u.gpr .x14 = BitVec.ofNat 64 (n - j))
    (fun j hj u ⟨Lu, Su, Ru, u11, u12, u14⟩ => ?_)
    ⟨L, Step.refl _ _ _ _, by
      refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R
      simp only [xorV]; rw [ifn (by omega)], by rw [h11]; rfl, by rw [h12]; rfl, h14⟩)
    fun u ⟨Lu, Su, Ru, _⟩ => ⟨Lu, Su, Ru⟩
  refine WP.mono (xorStep_ok Lu Ru (a := a) (b := b) (j := j) (by omega) (by omega) u11 u12 ws)
    fun u' ⟨L', S', R', x11, x12, x14⟩ => ⟨⟨L', Su.trans S', xorV_succ V hj hab ▸ R', x11, x12, ?_⟩, ?_⟩
  · rw [x14, u14, counter_step hj (by omega)]
  · rw [x14, u14, counter_step hj (by omega)]; exact counter_ne hj (by omega)

end VG.Proof.RsaOaep.AArch64
