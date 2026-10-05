import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.MlKem.Arm.Poly

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Common`. -/
section

/-!
# ML-KEM on 32-bit ARM: common lemmas

What the proofs of the primitives share: the rule for a loop counted down to
zero (`wp_loop_ne`), the symbolic execution of a block (`run_block`),
addresses in the arrays, and the arithmetic of the reductions modulo `q`
(`fixq`, the value `VG.Impl.MlKem.Arm.fixup` computes).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm
open VG.Spec.MlKem

/-! ## Loops -/

/-- A `do … while (ne)` loop whose body runs `N` times: iteration `i` keeps
the invariant, and sets `Z` exactly when it is the last. -/
theorem wp_loop_ne {body : Prog isa} {Q : State → Prop} (Inv : Nat → State → Prop) {N : Nat}
    (hN : 0 < N)
    (hstep : ∀ i < N, ∀ s, Inv i s → WP isa body s (fun s' => Inv (i + 1) s' ∧ s'.z = decide (i + 1 = N)))
    (hQ : ∀ s, Inv N s → Q s) {s₀ : State} (h0 : Inv 0 s₀) : WP isa (.loop body .ne) s₀ Q := by
  let I : Nat → State → Prop := fun n s => ∃ i, i < N ∧ n = N - i ∧ Inv i s
  have hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  by_cases h : i + 1 = N
  · refine .inl ⟨?_, hQ s' (h ▸ hs')⟩
    show some (!s'.z) = some false
    rw [hz, decide_eq_true h]; rfl
  · refine .inr ⟨?_, N - (i + 1), by omega, i + 1, by omega, rfl, hs'⟩
    show some (!s'.z) = some true
    rw [hz, decide_eq_false h]; rfl

/-- The flag `Z` after `subs r, r, #k` from `k (N - i)`: set when the count
reaches zero. -/
theorem count_z {N i k : Nat} (hi : i < N) (hk0 : 0 < k) (hk : k * N < 2 ^ 32) :
    (BitVec.ofNat 32 (k * (N - i)) - BitVec.ofNat 32 k == 0) = decide (i + 1 = N) := by
  by_cases h : i + 1 = N
  · subst h
    simp only [decide_true, Nat.add_sub_cancel_left, Nat.mul_one, BitVec.sub_self]
    rfl
  · simp only [decide_eq_false h, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    have h1 : k * (N - i) < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hk
    have h2 : k * 1 ≤ k * (N - i) := Nat.mul_le_mul_left _ (by omega)
    have h3 : k * 2 ≤ k * (N - i) := Nat.mul_le_mul_left _ (by omega)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt (a := k) (by omega)] at this
    have h0 : (0 : BitVec 32).toNat = 0 := rfl
    omega

/-- The count after `subs r, r, #k`. -/
theorem count_sub {N i k : Nat} (hi : i < N) :
    BitVec.ofNat 32 (k * (N - i)) - BitVec.ofNat 32 k = BitVec.ofNat 32 (k * (N - (i + 1))) := by
  have : k * (N - i) = k * (N - (i + 1)) + k := by
    rw [show N - i = (N - (i + 1)) + 1 by omega, Nat.mul_succ]
  rw [this, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-! ## Symbolic execution -/

/-- Runs a straight-line block symbolically (see `WP.of_runBlock`), with the
facts `ls` about the registers and memory it reads. Read through register
writes without expanding the whole state at every step, then normalize the
final state once for the postcondition. -/
syntax "run_block " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| run_block [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
        Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.sp_setReg, RegUpd.z_setReg, RegUpd.n_setReg, RegUpd.c_setReg, RegUpd.v_setReg,
        State.load32, State.store32, State.load8, State.store8,
        subFlags, addFlags, ite_true, ite_false, Option.map_some, Option.some.injEq,
        exists_eq_left', List.cons_append, List.nil_append, List.append_nil, $ls,*]
      set_option linter.unusedSimpArgs false in
      all_goals try simp (config := {decide := true}) only [State.setReg, $ls,*]))

/-- Resolves the `if`s on indices whose ranges `omega` knows. -/
macro "resolve_ifs" : tactic => `(tactic| (
  set_option linter.unusedSimpArgs false in
  simp (disch := omega) only [ite_eq_left, ite_eq_right, ite_true, ite_false]))

/-! ## Addresses -/

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- A pointer `p + i`, plus the offset `o` of an instruction, without
wrapping around. -/
theorem addr_ptr (p : BitVec 32) (i o : Nat) (h : p.toNat + (i + o) < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 i + BitVec.ofNat 32 o) = State.addr p + BitVec.ofNat 64 (i + o) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact addr_add h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  exact h

theorem inRegions_of {rs : List Region} {R : Region} (hR : R ∈ rs) {a : Addr} {n : Nat}
    (h : R.Contains a n) : InRegions rs a n := ⟨R, hR, h⟩

/-- An access at offset `off` of a region in `rs`. -/
theorem inRegions_off {rs : List Region} {base : Addr} {len : Nat} (hR : ⟨base, len⟩ ∈ rs)
    {off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    InRegions rs (base + BitVec.ofNat 64 off) n :=
  ⟨_, hR, VG.Proof.MlKem.Arm.contains_off h ho⟩

theorem mem_append_left' {R : Region} {rs : List Region} (rd : List Region) (h : R ∈ rs) :
    R ∈ rd ++ rs := List.mem_append_right _ h

/-- A byte of a region disjoint from the regions written is unchanged. -/
theorem frame_byte {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {base : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨base, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) {i : Nat} (hi : i < len) :
    m' (base + BitVec.ofNat 64 i) = m (base + BitVec.ofNat 64 i) :=
  hf.bytes (R := ⟨base, len⟩) hd hlen hi

/-- A coefficient of a polynomial disjoint from the regions written is
unchanged. -/
theorem frame_coeff {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) {i : Nat} (hi : i < n) :
    coeffAt m' p i = coeffAt m p i :=
  coeffAt_congr (bytes_frame hf hd (by decide)) hi

/-- A pointer `p + i` plus an instruction's offset `o`, at coefficient `j`
of the polynomial at `p`. -/
theorem addr_coeff {p : BitVec 32} {i o j : Nat} (h : p.toNat + 1024 ≤ 2 ^ 32) (hj : i + o = 4 * j)
    (hjn : j < 256) :
    State.addr (p + BitVec.ofNat 32 i + BitVec.ofNat 32 o) = coeffAddr (State.addr p) j := by
  rw [VG.Proof.MlKem.Arm.addr_ptr _ _ _ (by omega), hj]

/-- A pointer `p + i` plus an instruction's offset `o`, at byte `k` of the
`len` bytes at `p`. -/
theorem addr_byte {p : BitVec 32} {i o k len : Nat} (h : p.toNat + len ≤ 2 ^ 32) (hk : i + o = k)
    (hkl : k < len) : State.addr (p + BitVec.ofNat 32 i + BitVec.ofNat 32 o) = State.addr p + BitVec.ofNat 64 k := by
  rw [VG.Proof.MlKem.Arm.addr_ptr _ _ _ (by omega), hk]

/-- The low byte of a word, as `strb` stores it. -/
theorem setWidth8 (v : BitVec 32) : v.setWidth 8 = BitVec.ofNat 8 v.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte zero-extended, as `ldrb` loads it. -/
theorem setWidth32_toNat (b : Byte) : (b.setWidth 32).toNat = b.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := b.isLt; omega)

/-- Byte `k` after writing byte `a`, of the bytes at `O`. -/
theorem byte_writeW8 (m : Mem) (O : Addr) {a k : Nat} (ha : a < 2 ^ 64) (hk : k < 2 ^ 64) (v : Byte) :
    (m.writeW (O + BitVec.ofNat 64 a) v) (O + BitVec.ofNat 64 k) =
      if k = a then v else m (O + BitVec.ofNat 64 k) := by
  rw [VG.WriteBytes.writeW8_apply]
  by_cases h : k = a
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right]
    intro e
    apply h
    have := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp e)
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt ha] at this

/-- Two writes of a byte at the same address: the second is what remains. -/
theorem writeW8_writeW8 (m : Mem) (a : Addr) (v w : Byte) : (m.writeW a v).writeW a w = m.writeW a w := by
  funext x
  rw [VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
  split <;> rfl

/-- A byte of a region disjoint from one written. -/
theorem byte_writeW_disj {m : Mem} {R S : Region} (hd : R.Disjoint S) {a x : Addr} {w : Nat}
    (v : BitVec w) (ha : S.Contains a (w / 8)) (hx : R.Contains x 1) : (m.writeW a v) x = m x :=
  Mem.write_apply fun h => hd x hx (ha.byte h)

/-- A word of a region disjoint from one written. -/
theorem readW_writeW_disj {m : Mem} {R S : Region} (hd : R.Disjoint S) {a x : Addr} {w : Nat}
    (v : BitVec w) (ha : S.Contains a (w / 8)) (hx : R.Contains x 4) :
    (m.writeW a v).readW x 32 = m.readW x 32 :=
  Mem.readW_writeW_sep (hd.sep hx ha) (by decide)

/-- The returned `u32` is the low word, `r0`, of the returned pair. -/
theorem setWidth_append32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega

/-- The next coefficient written, from an invariant saying which are. -/
theorem coeff_one {m m₀ : Mem} {F : Addr} {out : Nat → BitVec 32} {a : Nat} (ha : a < 256)
    (h : ∀ j < 256, coeffAt m F j = if j < a then out j else coeffAt m₀ F j) {v : BitVec 32}
    (hv : v = out a) :
    ∀ j < 256, coeffAt (m.writeW (coeffAddr F a) v) F j = if j < a + 1 then out j else coeffAt m₀ F j := by
  intro j hj
  rw [coeffAt_writeW _ _ (by rw [n_eq]; exact hj) (by rw [n_eq]; exact ha), h j hj]
  rcases (by omega : j < a ∨ j = a ∨ a < j) with h' | rfl | h'
  · resolve_ifs
  · rw [hv]; resolve_ifs
  · resolve_ifs

/-- The next byte written, from an invariant saying which are. -/
theorem byte_one {m m₀ : Mem} {O : Addr} {out : Nat → Byte} {a L : Nat} (ha : a < L)
    (hL : L < 2 ^ 64) (h : ∀ k < L, m (O + BitVec.ofNat 64 k) = if k < a then out k else m₀ (O + BitVec.ofNat 64 k))
    {v : Byte} (hv : v = out a) :
    ∀ k < L, (m.writeW (O + BitVec.ofNat 64 a) v) (O + BitVec.ofNat 64 k) =
      if k < a + 1 then out k else m₀ (O + BitVec.ofNat 64 k) := by
  intro k hk
  rw [VG.Proof.MlKem.Arm.byte_writeW8 _ _ (by omega) (by omega), h k hk]
  rcases (by omega : k < a ∨ k = a ∨ a < k) with h' | rfl | h'
  · resolve_ifs
  · rw [hv]; resolve_ifs
  · resolve_ifs

/-- `x - y` is zero exactly when `x = y`, as `cmp` computes it. -/
theorem sub_beq_zero (x y : BitVec 32) : (x - y == 0) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    exact h (by rw [← BitVec.sub_add_cancel x y, e]; simp)

/-- The flag `Z` of `cmp x, #k`. -/
theorem cmp_z (x : BitVec 32) (k : Nat) (hk : k < 2 ^ 32) :
    (x - BitVec.ofNat 32 k == 0) = decide (x.toNat = k) := by
  rw [VG.Proof.MlKem.Arm.sub_beq_zero]
  have : x = BitVec.ofNat 32 k ↔ x.toNat = k :=
    ⟨fun e => by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk],
      fun e => BitVec.eq_of_toNat_eq (by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk])⟩
  simp only [this]

/-! ## Reduction modulo `q` -/

/-- What `fixup` leaves: `u + q` if `u` is negative, `u` otherwise. -/
def fixq (u : BitVec 32) : BitVec 32 :=
  u + (u >>> 31) + ((u >>> 31) <<< 8) + ((u >>> 31) <<< 10) + ((u >>> 31) <<< 11)

theorem fixq_toNat {u : BitVec 32} (h : u.toNat < 3329 ∨ 2 ^ 32 - 3329 ≤ u.toNat) :
    (VG.Proof.MlKem.Arm.fixq u).toNat = if u.toNat < 3329 then u.toNat else u.toNat + 3329 - 2 ^ 32 := by
  unfold VG.Proof.MlKem.Arm.fixq
  split <;> bv_omega

/-- `fixq (a + b - q)`: the sum of reduced values, reduced. -/
theorem fixq_add {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlKem.Arm.fixq (a + b - 3328 - 1)).toNat = (a.toNat + b.toNat) % q := by
  rw [q_eq] at *
  rw [VG.Proof.MlKem.Arm.fixq_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixq (a - b)`: the difference of reduced values, reduced. -/
theorem fixq_sub {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlKem.Arm.fixq (a - b)).toNat = (a.toNat + q - b.toNat) % q := by
  rw [q_eq] at *
  rw [VG.Proof.MlKem.Arm.fixq_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixq (x - q)` of `x < 2q`: `x` reduced. -/
theorem fixq_subq {x : BitVec 32} (hx : x.toNat < 2 * q) : (VG.Proof.MlKem.Arm.fixq (x - 3328 - 1)).toNat = x.toNat % q := by
  rw [q_eq] at *
  rw [VG.Proof.MlKem.Arm.fixq_toNat (by bv_omega)]
  split <;> bv_omega

theorem fixq_lt {u : BitVec 32} (h : u.toNat < 3329 ∨ 2 ^ 32 - 3329 ≤ u.toNat) : (VG.Proof.MlKem.Arm.fixq u).toNat < q := by
  rw [VG.Proof.MlKem.Arm.fixq_toNat h, q_eq]; split <;> omega

/-- A word is the element of `ℤ_q` it represents, once reduced. -/
theorem ofNat_val_eq {v : BitVec 32} {x : Zq} (h : v.toNat = x.val) : v = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Add`. -/
section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_add` and `vg_mlkem_sub`

One symbolic execution of each loop body, for any pointers (`addBody_ok`,
`subBody_ok`); the loop invariant says which coefficients of `f` are done
(`Inv`); the arithmetic is `fixq_add` and `fixq_sub`.
-/

namespace VG.Proof.MlKem.Arm.Add

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem

/-! ## The loop bodies -/

/-- What an iteration of either loop does, but for the value stored. -/
def Step (s : State) (x y c v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = y + 4 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
    s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) v ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = c)
  (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
  (oa : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 ia ib oa

theorem addBody_ok :
    WP isa (.block addBody) s (VG.Proof.MlKem.Arm.Add.Step s x y c (VG.Proof.MlKem.Arm.fixq (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
      s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 - 3328 - 1))) := by
  run_block [addBody, subQ, fixup, accTail, VG.Proof.MlKem.Arm.Add.Step, VG.Proof.MlKem.Arm.fixq, h0, h1, h2, ia, ib, oa, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem subBody_ok :
    WP isa (.block subBody) s (VG.Proof.MlKem.Arm.Add.Step s x y c (VG.Proof.MlKem.Arm.fixq (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 -
      s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32))) := by
  run_block [subBody, fixup, accTail, VG.Proof.MlKem.Arm.Add.Step, VG.Proof.MlKem.Arm.fixq, h0, h1, h2, ia, ib, oa, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev pg : BitVec 32 := s₀.gpr .r1
abbrev F : Addr := State.addr (VG.Proof.MlKem.Arm.Add.pf s₀)
abbrev G : Addr := State.addr (VG.Proof.MlKem.Arm.Add.pg s₀)

end

/-- The precondition of both functions. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (VG.Proof.MlKem.Arm.Add.G s₀)]
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.Arm.Add.F s₀)]
  disj : (polyRegion (VG.Proof.MlKem.Arm.Add.F s₀)).Disjoint (polyRegion (VG.Proof.MlKem.Arm.Add.G s₀))
  fitF : (VG.Proof.MlKem.Arm.Add.pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitG : (VG.Proof.MlKem.Arm.Add.pg s₀).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s₀.mem (VG.Proof.MlKem.Arm.Add.F s₀)
  redG : Reduced s₀.mem (VG.Proof.MlKem.Arm.Add.G s₀)

/-- After `i` iterations, writing `out j` to coefficient `j`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.MlKem.Arm.Add.pf s₀ + BitVec.ofNat 32 (4 * i)
  r1 : s.gpr .r1 = VG.Proof.MlKem.Arm.Add.pg s₀ + BitVec.ofNat 32 (4 * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (VG.Proof.MlKem.Arm.Add.F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (VG.Proof.MlKem.Arm.Add.F s₀) j = if j < i then out j else coeffAt s₀.mem (VG.Proof.MlKem.Arm.Add.F s₀) j

theorem ptr_succ (p : BitVec 32) (k i : Nat) :
    p + BitVec.ofNat 32 (k * i) + BitVec.ofNat 32 k = p + BitVec.ofNat 32 (k * (i + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Add.Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : VG.Proof.MlKem.Arm.Add.Inv out s₀ i s) {body : List Instr}
    (hb : ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y → s.gpr .r2 = c →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block body) s (VG.Proof.MlKem.Arm.Add.Step s x y c (out i))) :
    WP isa (.block body) s fun s' => VG.Proof.MlKem.Arm.Add.Inv out s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  have fF := hp.fitF
  have fG := hp.fitG
  have eF : State.addr (VG.Proof.MlKem.Arm.Add.pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlKem.Arm.Add.F s₀) i :=
    VG.Proof.MlKem.Arm.addr_ptr _ _ _ (by omega)
  have eG : State.addr (VG.Proof.MlKem.Arm.Add.pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlKem.Arm.Add.G s₀) i :=
    VG.Proof.MlKem.Arm.addr_ptr _ _ _ (by omega)
  have cF := coeff_contains (VG.Proof.MlKem.Arm.Add.F s₀) (i := i) hi
  have cG := coeff_contains (VG.Proof.MlKem.Arm.Add.G s₀) (i := i) hi
  refine WP.mono (hb h.r0 h.r1 h.r2 ?_ ?_ ?_) fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, pres⟩ => ⟨⟨?_, ?_, ?_,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [eF, h.rd, h.wr, hp.rd, hp.wr]; exact VG.Proof.MlKem.Arm.inRegions_of (by simp) cF
  · rw [eG, h.rd, h.wr, hp.rd, hp.wr]; exact VG.Proof.MlKem.Arm.inRegions_of (by simp) cG
  · rw [eF, h.wr, hp.wr]; exact VG.Proof.MlKem.Arm.inRegions_of (by simp) cF
  · rw [r0]; exact VG.Proof.MlKem.Arm.Add.ptr_succ _ 4 i
  · rw [r1]; exact VG.Proof.MlKem.Arm.Add.ptr_succ _ 4 i
  · rw [r2]; exact VG.Proof.MlKem.Arm.count_sub (k := 1) hi
  · rw [m, eF]
    exact h.frame.writeW (List.mem_singleton_self _) _ cF
  · intro j hj
    rw [m, eF, coeffAt_writeW _ _ hj hi, h.coeff j hj]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij]
      by_cases hj' : j < i
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [z]; exact VG.Proof.MlKem.Arm.count_z (k := 1) hi (by decide) (by decide)

/-- The whole loop. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Add.Pre s₀) {body : List Instr}
    (hb : ∀ i < 256, ∀ s, VG.Proof.MlKem.Arm.Add.Inv out s₀ i s → ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y →
      s.gpr .r2 = c → InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block body) s (VG.Proof.MlKem.Arm.Add.Step s x y c (out i))) :
    WP isa (.seq (.block [.mov .r2 (.imm 256)]) (.loop (.block body) .ne)) s₀ (VG.Proof.MlKem.Arm.Add.Inv out s₀ 256) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), VG.Proof.MlKem.Arm.wp_loop_ne (VG.Proof.MlKem.Arm.Add.Inv out s₀) (N := 256) (by decide)
    (fun i hi s h => VG.Proof.MlKem.Arm.Add.inv_step hp hi h (hb i hi s h)) (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun j _ => rfl⟩
  simp only [State.setReg]
  rw [ite_eq_right]
  intro e; subst e; simp [preserved] at hr

/-! ## Correctness -/

/-- The value stored in coefficient `j` by `vg_mlkem_add`. -/
def addOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((add (polyAt s₀.mem (VG.Proof.MlKem.Arm.Add.F s₀)) (polyAt s₀.mem (VG.Proof.MlKem.Arm.Add.G s₀)))[j]!).val

/-- The value stored in coefficient `j` by `vg_mlkem_sub`. -/
def subOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((sub (polyAt s₀.mem (VG.Proof.MlKem.Arm.Add.F s₀)) (polyAt s₀.mem (VG.Proof.MlKem.Arm.Add.G s₀)))[j]!).val

/-- What an iteration reads: coefficient `i` of each polynomial, as on entry. -/
theorem reads {out : Nat → BitVec 32} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Add.Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : VG.Proof.MlKem.Arm.Add.Inv out s₀ i s) {x y : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) :
    s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlKem.Arm.Add.F s₀) i ∧
      s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlKem.Arm.Add.G s₀) i := by
  have fF := hp.fitF
  have fG := hp.fitG
  rw [← h0, ← h1, h.r0, h.r1, VG.Proof.MlKem.Arm.addr_ptr _ _ _ (by omega), VG.Proof.MlKem.Arm.addr_ptr _ _ _ (by omega)]
  refine ⟨?_, ?_⟩
  · show coeffAt s.mem (VG.Proof.MlKem.Arm.Add.F s₀) i = _
    rw [h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]
  · show coeffAt s.mem (VG.Proof.MlKem.Arm.Add.G s₀) i = _
    exact VG.Proof.MlKem.Arm.frame_coeff h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) hi

theorem add_hb {s₀ : State} (hp : VG.Proof.MlKem.Arm.Add.Pre s₀) : ∀ i < 256, ∀ s, VG.Proof.MlKem.Arm.Add.Inv (VG.Proof.MlKem.Arm.Add.addOut s₀) s₀ i s →
    ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y → s.gpr .r2 = c →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block addBody) s (VG.Proof.MlKem.Arm.Add.Step s x y c (VG.Proof.MlKem.Arm.Add.addOut s₀ i)) := by
  intro i hi s h x y c h0 h1 h2 ia ib oa
  obtain ⟨ea, eb⟩ := VG.Proof.MlKem.Arm.Add.reads hp hi h h0 h1
  refine WP.mono (VG.Proof.MlKem.Arm.Add.addBody_ok h0 h1 h2 ia ib oa) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = VG.Proof.MlKem.Arm.Add.addOut s₀ i) ▸ hs
  refine VG.Proof.MlKem.Arm.ofNat_val_eq ?_
  rw [VG.Proof.MlKem.Arm.fixq_add (hp.redF i hi) (hp.redG i hi), add_get _ _ hi, val_add', polyAt_val hp.redF hi,
    polyAt_val hp.redG hi]

theorem sub_hb {s₀ : State} (hp : VG.Proof.MlKem.Arm.Add.Pre s₀) : ∀ i < 256, ∀ s, VG.Proof.MlKem.Arm.Add.Inv (VG.Proof.MlKem.Arm.Add.subOut s₀) s₀ i s →
    ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y → s.gpr .r2 = c →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block subBody) s (VG.Proof.MlKem.Arm.Add.Step s x y c (VG.Proof.MlKem.Arm.Add.subOut s₀ i)) := by
  intro i hi s h x y c h0 h1 h2 ia ib oa
  obtain ⟨ea, eb⟩ := VG.Proof.MlKem.Arm.Add.reads hp hi h h0 h1
  refine WP.mono (VG.Proof.MlKem.Arm.Add.subBody_ok h0 h1 h2 ia ib oa) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = VG.Proof.MlKem.Arm.Add.subOut s₀ i) ▸ hs
  refine VG.Proof.MlKem.Arm.ofNat_val_eq ?_
  rw [VG.Proof.MlKem.Arm.fixq_sub (hp.redF i hi) (hp.redG i hi), sub_get _ _ hi, val_sub', polyAt_val hp.redF hi,
    polyAt_val hp.redG hi, Nat.add_sub_assoc (by have := hp.redG i hi; omega)]

/-- The loop's result: `f` is `out` of each coefficient. -/
theorem polyIs_of_inv {out : Nat → BitVec 32} {s₀ s : State} {g : Poly}
    (h : VG.Proof.MlKem.Arm.Add.Inv out s₀ 256 s) (hg : ∀ j < 256, out j = BitVec.ofNat 32 (g[j]!).val) :
    PolyIs s.mem (VG.Proof.MlKem.Arm.Add.F s₀) g :=
  polyIs_of_coeffAt fun j hj => by rw [h.coeff j hj, ite_eq_left hj, hg j hj]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.addContract Arm.abi).pre s) : VG.Proof.MlKem.Arm.Add.Pre s := by
  sig_pre [Spec.MlKem.addContract, Spec.MlKem.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem pre_of_sub {s : State} (h : (Spec.MlKem.subContract Arm.abi).pre s) : VG.Proof.MlKem.Arm.Add.Pre s := by
  sig_pre [Spec.MlKem.subContract, Spec.MlKem.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun i _ => by
  rw [coeffAt_eq]
  have : Mem.readW (fun _ => (0 : Byte)) (coeffAddr p i) 32 = 0 := by
    simp [Mem.readW, Mem.read]
  rw [this]; decide

/-- The taint analysis: only the pointers are public. -/
theorem ct {k : Contract isa} (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1)
    {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r0, .r1]) c hc).isSome = true) :
    ConstantTime isa k.pre k.pub c :=
  VG.Taint.constantTime (A := VG.Arm.taint) (Taint.ofRegs [.r0, .r1]) (fun s₁ s₂ _ _ hp => by
    obtain ⟨h0, h1⟩ := hpub s₁ s₂ hp
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption) h

/-- The taint analysis, with the registers `rs` public. -/
theorem ctRegs {k : Contract isa} (rs : List Reg)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    ConstantTime isa k.pre k.pub c :=
  VG.Taint.constantTime (A := VG.Arm.taint) (Taint.ofRegs rs)
    (fun s₁ s₂ _ _ hp => Taint.agree_ofRegs (hpub s₁ s₂ hp)) h

theorem add_verified : Verified Arm.target Impl.MlKem.Arm.add (Spec.MlKem.addContract Arm.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.Arm.Add.ct (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := VG.Proof.MlKem.Arm.Add.pre_of hs
    obtain ⟨t, s', he, h⟩ := VG.Proof.MlKem.Arm.Add.loop_ok hp (VG.Proof.MlKem.Arm.Add.add_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp⟩, ?_⟩
    sig_post [Spec.MlKem.addContract, Spec.MlKem.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact VG.Proof.MlKem.Arm.Add.polyIs_of_inv h fun j _ => rfl
  · sig_pub [Spec.MlKem.addContract, Spec.MlKem.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact ⟨h.2.1, h.2.2⟩
  · refine ⟨VG.Proof.MlKem.Arm.Add.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.addContract, Spec.MlKem.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlKem.Arm.Add.reduced_zero _
        | decide +kernel

theorem sub_verified : Verified Arm.target Impl.MlKem.Arm.sub (Spec.MlKem.subContract Arm.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.Arm.Add.ct (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := VG.Proof.MlKem.Arm.Add.pre_of_sub hs
    obtain ⟨t, s', he, h⟩ := VG.Proof.MlKem.Arm.Add.loop_ok hp (VG.Proof.MlKem.Arm.Add.sub_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp⟩, ?_⟩
    sig_post [Spec.MlKem.subContract, Spec.MlKem.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact VG.Proof.MlKem.Arm.Add.polyIs_of_inv h fun j _ => rfl
  · sig_pub [Spec.MlKem.subContract, Spec.MlKem.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact ⟨h.2.1, h.2.2⟩
  · refine ⟨VG.Proof.MlKem.Arm.Add.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.subContract, Spec.MlKem.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlKem.Arm.Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.Arm.Add

end
