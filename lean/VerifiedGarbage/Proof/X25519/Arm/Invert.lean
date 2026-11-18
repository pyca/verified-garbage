module

import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.X25519.Arm.Mul
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.X25519.Arm.Field

/-! ### `X25519.Arm.Cswap`, which this module and modules that import it used -/

section

/-!
# X25519 on 32-bit ARM: the conditional swap

`cswap x y` swaps the elements at `x` and `y` if the mask in `r9` is `-1` and
leaves them if it is `0` (`cswap_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm

theorem sel0 (a c : BitVec 32) : a ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 0)) = a := by simp

theorem sel0' (a c : BitVec 32) : c ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 0)) = c := by simp

theorem sel1 (a c : BitVec 32) : a ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 1)) = c := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem sel1' (a c : BitVec 32) : c ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 1)) = a := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

section
variable {e : Nat} {b : BitVec 32}

/-- While swapping `x` and `y` from `s0`, after `n` limbs. -/
structure SwapInv (b : BitVec 32) (x y sw : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3, .r4] s0 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 x, 4 * n⟩, ⟨State.addr b + BitVec.ofNat 64 y, 4 * n⟩]
    s0.mem s.mem
  lx : ∀ j < n, limb s.mem (State.addr b) x j =
    sel sw (limb s0.mem (State.addr b) x j) (limb s0.mem (State.addr b) y j)
  ly : ∀ j < n, limb s.mem (State.addr b) y j =
    sel sw (limb s0.mem (State.addr b) y j) (limb s0.mem (State.addr b) x j)

/-- The swap of the first `n` limbs. -/
theorem cswapN_ok {n x y : Nat} (hx : x + 4 * n ≤ 4096) (hy : y + 4 * n ≤ 4096)
    (hxy : x + 4 * n ≤ y ∨ y + 4 * n ≤ x)
    {s0 : State} (hc : CtxN e b s0) {sw : Nat} (hsw : sw ≤ 1) (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block ((List.range n).flatMap (cswapStep x y))) s0 (SwapInv b x y sw s0 n) := by
  refine wp_range_flatMap (M := isa) (SwapInv b x y sw s0) (fun k s hk h => ?_) n (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : CtxN e b s := hc.of_rest h.rest (by decide)
  have wx : wd s.mem (State.addr b) (x + 4 * k) = limb s0.mem (State.addr b) x k :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hx, hk]) (by omega_using [hx, hk])
      · exact Offset.disjoint _ (by omega_using [hxy, hk]) (by omega_using [hx, hk]) (by omega_using [hy, hk])
  have wy : wd s.mem (State.addr b) (y + 4 * k) = limb s0.mem (State.addr b) y k :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hxy, hk]) (by omega_using [hy, hk]) (by omega_using [hx, hk])
      · exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hy, hk]) (by omega_using [hy, hk])
  unfold cswapStep
  refine ldr0_ok hcs (d := x + 4 * k) (by omega_using [hx, hk]) fun t1 v1 => ?_
  refine ldr0_ok (hcs.of_rest (v1.rest (ws := [.r2]) (by decide)) (by decide)) (d := y + 4 * k) (by omega_using [hy, hk])
    fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 v5 => wp_dp (op2_reg _ _) fun t6 v6 => ?_
  have hr6 : Rest [.r2, .r3, .r4] s t6 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))))
  have hc6 : CtxN e b t6 := hcs.of_rest hr6 (by decide)
  refine str0_ok hc6 (d := x + 4 * k) (by omega_using [hx, hk]) fun t7 v7 => ?_
  refine str0_ok (hc6.of_rest (v7.rest []) (by decide)) (d := y + 4 * k) (by omega_using [hy, hk]) fun t8 v8 => ?_
  refine WP.block_nil ?_
  -- The values.
  have eX : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (x + 4 * k)) 32 := by
    rw [v2.other _ (by decide), v1.gpr]
  have eY : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (y + 4 * k)) 32 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h9]
  have e6x : t6.gpr .r2 = t2.gpr .r2 ^^^ ((t2.gpr .r2 ^^^ t2.gpr .r3) &&& (0 - BitVec.ofNat 32 sw)) := by
    rw [v6.other _ (by decide), v5.gpr, v4.other _ (by decide), v3.other _ (by decide), v4.gpr]
    show _ ^^^ (t3.gpr .r4 &&& t3.gpr .r9) = _
    rw [v3.gpr, em]; rfl
  have e6y : t6.gpr .r3 = t2.gpr .r3 ^^^ ((t2.gpr .r2 ^^^ t2.gpr .r3) &&& (0 - BitVec.ofNat 32 sw)) := by
    rw [v6.gpr, v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v5.other _ (by decide),
      v4.gpr]
    show _ ^^^ (t3.gpr .r4 &&& t3.gpr .r9) = _
    rw [v3.gpr, em]; rfl
  have hm8 : t8.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (x + 4 * k)) (t6.gpr .r2)).writeW
      (State.addr b + BitVec.ofNat 64 (y + 4 * k)) (t6.gpr .r3) := by
    rw [v8.mem, v7.gpr, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have vx : (t6.gpr .r2).toNat = sel sw (limb s0.mem (State.addr b) x k) (limb s0.mem (State.addr b) y k) := by
    rw [e6x, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0]; rfl
    · rw [sel1]; rfl
  have vy : (t6.gpr .r3).toNat = sel sw (limb s0.mem (State.addr b) y k) (limb s0.mem (State.addr b) x k) := by
    rw [e6y, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0']; rfl
    · rw [sel1']; rfl
  refine ⟨h.rest.trans (hr6.trans ((v7.rest _).trans (v8.rest _))), ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hm8]
    refine ((h.frame.sub fun r hr => ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hx, hk]))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hy, hk]))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega_using [])⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_using [])⟩
  · rw [limb, hm8, wd_write_other _ _ _ (by omega_using [hxy, hk, hj]) (by omega_using [hx, hk, hj]) (by omega_using [hy, hk])]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [hx, hk])]; exact h.lx j hj
    · rw [wd_write_self, vx]
  · rw [limb, hm8]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [hy, hk]),
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_using [hx, hk])]; exact h.ly j hj
    · rw [wd_write_self, vy]

theorem cswap_ok {x y : Nat} (hx : x + 64 ≤ 4096) (hy : y + 64 ≤ 4096) (hxy : x + 64 ≤ y ∨ y + 64 ≤ x)
    {s0 : State} (hc : CtxN e b s0) {sw : Nat} (hsw : sw ≤ 1) (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block (cswap x y)) s0 (SwapInv b x y sw s0 16) :=
  cswapN_ok (n := 16) hx hy hxy hc hsw h9

end

end VG.Proof.X25519.Arm

end

end

/-! ### `X25519.Arm.Slots`, which this module and modules that import it used -/

section

/-!
# X25519 on 32-bit ARM: the field elements the working space holds

`SlotsOk m B qs v`: each slot `q` of `qs` holds limbs below `2¹⁶` of the
element `v q`. The field operations as updates of `v` (`mulS`, `addS`, `subS`,
`cswapS`), for slots whose separation from the output is decided on their
offsets (`Sep1`), and writing only the field area `[64, acc + 128)` of the
working space (`FA`), for the product at any `acc` (X25519's `ACC` or
Ed25519's).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe)
open VG.Proof.X25519 (toFe toFe_mul toFe_add toFe_sub)

/-- Each slot `q` of `qs` holds limbs below `2¹⁶` of `v q`. -/
def SlotsOk (m : Mem) (B : Addr) (qs : List Nat) (v : Nat → Fe) : Prop :=
  ∀ q ∈ qs, Lim m B q ∧ FS m B q = v q

theorem SlotsOk.mono {m : Mem} {B : Addr} {qs qs' : List Nat} {v : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs', q ∈ qs) : SlotsOk m B qs' v := fun q hq => h q (hs q hq)

theorem SlotsOk.congr {m : Mem} {B : Addr} {qs : List Nat} {v w : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs, v q = w q) : SlotsOk m B qs w := fun q hq => ⟨(h q hq).1, (h q hq).2.trans (hs q hq)⟩

/-- `v` with the element `x` at `o`. -/
def upd (v : Nat → Fe) (o : Nat) (x : Fe) (q : Nat) : Fe := if q = o then x else v q

theorem upd_self (v : Nat → Fe) (o : Nat) (x : Fe) : upd v o x o = x := by simp [upd]

theorem upd_of_ne (v : Nat → Fe) {o q : Nat} (x : Fe) (h : q ≠ o) : upd v o x q = v q := by simp [upd, h]

/-- Every slot of `qs` is `o` or separate from it, and in `[64, acc)`. -/
def Sep1 (acc o : Nat) (qs : List Nat) : Bool :=
  qs.all fun q => (q == o || q + 64 ≤ o || o + 64 ≤ q) && 64 ≤ q && q + 64 ≤ acc

theorem sep1_get {acc o : Nat} {qs : List Nat} (h : Sep1 acc o qs = true) {q : Nat} (hq : q ∈ qs) :
    (q = o ∨ q + 64 ≤ o ∨ o + 64 ≤ q) ∧ 64 ≤ q ∧ q + 64 ≤ acc := by
  have := List.all_eq_true.mp h q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.elim (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h)),
    this.1.2, this.2⟩

/-- The field area `[64, acc + 128)` of the working space: the elements and
the product at `acc`. -/
abbrev FA (acc : Nat) (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 64, acc + 64⟩

section
variable {e acc : Nat} {b : BitVec 32}

/-- The slots of `qs` other than `o` after a write of `o` (and `acc`). -/
theorem slots_after (hA : acc + 128 ≤ 4096) {o : Nat} {qs : List Nat} (hq : Sep1 acc o qs = true)
    (ho : o + 64 ≤ acc) {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] m m')
    {v : Nat → Fe} (hS : SlotsOk m (State.addr b) qs v) {q : Nat} (hq' : q ∈ qs) (hqo : q ≠ o) :
    Lim m' (State.addr b) q ∧ FS m' (State.addr b) q = v q := by
  obtain ⟨h1, h2, h3⟩ := sep1_get hq hq'
  have e : ∀ k < 16, limb m' (State.addr b) q k = limb m (State.addr b) q k :=
    limb_frame hf fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hqo, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, ho])
      · exact Offset.disjoint _ (.inl (by omega_using [h3, hk])) (by omega_using [hA, h3, hk]) (by omega_using [hA])
  refine ⟨fun k hk => by rw [e k hk]; exact (hS q hq').1 k hk, ?_⟩
  rw [FS, V, val16_congr e]; exact (hS q hq').2

theorem frame_FA (_hA : acc + 128 ≤ 4096) {o : Nat} (ho : 64 ≤ o ∧ o + 64 ≤ acc) {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] m m') :
    Frame [FA acc b] m m' := by
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega_using [ho]) (by omega_arith)

/-- `mul o x y` is a multiplication with its product at `acc`: `mul_ok`'s
statement, which `mulAt acc` meets (`mulAt_mulOk`). -/
def MulOk (acc : Nat) (mul : Nat → Nat → Nat → Prog isa) : Prop :=
  ∀ {e : Nat} {b : BitVec 32} {o x y : Nat}, o + 64 ≤ acc → x + 64 ≤ acc → y + 64 ≤ acc →
    ∀ {s : State}, CtxN e b s → Lim s.mem (State.addr b) x → Lim s.mem (State.addr b) y →
    WP isa (mul o x y) s fun s' =>
      Rest clob s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] s.mem s'.mem ∧
      Lim s'.mem (State.addr b) o ∧
      V s'.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P

theorem mulAt_mulOk (hA : acc + 128 ≤ 4096) : MulOk acc (mulAt acc) :=
  fun ho hx hy _ hc hlx hly => mul_ok hA ho hx hy hc hlx hly

theorem mulS (hA : acc + 128 ≤ 4096) {M : Nat → Nat → Nat → Prog isa} (hM : MulOk acc M) {o x y : Nat}
    {qs : List Nat} {v : Nat → Fe} (hq : Sep1 acc o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ acc) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : CtxN e b s)
    (hS : SlotsOk s.mem (State.addr b) qs v) :
    WP isa (M o x y) s fun s' => Rest clob s s' ∧ Frame [FA acc b] s.mem s'.mem ∧
      SlotsOk s'.mem (State.addr b) (o :: qs) (upd v o (v x * v y)) := by
  refine WP.mono (hM ho.2 (sep1_get hq hx).2.2 (sep1_get hq hy).2.2 hc (hS x hx).1 (hS y hy).1)
    fun s' ⟨hr, hf, hl, hv⟩ => ⟨hr, frame_FA hA ho hf, fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    refine ⟨hl, ?_⟩
    rw [upd_self, ← (hS x hx).2, ← (hS y hy).2]
    exact toFe_mul hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hA hq ho.2 hf hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem frame_o {o : Nat} {m m' : Mem} (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] m m') :
    Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem addS (hA : acc + 128 ≤ 4096) {o x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : Sep1 acc o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ acc) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : CtxN e b s)
    (hS : SlotsOk s.mem (State.addr b) qs v) :
    WP isa (.block (add o x y)) s fun s' => Rest clob s s' ∧ Frame [FA acc b] s.mem s'.mem ∧
      SlotsOk s'.mem (State.addr b) (o :: qs) (upd v o (v x + v y)) := by
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  refine WP.mono (add_ok (by omega_using [hA, ho]) (by omega_using [hA, hx']) (by omega_using [hA, hy'])
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    hc (hS x hx).1 (hS y hy).1) fun s' ⟨hr, hf, hl, hv⟩ => ⟨hr, frame_FA hA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    refine ⟨hl, ?_⟩
    rw [upd_self, ← (hS x hx).2, ← (hS y hy).2]
    exact toFe_add hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hA hq ho.2 (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem subS (hA : acc + 128 ≤ 4096) {o x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : Sep1 acc o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ acc) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : CtxN e b s)
    (hS : SlotsOk s.mem (State.addr b) qs v) :
    WP isa (.block (sub o x y)) s fun s' => Rest clob s s' ∧ Frame [FA acc b] s.mem s'.mem ∧
      SlotsOk s'.mem (State.addr b) (o :: qs) (upd v o (v x - v y)) := by
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  refine WP.mono (sub_ok (by omega_using [hA, ho]) (by omega_using [hA, hx']) (by omega_using [hA, hy'])
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    hc (hS x hx).1 (hS y hy).1) fun s' ⟨hr, hf, hl, hv⟩ => ⟨hr, frame_FA hA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    refine ⟨hl, ?_⟩
    rw [upd_self, ← (hS x hx).2, ← (hS y hy).2]
    exact toFe_sub hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hA hq ho.2 (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

/-- The elements after swapping `x` and `y` if `sw = 1`. -/
def swapV (x y sw : Nat) (v : Nat → Fe) (q : Nat) : Fe :=
  if q = x then sel sw (v x) (v y) else if q = y then sel sw (v y) (v x) else v q

theorem cswapS (hA : acc + 128 ≤ 4096) {x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : Sep1 acc x qs = true) (hq' : Sep1 acc y qs = true)
    (hx : x ∈ qs) (hy : y ∈ qs) (hxy : x + 64 ≤ y ∨ y + 64 ≤ x) {s : State} (hc : CtxN e b s) {sw : Nat}
    (hsw : sw ≤ 1) (h9 : s.gpr .r9 = 0 - BitVec.ofNat 32 sw) (hS : SlotsOk s.mem (State.addr b) qs v) :
    WP isa (.block (cswap x y)) s fun s' => Rest [.r2, .r3, .r4] s s' ∧ Frame [FA acc b] s.mem s'.mem ∧
      SlotsOk s'.mem (State.addr b) qs (swapV x y sw v) := by
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  refine WP.mono (cswap_ok (b := b) (by omega_using [hA, hx']) (by omega_using [hA, hy']) hxy hc hsw h9) fun s' h => ⟨h.rest, ?_, ?_⟩
  · refine h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega_arith) (by omega_arith)
  · intro q hq''
    have hlx : ∀ k < 16, limb s'.mem (State.addr b) x k =
        sel sw (limb s.mem (State.addr b) x k) (limb s.mem (State.addr b) y k) := h.lx
    have hly : ∀ k < 16, limb s'.mem (State.addr b) y k =
        sel sw (limb s.mem (State.addr b) y k) (limb s.mem (State.addr b) x k) := h.ly
    by_cases hqx : q = x
    · subst hqx
      simp only [swapV, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) q k :=
          fun k hk => by rw [hlx k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS q hx).1 k hk, ?_⟩
        rw [FS, V, val16_congr e]; exact (hS q hx).2
      · have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) y k :=
          fun k hk => by rw [hlx k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS y hy).1 k hk, ?_⟩
        rw [FS, V, val16_congr e]; exact (hS y hy).2
    by_cases hqy : q = y
    · subst hqy
      simp only [swapV, hqx, ite_false, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) q k :=
          fun k hk => by rw [hly k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS q hy).1 k hk, ?_⟩
        rw [FS, V, val16_congr e]; exact (hS q hy).2
      · have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) x k :=
          fun k hk => by rw [hly k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS x hx).1 k hk, ?_⟩
        rw [FS, V, val16_congr e]; exact (hS x hx).2
    · simp only [swapV, hqx, hqy, ite_false]
      obtain ⟨h1, h2, h3⟩ := sep1_get hq hq''
      obtain ⟨h1', -, -⟩ := sep1_get hq' hq''
      have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) q k :=
        limb_frame h.frame fun r hr k hk => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (by omega_using [hqx, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, hx'])
          · exact Offset.disjoint _ (by omega_using [hqy, h1', hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, hy'])
      refine ⟨fun k hk => by rw [e k hk]; exact (hS q hq'').1 k hk, ?_⟩
      rw [FS, V, val16_congr e]; exact (hS q hq'').2

end

end VG.Proof.X25519.Arm

end

end

/-! ### `X25519.Arm.Ladder`, which this module and modules that import it used -/

section

/-!
# X25519 on 32-bit ARM: the ladder

One iteration of the ladder (`step_ok`) takes the elements `x1, x2, z2, x3,
z3, a24` from the state after the bits `254` down to `n` (`ladderAfter k x1
n`) to the state after `n - 1`, with the swap in `r10` and the counter in
`r11`; the loop (`ladder_ok`) runs it for the bits 254 down to 0.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe Ladder ladderStep cswap a24)
open VG.Proof.X25519 (toFe ladderAfter ladderAfter_step ladderStep_eq bit bit_le ladderAfter_swap_le)

/-- `s'` is `s` but for the registers `r1`–`r11`, the flags and the field
area. -/
structure Stp (b : BitVec 32) (s s' : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s'
  frame : Frame [FA ACC b] s.mem s'.mem

theorem Stp.refl (b : BitVec 32) (s : State) : Stp b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Stp.trans {b : BitVec 32} {s₁ s₂ s₃ : State} (h₁ : Stp b s₁ s₂) (h₂ : Stp b s₂ s₃) : Stp b s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₁.frame.trans h₂.frame⟩

theorem Stp.of_rest {b : BitVec 32} {s s' : State} {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ [Reg.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11])
    (hm : s'.mem = s.mem) : Stp b s s' := ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

/-- Between field operations, from `s0`: `r10` and `r11` hold `a` and `c`,
and the slots `qs` the elements `v`. -/
structure Cur (b : BitVec 32) (s0 : State) (a c : BitVec 32) (qs : List Nat) (v : Nat → Fe) (s : State) :
    Prop where
  ctx : Ctx b s
  stp : Stp b s0 s
  r10 : s.gpr .r10 = a
  r11 : s.gpr .r11 = c
  slots : SlotsOk s.mem (State.addr b) qs v

section
variable {b : BitVec 32} {s0 : State} {a c : BitVec 32} {qs : List Nat} {v : Nat → Fe}

theorem Cur.next {s s' : State} (h : Cur b s0 a c qs v s) (hr : Rest clob s s')
    (hf : Frame [FA ACC b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : SlotsOk s'.mem (State.addr b) qs' v') : Cur b s0 a c qs' v' s' :=
  ⟨h.ctx.of_rest hr (by decide), h.stp.trans ⟨hr.mono (by decide), hf⟩,
    by rw [hr.gpr _ (by decide), h.r10], by rw [hr.gpr _ (by decide), h.r11], hS⟩

theorem opMul {M : Nat → Nat → Nat → Prog isa} (hM : MulOk ACC M) {o x y : Nat} (hq : Sep1 ACC o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (M o x y) s (Cur b s0 a c (o :: qs) (upd v o (v x * v y))) :=
  WP.mono (mulS (by decide) hM hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

theorem opAdd {o x y : Nat} (hq : Sep1 ACC o qs = true) (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (add o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x + v y))) :=
  WP.mono (addS (by decide) hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

theorem opSub {o x y : Nat} (hq : Sep1 ACC o qs = true) (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (sub o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x - v y))) :=
  WP.mono (subS (by decide) hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

end

/-! ## Sequences of field operations -/

/-- A field operation: `o = x · y`, `x + y` or `x - y`. -/
inductive FOp
  | mul (o x y : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)

/-- The code of an operation, with the multiplication `M`. -/
def FOp.code (M : Nat → Nat → Nat → Prog isa) : FOp → Prog isa
  | .mul o x y => M o x y
  | .add o x y => .block (Impl.X25519.Arm.add o x y)
  | .sub o x y => .block (Impl.X25519.Arm.sub o x y)

def FOp.out : FOp → Nat
  | .mul o _ _ | .add o _ _ | .sub o _ _ => o

def FOp.x : FOp → Nat
  | .mul _ x _ | .add _ x _ | .sub _ x _ => x

def FOp.y : FOp → Nat
  | .mul _ _ y | .add _ _ y | .sub _ _ y => y

def FOp.val : FOp → (Nat → Fe) → Fe
  | .mul _ x y, v => v x * v y
  | .add _ x y, v => v x + v y
  | .sub _ x y, v => v x - v y

/-- The operations `ops`, then `k`. -/
def opsCode (M : Nat → Nat → Nat → Prog isa) : List FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq (op.code M) (opsCode M ops k)

/-- Each operation's slots are separate or equal, below `ACC`, and its inputs
known. -/
def opsOk : List FOp → List Nat → Bool
  | [], _ => true
  | op :: ops, qs => Sep1 ACC op.out qs && 64 ≤ op.out && op.out + 64 ≤ ACC && qs.contains op.x &&
      qs.contains op.y && opsOk ops (op.out :: qs)

/-- The elements after the operations. -/
def runOps : List FOp → (Nat → Fe) → Nat → Fe
  | [], v => v
  | op :: ops, v => runOps ops (upd v op.out (op.val v))

/-- The slots known after the operations. -/
def outsQ : List FOp → List Nat → List Nat
  | [], qs => qs
  | op :: ops, qs => outsQ ops (op.out :: qs)

theorem op_ok {M : Nat → Nat → Nat → Prog isa} (hM : MulOk ACC M) {b : BitVec 32} {s0 : State}
    {a c : BitVec 32} {qs : List Nat} {v : Nat → Fe} (op : FOp)
    (hq : Sep1 ACC op.out qs = true) (ho : 64 ≤ op.out ∧ op.out + 64 ≤ ACC) (hx : op.x ∈ qs) (hy : op.y ∈ qs)
    {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (op.code M) s (Cur b s0 a c (op.out :: qs) (upd v op.out (op.val v))) := by
  cases op with
  | mul o x y => exact opMul hM hq ho hx hy h
  | add o x y => exact opAdd hq ho hx hy h
  | sub o x y => exact opSub hq ho hx hy h

theorem ops_ok {M : Nat → Nat → Nat → Prog isa} (hM : MulOk ACC M) {b : BitVec 32} {s0 : State}
    {a c : BitVec 32} {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs = true →
      Cur b s0 a c qs v s → (∀ s', Cur b s0 a c (outsQ ops qs) (runOps ops v) s' → WP isa k s' Q) →
      WP isa (opsCode M ops k) s Q
  | [], _, _, s, _, h, hk => hk s h
  | op :: ops, qs, v, s, hok, h, hk => by
    simp only [opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
    exact WP.seq (WP.mono (op_ok hM op h1 ⟨h2, h3⟩ h4 h5 h) fun s' h' => ops_ok hM ops _ _ s' h6 h' hk)

/-! ## One iteration -/

/-- The field operations of an iteration, after the swaps. -/
def ladOps : List FOp :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB, .add C X3 Z3, .sub D X3 Z3,
    .mul DA D A, .mul CB C B, .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3,
    .mul Z3 X1 Z3, .mul X2 AA BB, .mul Z2 A24 E, .add Z2 AA Z2, .mul Z2 E Z2]

/-- The slots the ladder's state lives in. -/
def LQ : List Nat := [X1, X2, Z2, X3, Z3, A24]

theorem ladOps_ok : opsOk ladOps LQ = true := by decide

/-- The elements of the ladder's state `st`, and `x1` and `a24`. -/
def ladV (x1 : Fe) (st : Ladder) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then st.x2 else if q = Z2 then st.z2 else if q = X3 then st.x3
  else if q = Z3 then st.z3 else a24

theorem cswap_fst (sw : Nat) (x y : Fe) : (Spec.X25519.cswap sw x y).1 = sel sw x y := by
  unfold Spec.X25519.cswap sel; split <;> rfl

theorem cswap_snd (sw : Nat) (x y : Fe) : (Spec.X25519.cswap sw x y).2 = sel sw y x := by
  unfold Spec.X25519.cswap sel; split <;> rfl

/-- The elements after an iteration. -/
theorem ladOps_vals (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ∀ q ∈ LQ, runOps ladOps (swapV Z2 Z3 (st.swap ^^^ bit k t) (swapV X2 X3 (st.swap ^^^ bit k t)
      (ladV x1 st))) q = ladV x1 (ladderStep k x1 st t) q := by
  intro q hq
  rw [ladderStep_eq]
  simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ladOps, runOps, FOp.out, FOp.val, upd, swapV, ladV, cswap_fst, cswap_snd, X1, X2, Z2, X3,
      Z3, A, B, C, D, AA, BB, E, DA, CB, A24, Nat.reduceEqDiff, ↓reduceIte]

theorem ofNat_xor {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    BitVec.ofNat 32 x ^^^ BitVec.ofNat 32 y = BitVec.ofNat 32 (x ^^^ y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_imm hx, toNat_imm hy, toNat_imm (Nat.xor_lt_two_pow hx hy)]

theorem xor_le_one {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

theorem ea2 {b : BitVec 32} (hfit : b.toNat + 4096 ≤ 2 ^ 32) {x d : Nat} (h : x + d < 4096) :
    State.addr (b + BitVec.ofNat 32 x + BitVec.ofNat 32 d) = State.addr b + BitVec.ofNat 64 (x + d) := by
  rw [Offset.add_add]; exact addr_add (by omega_arith)

/-- The loop invariant of the ladder from `sL`, before the iteration for the
bit `n - 1`. -/
structure LadInv (b : BitVec 32) (k : Nat) (x1 : Fe) (sL : State) (n : Nat) (s : State) : Prop where
  cur : Cur b sL (BitVec.ofNat 32 (ladderAfter k x1 n).swap) (BitVec.ofNat 32 n) LQ
    (ladV x1 (ladderAfter k x1 n)) s

/-- The bits of the scalar in `BITS`. -/
def Bits (b : BitVec 32) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 255, m (State.addr b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (bit k t)

theorem head_ok {b : BitVec 32} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa (.block stepHead) s (Cur b sL (BitVec.ofNat 32 (bit k (n - 1))) (BitVec.ofNat 32 (n - 1)) LQ
      (swapV Z2 Z3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1))
        (swapV X2 X3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) (ladV x1 (ladderAfter k x1 n))))) := by
  obtain ⟨hcur⟩ := h
  have hc := hcur.ctx
  have hfit := hc.fit
  have hB : BITS = 1280 := rfl
  obtain hsw := ladderAfter_swap_le k x1 hn'
  obtain hbt := bit_le k (n - 1)
  obtain hx := xor_le_one hsw hbt
  simp only [stepHead, mask, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  obtain e11 : s1.gpr .r11 = BitVec.ofNat 32 (n - 1) := by
    rw [u1.gpr]; show s.gpr .r11 - 1 = _
    rw [hcur.r11]
    apply BitVec.eq_of_toNat_eq
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [toNat_sub_le (by rw [toNat_imm (by omega_arith), t1]; omega_arith), toNat_imm (by omega_arith), toNat_imm (by omega_arith), t1]
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (n - 1 + BITS)) (by decide)
    (by rw [u2.gpr]; show State.addr (s1.gpr .r0 + s1.gpr .r11 + _) = _
        rw [e11, u1.other _ (by decide), hc.r0, ea2 hfit (by omega_arith)])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s3 u3 => ?_
  obtain e1 : s3.gpr .r1 = BitVec.ofNat 32 (bit k (n - 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, hcur.stp.frame _ fun r hr => ?_, Nat.add_comm, hbits _ (by omega_arith)]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, toNat_imm (by omega_arith)]; omega_arith
    · rw [List.mem_singleton.mp hr]
      exact fun h => by
        simp only [Region.Contains] at h
        rw [Offset.sub_toNat _ (by omega_arith) (by omega_arith)] at h
        have := ACC_eq
        omega_arith
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  obtain e10 : s4.gpr .r10 = BitVec.ofNat 32 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u4.gpr]; show s3.gpr .r10 ^^^ s3.gpr .r1 = _
    rw [e1, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hcur.r10,
      ofNat_xor (by omega_arith) (by omega_arith)]
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => wp_dp (op2_reg _ _) fun s6 u6 => ?_
  obtain e9 : s6.gpr .r9 = 0 - BitVec.ofNat 32 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u6.gpr]; show s5.gpr .r9 - s5.gpr .r10 = _
    rw [u5.gpr, u5.other _ (by decide), e10]
  obtain hr6 : Rest [.r1, .r9, .r10, .r11] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  obtain hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain hc6 : Ctx b s6 := hc.of_rest hr6 (by decide)
  obtain hS6 : SlotsOk s6.mem (State.addr b) LQ (ladV x1 (ladderAfter k x1 n)) := by
    rw [hm6]; exact hcur.slots
  refine WP.append (cswapS (acc := ACC) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc6 hx e9 hS6)
    fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  obtain hc7 : Ctx b s7 := hc6.of_rest hr7 (by decide)
  refine WP.append (cswapS (acc := ACC) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc7 hx
    (by rw [hr7.gpr _ (by decide), e9]) hS7) fun s8 ⟨hr8, hf8, hS8⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s9 u9 => WP.block_nil ?_
  obtain hr9 : Rest [.r1, .r2, .r3, .r4, .r9, .r10, .r11] s s9 :=
    (hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
      (u9.rest (by decide))))
  exact ⟨hc.of_rest hr9 (by decide),
    hcur.stp.trans ⟨hr9.mono (by decide), by rw [u9.mem, ← hm6]; exact hf7.trans hf8⟩,
    by rw [u9.gpr, hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), e1],
    by rw [u9.other _ (by decide), hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e11],
    by rw [u9.mem]; exact hS8⟩

theorem sub0 (x : BitVec 32) : x - 0 = x := by simp

theorem step_eq (M : Nat → Nat → Nat → Prog isa) :
    stepWith M = .seq (.block stepHead) (opsCode M ladOps (.block [.cmp .r11 (.imm 0)])) := rfl

section
variable {M : Nat → Nat → Nat → Prog isa} (hM : MulOk ACC M)
include hM

theorem step_ok {b : BitVec 32} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa (stepWith M) s fun s' => LadInv b k x1 sL (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  rw [step_eq]
  refine WP.seq (WP.mono (head_ok hbits hn hn' h) fun s1 h1 =>
    ops_ok hM ladOps LQ _ s1 ladOps_ok h1 fun s2 h2 => ?_)
  refine wp_cmp (op2_imm (by decide)) fun s3 u3 hz => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h2.ctx.of_rest (u3.rest []) (by decide)
  · exact h2.stp.trans (Stp.of_rest (u3.rest []) (by decide) u3.mem)
  · rw [u3.gpr, h2.r10, ladderAfter_step k x1 (show n - 1 < 255 by omega_arith), Nat.sub_add_cancel hn,
      ladderStep_eq]
  · rw [u3.gpr, h2.r11]
  · rw [u3.mem]
    refine (h2.slots.mono (by decide)).congr fun q hq => ?_
    rw [ladderAfter_step k x1 (show n - 1 < 255 by omega_arith), Nat.sub_add_cancel hn]
    exact ladOps_vals k x1 _ (n - 1) q hq
  · rw [hz, h2.r11, sub0, ofNat_beq_zero (by omega_arith)]

/-- The ladder, from the state with the bits of the scalar in `BITS` and the
initial elements in `LQ`. -/
theorem ladder_ok {b : BitVec 32} {k : Nat} {x1 : Fe} {s : State} (hc : Ctx b s) (hbits : Bits b k s.mem)
    (hS : SlotsOk s.mem (State.addr b) LQ (ladV x1 (VG.Proof.X25519.init x1))) :
    WP isa (ladderWith M) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      s'.gpr .r10 = BitVec.ofNat 32 (ladderAfter k x1 0).swap ∧
      SlotsOk s'.mem (State.addr b) LQ (ladV x1 (ladderAfter k x1 0)) := by
  unfold ladderWith
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 =>
    WP.block_nil ?_)
  obtain hr2 : Rest [.r10, .r11] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain hbits2 : Bits b k s2.mem := by rw [hm2]; exact hbits
  obtain h255 : LadInv b k x1 s2 255 s2 :=
    ⟨⟨hc.of_rest hr2 (by decide), Stp.refl _ _, by rw [u2.gpr]; rfl,
      by rw [u2.other _ (by decide), u1.gpr]; rfl, by rw [hm2]; exact hS⟩⟩
  obtain hst : Stp b s s2 := Stp.of_rest hr2 (by decide) hm2
  refine WP.mono (Q := LadInv b k x1 s2 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ LadInv b k x1 s2 m s') ?_ 255 s2 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨hst.trans h'.stp, h'.ctx, h'.r10, h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (step_ok hM hbits2 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, hl'⟩

end

end VG.Proof.X25519.Arm

end

end

/-!
# X25519 on 32-bit ARM: the inversion

`invert` computes `z^(p-2)` into `R` for the element `z` at `Z2` by
square-and-multiply over the bits of `p - 2` from 254 down to 0 (`invert_ok`):
after the bits down to `n`, `R` holds `z^((p - 2) >> n)`.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe)

/-! ## The bits of `p - 2` -/

def pbitsB : Nat → Bool
  | 0 => true
  | t + 1 => ((P - 2) >>> t % 2 == if t = 4 ∨ t = 2 then 0 else 1) && pbitsB t

theorem pbitsB_ok : pbitsB 255 = true := by decide +kernel

/-- Every bit of `p - 2 = 2²⁵⁵ - 21` but bits 4 and 2 (and those from 255 up) is 1. -/
theorem pbits : ∀ t < 255, (P - 2) >>> t % 2 = if t = 4 ∨ t = 2 then 0 else 1 := by
  have : ∀ n, pbitsB n = true → ∀ t < n, (P - 2) >>> t % 2 = if t = 4 ∨ t = 2 then 0 else 1 := by
    intro n; induction n with
    | zero => intro _ t ht; omega_using [ht]
    | succ n ih =>
      intro h t ht
      simp only [pbitsB, Bool.and_eq_true, beq_iff_eq] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact ih h.2 t ht
      · exact h.1
  exact this 255 pbitsB_ok

theorem p255 : (P - 2) >>> 255 = 0 := by decide +kernel

theorem iteT {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem shr_step (x t : Nat) : x >>> t = 2 * (x >>> (t + 1)) + x >>> t % 2 := by
  rw [Nat.shiftRight_succ]; omega_using []

/-! ## Stores of a register -/

section
variable {b : BitVec 32}

/-- Stores of register `r` into the `n` words from `o`. -/
theorem stores_ok {r : Reg} {o n : Nat} (ho : o + 4 * n ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block (storeN r o n)) s fun s' =>
      (∀ j < n, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  unfold storeN
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun m s' => (∀ j < m, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * m⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun m s' hm ⟨h1, h2, h3, h4⟩ => ?_) n (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩) fun s' h => h
  refine str0_ok (hc.of_rest h4 (by decide)) (d := o + 4 * m) (by omega_using [ho, hm]) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, by rw [u2.gpr, h3], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [ho, hm])]; exact h1 j hj
    · rw [wd_write_self, h3]
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho, hm]))

/-! ## The inversion -/

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]

/-- `z^((p - 2) >> n)` in `R`, for `z` at `Z2`. -/
def invV (v : Nat → Fe) (n : Nat) : Nat → Fe := upd v R (VG.Proof.X25519.pw (v Z2) ((P - 2) >>> n))

/-- The loop invariant of the inversion from `sI`, before the step for the bit
`n - 1`. -/
structure InvInv (b : BitVec 32) (sI : State) (c : BitVec 32) (v : Nat → Fe) (n : Nat) (s : State) :
    Prop where
  cur : Cur b sI (BitVec.ofNat 32 n) c IQ (invV v n) s

theorem sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    obtain e : BitVec.ofNat 32 x = BitVec.ofNat 32 y := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 32 x) (BitVec.ofNat 32 y), h']; simp
    have := congrArg BitVec.toNat e
    rwa [toNat_imm hx, toNat_imm hy] at this

theorem Cur.congr {s0 s : State} {a c : BitVec 32} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : Cur b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.r10, h.r11, (h.slots.mono hq).congr hv⟩

section
variable {M : Nat → Nat → Nat → Prog isa} (hM : MulOk ACC M)
include hM

theorem invStep_ok {sI : State} {c : BitVec 32} {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255)
    {s : State} (h : InvInv b sI c v n s) :
    WP isa (invStepWith M) s fun s' => InvInv b sI c v (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  obtain ⟨hcur⟩ := h
  obtain hb := pbits (n - 1) (by omega_using [hn'])
  obtain he := shr_step (P - 2) (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold invStepWith
  refine WP.seq (wp_dp (op2_imm (by decide)) fun s1 u1 => WP.block_nil ?_)
  obtain h1 : Cur b sI (BitVec.ofNat 32 (n - 1)) c IQ (invV v n) s1 := by
    refine ⟨hcur.ctx.of_rest (u1.rest (ws := [.r10]) (by decide)) (by decide),
      hcur.stp.trans (Stp.of_rest (u1.rest (ws := [.r10]) (by decide)) (by decide) u1.mem), ?_,
      by rw [u1.other _ (by decide), hcur.r11], by rw [u1.mem]; exact hcur.slots⟩
    rw [u1.gpr]; show s.gpr .r10 - 1 = _
    rw [hcur.r10]
    apply BitVec.eq_of_toNat_eq
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [toNat_sub_le (by rw [toNat_imm (by omega_using [hn']), t1]; omega_using [hn]), toNat_imm (by omega_using [hn']), toNat_imm (by omega_using [hn']), t1]
  refine WP.seq (WP.mono (opMul hM (o := R) (x := R) (y := R) (by decide) (by decide) (by decide) (by decide) h1)
    fun s2 h2 => ?_)
  -- After the square.
  obtain hsq : ∀ q ∈ IQ, upd (invV v n) R (invV v n R * invV v n R) q =
      upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, upd_self, Nat.two_mul, ← VG.Proof.X25519.pw_mul]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq, upd_of_ne _ _ hq]
  obtain h2' := h2.congr (qs' := IQ) (by decide) hsq
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s3 u3 hz3 => WP.block_nil ?_)
  obtain h3 := h2'.next (Fupd.rest u3 _) (by rw [u3.mem]; exact Frame.refl _ _) (by rw [u3.mem]; exact h2'.slots)
  obtain hz3' : s3.z = decide (n - 1 = 4) := by
    rw [hz3, h2'.r10]; exact sub_beq (by omega_using [hn']) (by decide)
  refine WP.seq (WP.mono (Q := Cur b sI (BitVec.ofNat 32 (n - 1)) c IQ (invV v (n - 1))) ?_ fun s4 h4 =>
    wp_cmp (op2_imm (by decide)) fun s5 u5 hz5 => WP.block_nil ⟨⟨h4.next (Fupd.rest u5 _)
      (by rw [u5.mem]; exact Frame.refl _ _) (by rw [u5.mem]; exact h4.slots)⟩, ?_⟩)
  · refine WP.ite s3.z (eval_eq _) (fun ht => WP.block_nil (h3.congr (fun q hq => hq) fun q _ => ?_))
      (fun hf => ?_)
    · have h4 : n - 1 = 4 := by rw [hz3'] at ht; simpa using ht
      by_cases hq : q = R
      · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inl h4), Nat.add_zero]
      · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
    · have h4 : n - 1 ≠ 4 := by rw [hz3'] at hf; simpa using hf
      refine WP.seq (wp_cmp (op2_imm (by decide)) fun s4 u4 hz4 => WP.block_nil ?_)
      obtain h4' := h3.next (Fupd.rest u4 _) (by rw [u4.mem]; exact Frame.refl _ _) (by rw [u4.mem]; exact h3.slots)
      obtain hz4' : s4.z = decide (n - 1 = 2) := by
        rw [hz4, h3.r10]; exact sub_beq (by omega_using [hn']) (by decide)
      refine WP.ite s4.z (eval_eq _) (fun ht => WP.block_nil (h4'.congr (fun q hq => hq) fun q _ => ?_))
        (fun hf => ?_)
      · have h2 : n - 1 = 2 := by rw [hz4'] at ht; simpa using ht
        by_cases hq : q = R
        · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inr h2), Nat.add_zero]
        · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
      · have h2 : n - 1 ≠ 2 := by rw [hz4'] at hf; simpa using hf
        refine WP.mono (opMul hM (o := R) (x := R) (y := Z2) (by decide) (by decide) (by decide) (by decide) h4')
          fun s5 h5 => h5.congr (by decide) fun q _ => ?_
        by_cases hq : q = R
        · subst hq
          rw [upd_self, upd_self, upd_of_ne _ _ (by decide : Z2 ≠ R), invV, upd_self, he, hb,
            iteF (show ¬ (n - 1 = 4 ∨ n - 1 = 2) by omega_using [h4, h2]), ← VG.Proof.X25519.pw_mul,
            VG.Proof.X25519.pw_one]
        · rw [upd_of_ne _ _ hq, upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
  · rw [hz5, h4.r10]; exact sub_beq (by omega_using [hn']) (by decide)

theorem invert_ok {c : BitVec 32} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem (State.addr b) [Z2, X2] v) (h11 : s.gpr .r11 = c) :
    WP isa (invertWith M) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem (State.addr b) IQ (upd v R (VG.Proof.X25519.pw (v Z2) (P - 2))) := by
  unfold invertWith
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  obtain hr2 : Rest [.r1, .r2] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine str0_ok hc2 (d := R) (by decide) fun s3 u3 => ?_
  refine WP.append (stores_ok (o := R + 4) (n := 15) (by decide) (hc2.of_rest (u3.rest []) (by decide)))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => WP.block_nil ?_
  obtain hr5 : Rest [.r1, .r2, .r10] s s5 :=
    (hr2.mono (by decide)).trans ((u3.rest _).trans ((h4r.mono (by decide)).trans (u5.rest (by decide))))
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  -- The limbs of `R`: 1, then zeros.
  obtain hlimb : ∀ k < 16, limb s5.mem (State.addr b) R k = if k = 0 then 1 else 0 := by
    intro k hk
    rw [limb, u5.mem]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega_using [hk])
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega_using [hk0], u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega_using [hk0], ite_false]; rfl
  obtain hf5 : Frame [⟨State.addr b + BitVec.ofNat 64 R, 64⟩] s.mem s5.mem := by
    rw [u5.mem, ← hm2]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s2.gpr .r1)
      (Offset.contains (State.addr b) (d := R) (n := 4) (e := R) (k := 64) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  obtain hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  obtain hst5 : Stp b s s5 := ⟨hr5.mono (by decide), hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩⟩
  obtain hS5 : SlotsOk s5.mem (State.addr b) IQ (invV v 255) := by
    have hZ2 : Z2 = 192 := rfl
    have hX2 : X2 = 128 := rfl
    have hR : R = 1024 := rfl
    intro q hq
    simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · have e := limb_frame (o := Z2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hZ2, hR, hk])) (by omega_using [hZ2, hk]) (by omega_using [hR])
      refine ⟨fun k hk => by rw [e k hk]; exact (hS Z2 (by decide)).1 k hk, ?_⟩
      rw [FS, V, val16_congr e, invV, upd_of_ne _ _ (by decide)]; exact (hS Z2 (by decide)).2
    · refine ⟨fun k hk => by rw [hlimb k hk]; split <;> decide, ?_⟩
      rw [FS, V, val16_congr hlimb, invV, upd_self, p255, VG.Proof.X25519.pw_zero]
      rfl
    · have e := limb_frame (o := X2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX2, hR, hk])) (by omega_using [hX2, hk]) (by omega_using [hR])
      refine ⟨fun k hk => by rw [e k hk]; exact (hS X2 (by decide)).1 k hk, ?_⟩
      rw [FS, V, val16_congr e, invV, upd_of_ne _ _ (by decide)]; exact (hS X2 (by decide)).2
  obtain h255 : InvInv b s5 c v 255 s5 :=
    ⟨⟨hc5, Stp.refl _ _, u5.gpr, by rw [hr5.gpr _ (by decide), h11], hS5⟩⟩
  refine WP.mono (Q := InvInv b s5 c v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ InvInv b s5 c v m s') ?_ 255 s5 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨hst5.trans h'.stp, h'.ctx, h'.slots.congr fun q _ => by
      simp only [invV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (invStep_ok hM h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega_using [hm], by omega_using [hm], by omega_using [h2], hl'⟩

end

end

end VG.Proof.X25519.Arm
