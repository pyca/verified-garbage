module

public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X25519.RISCV64.Pass

/-!
# Ed448's verification on RISCV64: the checks

The context of the function's body (`VCtx`: X448's, the whole working space
but the 8 bytes rounding may skip writable, and `a0` at `OUT`), the doubleword `BAD` the checks
accumulate (`bad`, `orBad_ok`), and the ORs of the words at `OUT`
(`outOr_ok`) and of their differences from the words at `p` (`outSame_ok`),
which are 0 exactly when the element there is 0 or the same (`orw_eq_zero`,
`val32_inj`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519

/-! ## Words -/

/-- The OR of `f 0`, …, `f (n - 1)`. -/
def orw (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => orw f n ||| f n

theorem orw_lt {f : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k < 2 ^ 32) → orw f n < 2 ^ 32
  | 0, _ => Nat.two_pow_pos 32
  | n + 1, h => Nat.or_lt_two_pow (orw_lt fun k hk => h k (by omega)) (h n (by omega))

theorem orw_eq_zero {f : Nat → Nat} : ∀ {n : Nat}, orw f n = 0 ↔ ∀ k < n, f k = 0
  | 0 => by simp [orw]
  | n + 1 => by
    rw [orw, Nat.or_eq_zero_iff, orw_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem val32_eq_zero {f : Nat → Nat} : ∀ {n : Nat}, val32 f n = 0 ↔ ∀ k < n, f k = 0
  | 0 => by simp [val32]
  | n + 1 => by
    rw [val32_succ, Nat.add_eq_zero_iff, val32_eq_zero, Nat.mul_eq_zero]
    have := Nat.two_pow_pos (32 * n)
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h1 k hk
      · exact h2.resolve_left (by omega)
    · intro h
      exact ⟨fun k hk => h k (by omega), .inr (h n (by omega))⟩

theorem val32_inj {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k < 2 ^ 32) → (∀ k < n, g k < 2 ^ 32) →
    (val32 f n = val32 g n ↔ ∀ k < n, f k = g k)
  | 0, _, _ => by simp [val32]
  | n + 1, hf, hg => by
    have hf' := val32_lt (f := f) (n := n) fun k hk => hf k (by omega)
    have hg' := val32_lt (f := g) (n := n) fun k hk => hg k (by omega)
    have ih := val32_inj (n := n) (fun k hk => hf k (by omega)) (fun k hk => hg k (by omega))
    rw [val32_succ, val32_succ]
    generalize hM : 2 ^ (32 * n) = M at hf' hg'
    have hM0 : 0 < M := by rw [← hM]; exact Nat.two_pow_pos _
    constructor
    · intro h
      have e1 : val32 f n = val32 g n := by
        have := congrArg (· % M) h
        simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf', Nat.mod_eq_of_lt hg'] at this
        exact this
      have e2 : f n = g n := by
        have := congrArg (· / M) h
        simp only [Nat.add_mul_div_left _ _ hM0, Nat.div_eq_of_lt hf', Nat.div_eq_of_lt hg',
          Nat.zero_add] at this
        exact this
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact ih.mp e1 k hk
      · exact e2
    · intro h
      rw [ih.mpr fun k hk => h k (by omega), h n (by omega)]

theorem xor_eq_zero {x y : Nat} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = x ^^^ y ^^^ y := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      _ = y := by rw [h, Nat.zero_xor]
  · rintro rfl; exact Nat.xor_self x

theorem fin_sub_eq_zero {n : Nat} [NeZero n] {a c : Fin n} : a - c = 0 ↔ a = c := by
  constructor
  · intro h; grind
  · rintro rfl; exact Fin.sub_self

/-! ## The context -/

/-- The doubleword of accumulated checks. -/
def bad (m : Mem) (b : Addr) : Nat := (m.readW (b + BitVec.ofNat 64 BAD) 64).toNat

theorem offs : VG.Impl.X448.RISCV64.ACC = 952 ∧ OUT = 2048 ∧ BAD = 1696 ∧ SIGN = 1704 := ⟨rfl, rfl, rfl, rfl⟩

/-- X448's context, the working space writable (all but the 8 bytes the
rounding may skip), and `a0` at `OUT`. -/
structure VCtx (b : Addr) (s : State) : Prop where
  ctx : Ctx b s
  ws : ∀ d n, d + n ≤ 8184 → InRegions s.wr (b + BitVec.ofNat 64 d) n
  a0 : s.gpr .a0 = b + BitVec.ofNat 64 OUT

section
variable {b : Addr}

theorem VCtx.of_rest {s s' : State} {ws : List Reg} (h : VCtx b s) (hr : Rest ws s s')
    (h3 : Reg.a0 ∉ ws) (h6 : Reg.a3 ∉ ws) : VCtx b s' :=
  ⟨h.ctx.of_rest hr h6, by rw [hr.wr]; exact h.ws, by rw [hr.gpr _ h3, h.a0]⟩

theorem VCtx.inW {s : State} (h : VCtx b s) {d n : Nat} (hd : d + n ≤ 8184) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n :=
  h.ws d n hd

theorem VCtx.inR {s : State} (h : VCtx b s) {d n : Nat} (hd : d + n ≤ 8184) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) n :=
  let ⟨r, hr, hc⟩ := h.ws d n hd
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- An address `P + d` is a multiple of 8 if `P` and `d` are. -/
theorem al8 {P : Addr} (hP : P.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) :
    (P + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem VCtx.al8 {s : State} (h : VCtx b s) {d : Nat} (hd : d % 8 = 0) :
    (b + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  _root_.VG.Proof.Ed448.RISCV64.al8 h.ctx.al hd

/-- An element below `1064` stays through writes of regions apart from `[0, 1064)`. -/
theorem fs_lo {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hrs : ∀ r ∈ rs, Region.Disjoint ⟨b, 1064⟩ r)
    {q : Nat} (hq : q + 56 ≤ 1064) : FS m' b q = FS m b q := by
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => (hrs r hr).sub_left (Offset.sub_base _ (by omega))
  rw [FS, V, val32_congr e]; rfl

theorem SlotsOk.lo {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hrs : ∀ r ∈ rs, Region.Disjoint ⟨b, 1064⟩ r) {qs : List Nat} {v : Nat → VG.Spec.X448.Fe}
    (hS : SlotsOk m b qs v) (hq : (qs.all fun q => q + 56 ≤ 1064) = true) : SlotsOk m' b qs v := fun q hq' => by
  have h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  rw [fs_lo hf hrs h]; exact hS q hq'

/-- The regions above the field area: `[1064, 8184)` of the working space. -/
theorem disj_hi {d n : Nat} (hd : 1064 ≤ d) (hn : d + n ≤ 8184) :
    Region.Disjoint ⟨b, 1064⟩ ⟨b + BitVec.ofNat 64 d, n⟩ :=
  (Offset.disjoint_base b (d := d) (n := n) (k := 1064) hd (by omega)).symm

/-- `BAD |= r`. -/
theorem orBad_ok {s : State} (hc : VCtx b s) {r : Reg} (hr : r ≠ .a6) :
    WP isa (.block (orBad r)) s fun t => Rest [.a6] s t ∧
      Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] s.mem t.mem ∧ bad t.mem b = bad s.mem b ||| (s.gpr r).toNat := by
  unfold orBad
  refine wp_ld (a := b + BitVec.ofNat 64 BAD) (by decide) (by rw [hc.ctx.a3]) (hc.al8 (by decide))
    (hc.inR (by decide)) fun s1 u1 => wp_or fun s2 u2 => ?_
  refine wp_sd (a := b + BitVec.ofNat 64 BAD) (by decide)
    (by rw [u2.other _ (by decide), u1.other _ (by decide), hc.ctx.a3]) (hc.al8 (by decide))
    (by rw [u2.wr, u1.wr]; exact hc.inW (by decide)) fun s3 u3 => WP.block_nil ?_
  have hm3 : s3.mem = s.mem.writeW (b + BitVec.ofNat 64 BAD) (s2.gpr .a6) := by rw [u3.mem, u2.mem, u1.mem]
  refine ⟨(u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest _)), ?_, ?_⟩
  · rw [hm3]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (64 / 8))
  · rw [bad, hm3, Mem.readW_writeW_self64, u2.gpr, u1.gpr, u1.other _ hr, BitVec.toNat_or]; rfl

/-- The OR of the first `k` words of `outOr`, from `s0`. -/
structure OrInv (o : Addr) (f : Nat → Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a7] s0 s
  mem : s.mem = s0.mem
  val : (s.gpr .a7).toNat = orw f k

/-- The OR of the words at `OUT`, into `a7`. -/
theorem outOr_ok {s : State} (hc : VCtx b s) :
    WP isa (.block outOr) s fun t => Rest [.a4, .a7] s t ∧ t.mem = s.mem ∧
      (t.gpr .a7).toNat = orw (fun k => wd s.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 := by
  unfold outOr
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (wp_range_flatMap (M := isa)
    (OrInv (b + BitVec.ofNat 64 OUT) (fun k => wd s.mem (b + BitVec.ofNat 64 OUT) (4 * k)) s)
    (fun k t hk h => ?_) 14 (Nat.le_refl _) s1
    ⟨u1.rest (by decide), u1.mem, by rw [u1.gpr]; rfl⟩) fun t h => ⟨h.rest, h.mem, h.val⟩
  refine wp_lw (a := b + BitVec.ofNat 64 (OUT + 4 * k)) (by omega)
    (by rw [h.rest.gpr _ (by decide), hc.a0, Offset.add_add]) (al4 hc.ctx.al (by unfold OUT; omega))
    (by rw [h.rest.rd, h.rest.wr]; exact hc.inR (by unfold OUT; omega)) fun t1 v1 => wp_or fun t2 v2 => ?_
  refine WP.block_nil ⟨h.rest.trans ((v1.rest (by decide)).trans (v2.rest (by decide))), by
    rw [v2.mem, v1.mem, h.mem], ?_⟩
  rw [v2.gpr, BitVec.toNat_or, v1.other _ (by decide), h.val, v1.gpr, toNat_ext32, h.mem, orw, wd,
    Offset.add_add]

/-- The OR of the differences of the words at `OUT` and at `p`, into `BAD`. -/
theorem outSame_ok {s : State} (hc : VCtx b s) {p : Nat} (hp : p + 56 ≤ 2048) (hp4 : p % 4 = 0) :
    WP isa (.block (outSame p)) s fun t => Rest [.a4, .a5, .a6, .a7] s t ∧
      Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] s.mem t.mem ∧
      bad t.mem b = bad s.mem b |||
        orw (fun k => wd s.mem (b + BitVec.ofNat 64 OUT) (4 * k) ^^^ wd s.mem b (p + 4 * k)) 14 := by
  unfold outSame
  rw [List.cons_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  let f := fun k => wd s.mem (b + BitVec.ofNat 64 OUT) (4 * k) ^^^ wd s.mem b (p + 4 * k)
  refine WP.append (wp_range_flatMap (M := isa) (fun k t => Rest [.a4, .a5, .a7] s t ∧ t.mem = s.mem ∧
      (t.gpr .a7).toNat = orw f k)
    (fun k t hk h => ?_) 14 (Nat.le_refl _) s1
    ⟨u1.rest (by decide), u1.mem, by rw [u1.gpr]; rfl⟩) fun t ⟨hr, hm, hv⟩ => ?_
  · obtain ⟨hr, hm, hv⟩ := h
    refine wp_lw (a := b + BitVec.ofNat 64 (OUT + 4 * k)) (by omega)
      (by rw [hr.gpr _ (by decide), hc.a0, Offset.add_add]) (al4 hc.ctx.al (by unfold OUT; omega))
      (by rw [hr.rd, hr.wr]; exact hc.inR (by unfold OUT; omega)) fun t1 v1 => ?_
    refine wp_lw (a := b + BitVec.ofNat 64 (p + 4 * k)) (by omega)
      (by rw [v1.other _ (by decide), hr.gpr _ (by decide), hc.ctx.a3]) (al4 hc.ctx.al (by omega))
      (by rw [v1.rd, v1.wr, hr.rd, hr.wr]; exact hc.inR (by omega)) fun t2 v2 => ?_
    refine wp_xor fun t3 v3 => wp_or fun t4 v4 => WP.block_nil ⟨?_, ?_, ?_⟩
    · exact hr.trans ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide)))))
    · rw [v4.mem, v3.mem, v2.mem, v1.mem, hm]
    · rw [v4.gpr, BitVec.toNat_or, v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), hv,
        v3.gpr, BitVec.toNat_xor, v2.other _ (by decide), v1.gpr, v2.gpr, toNat_ext32, toNat_ext32, v1.mem, hm,
        orw]
      simp only [f, wd, Offset.add_add]
  · have hc' : VCtx b t := hc.of_rest (hr.trans (Rest.refl _ _)) (by decide) (by decide)
    refine WP.mono (orBad_ok hc' (r := .a7) (by decide)) fun t' ⟨hr', hf', hb'⟩ =>
      ⟨(hr.mono (by decide)).trans (hr'.mono (by decide)), by rw [← hm]; exact hf', ?_⟩
    rw [hb', hv, bad, bad, hm]

end

end VG.Proof.Ed448.RISCV64
