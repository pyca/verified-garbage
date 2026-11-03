module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Cols
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V: the residue as words

`packC` (`Impl/Weierstrass/RISCV64/P521Unsat.lean`) meets GenWide's
specification of an operation (`GenWide.CoreSpecP`): a tight element to the
nine words of its residue modulo `p` (`pack_spec`). The carries through the
limbs (`carryPass_ok`), the bits from 521 on (`topCut_ok`), the carries of
`v + 1` (`probe_ok`), which make the limbs at `Z` the residue (`canon_ok`),
then each word from the limbs it has bits of (`packStep_ok`, `pack_word`).
-/

@[expose] public section

-- The limbs' positions are numerals.
set_option exponentiation.threshold 600

namespace VG.Proof.Weierstrass.RISCV64.P521Unsat

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P521Unsat
open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk CoreSpecP ownR clobW xv ov)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- The limbs at `Z`. -/
abbrev zl (m : Mem) (b : Addr) (j : Nat) : Nat := dw m b (Z + 8 * j)

/-- What the passes over the limbs keep, from `s0`: memory but at `Z`. -/
structure ZKept (b O : Addr) (s0 s : State) : Prop where
  kept : Kept b O s0 s
  a6 : s.gpr .a6 = M58
  fz : Frame [Zr b] s0.mem s.mem

theorem ZKept.trans {b O : Addr} {s0 s1 s2 : State} (h₁ : ZKept b O s0 s1) (h₂ : ZKept b O s1 s2) : ZKept b O s0 s2 :=
  ⟨h₁.kept.trans h₂.kept, h₂.a6, h₁.fz.trans h₂.fz⟩

theorem ZKept.refl {b O : Addr} {s : State} (h6 : s.gpr .a6 = M58) : ZKept b O s s :=
  ⟨Kept.refl _ _ _, h6, Frame.refl _ _⟩

theorem ZKept.keeps {b O : Addr} {s0 s s' : State} (h : ZKept b O s0 s) {rs : List Reg} (hk : Keeps rs s s')
    (hc : ∀ r ∈ rs, r ∈ clobW ∧ r ≠ .a6 := by decide) : ZKept b O s0 s' :=
  ⟨h.kept.keeps hk fun r hr => (hc r hr).1, by rw [hk.1 _ fun e => (hc _ e).2 rfl, h.a6], by rw [hk.2.1]; exact h.fz⟩

/-- A write to the limbs at `Z`. -/
theorem ZKept.sd {b O : Addr} {s0 s s' : State} (h : ZKept b O s0 s) {j : Nat}
    (hj : j < 9) {v : BitVec 64} (u : Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 (Z + 8 * j)) v)) :
    ZKept b O s0 s' :=
  ⟨h.kept.sd (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) u, by rw [u.gpr]; exact h.a6, by
    rw [u.mem]
    exact h.fz.writeW (List.mem_singleton_self _) _ (Offset.contains b (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)
      (by rw [Z_eq]; omega))⟩

theorem zl_write {m : Mem} {b : Addr} {i j : Nat} (hi : i < 9) (hj : j < 9) (v : BitVec 64) :
    zl (m.writeW (b + BitVec.ofNat 64 (Z + 8 * i)) v) b j = if j = i then v.toNat else zl m b j := by
  unfold zl
  split
  · subst j; exact dw_write_self _ _ _ _
  · exact dw_write_other _ _ _ (by omega) (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)

/-- An operand's word, unchanged by a write to the own working space. -/
theorem dwA_write {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) {m : Mem} {j d : Nat} (hj : j < 9)
    (hd : 1472 ≤ d) (hd' : d + 8 ≤ 1632) (v : BitVec 64) :
    dw (m.writeW (b + BitVec.ofNat 64 d) v) A (8 * j) = dw m A (8 * j) := by
  unfold dw
  rw [Mem.readW_writeW_sep (w := 64) (w' := 64) ?_ (by decide)]
  have hs : Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ (ownR 9 b) := own_sub hd hd'
  exact Region.Disjoint.sep (fun x h₁ h₂ => hC.adis j hj x h₁ (hs x h₂)) (Region.contains_self _ _)
    (Region.contains_self _ _)

theorem carry_arith {L K c t c0 F : Nat} (hv : L + K * c = F + c0) :
    L + K * ((t + c) % 2 ^ 58) + K * 2 ^ 58 * ((t + c) / 2 ^ 58) = F + K * t + c0 := by
  have h : K * ((t + c) % 2 ^ 58) + K * 2 ^ 58 * ((t + c) / 2 ^ 58) = K * t + K * c := by
    rw [Nat.mul_assoc, ← Nat.mul_add, Nat.add_comm, Nat.div_add_mod, Nat.mul_add]
  omega

/-! ## The carries -/

/-- Where a pass reads its limbs: `[t4]`, or `Z` itself. -/
def IsLimbs (A b : Addr) (src : Reg) (off : Nat) (P : Addr) (d : Nat) : Prop :=
  src = .t4 ∧ off = 0 ∧ P = A ∧ d = 0 ∨ src = .a3 ∧ off = Z ∧ P = b ∧ d = Z

/-- After `i` limbs of a pass over the limbs `f` from the carry `c0`. -/
structure CarryInv (b O : Addr) (f : Nat → Nat) (c0 : Nat) (P : Addr) (d : Nat) (s0 : State) (i : Nat) (s : State) :
    Prop where
  zk : ZKept b O s0 s
  src : ∀ j, i ≤ j → j < 9 → dw s.mem P (d + 8 * j) = f j
  lt : ∀ j < i, j < 8 → zl s.mem b j < 2 ^ 58
  carry : i < 9 → (s.gpr .a4).toNat < 4
  val : i < 9 → lv (zl s.mem b) i + 2 ^ (58 * i) * (s.gpr .a4).toNat = lv f i + c0
  fin : i = 9 → lv (zl s.mem b) 9 = lv f 9 + c0 ∧ zl s.mem b 8 < f 8 + 4

theorem carryStep_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {src : Reg} {off : Nat} {P : Addr}
    {d : Nat} (hL : IsLimbs A b src off P d) {f : Nat → Nat} (hf : ∀ j < 9, f j < 2 ^ 59) {c0 : Nat} {i : Nat}
    (hi : i < 9) {s : State} (h : CarryInv b O f c0 P d s0 i s) :
    WP isa (.block (carryStep src off i)) s (CarryInv b O f c0 P d s0 (i + 1)) := by
  have hb := hC.nowrap
  have hCs := h.zk.kept.core hC
  unfold carryStep
  simp only [List.cons_append, List.nil_append]
  -- The load.
  have hld : ∀ {is : List Instr} {Q : State → Prop},
      (∀ s', Upd s s' .a1 (BitVec.ofNat 64 (f i)) → WP isa (.block is) s' Q) →
      WP isa (.block (.load .d .a1 src (off + 8 * i) :: is)) s Q := fun k => by
    rcases hL with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [Nat.zero_add]
      refine ldA_ok hCs hi fun s' u => k s' ?_
      have e : s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (f i) := by
        rw [← h.src i (Nat.le_refl _) hi]; simp only [dw, Nat.zero_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [e] at u; exact u
    · refine ld_ok hCs.ctx (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) fun s' u => k s' ?_
      have e : s.mem.readW (P + BitVec.ofNat 64 (Z + 8 * i)) 64 = BitVec.ofNat 64 (f i) := by
        rw [← h.src i (Nat.le_refl _) hi]; simp only [dw, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [e] at u; exact u
  have hfi := hf i hi
  have hc := h.carry hi
  refine hld fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  have e₂ : (s₂.gpr .a1).toNat = f i + (s.gpr .a4).toNat := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have K₂ : ZKept b O s0 s₂ := (h.zk.keeps (rs := [.a1]) ⟨fun r hr => by
    rw [u₂.other r (by simpa using hr), u₁.other r (by simpa using hr)], by rw [u₂.mem, u₁.mem],
    by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩)
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hrest : ∀ {s' : State} {v : BitVec 64}, s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (Z + 8 * i)) v →
      ∀ j, i + 1 ≤ j → j < 9 → dw s'.mem P (d + 8 * j) = f j := fun hm j hj hj' => by
    rw [hm, ← h.src j (by omega) hj']
    rcases hL with ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
    · rw [Nat.zero_add]; exact dwA_write hC hj' (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) _
    · exact dw_write_other _ _ _ (by omega) (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)
  split
  · -- A limb below the top: cut, carry out.
    rename_i h8
    refine wp_srl (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => ?_
    have hc₄ : Ctx b s₄ := ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), K₂.kept.core hC |>.ctx.a3],
      hC.ctx.al, by rw [u₄.wr, u₃.wr]; exact (K₂.kept.core hC).ctx.wr⟩
    refine sd_ok hc₄ (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) fun s₅ u₅ => WP.block_nil ?_
    have e₄ : (s₄.gpr .a1).toNat = (f i + (s.gpr .a4).toNat) % 2 ^ 58 := by
      rw [u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide), K₂.a6, and_M58, e₂]
    have e₅ : (s₅.gpr .a4).toNat = (f i + (s.gpr .a4).toNat) / 2 ^ 58 := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, shr_toNat, e₂]
    have hm₅ : s₅.mem = s.mem.writeW (b + BitVec.ofNat 64 (Z + 8 * i)) (s₄.gpr .a1) := by
      rw [u₅.mem, u₄.mem, u₃.mem, hm₂]
    have hz : ∀ j < 9, zl s₅.mem b j = if j = i then (f i + (s.gpr .a4).toNat) % 2 ^ 58 else zl s.mem b j :=
      fun j hj => by rw [hm₅, zl_write hi hj, e₄]
    refine ⟨(((K₂.keeps (rs := [.a4]) ⟨fun r hr => u₃.other r (by simpa using hr), u₃.mem, u₃.rd, u₃.wr, u₃.sp⟩).keeps
      (rs := [.a1]) ⟨fun r hr => u₄.other r (by simpa using hr), u₄.mem, u₄.rd, u₄.wr, u₄.sp⟩).sd hi u₅),
      hrest hm₅, fun j hj hj8 => ?_, fun _ => by rw [e₅]; omega, fun _ => ?_, fun e => absurd e (by omega)⟩
    · rw [hz j (by omega)]
      split
      · exact Nat.mod_lt _ (by decide)
      · exact h.lt j (by omega) hj8
    · rw [lv, lv_congr (g := zl s.mem b) fun j hj => by rw [hz j (by omega), ite_eq_right (by omega)], hz i hi, ite_eq_left rfl,
        e₅, lv, show 58 * (i + 1) = 58 * i + 58 by omega, Nat.pow_add]
      exact carry_arith (h.val hi)
  · -- The top limb: no cut.
    rename_i h8
    have hi8 : i = 8 := by omega
    subst hi8
    have hc₂ : Ctx b s₂ := (K₂.kept.core hC).ctx
    refine sd_ok hc₂ (by rw [Z_eq]; omega) (by rw [Z_eq]) fun s₃ u₃ => WP.block_nil ?_
    have hm₃ : s₃.mem = s.mem.writeW (b + BitVec.ofNat 64 (Z + 8 * 8)) (s₂.gpr .a1) := by rw [u₃.mem, hm₂]
    have hz : ∀ j < 9, zl s₃.mem b j = if j = 8 then f 8 + (s.gpr .a4).toNat else zl s.mem b j :=
      fun j hj => by rw [hm₃, zl_write (by decide) hj, e₂]
    refine ⟨K₂.sd (by decide) u₃, fun j hj hj' => absurd hj' (by omega), fun j hj hj8 => ?_,
      fun e => absurd e (by decide), fun e => absurd e (by decide), fun _ => ⟨?_, ?_⟩⟩
    · rw [hz j (by omega), ite_eq_right (by omega)]; exact h.lt j (by omega) hj8
    · rw [lv, lv_congr (g := zl s.mem b) fun j hj => by rw [hz j (by omega), ite_eq_right (by omega)], hz 8 (by decide),
        ite_eq_left rfl, show lv f 9 = lv f 8 + 2 ^ (58 * 8) * f 8 from rfl]
      have := h.val (by decide)
      rw [Nat.mul_add]
      omega
    · rw [hz 8 (by decide), ite_eq_left rfl]; omega

/-- A pass over the limbs. -/
theorem carryPass_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {src : Reg} {off : Nat} {P : Addr}
    {d : Nat} (hL : IsLimbs A b src off P d) {f : Nat → Nat} (hf : ∀ j < 9, f j < 2 ^ 59) {c0 : Nat} (hc0 : c0 < 4)
    {s : State} (hz : ZKept b O s0 s) (hsrc : ∀ j < 9, dw s.mem P (d + 8 * j) = f j)
    (ha4 : (s.gpr .a4).toNat = c0) :
    WP isa (.block (carryPass src off)) s (CarryInv b O f c0 P d s0 9) :=
  wp_range_flatMap (M := isa) (CarryInv b O f c0 P d s0) (fun i s' hi h => carryStep_ok hC hL hf hi h) 9
    (Nat.le_refl _) s ⟨hz, fun j _ hj => hsrc j hj, fun _ h => absurd h (Nat.not_lt_zero _), fun _ => by omega,
      fun _ => by rw [ha4]; simp [lv], fun e => absurd e (by decide)⟩

theorem and_M57 (x : BitVec 64) : (x &&& M58 >>> 1).toNat = x.toNat % 2 ^ 57 := by
  rw [show M58 >>> 1 = BitVec.ofNat 64 (2 ^ 57 - 1) by decide, BitVec.toNat_and,
    show (BitVec.ofNat 64 (2 ^ 57 - 1)).toNat = 2 ^ 57 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `topCut`: limb 8's bits from 57 on into `a4`, and limb 8 cut to 57 bits. -/
theorem topCut_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {s : State} (hz : ZKept b O s0 s) :
    WP isa (.block topCut) s fun s' => ZKept b O s0 s' ∧ (s'.gpr .a4).toNat = zl s.mem b 8 / 2 ^ 57 ∧
      zl s'.mem b 8 = zl s.mem b 8 % 2 ^ 57 ∧ ∀ j < 8, zl s'.mem b j = zl s.mem b j := by
  have hCs := hz.kept.core hC
  unfold topCut
  refine ld_ok hCs.ctx (by rw [Z_eq]; omega) (by rw [Z_eq]) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ =>
    wp_srl (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => ?_
  have hc₄ : Ctx b s₄ := ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide), hCs.ctx.a3], hCs.ctx.al, by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hCs.ctx.wr⟩
  rw [show Z + 64 = Z + 8 * 8 from rfl]
  refine sd_ok hc₄ (by rw [Z_eq]; omega) (by rw [Z_eq]) fun s₅ u₅ => WP.block_nil ?_
  have hz₄ : ZKept b O s0 s₄ := ((((hz.keeps (rs := [.a1]) ⟨fun r hr => u₁.other r (by simpa using hr), u₁.mem, u₁.rd,
    u₁.wr, u₁.sp⟩).keeps (rs := [.a4]) ⟨fun r hr => u₂.other r (by simpa using hr), u₂.mem, u₂.rd, u₂.wr,
    u₂.sp⟩).keeps (rs := [.a7]) ⟨fun r hr => u₃.other r (by simpa using hr), u₃.mem, u₃.rd, u₃.wr, u₃.sp⟩).keeps
    (rs := [.a1]) ⟨fun r hr => u₄.other r (by simpa using hr), u₄.mem, u₄.rd, u₄.wr, u₄.sp⟩)
  have hm₅ : s₅.mem = s.mem.writeW (b + BitVec.ofNat 64 (Z + 8 * 8)) (s₄.gpr .a1) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have e₄ : (s₄.gpr .a1).toNat = zl s.mem b 8 % 2 ^ 57 := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      u₁.other _ (by decide), hz.a6, and_M57]; rfl
  refine ⟨hz₄.sd (by decide) u₅, ?_, by rw [hm₅, zl_write (by decide) (by decide), ite_eq_left rfl, e₄],
    fun j hj => by rw [hm₅, zl_write (by decide) (by omega), ite_eq_right (by omega)]⟩
  rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, shr_toNat, u₁.gpr]; rfl

theorem lv_lt {f : Nat → Nat} : ∀ {n}, (∀ j < n, f j < 2 ^ 58) → lv f n < 2 ^ (58 * n)
  | 0, _ => by simp [lv]
  | n + 1, h => by
    have ih := lv_lt (n := n) fun j hj => h j (by omega)
    have hn := h n (by omega)
    rw [lv, show 58 * (n + 1) = 58 * n + 58 by omega, Nat.pow_add]
    have : 2 ^ (58 * n) * f n ≤ 2 ^ (58 * n) * (2 ^ 58 - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ (58 * n) * (2 ^ 58 - 1) + 2 ^ (58 * n) = 2 ^ (58 * n) * 2 ^ 58 := by
      rw [Nat.mul_sub, Nat.mul_one]; have := Nat.le_mul_of_pos_right (2 ^ (58 * n)) (Nat.two_pow_pos 58); omega
    omega

theorem probe_div (f : Nat → Nat) (i k : Nat) :
    (lv f (i + 1) + 1) / (2 ^ (58 * i) * 2 ^ k) = (f i + (lv f i + 1) / 2 ^ (58 * i)) / 2 ^ k := by
  rw [lv, ← Nat.div_div_eq_div_mul, show lv f i + 2 ^ (58 * i) * f i + 1 = lv f i + 1 + 2 ^ (58 * i) * f i by omega,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_comm]

/-- After `i` limbs of the probe. -/
def ProbeInv (b : Addr) (s0 : State) (i : Nat) (s : State) : Prop :=
  Keeps [.a1, .a4] s0 s ∧ (s.gpr .a4).toNat = (lv (zl s0.mem b) i + 1) / 2 ^ (58 * i)

/-- The probe: the carry of `v + 1` past `2⁵²¹`. -/
theorem probe_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {s : State} (hz : ZKept b O s0 s)
    (hl : ∀ j < 8, zl s.mem b j < 2 ^ 58) (h8 : zl s.mem b 8 < 2 ^ 60) :
    WP isa (.block ([.li .a4 1] ++ (List.range 8).flatMap probeStep ++
        [.load .d .a1 .a3 (Z + 64), .add .a1 .a1 .a4, .shift .srl .d .a4 .a1 57])) s fun s' =>
      Keeps [.a1, .a4] s s' ∧ (s'.gpr .a4).toNat = (lv (zl s.mem b) 9 + 1) / 2 ^ 521 := by
  have hCs := hz.kept.core hC
  rw [List.append_assoc, List.singleton_append]
  refine wp_li (imm := 1) (by decide) fun s₁ u₁ => ?_
  have k₁ : Keeps [.a1, .a4] s s₁ := ⟨fun r hr => u₁.other r (by simp at hr; exact hr.2), u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (ProbeInv b s) (N := 8) (fun i s' hi h => ?_) 8
    (Nat.le_refl _) s₁ ⟨k₁, by rw [u₁.gpr]; simp [lv]⟩) fun s₂ h₂ => ?_)
  · obtain ⟨k, e⟩ := h
    have hc : Ctx b s' := ⟨by rw [k.1 _ (by decide), hCs.ctx.a3], hCs.ctx.al, by rw [k.2.2.2.1]; exact hCs.ctx.wr⟩
    have hlt := lv_lt (f := zl s.mem b) (n := i) fun j hj => hl j (by omega)
    have hcar : (s'.gpr .a4).toNat ≤ 1 := by
      rw [e]; exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_succ, Nat.mul_one]; omega))
    unfold probeStep
    refine ld_ok hc (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) fun t₁ v₁ => wp_add fun t₂ v₂ =>
      wp_srl (by decide) fun t₃ v₃ => WP.block_nil ⟨?_, ?_⟩
    · exact k.trans (rs' := [.a1, .a4]) ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [v₃.other _ hr.2, v₂.other _ hr.1, v₁.other _ hr.1], by rw [v₃.mem, v₂.mem, v₁.mem],
        by rw [v₃.rd, v₂.rd, v₁.rd], by rw [v₃.wr, v₂.wr, v₁.wr], by rw [v₃.sp, v₂.sp, v₁.sp]⟩ |>.mono (by decide)
    · have hzi : dw s.mem b (Z + 8 * i) < 2 ^ 58 := hl i hi
      have ev : (t₂.gpr .a1).toNat = zl s.mem b i + (s'.gpr .a4).toNat := by
        rw [v₂.gpr, v₁.gpr, v₁.other _ (by decide), BitVec.toNat_add, Nat.mod_eq_of_lt (by
          show dw s'.mem b (Z + 8 * i) + _ < _; rw [k.2.1]; omega), k.2.1]; rfl
      rw [v₃.gpr, shr_toNat, ev, e, show 58 * (i + 1) = 58 * i + 58 by omega, Nat.pow_add, probe_div]
  · obtain ⟨k₂, e₂⟩ := h₂
    have hc : Ctx b s₂ := ⟨by rw [k₂.1 _ (by decide), hCs.ctx.a3], hCs.ctx.al, by rw [k₂.2.2.2.1]; exact hCs.ctx.wr⟩
    have hlt := lv_lt (f := zl s.mem b) (n := 8) fun j hj => hl j hj
    have hcar : (s₂.gpr .a4).toNat ≤ 1 := by
      rw [e₂]; exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_succ, Nat.mul_one]; omega))
    refine ld_ok hc (by rw [Z_eq]; omega) (by rw [Z_eq]) fun t₁ v₁ => wp_add fun t₂ v₂ =>
      wp_srl (by decide) fun t₃ v₃ => WP.block_nil ⟨?_, ?_⟩
    · exact k₂.trans (rs' := [.a1, .a4]) ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [v₃.other _ hr.2, v₂.other _ hr.1, v₁.other _ hr.1], by rw [v₃.mem, v₂.mem, v₁.mem],
        by rw [v₃.rd, v₂.rd, v₁.rd], by rw [v₃.wr, v₂.wr, v₁.wr], by rw [v₃.sp, v₂.sp, v₁.sp]⟩ |>.mono (by decide)
    · have ev : (t₂.gpr .a1).toNat = zl s.mem b 8 + (s₂.gpr .a4).toNat := by
        rw [v₂.gpr, v₁.gpr, v₁.other _ (by decide), BitVec.toNat_add, Nat.mod_eq_of_lt (by
          show dw s₂.mem b (Z + 64) + _ < _; rw [k₂.2.1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le h8 hcar)
            (by decide)), k₂.2.1]; rfl
      rw [v₃.gpr, shr_toNat, ev, e₂, show (521 : Nat) = 58 * 8 + 57 from rfl, Nat.pow_add, probe_div]

/-! ## The residue -/

theorem canon_arith {X q : Nat} (hX : X < 2 ^ 521) (hq : q ≤ 2) :
    (X + q + (X + q + 1) / 2 ^ 521) % 2 ^ 521 = (X + 2 ^ 521 * q) % p ∧
      (X + q + (X + q + 1) / 2 ^ 521) % 2 ^ 521 < p := by
  by_cases h : X + q + 1 < 2 ^ 521
  · rw [Nat.div_eq_of_lt h, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    have e : X + 2 ^ 521 * q = (X + q) + p * q := by simp only [p]; omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simp only [p]; omega)]
    exact ⟨rfl, by simp only [p]; omega⟩
  · have h1 : (X + q + 1) / 2 ^ 521 = 1 := by omega
    rw [h1]
    have e1 : (X + q + 1) % 2 ^ 521 = X + q + 1 - 2 ^ 521 := by omega
    have e : X + 2 ^ 521 * q = (X + q + 1 - 2 ^ 521) + p * (q + 1) := by simp only [p]; omega
    rw [e1, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simp only [p]; omega)]
    exact ⟨rfl, by simp only [p]; omega⟩

theorem top_mod {L z : Nat} (hL : L < 2 ^ 464) : (L + 2 ^ 464 * z) % 2 ^ 521 = L + 2 ^ 464 * (z % 2 ^ 57) := by
  omega

/-- The limbs at `Z` of a canonical residue. -/
def Canon (m : Mem) (b : Addr) : Prop := (∀ j < 8, zl m b j < 2 ^ 58) ∧ zl m b 8 < 2 ^ 57

theorem lv_canon {m : Mem} {b : Addr} (h : Canon m b) : lv (zl m b) 8 < 2 ^ 464 :=
  lv_lt (n := 8) fun j hj => h.1 j hj

/-- `canon`: the limbs at `Z` of the residue of the tight element at `[A]`. -/
theorem canon_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0)
    (hA : TightF (fun i => dw s0.mem A (8 * i))) (h6 : s0.gpr .a6 = M58) :
    WP isa (.block canon) s0 fun s => ZKept b O s0 s ∧ Canon s.mem b ∧
      lv (zl s.mem b) 9 = lv (fun i => dw s0.mem A (8 * i)) 9 % p := by
  have hb := hC.nowrap
  have e : canon = [.li .a4 0] ++ (carryPass .t4 0 ++ (topCut ++ (carryPass .a3 Z ++
      (([.li .a4 1] ++ (List.range 8).flatMap probeStep ++
        [.load .d .a1 .a3 (Z + 64), .add .a1 .a1 .a4, .shift .srl .d .a4 .a1 57]) ++ (carryPass .a3 Z ++ topCut))))) := by
    simp only [canon, List.append_assoc, List.cons_append, List.nil_append]
  rw [e, List.singleton_append]
  have hf0 : ∀ j < 9, dw s0.mem A (8 * j) < 2 ^ 59 := fun j hj => hA.lt hj
  refine wp_li (imm := 0) (by decide) fun s₁ u₁ => ?_
  have z₁ : ZKept b O s0 s₁ := (ZKept.refl h6).keeps (rs := [.a4])
    ⟨fun r hr => u₁.other r (by simpa using hr), u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩
  -- The carries.
  refine WP.block_append (WP.mono (carryPass_ok hC (.inl ⟨rfl, rfl, rfl, rfl⟩) hf0 (c0 := 0) (by decide) z₁
    (fun j _ => by rw [Nat.zero_add, u₁.mem]) (by rw [u₁.gpr]; rfl)) fun s₂ h₂ => ?_)
  obtain ⟨v₂, t₂⟩ := h₂.fin rfl
  -- The bits from 521 on.
  refine WP.block_append (WP.mono (topCut_ok hC h₂.zk) fun s₃ ⟨z₃, q₃, c₃, o₃⟩ => ?_)
  have hq : zl s₂.mem b 8 / 2 ^ 57 ≤ 2 := by
    have h8 : dw s0.mem A (8 * 8) < 2 ^ 58 := hA.2
    have t₂' : zl s₂.mem b 8 < dw s0.mem A (8 * 8) + 4 := t₂
    omega
  have l₃ : Canon s₃.mem b := ⟨fun j hj => by rw [o₃ j hj]; exact h₂.lt j (by omega) hj, by
    rw [c₃]; exact Nat.mod_lt _ (by decide)⟩
  have e₃ : lv (zl s₃.mem b) 9 = lv (zl s₂.mem b) 8 + 2 ^ 464 * (zl s₂.mem b 8 % 2 ^ 57) := by
    rw [show lv (zl s₃.mem b) 9 = lv (zl s₃.mem b) 8 + 2 ^ (58 * 8) * zl s₃.mem b 8 from rfl, c₃,
      lv_congr (g := zl s₂.mem b) o₃]
  -- The carries again.
  refine WP.block_append (WP.mono (carryPass_ok hC (.inr ⟨rfl, rfl, rfl, rfl⟩) (f := zl s₃.mem b)
    (fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact Nat.lt_trans (l₃.1 j hj) (by decide)
      · exact Nat.lt_trans l₃.2 (by decide))
    (c0 := zl s₂.mem b 8 / 2 ^ 57) (by omega) z₃ (fun _ _ => rfl) q₃) fun s₄ h₄ => ?_)
  obtain ⟨v₄, t₄⟩ := h₄.fin rfl
  have hX : lv (zl s₃.mem b) 9 < 2 ^ 521 := by
    have := lv_canon l₃; have := l₃.2; rw [show lv (zl s₃.mem b) 9 = lv (zl s₃.mem b) 8 + 2 ^ (58 * 8) * zl s₃.mem b 8
      from rfl]; omega
  -- The probe.
  refine WP.block_append (WP.mono (probe_ok hC h₄.zk (fun j hj => h₄.lt j (by omega) hj) (by
    have := l₃.2; omega)) fun s₅ ⟨k₅, q₅⟩ => ?_)
  have z₅ : ZKept b O s0 s₅ := h₄.zk.keeps k₅
  have hq2 : (lv (zl s₄.mem b) 9 + 1) / 2 ^ 521 ≤ 1 := by rw [v₄]; omega
  -- The correction.
  refine WP.block_append (WP.mono (carryPass_ok hC (.inr ⟨rfl, rfl, rfl, rfl⟩) (f := zl s₄.mem b)
    (fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact Nat.lt_trans (h₄.lt j (by omega) hj) (by decide)
      · have := l₃.2; omega)
    (c0 := (lv (zl s₄.mem b) 9 + 1) / 2 ^ 521) (by omega) z₅ (fun _ _ => by rw [k₅.2.1]) q₅) fun s₆ h₆ => ?_)
  obtain ⟨v₆, -⟩ := h₆.fin rfl
  refine WP.mono (topCut_ok hC h₆.zk) fun s₇ ⟨z₇, _, c₇, o₇⟩ => ⟨z₇, ⟨fun j hj => ?_, ?_⟩, ?_⟩
  · rw [o₇ j hj]; exact h₆.lt j (by omega) hj
  · rw [c₇]; exact Nat.mod_lt _ (by decide)
  · have hL : lv (zl s₆.mem b) 8 < 2 ^ 464 := lv_lt (n := 8) fun j hj => h₆.lt j (by omega) hj
    rw [show lv (zl s₇.mem b) 9 = lv (zl s₇.mem b) 8 + 2 ^ (58 * 8) * zl s₇.mem b 8 from rfl, c₇,
      lv_congr (g := zl s₆.mem b) o₇, ← top_mod hL,
      show lv (zl s₆.mem b) 8 + 2 ^ (58 * 8) * zl s₆.mem b 8 = lv (zl s₆.mem b) 9 from rfl, v₆, v₄]
    have hv2 : lv (zl s₂.mem b) 9 = lv (zl s₃.mem b) 9 + 2 ^ 521 * (zl s₂.mem b 8 / 2 ^ 57) := by
      rw [e₃, show lv (zl s₂.mem b) 9 = lv (zl s₂.mem b) 8 + 2 ^ (58 * 8) * zl s₂.mem b 8 from rfl]
      have := Nat.div_add_mod (zl s₂.mem b 8) (2 ^ 57)
      omega
    rw [(canon_arith hX hq).1, ← hv2, v₂, Nat.add_zero]

/-! ## The words -/

/-- Limb `k`'s part of word `j`. -/
def shv (j : Nat) (l : Nat → Nat) (k : Nat) : Nat :=
  if 64 * j ≤ 58 * k then l k * 2 ^ (58 * k - 64 * j) % 2 ^ 64 else l k / 2 ^ (64 * j - 58 * k)

/-- The limbs a word gathers. -/
theorem packInner_ok {b : Addr} (j : Nat) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < 9 ∧ 58 * k < 64 * j + 64 ∧ 64 * j < 58 * k + 58) → ∀ {s : State}, Ctx b s →
      WP isa (.block (ks.flatMap fun k =>
        [.load .d .a1 .a3 (Z + 8 * k)] ++
        (if 64 * j ≤ 58 * k then [.shift .sll .d .a1 .a1 (58 * k - 64 * j)]
         else [.shift .srl .d .a1 .a1 (64 * j - 58 * k)]) ++ [.add .a2 .a2 .a1])) s fun s' =>
        Keeps [.a1, .a2] s s' ∧ (s'.gpr .a2).toNat = ((s.gpr .a2).toNat + tsum (shv j (zl s.mem b)) ks) % 2 ^ 64
  | [], _, s, _ => WP.block_nil ⟨Keeps.refl _ _, by rw [tsum_nil, Nat.add_zero, Nat.mod_eq_of_lt (s.gpr .a2).isLt]⟩
  | k :: ks, hks, s, hc => by
    obtain ⟨hk, h1, h2⟩ := hks k (List.mem_cons_self ..)
    rw [List.flatMap_cons, List.append_assoc, List.singleton_append]
    refine ld_ok hc (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) fun s₁ u₁ => ?_
    have step : ∀ s₂ : State, Keeps [.a1] s₁ s₂ → (s₂.gpr .a1).toNat = shv j (zl s.mem b) k →
        WP isa (.block (.add .a2 .a2 .a1 :: ks.flatMap fun k =>
          [.load .d .a1 .a3 (Z + 8 * k)] ++
          (if 64 * j ≤ 58 * k then [.shift .sll .d .a1 .a1 (58 * k - 64 * j)]
           else [.shift .srl .d .a1 .a1 (64 * j - 58 * k)]) ++ [.add .a2 .a2 .a1])) s₂ fun s' =>
          Keeps [.a1, .a2] s s' ∧ (s'.gpr .a2).toNat = ((s.gpr .a2).toNat + tsum (shv j (zl s.mem b)) (k :: ks)) %
            2 ^ 64 := fun s₂ k₂ e₂ => by
      refine wp_add fun s₃ u₃ => ?_
      have k₃ : Keeps [.a1, .a2] s s₃ := ⟨fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          rw [u₃.other _ hr.2, k₂.1 _ (by simpa using hr.1), u₁.other _ hr.1],
        by rw [u₃.mem, k₂.2.1, u₁.mem], by rw [u₃.rd, k₂.2.2.1, u₁.rd], by rw [u₃.wr, k₂.2.2.2.1, u₁.wr],
        by rw [u₃.sp, k₂.2.2.2.2, u₁.sp]⟩
      have hc₃ : Ctx b s₃ := ⟨by rw [k₃.1 _ (by decide), hc.a3], hc.al, by rw [k₃.2.2.2.1]; exact hc.wr⟩
      refine WP.mono (packInner_ok j ks (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) hc₃)
        fun s' ⟨k', e'⟩ => ⟨(k₃.trans k').mono (by decide), ?_⟩
      rw [e', u₃.gpr, BitVec.toNat_add, k₂.1 _ (by decide), u₁.other _ (by decide), e₂, k₃.2.1]
      simp only [tsum, List.map_cons, List.sum_cons]
      rw [Nat.mod_add_mod, Nat.add_assoc]
    have hl : (s₁.gpr .a1).toNat = zl s.mem b k := by rw [u₁.gpr]; rfl
    split
    · rename_i hle
      refine wp_sll (by omega) fun s₂ u₂ => step s₂ ⟨fun r hr => u₂.other r (by simpa using hr), u₂.mem, u₂.rd, u₂.wr,
        u₂.sp⟩ ?_
      rw [u₂.gpr, shl_toNat, hl, shv, ite_eq_left hle]
    · rename_i hle
      refine wp_srl (by omega) fun s₂ u₂ => step s₂ ⟨fun r hr => u₂.other r (by simpa using hr), u₂.mem, u₂.rd, u₂.wr,
        u₂.sp⟩ ?_
      rw [u₂.gpr, shr_toNat, hl, shv, ite_eq_right hle]

theorem packLimbs_ok (j : Nat) : ∀ k ∈ packLimbs j, k < 9 ∧ 58 * k < 64 * j + 64 ∧ 64 * j < 58 * k + 58 := by
  intro k hk
  simp only [packLimbs, List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
  exact ⟨hk.1, hk.2⟩

/-- Word `j` of the residue. -/
def pw (l : Nat → Nat) (j : Nat) : Nat := tsum (shv j l) (packLimbs j) % 2 ^ 64

theorem packStep_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {j : Nat} (hj : j < 9) {s : State}
    (hk : Kept b O s0 s) :
    WP isa (.block (packStep j)) s fun s' => Kept b O s0 s' ∧
      s'.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (BitVec.ofNat 64 (pw (zl s.mem b) j)) := by
  have hCs := hk.core hC
  unfold packStep
  rw [List.append_assoc, List.singleton_append]
  refine wp_li (imm := 0) (by decide) fun s₁ u₁ => ?_
  have hc₁ : Ctx b s₁ := ⟨by rw [u₁.other _ (by decide), hCs.ctx.a3], hCs.ctx.al, by rw [u₁.wr]; exact hCs.ctx.wr⟩
  refine WP.block_append (WP.mono (packInner_ok j _ (packLimbs_ok j) hc₁) fun s₂ ⟨k₂, e₂⟩ => ?_)
  have K₂ : Kept b O s0 s₂ := (hk.upd u₁).keeps k₂
  refine sdO_ok (K₂.core hC) hj fun s₃ u₃ => WP.block_nil ⟨K₂.sdO hj u₃, ?_⟩
  rw [u₃.mem, k₂.2.1, u₁.mem]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [e₂, u₁.gpr, u₁.mem, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add, pw, Nat.mod_mod]

theorem lv9 (l : Nat → Nat) : lv l 9 = l 0 + 2 ^ 58 * l 1 + 2 ^ 116 * l 2 + 2 ^ 174 * l 3 + 2 ^ 232 * l 4 +
    2 ^ 290 * l 5 + 2 ^ 348 * l 6 + 2 ^ 406 * l 7 + 2 ^ 464 * l 8 := by
  simp only [lv, Nat.reduceMul, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

theorem tsum1 (f : Nat → Nat) (a : Nat) : tsum f [a] = f a := by simp [tsum]
theorem tsum2 (f : Nat → Nat) (a b : Nat) : tsum f [a, b] = f a + f b := by simp [tsum]
theorem tsum3 (f : Nat → Nat) (a b c : Nat) : tsum f [a, b, c] = f a + f b + f c := by simp [tsum]; omega

theorem packLimbs0 : packLimbs 0 = [0, 1] := by decide
theorem shv0_0 (l : Nat → Nat) : shv 0 l 0 = l 0 * 2 ^ 0 % 2 ^ 64 := by unfold shv; rw [ite_eq_left (by decide)]
theorem shv0_1 (l : Nat → Nat) : shv 0 l 1 = l 1 * 2 ^ 58 % 2 ^ 64 := by unfold shv; rw [ite_eq_left (by decide)]
theorem packLimbs1 : packLimbs 1 = [1, 2] := by decide
theorem shv1_1 (l : Nat → Nat) : shv 1 l 1 = l 1 / 2 ^ 6 := by unfold shv; rw [ite_eq_right (by decide)]
theorem shv1_2 (l : Nat → Nat) : shv 1 l 2 = l 2 * 2 ^ 52 % 2 ^ 64 := by unfold shv; rw [ite_eq_left (by decide)]
theorem packLimbs2 : packLimbs 2 = [2, 3] := by decide
theorem shv2_2 (l : Nat → Nat) : shv 2 l 2 = l 2 / 2 ^ 12 := by unfold shv; rw [ite_eq_right (by decide)]
theorem shv2_3 (l : Nat → Nat) : shv 2 l 3 = l 3 * 2 ^ 46 % 2 ^ 64 := by unfold shv; rw [ite_eq_left (by decide)]
theorem packLimbs3 : packLimbs 3 = [3, 4] := by decide
theorem shv3_3 (l : Nat → Nat) : shv 3 l 3 = l 3 / 2 ^ 18 := by unfold shv; rw [ite_eq_right (by decide)]
theorem shv3_4 (l : Nat → Nat) : shv 3 l 4 = l 4 * 2 ^ 40 % 2 ^ 64 := by unfold shv; rw [ite_eq_left (by decide)]
theorem packLimbs4 : packLimbs 4 = [4, 5] := by decide
theorem shv4_4 (l : Nat → Nat) : shv 4 l 4 = l 4 / 2 ^ 24 := by unfold shv; rw [ite_eq_right (by decide)]
theorem shv4_5 (l : Nat → Nat) : shv 4 l 5 = l 5 * 2 ^ 34 % 2 ^ 64 := by unfold shv; rw [ite_eq_left (by decide)]
theorem packLimbs5 : packLimbs 5 = [5, 6] := by decide
theorem shv5_5 (l : Nat → Nat) : shv 5 l 5 = l 5 / 2 ^ 30 := by unfold shv; rw [ite_eq_right (by decide)]
theorem shv5_6 (l : Nat → Nat) : shv 5 l 6 = l 6 * 2 ^ 28 % 2 ^ 64 := by unfold shv; rw [ite_eq_left (by decide)]
theorem packLimbs6 : packLimbs 6 = [6, 7] := by decide
theorem shv6_6 (l : Nat → Nat) : shv 6 l 6 = l 6 / 2 ^ 36 := by unfold shv; rw [ite_eq_right (by decide)]
theorem shv6_7 (l : Nat → Nat) : shv 6 l 7 = l 7 * 2 ^ 22 % 2 ^ 64 := by unfold shv; rw [ite_eq_left (by decide)]
theorem packLimbs7 : packLimbs 7 = [7, 8] := by decide
theorem shv7_7 (l : Nat → Nat) : shv 7 l 7 = l 7 / 2 ^ 42 := by unfold shv; rw [ite_eq_right (by decide)]
theorem shv7_8 (l : Nat → Nat) : shv 7 l 8 = l 8 * 2 ^ 16 % 2 ^ 64 := by unfold shv; rw [ite_eq_left (by decide)]
theorem packLimbs8 : packLimbs 8 = [8] := by decide
theorem shv8_8 (l : Nat → Nat) : shv 8 l 8 = l 8 / 2 ^ 48 := by unfold shv; rw [ite_eq_right (by decide)]

/-- The words gathered from canonical limbs are the residue's. -/
theorem pack_word {l : Nat → Nat} (hl : ∀ j < 8, l j < 2 ^ 58) :
    ∀ j < 9, pw l j = lw (lv l 9) j := by
  have h0 := hl 0 (by decide); have h1 := hl 1 (by decide); have h2 := hl 2 (by decide)
  have h3 := hl 3 (by decide); have h4 := hl 4 (by decide); have h5 := hl 5 (by decide)
  have h6 := hl 6 (by decide); have h7 := hl 7 (by decide)
  intro j hj
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · rw [pw, packLimbs0, tsum2, shv0_0, shv0_1, lv9, lw]; omega
  · rw [pw, packLimbs1, tsum2, shv1_1, shv1_2, lv9, lw]; omega
  · rw [pw, packLimbs2, tsum2, shv2_2, shv2_3, lv9, lw]; omega
  · rw [pw, packLimbs3, tsum2, shv3_3, shv3_4, lv9, lw]; omega
  · rw [pw, packLimbs4, tsum2, shv4_4, shv4_5, lv9, lw]; omega
  · rw [pw, packLimbs5, tsum2, shv5_5, shv5_6, lv9, lw]; omega
  · rw [pw, packLimbs6, tsum2, shv6_6, shv6_7, lv9, lw]; omega
  · rw [pw, packLimbs7, tsum2, shv7_7, shv7_8, lv9, lw]; omega
  · rw [pw, packLimbs8, tsum1, shv8_8, lv9, lw]; omega
  · omega

theorem colsV_lw (X : Nat) : ∀ n, colsV (lw X) n = X % (2 ^ 64) ^ n
  | 0 => by simp [colsV, Nat.mod_one]
  | n + 1 => by
    rw [colsV, colsV_lw X n, show ((2 : Nat) ^ 64) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 from Nat.pow_succ .., Nat.mod_mul,
      lw, Nat.pow_mul]

/-- After `j` words of the packing from `sc`. -/
structure PackInv (b O : Addr) (s0 sc : State) (j : Nat) (s : State) : Prop where
  kept : Kept b O s0 s
  zs : ∀ k < 9, zl s.mem b k = zl sc.mem b k
  outs : ∀ i < j, dw s.mem O (8 * i) = pw (zl sc.mem b) i

/-- `packC`: the residue modulo `p` of a tight element, as nine words. -/
theorem pack_spec : CoreSpecP 9 (.block packC) (fun A _ => Tight A) (fun A _ r => r = uv A % p) := by
  intro b A B O s hC hA
  rw [tight_xv] at hA
  have hb := hC.nowrap
  unfold packC
  rw [List.append_assoc]
  refine mask_ok fun s₁ k₁ h6 => ?_
  have hC₁ := core_of hC (fun r hr => k₁.1 r fun e => hr (by simp at e; rw [e]; decide)) k₁.2.2.1 k₁.2.2.2.1
  have hA₁ : TightF (fun i => dw s₁.mem A (8 * i)) := by rw [k₁.2.1]; exact hA
  refine WP.block_append (WP.mono (canon_ok hC₁ hA₁ h6) fun s₂ ⟨z₂, c₂, v₂⟩ => ?_)
  have K₂ : Kept b O s s₂ := ((Kept.refl b O s).keeps k₁).trans z₂.kept
  refine WP.mono (wp_range_flatMap (M := isa) (PackInv b O s s₂) (fun j t hj h => ?_) 9 (Nat.le_refl _) s₂
    ⟨K₂, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s' h' => ⟨?_, h'.kept.frame, h'.kept.gpr,
      h'.kept.rd, h'.kept.wr, h'.kept.sp⟩
  · refine WP.mono (packStep_ok hC hj h.kept) fun t' ⟨K', hm⟩ => ⟨K', fun k hk => ?_, fun i hi => ?_⟩
    · rw [← h.zs k hk, hm]; exact dw_own_sdO hC hj (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) _
    · have hpw : pw (zl t.mem b) j = pw (zl s₂.mem b) j := by
        unfold pw; congr 1; unfold tsum; congr 1
        exact List.map_congr_left fun k hk => by
          unfold shv; rw [h.zs k (packLimbs_ok j k hk).1]
      rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [dw_write_other _ _ _ (by omega) (by have := hC.onw; omega) (by have := hC.onw; omega)]
        exact h.outs i hi
      · rw [dw_write_self, BitVec.toNat_ofNat, hpw, pw, Nat.mod_mod]
  · have hw : ∀ i < 9, dw s'.mem O (8 * i) = lw (lv (zl s₂.mem b) 9) i := fun i hi => by
      rw [h'.outs i hi, pack_word c₂.1 i hi]
    dsimp only
    rw [show ov s'.mem O 9 = colsV (lw (lv (zl s₂.mem b) 9)) 9 from
      GenWide.colsV_congr fun i hi => hw i hi, colsV_lw, uv_xv, ← k₁.2.1, ← v₂]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by rw [v₂]; exact Nat.mod_lt _ (by decide)) (by decide))

end VG.Proof.Weierstrass.RISCV64.P521Unsat
