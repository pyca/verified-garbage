module

public import VerifiedGarbage.Proof.Poly1305.Arm.Bytes
public import VerifiedGarbage.Proof.Poly1305.Limbs32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Poly1305 on 32-bit ARM with `umaal`: the arithmetic in radix `2³²`

The code of `Impl/Poly1305/Arm.lean`'s "With `umaal`", run one instruction at
a time on the registers by name (`RF`, `St`): each `umaal` gives two new
words and the equation between them and its operands, and the numbers those
equations make are `Proof/Poly1305/Limbs32.lean`'s. Between blocks (`WAcc`)
the accumulator's five words are in `r3`, `r5`, `r7`, `r10` and `r11`, the
top one below `topMax`, and the state holds the words of the clamped `r` and
`s1`–`s3` (`KeyW`).
-/
-- separate module: the arithmetic of the `umaal` variant, apart from the steps both variants share

@[expose] public section

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P)
open VG.Proof.Poly1305.Limbs32 (val5 topMax)

/-! ## The registers, by name -/

/-- The registers' values. -/
structure RF where
  r0 : BitVec 32
  r1 : BitVec 32
  r2 : BitVec 32
  r3 : BitVec 32
  r4 : BitVec 32
  r5 : BitVec 32
  r6 : BitVec 32
  r7 : BitVec 32
  r8 : BitVec 32
  r9 : BitVec 32
  r10 : BitVec 32
  r11 : BitVec 32
  r12 : BitVec 32
  lr : BitVec 32

/-- Register `r` of `f`. -/
def RF.get (f : RF) : Reg → BitVec 32
  | .r0 => f.r0 | .r1 => f.r1 | .r2 => f.r2 | .r3 => f.r3 | .r4 => f.r4 | .r5 => f.r5 | .r6 => f.r6
  | .r7 => f.r7 | .r8 => f.r8 | .r9 => f.r9 | .r10 => f.r10 | .r11 => f.r11 | .r12 => f.r12
  | .lr => f.lr

/-- `f` with register `r` set to `v`. -/
def RF.set (f : RF) : Reg → BitVec 32 → RF
  | .r0, v => { f with r0 := v } | .r1, v => { f with r1 := v } | .r2, v => { f with r2 := v }
  | .r3, v => { f with r3 := v } | .r4, v => { f with r4 := v } | .r5, v => { f with r5 := v }
  | .r6, v => { f with r6 := v } | .r7, v => { f with r7 := v } | .r8, v => { f with r8 := v }
  | .r9, v => { f with r9 := v } | .r10, v => { f with r10 := v } | .r11, v => { f with r11 := v }
  | .r12, v => { f with r12 := v } | .lr, v => { f with lr := v }

/-- The registers `g`, by name. -/
def RF.of (g : Reg → BitVec 32) : RF :=
  ⟨g .r0, g .r1, g .r2, g .r3, g .r4, g .r5, g .r6, g .r7, g .r8, g .r9, g .r10, g .r11, g .r12, g .lr⟩

theorem RF.get_of (g : Reg → BitVec 32) : (RF.of g).get = g := by
  funext r; cases r <;> rfl

theorem RF.get_set (f : RF) (d : Reg) (v : BitVec 32) (r : Reg) :
    (f.set d v).get r = if r = d then v else f.get r := by
  cases d <;> cases r <;> rfl

/-- `s` is `s₀` but for its registers, which are `f`, and the flags. -/
structure St (s₀ s : State) (f : RF) : Prop where
  gpr : s.gpr = f.get
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem St.init (s : State) : St s s (RF.of s.gpr) := ⟨(RF.get_of _).symm, rfl, rfl, rfl, rfl⟩

theorem St.g {s₀ s : State} {f : RF} (h : St s₀ s f) (r : Reg) : s.gpr r = f.get r := congrFun h.gpr r

theorem St.set {s₀ s : State} {f : RF} (h : St s₀ s f) (d : Reg) (v : BitVec 32) :
    St s₀ (s.setReg d v) (f.set d v) :=
  ⟨by funext r; rw [RF.get_set, ← h.g]; rfl, h.mem, h.rd, h.wr, h.sp⟩

/-- What the code leaves, from the registers it leaves: all but `r1`–`r12`
and the flags. -/
theorem St.keeps {s s' : State} {f : RF} (h : St s s' f) (h0 : f.r0 = s.gpr .r0) (hl : f.lr = s.gpr .lr) :
    Keeps work s s' :=
  ⟨fun r hr => by
    rw [h.g]
    cases r <;> first | exact h0 | exact hl | exact absurd (by decide) hr, h.mem, h.rd, h.wr, h.sp⟩

/-- What the code leaves, from the registers it leaves: all but `ws`. -/
theorem St.keepsL {s s' : State} {f : RF} {ws : List Reg} (h : St s s' f)
    (hk : ∀ r, r ∉ ws → f.get r = s.gpr r) : Keeps ws s s' :=
  ⟨fun r hr => by rw [h.g]; exact hk r hr, h.mem, h.rd, h.wr, h.sp⟩

section
variable {s₀ s : State} {f : RF} {is : List Instr} {Q : State → Prop}

theorem St.op_reg (h : St s₀ s f) (r : Reg) : (Op2.reg r).eval s = some (f.get r) := by
  rw [op2_reg, h.g]

theorem St.op_lsr (h : St s₀ s f) {r : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsr n).eval s = some (f.get r >>> n) := by
  rw [op2_lsr hn, h.g]

theorem St.op_lsl (h : St s₀ s f) {r : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsl n).eval s = some (f.get r <<< n) := by
  rw [op2_lsl hn, h.g]

theorem St.mov (h : St s₀ s f) {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', St s₀ s' (f.set d v) → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some]) (k _ (h.set d v))

theorem St.add (h : St s₀ s f) {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', St s₀ s' (f.set d (f.get n + y)) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (f.get n + y)) (by simp only [exec, ho, Option.map_some, h.g]) (k _ (h.set d _))

theorem St.and (h : St s₀ s f) {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', St s₀ s' (f.set d (f.get n &&& y)) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .and d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (f.get n &&& y)) (by simp only [exec, ho, Option.map_some, h.g]) (k _ (h.set d _))

theorem St.mul (h : St s₀ s f) {d n m : Reg}
    (k : ∀ s', St s₀ s' (f.set d (f.get n * f.get m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons (s' := s.setReg d (f.get n * f.get m)) (by simp only [exec, h.g]) (k _ (h.set d _))

theorem St.mla (h : St s₀ s f) {d n m a : Reg}
    (k : ∀ s', St s₀ s' (f.set d (f.get n * f.get m + f.get a)) → WP isa (.block is) s' Q) :
    WP isa (.block (.mla d n m a :: is)) s Q :=
  WP.cons (s' := s.setReg d (f.get n * f.get m + f.get a)) (by simp only [exec, h.g]) (k _ (h.set d _))

/-- A load of a word whose value is `v`. -/
theorem St.ldr (h : St s₀ s f) {t n : Reg} {off : Nat} {a : Addr} {v : BitVec 32} (ho : off < 4096)
    (ha : State.addr (f.get n + BitVec.ofNat 32 off) = a) (hin : InRegions (s₀.rd ++ s₀.wr) a 4)
    (hv : s₀.mem.readW a 32 = v)
    (k : ∀ s', St s₀ s' (f.set t v) → WP isa (.block is) s' Q) : WP isa (.block (.ldr t n off :: is)) s Q := by
  subst ha hv
  refine WP.cons (s' := s.setReg t (s₀.mem.readW _ 32)) ?_ (k _ (h.set t _))
  rw [exec_ldr ho (by rw [h.g, h.rd, h.wr]; exact hin), h.g, h.mem]

/-- `umaal lo, hi, n, m`: two new words `l` and `c`, with
`l + 2³² c = n m + hi + lo`. -/
theorem St.umaal (h : St s₀ s f) {lo hi n m : Reg} (hne : lo ≠ hi)
    (k : ∀ s' (l c : BitVec 32),
      l.toNat + 2 ^ 32 * c.toNat = (f.get n).toNat * (f.get m).toNat + (f.get hi).toNat + (f.get lo).toNat →
      St s₀ s' ((f.set lo l).set hi c) → WP isa (.block is) s' Q) :
    WP isa (.block (.umaal lo hi n m :: is)) s Q := by
  obtain hlt : (f.get n).toNat * (f.get m).toNat + (f.get hi).toNat + (f.get lo).toNat < 2 ^ 64 := by
    have h1 : (f.get n).toNat * (f.get m).toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (Nat.le_of_lt_succ (f.get n).isLt) (Nat.le_of_lt_succ (f.get m).isLt)
    have h2 := (f.get hi).isLt
    have h3 := (f.get lo).isLt
    omega_using [h1, h2, h3]
  generalize hR : (f.get n).toNat * (f.get m).toNat + (f.get hi).toNat + (f.get lo).toNat = R at hlt k
  refine WP.cons (s' := (s.setReg lo (BitVec.ofNat 32 R)).setReg hi (BitVec.ofNat 32 (R / 2 ^ 32)))
    (by simp only [exec, hne, ↓reduceIte, h.g, hR]) (k _ _ _ ?_ ((h.set lo _).set hi _))
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := R / 2 ^ 32) (by omega_using [hlt])]
  omega_arith

end

/-- The registers by name, after an instruction that sets one to a value
given (`rf`), to a value read from others (`rfg`), or after an `umaal`, with
its equation (`rfu`). -/
local macro "rf " h:ident : tactic => `(tactic| simp only [RF.set] at $h:ident)
/-- `rf`, for a value read from other registers. -/
local macro "rfg " h:ident : tactic => `(tactic| simp only [RF.set, RF.get] at $h:ident)
/-- `rf`, after an `umaal`, with its equation. -/
local macro "rfu " q:ident h:ident : tactic =>
  `(tactic| (simp only [RF.get] at $q:ident; simp only [RF.set] at $h:ident))

/-! ## Words -/

theorem top5_toNat (x : BitVec 32) (h : 5 * (x.toNat / 4) < 2 ^ 32) :
    (x >>> 2 + (x >>> 2) <<< 2).toNat = 5 * (x.toNat / 4) := by
  rw [BitVec.toNat_add, toNat_shl, toNat_shr]
  omega_using [h]

theorem and3_toNat (x : BitVec 32) : (x &&& 3).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 2

theorem zero_toNat : (0 : BitVec 32).toNat = 0 := rfl
theorem one_toNat : (1 : BitVec 32).toNat = 1 := rfl
theorem five_toNat : (5 : BitVec 32).toNat = 5 := rfl

/-- The accumulator's words: `h0`–`h4` in `r3`, `r5`, `r7`, `r10` and `r11`. -/
def WRegs (h0 h1 h2 h3 h4 : Nat) (s : State) : Prop :=
  (s.gpr .r3).toNat = h0 ∧ (s.gpr .r5).toNat = h1 ∧ (s.gpr .r7).toNat = h2 ∧ (s.gpr .r10).toNat = h3 ∧
    (s.gpr .r11).toNat = h4

/-- The words to multiply: `a0`–`a4` in `r4`, `r6`, `r8`, `r9` and `r12`. -/
def ARegs (a0 a1 a2 a3 a4 : Nat) (s : State) : Prop :=
  (s.gpr .r4).toNat = a0 ∧ (s.gpr .r6).toNat = a1 ∧ (s.gpr .r8).toNat = a2 ∧ (s.gpr .r9).toNat = a3 ∧
    (s.gpr .r12).toNat = a4

/-- The multipliers in the state at `B`: the words `r0`, `4 q1`, `4 q2`, `4 q3`
of the clamped `r` at `[88, 104)` and `s1`–`s3`, `5 qj`, at `[104, 116)`. -/
structure KeyW (B : Addr) (r0 q1 q2 q3 : Nat) (m : Mem) : Prop where
  w0 : (m.readW (B + BitVec.ofNat 64 88) 32).toNat = r0
  w1 : (m.readW (B + BitVec.ofNat 64 92) 32).toNat = 4 * q1
  w2 : (m.readW (B + BitVec.ofNat 64 96) 32).toNat = 4 * q2
  w3 : (m.readW (B + BitVec.ofNat 64 100) 32).toNat = 4 * q3
  s1 : (m.readW (B + BitVec.ofNat 64 104) 32).toNat = 5 * q1
  s2 : (m.readW (B + BitVec.ofNat 64 108) 32).toNat = 5 * q2
  s3 : (m.readW (B + BitVec.ofNat 64 112) 32).toNat = 5 * q3
  b0 : r0 < 2 ^ 28
  b1 : q1 < 2 ^ 26
  b2 : q2 < 2 ^ 26
  b3 : q3 < 2 ^ 26

/-! ## Adding a block -/

theorem addBlock_ok (pad : Bool) {h0 h1 h2 h3 h4 : Nat} {s : State}
    (hh : WRegs h0 h1 h2 h3 h4 s) (hb : h4 < topMax)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (addBlock pad)) s fun s' => ∃ a0 a1 a2 a3 a4,
      ARegs a0 a1 a2 a3 a4 s' ∧ a4 ≤ 6 ∧
      val5 a0 a1 a2 a3 a4 % P = (val5 h0 h1 h2 h3 h4 + msgVal s + if pad then 2 ^ 128 else 0) % P ∧
      Keeps work s s' := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := hh
  obtain hc : 5 * ((s.gpr .r11).toNat / 4) < 2 ^ 32 := by
    rw [e4]; have : h4 < 3 * 2 ^ 30 := hb; omega_using [this]
  have i₀ := St.init s
  simp only [RF.of] at i₀
  rw [addBlock, top5]
  simp only [List.cons_append, List.nil_append]
  refine i₀.ldr (v := word s 0) (by decide) rfl (hin 0 (by decide)) rfl fun s₁ i₁ => ?_
  rf i₁
  refine i₁.ldr (v := word s 1) (by decide) rfl (hin 1 (by decide)) rfl fun s₂ i₂ => ?_
  rf i₂
  refine i₂.ldr (v := word s 2) (by decide) rfl (hin 2 (by decide)) rfl fun s₃ i₃ => ?_
  rf i₃
  refine i₃.ldr (v := word s 3) (by decide) rfl (hin 3 (by decide)) rfl fun s₄ i₄ => ?_
  rf i₄
  refine i₄.mov (i₄.op_lsr (by decide)) fun s₅ i₅ => ?_
  rfg i₅
  refine i₅.add (i₅.op_lsl (by decide)) fun s₆ i₆ => ?_
  rfg i₆
  refine i₆.and (op2_imm (by decide)) fun s₇ i₇ => ?_
  rfg i₇
  refine i₇.mov (op2_imm (by decide)) fun s₈ i₈ => ?_
  rf i₈
  refine i₈.umaal (by decide) fun s₉ a0 c1 q0 i₉ => ?_
  rfu q0 i₉
  refine i₉.umaal (by decide) fun s₁₀ a1 c2 q1 i₁₀ => ?_
  rfu q1 i₁₀
  refine i₁₀.umaal (by decide) fun s₁₁ a2 c3 q2 i₁₁ => ?_
  rfu q2 i₁₁
  refine i₁₁.umaal (by decide) fun s₁₂ a3 c4 q3 i₁₂ => ?_
  rfu q3 i₁₂
  refine i₁₂.add (i₁₂.op_reg _) fun s₁₃ i₁₃ => ?_
  rfg i₁₃
  -- The numbers.
  rw [e0, one_toNat, Nat.mul_one, top5_toNat _ hc, e4] at q0
  rw [e1, one_toNat, Nat.mul_one] at q1
  rw [e2, one_toNat, Nat.mul_one] at q2
  rw [e3, one_toNat, Nat.mul_one] at q3
  rw [e4] at hc
  obtain key : ∀ p ≤ 1, val5 a0.toNat a1.toNat a2.toNat a3.toNat (h4 % 4 + c4.toNat + p) % P =
      (val5 h0 h1 h2 h3 h4 + msgVal s + 2 ^ 128 * p) % P ∧ h4 % 4 + c4.toNat + p ≤ 6 := fun p hp =>
    Limbs32.add_arith (e0 ▸ (s.gpr .r3).isLt) (e1 ▸ (s.gpr .r5).isLt) (e2 ▸ (s.gpr .r7).isLt)
      (e3 ▸ (s.gpr .r10).isLt) (word s 0).isLt (word s 1).isLt (word s 2).isLt (word s 3).isLt hp hc q0 q1 q2 q3
  obtain hsum : ((s.gpr .r11 &&& 3) + c4).toNat = h4 % 4 + c4.toNat := by
    have := (key 0 (Nat.zero_le _)).2
    rw [toNat_add_lt (by rw [and3_toNat, e4]; omega_using [this]), and3_toNat, e4]
  cases pad
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hv, ha4⟩ := key 0 (Nat.zero_le _)
    rw [Nat.mul_zero] at hv
    rw [Nat.add_zero] at hv ha4
    exact WP.block_nil ⟨a0.toNat, a1.toNat, a2.toNat, a3.toNat, h4 % 4 + c4.toNat,
      ⟨congrArg BitVec.toNat (i₁₃.g .r4), congrArg BitVec.toNat (i₁₃.g .r6), congrArg BitVec.toNat (i₁₃.g .r8),
        congrArg BitVec.toNat (i₁₃.g .r9), (congrArg BitVec.toNat (i₁₃.g .r12)).trans hsum⟩,
      ha4, hv, i₁₃.keeps rfl rfl⟩
  · simp only [↓reduceIte]
    refine i₁₃.add (op2_imm (by decide)) fun s₁₄ i₁₄ => ?_
    rfg i₁₄
    obtain ⟨hv, ha4⟩ := key 1 (Nat.le_refl _)
    rw [Nat.mul_one] at hv
    refine WP.block_nil ⟨a0.toNat, a1.toNat, a2.toNat, a3.toNat, h4 % 4 + c4.toNat + 1,
      ⟨congrArg BitVec.toNat (i₁₄.g .r4), congrArg BitVec.toNat (i₁₄.g .r6), congrArg BitVec.toNat (i₁₄.g .r8),
        congrArg BitVec.toNat (i₁₄.g .r9), (congrArg BitVec.toNat (i₁₄.g .r12)).trans ?_⟩,
      ha4, hv, i₁₄.keeps rfl rfl⟩
    show ((s.gpr .r11 &&& 3) + c4 + 1).toNat = h4 % 4 + c4.toNat + 1
    rw [toNat_add_lt (by rw [hsum, one_toNat]; omega_using [ha4]), hsum, one_toNat]

/-! ## Multiplying by `r` -/

/-- The product of a word of at most 6 and a word below `2²⁹`, a word. -/
theorem toNat_mul6 {x y : BitVec 32} {a m : Nat} (hx : x.toNat = a) (hy : y.toNat = m) (ha : a ≤ 6)
    (hm : m < 2 ^ 29) : (x * y).toNat = a * m := by
  have := Nat.mul_le_mul ha (Nat.le_of_lt_succ (show m < 2 ^ 29 - 1 + 1 from hm))
  rw [toNat_mul_lt (by rw [hx, hy]; omega_using [this]), hx, hy]

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem mulU_ok {r0 q1 q2 q3 a0 a1 a2 a3 a4 : Nat} {s : State} (hs0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (hk : KeyW (State.addr st) r0 q1 q2 q3 s.mem) (ha : ARegs a0 a1 a2 a3 a4 s) (ha4 : a4 ≤ 6) :
    WP isa (.block mulU) s fun s' => ∃ w0 w1 w2 w3 w4, WRegs w0 w1 w2 w3 w4 s' ∧ w4 < topMax ∧
      val5 w0 w1 w2 w3 w4 % P = val5 a0 a1 a2 a3 a4 * Limbs32.key r0 q1 q2 q3 % P ∧ Keeps work s s' := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := ha
  have hb0 := hk.b0
  have hb1 := hk.b1
  have hb2 := hk.b2
  have hb3 := hk.b3
  have i₀ := St.init s
  simp only [RF.of, hs0] at i₀
  rw [mulU, mulR0, mul1, mul2, mul3]
  simp only [List.cons_append, List.nil_append]
  -- The products of `a4`, and the chain of `r0`.
  refine i₀.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₁ i₁ => ?_
  rf i₁
  refine i₁.mul fun s₂ i₂ => ?_
  rfg i₂
  refine i₂.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₃ i₃ => ?_
  rf i₃
  refine i₃.mul fun s₄ i₄ => ?_
  rfg i₄
  refine i₄.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₅ i₅ => ?_
  rf i₅
  refine i₅.mul fun s₆ i₆ => ?_
  rfg i₆
  refine i₆.mov (op2_imm (by decide)) fun s₇ i₇ => ?_
  rf i₇
  refine i₇.mov (op2_imm (by decide)) fun s₈ i₈ => ?_
  rf i₈
  refine i₈.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₉ i₉ => ?_
  rf i₉
  refine i₉.umaal (by decide) fun s₁₀ x0 xc1 qx0 i₁₀ => ?_
  rfu qx0 i₁₀
  refine i₁₀.umaal (by decide) fun s₁₁ x1 xc2 qx1 i₁₁ => ?_
  rfu qx1 i₁₁
  refine i₁₁.umaal (by decide) fun s₁₂ x2 xc3 qx2 i₁₂ => ?_
  rfu qx2 i₁₂
  refine i₁₂.umaal (by decide) fun s₁₃ x3 xc4 qx3 i₁₃ => ?_
  rfu qx3 i₁₃
  refine i₁₃.mla fun s₁₄ i₁₄ => ?_
  rfg i₁₄
  obtain ⟨x4, hx4⟩ : ∃ x4 : BitVec 32,
      x4 = s.gpr .r12 * s.mem.readW (State.addr st + BitVec.ofNat 64 88) 32 + xc4 := ⟨_, rfl⟩
  rw [← hx4] at i₁₄
  -- The chain of `s1` and `r1`.
  refine i₁₄.mov (op2_imm (by decide)) fun s₁₅ i₁₅ => ?_
  rf i₁₅
  refine i₁₅.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₁₆ i₁₆ => ?_
  rf i₁₆
  refine i₁₆.umaal (by decide) fun s₁₇ y0 yc1 qy0 i₁₇ => ?_
  rfu qy0 i₁₇
  refine i₁₇.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₁₈ i₁₈ => ?_
  rf i₁₈
  refine i₁₈.umaal (by decide) fun s₁₉ y1 yc2 qy1 i₁₉ => ?_
  rfu qy1 i₁₉
  refine i₁₉.umaal (by decide) fun s₂₀ y2 yc3 qy2 i₂₀ => ?_
  rfu qy2 i₂₀
  refine i₂₀.umaal (by decide) fun s₂₁ y3 yc4 qy3 i₂₁ => ?_
  rfu qy3 i₂₁
  refine i₂₁.add (i₂₁.op_reg _) fun s₂₂ i₂₂ => ?_
  rfg i₂₂
  obtain ⟨y4, hy4⟩ : ∃ y4 : BitVec 32, y4 = x4 + yc4 := ⟨_, rfl⟩
  rw [← hy4] at i₂₂
  -- The chain of `s2` and `r2`.
  refine i₂₂.mov (op2_imm (by decide)) fun s₂₃ i₂₃ => ?_
  rf i₂₃
  refine i₂₃.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₂₄ i₂₄ => ?_
  rf i₂₄
  refine i₂₄.umaal (by decide) fun s₂₅ z0 zc1 qz0 i₂₅ => ?_
  rfu qz0 i₂₅
  refine i₂₅.umaal (by decide) fun s₂₆ z1 zc2 qz1 i₂₆ => ?_
  rfu qz1 i₂₆
  refine i₂₆.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₂₇ i₂₇ => ?_
  rf i₂₇
  refine i₂₇.umaal (by decide) fun s₂₈ z2 zc3 qz2 i₂₈ => ?_
  rfu qz2 i₂₈
  refine i₂₈.umaal (by decide) fun s₂₉ z3 zc4 qz3 i₂₉ => ?_
  rfu qz3 i₂₉
  refine i₂₉.add (i₂₉.op_reg _) fun s₃₀ i₃₀ => ?_
  rfg i₃₀
  obtain ⟨z4, hz4⟩ : ∃ z4 : BitVec 32, z4 = y4 + zc4 := ⟨_, rfl⟩
  rw [← hz4] at i₃₀
  -- The chain of `s3` and `r3`.
  refine i₃₀.mov (op2_imm (by decide)) fun s₃₁ i₃₁ => ?_
  rf i₃₁
  refine i₃₁.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₃₂ i₃₂ => ?_
  rf i₃₂
  refine i₃₂.umaal (by decide) fun s₃₃ w0 wc1 qw0 i₃₃ => ?_
  rfu qw0 i₃₃
  refine i₃₃.umaal (by decide) fun s₃₄ w1 wc2 qw1 i₃₄ => ?_
  rfu qw1 i₃₄
  refine i₃₄.umaal (by decide) fun s₃₅ w2 wc3 qw2 i₃₅ => ?_
  rfu qw2 i₃₅
  refine i₃₅.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₃₆ i₃₆ => ?_
  rf i₃₆
  refine i₃₆.umaal (by decide) fun s₃₇ w3 wc4 qw3 i₃₇ => ?_
  rfu qw3 i₃₇
  refine i₃₇.add (i₃₇.op_reg _) fun s₃₈ i₃₈ => WP.block_nil ?_
  rfg i₃₈
  -- The numbers.
  obtain p1 := toNat_mul6 e4 hk.s1 ha4 (by omega_using [hb1])
  obtain p2 := toNat_mul6 e4 hk.s2 ha4 (by omega_using [hb2])
  obtain p3 := toNat_mul6 e4 hk.s3 ha4 (by omega_using [hb3])
  obtain p0 := toNat_mul6 e4 hk.w0 ha4 (by omega_using [hb0])
  rw [e0, hk.w0, zero_toNat] at qx0
  rw [e1, hk.w0, p1] at qx1
  rw [e2, hk.w0, p2] at qx2
  rw [e3, hk.w0, p3] at qx3
  obtain ex4 : x4.toNat = (a4 * r0 + xc4.toNat) % 2 ^ 32 := by rw [hx4, BitVec.toNat_add, p0]
  rw [e3, hk.s1, zero_toNat] at qy0
  rw [e0, hk.w1] at qy1
  rw [e1, hk.w1] at qy2
  rw [e2, hk.w1] at qy3
  obtain ey4 : y4.toNat = (x4.toNat + yc4.toNat) % 2 ^ 32 := by rw [hy4, BitVec.toNat_add]
  rw [e2, hk.s2, zero_toNat] at qz0
  rw [e3, hk.s2] at qz1
  rw [e0, hk.w2] at qz2
  rw [e1, hk.w2] at qz3
  obtain ez4 : z4.toNat = (y4.toNat + zc4.toNat) % 2 ^ 32 := by rw [hz4, BitVec.toNat_add]
  rw [e1, hk.s3, zero_toNat] at qw0
  rw [e2, hk.s3] at qw1
  rw [e3, hk.s3] at qw2
  rw [e0, hk.w3] at qw3
  obtain ew4 : (z4 + wc4).toNat = (z4.toNat + wc4.toNat) % 2 ^ 32 := BitVec.toNat_add _ _
  obtain ⟨hv, hw4⟩ := Limbs32.mul_arith (e0 ▸ (s.gpr .r4).isLt) (e1 ▸ (s.gpr .r6).isLt) (e2 ▸ (s.gpr .r8).isLt)
    (e3 ▸ (s.gpr .r9).isLt) ha4 hb0 hb1 hb2 hb3 qx0 qx1 qx2 qx3 ex4 qy0 qy1 qy2 qy3 ey4 qz0 qz1 qz2 qz3 ez4
    qw0 qw1 qw2 qw3 ew4
  exact ⟨w0.toNat, w1.toNat, w2.toNat, w3.toNat, (z4 + wc4).toNat,
    ⟨congrArg BitVec.toNat (i₃₈.g .r3), congrArg BitVec.toNat (i₃₈.g .r5), congrArg BitVec.toNat (i₃₈.g .r7),
      congrArg BitVec.toNat (i₃₈.g .r10), congrArg BitVec.toNat (i₃₈.g .r11)⟩, hw4, hv, i₃₈.keeps hs0.symm rfl⟩

/-- Absorbing the block at `r1`. -/
theorem absorbU_ok (pad : Bool) {r0 q1 q2 q3 h0 h1 h2 h3 h4 : Nat} {s : State} (hs0 : s.gpr .r0 = st)
    (hw : stR st ∈ s.wr) (hk : KeyW (State.addr st) r0 q1 q2 q3 s.mem) (hh : WRegs h0 h1 h2 h3 h4 s)
    (hb : h4 < topMax)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (absorbU pad)) s fun s' => ∃ w0 w1 w2 w3 w4, WRegs w0 w1 w2 w3 w4 s' ∧ w4 < topMax ∧
      val5 w0 w1 w2 w3 w4 % P =
        (val5 h0 h1 h2 h3 h4 + msgVal s + if pad then 2 ^ 128 else 0) * Limbs32.key r0 q1 q2 q3 % P ∧
      Keeps work s s' := by
  rw [absorbU]
  refine WP.append (addBlock_ok pad hh hb hin) fun s₁ ⟨a0, a1, a2, a3, a4, ha, ha4, hva, k₁⟩ => ?_
  refine WP.mono (mulU_ok hfit (r0 := r0) (q1 := q1) (q2 := q2) (q3 := q3) (by rw [k₁.gpr _ (by decide), hs0])
    (by rw [k₁.wr]; exact hw) (by rw [k₁.mem]; exact hk) ha ha4) fun s₂ h₂ => ?_
  obtain ⟨w0, w1, w2, w3, w4, hW, hw4, hvw, k₂⟩ := h₂
  refine ⟨w0, w1, w2, w3, w4, hW, hw4, ?_, k₁.trans k₂⟩
  rw [hvw, Nat.mul_mod, hva, ← Nat.mul_mod]

end

/-! ## The final reduction -/

/-- `h` reduced fully: its words in `r3`, `r5`, `r7`, `r10` and `r1`. -/
def OutW (w0 w1 w2 w3 w4 : Nat) (s : State) : Prop :=
  (s.gpr .r3).toNat = w0 ∧ (s.gpr .r5).toNat = w1 ∧ (s.gpr .r7).toNat = w2 ∧ (s.gpr .r10).toNat = w3 ∧
    (s.gpr .r1).toNat = w4

/-- A carry of a sum of two words. -/
theorem carry_le {x c a b : Nat} (hx : x + 2 ^ 32 * c = a + b) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) : c ≤ 1 := by
  omega_using [hx, ha, hb]

theorem reduceU_ok {h0 h1 h2 h3 h4 : Nat} {s : State} (hh : WRegs h0 h1 h2 h3 h4 s) (hb : h4 < topMax) :
    WP isa (.block reduceU) s fun s' => ∃ w0 w1 w2 w3 w4, OutW w0 w1 w2 w3 w4 s' ∧
      val5 w0 w1 w2 w3 w4 = val5 h0 h1 h2 h3 h4 % P ∧ Keeps work s s' := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := hh
  obtain hc : 5 * ((s.gpr .r11).toNat / 4) < 2 ^ 32 := by
    rw [e4]; have : h4 < 3 * 2 ^ 30 := hb; omega_using [this]
  have i₀ := St.init s
  simp only [RF.of] at i₀
  rw [reduceU, top5, addLow, carry5]
  simp only [List.cons_append, List.nil_append]
  -- The top word folded in.
  refine i₀.mov (i₀.op_lsr (by decide)) fun s₁ i₁ => ?_
  rfg i₁
  refine i₁.add (i₁.op_lsl (by decide)) fun s₂ i₂ => ?_
  rfg i₂
  refine i₂.and (op2_imm (by decide)) fun s₃ i₃ => ?_
  rfg i₃
  refine i₃.mov (op2_imm (by decide)) fun s₄ i₄ => ?_
  rf i₄
  refine i₄.umaal (by decide) fun s₅ x0 c1 qx0 i₅ => ?_
  rfu qx0 i₅
  refine i₅.umaal (by decide) fun s₆ x1 c2 qx1 i₆ => ?_
  rfu qx1 i₆
  refine i₆.umaal (by decide) fun s₇ x2 c3 qx2 i₇ => ?_
  rfu qx2 i₇
  refine i₇.umaal (by decide) fun s₈ x3 c4 qx3 i₈ => ?_
  rfu qx3 i₈
  refine i₈.add (i₈.op_reg _) fun s₉ i₉ => ?_
  rfg i₉
  obtain ⟨x4, hx4⟩ : ∃ x4 : BitVec 32, x4 = (s.gpr .r11 &&& 3) + c4 := ⟨_, rfl⟩
  rw [← hx4] at i₉
  -- The carry of `h + 5`.
  refine i₉.mov (op2_imm (by decide)) fun s₁₀ i₁₀ => ?_
  rf i₁₀
  refine i₁₀.mov (i₁₀.op_reg _) fun s₁₁ i₁₁ => ?_
  rfg i₁₁
  refine i₁₁.umaal (by decide) fun s₁₂ y0 d1 qy0 i₁₂ => ?_
  rfu qy0 i₁₂
  refine i₁₂.mov (i₁₂.op_reg _) fun s₁₃ i₁₃ => ?_
  rfg i₁₃
  refine i₁₃.umaal (by decide) fun s₁₄ y1 d2 qy1 i₁₄ => ?_
  rfu qy1 i₁₄
  refine i₁₄.mov (i₁₄.op_reg _) fun s₁₅ i₁₅ => ?_
  rfg i₁₅
  refine i₁₅.umaal (by decide) fun s₁₆ y2 d3 qy2 i₁₆ => ?_
  rfu qy2 i₁₆
  refine i₁₆.mov (i₁₆.op_reg _) fun s₁₇ i₁₇ => ?_
  rfg i₁₇
  refine i₁₇.umaal (by decide) fun s₁₈ y3 d4 qy3 i₁₈ => ?_
  rfu qy3 i₁₈
  -- Five times it, added.
  refine i₁₈.add (i₁₈.op_reg _) fun s₁₉ i₁₉ => ?_
  rfg i₁₉
  refine i₁₉.mov (i₁₉.op_lsr (by decide)) fun s₂₀ i₂₀ => ?_
  rfg i₂₀
  refine i₂₀.add (i₂₀.op_lsl (by decide)) fun s₂₁ i₂₁ => ?_
  rfg i₂₁
  refine i₂₁.umaal (by decide) fun s₂₂ w0 k1 qw0 i₂₂ => ?_
  rfu qw0 i₂₂
  refine i₂₂.umaal (by decide) fun s₂₃ w1 k2 qw1 i₂₃ => ?_
  rfu qw1 i₂₃
  refine i₂₃.umaal (by decide) fun s₂₄ w2 k3 qw2 i₂₄ => ?_
  rfu qw2 i₂₄
  refine i₂₄.umaal (by decide) fun s₂₅ w3 k4 qw3 i₂₅ => ?_
  rfu qw3 i₂₅
  refine i₂₅.add (i₂₅.op_reg _) fun s₂₆ i₂₆ => ?_
  rfg i₂₆
  refine i₂₆.and (op2_imm (by decide)) fun s₂₇ i₂₇ => WP.block_nil ?_
  rfg i₂₇
  -- The numbers.
  rw [zero_toNat, Nat.zero_mul, Nat.zero_add, top5_toNat _ hc, e4, e0] at qx0
  rw [zero_toNat, Nat.zero_mul, Nat.zero_add, e1] at qx1
  rw [zero_toNat, Nat.zero_mul, Nat.zero_add, e2] at qx2
  rw [zero_toNat, Nat.zero_mul, Nat.zero_add, e3] at qx3
  rw [e4] at hc
  obtain hc4 := carry_le qx3 c3.isLt (e3 ▸ (s.gpr .r10).isLt)
  obtain ex4 : x4.toNat = h4 % 4 + c4.toNat := by
    rw [hx4, toNat_add_lt (by rw [and3_toNat]; omega_using [hc4]), and3_toNat, e4]
  rw [zero_toNat, Nat.zero_mul, Nat.zero_add, five_toNat] at qy0
  rw [zero_toNat, Nat.zero_mul, Nat.zero_add] at qy1 qy2 qy3
  obtain hd4 := carry_le qy3 d3.isLt x3.isLt
  obtain eg : (d4 + x4).toNat = d4.toNat + (h4 % 4 + c4.toNat) := by
    rw [toNat_add_lt (by rw [ex4]; omega_using [hd4, hc4]), ex4]
  rw [zero_toNat, Nat.zero_mul, Nat.zero_add, top5_toNat _ (by rw [eg]; omega_using [hd4, hc4]), eg] at qw0
  rw [zero_toNat, Nat.zero_mul, Nat.zero_add] at qw1 qw2 qw3
  obtain hk4 := carry_le qw3 k3.isLt x3.isLt
  obtain ew4 : ((x4 + k4) &&& 3).toNat = (h4 % 4 + c4.toNat + k4.toNat) % 4 := by
    rw [and3_toNat, toNat_add_lt (by rw [ex4]; omega_using [hk4, hc4]), ex4]
  obtain hv := Limbs32.reduce_arith (e0 ▸ (s.gpr .r3).isLt) (e1 ▸ (s.gpr .r5).isLt) (e2 ▸ (s.gpr .r7).isLt)
    (e3 ▸ (s.gpr .r10).isLt) hc x0.isLt x1.isLt x2.isLt x3.isLt y0.isLt y1.isLt y2.isLt y3.isLt w0.isLt w1.isLt
    w2.isLt w3.isLt qx0 qx1 qx2 qx3 qy0 qy1 qy2 qy3 qw0 qw1 qw2 qw3
  exact ⟨w0.toNat, w1.toNat, w2.toNat, w3.toNat, (h4 % 4 + c4.toNat + k4.toNat) % 4,
    ⟨congrArg BitVec.toNat (i₂₇.g .r3), congrArg BitVec.toNat (i₂₇.g .r5), congrArg BitVec.toNat (i₂₇.g .r7),
      congrArg BitVec.toNat (i₂₇.g .r10), (congrArg BitVec.toNat (i₂₇.g .r1)).trans ew4⟩, hv, i₂₇.keeps rfl rfl⟩

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The tag: `h mod p` plus `s`, the key's words at `[40, 56)`, modulo `2¹²⁸`,
its words in `r3`, `r5`, `r7` and `r10`. -/
theorem tagU_ok {h0 h1 h2 h3 h4 : Nat} {s : State} (hs0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (hh : WRegs h0 h1 h2 h3 h4 s) (hb : h4 < topMax) :
    WP isa (.block (reduceU ++ addKey)) s fun s' => ∃ t0 t1 t2 t3,
      ((s'.gpr .r3).toNat = t0 ∧ (s'.gpr .r5).toNat = t1 ∧ (s'.gpr .r7).toNat = t2 ∧ (s'.gpr .r10).toNat = t3) ∧
      t0 + 2 ^ 32 * t1 + 2 ^ 64 * t2 + 2 ^ 96 * t3 =
        (val5 h0 h1 h2 h3 h4 % P +
          ((s.mem.readW (State.addr st + BitVec.ofNat 64 40) 32).toNat +
            2 ^ 32 * (s.mem.readW (State.addr st + BitVec.ofNat 64 44) 32).toNat +
            2 ^ 64 * (s.mem.readW (State.addr st + BitVec.ofNat 64 48) 32).toNat +
            2 ^ 96 * (s.mem.readW (State.addr st + BitVec.ofNat 64 52) 32).toNat)) % 2 ^ 128 ∧
      Keeps work s s' := by
  refine WP.append (reduceU_ok hh hb) fun s₁ ⟨w0, w1, w2, w3, w4, ⟨e0, e1, e2, e3, _⟩, hv, k₁⟩ => ?_
  obtain hs1 : s₁.gpr .r0 = st := by rw [k₁.gpr _ (by decide), hs0]
  obtain hw1 : stR st ∈ s₁.wr := by rw [k₁.wr]; exact hw
  have i₀ := St.init s₁
  simp only [RF.of, hs1] at i₀
  rw [addKey]
  simp only [List.cons_append, List.nil_append]
  refine i₀.mov (op2_imm (by decide)) fun t₁ i₁ => ?_
  rf i₁
  refine i₁.mov (op2_imm (by decide)) fun t₂ i₂ => ?_
  rf i₂
  refine i₂.ldr (by decide) (ea hfit (by decide)) (inSt hw1 (by decide)) rfl fun t₃ i₃ => ?_
  rf i₃
  refine i₃.umaal (by decide) fun t₄ g0 c1 q0 i₄ => ?_
  rfu q0 i₄
  refine i₄.ldr (by decide) (ea hfit (by decide)) (inSt hw1 (by decide)) rfl fun t₅ i₅ => ?_
  rf i₅
  refine i₅.umaal (by decide) fun t₆ g1 c2 q1 i₆ => ?_
  rfu q1 i₆
  refine i₆.ldr (by decide) (ea hfit (by decide)) (inSt hw1 (by decide)) rfl fun t₇ i₇ => ?_
  rf i₇
  refine i₇.umaal (by decide) fun t₈ g2 c3 q2 i₈ => ?_
  rfu q2 i₈
  refine i₈.ldr (by decide) (ea hfit (by decide)) (inSt hw1 (by decide)) rfl fun t₉ i₉ => ?_
  rf i₉
  refine i₉.umaal (by decide) fun t₁₀ g3 c4 q3 i₁₀ => WP.block_nil ?_
  rfu q3 i₁₀
  rw [one_toNat, Nat.mul_one, zero_toNat, Nat.add_zero, e0, k₁.mem] at q0
  rw [one_toNat, Nat.mul_one, e1, k₁.mem] at q1
  rw [one_toNat, Nat.mul_one, e2, k₁.mem] at q2
  rw [one_toNat, Nat.mul_one, e3, k₁.mem] at q3
  refine ⟨g0.toNat, g1.toNat, g2.toNat, g3.toNat,
    ⟨congrArg BitVec.toNat (i₁₀.g .r3), congrArg BitVec.toNat (i₁₀.g .r5), congrArg BitVec.toNat (i₁₀.g .r7),
      congrArg BitVec.toNat (i₁₀.g .r10)⟩, ?_, k₁.trans (i₁₀.keeps hs1.symm rfl)⟩
  rw [← hv]
  exact Limbs32.sum_arith g0.isLt g1.isLt g2.isLt g3.isLt q0 q1 q2 q3

/-! ## The multipliers and the stored accumulator -/

omit hfit in
theorem cw_mod4 (m : Mem) (B : Addr) {i : Nat} (hi : i ≠ 0) : (cw m B i).toNat % 4 = 0 := by
  simp only [cw, BitVec.toNat_and, hi, ite_false]
  show (_ &&& 0x0ffffffc) % 4 = 0
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (0x0ffffffc &&& 2 ^ 2 - 1 : Nat) = 0 by decide, Nat.and_zero]

omit hfit in
/-- `rj + rj / 4`, for a word below `2²⁸`. -/
theorem sword_toNat {x : BitVec 32} (h : x.toNat < 2 ^ 28) (h4 : x.toNat % 4 = 0) :
    (x + x >>> 2).toNat = 5 * (x.toNat / 4) := by
  rw [toNat_add_lt (by rw [toNat_shr]; omega_using [h]), toNat_shr]
  omega_using [h4]

/-- The clamped words of `r` in the memory `m` of the state at `B`, as the
multipliers. -/
abbrev kq (m : Mem) (B : Addr) (i : Nat) : Nat := (cw m B i).toNat / 4

theorem setupU_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block setupU) s fun s' =>
      KeyW (State.addr st) (cw s.mem (State.addr st) 0).toNat (kq s.mem (State.addr st) 1)
        (kq s.mem (State.addr st) 2) (kq s.mem (State.addr st) 3) s'.mem ∧
      KeepsF [.r1, .r2] [rR (State.addr st)] s s' := by
  rw [setupU, setupS]
  refine WP.append (clampWords_ok hfit h0 hw) fun s₁ ⟨hm₁, k₁⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < 4, s'.mem.readW (State.addr st + BitVec.ofNat 64 (88 + 4 * i)) 32 =
        cw s.mem (State.addr st) i) ∧
      (∀ i < n, s'.mem.readW (State.addr st + BitVec.ofNat 64 (104 + 4 * i)) 32 =
        cw s.mem (State.addr st) (i + 1) + cw s.mem (State.addr st) (i + 1) >>> 2) ∧
      KeepsF [.r1, .r2] [rR (State.addr st)] s s')
    (fun n s' hn ⟨hl, hs, hk⟩ => ?_) 3 (Nat.le_refl _) s₁
    ⟨hm₁, fun _ h => absurd h (Nat.not_lt_zero _), k₁⟩) fun s' ⟨hl, hs, hk⟩ => ⟨?_, hk⟩
  · obtain hs0 : s'.gpr .r0 = st := by rw [hk.gpr _ (by decide), h0]
    refine wp_ldr (a := State.addr st + BitVec.ofNat 64 (88 + 4 * (n + 1))) (by omega_using [hn])
      (by rw [hs0, show 92 + 4 * n = 88 + 4 * (n + 1) by omega_using []]; exact ea hfit (by omega_using [hn]))
      (by rw [hk.rd, hk.wr]; exact inSt hw (by omega_using [hn])) fun t₁ u₁ => ?_
    refine wp_add (op2_lsr (by decide)) fun t₂ u₂ => ?_
    refine wp_str (a := State.addr st + BitVec.ofNat 64 (104 + 4 * n)) (by omega_using [hn])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hs0]; exact ea hfit (by omega_using [hn]))
      (by rw [u₂.wr, u₁.wr, hk.wr]; exact outSt hw (by omega_using [hn])) fun t₃ u₃ =>
        WP.block_nil ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
    · rw [u₃.mem, readW_writeW_off _ _ _ (by omega_using [hi]) (by omega_using [hn]) (by omega_using [hi, hn]),
        u₂.mem, u₁.mem]
      exact hl i hi
    · rw [u₃.mem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
      · rw [readW_writeW_off _ _ _ (by omega_using [hn, h']) (by omega_using [hn]) (by omega_using [h']),
          u₂.mem, u₁.mem]
        exact hs i h'
      · rw [Mem.readW_writeW_self32, u₂.gpr, u₁.gpr, hl (i + 1) (by omega_using [hn])]
    · refine hk.trans ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u₃.gpr, u₂.other _ hr.1, u₁.other _ hr.1]
      · rw [u₃.mem, u₂.mem, u₁.mem]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (contains_sub _ (by omega_using [hn]) (by omega_using [hn]) (by decide))
      · rw [u₃.rd, u₂.rd, u₁.rd]
      · rw [u₃.wr, u₂.wr, u₁.wr]
      · rw [u₃.sp, u₂.sp, u₁.sp]
  · have c0 := cw_lt s.mem (State.addr st) 0
    have c1 := cw_lt s.mem (State.addr st) 1
    have c2 := cw_lt s.mem (State.addr st) 2
    have c3 := cw_lt s.mem (State.addr st) 3
    have m1 := cw_mod4 s.mem (State.addr st) (i := 1) (by decide)
    have m2 := cw_mod4 s.mem (State.addr st) (i := 2) (by decide)
    have m3 := cw_mod4 s.mem (State.addr st) (i := 3) (by decide)
    exact ⟨congrArg BitVec.toNat (hl 0 (by decide)),
      (congrArg BitVec.toNat (hl 1 (by decide))).trans (by show _ = 4 * (_ / 4); omega_using [m1]),
      (congrArg BitVec.toNat (hl 2 (by decide))).trans (by show _ = 4 * (_ / 4); omega_using [m2]),
      (congrArg BitVec.toNat (hl 3 (by decide))).trans (by show _ = 4 * (_ / 4); omega_using [m3]),
      (congrArg BitVec.toNat (hs 0 (by decide))).trans (sword_toNat c1 m1),
      (congrArg BitVec.toNat (hs 1 (by decide))).trans (sword_toNat c2 m2),
      (congrArg BitVec.toNat (hs 2 (by decide))).trans (sword_toNat c3 m3),
      c0, by show _ / 4 < 2 ^ 26; omega_using [c1], by show _ / 4 < 2 ^ 26; omega_using [c2],
      by show _ / 4 < 2 ^ 26; omega_using [c3]⟩

/-- The registers of the accumulator's words. -/
abbrev wregs : List Reg := [.r3, .r5, .r7, .r10, .r11]

theorem loadAccU_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block loadAccU) s fun s' =>
      WRegs (hwd s.mem (State.addr st) 0) (hwd s.mem (State.addr st) 1) (hwd s.mem (State.addr st) 2)
        (hwd s.mem (State.addr st) 3) (hwd s.mem (State.addr st) 4 % 4) s' ∧ Keeps wregs s s' := by
  have i₀ := St.init s
  simp only [RF.of, h0] at i₀
  rw [loadAccU]
  refine i₀.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₁ i₁ => ?_
  rf i₁
  refine i₁.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₂ i₂ => ?_
  rf i₂
  refine i₂.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₃ i₃ => ?_
  rf i₃
  refine i₃.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₄ i₄ => ?_
  rf i₄
  refine i₄.ldr (by decide) (ea hfit (by decide)) (inSt hw (by decide)) rfl fun s₅ i₅ => ?_
  rf i₅
  refine i₅.and (op2_imm (by decide)) fun s₆ i₆ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact congrArg BitVec.toNat (i₆.g .r3)
  · exact congrArg BitVec.toNat (i₆.g .r5)
  · exact congrArg BitVec.toNat (i₆.g .r7)
  · exact congrArg BitVec.toNat (i₆.g .r10)
  · exact (congrArg BitVec.toNat (i₆.g .r11)).trans (and3_toNat _)
  · exact i₆.keepsL fun r hr => by
      cases r <;> first | rfl | exact h0.symm | exact absurd (by decide) hr

end

/-! ## At a block boundary -/

/-- With `umaal`, at a block boundary: the state at `B` holds the multipliers
of the clamped key `r`, and the accumulator's five words are congruent to
`v` modulo `p`. -/
structure WAcc (B : Addr) (r v : Nat) (s : State) : Prop where
  key : ∃ r0 q1 q2 q3, KeyW B r0 q1 q2 q3 s.mem ∧ r = Limbs32.key r0 q1 q2 q3
  acc : ∃ h0 h1 h2 h3 h4, WRegs h0 h1 h2 h3 h4 s ∧ h4 < topMax ∧ val5 h0 h1 h2 h3 h4 % P = v % P

/-- `WAcc` holds while the accumulator's registers and the multipliers stay. -/
theorem WAcc.keep {B : Addr} {r v : Nat} {s s' : State} (h : WAcc B r v s)
    (hg : ∀ q ∈ wregs, s'.gpr q = s.gpr q)
    (hm : ∀ i < 7, s'.mem.readW (B + BitVec.ofNat 64 (88 + 4 * i)) 32 =
      s.mem.readW (B + BitVec.ofNat 64 (88 + 4 * i)) 32) : WAcc B r v s' := by
  obtain ⟨r0, q1, q2, q3, hk, hr⟩ := h.key
  obtain ⟨h0, h1, h2, h3, h4, ⟨e0, e1, e2, e3, e4⟩, hb, hv⟩ := h.acc
  refine ⟨⟨r0, q1, q2, q3, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hk.b0, hk.b1, hk.b2, hk.b3⟩, hr⟩,
    ⟨h0, h1, h2, h3, h4, ⟨?_, ?_, ?_, ?_, ?_⟩, hb, hv⟩⟩
  · exact (congrArg BitVec.toNat (hm 0 (by decide))).trans hk.w0
  · exact (congrArg BitVec.toNat (hm 1 (by decide))).trans hk.w1
  · exact (congrArg BitVec.toNat (hm 2 (by decide))).trans hk.w2
  · exact (congrArg BitVec.toNat (hm 3 (by decide))).trans hk.w3
  · exact (congrArg BitVec.toNat (hm 4 (by decide))).trans hk.s1
  · exact (congrArg BitVec.toNat (hm 5 (by decide))).trans hk.s2
  · exact (congrArg BitVec.toNat (hm 6 (by decide))).trans hk.s3
  · rw [hg _ (by decide)]; exact e0
  · rw [hg _ (by decide)]; exact e1
  · rw [hg _ (by decide)]; exact e2
  · rw [hg _ (by decide)]; exact e3
  · rw [hg _ (by decide)]; exact e4

theorem WAcc.congr {B : Addr} {r v v' : Nat} {s : State} (h : WAcc B r v s) (hv : v % P = v' % P) :
    WAcc B r v' s := by
  obtain ⟨h0, h1, h2, h3, h4, hw, hb, hv'⟩ := h.acc
  exact ⟨h.key, h0, h1, h2, h3, h4, hw, hb, hv'.trans hv⟩

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The multipliers and the accumulator's words, from the state's key and accumulator. -/
theorem setupU_wacc {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block (setupU ++ loadAccU)) s fun s' =>
      WAcc (State.addr st) (val (rlimb s.mem (State.addr st))) (val (accD s.mem (State.addr st))) s' ∧
      KeepsF (.r1 :: .r2 :: wregs) [rR (State.addr st)] s s' := by
  refine WP.append (setupU_ok hfit h0 hw) fun s₁ ⟨hk₁, k₁⟩ => ?_
  refine WP.mono (loadAccU_ok hfit (by rw [k₁.gpr _ (by decide), h0]) (by rw [k₁.wr]; exact hw))
    fun s₂ ⟨hW, k₂⟩ => ⟨⟨⟨_, _, _, _, by rw [k₂.mem]; exact hk₁, ?_⟩, _, _, _, _, _, hW, ?_, ?_⟩, ?_⟩
  · have m1 := cw_mod4 s.mem (State.addr st) (i := 1) (by decide)
    have m2 := cw_mod4 s.mem (State.addr st) (i := 2) (by decide)
    have m3 := cw_mod4 s.mem (State.addr st) (i := 3) (by decide)
    rw [rlimb, val_mlimb (cw s.mem (State.addr st) 0).isLt (cw s.mem (State.addr st) 1).isLt
      (cw s.mem (State.addr st) 2).isLt (cw s.mem (State.addr st) 3).isLt]
    simp only [Limbs32.key, kq]
    omega_using [m1, m2, m3]
  · show hwd s₁.mem (State.addr st) 4 % 4 < 3 * 2 ^ 30
    omega_arith
  · obtain hf : ∀ i < 5, hwd s₁.mem (State.addr st) i = hwd s.mem (State.addr st) i := fun i hi => by
      simp only [hwd]
      rw [k₁.frame.readW (Region.contains_self _ _)
        (by simpa using key_rR (State.addr st) (d := 4 * i) (by omega_using [hi])) (by decide)]
    rw [hf 0 (by decide), hf 1 (by decide), hf 2 (by decide), hf 3 (by decide), hf 4 (by decide), val_accD]
    rfl
  · exact (k₁.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp).trans
      ((k₂.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).keepsF _)

/-- Absorbing the block at `r1`. -/
theorem absorbU_wacc (pad : Bool) {r v : Nat} {s : State} (hs0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (h : WAcc (State.addr st) r v s)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (absorbU pad)) s fun s' =>
      WAcc (State.addr st) r ((v + msgVal s + if pad then 2 ^ 128 else 0) * r) s' ∧ Keeps work s s' := by
  obtain ⟨r0, q1, q2, q3, hk, hr⟩ := h.key
  obtain ⟨h0, h1, h2, h3, h4, hW, hb, hv⟩ := h.acc
  refine WP.mono (absorbU_ok hfit pad hs0 hw hk hW hb hin) fun s' h' => ?_
  obtain ⟨w0, w1, w2, w3, w4, hW', hb', hv', k'⟩ := h'
  refine ⟨⟨⟨r0, q1, q2, q3, by rw [k'.mem]; exact hk, hr⟩, w0, w1, w2, w3, w4, hW', hb', ?_⟩, k'⟩
  rw [hv', hr, Nat.mul_mod, Nat.add_mod (val5 h0 h1 h2 h3 h4 + msgVal s), Nat.add_mod (val5 h0 h1 h2 h3 h4), hv,
    ← Nat.add_mod v, ← Nat.add_mod, ← Nat.mul_mod]

omit hfit in
/-- The accumulator reduced fully. -/
theorem reduceU_wacc {B : Addr} {r v : Nat} {s : State} (h : WAcc B r v s) :
    WP isa (.block reduceU) s fun s' => ∃ w0 w1 w2 w3 w4, OutW w0 w1 w2 w3 w4 s' ∧
      val5 w0 w1 w2 w3 w4 = v % P ∧ Keeps work s s' := by
  obtain ⟨h0, h1, h2, h3, h4, hW, hb, hv⟩ := h.acc
  refine WP.mono (reduceU_ok hW hb) fun s' h' => ?_
  obtain ⟨w0, w1, w2, w3, w4, hO, hv', k'⟩ := h'
  exact ⟨w0, w1, w2, w3, w4, hO, hv'.trans hv, k'⟩

/-- The tag. -/
theorem tagU_wacc {r v : Nat} {s : State} (hs0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (h : WAcc (State.addr st) r v s) :
    WP isa (.block (reduceU ++ addKey)) s fun s' => ∃ t0 t1 t2 t3,
      ((s'.gpr .r3).toNat = t0 ∧ (s'.gpr .r5).toNat = t1 ∧ (s'.gpr .r7).toNat = t2 ∧ (s'.gpr .r10).toNat = t3) ∧
      t0 + 2 ^ 32 * t1 + 2 ^ 64 * t2 + 2 ^ 96 * t3 =
        (v % P +
          ((s.mem.readW (State.addr st + BitVec.ofNat 64 40) 32).toNat +
            2 ^ 32 * (s.mem.readW (State.addr st + BitVec.ofNat 64 44) 32).toNat +
            2 ^ 64 * (s.mem.readW (State.addr st + BitVec.ofNat 64 48) 32).toNat +
            2 ^ 96 * (s.mem.readW (State.addr st + BitVec.ofNat 64 52) 32).toNat)) % 2 ^ 128 ∧
      Keeps work s s' := by
  obtain ⟨h0, h1, h2, h3, h4, hW, hb, hv⟩ := h.acc
  refine WP.mono (tagU_ok hfit hs0 hw hW hb) fun s' h' => ?_
  obtain ⟨t0, t1, t2, t3, hT, ht, k'⟩ := h'
  exact ⟨t0, t1, t2, t3, hT, by rw [ht, hv], k'⟩

end

end VG.Proof.Poly1305.Arm
