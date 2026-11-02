module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Fn
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The Miller–Rabin round on RISC-V: the core

`core_ok` (`Fn.lean`'s `CoreOk`): the table (`table_ok`: `b^j R mod c` in
table entry `j`), the windows of `E` (`windows_ok`, each window
`RsaKeyGen.wWin` by `window_ok`: four squarings `square_ok`, the selection of
`T_d` by a scan of the whole table `select_ok`, the product and the flag
`update_ok`), then the three last squarings (`last_ok`) leave the mask of
`Proof.MillerRabin.Round.round c b` in `s6`, as on PPC64LE
(`Proof/MillerRabin/PPC64LE/{Table,Window,Exp,Last,Core}.lean`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.MillerRabin.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot slot_sep Arrays)
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)
open VG.Impl.Bignum.RISCV64.ModExp (sqrOp copy)
open VG.Proof.RsaKeyGen (mont_val mont_eq_m1 mont_eq_one wSq wWin wRun wEnd mrE mrSig mrA sigOf win_digit
  shl4_succ)

/-! ## Frames -/

theorem ctx_core : ∀ r ∈ ctxRegs, r ∉ coreRegs := by decide

/-- What every step of the table keeps, from `s₀`: the context, the
constants, only the round's arrays written, only the core's registers. -/
structure Fr (s₀ s : State) (B : Addr) (Z w c : Nat) : Prop where
  ctx : MCtx s B Z w c
  consts : Consts s.mem B w c
  muts : Mut B w s₀.mem s.mem
  keep : Keep coreRegs s₀ s

theorem Fr.step {s₀ s t : State} {B : Addr} {Z w c : Nat} (h : Fr s₀ s B Z w c) {js : List Nat}
    (o : Arrays B w js s.mem t.mem) (hjs : ∀ j ∈ js, j ∈ mutArrs) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ rs, r ∈ coreRegs) : Fr s₀ t B Z w c := by
  have hm : Mut B w s.mem t.mem := Mut.of o hjs
  refine ⟨h.ctx.of k (fun r hr hr' => ctx_core r hr (hrs r hr')) o (fun j hj => ?_),
    h.consts.of_mut hm h.ctx.nw, Mut.trans h.muts hm, (h.keep.trans k).mono fun r hr => ?_⟩
  · have := hjs j hj
    simp only [mutArrs, List.mem_cons, List.not_mem_nil, or_false] at this
    omega_arith
  · rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · exact hrs r hr

theorem Fr.regs {s₀ s t : State} {B : Addr} {Z w c : Nat} (h : Fr s₀ s B Z w c) (hm : t.mem = s.mem)
    {rs : List Reg} (k : Keep rs s t) (hrs : ∀ r ∈ rs, r ∈ coreRegs := by decide) : Fr s₀ t B Z w c :=
  h.step (js := []) (fun x _ => by rw [hm]) (fun _ h => absurd h List.not_mem_nil) k hrs

/-- An array other than the one written keeps its number. -/
theorem aout {B : Addr} {w o j : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * w) m m') (hj : j < 28)
    (hne : j ≠ o) (hn : B.toNat + slot w 28 ≤ 2 ^ 64) : A m' B w j = A m B w j :=
  arr_eq (arr1 h (by omega_arith)) hj (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith) hn

/-! ## The table -/

theorem entry_addr (B : Addr) (w j : Nat) :
    (BitVec.ofNat 64 j + BitVec.ofNat 64 11) * BitVec.ofNat 64 (8 * (w + 2)) + off B (slot w 0) =
      off B (slot w (11 + j)) := by
  simp only [off, slot, Impl.Bignum.hdrBytes, Nat.zero_mul, Nat.add_zero]
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul, Nat.add_comm 11 j, BitVec.ofNat_add 256]
  ac_rfl

/-- `entry rd rj`: the base of table entry `j` (in `rj`) into `rd`. -/
theorem entry_ok {s : State} {B : Addr} {Z w c j : Nat} (h : MCtx s B Z w c) {rd rj : Reg}
    (hd : rd = .a2 ∧ rj = .s11 ∨ rd = .a5 ∧ rj = .a1) (hj : s.gpr rj = BitVec.ofNat 64 j) :
    WP isa (.block (entry rd rj)) s fun t =>
      (t.gpr rd = off B (slot w (11 + j)) ∧ t.mem = s.mem) ∧ Keep [.t2, rd] s t := by
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold entry aTab
    brun [hj, h.s5, h.a7, entry_addr]

/-- `toEntry a`: table entry `j` (in `s11`) := array `a`. -/
theorem toEntry_ok {s : State} {B : Addr} {Z w c j : Nat} (h : MCtx s B Z w c)
    (h11 : s.gpr .s11 = BitVec.ofNat 64 j) (hj : j < 16) {a : Nat} (ha : a < 11) :
    WP isa (toEntry a) s fun t =>
      (A t.mem B w (11 + j) = A s.mem B w a ∧ Outside B (slot w (11 + j)) (8 * w) s.mem t.mem) ∧
        Keep copyRegs s t := by
  unfold toEntry
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Win.ones_ok s) fun t₁ ⟨⟨h4, m1⟩, k1⟩ => ?_
  have c1 := h.regs k1 (by decide) m1
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok (j := j) c1 (.inl ⟨rfl, rfl⟩) (by rw [k1.gpr (by decide), h11]))
    fun t₂ ⟨⟨a2, m2⟩, k2⟩ => ?_
  have c2 := c1.regs k2 (by decide) m2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) c2.a7 c2.s5 a) fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have c3 := c2.regs k3 (by decide) m3
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) c3.a7 c3.s5 a) fun t₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  have c4 := c3.regs k4 (by decide) m4
  have k14 := ((k1.trans k2).trans k3).trans k4
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (sel_ok c4 (b := true) (o := 11 + j) (a := a) (t := a) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by rw [k4.gpr (by decide), k3.gpr (by decide), a2])
    (by rw [k4.gpr (by decide), a5]) a6
    (by rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), h4])) fun t ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  exact ⟨⟨by simpa only [ite_true] using hv, hout⟩, (k14.trans k).mono (by decide)⟩

/-- The table's entries below `j`. -/
def TabUpTo (m : Mem) (B : Addr) (w c b j : Nat) : Prop :=
  ∀ i < j, A m B w (11 + i) = b ^ i % c * 2 ^ (64 * w) % c

/-- The whole table. -/
abbrev TabOK (m : Mem) (B : Addr) (w c b : Nat) : Prop := TabUpTo m B w c b 16

theorem pow_mul_mod (b i c : Nat) : b ^ i % c * (b % c) % c = b ^ (i + 1) % c := by
  rw [← Nat.mul_mod, Nat.pow_succ]

/-- The table, from `b R mod c` in array 5 and `R mod c` in array 9; then
`y := R mod c`. -/
theorem table_ok {s : State} {B : Addr} {Z w c b : Nat} (h : MCtx s B Z w c) (hc : Consts s.mem B w c)
    (hc3 : 3 ≤ c) (hodd : c % 2 = 1) (h5 : A s.mem B w 5 = b % c * 2 ^ (64 * w) % c) :
    WP isa table s fun t => Fr s t B Z w c ∧ TabOK t.mem B w c b ∧ A t.mem B w aY = 2 ^ (64 * w) % c := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have f0 : Fr s s B Z w c := ⟨h, hc, fun _ _ => rfl, Keep.refl _ _⟩
  have hn := h.nw
  have hW : aW = 5 := rfl
  unfold table
  refine WP.seq (WP.mono (WP.keep [.s11] (Q := fun t => t.gpr .s11 = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by brun [Pub.pub_li0]) (by rfl) (by rfl)) fun s₁ ⟨⟨a11, m1⟩, k1⟩ => ?_)
  have f1 := f0.regs m1 k1
  refine WP.seq (WP.mono (toEntry_ok f1.ctx a11 (by decide) (a := aOne) (by decide)) fun s₂ ⟨⟨v0, o2⟩, k2⟩ => ?_)
  have f2 := f1.step (arr1 o2 (by omega_arith)) (by decide) k2 (by decide)
  refine WP.seq (WP.mono (WP.keep [.s11] (Q := fun t => t.gpr .s11 = BitVec.ofNat 64 1 ∧ t.mem = s₂.mem)
    (by brun [Pub.pub_li1]) (by rfl) (by rfl)) fun s₃ ⟨⟨b11, m3⟩, k3⟩ => ?_)
  have f3 := f2.regs m3 k3
  refine WP.seq (WP.mono (toEntry_ok f3.ctx b11 (by decide) (a := aW) (by decide)) fun s₄ ⟨⟨v1, o4⟩, k4⟩ => ?_)
  have f4 := f3.step (arr1 o4 (by omega_arith)) (by decide) k4 (by decide)
  refine WP.seq (WP.mono (copy_ok f4.ctx (o := aY) (a := aW) (by decide) (by decide) (by decide))
    fun s₅ ⟨⟨vy, o5⟩, k5⟩ => ?_)
  have f5 := f4.step (arr1 o5 (by omega_arith)) (by decide) k5 (by decide)
  refine WP.seq (WP.mono (WP.keep [.s11] (Q := fun t => t.gpr .s11 = BitVec.ofNat 64 2 ∧ t.mem = s₅.mem)
    (by brun [exec_li]) (by rfl) (by rfl)) fun s₆ ⟨⟨c11, m6⟩, k6⟩ => ?_)
  have f6 := f5.regs m6 k6
  -- array 5 throughout
  have w5_4 : A s₄.mem B w 5 = A s.mem B w 5 := by
    rw [aout o4 (by decide) (by decide) hn, m3, aout o2 (by decide) (by decide) hn, m1]
  have w5 : A s₆.mem B w 5 = A s.mem B w 5 := by
    rw [m6, aout o5 (by decide) (by decide) hn, w5_4]
  -- the first two entries
  have tab2 : TabUpTo s₆.mem B w c b 2 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl
    · rw [m6, aout o5 (by decide) (by decide) hn, aout o4 (by decide) (by decide) hn, m3, v0, m1, hc.one,
        Nat.pow_zero, Nat.mod_eq_of_lt (show 1 < c by omega_arith), Nat.one_mul]
    · rw [m6, aout o5 (by decide) (by decide) hn, v1, m3, aout o2 (by decide) (by decide) hn, m1, hW, h5,
        Nat.pow_one]
  have y6 : A s₆.mem B w aY = b ^ 1 % c * 2 ^ (64 * w) % c := by
    rw [m6, vy, hW, w5_4, h5, Nat.pow_one]
  refine WP.seq (WP.mono (count_loop (n := 14) (cr := .t2) (by decide)
      (fun k t => Fr s t B Z w c ∧ t.gpr .s11 = BitVec.ofNat 64 (2 + k) ∧
        A t.mem B w 5 = A s.mem B w 5 ∧ TabUpTo t.mem B w c b (2 + k) ∧
        A t.mem B w aY = b ^ (1 + k) % c * 2 ^ (64 * w) % c)
      (fun k hk t ⟨ft, t11, t5, ttab, ty⟩ => ?_) ⟨f6, c11, w5, tab2, y6⟩) fun t ⟨ft, _, _, ttab, _⟩ => ?_)
  · have hb5 : A t.mem B w 5 < c := by rw [t5, h5]; exact Nat.mod_lt _ (by omega_arith)
    refine WP.seq (WP.mono (mont_ok ft.ctx (o := aY) (a := aY) (b := aW) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hb5) fun u ⟨⟨cu, hlt, heq, hout⟩, ku⟩ => ?_)
    have fu := ft.step hout (by decide) ku (by decide)
    have uy : A u.mem B w aY = b ^ (2 + k) % c * 2 ^ (64 * w) % c := by
      rw [show 2 + k = (1 + k) + 1 by omega_arith, ← pow_mul_mod]
      exact mont_val hR hlt heq ty (by rw [hW, t5, h5])
    have u11 : u.gpr .s11 = BitVec.ofNat 64 (2 + k) := (ku.gpr (by decide)).trans t11
    refine WP.seq (WP.mono (toEntry_ok fu.ctx u11 (by omega_arith) (a := aY) (by decide))
      fun v ⟨⟨ve, vo⟩, kv⟩ => ?_)
    have fv := fu.step (arr1 vo (by omega_arith)) (by
      simp only [mutArrs, List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_arith) kv (by decide)
    have hend : WP isa (.block [.addi .s11 .s11 1, .addi .t2 .s11 (-16)]) v fun x =>
        (x.gpr .s11 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 ∧
          x.gpr .t2 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 - BitVec.ofNat 64 16 ∧ x.mem = v.mem) ∧
          Keep [.s11, .t2] v x := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [(kv.gpr (r := .s11) (by decide)).trans u11]
    refine WP.mono hend fun x ⟨⟨x11, x2, xm⟩, kx⟩ => ⟨⟨fv.regs xm kx, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [x11, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [xm, aout vo (by decide) (by omega_arith) hn, arr_eq hout (by decide) (by decide) hn, t5]
    · intro i hi
      rw [xm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < 2 + k + 1 by omega_arith) with hi | rfl
      · rw [aout vo (by omega_arith) (by omega_arith) hn, arr_eq hout (by omega_arith)
          (by simp only [aY, List.mem_cons, List.not_mem_nil, or_false]; omega_arith) hn]
        exact ttab i hi
      · rw [ve, uy]
    · rw [xm, aout vo (by decide) (by simp only [aY]; omega_arith) hn, uy, show 1 + (k + 1) = 2 + k by omega_arith]
    · rw [x2, ← BitVec.ofNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
  · refine WP.mono (copy_ok ft.ctx (o := aY) (a := aOne) (by decide) (by decide) (by decide))
      fun u ⟨⟨uy, uo⟩, ku⟩ => ⟨ft.step (arr1 uo (by omega_arith)) (by decide) ku (by decide), fun i hi => ?_, ?_⟩
    · rw [aout uo (by omega_arith) (by simp only [aY]; omega_arith) hn]; exact ttab i hi
    · rw [uy, ft.consts.one]

/-! ## Windows: their frame -/

/-- The arrays a window writes. -/
def winArrs : List Nat := [2, 3, 5, 6]

/-- The registers a window's pieces write, but `s7`. -/
def wRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .s6, .s11]

/-- What the windows keep, from `s₀`: the context, the constants, the table,
only arrays 2, 3, 5 and 6 written, only the core's registers. -/
structure WSt (s₀ t : State) (B : Addr) (Z w c b : Nat) : Prop where
  ctx : MCtx t B Z w c
  consts : Consts t.mem B w c
  tab : TabOK t.mem B w c b
  outs : Arrays B w winArrs s₀.mem t.mem
  keep : Keep coreRegs s₀ t

theorem WSt.step {s₀ s t : State} {B : Addr} {Z w c b : Nat} (h : WSt s₀ s B Z w c b) {js : List Nat}
    (o : Arrays B w js s.mem t.mem) (hjs : ∀ j ∈ js, j ∈ winArrs) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ rs, r ∈ coreRegs) : WSt s₀ t B Z w c b := by
  have hn := h.ctx.nw
  have o' : Arrays B w winArrs s.mem t.mem := o.mono hjs
  have hm : Mut B w s.mem t.mem := Mut.of o' (by decide)
  refine ⟨h.ctx.of k (fun r hr hr' => ctx_core r hr (hrs r hr')) o' (by decide), h.consts.of_mut hm hn,
    fun i hi => ?_, Arrays.trans h.outs o', (h.keep.trans k).mono fun r hr => ?_⟩
  · rw [arr_eq o' (by omega_arith) (by simp only [winArrs, List.mem_cons, List.not_mem_nil, or_false]; omega_arith) hn]
    exact h.tab i hi
  · rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · exact hrs r hr

theorem WSt.regs {s₀ s t : State} {B : Addr} {Z w c b : Nat} (h : WSt s₀ s B Z w c b) (hm : t.mem = s.mem)
    {rs : List Reg} (k : Keep rs s t) (hrs : ∀ r ∈ rs, r ∈ coreRegs := by decide) : WSt s₀ t B Z w c b :=
  h.step (js := []) (fun x _ => by rw [hm]) (fun _ h => absurd h List.not_mem_nil) k hrs

theorem mask_or (p q : Bool) : mask p ||| mask q = mask (p || q) := by cases p <;> cases q <;> decide

theorem mask_and (p q : Bool) : mask p &&& mask q = mask (p && q) := by cases p <;> cases q <;> decide

/-- `square`: `y := y²`, the flag or'ed with `y = −1` (`wSq c true`). -/
theorem square_ok {s₀ s : State} {B : Addr} {Z w c b Y : Nat} {P : Bool} (h : WSt s₀ s B Z w c b)
    (hc3 : 3 ≤ c) (hodd : c % 2 = 1) (hy : A s.mem B w aY = Y * 2 ^ (64 * w) % c)
    (h6 : s.gpr .s6 = mask P) :
    WP isa square s fun t => (WSt s₀ t B Z w c b ∧
      A t.mem B w aY = (wSq c true (Y, P)).1 * 2 ^ (64 * w) % c ∧ (wSq c true (Y, P)).1 < c ∧
      t.gpr .s6 = mask (wSq c true (Y, P)).2) ∧ Keep wRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hn := h.ctx.nw
  unfold square
  refine WP.seq (WP.mono (sqr_ok h.ctx (o := aY) (a := aY) (p := aW) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hy]; exact Nat.mod_lt _ (by omega_arith))) fun u ⟨⟨_, hlt, heq, hout⟩, ku⟩ => ?_)
  have fu := h.step hout (by decide) ku (by decide)
  have uy : A u.mem B w aY = Y * Y % c * 2 ^ (64 * w) % c := mont_val hR hlt heq hy hy
  have u10 : A u.mem B w aMinus = c - 2 ^ (64 * w) % c := by
    rw [arr_eq hout (by decide) (by decide) hn, h.consts.minus]
  refine WP.seq (WP.mono (eqMask_ok fu.ctx (d := .a3) (.inl rfl) (a := aY) (b := aMinus) (by decide) (by decide))
    fun v ⟨⟨v3, vm⟩, kv⟩ => ?_)
  have fv := fu.regs vm kv
  have hblk : WP isa (.block [.logic .or .s6 .s6 .a3]) v fun t =>
      (t.gpr .s6 = v.gpr .s6 ||| v.gpr .a3 ∧ t.mem = v.mem) ∧ Keep [.s6] v t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun
  refine WP.mono hblk fun t ⟨⟨t6, tm⟩, kt⟩ => ⟨⟨fv.regs tm kt, ?_, Nat.mod_lt _ (by omega_arith), ?_⟩, ?_⟩
  · rw [tm, vm, uy]; rfl
  · have e : decide (A u.mem B w aY = A u.mem B w aMinus) = decide (Y * Y % c = c - 1) := by
      rw [uy, u10]
      exact decide_eq_decide.mpr (mont_eq_m1 hR (by omega_arith) (Nat.mod_lt _ (by omega_arith)))
    rw [t6, v3, kv.gpr (r := .s6) (by decide), ku.gpr (r := .s6) (by decide), h6, e, mask_or]
    rfl
  · exact ((ku.trans kv).trans kt).mono (by decide)

/-! ## Selecting `T_d` -/

theorem mask_sub (b : Bool) : BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) = mask b := by
  cases b <;> decide

theorem isDigit_ok {s : State} {j d : Nat} (h1 : s.gpr .a1 = BitVec.ofNat 64 j)
    (h11 : s.gpr .s11 = BitVec.ofNat 64 d) (hj : j < 16) (hd : d < 16) :
    WP isa (.block isDigit) s fun t => (t.gpr .s4 = mask (decide (j = d)) ∧ t.mem = s.mem) ∧
      Keep [.t2, .t3, .s4] s t := by
  have hx : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    exact Nat.xor_lt_two_pow (by omega_arith) (by omega_arith)
  have he : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0) ↔ j = d := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)] at this
    · rintro rfl; rfl
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold isDigit
  brun [h1, h11, Win.sub1_sign hx, Pub.pub_li0]
  rw [← mask_sub]
  by_cases e : j = d
  · simp [e]
  · simp [e, show ¬ (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0#64) from fun h => e (he.mp h)]

/-- The registers a choice of an entry writes. -/
def pickRegs : List Reg := [.t2, .t3, .s4, .a5, .a6, .a2, .a0, .t4, .t5, .s2, .s3]

/-- Array `o := j = d ? T_j : [t]`, for `j` in `a1` and `d` in `s11`. -/
theorem pick_ok {s : State} {B : Addr} {Z w c j d : Nat} (h : MCtx s B Z w c)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 j) (h11 : s.gpr .s11 = BitVec.ofNat 64 d) (hj : j < 16) (hd : d < 16)
    {o t : Nat} (hot : o = 3 ∧ t = 5 ∨ o = 5 ∧ t = 3) :
    WP isa (.seq (.block (isDigit ++ entry .a5 .a1 ++ base .a6 t ++ base .a2 o)) selectAcc64) s
      fun s' => (A s'.mem B w o = (if j = d then A s.mem B w (11 + j) else A s.mem B w t) ∧
        Outside B (slot w o) (8 * w) s.mem s'.mem) ∧ Keep pickRegs s s' := by
  have ho : o < 28 := by omega_arith
  have ht : t < 28 := by omega_arith
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (isDigit_ok h1 h11 hj hd) fun t₁ ⟨⟨h4, m1⟩, k1⟩ => ?_
  have e1 := h.regs k1 (by decide) m1
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok (j := j) e1 (.inr ⟨rfl, rfl⟩) (by rw [k1.gpr (by decide), h1]))
    fun t₂ ⟨⟨a5, m2⟩, k2⟩ => ?_
  have e2 := e1.regs k2 (by decide) m2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) e2.a7 e2.s5 t) fun t₃ ⟨⟨a6, m3⟩, k3⟩ => ?_
  have e3 := e2.regs k3 (by decide) m3
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) e3.a7 e3.s5 o) fun t₄ ⟨⟨a2, m4⟩, k4⟩ => ?_
  have e4 := e3.regs k4 (by decide) m4
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (sel_ok e4 (b := decide (j = d)) (o := o) (a := 11 + j) (t := t) ho (by omega_arith) ht
      (by omega_arith) (by omega_arith) a2
      (by rw [k4.gpr (by decide), k3.gpr (by decide), a5])
      (by rw [k4.gpr (by decide), a6])
      (by rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), h4]))
    fun s' ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  refine ⟨⟨by rw [hv]; by_cases e : j = d <;> simp [e], hout⟩, ?_⟩
  exact ((((k1.trans k2).trans k3).trans k4).trans k).mono (by decide)

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a b) s fun t => WP isa c t Q) : WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨_, _, he, _, _, he', hq⟩ := h
  cases he with
  | seq e1 e2 => exact ⟨_, _, .seq e1 (.seq e2 he'), hq⟩

theorem wp_seq_inv {a b : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq a b) s Q) :
    WP isa a s fun t => WP isa b t Q := by
  obtain ⟨_, _, he, hq⟩ := h
  cases he with
  | seq e1 e2 => exact ⟨_, _, e1, _, _, e2, hq⟩

theorem wp_block_prefix_seq {l₁ l₂ : List Instr} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.block l₁) s fun t => WP isa (.seq (.block l₂) c) t Q) :
    WP isa (.seq (.block (l₁ ++ l₂)) c) s Q := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  exact WP.mono h fun _ h' => wp_seq_inv h'

/-- The registers the selection writes. -/
def selectRegs : List Reg := pickRegs ++ [.a1]

/-- `select`: array 5 := `T_d`, for `d` in `s11`; only arrays 3 and 5 change. -/
theorem select_ok {s : State} {B : Addr} {Z w c d : Nat} (h : MCtx s B Z w c)
    (h11 : s.gpr .s11 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa select s fun t =>
      (A t.mem B w 5 = A s.mem B w (11 + d) ∧ Arrays B w [3, 5] s.mem t.mem ∧ MCtx t B Z w c) ∧
        Keep selectRegs s t := by
  have hn := h.nw
  have ch_arr : ∀ {m m' : Mem}, Arrays B w [3, 5] m m' → ∀ j < 28, j ≠ 3 → j ≠ 5 → A m' B w j = A m B w j :=
    fun hc j hj h3 h5 => arr_eq hc hj (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith) hn
  have ch3 : ∀ {m m' : Mem}, Outside B (slot w 3) (8 * w) m m' → Arrays B w [3, 5] m m' := fun o =>
    (arr1 o (by omega_arith)).mono (by simp)
  have ch5 : ∀ {m m' : Mem}, Outside B (slot w 5) (8 * w) m m' → Arrays B w [3, 5] m m' := fun o =>
    (arr1 o (by omega_arith)).mono (by simp)
  unfold select
  have hpre : WP isa (.block [.li .a1 0]) s fun t => (t.gpr .a1 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) ∧
      Keep [.a1] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [Pub.pub_li0]
  refine WP.seq (WP.mono hpre fun t₀ ⟨⟨a1, m0⟩, k0⟩ => ?_)
  let I : Nat → State → Prop := fun k t => MCtx t B Z w c ∧ t.gpr .s11 = BitVec.ofNat 64 d ∧
    t.gpr .a1 = BitVec.ofNat 64 (2 * k) ∧
    A t.mem B w 5 = (if d < 2 * k then A s.mem B w (11 + d) else A s.mem B w 5) ∧
    Arrays B w [3, 5] s.mem t.mem ∧ Keep selectRegs s t
  refine WP.mono (count_loop (n := 8) (cr := .t2) (by decide) I (fun k hk t ⟨et, t11, t1, t5, tout, kt⟩ => ?_)
    ⟨h.regs k0 (by decide) m0, by rw [k0.gpr (by decide), h11], a1, (by rw [m0]; simp),
      (by rw [m0]; exact fun _ _ => rfl), k0.mono (by decide)⟩)
    fun t ⟨ct, _, _, t5, tout, kt⟩ =>
      ⟨⟨by rw [t5, ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))], tout, ct⟩, kt⟩
  -- The first entry of the pair, into array 3.
  refine wp_seq_assoc (WP.mono (pick_ok et t1 t11 (by omega_arith) hd (o := aT) (t := aW) (by simp [aT, aW]))
    fun u ⟨⟨u3, uo⟩, ku⟩ => ?_)
  have eu := et.of ku (by decide) (arr1 uo (by omega_arith)) (by decide)
  -- The second, into array 5.
  rw [show ([.addi .a1 .a1 1] ++ isDigit ++ entry .a5 .a1 ++ base .a6 aT ++ base .a2 aW) =
      [.addi .a1 .a1 1] ++ (isDigit ++ entry .a5 .a1 ++ base .a6 aT ++ base .a2 aW) by
    simp only [List.append_assoc]]
  refine wp_seq_assoc (wp_block_prefix_seq ?_)
  have hinc : WP isa (.block [.addi .a1 .a1 1]) u fun v =>
      (v.gpr .a1 = BitVec.ofNat 64 (2 * k + 1) ∧ v.mem = u.mem) ∧ Keep [.a1] u v := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(ku.gpr (r := .a1) (by decide)).trans t1, ← BitVec.ofNat_add]
  refine WP.mono hinc fun v ⟨⟨v1, vm⟩, kv⟩ => ?_
  have ev := eu.regs kv (by decide) vm
  refine (WP.mono (pick_ok ev v1 (by rw [kv.gpr (by decide), ku.gpr (by decide), t11])
    (by omega_arith) hd (o := aW) (t := aT) (by simp [aT, aW])) fun x ⟨⟨x5, xo⟩, kx⟩ => ?_)
  have ex := ev.of kx (by decide) (arr1 xo (by omega_arith)) (by decide)
  have hend : WP isa (.block [.addi .a1 .a1 1, .addi .t2 .a1 (-16)]) x fun y =>
      (y.gpr .a1 = BitVec.ofNat 64 (2 * (k + 1)) ∧
        y.gpr .t2 = BitVec.ofNat 64 (2 * (k + 1)) - BitVec.ofNat 64 16 ∧ y.mem = x.mem) ∧ Keep [.a1, .t2] x y := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(kx.gpr (r := .a1) (by decide)).trans v1, ← BitVec.ofNat_add,
      show 2 * k + 1 + 1 = 2 * (k + 1) by omega_arith]
  have Cx : Arrays B w [3, 5] s.mem x.mem := Arrays.trans (Arrays.trans tout (ch3 uo)) (by rw [← vm]; exact ch5 xo)
  refine WP.mono hend fun y ⟨⟨y1, y2, ym⟩, ky⟩ => ⟨⟨ex.regs ky (by decide) ym, by
    rw [ky.gpr (by decide), kx.gpr (by decide), kv.gpr (by decide), ku.gpr (by decide), t11],
    y1, ?_, by rw [ym]; exact Cx, ?_⟩, ?_⟩
  · show A y.mem B w 5 = _
    rw [ym, show (5 : Nat) = aW from rfl, x5, vm, u3, show aW = 5 from rfl, t5,
      ch_arr (Arrays.trans tout (ch3 uo)) (11 + (2 * k + 1)) (by omega_arith) (by omega_arith) (by omega_arith),
      ch_arr tout (11 + 2 * k) (by omega_arith) (by omega_arith) (by omega_arith)]
    rcases (show d < 2 * k ∨ d = 2 * k ∨ d = 2 * k + 1 ∨ 2 * k + 1 < d by omega_arith) with hc | rfl | rfl | hc
    · simp [hc, show d < 2 * (k + 1) by omega_arith, show ¬ 2 * k + 1 = d by omega_arith,
        show ¬ 2 * k = d by omega_arith]
    · simp [show 2 * k < 2 * (k + 1) by omega_arith]
    · simp [show 2 * k + 1 < 2 * (k + 1) by omega_arith]
    · simp [show ¬ d < 2 * k by omega_arith, show ¬ d < 2 * (k + 1) by omega_arith,
        show ¬ 2 * k + 1 = d by omega_arith, show ¬ 2 * k = d by omega_arith]
  · exact (kt.trans ((((ku.trans kv).trans kx).trans ky))).mono (by decide)
  · rw [y2, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

/-! ## The flag after a window -/

theorem upd_arith (p P z : Bool) :
    mask P ^^^ ((mask p ^^^ mask P) &&& mask z) = mask (if z then p else P) := by
  cases p <;> cases P <;> cases z <;> decide

/-- `0 − (0 <u x)`: the mask of `x ≠ 0`. -/
theorem neg_mask (x : BitVec 64) :
    BitVec.ofNat 64 0 - (if BitVec.ofNat 64 0 < x then (1 : BitVec 64) else 0) = mask (decide (x ≠ 0)) := by
  by_cases hx : x = 0
  · subst hx; decide
  · have hlt : BitVec.ofNat 64 0 < x := by
      rw [BitVec.lt_def]
      exact Nat.pos_of_ne_zero fun h' => hx (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [hlt, ↓reduceIte, ne_eq, hx, not_false_eq_true, decide_true]
    decide

theorem nz_mask {d : Nat} (hd : d < 16) : decide (BitVec.ofNat 64 d ≠ 0) = decide (d ≠ 0) := by
  apply decide_eq_decide.mpr
  constructor
  · intro h e; exact h (by rw [e]; rfl)
  · intro h e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    exact h this

/-- The registers the update of the flag writes. -/
def updRegs : List Reg := [.a3, .a4, .t2, .t3, .s6] ++ eqRegs

/-- `update`: after `y := y T_d`, `P := d ≠ 0 ? (y = 1 ∨ y = −1) : P`. -/
theorem update_ok {s : State} {B : Addr} {Z w c Y d : Nat} {P : Bool} (h : MCtx s B Z w c)
    (hc : Consts s.mem B w c) (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hy : A s.mem B w aY = Y * 2 ^ (64 * w) % c) (hY : Y < c) (h6 : s.gpr .s6 = mask P)
    (h11 : s.gpr .s11 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa update s fun t =>
      (t.gpr .s6 = mask (if d = 0 then P else decide (Y = 1) || decide (Y = c - 1)) ∧ t.mem = s.mem) ∧
        Keep updRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold update
  refine WP.seq (WP.mono (eqMask_ok h (d := .a3) (.inl rfl) (a := aY) (b := aMinus) (by decide) (by decide))
    fun u ⟨⟨u3, um⟩, ku⟩ => ?_)
  have eu := h.regs ku (by decide) um
  refine WP.seq (WP.mono (eqMask_ok eu (d := .a4) (.inr rfl) (a := aY) (b := aOne) (by decide) (by decide))
    fun v ⟨⟨v4, vm⟩, kv⟩ => ?_)
  have hblk : WP isa (.block [.logic .or .a3 .a3 .a4, .li .t2 0, .sltu .t3 .t2 .s11, .sub .t3 .t2 .t3,
      .logic .xor .a3 .a3 .s6, .logic .and .a3 .a3 .t3, .logic .xor .s6 .s6 .a3]) v
      fun t => (t.gpr .s6 = v.gpr .s6 ^^^ (((v.gpr .a3 ||| v.gpr .a4) ^^^ v.gpr .s6) &&&
        (BitVec.ofNat 64 0 - (if BitVec.ofNat 64 0 < v.gpr .s11 then (1 : BitVec 64) else 0))) ∧ t.mem = v.mem) ∧
        Keep [.a3, .t2, .t3, .s6] v t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [Pub.pub_li0]
  refine WP.mono hblk fun t ⟨⟨t6, tm⟩, kt⟩ => ⟨⟨?_, by rw [tm, vm, um]⟩, ((ku.trans kv).trans kt).mono
    (by decide)⟩
  have e1 : decide (A s.mem B w aY = A s.mem B w aMinus) = decide (Y = c - 1) := by
    rw [hy, hc.minus]
    exact decide_eq_decide.mpr (mont_eq_m1 hR (by omega_arith) hY)
  have e2 : decide (A u.mem B w aY = A u.mem B w aOne) = decide (Y = 1) := by
    rw [um, hy, hc.one]
    exact decide_eq_decide.mpr (mont_eq_one hR (by omega_arith) hY)
  rw [t6, kv.gpr (r := .s6) (by decide), ku.gpr (r := .s6) (by decide), h6, kv.gpr (r := .a3) (by decide), u3, v4,
    kv.gpr (r := .s11) (by decide), ku.gpr (r := .s11) (by decide), h11, neg_mask, nz_mask hd, e1, e2, mask_or,
    upd_arith]
  by_cases e : d = 0 <;> simp [e, Bool.or_comm]

/-! ## A window -/

theorem montR_win {B : Addr} {w : Nat} {m m' : Mem} (h : Arrays B w [2, 3, aY] m m') :
    Arrays B w winArrs m m' := h.mono (by decide)

/-- A window: `RsaKeyGen.wWin` for the digit at the top of `s7`. -/
theorem window_ok {s₀ s : State} {B : Addr} {Z w c b Y : Nat} {P : Bool} {V : BitVec 64}
    (h : WSt s₀ s B Z w c b) (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hy : A s.mem B w aY = Y * 2 ^ (64 * w) % c) (h6 : s.gpr .s6 = mask P) (h7 : s.gpr .s7 = V) :
    WP isa window s fun t => (WSt s₀ t B Z w c b ∧
      A t.mem B w aY = (wWin c b (V >>> 60).toNat (Y, P)).1 * 2 ^ (64 * w) % c ∧
      (wWin c b (V >>> 60).toNat (Y, P)).1 < c ∧
      t.gpr .s6 = mask (wWin c b (V >>> 60).toNat (Y, P)).2 ∧ t.gpr .s7 = V <<< 4) ∧
      Keep (.s7 :: wRegs) s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hn := h.ctx.nw
  unfold window
  refine WP.seq (WP.mono (square_ok h hc3 hodd hy h6) fun t₁ ⟨⟨f1, y1, _, p1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (square_ok f1 hc3 hodd y1 p1) fun t₂ ⟨⟨f2, y2, _, p2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (square_ok f2 hc3 hodd y2 p2) fun t₃ ⟨⟨f3, y3, _, p3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (square_ok f3 hc3 hodd y3 p3) fun t₄ ⟨⟨f4, y4, _, p4⟩, k4⟩ => ?_)
  have k14 := ((k1.trans k2).trans k3).trans k4
  have h4 : t₄.gpr .s7 = V := by rw [k14.gpr (by decide), h7]
  have hdl : (V >>> 60).toNat < 16 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := V.isLt
    omega_arith
  have hdig : WP isa (.block [.shift .srl .d .s11 .s7 60]) t₄ fun u =>
      (u.gpr .s11 = BitVec.ofNat 64 (V >>> 60).toNat ∧ u.mem = t₄.mem) ∧ Keep [.s11] t₄ u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono hdig fun u ⟨⟨u11, um⟩, ku⟩ => ?_)
  have fu := f4.regs um ku
  refine WP.seq (WP.mono (select_ok fu.ctx u11 hdl) fun v ⟨⟨v5, vout, vc⟩, kv⟩ => ?_)
  have fv := fu.step vout (by decide) kv (by decide)
  have vy : A v.mem B w aY = (wSq c true (wSq c true (wSq c true (wSq c true (Y, P))))).1 * 2 ^ (64 * w) % c := by
    rw [arr_eq vout (by decide) (by decide) hn, um, y4]
  have vd : A v.mem B w 5 = b ^ (V >>> 60).toNat % c * 2 ^ (64 * w) % c := by
    rw [v5]; exact fu.tab _ hdl
  refine WP.seq (WP.mono (mont_ok fv.ctx (o := aY) (a := aY) (b := aW) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show A v.mem B w 5 < c; rw [vd]; exact Nat.mod_lt _ (by omega_arith)))
    fun x ⟨⟨_, xlt, xeq, xout⟩, kx⟩ => ?_)
  have fx := fv.step (montR_win xout) (by decide) kx (by decide)
  have xy : A x.mem B w aY = (wWin c b (V >>> 60).toNat (Y, P)).1 * 2 ^ (64 * w) % c := by
    simp only [wWin, VG.Proof.Bignum.powMod_eq]
    exact mont_val hR xlt xeq vy vd
  have xl : (wWin c b (V >>> 60).toNat (Y, P)).1 < c := by
    simp only [wWin]; exact Nat.mod_lt _ (by omega_arith)
  have x6 : x.gpr .s6 = mask (wSq c true (wSq c true (wSq c true (wSq c true (Y, P))))).2 := by
    rw [kx.gpr (r := .s6) (by decide), kv.gpr (r := .s6) (by decide), ku.gpr (r := .s6) (by decide), p4]
  have x11 : x.gpr .s11 = BitVec.ofNat 64 (V >>> 60).toNat := by
    rw [kx.gpr (r := .s11) (by decide), kv.gpr (r := .s11) (by decide), u11]
  refine WP.seq (WP.mono (update_ok fx.ctx fx.consts hc3 hodd xy xl x6 x11 hdl) fun y ⟨⟨y6, ym⟩, ky⟩ => ?_)
  have fy := fx.regs ym ky
  have y7 : y.gpr .s7 = V := by
    rw [ky.gpr (by decide), kx.gpr (by decide), kv.gpr (by decide), ku.gpr (by decide), h4]
  have hsh : WP isa (.block [.shift .sll .d .s7 .s7 4]) y fun z =>
      (z.gpr .s7 = V <<< 4 ∧ z.mem = y.mem) ∧ Keep [.s7] y z := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [y7]
  refine WP.mono hsh fun z ⟨⟨z7, zm⟩, kz⟩ => ⟨⟨fy.regs zm kz, by rw [zm, ym, xy], xl, ?_, z7⟩, ?_⟩
  · rw [kz.gpr (by decide), y6]
    rfl
  · exact (((((((k14.trans ku).trans kv).trans kx).trans ky).trans kz)).mono (by decide))

/-! ## The windows of the exponent -/

/-- The state of the windows after the top `j` of the `16 w` windows. -/
structure ExpAt (s₀ t : State) (B : Addr) (Z w c b j : Nat) : Prop where
  ws : WSt s₀ t B Z w c b
  y : A t.mem B w aY = (wRun c b (mrE c) (16 * w) j).1 * 2 ^ (64 * w) % c
  lt : (wRun c b (mrE c) (16 * w) j).1 < c
  p : t.gpr .s6 = mask (wRun c b (mrE c) (16 * w) j).2

/-- The inner loop: the 16 windows of the word `V`, from window `16 k`. -/
theorem inner_ok {s₀ u : State} {B : Addr} {Z w c b k : Nat} {V : BitVec 64} (hk : k < w)
    (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hV : V.toNat = mrE c / 2 ^ (64 * (w - 1 - k)) % 2 ^ 64)
    (h : ExpAt s₀ u B Z w c b (16 * k)) (h7 : u.gpr .s7 = V) (h10 : u.gpr .s10 = BitVec.ofNat 64 16) :
    WP isa (.loop (.seq window (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10)) u fun t =>
      ExpAt s₀ t B Z w c b (16 * (k + 1)) ∧ t.gpr .s8 = u.gpr .s8 ∧ t.gpr .s9 = u.gpr .s9 := by
  let I : Nat → State → Prop := fun i t => ExpAt s₀ t B Z w c b (16 * k + i) ∧ t.gpr .s7 = V <<< (4 * i) ∧
    t.gpr .s8 = u.gpr .s8 ∧ t.gpr .s9 = u.gpr .s9
  refine WP.mono (wp_countdown (body := .seq window (.block [.addi .s10 .s10 (-1)])) (cnt := .s10) (N := 16)
    (by decide) (by decide) I (fun i hi t ⟨ht, t7, t8, t9⟩ _ => ?_) ⟨by simpa using h, by simp [h7], rfl, rfl⟩ h10)
    fun t ⟨ht, _, t8, t9⟩ => ⟨by rw [show 16 * (k + 1) = 16 * k + 16 by omega_arith]; exact ht, t8, t9⟩
  refine WP.seq (WP.mono (window_ok ht.ws hc3 hodd ht.y ht.p t7) fun x ⟨⟨hx, xy, xl, x6, x7⟩, kx⟩ => ?_)
  have hd : ((V <<< (4 * i)) >>> 60).toNat = mrE c / 16 ^ (16 * w - 1 - (16 * k + i)) % 16 := by
    rw [win_digit (k := w - k) (by rw [hV, show w - k - 1 = w - 1 - k by omega_arith]) hi]
    rw [show 16 * (w - k - 1) + (15 - i) = 16 * w - 1 - (16 * k + i) by omega_arith]
  have hrun : wRun c b (mrE c) (16 * w) (16 * k + i + 1) =
      wWin c b ((V <<< (4 * i)) >>> 60).toNat
        ((wRun c b (mrE c) (16 * w) (16 * k + i)).1, (wRun c b (mrE c) (16 * w) (16 * k + i)).2) := by
    rw [hd, wRun]
  have hsub : WP isa (.block [.addi .s10 .s10 (-1)]) x fun z =>
      (z.gpr .s10 = x.gpr .s10 - BitVec.ofNat 64 1 ∧ z.mem = x.mem) ∧ Keep [.s10] x z := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun
  refine WP.mono hsub fun z ⟨⟨z10, zm⟩, kz⟩ => ⟨⟨⟨hx.regs zm kz, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [zm, xy, ← hrun]; rfl
  · rw [← hrun] at xl; exact xl
  · rw [kz.gpr (by decide), x6, ← hrun]; rfl
  · rw [kz.gpr (by decide), x7, shl4_succ]
  · rw [kz.gpr (by decide), kx.gpr (by decide), t8]
  · rw [kz.gpr (by decide), kx.gpr (by decide), t9]
  · rw [z10, kx.gpr (by decide)]

theorem shl3_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem off_sub8 (B : Addr) (y : Nat) : off B (y + 8) - BitVec.ofNat 64 8 = off B y := by
  rw [← off_add, BitVec.add_sub_cancel]

/-- The windows of `E`: `RsaKeyGen.wRun` over all `16 w` windows, from
`y = R mod c` (`1`) and a clear flag. -/
theorem windows_ok {s : State} {B : Addr} {Z w c b : Nat} (h : WSt s s B Z w c b) (hc3 : 3 ≤ c)
    (hodd : c % 2 = 1) (hy : A s.mem B w aY = 2 ^ (64 * w) % c) :
    WP isa windows s fun t => ExpAt s t B Z w c b (16 * w) := by
  have hw := h.ctx.w4
  have hw' := h.ctx.w128
  have hZ := h.ctx.hZ
  have hE := slot_lt (w := w) (show aE < 28 by decide)
  have alE := slot_al w aE
  unfold windows
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.li .s6 0, .addi .s9 .t0 0]) s fun t =>
      (t.gpr .s6 = mask false ∧ t.gpr .s9 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.s6, .s9] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [Pub.pub_li0, h.ctx.t0, BitVec.add_zero]
    all_goals rfl
  refine WP.mono h1 fun t₁ ⟨⟨a6, a9, m1⟩, k1⟩ => ?_
  have f1 := h.regs m1 k1
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .s8) (by decide) f1.ctx.a7 f1.ctx.s5 aE) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have f2 := f1.regs m2 k2
  have h3 : WP isa (.block [.shift .sll .d .t2 .t0 3, .add .s8 .s8 .t2]) t₂ fun t =>
      (t.gpr .s8 = off B (slot w aE + 8 * w) ∧ t.mem = t₂.mem) ∧ Keep [.t2, .s8] t₂ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [f2.ctx.t0, a8, shl3_ofNat w]
  refine WP.mono h3 fun t₃ ⟨⟨b8, m3⟩, k3⟩ => ?_
  have f3 := f2.regs m3 k3
  have e0 : ExpAt s t₃ B Z w c b (16 * 0) :=
    ⟨f3, by rw [m3, m2, m1, hy]; simp [wRun], by simp [wRun]; omega_arith,
      by rw [k3.gpr (by decide), k2.gpr (by decide), a6]; rfl⟩
  have c9 : t₃.gpr .s9 = BitVec.ofNat 64 w := by rw [k3.gpr (by decide), k2.gpr (by decide), a9]
  let I : Nat → State → Prop := fun k t => ExpAt s t B Z w c b (16 * k) ∧
    t.gpr .s8 = off B (slot w aE + 8 * (w - k))
  refine WP.mono (wp_countdown (cnt := .s9) (N := w) (by omega_arith) (by omega_arith) I
    (fun k hk t ⟨ht, t8⟩ _ => ?_) ⟨e0, by rw [b8, Nat.sub_zero]⟩ c9) fun t ⟨ht, _⟩ => ht
  -- the next word
  have hy8 : slot w aE + 8 * (w - k) = (slot w aE + 8 * (w - 1 - k)) + 8 := by omega_arith
  have hs := ht.ws.ctx.scr
  have hld : WP isa (.block [.addi .s8 .s8 (-8), .load .d .s7 .s8 0, .li .s10 16]) t fun u =>
      (u.gpr .s8 = off B (slot w aE + 8 * (w - 1 - k)) ∧
        u.gpr .s7 = Mont.word t.mem B (slot w aE + 8 * (w - 1 - k)) ∧ u.gpr .s10 = BitVec.ofNat 64 16 ∧
        u.mem = t.mem) ∧ Keep [.s7, .s8, .s10] t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li, t8, hy8, off_sub8, hs.ld (show slot w aE + 8 * (w - 1 - k) + 8 ≤ Z by omega_arith),
      hs.al8 (show slot w aE + 8 * (w - 1 - k) + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.seq (WP.mono hld fun u ⟨⟨u8, u7, u10, um⟩, ku⟩ => ?_)
  have eu : ExpAt s u B Z w c b (16 * k) :=
    ⟨ht.ws.regs um ku, by rw [um]; exact ht.y, ht.lt, by rw [ku.gpr (by decide)]; exact ht.p⟩
  have hV : (Mont.word t.mem B (slot w aE + 8 * (w - 1 - k))).toNat = mrE c / 2 ^ (64 * (w - 1 - k)) % 2 ^ 64 := by
    rw [← VG.Proof.Mont.wordsVal_word (n := w) (show w - 1 - k < w by omega_arith)]
    have := ht.ws.consts.e
    simp only [A] at this
    rw [this]
  refine WP.seq (WP.mono (inner_ok hk hc3 hodd hV eu u7 u10) fun x ⟨ex, x8, x9⟩ => ?_)
  have hsub : WP isa (.block [.addi .s9 .s9 (-1)]) x fun z =>
      (z.gpr .s9 = x.gpr .s9 - BitVec.ofNat 64 1 ∧ z.mem = x.mem) ∧ Keep [.s9] x z := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun
  refine WP.mono hsub fun z ⟨⟨z9, zm⟩, kz⟩ => ⟨⟨⟨ex.ws.regs zm kz, by rw [zm]; exact ex.y, ex.lt,
    by rw [kz.gpr (by decide)]; exact ex.p⟩, ?_⟩, ?_⟩
  · rw [kz.gpr (by decide), x8, u8, show w - 1 - k = w - (k + 1) by omega_arith]
  · rw [z9, x9, ku.gpr (by decide)]

/-! ## The last squarings -/

/-- `K` of `σ > j`, as `repeat16` builds it. -/
def sigK64 (j : Nat) : BitVec 64 :=
  if j = 1 then 0xDDDDDDDDDDDDDDDD#64 else if j = 2 then 0x9999999999999999#64 else 0x1111111111111111#64

theorem rep1 : repeat16 .t4 .t5 (sigK 1) = [.lui .t4 14#20, .addi .t4 .t4 (-547), .shift .sll .d .t5 .t4 16,
    .logic .or .t4 .t4 .t5, .shift .sll .d .t5 .t4 32, .logic .or .t4 .t4 .t5] := rfl

theorem rep2 : repeat16 .t4 .t5 (sigK 2) = [.lui .t4 10#20, .addi .t4 .t4 (-1639), .shift .sll .d .t5 .t4 16,
    .logic .or .t4 .t4 .t5, .shift .sll .d .t5 .t4 32, .logic .or .t4 .t4 .t5] := rfl

theorem rep3 : repeat16 .t4 .t5 (sigK 3) = [.lui .t4 1#20, .addi .t4 .t4 273, .shift .sll .d .t5 .t4 16,
    .logic .or .t4 .t4 .t5, .shift .sll .d .t5 .t4 32, .logic .or .t4 .t4 .t5] := rfl

/-- `repeat16`: `t4 := K`. -/
theorem repeat16_val (j : Nat) (hj : j = 1 ∨ j = 2 ∨ j = 3) (s : State) :
    WP isa (.block (repeat16 .t4 .t5 (sigK j))) s fun t =>
      (t.gpr .t4 = sigK64 j ∧ t.mem = s.mem) ∧ Keep [.t4, .t5] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  rcases hj with rfl | rfl | rfl
  · rw [rep1]; brun [exec_lui]; decide
  · rw [rep2]; brun [exec_lui]; decide
  · rw [rep3]; brun [exec_lui]; decide

theorem sig_mask (j : Nat) (hj : j = 1 ∨ j = 2 ∨ j = 3) {k : Nat} (hk : k < 64) :
    (BitVec.twoPow 64 k &&& sigK64 j = 0) = ¬ (j < sigOf k) := by
  rcases hj with rfl | rfl | rfl
  · exact VG.Proof.RsaKeyGen.sig_mask1 k hk
  · exact VG.Proof.RsaKeyGen.sig_mask2 k hk
  · exact VG.Proof.RsaKeyGen.sig_mask3 k hk

/-- The mask of `σ > j` from the word after `E`. -/
theorem sig_word {c j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    decide (BitVec.twoPow 64 (mrA c % 64) &&& sigK64 j ≠ 0) = decide (j < mrSig c) := by
  have h := sig_mask j hj (k := mrA c % 64) (Nat.mod_lt _ (by decide))
  rw [VG.Proof.RsaKeyGen.sigOf_mod] at h
  apply decide_eq_decide.mpr
  rw [show mrSig c = sigOf (mrA c) from rfl, ne_eq, h, Decidable.not_not]

/-- A squaring after the windows: `wSq c (σ > j)`. -/
theorem last_ok {s₀ s : State} {B : Addr} {Z w c b Y : Nat} {P : Bool}
    (h : WSt s₀ s B Z w c b) (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hy : A s.mem B w aY = Y * 2 ^ (64 * w) % c) (h6 : s.gpr .s6 = mask P) {j : Nat}
    (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (last j) s fun t => WSt s₀ t B Z w c b ∧
      A t.mem B w aY = (wSq c (decide (j < mrSig c)) (Y, P)).1 * 2 ^ (64 * w) % c ∧
      (wSq c (decide (j < mrSig c)) (Y, P)).1 < c ∧ t.gpr .s6 = mask (wSq c (decide (j < mrSig c)) (Y, P)).2 := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hn := h.ctx.nw
  have hZ := h.ctx.hZ
  have hE := slot_lt (w := w) (show aE < 28 by decide)
  have alE := slot_al w aE
  unfold last
  refine WP.seq (WP.mono (sqr_ok h.ctx (o := aY) (a := aY) (p := aW) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hy]; exact Nat.mod_lt _ (by omega_arith))) fun u ⟨⟨_, hlt, heq, hout⟩, ku⟩ => ?_)
  have fu := h.step hout (by decide) ku (by decide)
  have uy : A u.mem B w aY = Y * Y % c * 2 ^ (64 * w) % c := mont_val hR hlt heq hy hy
  have u10 : A u.mem B w aMinus = c - 2 ^ (64 * w) % c := by
    rw [arr_eq hout (by decide) (by decide) hn, h.consts.minus]
  refine WP.seq (WP.mono (eqMask_ok fu.ctx (d := .a3) (.inl rfl) (a := aY) (b := aMinus) (by decide) (by decide))
    fun v ⟨⟨v3, vm⟩, kv⟩ => ?_)
  have fv := fu.regs vm kv
  simp only [loadL, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) fv.ctx.a7 fv.ctx.s5 aE) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
  have fx := fv.regs xm kx
  have hs := fx.ctx.scr
  rw [WP.block_append_iff]
  have hld : WP isa (.block [.shift .sll .d .t2 .t0 3, .add .t3 .t3 .t2, .load .d .t3 .t3 0]) x fun y =>
      (y.gpr .t3 = Mont.word x.mem B (slot w aE + 8 * w) ∧ y.mem = x.mem) ∧ Keep [.t2, .t3] x y := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fx.ctx.t0, shl3_ofNat w, x3, hs.ld (show slot w aE + 8 * w + 8 ≤ Z by omega_arith),
      hs.al8 (show slot w aE + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hld fun y ⟨⟨y3, ym⟩, ky⟩ => ?_
  have fy := fx.regs ym ky
  rw [WP.block_append_iff]
  refine WP.mono (repeat16_val j hj y) fun z ⟨⟨z4, zm⟩, kz⟩ => ?_
  have fz := fy.regs zm kz
  have hblk : WP isa (.block [.logic .and .t3 .t3 .t4, .li .t2 0, .sltu .t3 .t2 .t3, .sub .t3 .t2 .t3,
      .logic .and .a3 .a3 .t3, .logic .or .s6 .s6 .a3]) z fun t =>
      (t.gpr .s6 = z.gpr .s6 ||| (z.gpr .a3 &&& (BitVec.ofNat 64 0 -
        (if BitVec.ofNat 64 0 < (z.gpr .t3 &&& z.gpr .t4) then (1 : BitVec 64) else 0))) ∧ t.mem = z.mem) ∧
        Keep [.t2, .t3, .a3, .s6] z t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [Pub.pub_li0]
  refine WP.mono hblk fun t ⟨⟨t6, tm⟩, kt⟩ => ⟨fz.regs tm kt, ?_, Nat.mod_lt _ (by omega_arith), ?_⟩
  · rw [tm, zm, ym, xm, vm, uy]; rfl
  · have e : decide (A u.mem B w aY = A u.mem B w aMinus) = decide (Y * Y % c = c - 1) := by
      rw [uy, u10]
      exact decide_eq_decide.mpr (mont_eq_m1 hR (by omega_arith) (Nat.mod_lt _ (by omega_arith)))
    have hl : Mont.word x.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := fx.consts.l
    rw [t6, kz.gpr (r := .s6) (by decide), ky.gpr (r := .s6) (by decide), kx.gpr (r := .s6) (by decide),
      kv.gpr (r := .s6) (by decide), ku.gpr (r := .s6) (by decide), h6,
      kz.gpr (r := .a3) (by decide), ky.gpr (r := .a3) (by decide), kx.gpr (r := .a3) (by decide), v3,
      kz.gpr (r := .t3) (by decide), y3, hl, z4, neg_mask, e, sig_word hj, mask_and, mask_or]
    simp only [wSq, Bool.and_comm]

/-! ## The round -/

/-- `core`: the table, the windows, the three squarings. -/
theorem core_ok : CoreOk := by
  intro s B Z w c b h hc hc3 hodd h5
  have hcw : c < 16 ^ (16 * w) := by
    rw [← h.n, show (16 : Nat) ^ (16 * w) = 2 ^ (64 * w) by
      rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]; congr 1; omega_arith]
    exact wordsVal_lt _ _ _ _
  have hE : mrE c < 16 ^ (16 * w) :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) hcw
  unfold core
  refine WP.seq (WP.mono (table_ok h hc hc3 hodd h5) fun t₁ ⟨f1, tab, y1⟩ => ?_)
  have w1 : WSt t₁ t₁ B Z w c b := ⟨f1.ctx, f1.consts, tab, fun _ _ => rfl, Keep.refl _ _⟩
  refine WP.seq (WP.mono (windows_ok w1 hc3 hodd y1) fun t₂ e2 => ?_)
  refine WP.seq (WP.mono (last_ok e2.ws hc3 hodd e2.y e2.p (j := 1) (by simp)) fun t₃ ⟨w3, y3, _, p3⟩ => ?_)
  refine WP.seq (WP.mono (last_ok w3 hc3 hodd y3 p3 (j := 2) (by simp)) fun t₄ ⟨w4, y4, _, p4⟩ => ?_)
  refine WP.mono (last_ok w4 hc3 hodd y4 p4 (j := 3) (by simp)) fun t ⟨w5, _, _, p5⟩ =>
    ⟨w5.ctx, ?_, Mut.trans f1.muts (Mut.of w5.outs (by decide)),
      (f1.keep.trans w5.keep).mono fun r hr => (List.mem_append.mp hr).elim id id⟩
  rw [p5]
  congr 1
  show (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 = _
  rw [VG.Proof.Ffdh.window_round_eq (W := 16 * w) b hc3 hodd hE, ← VG.Proof.Ffdh.rsa_round_eq b hc3 hodd]
  rfl

end VG.Proof.MillerRabin.RISCV64
