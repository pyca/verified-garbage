module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.WindowPower
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Ffdh.X86.Ops
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Framework.Offset

/-!
# FFDH key generation from the context on i686: the comb

Slot 6 `g^x mod p` by the context's comb (`comb_ok`): Montgomery one, then
for the rows `i` from the context's row count down, one square and the
product with the entry of row `i − 1`'s digit (`step_ok`), which `select`
reads by scanning all 32 entries; the product with one ends it. The loop's
invariant (`CombAt`) is `acc = g^(high x i) R mod p`
(`FixedBaseComb.high_step`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- What the comb writes: its two counters and the context's operations. -/
abbrev combR (len : Nat) : List (Nat × Nat) := (rowsOff, 4) :: (iOff, 4) :: stR len 0

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

theorem combR_fit (h : In Ex base bytes len args s) : ∀ p ∈ combR len, p.1 + p.2 ≤ bytes := by
  have F := stR_fit h (o := 0) (by decide)
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  intro p hp
  simp only [combR, List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · simp only [rowsOff]; omega
  · simp only [iOff]; omega
  · exact F p (by simpa only [stR, List.mem_cons, List.not_mem_nil, or_false] using hp)

/-- A header word of the counters, stored. -/
theorem counter_store (h : In Ex base bytes len args s) {d : Nat} (hd : d = rowsOff ∨ d = iOff) (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun u =>
      In Ex base bytes len args u ∧ Outside base d 4 s.mem u.mem ∧ w32 u.mem base d = (s.gpr r).toNat ∧
      Keeps [] s u ∧ u.zf = s.zf := by
  have nb : numBase = 3336 := rfl
  have hd' : d + 4 ≤ numBase := by rcases hd with rfl | rfl <;> simp only [rowsOff, iOff] <;> omega
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  refine wp_storeS (h.scratch.ea (d := d) (by omega_arith)) (h.scratch.write (d := d) (n := 4) (by omega_arith))
    fun u M => WP.block_nil ?_
  have O : Outside base d 4 s.mem u.mem := by rw [M.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  refine ⟨h.keep (M.keeps []) (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega_arith)), O, ?_, M.keeps [],
    M.zf⟩
  rw [M.mem, w32_write_self]

/-- The row counter down one: ZF at its last row. -/
theorem dec_ok (h : In Ex base bytes len args s) {i : Nat} (hi : 1 ≤ i) (hi' : i < 2 ^ 32)
    (hI : w32 s.mem base iOff = i) :
    WP isa (.block [.mov .eax (.mem (sc iOff)), .alu .sub .eax (.imm 1), .store (sc iOff) .eax]) s fun u =>
      In Ex base bytes len args u ∧ Outside base iOff 4 s.mem u.mem ∧ w32 u.mem base iOff = i - 1 ∧
      Keeps [.eax] s u ∧ u.zf = some (decide (i - 1 = 0)) := by
  have nb : numBase = 3336 := rfl
  refine wp_movS (readW_ok h (d := iOff) (by simp only [iOff]; omega) hI hi') fun s₁ U₁ _ =>
    wp_subZ rfl fun s₂ U₂ z₂ => ?_
  have K₂ : Keeps [.eax] s s₂ := (U₁.keeps.mono (by decide)).widen U₂.keeps
  have m₂ : s₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  have sub : BitVec.ofNat 32 i - 1 = BitVec.ofNat 32 (i - 1) := VG.Proof.Mont.X86.Dynamic.counter_sub hi' hi
  have v₂ : s₂.gpr .eax = BitVec.ofNat 32 (i - 1) := by rw [U₂.gpr, U₁.gpr, sub]
  refine WP.mono (counter_store (h.regs K₂ m₂) (d := iOff) (.inr rfl) .eax) fun u ⟨I, O, W, K, z⟩ =>
    ⟨I, by rw [← m₂]; exact O, ?_, K₂.trans (K.mono (by decide)), ?_⟩
  · rw [W, v₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [z, z₂, U₁.gpr, sub]
    congr 1
    by_cases e : i - 1 = 0
    · simp [e]
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro c
      have := congrArg BitVec.toNat c
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact e this

end

/-! ## What the comb keeps -/

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The wide slots 9 to 19 through the comb's writes. -/
theorem combR_sv (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (combR len)) m m') (R : CallRoom sp base bytes) {j : Nat} (hj9 : 9 ≤ j)
    (hj : j ≤ 19) : sv m' base len .wide j = sv m base len .wide j := by
  have := hi_fit (len := len) hj9 hj
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have T := h.table_fit .wide
  have t16 : te len .wide 16 = te len .wide 0 + 16 * bc len .wide := by simp only [te]; omega
  have nb : numBase = 3336 := rfl
  refine frameR_val32 F R h.scratch.nowrap (by omega) ?_ (combR_fit h)
  intro p hp
  simp only [combR, stR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [rowsOff, iOff] <;> omega

/-- The header's words past the counters through the comb's writes. -/
theorem combR_w32 (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (combR len)) m m') (R : CallRoom sp base bytes) {d : Nat} (hd8 : 8 ≤ d)
    (hd : d + 4 ≤ numBase) (hd4 : d % 4 = 0) (hr : d ≠ rowsOff) (hi : d ≠ iOff) :
    w32 m' base d = w32 m base d := by
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have hn := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  rw [← w32_val32_one, ← w32_val32_one]
  refine frameR_val32 F R h.scratch.nowrap (by omega) ?_ (combR_fit h)
  intro p hp
  simp only [combR, stR, List.mem_cons, List.not_mem_nil, or_false] at hp
  simp only [rowsOff, iOff] at hr hi
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [rowsOff, iOff] <;> omega

/-- The context through writes of the working space and the stack below `sp`. -/
theorem ctx_val (C : CtxRd base bytes len args s) {sp : BitVec 32}
    (hstk : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ (below sp 96)) {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (hws : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    {d N : Nat} (hd : d + 4 * N ≤ ctxBytes len) :
    val32 m' (ctxAddr args) d N = val32 m (ctxAddr args) d N := by
  refine val32_far F (fun r hr => ?_) (by have := C.span.fit; omega)
  have sub : Region.Sub ⟨off (ctxAddr args) d, 4 * N⟩ ⟨ctxAddr args, ctxBytes len⟩ := Offset.sub_base _ hd
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · exact hstk.sub_left sub
  · exact (C.apart.sub_left sub).sub_right (Offset.sub_base _ (hws p hp))

end

/-! ## The loop's state -/

/-- What the comb's rows keep: the context readable and apart, its entries, and x. -/
structure CombEnv (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (P G x bits : Nat) (s₀ : State) : Prop where
  rd : CtxRd base bytes len args s₀
  stk : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ (below (s₀.gpr .esp) 96)
  ents : ∀ e < 32, val32 s₀.mem (ctxAddr args) (24 + bc len .wide * (2 + e)) (cwc len .wide) =
    Spec.Rsa.powMod G (Spec.Rsa.FixedBaseComb.exponent bits e) P * 2 ^ (8 * bc len .wide) % P
  x13 : sv s₀.mem base len .wide 13 = x
  small : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639

/-- The comb's state with `V` in slot 6 at row `i`. -/
structure CombSt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (P bits : Nat) (s₀ : State) (V i : Nat) (u : State) : Prop where
  ctx : CtxOk Ex base bytes len args .wide P u
  one : sv u.mem base len .wide 3 = 1
  acc : sv u.mem base len .wide 6 = V
  lt : V < P
  rows : w32 u.mem base rowsOff = Spec.Rsa.FixedBaseComb.rows bits
  ctr : w32 u.mem base iOff = i
  frame : Frame (frameR base (s₀.gpr .esp) (combR len)) s₀.mem u.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ u

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32} {P G x bits : Nat} {s₀ : State}

theorem CombSt.inp {V i : Nat} {u : State} (S : CombSt Ex base bytes len args P bits s₀ V i u) :
    In Ex base bytes len args u := S.ctx.inp

theorem CombSt.esp {V i : Nat} {u : State} (S : CombSt Ex base bytes len args P bits s₀ V i u) :
    u.gpr .esp = s₀.gpr .esp := S.keeps.1 _ (by decide)

theorem CombSt.rd {V i : Nat} {u : State} (E : CombEnv Ex base bytes len args P G x bits s₀)
    (S : CombSt Ex base bytes len args P bits s₀ V i u) : CtxRd base bytes len args u := E.rd.keep S.keeps

theorem CombSt.ents {V i : Nat} {u : State} (E : CombEnv Ex base bytes len args P G x bits s₀)
    (S : CombSt Ex base bytes len args P bits s₀ V i u) {e : Nat} (he : e < 32) :
    val32 u.mem (ctxAddr args) (24 + bc len .wide * (2 + e)) (cwc len .wide) =
      Spec.Rsa.powMod G (Spec.Rsa.FixedBaseComb.exponent bits e) P * 2 ^ (8 * bc len .wide) % P := by
  have bw := bc_eq_cwc len .wide
  have row := Nat.mul_le_mul_left (bc len .wide) (show 2 + e + 1 ≤ 34 by omega)
  rw [Nat.mul_add, Nat.mul_one] at row
  rw [ctx_val E.rd E.stk S.frame (combR_fit S.inp) (by simp only [ctxBytes]; omega)]
  exact E.ents e he

theorem CombSt.x13 {V i : Nat} {u : State} (h₀ : In Ex base bytes len args s₀)
    (E : CombEnv Ex base bytes len args P G x bits s₀) (S : CombSt Ex base bytes len args P bits s₀ V i u) :
    sv u.mem base len .wide 13 = x := by
  rw [combR_sv h₀ S.frame h₀.room (by decide) (by decide)]; exact E.x13

end

/-! ## A row's pieces -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32} {P G x bits : Nat} {s₀ : State}

/-- A header word through a multiplication. -/
theorem mul_w32 {s : State} (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem} {o : Nat}
    (F : Frame (frameR base sp (mulR len .wide o)) m m') (R : CallRoom sp base bytes) (ho : o ≤ 8) {d : Nat}
    (hd : d + 4 ≤ numBase) : w32 m' base d = w32 m base d := by
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e1 : lo len (.slot .wide 1) = numBase + st len .wide := by simp [lo]
  have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) ho
  rw [← w32_val32_one, ← w32_val32_one]
  refine frameR_val32 F R h.scratch.nowrap (by omega) ?_ ?_
  · intro p hp
    simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega
  · intro p hp
    simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega

/-- A multiplication's ranges, among the comb's. -/
theorem mulR_combR {o : Nat} (ho : o ≤ 8) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (mulR len .wide o)) m m') : Frame (frameR base sp (combR len)) m m' := by
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e1 : lo len (.slot .wide 1) = numBase + st len .wide := by simp [lo]
  have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) (show o + 1 ≤ 9 by omega)
  rw [Nat.succ_mul] at this
  refine frameR_widen F fun p hp => ⟨(numBase, 9 * st len .wide), by simp [combR, stR], ?_⟩
  simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> dsimp only <;> omega

/-- The product of slot 6 and slot `b` (6 or 7) into slot 6. -/
theorem mulStep_ok {V i b : Nat} {u : State} (S : CombSt Ex base bytes len args P bits s₀ V i u)
    (hb : b = 6 ∨ b = 7) (hB : sv u.mem base len .wide b < P) :
    WP isa (mul .wide 6 6 b) u fun t => ∃ V', V' * 2 ^ (8 * bc len .wide) % P = V * sv u.mem base len .wide b % P ∧
      CombSt Ex base bytes len args P bits s₀ V' i t := by
  have h := S.inp
  have nb : numBase = 3336 := rfl
  refine WP.mono (cmul_ok S.ctx (o := 6) (a := 6) (b := b) (by decide) (by decide) (by decide) (by decide)
    (by omega) (by omega) hB) fun t ⟨C, K, F, L, V'⟩ => ⟨_, by rw [V', S.acc], ?_⟩
  rw [S.esp] at F
  have F' := F
  rw [← S.esp] at F'
  refine ⟨C, ?_, rfl, L, ?_, ?_, S.frame.trans (mulR_combR (by decide) F), S.keeps.trans (K.mono (by decide))⟩
  · rw [mulR_sv h F' h.room (o := 6) (j := 3) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.one
  · rw [mul_w32 h F' h.room (by decide) (by simp only [rowsOff]; omega)]; exact S.rows
  · rw [mul_w32 h F' h.room (by decide) (by simp only [iOff]; omega)]; exact S.ctr

/-- The digit of row `i − 1` and its entry, in slot 7. -/
theorem digitSelect_ok {V i : Nat} {u : State} (E : CombEnv Ex base bytes len args P G x bits s₀)
    (h₀ : In Ex base bytes len args s₀) (S : CombSt Ex base bytes len args P bits s₀ V i u) (hi : 1 ≤ i)
    (hiR : i ≤ Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa (.seq Generate.digit Generate.select) u fun t => CombSt Ex base bytes len args P bits s₀ V i t ∧
      sv t.mem base len .wide 7 = Spec.Rsa.powMod G (Spec.Rsa.FixedBaseComb.exponent bits
        (VG.Proof.Rsa.FixedBaseComb.digit bits x (i - 1))) P * 2 ^ (8 * bc len .wide) % P := by
  have h := S.inp
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  have bl := h.bytes_lt
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e3 : lo len (.slot .wide 3) = numBase + 3 * st len .wide := rfl
  have e6 : lo len (.slot .wide 6) = numBase + 6 * st len .wide := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have sm := E.small
  refine WP.seq (WP.mono (digit_ok h hi S.ctr S.rows (by omega)) fun t₁ ⟨I₁, O₁, W₁, K₁⟩ => ?_)
  rw [S.x13 h₀ E, teeth_digit] at W₁
  have D32 := VG.Proof.Rsa.FixedBaseComb.digit_lt bits x (i - 1)
  have Ct₁ : CtxRd base bytes len args t₁ := (S.rd E).keep K₁
  refine WP.mono (select_ok I₁ Ct₁ W₁ D32) fun t ⟨I, O, V7, K⟩ => ?_
  have rd7 := Nat.mul_le_mul_left (bc len .wide)
    (show 2 + VG.Proof.Rsa.FixedBaseComb.digit bits x (i - 1) + 1 ≤ 34 by omega)
  rw [Nat.mul_add, Nat.mul_one] at rd7
  -- The context did not change across the digit.
  have ct : val32 t₁.mem (ctxAddr args) (24 + bc len .wide * (2 + VG.Proof.Rsa.FixedBaseComb.digit bits x (i - 1)))
      (cwc len .wide) = val32 u.mem (ctxAddr args) (24 + bc len .wide * (2 + VG.Proof.Rsa.FixedBaseComb.digit bits x (i - 1)))
      (cwc len .wide) :=
    ctx_val (sp := u.gpr .esp) (S.rd E) (by rw [S.esp]; exact E.stk)
      (frameR_of_outside O₁ (by omega) (show (winOff, 4) ∈ [(winOff, 4)] from List.mem_singleton_self _))
      (by intro p hp; obtain rfl := List.mem_singleton.mp hp; simp only [winOff]; omega)
      (by simp only [ctxBytes]; omega)
  have Fw : Frame (frameR base (u.gpr .esp) [(winOff, 4)]) u.mem t₁.mem :=
    frameR_of_outside O₁ (by omega) (List.mem_singleton_self _)
  have F7 : Frame (frameR base (u.gpr .esp) [(lo len (.slot .wide 7), bc len .wide)]) t₁.mem t.mem := by
    have := frameR_of_outside (sp := u.gpr .esp) O (by omega) (List.mem_singleton_self _); exact this
  have C₁ := S.ctx.keepF2 K₁ (by decide) (by decide) Fw
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; simp only [winOff]; omega)
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact .inr ⟨by simp only [winOff]; omega,
      by simp only [winOff]; omega⟩)
  have sp₁ : t₁.gpr .esp = u.gpr .esp := K₁.1 _ (by decide)
  rw [← sp₁] at F7
  have C := C₁.keepF2 K (by decide) (by decide) F7
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; dsimp only; omega)
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact .inl (by dsimp only; omega))
  rw [sp₁] at F7
  have Ou : Outside base winOff 4 u.mem t₁.mem := O₁
  refine ⟨⟨C, ?_, ?_, S.lt, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [sv]
    rw [O.val32 (.inl (by omega)) (by omega), Ou.val32 (.inr (by omega)) (by omega)]; exact S.one
  · simp only [sv]
    rw [O.val32 (.inl (by omega)) (by omega), Ou.val32 (.inr (by omega)) (by omega)]; exact S.acc
  · rw [O.w32 (by simp only [rowsOff]; omega) (by simp only [rowsOff]; omega),
      Ou.w32 (by simp only [rowsOff, winOff]; omega) (by simp only [rowsOff]; omega)]
    exact S.rows
  · rw [O.w32 (by simp only [iOff]; omega) (by simp only [iOff]; omega),
      Ou.w32 (by simp only [iOff, winOff]; omega) (by simp only [iOff]; omega)]
    exact S.ctr
  · have Fw' := Fw
    have F7' := F7
    rw [S.esp] at Fw' F7'
    refine S.frame.trans ((frameR_widen (ws' := combR len) Fw' fun p hp => ?_).trans
      (frameR_widen (ws' := combR len) F7' fun p hp => ?_))
    · exact ⟨(0, 8), by simp [combR, stR], by obtain rfl := List.mem_singleton.mp hp; simp only [winOff]; omega⟩
    · exact ⟨(numBase, 9 * st len .wide), by simp [combR, stR], by
        obtain rfl := List.mem_singleton.mp hp; dsimp only; omega⟩
  · exact S.keeps.trans ((K₁.mono (by decide)).trans (K.mono (by decide)))
  · rw [V7, ct, S.ents E D32]

/-- The row counter down one. -/
theorem decStep_ok {V i : Nat} {u : State} (S : CombSt Ex base bytes len args P bits s₀ V i u) (hi : 1 ≤ i)
    (hi' : i < 2 ^ 32) :
    WP isa (.block [.mov .eax (.mem (sc iOff)), .alu .sub .eax (.imm 1), .store (sc iOff) .eax]) u fun t =>
      CombSt Ex base bytes len args P bits s₀ V (i - 1) t ∧ t.zf = some (decide (i - 1 = 0)) := by
  have h := S.inp
  have nb : numBase = 3336 := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e3 : lo len (.slot .wide 3) = numBase + 3 * st len .wide := rfl
  have e6 : lo len (.slot .wide 6) = numBase + 6 * st len .wide := rfl
  have bw := bc_eq_cwc len .wide
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have bl := h.bytes_lt
  refine WP.mono (dec_ok h hi hi' S.ctr) fun t ⟨I, O, W, K, z⟩ => ⟨?_, z⟩
  have F : Frame (frameR base (u.gpr .esp) [(iOff, 4)]) u.mem t.mem :=
    frameR_of_outside O (by simp only [iOff]; omega) (List.mem_singleton_self _)
  have C := S.ctx.keepF2 K (by decide) (by decide) F
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; simp only [iOff]; have := h.bytes_lt
        have := h.need; have en : CrtRt.need len = numBase + 28 * st len .wide := rfl; omega)
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact .inr ⟨by simp only [iOff]; omega,
      by simp only [iOff]; omega⟩)
  refine ⟨C, ?_, ?_, S.lt, ?_, W, ?_, S.keeps.trans (K.mono (by decide))⟩
  · simp only [sv]; rw [O.val32 (.inr (by simp only [iOff]; omega)) (by omega)]; exact S.one
  · simp only [sv]; rw [O.val32 (.inr (by simp only [iOff]; omega)) (by omega)]; exact S.acc
  · rw [O.w32 (by simp only [rowsOff, iOff]; omega) (by simp only [rowsOff]; omega)]; exact S.rows
  · rw [S.esp] at F
    exact S.frame.trans (frameR_mono F (by simp [combR]))

end

/-! ## A row, the loop and the comb -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32} {P G x bits : Nat} {s₀ : State}

/-- `g^E R mod P`, the Montgomery form of `g^E`. -/
abbrev enc (len P G E : Nat) : Nat := Spec.Rsa.powMod G E P * 2 ^ (8 * bc len .wide) % P

theorem enc_lt {len P G E : Nat} (hP : 0 < P) : enc len P G E < P := Nat.mod_lt _ hP

/-- One row: from `g^(high x i)` to `g^(high x (i − 1))`. -/
theorem step_ok (E : CombEnv Ex base bytes len args P G x bits s₀) (h₀ : In Ex base bytes len args s₀)
    {i : Nat} (hi : 1 ≤ i) (hiR : i ≤ Spec.Rsa.FixedBaseComb.rows bits) {u : State}
    (S : CombSt Ex base bytes len args P bits s₀ (enc len P G (VG.Proof.Rsa.FixedBaseComb.high bits x i)) i u) :
    WP isa Generate.step u fun t =>
      CombSt Ex base bytes len args P bits s₀ (enc len P G (VG.Proof.Rsa.FixedBaseComb.high bits x (i - 1))) (i - 1) t ∧
      t.zf = some (decide (i - 1 = 0)) := by
  have cp := S.ctx.coprime
  have P1 := S.ctx.gt
  unfold Generate.step
  refine WP.seq (WP.mono (mulStep_ok S (b := 6) (.inl rfl) (by rw [S.acc]; exact S.lt)) fun t₁ ⟨V₁, e₁, S₁⟩ => ?_)
  rw [S.acc] at e₁
  have v₁ : V₁ = enc len P G (2 * VG.Proof.Rsa.FixedBaseComb.high bits x i) :=
    VG.Proof.Rsa.FixedBaseComb.mont_square_encoded cp S₁.lt rfl e₁
  have ds := digitSelect_ok E h₀ S₁ hi hiR
  refine WP.seq ((WP.seq_iff.mp ds).mono fun t₂ h₂ => WP.seq (WP.mono h₂ fun t₃ ⟨S₃, T₃⟩ => ?_))
  refine WP.seq (WP.mono (mulStep_ok S₃ (b := 7) (.inr rfl) (by rw [T₃]; exact enc_lt (by omega)))
    fun t₄ ⟨V₄, e₄, S₄⟩ => ?_)
  rw [T₃] at e₄
  have v₄ : V₄ = enc len P G (2 * VG.Proof.Rsa.FixedBaseComb.high bits x i +
      Spec.Rsa.FixedBaseComb.exponent bits (VG.Proof.Rsa.FixedBaseComb.digit bits x (i - 1))) :=
    VG.Proof.Rsa.FixedBaseComb.mont_product_encoded cp S₄.lt v₁ rfl e₄
  have hs := VG.Proof.Rsa.FixedBaseComb.high_step bits x (i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at hs
  rw [← hs] at v₄
  subst v₄
  have := E.small
  exact decStep_ok S₄ hi (by omega)

/-- The rows, from the context's count down to none. -/
theorem loop_ok (E : CombEnv Ex base bytes len args P G x bits s₀) (h₀ : In Ex base bytes len args s₀)
    (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits) {u : State}
    (S : CombSt Ex base bytes len args P bits s₀
      (enc len P G (VG.Proof.Rsa.FixedBaseComb.high bits x (Spec.Rsa.FixedBaseComb.rows bits)))
      (Spec.Rsa.FixedBaseComb.rows bits) u) :
    WP isa (.loop Generate.step .ne) u
      (CombSt Ex base bytes len args P bits s₀ (enc len P G (VG.Proof.Rsa.FixedBaseComb.high bits x 0)) 0) := by
  have r := Spec.Rsa.FixedBaseComb.rows bits
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop hR (fun j t =>
      CombSt Ex base bytes len args P bits s₀
        (enc len P G (VG.Proof.Rsa.FixedBaseComb.high bits x (Spec.Rsa.FixedBaseComb.rows bits - j)))
        (Spec.Rsa.FixedBaseComb.rows bits - j) t) (fun j t hj I => ?_) (by simpa using S))
    fun t I => by simpa using I
  refine WP.mono (step_ok E h₀ (i := Spec.Rsa.FixedBaseComb.rows bits - j) (by omega) (by omega) I)
    fun v ⟨Sv, zv⟩ => ⟨?_, ?_⟩
  · rw [show Spec.Rsa.FixedBaseComb.rows bits - j - 1 = Spec.Rsa.FixedBaseComb.rows bits - (j + 1) by omega] at Sv
    exact Sv
  · rw [zv]; congr 1; exact decide_eq_decide.mpr (by omega)


/-- Slot 6 `g^x mod P` by the context's comb: the context of p, Montgomery one, the rows and the
product with one. -/
theorem comb_ok {s : State} (h : In Ex base bytes len args s) (E : CombEnv Ex base bytes len args P G x bits s)
    (hP : safeM (sv s.mem base len .wide 9) = P) (hx : x < 2 ^ bits) (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits)
    (hrows : w32 s.mem (ctxAddr args) 16 = Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa Generate.comb s fun u =>
      CtxOk Ex base bytes len args .wide P u ∧ sv u.mem base len .wide 6 = Spec.Rsa.powMod G x P ∧
      sv u.mem base len .wide 3 = 1 ∧ Frame (frameR base (s.gpr .esp) (combR len)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have bw := bc_eq_cwc len .wide
  have e3 : lo len (.slot .wide 3) = numBase + 3 * st len .wide := rfl
  have e6 : lo len (.slot .wide 6) = numBase + 6 * st len .wide := rfl
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have hn := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have sm := E.small
  have RR : 2 ^ (16 * bc len .wide) = 2 ^ (8 * bc len .wide) * 2 ^ (8 * bc len .wide) := by
    rw [← Nat.pow_add]; congr 1; omega
  unfold Generate.comb
  refine WP.seq (WP.mono (ctxP_ok h hP) fun s₁ ⟨C₁, one₁, R₁, F₁, _, K₁⟩ => ?_)
  have P1 := C₁.gt
  have cp := C₁.coprime
  refine WP.seq (WP.mono (cmul_ok C₁ (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [one₁]; exact P1)) fun s₂ ⟨C₂, K₂, F₂, L₂, V₂⟩ => ?_)
  have Y₂ : sv s₂.mem base len .wide 6 = 2 ^ (8 * bc len .wide) % P := by
    have v := VG.Proof.Bignum.mont_cancel cp (o := sv s₂.mem base len .wide 6) (c := 2 ^ (8 * bc len .wide))
      (by rw [V₂, R₁, one₁, Nat.mul_one, Nat.mod_mod, RR])
    rwa [Nat.mod_eq_of_lt L₂] at v
  have sp₁ : s₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have F₂' := F₂
  rw [sp₁] at F₂'
  have F₁₂ : Frame (frameR base (s.gpr .esp) (combR len)) s.mem s₂.mem :=
    (frameR_mono F₁ (by simp [combR])).trans (mulR_combR (by decide) F₂')
  have one₂ : sv s₂.mem base len .wide 3 = 1 := by
    rw [mulR_sv C₁.inp F₂ C₁.inp.room (o := 6) (j := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact one₁
  have K₁₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₂ := K₁.trans (K₂.mono (by decide))
  have h₂ := C₂.inp
  -- The context's row count to the counters.
  have rows₂ : w32 s₂.mem (ctxAddr args) 16 = Spec.Rsa.FixedBaseComb.rows bits := by
    rw [← w32_val32_one, ctx_val E.rd E.stk F₁₂ (combR_fit h) (by simp only [ctxBytes]; omega), w32_val32_one]
    exact hrows
  have fit := E.rd.span.fit
  have afit : (args ctxArg).toNat + ctxBytes len ≤ 2 ^ 32 := by
    simp only [ctxAddr, byteAddr, BitVec.toNat_setWidth] at fit
    rw [Nat.mod_eq_of_lt (by have := (args ctxArg).isLt; omega)] at fit; omega
  have a16 : addr (args ctxArg) 16 = off (ctxAddr args) 16 := addr_eq (by simp only [ctxBytes] at afit; omega)
  refine WP.seq (wp_movS (h₂.arg (i := ctxArg) (by decide)) fun s₃ U₃ _ => ?_)
  have rd₃ : InRegions (s₃.rd ++ s₃.wr) (addr (args ctxArg) 16) 4 := by
    rw [a16]
    exact ((E.rd.keep (K₁₂.trans (U₃.keeps.mono (by decide)))).row (d := 16) (n := 4)
      (by simp only [ctxBytes]; omega)).read
  refine wp_movS (readSrc_mem U₃.gpr rd₃) fun s₄ U₄ _ => ?_
  have v₄ : s₄.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows bits) := by
    rw [U₄.gpr, U₃.mem]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ← rows₂, a16]
  have K₂₄ : Keeps [.eax, .ecx] s₂ s₄ := (U₃.keeps.mono (by decide)).widen U₄.keeps
  have m₂₄ : s₄.mem = s₂.mem := by rw [U₄.mem, U₃.mem]
  have h₄ := h₂.regs K₂₄ m₂₄
  show WP isa (.block ([.store (sc rowsOff) .eax] ++ [.store (sc iOff) .eax])) s₄ _
  refine WP.block_append (WP.mono (counter_store h₄ (d := rowsOff) (.inl rfl) .eax)
    fun s₅ ⟨I₅, O₅, W₅, K₅, _⟩ => ?_)
  refine WP.mono (counter_store I₅ (d := iOff) (.inr rfl) .eax) fun s₆ ⟨I₆, O₆, W₆, K₆, _⟩ => ?_
  have K₄₆ : Keeps [] s₄ s₆ := K₅.trans K₆
  have sp₄ : s₄.gpr .esp = s.gpr .esp := by rw [K₂₄.1 _ (by decide), K₁₂.1 _ (by decide)]
  have sp₅ : s₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), sp₄]
  have Fr₅ : Frame (frameR base (s₄.gpr .esp) [(rowsOff, 4)]) s₄.mem s₅.mem :=
    frameR_of_outside O₅ (by simp only [rowsOff]; omega) (List.mem_singleton_self _)
  have Fi₆ : Frame (frameR base (s₅.gpr .esp) [(iOff, 4)]) s₅.mem s₆.mem :=
    frameR_of_outside O₆ (by simp only [iOff]; omega) (List.mem_singleton_self _)
  have C₅ := (C₂.regs K₂₄ m₂₄).keepF2 K₅ (by decide) (by decide) Fr₅
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; simp only [rowsOff]; omega)
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact .inr ⟨by simp only [rowsOff]; omega,
      by simp only [rowsOff]; omega⟩)
  have C₆ := C₅.keepF2 K₆ (by decide) (by decide) Fi₆
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; simp only [iOff]; omega)
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact .inr ⟨by simp only [iOff]; omega,
      by simp only [iOff]; omega⟩)
  rw [sp₄] at Fr₅
  rw [sp₅] at Fi₆
  have keep6 : ∀ j, 3 ≤ j → j ≤ 8 → sv s₆.mem base len .wide j = sv s₂.mem base len .wide j := fun j hj3 hj => by
    have := Nat.mul_le_mul_right (st len .wide) hj3
    have := Nat.mul_le_mul_right (st len .wide) hj
    have e : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
    have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
    simp only [sv]
    rw [O₆.val32 (.inr (by simp only [iOff]; omega)) (by omega), O₅.val32 (.inr (by simp only [rowsOff]; omega))
      (by omega), m₂₄]
  have acc₆ : sv s₆.mem base len .wide 6 =
      enc len P G (VG.Proof.Rsa.FixedBaseComb.high bits x (Spec.Rsa.FixedBaseComb.rows bits)) := by
    rw [keep6 6 (by decide) (by decide), Y₂, VG.Proof.Rsa.FixedBaseComb.high_top, enc, VG.Proof.Bignum.powMod_eq,
      Nat.pow_zero, Nat.mod_eq_of_lt P1, Nat.one_mul]
  have S₆ : CombSt Ex base bytes len args P bits s
      (enc len P G (VG.Proof.Rsa.FixedBaseComb.high bits x (Spec.Rsa.FixedBaseComb.rows bits)))
      (Spec.Rsa.FixedBaseComb.rows bits) s₆ := by
    refine ⟨C₆, by rw [keep6 3 (by decide) (by decide)]; exact one₂, acc₆, enc_lt (by omega), ?_, ?_, ?_,
      (K₁₂.trans (K₂₄.mono (by decide))).trans (K₄₆.mono (by decide))⟩
    · rw [O₆.w32 (by simp only [iOff, rowsOff]; omega) (by simp only [rowsOff]; omega), W₅, v₄, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    · rw [W₆, K₅.1 _ (by decide), v₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [m₂₄] at Fr₅
      exact (F₁₂.trans (frameR_mono Fr₅ (by simp [combR]))).trans (frameR_mono Fi₆ (by simp [combR]))
  refine WP.seq (WP.mono (loop_ok E h hR S₆) fun s₇ S₇ => ?_)
  refine WP.mono (cmul_ok S₇.ctx (o := 6) (a := 6) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [S₇.one]; exact P1)) fun u ⟨C, K, F, L, V⟩ => ⟨C, ?_, ?_, ?_, ?_⟩
  · rw [S₇.acc, S₇.one, Nat.mul_one, Nat.mod_mod, VG.Proof.Rsa.FixedBaseComb.high_zero bits x hx] at V
    have v := VG.Proof.Bignum.mont_cancel cp V
    have pl : Spec.Rsa.powMod G x P < P := by rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ (by omega)
    rwa [Nat.mod_eq_of_lt L, Nat.mod_eq_of_lt pl] at v
  · rw [mulR_sv S₇.inp F S₇.inp.room (o := 6) (j := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact S₇.one
  · rw [S₇.esp] at F; exact S₇.frame.trans (mulR_combR (by decide) F)
  · exact S₇.keeps.trans (K.mono (by decide))

end

end VG.Proof.Ffdh.X86.Cached
