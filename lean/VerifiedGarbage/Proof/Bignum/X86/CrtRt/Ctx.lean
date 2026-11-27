module

public import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Rsa.X86.Chain
import VerifiedGarbage.Proof.Dsa.Frame

/-! ### `Bignum.X86.CrtRt.Prepare`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.CrtRt.Power`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.CrtRt.Num2`, which this module and modules that import it used -/

section

/-! # Sums, differences, comparisons and imports in private CRT at a run-time width -/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (reduceLoop_ok compareLoop_ok byteAddr_ptr)
open VG.Impl.Bignum.X86.PublicRt (argAt)

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The pointers and count of `chain`, its carry cleared. -/
theorem chainSetup_ok (h : In Ex base bytes len args s) {o a b : Loc} {n : Cnt} (N : CntOk n)
    (ho : lo len o + cb len n ≤ bytes) (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes)
    {Q : State → Prop}
    (k : ∀ w, Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s w → w.mem = s.mem → PtrAt w base .ebp (lo len a) →
      PtrAt w base .ebx (lo len b) → PtrAt w base .edi (lo len o) → (w.gpr .edx).toNat = 4 * cw len n →
      w.gpr .ecx = cmask false → Q w) :
    WP isa (.block (ptrTo a .ebp .edx ++ ptrTo b .ebx .edx ++ ptrTo o .eax .edx ++ cntTo n .edx ++
      ([.mov .edi (.reg .eax), .mov .ecx (.imm 0)] : List Instr))) s Q := by
  have bl := h.bytes_lt
  simp only [List.append_assoc]
  refine ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_arith)
    fun u K m p => ?_
  have hu := h.regs K m
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_arith)
    fun v Kv mv pv => ?_
  have hv := hu.regs Kv mv
  refine ptrTo_ok (r := .eax) (t := .edx) (by decide) (by decide) hv.edi hv.width h.upper' (by omega_arith)
    fun w Kw mw pw => ?_
  have hw := hv.regs Kw mw
  refine cntTo_ok (r := .edx) hw.width h.upper' N.extra fun y Ky my cy => ?_
  refine wp_movS rfl fun y₁ u₁ _ => wp_movS rfl fun y₂ u₂ _ => WP.block_nil ?_
  refine k y₂ ((((((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))).trans
    (Ky.mono (by decide))).trans (u₁.keeps.mono (by decide))).trans (u₂.keeps.mono (by decide)))
    (by rw [u₂.mem, u₁.mem, my, mw, mv, m]) ?_ ?_ ?_ ?_ u₂.gpr
  · rw [PtrAt, u₂.other _ (by decide), u₁.other _ (by decide), Ky.1 _ (by decide), Kw.1 _ (by decide),
      Kv.1 _ (by decide)]; exact p
  · rw [PtrAt, u₂.other _ (by decide), u₁.other _ (by decide), Ky.1 _ (by decide), Kw.1 _ (by decide)]; exact pv
  · rw [PtrAt, u₂.other _ (by decide), u₁.gpr, Ky.1 _ (by decide)]; exact pw
  · rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact cnt_toNat h.upper' N cy

theorem chainSub_ok (h : In Ex base bytes len args s) {o a b : Loc} {n : Cnt} (N : CntOk n)
    (ho : lo len o + cb len n ≤ bytes) (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes)
    (hoa : Apart (lo len o) (cb len n) (lo len a) (cb len n)) (hob : Apart (lo len o) (cb len n) (lo len b) (cb len n)) :
    WP isa (chain .sbb o a b n) s fun u => Outside base (lo len o) (cb len n) s.mem u.mem ∧
      PtrAt u base .ebp (lo len a + cb len n) ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧ val32 u.mem base (lo len o) (cw len n) + val32 s.mem base (lo len b) (cw len n) =
        val32 s.mem base (lo len a) (cw len n) + 2 ^ (32 * cw len n) * c.toNat) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have ce := cb_eq (len := len) N
  unfold VG.Impl.Bignum.X86.CrtRt.chain
  refine WP.seq (chainSetup_ok h N ho ha hb fun w K m pa pb po c e => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Chain.subLoop_ok (h.ws.of_keeps K) (a := lo len a) (b := lo len b) (d := lo len o)
    (n := cw len n) (cw_pos h.lower') (by omega_using [ha, ce]) (by omega_using [hb, ce]) (by omega_using [ho, ce]) (by omega) (by omega) pa pb po c e)
    fun t ⟨O, P, V, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := K.trans Kt
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← m]; exact O.mono (Nat.zero_le _) (by omega_arith)
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  have ed : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  obtain ⟨c', ec', V'⟩ := V
  refine ⟨by rw [u₁.mem, ← m, ce]; exact O, by rw [PtrAt, u₁.other _ (by decide), ce]; exact P,
    ⟨c', by rw [u₁.other _ (by decide)]; exact ec', by rw [u₁.mem, ← m]; exact V'⟩,
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) (Kall.trans (u₁.keeps.mono (by decide))) ed⟩

theorem chainAdd_ok (h : In Ex base bytes len args s) {o a b : Loc} {n : Cnt} (N : CntOk n)
    (ho : lo len o + cb len n ≤ bytes) (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes)
    (hoa : Apart (lo len o) (cb len n) (lo len a) (cb len n)) (hob : Apart (lo len o) (cb len n) (lo len b) (cb len n)) :
    WP isa (chain .adc o a b n) s fun u => Outside base (lo len o) (cb len n) s.mem u.mem ∧
      PtrAt u base .ebp (lo len a + cb len n) ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧ val32 u.mem base (lo len o) (cw len n) + 2 ^ (32 * cw len n) * c.toNat =
        val32 s.mem base (lo len a) (cw len n) + val32 s.mem base (lo len b) (cw len n)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have ce := cb_eq (len := len) N
  unfold VG.Impl.Bignum.X86.CrtRt.chain
  refine WP.seq (chainSetup_ok h N ho ha hb fun w K m pa pb po c e => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Chain.addLoop_ok (h.ws.of_keeps K) (a := lo len a) (b := lo len b) (d := lo len o)
    (n := cw len n) (cw_pos h.lower') (by omega_using [ha, ce]) (by omega_using [hb, ce]) (by omega_using [ho, ce]) (by omega) (by omega) pa pb po c e)
    fun t ⟨O, P, _, V, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := K.trans Kt
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← m]; exact O.mono (Nat.zero_le _) (by omega_arith)
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  have ed : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  obtain ⟨c', ec', V'⟩ := V
  refine ⟨by rw [u₁.mem, ← m, ce]; exact O, by rw [PtrAt, u₁.other _ (by decide), ce]; exact P,
    ⟨c', by rw [u₁.other _ (by decide)]; exact ec', by rw [u₁.mem, ← m]; exact V'⟩,
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) (Kall.trans (u₁.keeps.mono (by decide))) ed⟩

theorem lessThan_ok (h : In Ex base bytes len args s) {a b : Loc} {n : Cnt} (N : CntOk n)
    (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes) :
    WP isa (lessThan a b n) s fun u => u.mem = s.mem ∧
      u.gpr .ecx = cmask (decide (val32 s.mem base (lo len a) (cw len n) < val32 s.mem base (lo len b) (cw len n))) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have ce := cb_eq (len := len) N
  unfold lessThan
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .esi) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_arith)
    fun u K m p => ?_)
  have hu := h.regs K m
  refine ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_arith)
    fun v Kv mv pv => ?_
  have hv := hu.regs Kv mv
  refine cntTo_ok (r := .edx) hv.width h.upper' N.extra fun w Kw mw cv => wp_movS rfl fun y uy _ => WP.block_nil ?_
  have Ky : Keeps [.ecx, .edx, .ebp, .esi] s y :=
    (((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))).trans (uy.keeps.mono (by decide))
  have my : y.mem = s.mem := by rw [uy.mem, mw, mv, m]
  refine WP.mono (compareLoop_ok (h.ws.of_keeps Ky) (x := lo len a) (y := lo len b) (N := cw len n)
    (cw_pos h.lower') (by omega_arith) (by omega_arith)
    (by rw [PtrAt, uy.other _ (by decide), Kw.1 _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [PtrAt, uy.other _ (by decide), Kw.1 _ (by decide)]; exact pv)
    (by rw [uy.other _ (by decide)]; exact cnt_toNat h.upper' N cv) uy.gpr)
    fun t ⟨mt, et, Kt⟩ => ⟨by rw [mt, my], by rw [et, my], (Ky.mono (by decide)).trans Kt⟩

theorem cmask_or_not (x y : Bool) : (cmask x ||| cmask y) ^^^ BitVec.allOnes 32 = cmask (!(x || y)) := by
  cases x <;> cases y <;> rfl

theorem equal_ok (h : In Ex base bytes len args s) {a b : Loc} {n : Cnt} (N : CntOk n)
    (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes) :
    WP isa (equal a b n) s fun u => u.mem = s.mem ∧
      u.gpr .ecx = cmask (decide (val32 s.mem base (lo len a) (cw len n) = val32 s.mem base (lo len b) (cw len n))) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  unfold equal
  refine WP.seq (WP.mono (lessThan_ok h N ha hb) fun u ⟨mu, eu, Ku⟩ => ?_)
  refine WP.seq (wp_movS rfl fun u₁ uu _ => WP.block_nil ?_)
  have hu := h.regs ((Ku.mono (by decide)).trans (uu.keeps.mono (by decide)) :
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₁) (by rw [uu.mem, mu])
  refine WP.seq (WP.mono (lessThan_ok hu N hb ha) fun v ⟨mv, ev, Kv⟩ => ?_)
  refine wp_orS rfl fun v₁ w₁ => wp_logicS (.inr rfl) rfl fun v₂ w₂ => WP.block_nil ?_
  have mem₁ : u₁.mem = s.mem := by rw [uu.mem, mu]
  refine ⟨by rw [w₂.mem, w₁.mem, mv, mem₁], ?_,
    ((((Ku.mono (by decide)).trans (uu.keeps.mono (by decide))).trans (Kv.mono (by decide))).trans
      (w₁.keeps.mono (by decide))).trans (w₂.keeps.mono (by decide))⟩
  have ebx : v.gpr .ebx = cmask (decide (val32 s.mem base (lo len a) (cw len n) < val32 s.mem base (lo len b) (cw len n))) := by
    rw [Kv.1 _ (by decide), uu.gpr, eu]
  rw [w₂.gpr]
  show v₁.gpr .ecx ^^^ BitVec.allOnes 32 = _
  rw [w₁.gpr, ev, ebx, mem₁, cmask_or_not]
  congr 1
  rw [show ∀ x y : Nat, (decide (x = y)) = !(decide (y < x) || decide (x < y)) from fun x y => by
    by_cases h₁ : x = y <;> by_cases h₂ : y < x <;> by_cases h₃ : x < y <;> simp_all <;> omega_arith]

end

end VG.Proof.Bignum.X86.CrtRt

end

end

/-! # `R² mod M` in a context of private CRT at a run-time width

A doubling modulo `M` of slot 4 (`doubleStep_ok`): the sum into slot 1 with
its carry in the word after it, the sum less `M` into slot 4, and the sum
back where it is below `M`. One, doubled `16 Bc` times, is `R² mod M` for
`R = 2^(8 Bc)` (`powerTwo_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (select_mod' count1_zf countLoop wp_carry)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The offset of slot `j` of the context. -/
abbrev sl (len : Nat) (c : Ctx) (j : Nat) : Nat := lo len (.slot c j)

/-- The value of slot `j` of the context. -/
abbrev sv (m : Mem) (base : Addr) (len : Nat) (c : Ctx) (j : Nat) : Nat :=
  val32 m base (lo len (.slot c j)) (cwc len c)

theorem sl_zero (len : Nat) (c : Ctx) : sl len c 0 = numBase := by simp [lo]

theorem sl_le {len : Nat} (c : Ctx) {i j : Nat} (hij : i < j) : sl len c i + st len c ≤ sl len c j := by
  have := Nat.mul_le_mul_right (st len c) hij
  simp only [lo, Nat.succ_mul] at *; omega_using [this]

theorem zero_sub_cmask (c : Bool) : (0 : BitVec 32) - cmask c = BitVec.ofNat 32 c.toNat := by
  cases c <;> rfl

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem addMod_ok (h : In Ex base bytes len args s) (c : Ctx) {o a b : Nat}
    (ho2 : 2 ≤ o) (ho : o ≤ 8) (ha2 : 2 ≤ a) (ha : a ≤ 8) (hb2 : 2 ≤ b) (hb : b ≤ 8)
    (hA : sv s.mem base len c a < sv s.mem base len c 0) (hB : sv s.mem base len c b < sv s.mem base len c 0) :
    WP isa (addMod c o a b) s fun u =>
      Frame (frameR base (s.gpr .esp) [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c o), bc len c)]) s.mem u.mem ∧
      sv u.mem base len c o = (sv s.mem base len c a + sv s.mem base len c b) % sv s.mem base len c 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain g := bc_ge h.lower' c
  obtain bw := bc_eq_cwc len c
  obtain s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  obtain s1o : lo len (.slot c 1) + st len c ≤ lo len (.slot c o) := sl_le (len := len) c (by omega_arith)
  obtain s1a : lo len (.slot c 1) + st len c ≤ lo len (.slot c a) := sl_le (len := len) c (by omega_arith)
  obtain s1b : lo len (.slot c 1) + st len c ≤ lo len (.slot c b) := sl_le (len := len) c (by omega_arith)
  obtain so8 : lo len (.slot c o) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) ho; simp only [lo]; omega_arith
  obtain sa8 : lo len (.slot c a) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) ha; simp only [lo]; omega_arith
  obtain sb8 : lo len (.slot c b) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hb; simp only [lo]; omega_arith
  obtain z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain N1 := one_ok c
  obtain cb1 : cb len (one c) = bc len c := by simp [cb, one]
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  unfold addMod
  -- The sum into slot 1.
  refine WP.seq (WP.mono (chainAdd_ok (o := .slot c 1) (a := .slot c a) (b := .slot c b) h N1
    (by simp only [cb1]; omega_arith) (by simp only [cb1]; omega_arith) (by simp only [cb1]; omega_arith)
    (by simp only [cb1]; omega_arith) (by simp only [cb1]; omega_arith)) fun u₁ ⟨O₁, _, ⟨c₁, ec₁, V₁⟩, K₁⟩ => ?_)
  simp only [cb1, cw1] at O₁ V₁
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  -- Its carry in the word after it.
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .eax) (t := .edx) (x := .slot c 1) (by decide) (by decide) h₁.edi h₁.width
    h.upper' (by omega_arith) fun u₂ K₂ m₂ p₂ => ?_)
  obtain h₂ := h₁.regs K₂ m₂
  refine cntTo_ok (r := .edx) (n := one c) h₂.width h.upper' N1.extra fun u₃ K₃ m₃ c₃ => ?_
  refine wp_addS rfl fun u₄ a₄ _ => wp_movS rfl fun u₅ a₅ _ => wp_subS rfl fun u₆ a₆ _ => ?_
  obtain K₆ : Keeps [.eax, .edx] u₂ u₆ := ((K₃.mono (by decide)).trans (a₄.keeps.mono (by decide))).trans
    ((a₅.keeps.mono (by decide)).trans (a₆.keeps.mono (by decide)))
  obtain ws₆ := h.ws.of_keeps ((K₁.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₁).trans
    ((K₂.mono (by decide)).trans (K₆.mono (by decide))))
  obtain p₆ : PtrAt u₆ base .eax (lo len (.slot c 1) + bc len c) := by
    rw [PtrAt, a₆.other _ (by decide), a₅.other _ (by decide), a₄.gpr, K₃.1 _ (by decide), c₃, cb1,
      ptr_add p₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := bc len c) (by omega_arith)]
  refine wp_storeS (ea_ptr ws₆ p₆ (d := 0) (by omega_arith))
    (ws_write ws₆ (y := lo len (.slot c 1) + bc len c + 0) (n := 4) (by omega_arith)) fun u₇ m₇ => WP.block_nil ?_
  obtain edx₆ : u₆.gpr .edx = BitVec.ofNat 32 c₁.toNat := by
    rw [a₆.gpr, a₅.gpr, a₅.other _ (by decide), a₄.other _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide),
      ec₁, zero_sub_cmask]
  obtain m₇' : u₇.mem = u₁.mem.writeW (off base (lo len (.slot c 1) + bc len c)) (BitVec.ofNat 32 c₁.toNat) := by
    rw [m₇.mem, edx₆, a₆.mem, a₅.mem, a₄.mem, m₃, m₂, Nat.add_zero]
  obtain K₇ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₇ :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₆.mono (by decide))).trans (m₇.keeps _)
  obtain W₇ : Outside base (lo len (.slot c 1) + bc len c) 4 u₁.mem u₇.mem := by
    rw [m₇']; exact writeW32_outside _ _ _ (by omega_arith)
  obtain h₇ := h.keep K₇ (by decide) (by decide)
    ((O₁.mono (Nat.zero_le _) (by omega_arith)).trans (W₇.mono (Nat.zero_le _) (by omega_arith)))
  obtain S₇ : val32 u₇.mem base (lo len (.slot c 1)) (cwc len c) = val32 u₁.mem base (lo len (.slot c 1)) (cwc len c) :=
    W₇.val32 (by omega_arith) (by omega_arith)
  obtain T₇ : w32 u₇.mem base (lo len (.slot c 1) + bc len c) = c₁.toNat := by
    rw [m₇', w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by cases c₁ <;> decide)]
  obtain M₇ : val32 u₇.mem base numBase (cwc len c) = val32 s.mem base numBase (cwc len c) := by
    rw [W₇.val32 (by omega_arith) (by omega_arith), O₁.val32 (by omega_arith) (by omega_arith)]
  -- The sum less `M` into slot 4.
  refine WP.seq (WP.mono (chainSub_ok (o := .slot c o) (a := .slot c 1) (b := .slot c 0) h₇ N1
    (by simp only [cb1]; omega_arith) (by simp only [cb1]; omega_arith) (by simp only [cb1]; omega_arith)
    (by simp only [cb1]; omega_arith) (by simp only [cb1]; omega_arith)) fun u₈ ⟨O₈, P₈, ⟨b₁, eb₁, V₈⟩, K₈⟩ => ?_)
  simp only [cb1, cw1] at O₈ V₈ P₈
  obtain K₈' := K₇.trans K₈
  obtain ws₈ := h.ws.of_keeps K₈'
  obtain T₈ : w32 u₈.mem base (lo len (.slot c 1) + bc len c) = c₁.toNat := by
    rw [O₈.w32 (by omega_arith) (by omega_arith), T₇]
  -- The mask: the carry less the borrow.
  refine WP.seq (wp_movS (readSrc_ptr ws₈ P₈ (d := 0) (by omega_arith)) fun t₁ u₁' _ => ?_)
  refine wp_carry (by rw [u₁'.other _ (by decide), eb₁]) fun t₂ u₂' c₂ => wp_sbbS rfl c₂ fun t₃ u₃' c₃ => ?_
  refine wp_sbb_self c₃ fun t₄ u₄' => wp_movS rfl fun t₅ u₅' _ => WP.block_nil ?_
  obtain K₅ : Keeps [.eax, .ecx] u₈ t₅ :=
    ((((u₁'.keeps.mono (by decide)).widen u₂'.keeps).widen u₃'.keeps).widen u₄'.keeps).widen u₅'.keeps
  obtain m₅ : t₅.mem = u₈.mem := by rw [u₅'.mem, u₄'.mem, u₃'.mem, u₂'.mem, u₁'.mem]
  obtain ecx₅ : t₅.gpr .ecx = cmask (decide (c₁.toNat < b₁.toNat)) := by
    rw [u₅'.gpr, u₄'.gpr]
    obtain eax₂ : (t₂.gpr .eax).toNat = c₁.toNat := by
      rw [u₂'.other _ (by decide), u₁'.gpr, Nat.add_zero, ← T₈]
    rw [eax₂, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
  obtain K₅' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t₅ := K₈'.trans (K₅.mono (by decide))
  obtain h₅ := h.keep K₅' (by decide) (by decide) (by
    rw [m₅]; exact ((O₁.mono (Nat.zero_le _) (by omega_arith)).trans (W₇.mono (Nat.zero_le _) (by omega_arith))).trans
      (O₈.mono (Nat.zero_le _) (by omega_arith)))
  -- The sum back where it is below `M`.
  refine WP.mono (selectX_ok (x := .slot c 1) (d := .slot c o) h₅ N1 (by simp only [cb1]; omega_arith)
    (by simp only [cb1]; omega_arith) (by simp only [cb1]; omega_arith) (by simp only [cw1]; omega_arith) ecx₅) fun u₉ ⟨O₉, V₉, K₉⟩ => ?_
  simp only [cb1, cw1] at O₉ V₉
  obtain M₈ : val32 u₈.mem base numBase (cwc len c) = val32 s.mem base numBase (cwc len c) := by
    rw [O₈.val32 (by omega_arith) (by omega_arith), M₇]
  refine ⟨?_, ?_, ?_⟩
  · have F₁ := frameR_of_outside (sp := s.gpr .esp) (ws := [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c o), bc len c)])
      (O₁.mono (Nat.le_refl _) (by omega_arith) : Outside base (lo len (.slot c 1)) (bc len c + 4) s.mem u₁.mem) (by omega_arith)
      (by simp)
    obtain F₇ := frameR_of_outside (sp := s.gpr .esp) (ws := [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c o), bc len c)])
      (W₇.mono (by omega_arith) (by omega_arith) : Outside base (lo len (.slot c 1)) (bc len c + 4) u₁.mem u₇.mem) (by omega_arith)
      (by simp)
    obtain F₈ := frameR_of_outside (sp := s.gpr .esp) (ws := [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c o), bc len c)])
      O₈ (by omega_arith) (by simp)
    obtain F₉ := frameR_of_outside (sp := s.gpr .esp) (ws := [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c o), bc len c)])
      O₉ (by omega_arith) (by simp)
    rw [m₅] at F₉
    exact ((F₁.trans F₇).trans F₈).trans F₉
  · have key := select_mod' (X := 2 ^ (32 * cwc len c)) (Tl := val32 u₁.mem base (lo len (.slot c 1)) (cwc len c))
      (D := val32 u₈.mem base (lo len (.slot c o)) (cwc len c)) (top := c₁.toNat) (c := b₁)
      (M := val32 s.mem base numBase (cwc len c)) (val32_lt _ _ _ _) (val32_lt _ _ _ _)
      (by rw [V₁]; simp only [sv, sl_zero] at hA hB; omega_arith) (by have V := V₈; rw [S₇, z0, M₇] at V; exact V)
    simp only [sv, sl_zero]
    rw [V₉, m₅]
    rw [show val32 u₈.mem base (lo len (.slot c 1)) (cwc len c) =
        val32 u₁.mem base (lo len (.slot c 1)) (cwc len c) by rw [O₈.val32 (by omega_arith) (by omega_arith), S₇]]
    rw [key, V₁]
  · exact K₅'.trans (K₉.mono (by decide))

theorem doubleStep_ok (h : In Ex base bytes len args s) (c : Ctx)
    (hT : sv s.mem base len c 4 < sv s.mem base len c 0) :
    WP isa (doubleStep c) s fun u =>
      Frame (frameR base (s.gpr .esp) [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)]) s.mem u.mem ∧
      sv u.mem base len c 4 = (sv s.mem base len c 4 + sv s.mem base len c 4) % sv s.mem base len c 0 ∧
      u.gpr .esi = s.gpr .esi - 1 ∧ u.zf = some (s.gpr .esi - 1 == 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  unfold doubleStep
  refine WP.seq (WP.mono (addMod_ok h c (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hT hT)
    fun u₁ ⟨F₁, V₁, K₁⟩ => ?_)
  refine wp_subZ rfl fun u₂ e₂ z₂ => WP.block_nil ?_
  obtain esi₁ : u₁.gpr .esi = s.gpr .esi := K₁.1 _ (by decide)
  refine ⟨by rw [e₂.mem]; exact F₁, by rw [e₂.mem]; exact V₁, by rw [e₂.gpr, esi₁], by rw [z₂, esi₁], ?_⟩
  exact (K₁.mono (by decide)).trans (e₂.keeps.mono (by decide))

end

end VG.Proof.Bignum.X86.CrtRt

end

end

/-! # A context of private CRT at a run-time width

One doubled `8 Bc + Bc / 8` times is `2^(8 Bc + Bc / 8) mod M` (`powerTwo_ok`).
`prepBase` replaces the modulus by three unless it is an odd number above one,
and sets one, the inverse and that power (`prepBase_ok`), which `prepare`'s
squares take to `R² mod M` (`prepCtx_ok`, `Stage.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (count1_zf countLoop)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The exponent of the power of two `powerTwo` computes: `8 Bc + Bc / 8`. -/
abbrev twoExp (len : Nat) (c : Ctx) : Nat := 8 * bc len c + bc len c / 8

/-- The ranges `powerTwo` changes. -/
abbrev powR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem powerTwo_ok (h : In Ex base bytes len args s) (c : Ctx) (hM : 1 < sv s.mem base len c 0) :
    WP isa (powerTwo c) s fun u =>
      Frame (frameR base (s.gpr .esp) (powR len c)) s.mem u.mem ∧
      sv u.mem base len c 4 = 2 ^ twoExp len c % sv s.mem base len c 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain g := bc_ge h.lower' c
  obtain hb := bc_le h.upper' c
  obtain bw := bc_eq_cwc len c
  obtain s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  obtain s14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  obtain s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  obtain z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain cb1 : cb len (one c) = bc len c := by simp [cb, one]
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  obtain fit : ∀ p ∈ powR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  unfold powerTwo
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 4) h (one_ok c) (by rw [cb1]; omega_arith) (v := 1) (by decide))
    fun u₀ ⟨O₀, V₀, K₀⟩ => ?_)
  simp only [cb1, cw1] at O₀ V₀
  obtain h₀ := h.keep K₀ (by decide) (by decide) (O₀.mono (Nat.zero_le _) (by omega_arith))
  obtain M₀ : sv u₀.mem base len c 0 = sv s.mem base len c 0 := O₀.val32 (by omega_arith) (by omega_arith)
  refine WP.seq (widthC_ok (k := 0) (c := c) (r := .esi) h₀.width h.upper' fun u₁ K₁ m₁ e₁ => ?_)
  refine wp_movS rfl fun u₂ a₂ _ => wp_shr (by decide) fun u₃ a₃ _ => wp_addS rfl fun u₄ a₄ _ => ?_
  refine wp_addS rfl fun u₅' a₅' _ => wp_addS rfl fun u₆ a₆ _ => wp_addS rfl fun u₅ a₅ _ => WP.block_nil ?_
  obtain K₅ : Keeps [.esi, .eax] u₀ u₅ :=
    (((((K₁.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (a₄.keeps.mono (by decide))).trans ((a₅'.keeps.mono (by decide)).trans (a₆.keeps.mono (by decide)))).trans
      (a₅.keeps.mono (by decide))
  obtain m₅ : u₅.mem = u₀.mem := by rw [a₅.mem, a₆.mem, a₅'.mem, a₄.mem, a₃.mem, a₂.mem, m₁]
  obtain esi₅ : (u₅.gpr .esi).toNat = twoExp len c := by
    obtain eax₆ : u₆.gpr .eax = u₁.gpr .esi >>> 3 := by
      rw [a₆.other _ (by decide), a₅'.other _ (by decide), a₄.other _ (by decide), a₃.gpr, a₂.gpr]
    obtain esi₆ : u₆.gpr .esi = u₁.gpr .esi + u₁.gpr .esi + (u₁.gpr .esi + u₁.gpr .esi) +
        (u₁.gpr .esi + u₁.gpr .esi + (u₁.gpr .esi + u₁.gpr .esi)) := by
      rw [a₆.gpr, a₅'.gpr, a₄.gpr, a₃.other _ (by decide), a₂.other _ (by decide)]
    rw [a₅.gpr, esi₆, eax₆, e₁]
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    simp only [twoExp]
    rw [Nat.mod_eq_of_lt (a := bc len c) (by omega_arith)]
    omega_arith
  obtain h₅ := h₀.regs (K₅.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₀ u₅) m₅
  obtain sp₅ : u₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), K₀.1 _ (by decide)]
  let M := sv s.mem base len c 0
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₅ t ∧
      Frame (frameR base (s.gpr .esp) (powR len c)) u₅.mem t.mem ∧
      sv t.mem base len c 4 = 2 ^ j % M ∧ (t.gpr .esi).toNat = twoExp len c - j
  obtain I₀ : I 0 u₅ := ⟨Keeps.refl _ _, Frame.refl _ _,
    by rw [m₅]; simp only [sv] at V₀ ⊢; rw [V₀, Nat.pow_zero, Nat.mod_eq_of_lt hM], by rw [esi₅]; rfl⟩
  refine WP.mono (countLoop (N := twoExp len c) (by simp only [twoExp]; omega_arith) I ?_ I₀) fun t ⟨Kt, Ft, Vt, _⟩ => ?_
  · rintro j t hj ⟨Kt, Ft, Vt, esit⟩
    obtain ht := h₅.keepF Kt (by decide) (by decide) (by rw [sp₅]; exact Ft) fit
    obtain Mt : sv t.mem base len c 0 = M := by
      have := frameR_val32 (d := lo len (.slot c 0)) (k := cwc len c) Ft h.room nw' (by omega_arith) (by
        intro p hp
        simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> omega_arith) fit
      simp only [sv]; rw [this, m₅]; exact M₀
    obtain hM' : 0 < M := by omega_arith
    refine WP.mono (doubleStep_ok ht c (by rw [Vt, Mt]; exact Nat.mod_lt _ hM'))
      fun u ⟨Fu, Vu, esiu, zu, Ku⟩ => ?_
    obtain ⟨c₁, c₂⟩ := count1_zf esit hj
    obtain spt : t.gpr .esp = s.gpr .esp := by rw [Kt.1 _ (by decide), sp₅]
    refine ⟨⟨Kt.trans Ku, Ft.trans (by rw [← spt]; exact Fu), ?_, by rw [esiu]; exact c₁⟩, by rw [zu, c₂]⟩
    rw [Vu, Vt, Mt, ← Nat.add_mod, ← Nat.two_mul, Nat.mul_comm, ← Nat.pow_succ]
  · have K₅s : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₅ := (K₀.mono (by decide)).trans (K₅.mono (by decide))
    refine ⟨?_, Vt, K₅s.trans Kt⟩
    rw [← m₅] at O₀
    exact (frameR_of_outside O₀ (by omega_arith) (by simp [powR])).trans Ft

/-- The modulus a context runs with: the factor itself if it is an odd number above one, else three. -/
def safeM (m : Nat) : Nat := if 1 < m ∧ m % 2 = 1 then m else 3

theorem safeM_gt (m : Nat) : 1 < safeM m := by unfold safeM; split <;> omega_arith

theorem safeM_odd (m : Nat) : safeM m % 2 = 1 := by unfold safeM; split <;> omega_arith

theorem safeM_of {m : Nat} (gt : 1 < m) (odd : m % 2 = 1) : safeM m = m := by
  unfold safeM; simp [gt, odd]

/-- The ranges `prepBase` changes. -/
abbrev baseR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(invOff, 4), (lo len (.slot c 0), bc len c), (lo len (.slot c 1), bc len c + 4), (lo len (.slot c 3), bc len c),
    (lo len (.slot c 4), bc len c), (lo len (.slot c 7), bc len c)]

/-- The ranges `prepare` changes: `prepBase`'s, and the callee's range of its squares. -/
abbrev prepR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(invOff, 4), (lo len (.slot c 0), bc len c), (lo len (.slot c 1), 3 * bc len c + 56),
    (lo len (.slot c 3), bc len c), (lo len (.slot c 4), bc len c), (lo len (.slot c 7), bc len c)]

theorem w32_val32_one (m : Mem) (base : Addr) (d : Nat) : val32 m base d 1 = w32 m base d := by
  simp [val32]

theorem cmask_and (a b : Bool) : cmask a &&& cmask b = cmask (a && b) := by cases a <;> cases b <;> rfl

theorem cmask_not (a : Bool) : cmask a ^^^ BitVec.allOnes 32 = cmask (!a) := by cases a <;> rfl

theorem zero_sub_and_one (w : BitVec 32) : (0 : BitVec 32) - (w &&& 1) = cmask (decide (w.toNat % 2 = 1)) := by
  obtain e : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    omega_arith
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h | h <;> rw [h] <;> rfl

/-- `prepBasePre`: the modulus made safe, one in slot 3 and the inverse. -/
theorem prepBasePre_ok (h : In Ex base bytes len args s) (c : Ctx) :
    WP isa (prepBasePre c) s fun u => In Ex base bytes len args u ∧
      Frame (frameR base (s.gpr .esp) (baseR len c)) s.mem u.mem ∧
      sv u.mem base len c 0 = safeM (sv s.mem base len c 0) ∧ sv u.mem base len c 3 = 1 ∧
      (safeM (sv s.mem base len c 0) * w32 u.mem base invOff + 1) % 2 ^ 32 = 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain g := bc_ge h.lower' c
  obtain bw := bc_eq_cwc len c
  obtain s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  obtain s13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  obtain s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  obtain s47 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 7) := sl_le (len := len) c (by decide)
  obtain s78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  obtain z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have nb : numBase = 3336 := rfl
  obtain cb1 : cb len (one c) = bc len c := by simp [cb, one]
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  obtain hk : ∃ k, cwc len c = k + 1 := ⟨cwc len c - 1, by omega_arith⟩
  obtain ⟨k, ek⟩ := hk
  obtain fitP : ∀ p ∈ baseR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (try simp only [invOff]) <;> omega_arith
  let M₀ := sv s.mem base len c 0
  unfold prepBasePre
  -- One in slot 3, three in slot 7.
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 3) h (one_ok c) (by rw [cb1]; omega_arith) (v := 1) (by decide))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  simp only [cb1, cw1] at O₁ V₁
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 7) h₁ (one_ok c) (by rw [cb1]; omega_arith) (v := 3) (by decide))
    fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  simp only [cb1, cw1] at O₂ V₂
  obtain h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  obtain M₂ : val32 u₂.mem base numBase (cwc len c) = M₀ := by
    rw [O₂.val32 (by omega_arith) (by omega_arith), O₁.val32 (by omega_arith) (by omega_arith), ← z0]
  obtain one₂ : val32 u₂.mem base (lo len (.slot c 3)) (cwc len c) = 1 := by
    rw [O₂.val32 (by omega_arith) (by omega_arith), V₁]
  -- `ecx`: whether the modulus is above one.
  refine WP.seq (WP.mono (lessThan_ok (a := .slot c 3) (b := .slot c 0) h₂ (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith)) fun u₃ ⟨m₃, e₃, K₃⟩ => ?_)
  simp only [cw1, one₂, z0, M₂] at e₃
  obtain h₃ := h₂.regs (K₃.mono (by decide) : Keeps [.eax, .ecx, .edx, .ebp, .esi] u₂ u₃) m₃
  -- `ecx`: whether it is to be replaced.
  refine WP.seq (wp_movS (readSrc_sc h₃.scratch (d := numBase) (by omega_arith)) fun v₁ a₁ _ => ?_)
  refine wp_logicS (.inl rfl) rfl fun v₂ a₂ => wp_movS rfl fun v₃ a₃ _ => wp_subS rfl fun v₄ a₄ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v₅ a₅ => wp_logicS (.inr rfl) rfl fun v₆ a₆ => WP.block_nil ?_
  obtain mem₆ : v₆.mem = u₂.mem := by rw [a₆.mem, a₅.mem, a₄.mem, a₃.mem, a₂.mem, a₁.mem, m₃]
  obtain par : (u₂.mem.readW (off base numBase) 32).toNat % 2 = M₀ % 2 := by
    rw [← M₂, ek, VG.Proof.Mont.X86.Dynamic.val32_parity]
  obtain edx₂ : v₂.gpr .edx = u₂.mem.readW (off base numBase) 32 &&& 1 := by
    rw [a₂.gpr]; show v₁.gpr .edx &&& 1 = _; rw [a₁.gpr, m₃]
  obtain eax₄ : v₄.gpr .eax = (0 : BitVec 32) - (u₂.mem.readW (off base numBase) 32 &&& 1) := by
    rw [a₄.gpr, a₃.gpr, a₃.other _ (by decide), edx₂]
  obtain ecx₄ : v₄.gpr .ecx = cmask (decide (1 < M₀)) := by
    rw [a₄.other _ (by decide), a₃.other _ (by decide), a₂.other _ (by decide), a₁.other _ (by decide), e₃]
  obtain ecx₅ : v₅.gpr .ecx = v₄.gpr .ecx &&& v₄.gpr .eax := by rw [a₅.gpr]; rfl
  obtain ecx₆ : v₆.gpr .ecx = cmask (!(decide (1 < M₀) && decide (M₀ % 2 = 1))) := by
    rw [a₆.gpr]
    show v₅.gpr .ecx ^^^ BitVec.allOnes 32 = _
    rw [ecx₅, ecx₄, eax₄, zero_sub_and_one, par, cmask_and, cmask_not]
  obtain K₆ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₆ :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      ((((((a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
        (a₄.keeps.mono (by decide))).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide)))
  obtain h₆ := h₂.regs ((K₃.mono (by decide) : Keeps [.eax, .ecx, .edx, .ebp, .esi] u₂ u₃).trans
    ((((((a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
        (a₄.keeps.mono (by decide))).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide))) :
      Keeps [.eax, .ecx, .edx, .ebp, .esi] u₂ v₆) mem₆
  -- The modulus replaced by three where it is to be.
  refine WP.seq (WP.mono (select_ok (x := .slot c 7) (d := .slot c 0) h₆ (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith) (by rw [cb1]; simp only [Apart]; omega_arith) ecx₆) fun u₇ ⟨O₇, V₇, K₇⟩ => ?_)
  simp only [cb1, cw1] at O₇ V₇
  obtain safe₇ : val32 u₇.mem base numBase (cwc len c) = safeM M₀ := by
    rw [← z0, V₇, mem₆]
    have three : val32 u₂.mem base (lo len (.slot c 7)) (cwc len c) = 3 := V₂
    rw [three, z0, M₂]
    unfold safeM
    by_cases hp : 1 < M₀ ∧ M₀ % 2 = 1
    · have e : (!(decide (1 < M₀) && decide (M₀ % 2 = 1))) = false := by simp [hp.1, hp.2]
      rw [e]; simp [hp]
    · have e : (!(decide (1 < M₀) && decide (M₀ % 2 = 1))) = true := by
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega_arith
      rw [e]; simp [hp]
  obtain h₇ := h₆.keep K₇ (by decide) (by decide) (O₇.mono (Nat.zero_le _) (by omega_arith))
  -- The inverse.
  obtain odd₇ : w32 u₇.mem base numBase % 2 = 1 := by
    rw [← VG.Proof.Mont.X86.Dynamic.val32_parity u₇.mem base numBase k, ← ek, safe₇]; exact safeM_odd _
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok h₇.scratch (mo := numBase) (inv := invOff) (by omega_arith)
    (by simp only [invOff]; omega_arith) odd₇) fun u₈ ⟨I₈, O₈, K₈⟩ => ?_
  obtain h₈ := h₇.keep K₈ (by decide) (by decide) (O₈.mono (Nat.zero_le _) (by simp only [invOff]; omega_arith))
  obtain M₈ : val32 u₈.mem base numBase (cwc len c) = safeM M₀ := by
    rw [O₈.val32 (by simp only [invOff]; omega_arith) (by omega_arith), safe₇]
  refine ⟨h₈, ?_, by simp only [sv, z0]; rw [M₈]; simp only [M₀, sv, z0], ?_, ?_, K₆.trans ((K₇.mono (by decide)).trans (K₈.mono (by decide)))⟩
  · have F₁ := frameR_of_outside (sp := s.gpr .esp) (ws := baseR len c) O₁ (by omega_arith) (by simp)
    obtain F₂ := frameR_of_outside (sp := s.gpr .esp) (ws := baseR len c) O₂ (by omega_arith) (by simp)
    obtain F₇ := frameR_of_outside (sp := s.gpr .esp) (ws := baseR len c) O₇ (by omega_arith) (by simp)
    obtain F₈ := frameR_of_outside (sp := s.gpr .esp) (ws := baseR len c) O₈ (by simp only [invOff]; omega_arith) (by simp)
    rw [mem₆] at F₇
    exact ((F₁.trans F₂).trans F₇).trans F₈
  · simp only [sv]
    rw [O₈.val32 (by simp only [invOff]; omega_arith) (by omega_arith), O₇.val32 (by omega_arith) (by omega_arith), mem₆,
      one₂]
  · rw [← safe₇, ek, val32, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left]
    exact I₈

theorem prepBase_ok (h : In Ex base bytes len args s) (c : Ctx) :
    WP isa (prepBase c) s fun u =>
      Frame (frameR base (s.gpr .esp) (baseR len c)) s.mem u.mem ∧
      sv u.mem base len c 0 = safeM (sv s.mem base len c 0) ∧ sv u.mem base len c 3 = 1 ∧
      sv u.mem base len c 4 = 2 ^ twoExp len c % safeM (sv s.mem base len c 0) ∧
      (safeM (sv s.mem base len c 0) * w32 u.mem base invOff + 1) % 2 ^ 32 = 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain bw := bc_eq_cwc len c
  obtain s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  obtain s13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  obtain s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  obtain z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have nb : numBase = 3336 := rfl
  obtain g := bc_ge h.lower' c
  obtain s47 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 7) := sl_le (len := len) c (by decide)
  obtain s78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  obtain hk : ∃ k, cwc len c = k + 1 := ⟨cwc len c - 1, by omega_arith⟩
  obtain ⟨k, ek⟩ := hk
  unfold prepBase
  refine WP.seq (WP.mono (prepBasePre_ok h c) fun u₈ ⟨h₈, F₈, M₈, one₈, I₈, K₈⟩ => ?_)
  simp only [sv, z0] at M₈
  -- `R² mod M`.
  refine WP.mono (powerTwo_ok h₈ c (by simp only [sv, z0]; rw [M₈]; exact safeM_gt _)) fun u ⟨F₉, V₉, K₉⟩ => ?_
  obtain sp₈ : u₈.gpr .esp = s.gpr .esp := K₈.1 _ (by decide)
  rw [sp₈] at F₉
  obtain fitW : ∀ p ∈ powR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  obtain keepVal : ∀ d, d + 4 * cwc len c ≤ bytes → (d + 4 * cwc len c ≤ lo len (.slot c 1) ∨
      lo len (.slot c 1) + (bc len c + 4) ≤ d) → (d + 4 * cwc len c ≤ lo len (.slot c 4) ∨ lo len (.slot c 4) + bc len c ≤ d) →
      val32 u.mem base d (cwc len c) = val32 u₈.mem base d (cwc len c) := fun d hd h1 h2 =>
    frameR_val32 F₉ h.room nw' hd (by
      intro p hp
      simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith) fitW
  refine ⟨?_, ?_, ?_, ?_, ?_, K₈.trans K₉⟩
  · exact F₈.trans (frameR_mono F₉ (by simp))
  · simp only [sv, z0]; rw [keepVal _ (by omega_arith) (by omega_arith) (by omega_arith), M₈]
  · simp only [sv] at one₈ ⊢
    rw [keepVal _ (by omega_arith) (by omega_arith) (by omega_arith), one₈]
  · simp only [sv] at V₉ ⊢; rw [V₉]; simp only [z0]; rw [M₈]
  · have W : w32 u.mem base invOff = w32 u₈.mem base invOff := by
      rw [← w32_val32_one, ← w32_val32_one]
      exact frameR_val32 F₉ h.room nw' (by simp only [invOff]; omega_arith) (by
        intro p hp
        simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> simp only [invOff] <;> omega_arith) fitW
    rw [W]
    exact I₈

end

end VG.Proof.Bignum.X86.CrtRt

end

end

/-! # A Montgomery context of private CRT at a run-time width

`CtxOk c M`: the inputs, the odd modulus `M` above one in slot 0 of the
context `c`, and `-M⁻¹ mod 2³²` in the header. A multiplication keeps it
(`cmul_ok`), as does any stage that changes neither (`CtxOk.keepF`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

structure CtxOk (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (c : Ctx) (M : Nat) (s : State) :
    Prop where
  inp : In Ex base bytes len args s
  mod : sv s.mem base len c 0 = M
  gt : 1 < M
  odd : M % 2 = 1
  inv : (M * w32 s.mem base invOff + 1) % 2 ^ 32 = 0

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

/-- `R = 2^(8 Bc)` is prime to `M`. -/
theorem CtxOk.coprime (C : CtxOk Ex base bytes len args c M s) : Nat.Coprime (2 ^ (8 * bc len c)) M :=
  VG.Proof.Bignum.coprime_pow2 C.odd _

theorem CtxOk.keepF (C : CtxOk Ex base bytes len args c M s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) {ws : List (Nat × Nat)}
    (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    (h0 : ∀ p ∈ ws, numBase + bc len c ≤ p.1) : CtxOk Ex base bytes len args c M t := by
  have h := C.inp
  have nw := h.scratch.nowrap
  have f0 := h.slot_fit c (j := 0) (by decide)
  have bw := bc_eq_cwc len c
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  refine ⟨h.keepF K di sp F hfit, ?_, C.gt, C.odd, ?_⟩
  · have hm := C.mod
    simp only [sv, z0] at hm ⊢
    rw [frameR_val32 F h.room nw (by omega_using [f0, bw, z0, est]) (fun p hp => .inl (by have := h0 p hp; omega_using [bw, this])) hfit]
    exact hm
  · rw [← w32_val32_one, frameR_val32 F h.room nw (by simp only [invOff, numBase] at *; omega_using [f0, z0])
      (fun p hp => .inl (by have := h0 p hp; simp only [invOff, numBase] at *; omega_using [this])) hfit, w32_val32_one]
    exact C.inv

/-- The same for ranges that may also lie in the header past its first word. -/
theorem CtxOk.keepF2 (C : CtxOk Ex base bytes len args c M s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) {ws : List (Nat × Nat)}
    (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    (h0 : ∀ p ∈ ws, numBase + bc len c ≤ p.1 ∨ (4 ≤ p.1 ∧ p.1 + p.2 ≤ numBase)) :
    CtxOk Ex base bytes len args c M t := by
  have h := C.inp
  have nw := h.scratch.nowrap
  have f0 := h.slot_fit c (j := 0) (by decide)
  have bw := bc_eq_cwc len c
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have nb : numBase = 3336 := rfl
  have io : invOff = 0 := rfl
  refine ⟨h.keepF K di sp F hfit, ?_, C.gt, C.odd, ?_⟩
  · have hm := C.mod
    simp only [sv, z0] at hm ⊢
    rw [frameR_val32 F h.room nw (by omega_using [f0, bw, z0, est]) (fun p hp => by
      rcases h0 p hp with e | e
      · exact .inl (by omega_using [bw, e])
      · exact .inr (by omega_using [e])) hfit]
    exact hm
  · rw [← w32_val32_one, frameR_val32 F h.room nw (by omega_using [f0, est, io])
      (fun p hp => .inl (by rcases h0 p hp with e | e <;> omega_arith)) hfit, w32_val32_one]
    exact C.inv

/-- The ranges of a multiplication into slot `o`. -/
abbrev mulR (len : Nat) (c : Ctx) (o : Nat) : List (Nat × Nat) :=
  [(lo len (.slot c o), bc len c), (lo len (.slot c 1), 3 * bc len c + 56)]

theorem cmul_ok (C : CtxOk Ex base bytes len args c M s) {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a)
    (ha : a ≤ 8) (hb3 : 3 ≤ b) (hb : b ≤ 8) (hB : sv s.mem base len c b < M) :
    WP isa (mul c o a b) s fun t =>
      CtxOk Ex base bytes len args c M t ∧ Keeps [.eax, .ecx, .edx] s t ∧
      Frame (frameR base (s.gpr .esp) (mulR len c o)) s.mem t.mem ∧
      sv t.mem base len c o < M ∧
      sv t.mem base len c o * 2 ^ (8 * bc len c) % M = sv s.mem base len c a * sv s.mem base len c b % M := by
  have h := C.inp
  have f8 := h.slot_fit c (j := 8) (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have hm := C.mod
  simp only [sv, z0] at hm hB
  have ok := mul_ok h c ho3 ho ha3 ha hb3 hb (by rw [hm]; exact C.inv) (by rw [hm]; exact hB)
  rw [hm] at ok
  refine WP.mono ok fun t ⟨cs, rd, wr, F, L, V⟩ => ?_
  have Ks : Keeps [.eax, .ecx, .edx] s t := ⟨fun r hr => by
    have := cs r; revert hr this; cases r <;> simp [calleeSaved], rd, wr⟩
  have F' : Frame (frameR base (s.gpr .esp) (mulR len c o)) s.mem t.mem := frameR_of_mul F (by simp) (by simp)
  have mo : ∀ j, 3 ≤ j → j ≤ 8 → numBase + 3 * st len c ≤ lo len (.slot c j) ∧
      lo len (.slot c j) + st len c ≤ lo len (.slot c 8) + st len c := fun j h3 h8 => by
    have := Nat.mul_le_mul_right (st len c) h3
    have := Nat.mul_le_mul_right (st len c) h8
    simp only [lo]; omega_arith
  obtain ⟨o1, o2⟩ := mo o ho3 ho
  have s1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  refine ⟨C.keepF Ks (by decide) (by decide) F' (by
      intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith) (by
      intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith), Ks, F', L, V⟩

/-- The context holds after register changes but `edi` and `esp`. -/
theorem CtxOk.regs (C : CtxOk Ex base bytes len args c M s) {regs : List Reg} (K : Keeps regs s t)
    (m : t.mem = s.mem) (di : .edi ∉ regs := by decide) (sp : .esp ∉ regs := by decide) :
    CtxOk Ex base bytes len args c M t :=
  ⟨C.inp.regs K m di sp, by rw [sv, m]; exact C.mod, C.gt, C.odd, by rw [m]; exact C.inv⟩

end

end VG.Proof.Bignum.X86.CrtRt
