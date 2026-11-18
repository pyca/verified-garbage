module

import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Impl.Ffdh.X86.Cached
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx

/-! ### `Ffdh.X86.Cached.Digit`, which this module and modules that import it used -/

section

/-!
# FFDH key generation from the context on i686: the comb's digit

Row `i − 1`'s digit, `FixedBaseComb.digit`, into the window word: for each
tooth `j`, bit `i − 1 + j rows` of x (slot 13), read from the public word
`⌊k / 32⌋` of the slot (0 past it, `bit_ok`) and shifted down by the public
`k mod 32` in five steps (`shifts_ok`), at bit `j` (`tooth_ok`,
`digit_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate
open VG.Proof.Bignum.X86.PublicRt (wp_shr)

/-! ## Programs in order -/

theorem seqs_cons (p : Prog isa) (ps : List (Prog isa)) : seqs (p :: ps) = .seq p (seqs ps) := rfl

theorem wp_seqs_append {xs ys : List (Prog isa)} {s : State} {Q : State → Prop}
    (h : WP isa (seqs xs) s fun u => WP isa (seqs ys) u Q) : WP isa (seqs (xs ++ ys)) s Q := by
  induction xs generalizing s with
  | nil => exact WP.block_nil_iff.mp h
  | cons x xs ih =>
    rw [List.cons_append, seqs_cons]
    rw [seqs_cons] at h
    exact WP.seq (WP.mono (WP.seq_iff.mp h) fun u hu => ih hu)

/-- `f 0`, …, `f (n − 1)` in order, by an invariant at each. -/
theorem wp_seqs_range (f : Nat → Prog isa) (I : Nat → State → Prop) :
    ∀ (n : Nat), (∀ e < n, ∀ u, I e u → WP isa (f e) u (I (e + 1))) → ∀ {s : State}, I 0 s →
      WP isa (seqs ((List.range n).map f)) s (I n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hs, s, h => by
    rw [List.range_succ, List.map_append]
    refine wp_seqs_append (WP.mono (wp_seqs_range f I n (fun e he => hs e (by omega_using [he])) h) fun u hu => ?_)
    rw [List.map_singleton, seqs_cons]
    exact WP.seq (WP.mono (hs n (by omega_using []) u hu) fun v hv => WP.block_nil hv)

/-! ## Words of a number -/

theorem w32_of_val32 (m : Mem) (base : Addr) : ∀ (N d q : Nat), q < N →
    w32 m base (d + 4 * q) = val32 m base d N / 2 ^ (32 * q) % 2 ^ 32
  | 0, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | N + 1, d, 0, _ => by
    rw [val32, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (show w32 m base d < 2 ^ 32 from BitVec.isLt _)]
  | N + 1, d, q + 1, hq => by
    rw [val32, show d + 4 * (q + 1) = (d + 4) + 4 * q by omega_using [], w32_of_val32 m base N (d + 4) q (by omega_using [hq]),
      show 32 * (q + 1) = 32 + 32 * q by omega_using [], Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 32), Nat.div_eq_of_lt (show w32 m base d < 2 ^ 32 from BitVec.isLt _), Nat.zero_add]

/-- Bit `k` of a number from its word `⌊k / 32⌋`. -/
theorem bit_of_word (x k : Nat) :
    x / 2 ^ (32 * (k / 32)) % 2 ^ 32 / 2 ^ (k % 32) % 2 = VG.Proof.Rsa.FixedBaseComb.bit x k := by
  unfold VG.Proof.Rsa.FixedBaseComb.bit
  obtain h32 : k % 32 < 32 := Nat.mod_lt _ (by decide)
  conv => rhs; rw [← Nat.div_add_mod k 32, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x / 2 ^ (32 * (k / 32)) = y
  obtain dv : 2 ^ (k % 32) * 2 ∣ 2 ^ 32 := by
    rw [← Nat.pow_succ]; exact Nat.pow_dvd_pow 2 (by omega_using [])
  rw [← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ dv, Nat.mod_mul_right_div_self]

/-! ## The shift by `k mod 32` -/

/-- The flags `test` leaves for a bit `b` of `c`, and the shift so far. -/
theorem shift_bits : ∀ b ∈ [16, 8, 4, 2, 1], ∀ c < 32,
    (BitVec.ofNat 32 c &&& BitVec.ofNat 32 b == 0) = decide (c / b * b = c / (2 * b) * (2 * b)) ∧
      (c / b * b = c / (2 * b) * (2 * b) ∨ c / b * b = c / (2 * b) * (2 * b) + b) := by decide

/-- One step of the shift: `eax` shifted down by bit `b` of `c`. -/
theorem shiftStep_ok {s : State} {b c a : Nat} (hb : b ∈ [16, 8, 4, 2, 1]) (hc : c < 32)
    (hecx : s.gpr .ecx = BitVec.ofNat 32 c) (heax : (s.gpr .eax).toNat = a / 2 ^ (c / (2 * b) * (2 * b))) :
    WP isa (.seq (.block [.alu .test .ecx (.imm (BitVec.ofNat 32 b))])
      (.ite .ne (.block [.shift .shr .eax b]) (.block []))) s fun u =>
      u.mem = s.mem ∧ Keeps [.eax] s u ∧ (u.gpr .eax).toNat = a / 2 ^ (c / b * b) := by
  obtain ⟨z, alt⟩ := shift_bits b hb c hc
  obtain b31 : 1 ≤ b ∧ b ≤ 31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; omega_using [hb]
  refine WP.seq (wp_testS rfl fun t T zt => WP.block_nil ?_)
  rw [hecx, z] at zt
  refine WP.ite (!decide (c / b * b = c / (2 * b) * (2 * b))) (by simp only [eval, zt, Option.map_some])
    (fun e => wp_shr b31 fun u U => WP.block_nil ⟨by rw [U.mem, T.mem], ⟨fun r hr => ?_, by rw [U.rd, T.rd],
      by rw [U.wr, T.wr]⟩, ?_⟩)
    (fun e => WP.block_nil ⟨T.mem, ⟨fun r _ => by rw [T.gpr], T.rd, T.wr⟩, ?_⟩)
  · rw [U.other r (by simpa using hr), T.gpr]
  · have ne : ¬ c / b * b = c / (2 * b) * (2 * b) := by simpa using e
    rw [U.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, T.gpr, heax, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rcases alt with h | h
    · exact absurd h ne
    · rw [h]
  · have eq : c / b * b = c / (2 * b) * (2 * b) := by simpa using e
    rw [T.gpr, heax, eq]

/-- The five steps: `eax` shifted down by `c`. -/
theorem shifts_ok {s : State} {c a : Nat} (hc : c < 32) (hecx : s.gpr .ecx = BitVec.ofNat 32 c)
    (heax : (s.gpr .eax).toNat = a) :
    WP isa (seqs ([16, 8, 4, 2, 1].map fun b => .seq (.block [.alu .test .ecx (.imm (BitVec.ofNat 32 b))])
      (.ite .ne (.block [.shift .shr .eax b]) (.block [])))) s fun u =>
      u.mem = s.mem ∧ Keeps [.eax] s u ∧ (u.gpr .eax).toNat = a / 2 ^ c := by
  obtain step : ∀ {b : Nat}, b ∈ [16, 8, 4, 2, 1] → ∀ {u : State} {rest : List Nat},
      u.mem = s.mem → Keeps [.eax] s u → (u.gpr .eax).toNat = a / 2 ^ (c / (2 * b) * (2 * b)) →
      (∀ v, v.mem = s.mem → Keeps [.eax] s v → (v.gpr .eax).toNat = a / 2 ^ (c / b * b) →
        WP isa (seqs (rest.map fun b => .seq (.block [.alu .test .ecx (.imm (BitVec.ofNat 32 b))])
          (.ite .ne (.block [.shift .shr .eax b]) (.block [])))) v fun u =>
            u.mem = s.mem ∧ Keeps [.eax] s u ∧ (u.gpr .eax).toNat = a / 2 ^ c) →
      WP isa (seqs ((b :: rest).map fun b => .seq (.block [.alu .test .ecx (.imm (BitVec.ofNat 32 b))])
          (.ite .ne (.block [.shift .shr .eax b]) (.block [])))) u fun u =>
            u.mem = s.mem ∧ Keeps [.eax] s u ∧ (u.gpr .eax).toNat = a / 2 ^ c :=
    fun {b} hb {u} {rest} m K e k => by
      rw [List.map_cons, seqs_cons]
      obtain ecx : u.gpr .ecx = BitVec.ofNat 32 c := by rw [K.1 _ (by decide), hecx]
      exact WP.seq (WP.mono (shiftStep_ok hb hc ecx e) fun v ⟨mv, Kv, ev⟩ =>
        k v (mv.trans m) (K.trans Kv) ev)
  refine step (b := 16) (by decide) rfl (Keeps.refl _ _) (by rw [heax, Nat.div_eq_of_lt hc]; simp) fun v₁ m₁ K₁ e₁ => ?_
  refine step (b := 8) (by decide) m₁ K₁ (by rw [e₁]) fun v₂ m₂ K₂ e₂ => ?_
  refine step (b := 4) (by decide) m₂ K₂ (by rw [e₂]) fun v₃ m₃ K₃ e₃ => ?_
  refine step (b := 2) (by decide) m₃ K₃ (by rw [e₃]) fun v₄ m₄ K₄ e₄ => ?_
  refine step (b := 1) (by decide) m₄ K₄ (by rw [e₄]) fun v₅ m₅ K₅ e₅ => ?_
  exact WP.block_nil ⟨m₅, K₅, by rw [e₅, Nat.div_one, Nat.mul_one]⟩

/-! ## A bit of x -/

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- Bit `k` (in `esi`, public) of x (slot 13), in the low bit of `eax`. -/
theorem bit_ok (h : In Ex base bytes len args s) {k : Nat} (hk : k < 2 ^ 32)
    (hesi : s.gpr .esi = BitVec.ofNat 32 k) :
    WP isa Generate.bit s fun u => u.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s u ∧
      (u.gpr .eax).toNat % 2 = VG.Proof.Rsa.FixedBaseComb.bit (sv s.mem base len .wide 13) k := by
  have bl := h.bytes_lt
  obtain f13 := h.slot_fit .wide (j := 13) (by decide)
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain hb := bc_le h.upper' .wide
  unfold Generate.bit
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mov fun s₁ U₁ => wp_shr (by decide) fun s₂ U₂ => wp_addS rfl fun s₃ U₃ _ =>
    wp_addS rfl fun s₄ U₄ _ => ?_)
  obtain e₄ : (s₄.gpr .ecx).toNat = 4 * (k / 32) := by
    rw [U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr, hesi]
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hk]
    omega_using [hk]
  obtain K₄ : Keeps [.ecx] s s₄ := (((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps).widen U₄.keeps
  obtain m₄ : s₄.mem = s.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  obtain h₄ := h.regs K₄ m₄
  refine widthC_ok h₄.width h.upper' fun s₅ K₅ m₅ e₅ => wp_cmpC rfl fun s₆ F₆ c₆ => WP.block_nil ?_
  obtain ecx₅ : (s₅.gpr .ecx).toNat = 4 * (k / 32) := by rw [K₅.1 _ (by decide)]; exact e₄
  rw [ecx₅, e₅, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])] at c₆
  obtain K₆ : Keeps [.ecx, .edx] s s₆ := (K₄.mono (by decide)).trans (K₅.mono (by decide)) |>.trans
    ⟨fun r _ => by rw [F₆.gpr], F₆.rd, F₆.wr⟩
  obtain m₆ : s₆.mem = s.mem := by rw [F₆.mem, m₅, m₄]
  obtain h₆ := h.regs K₆ m₆
  obtain esi₆ : s₆.gpr .esi = BitVec.ofNat 32 k := by rw [K₆.1 _ (by decide), hesi]
  obtain ecx₆ : (s₆.gpr .ecx).toNat = 4 * (k / 32) := by rw [F₆.gpr]; exact ecx₅
  obtain x13 := val32_lt s.mem base (lo len (.slot .wide 13)) (cwc len .wide)
  refine WP.ite (decide (4 * (k / 32) < bc len .wide)) (by simp only [eval, c₆]) (fun e => ?_)
    (fun e => wp_movS rfl fun u U _ => WP.block_nil ⟨by rw [U.mem, m₆], (K₆.mono (by decide)).trans (U.keeps.mono (by decide)), ?_⟩)
  · have lt : k / 32 < cwc len .wide := by have := of_decide_eq_true e; omega_using [bw, this]
    refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h₆.edi h₆.width h.upper'
      (by omega_using [bl, f13]) fun s₇ K₇ m₇ p₇ => ?_)
    refine wp_addS rfl fun s₈ U₈ _ => ?_
    obtain p₈ : PtrAt s₈ base .ebp (lo len (.slot .wide 13) + 4 * (k / 32)) := by
      rw [PtrAt, U₈.gpr, BitVec.toNat_add, p₇, K₇.1 _ (by decide), ecx₆]; omega_using []
    obtain K₈ : Keeps [.ecx, .edx, .ebp] s s₈ := (K₆.mono (by decide)).trans ((K₇.mono (by decide)).trans
      (U₈.keeps.mono (by decide)))
    obtain m₈ : s₈.mem = s.mem := by rw [U₈.mem, m₇, m₆]
    obtain h₈ := h.regs K₈ m₈
    refine wp_movS (VG.Proof.Mont.X86.Rt.readSrc_ptr h₈.ws p₈ (d := 0) (by omega_using [f13, bw, est, lt])) fun s₉ U₉ _ => ?_
    refine wp_mov fun s₁₀ U₁₀ => wp_logicS (.inl rfl) rfl fun s₁₁ U₁₁ => WP.block_nil ?_
    obtain esi₈ : s₈.gpr .esi = BitVec.ofNat 32 k := by rw [K₈.1 _ (by decide), hesi]
    obtain ecx₁₁ : s₁₁.gpr .ecx = BitVec.ofNat 32 (k % 32) := by
      rw [U₁₁.gpr, U₁₀.gpr, U₉.other _ (by decide), esi₈]
      simp only [↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
      rw [show BitVec.toNat (31 : BitVec 32) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega_using []
    obtain eax₁₁ : (s₁₁.gpr .eax).toNat = sv s.mem base len .wide 13 / 2 ^ (32 * (k / 32)) % 2 ^ 32 := by
      rw [U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.gpr, Nat.add_zero, m₈]
      exact w32_of_val32 s.mem base (cwc len .wide) _ _ lt
    obtain K₁₁ : Keeps [.eax, .ecx] s₈ s₁₁ := ((U₉.keeps.mono (by decide)).widen U₁₀.keeps).widen U₁₁.keeps
    refine WP.mono (shifts_ok (Nat.mod_lt _ (by decide)) ecx₁₁ eax₁₁) fun u ⟨mu, Ku, eu⟩ => ⟨?_, ?_, ?_⟩
    · rw [mu, U₁₁.mem, U₁₀.mem, U₉.mem, m₈]
    · exact (K₈.mono (by decide)).trans ((K₁₁.mono (by decide)).trans (Ku.mono (by decide)))
    · rw [eu]; exact bit_of_word _ _
  · rw [U.gpr]
    obtain ge : 32 * cwc len .wide ≤ k := by have := of_decide_eq_false e; omega_using [bw, this]
    show 0 % 2 = _
    unfold VG.Proof.Rsa.FixedBaseComb.bit
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x13 (Nat.pow_le_pow_right (by decide) ge))]

end

/-! ## The digit -/

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A register stored to the header word `d`. -/
theorem storeW_ok (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ numBase) (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun u =>
      In Ex base bytes len args u ∧ Outside base d 4 s.mem u.mem ∧ w32 u.mem base d = (s.gpr r).toNat ∧
      Keeps [] s u := by
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  refine wp_storeS (h.scratch.ea (d := d) (by omega_arith)) (h.scratch.write (d := d) (n := 4) (by omega_arith))
    fun u M => WP.block_nil ?_
  obtain O : Outside base d 4 s.mem u.mem := by rw [M.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  refine ⟨h.keep (M.keeps []) (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega_arith)), O, ?_, M.keeps []⟩
  rw [M.mem, w32_write_self]

/-- A header word read. -/
theorem readW_ok (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ numBase) {v : Nat} (hv : w32 s.mem base d = v)
    (hv' : v < 2 ^ 32) : readSrc s (.mem (sc d)) = some (BitVec.ofNat 32 v) := by
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  rw [readSrc_sc h.scratch (d := d) (by omega_arith)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv']
  exact hv

/-- `esi += [d]`, `j` times. -/
theorem addsMem_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {d R : Nat}
    (hd : d + 4 ≤ numBase) (hR : w32 s.mem base d = R) (hR' : R < 2 ^ 32) : ∀ (j : Nat) {t : State},
    t.mem = s.mem → Keeps [.esi] s t →
    (∀ u, Keeps [.esi] s u → u.mem = s.mem → u.gpr .esi = t.gpr .esi + BitVec.ofNat 32 (j * R) →
      WP isa (.block is) u Q) →
    WP isa (.block (List.replicate j (.alu .add .esi (.mem (sc d))) ++ is)) t Q
  | 0, t, m, K, k => by
    simpa using k t K m (by simp)
  | j + 1, t, m, K, k => by
    rw [List.replicate_succ, List.cons_append]
    obtain ht := h.regs K m
    refine wp_addS (readW_ok ht hd (by rw [m]; exact hR) hR') fun u U _ => ?_
    refine addsMem_ok h hd hR hR' j (by rw [U.mem, m]) (K.trans (U.keeps.mono (by decide))) fun v Kv mv ev => ?_
    refine k v Kv mv ?_
    rw [ev, U.gpr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2
    rw [Nat.succ_mul, Nat.add_comm]

/-- `eax += eax`, `j` times. -/
theorem addsSelf_ok {is : List Instr} {Q : State → Prop} : ∀ (j : Nat) {t : State},
    (∀ u, Keeps [.eax] t u → u.mem = t.mem → (u.gpr .eax).toNat = (t.gpr .eax).toNat * 2 ^ j % 2 ^ 32 →
      WP isa (.block is) u Q) →
    WP isa (.block (List.replicate j (.alu .add .eax (.reg .eax)) ++ is)) t Q
  | 0, t, k => by
    simpa using k t (Keeps.refl _ _) rfl (by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (BitVec.isLt _)])
  | j + 1, t, k => by
    rw [List.replicate_succ, List.cons_append]
    refine wp_addS rfl fun u U _ => addsSelf_ok j fun v Kv mv ev => k v ((U.keeps.mono (by decide)).trans Kv)
      (by rw [mv, U.mem]) ?_
    rw [ev, U.gpr, BitVec.toNat_add, Nat.mod_mul_mod, Nat.pow_succ, ← Nat.two_mul]
    congr 1
    rw [Nat.pow_succ', Nat.mul_comm 2, Nat.mul_assoc]

/-- Disjoint bits of the digit. -/
theorem or_bit : ∀ j < 5, ∀ W < 2 ^ j, ∀ b < 2, (b * 2 ^ j ||| W) = W + b * 2 ^ j := by decide

/-- Bit `i − 1 + j rows` of x into bit `j` of the window word, which held `W < 2^j`. -/
theorem tooth_ok (h : In Ex base bytes len args s) {j i R W : Nat} (hj : j < 5) (hi : 1 ≤ i)
    (hI : w32 s.mem base iOff = i) (hR : w32 s.mem base rowsOff = R) (hb : i + 4 * R < 2 ^ 32)
    (hW : w32 s.mem base winOff = W) (hWj : W < 2 ^ j) :
    WP isa (tooth j) s fun u =>
      In Ex base bytes len args u ∧ Outside base winOff 4 s.mem u.mem ∧
      w32 u.mem base winOff = W + VG.Proof.Rsa.FixedBaseComb.bit (sv s.mem base len .wide 13) (i - 1 + j * R) * 2 ^ j ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have io : iOff = 68 := rfl
  have ro : rowsOff = 56 := rfl
  have wo : winOff = 4 := rfl
  have nb : numBase = 3336 := rfl
  obtain p16 : 2 ^ j ≤ 16 := Nat.pow_le_pow_right (show 0 < 2 by decide) (show j ≤ 4 by omega_using [hj])
  unfold tooth
  simp only [List.cons_append, List.nil_append]
  rw [← List.append_nil (List.replicate j (Instr.alu .add .esi (.mem (sc rowsOff))))]
  refine WP.seq (wp_movS (readW_ok h (d := iOff) (by omega_using [io, nb]) hI (by omega_using [hb])) fun s₁ U₁ _ =>
    wp_subS rfl fun s₂ U₂ _ => ?_)
  obtain K₂ : Keeps [.esi] s s₂ := (U₁.keeps.mono (by decide)).widen U₂.keeps
  obtain m₂ : s₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  refine addsMem_ok h (d := rowsOff) (by omega_using [ro, nb]) hR (by omega_using [hb]) j m₂ K₂ fun s₃ K₃ m₃ e₃ => WP.block_nil ?_
  obtain k3 : i - 1 + j * R < 2 ^ 32 := by have := Nat.mul_le_mul_right R (show j ≤ 4 by omega_using [hj]); omega_using [hb, this]
  obtain esi₃ : s₃.gpr .esi = BitVec.ofNat 32 (i - 1 + j * R) := by
    rw [e₃, U₂.gpr, U₁.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hi]), BitVec.ofNat_add_ofNat]
  obtain h₃ := h.regs K₃ m₃
  refine WP.seq (WP.mono (bit_ok h₃ k3 esi₃) fun s₄ ⟨m₄, K₄, e₄⟩ => ?_)
  rw [m₃] at e₄
  obtain h₄ := h₃.regs K₄ m₄
  refine wp_logicS (.inl rfl) rfl fun s₅ U₅ => ?_
  obtain v₅ : (s₅.gpr .eax).toNat = VG.Proof.Rsa.FixedBaseComb.bit (sv s.mem base len .wide 13) (i - 1 + j * R) := by
    rw [U₅.gpr]; simp only [↓reduceIte]
    rw [BitVec.toNat_and, show BitVec.toNat (1 : BitVec 32) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.pow_one, e₄]
  obtain bl := VG.Proof.Rsa.FixedBaseComb.bit_lt (sv s.mem base len .wide 13) (i - 1 + j * R)
  obtain bj : VG.Proof.Rsa.FixedBaseComb.bit (sv s.mem base len .wide 13) (i - 1 + j * R) * 2 ^ j ≤ 16 :=
    Nat.le_trans (Nat.mul_le_mul_right (2 ^ j) (Nat.le_of_lt_succ bl)) (by omega_using [p16])
  refine addsSelf_ok j fun s₆ K₆ m₆ e₆ => ?_
  rw [v₅, Nat.mod_eq_of_lt (by omega_using [bj])] at e₆
  obtain K₅₆ : Keeps [.eax] s₄ s₆ := (U₅.keeps.mono (by decide)).trans K₆
  obtain m₆' : s₆.mem = s.mem := by rw [m₆, U₅.mem, m₄, m₃]
  obtain h₆ := h.regs ((K₃.mono (by decide)).trans ((K₄.mono (by decide)).trans (K₅₆.mono (by decide))) :
    Keeps [.eax, .ecx, .edx, .ebp, .esi] s s₆) m₆'
  refine wp_orS (readW_ok h₆ (d := winOff) (v := W) (by omega_using [wo, nb]) (by rw [m₆']; exact hW) (by omega_using [hWj, p16])) fun s₇ U₇ => ?_
  obtain h₇ := h₆.regs U₇.keeps U₇.mem
  refine WP.mono (storeW_ok h₇ (d := winOff) (by omega_using [wo, nb]) .eax) fun u ⟨I, O, Wu, Ku⟩ => ⟨I, ?_, ?_, ?_⟩
  · rw [U₇.mem, m₆'] at O; exact O
  · rw [Wu, U₇.gpr, BitVec.toNat_or, e₆, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hWj, p16])]
    exact or_bit j hj W hWj _ bl
  · exact ((K₃.mono (by decide)).trans ((K₄.mono (by decide)).trans ((K₅₆.mono (by decide)).trans
      ((U₇.keeps.mono (by decide)).trans (Ku.mono (by decide))))))


/-- The digit's first `e` teeth: bits `row + j R` of x for `j < e`, at bit `j`. -/
def teeth (x row R : Nat) : Nat → Nat
  | 0 => 0
  | e + 1 => teeth x row R e + VG.Proof.Rsa.FixedBaseComb.bit x (row + e * R) * 2 ^ e

theorem teeth_lt (x row R : Nat) : ∀ e, teeth x row R e < 2 ^ e
  | 0 => by rw [teeth]; exact Nat.one_pos
  | e + 1 => by
    have := teeth_lt x row R e
    have := VG.Proof.Rsa.FixedBaseComb.bit_lt x (row + e * R)
    rw [teeth, Nat.pow_succ]
    have : VG.Proof.Rsa.FixedBaseComb.bit x (row + e * R) * 2 ^ e ≤ 2 ^ e :=
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ this)) (by omega_using [])
    omega_arith

theorem teeth_digit (bits x row : Nat) :
    teeth x row (Spec.Rsa.FixedBaseComb.rows bits) 5 = VG.Proof.Rsa.FixedBaseComb.digit bits x row := by
  simp only [teeth, VG.Proof.Rsa.FixedBaseComb.digit, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    Nat.pow_zero, Nat.mul_one]
  omega_using []

/-- Row `i − 1`'s digit, of rows of `R` bits, into the window word. -/
theorem digit_ok (h : In Ex base bytes len args s) {i R : Nat} (hi : 1 ≤ i)
    (hI : w32 s.mem base iOff = i) (hR : w32 s.mem base rowsOff = R) (hb : i + 4 * R < 2 ^ 32) :
    WP isa Generate.digit s fun u =>
      In Ex base bytes len args u ∧ Outside base winOff 4 s.mem u.mem ∧
      w32 u.mem base winOff = teeth (sv s.mem base len .wide 13) (i - 1) R 5 ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have io : iOff = 68 := rfl
  have ro : rowsOff = 56 := rfl
  have wo : winOff = 4 := rfl
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have e13 : lo len (.slot .wide 13) = numBase + 13 * st len .wide := rfl
  obtain f13 := h.slot_fit .wide (j := 13) (by decide)
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  unfold Generate.digit
  refine WP.seq (wp_movS rfl fun s₁ U₁ _ => ?_)
  obtain h₁ := h.regs U₁.keeps U₁.mem
  refine WP.mono (storeW_ok h₁ (d := winOff) (by omega_using [wo, nb]) .eax) fun s₂ ⟨I₂, O₂, W₂, K₂⟩ => ?_
  rw [U₁.mem] at O₂
  rw [U₁.gpr] at W₂
  obtain K₁₂ : Keeps [.eax, .ecx, .edx, .ebp, .esi] s s₂ := (U₁.keeps.mono (by decide)).trans (K₂.mono (by decide))
  refine wp_seqs_range tooth (fun e u => In Ex base bytes len args u ∧ Outside base winOff 4 s.mem u.mem ∧
      w32 u.mem base winOff = teeth (sv s.mem base len .wide 13) (i - 1) R e ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s u) 5 (fun e he u ⟨Iu, Ou, Wu, Ku⟩ => ?_) ⟨I₂, O₂, W₂, K₁₂⟩
  obtain iu : w32 u.mem base iOff = i := by rw [Ou.w32 (by omega_using [io, wo]) (by omega_using [io])]; exact hI
  obtain ru : w32 u.mem base rowsOff = R := by rw [Ou.w32 (by omega_using [ro, wo]) (by omega_using [ro])]; exact hR
  obtain xu : sv u.mem base len .wide 13 = sv s.mem base len .wide 13 :=
    Ou.val32 (.inr (by omega_arith)) (by omega_arith)
  refine WP.mono (tooth_ok Iu (j := e) he hi iu ru hb Wu (teeth_lt _ _ _ e)) fun v ⟨Iv, Ov, Wv, Kv⟩ =>
    ⟨Iv, Ou.trans Ov, ?_, Ku.trans Kv⟩
  rw [Wv, xu, teeth]

end

end VG.Proof.Ffdh.X86.Cached

end

end

/-!
# FFDH key generation from the context on i686: the digit's entry

`select_ok`: slot 7 the context's entry of the digit in the window word, by
scanning all 32 entries under an equality mask, each copied by
`selectLoop_far_ok`; the context's rows, at `ctx + 24 + B j` (`rowAt_ok`),
are read only.
-/

@[expose] public section

/-!
# FFDH's key-generation context on i686: copying its rows

A row of the context and a slot of the working space are copied, either way,
by `selectLoop` under a mask (`selectLoop_far_ok`): the source is any
readable span, apart from the destination, a span of a writable region.
-/

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

/-- Memory changed only in `[d, d + n)` of `D` is framed by that span. -/
theorem Outside.frame_span {D : Addr} {d n : Nat} {m m' : Mem} (h : Outside D d n m m')
    (hn : D.toNat + d + n ≤ 2 ^ 64) : Frame [⟨off D d, n⟩] m m' := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  refine h x (Classical.byContradiction fun hne => hc ?_)
  have h₁ : d ≤ ofs D x := by omega_using [hne]
  have h₂ : ofs D x < d + n := by omega_using [hne]
  have e : (x - off D d).toNat = ofs D x - d := by
    simp only [ofs, off]
    rw [← BitVec.sub_sub]
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn, hne])]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn, hne])]; exact h₁
  omega_using [hne, e]

/-- A word read apart from a span that changed. -/
theorem Outside.readW_far {D : Addr} {d n : Nat} {m m' : Mem} (h : Outside D d n m m')
    (hn : D.toNat + d + n ≤ 2 ^ 64) {a : Addr} (ha : Region.Disjoint ⟨a, 4⟩ ⟨off D d, n⟩) :
    m'.readW a 32 = m.readW a 32 :=
  (Outside.frame_span h hn).readW (r := ⟨a, 4⟩) (Region.contains_self _ _)
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ha) (by decide)

/-- `[r + 0]` for `r = S + x`, `S + x + 4` within 32 bits. -/
theorem ea_far {s : State} {S : Addr} {r : Reg} {x : Nat} (hp : PtrAt s S r x)
    (hx : S.toNat + x + 4 ≤ 2 ^ 32) : s.ea (at_ r 0) = off S x := by
  rw [at_, ea_mk, addr_eq (by omega_using [])]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hS : S.toNat < 2 ^ 64 := S.isLt
  rw [Nat.mod_eq_of_lt (a := (s.gpr r).toNat) (by have := (s.gpr r).isLt; omega_using []), hp]
  repeat rw [Nat.mod_eq_of_lt (by omega_arith)]
  omega_using []

/-- A readable span at `S + x`. -/
structure Span (s : State) (S : Addr) (x n : Nat) : Prop where
  read : InRegions (s.rd ++ s.wr) (off S x) n
  fit : S.toNat + x + n ≤ 2 ^ 32

theorem Span.of_keeps {s t : State} {S : Addr} {x n : Nat} {rs : List Reg} (h : Span s S x n) (K : Keeps rs s t) :
    Span t S x n := ⟨by rw [K.2.1, K.2.2]; exact h.read, h.fit⟩

theorem Span.sub {s : State} {S : Addr} {x n : Nat} (h : Span s S x n) {y k : Nat} (hy : x ≤ y)
    (hk : y + k ≤ x + n) : Span s S y k := by
  refine ⟨?_, by have := h.fit; omega_using [hk, this]⟩
  have := VG.CallLay.inRegions_sub h.read (off := y - x) (l := k) (by omega_using [hy, hk]) (by have := h.fit; omega_using [this])
  rwa [show off S x + BitVec.ofNat 64 (y - x) = off S y by
    rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using [hy]] at this

/-- A load through `r = S + x` of a readable span. -/
theorem readSrc_far {s : State} {S : Addr} {r : Reg} {x : Nat} (hp : PtrAt s S r x) (hs : Span s S x 4) :
    readSrc s (.mem (at_ r 0)) = some (s.mem.readW (off S x) 32) := by
  show s.load32 (s.ea (at_ r 0)) = _
  rw [ea_far hp hs.fit, State.load32, ite_eq_left_iff.mpr fun h => absurd hs.read h]

/-- `selectLoop`: the destination's `N` words (at `D + d`, of a writable
region) set to the source's (a readable span at `S + x`, apart from them)
where the mask `ecx` is all ones, else kept. -/
theorem selectLoop_far_ok {t₀ : State} {D S : Addr} {L : Nat} (hw : Ws t₀ D L) {x d N : Nat} (k : Bool)
    (hN : 0 < N) (hs : Span t₀ S x (4 * N)) (hd : d + 4 * N ≤ L)
    (hdx : Region.Disjoint ⟨off S x, 4 * N⟩ ⟨off D d, 4 * N⟩)
    (hebp : PtrAt t₀ S .ebp x) (hebx : PtrAt t₀ D .ebx d)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask k) :
    WP isa VG.Impl.Bignum.X86.CrtRt.selectLoop t₀
      fun u => Outside D d (4 * N) t₀.mem u.mem ∧
        val32 u.mem D d N = (if k then val32 t₀.mem S x N else val32 t₀.mem D d N) ∧
        PtrAt u D .ebx (d + 4 * N) ∧ PtrAt u S .ebp (x + 4 * N) ∧ Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  have hsf := hs.fit
  unfold VG.Impl.Bignum.X86.CrtRt.selectLoop
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ t ∧
      PtrAt t S .ebp (x + 4 * j) ∧ PtrAt t D .ebx (d + 4 * j) ∧ (t.gpr .edi).toNat = 4 * (N - j) ∧
      Outside D d (4 * j) t₀.mem t.mem ∧
      val32 t.mem D d j = (if k then val32 t₀.mem S x j else val32 t₀.mem D d j)) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hedi, Outside.refl _ _ _ _,
      by cases k <;> rfl⟩) fun u ⟨K, pe, P, _, O, V⟩ => ⟨O, V, P, pe, K⟩
  rintro j t hj ⟨Kt, ebp, ebx, edi, O, V⟩
  have ht := hw.of_keeps Kt
  have ecx : t.gpr .ecx = cmask k := by rw [Kt.1 _ (by decide)]; exact hecx
  have sj : Span t S (x + 4 * j) 4 := (hs.of_keeps Kt).sub (by omega_using []) (by omega_using [hj])
  have xw : t.mem.readW (off S (x + 4 * j)) 32 = t₀.mem.readW (off S (x + 4 * j)) 32 :=
    Outside.readW_far (n := 4 * N) (O.mono (Nat.le_refl _) (by omega_using [hj])) (by omega_using [hd, hn])
      (hdx.sub_left (Offset.sub S (by omega_using []) (by omega_using [hj])))
  have dw : w32 t.mem D (d + 4 * j) = w32 t₀.mem D (d + 4 * j) :=
    O.w32 (by omega_using []) (by omega_using [hd, hj, hn])
  refine wp_movS (readSrc_ptr ht ebx (d := 0) (by omega_using [hd, hj])) fun s₁ u₁ _ => ?_
  have ebp₁ : PtrAt s₁ S .ebp (x + 4 * j) := by rw [PtrAt, u₁.other _ (by decide)]; exact ebp
  refine wp_movS (readSrc_far ebp₁ (sj.of_keeps u₁.keeps)) fun s₂ u₂ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₃ u₃ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  have K₅ : Keeps [.eax, .edx] t s₅ :=
    (((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps |>.widen u₄.keeps).widen u₅.keeps
  have ht₅ := ht.of_keeps K₅
  have ebx₅ : PtrAt s₅ D .ebx (d + 4 * j) := by rw [PtrAt, K₅.1 _ (by decide)]; exact ebx
  refine wp_storeS (ea_ptr ht₅ ebx₅ (d := 0) (by omega_using [hd, hj]))
    (ws_write ht₅ (y := d + 4 * j + 0) (n := 4) (by omega_using [hd, hj])) fun s₆ m₆ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => wp_addS rfl fun s₈ u₈ _ => wp_subZ rfl fun s₉ u₉ z₉ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf edi hj
  have r₆ : ∀ r, r = .ebp ∨ r = .ebx ∨ r = .edi → s₆.gpr r = t.gpr r := by
    intro r hr; rw [m₆.gpr]; apply K₅.1; rcases hr with rfl | rfl | rfl <;> decide
  have mem₅ : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ecx₃ : s₃.gpr .ecx = t.gpr .ecx := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have eax₅ : s₅.gpr .eax = t.mem.readW (off D (d + 4 * j)) 32 ^^^
      ((t.mem.readW (off S (x + 4 * j)) 32 ^^^ t.mem.readW (off D (d + 4 * j)) 32) &&&
        (if k then BitVec.allOnes 32 else 0)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, ecx₃, ecx, u₃.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, Nat.add_zero]
    rfl
  rw [select_val] at eax₅
  refine ⟨⟨Kt.trans ((((K₅.mono (by decide)).widen (m₆.keeps [])).widen u₇.keeps |>.widen u₈.keeps).widen u₉.keeps),
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, r₆ _ (.inl rfl)]
    rw [VG.Proof.Mont.X86.Rt.ptr_add ebp]; congr 1
  · rw [PtrAt, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), r₆ _ (.inr (.inl rfl))]; exact ptr4 ebx
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), r₆ _ (.inr (.inr rfl))]; exact c₁
  · rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, mem₅, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hd, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, mem₅, Nat.add_zero, val32_store hn (by omega_using [hd, hj]), V, eax₅,
      val32_succ t₀.mem S x, val32_succ t₀.mem D d]
    have xw' : (t.mem.readW (off S (x + 4 * j)) 32).toNat = w32 t₀.mem S (x + 4 * j) := by rw [xw]
    have dw' : (t.mem.readW (off D (d + 4 * j)) 32).toNat = w32 t₀.mem D (d + 4 * j) := dw
    cases k
    · simp only [Bool.false_eq_true, ite_false, dw']
    · simp only [ite_true, xw']
  · rw [z₉, u₈.other _ (by decide), u₇.other _ (by decide), r₆ _ (.inr (.inr rfl)), c₂]

end VG.Proof.Ffdh.X86.Cached

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- A number apart from the bytes that changed keeps its value. -/
theorem val32_far {rs : List Region} {m m' : Mem} (F : Frame rs m m') {P : Addr} {d N : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨off P d, 4 * N⟩ r) (hn : 4 * N < 2 ^ 64) :
    val32 m' P d N = val32 m P d N := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  exact congrArg BitVec.toNat (F.read (Region.contains_self _ _) hd hn)

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The context's address. -/
abbrev ctxAddr (args : Nat → BitVec 32) : Addr := byteAddr (args ctxArg)

/-- The context's bytes: three words, then 34 rows of `B` bytes. -/
abbrev ctxBytes (len : Nat) : Nat := 24 + bc len .wide * 34

/-- `r :=` the address of row `j` of the context, `ctx + 24 + B j`. -/
theorem rowAt_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {r : Reg} {j : Nat}
    (hj : j ≤ 34) (heax : s.gpr .eax = BitVec.ofNat 32 j)
    (k : ∀ u, Keeps [.eax, .ecx, .edx, r] s u → u.mem = s.mem →
      PtrAt u (ctxAddr args) r (24 + bc len .wide * j) → WP isa (.block is) u Q) :
    WP isa (.block (rowAt r ++ is)) s Q := by
  have hb := bc_le h.upper' .wide
  unfold rowAt
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine widthC_ok h.width h.upper' fun s₁ K₁ m₁ e₁ => wp_mul fun s₂ U₂ => ?_
  have h₁ := h.regs K₁ m₁
  have h₂ := h₁.regs ⟨fun q hq => U₂.other q (by simp at hq; exact hq.1) (by simp at hq; exact hq.2), U₂.rd,
    U₂.wr⟩ U₂.mem (rs := [.eax, .edx])
  refine wp_movS (h₂.arg (i := ctxArg) (by decide)) fun s₃' U₃' _ => wp_addS rfl fun s₃ U₃ _ =>
    wp_addS rfl fun s₄ U₄ _ => wp_mov fun u U => ?_
  refine k u ?_ (by rw [U.mem, U₄.mem, U₃.mem, U₃'.mem, U₂.mem, m₁]) ?_
  · refine ⟨fun q hq => ?_, by rw [U.rd, U₄.rd, U₃.rd, U₃'.rd, U₂.rd, K₁.2.1],
      by rw [U.wr, U₄.wr, U₃.wr, U₃'.wr, U₂.wr, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [U.other q hq.2.2.2, U₄.other q hq.1, U₃.other q hq.1, U₃'.other q hq.2.1, U₂.other q hq.1 hq.2.2.1,
      K₁.1 q (by simpa using hq.2.2.1)]
  · have ea : (s₁.gpr .eax).toNat = j := by
      rw [K₁.1 _ (by decide), heax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj])]
    rw [PtrAt, U.gpr, U₄.gpr, U₃.gpr, U₃'.gpr, U₃'.other _ (by decide), U₂.eax, e₁, ea, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hb])]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, ctxAddr, byteAddr, BitVec.toNat_setWidth]
    have a32 := (args ctxArg).isLt
    rw [Nat.mod_eq_of_lt (a := (args ctxArg).toNat) (by omega_using [])]
    rw [Nat.mod_eq_of_lt (a := j * bc len .wide) (by
      have := Nat.mul_le_mul_right (bc len .wide) hj; omega_using [hb, this])]
    rw [show BitVec.toNat (24 : BitVec 32) = 24 from rfl, Nat.mul_comm j]
    omega_using []

/-- The context readable, apart from the working space. -/
structure CtxRd (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  span : Span s (ctxAddr args) 0 (ctxBytes len)
  apart : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ ⟨base, bytes⟩

theorem CtxRd.keep {t : State} {rs : List Reg} (C : CtxRd base bytes len args s) (K : Keeps rs s t) :
    CtxRd base bytes len args t := ⟨C.span.of_keeps K, C.apart⟩

/-- The context's 32-bit address does not wrap. -/
theorem CtxRd.afit (C : CtxRd base bytes len args s) : (args ctxArg).toNat + ctxBytes len ≤ 2 ^ 32 := by
  have fit := C.span.fit
  have hv : (byteAddr (args ctxArg)).toNat = (args ctxArg).toNat := by
    simp only [byteAddr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (args ctxArg).isLt; omega_using [])
  simp only [ctxAddr] at fit
  omega_using [fit, hv]

/-- A span of the context, within it. -/
theorem CtxRd.row (C : CtxRd base bytes len args s) {d n : Nat} (hd : d + n ≤ ctxBytes len) :
    Span s (ctxAddr args) d n := C.span.sub (Nat.zero_le _) (by omega_using [hd])

/-- Entry `e` (at `ebp`) into slot 7 if it is the window word's; `ebp` past it. -/
theorem combSelectStep_ok (h : In Ex base bytes len args s) (C : CtxRd base bytes len args s) {e D : Nat} (he : e < 32)
    (hw : w32 s.mem base winOff = D) (hD : D < 32)
    (hebp : PtrAt s (ctxAddr args) .ebp (24 + bc len .wide * (2 + e))) :
    WP isa (selectStep e) s fun u =>
      In Ex base bytes len args u ∧ Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem ∧
      PtrAt u (ctxAddr args) .ebp (24 + bc len .wide * (2 + (e + 1))) ∧
      sv u.mem base len .wide 7 = (if D = e then val32 s.mem (ctxAddr args) (24 + bc len .wide * (2 + e))
        (cwc len .wide) else sv s.mem base len .wide 7) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have f7 := h.slot_fit .wide (j := 7) (by decide)
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have hb := bc_le h.upper' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  have ce : 2 + e ≤ 33 := by omega_using [he]
  have row := Nat.mul_le_mul_left (bc len .wide) (show 2 + e + 1 ≤ 34 by omega_using [he])
  rw [Nat.mul_add, Nat.mul_one] at row
  unfold Generate.selectStep
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.windowMask_ok h.scratch (j := e)
    (by omega_using [f7, est]) (by rw [← wo, hw]; exact hD) he) fun s₁ ⟨m₁, c₁, K₁⟩ => ?_))
  have h₁ := h.regs K₁ m₁
  refine ptrTo_ok (r := .ebx) (t := .edx) (x := .slot .wide 7) (by decide) (by decide) h₁.edi h₁.width h.upper'
    (by omega_using [bl, f7]) fun s₂ K₂ m₂ p₂ => ?_
  have h₂ := h₁.regs K₂ m₂
  refine cntTo_ok (n := one .wide) (r := .edi) h₂.width h.upper' (by decide) fun s₃ K₃ m₃ e₃ => WP.block_nil ?_
  have K₁₃ : Keeps [.eax, .ebx, .ecx, .edx, .edi] s s₃ :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))
  have m₁₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  have ws₃ : Ws s₃ base bytes := h.ws.of_keeps K₁₃
  have ebp₃ : PtrAt s₃ (ctxAddr args) .ebp (24 + bc len .wide * (2 + e)) := by
    rw [PtrAt, K₁₃.1 _ (by decide)]; exact hebp
  have ebx₃ : PtrAt s₃ base .ebx (lo len (.slot .wide 7)) := by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂
  have edi₃ : (s₃.gpr .edi).toNat = 4 * cwc len .wide := by
    rw [e₃, cb1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]; exact bw
  have ecx₃ : s₃.gpr .ecx = cmask (decide (D = e)) := by
    rw [K₃.1 _ (by decide), K₂.1 _ (by decide), c₁, show w32 s.mem base 4 = D from hw]
    simp only [cmask, decide_eq_true_eq]
  have span : Span s₃ (ctxAddr args) (24 + bc len .wide * (2 + e)) (4 * cwc len .wide) :=
    (C.keep K₁₃).row (by simp only [ctxBytes]; omega_using [bw, row])
  have dis : Region.Disjoint ⟨off (ctxAddr args) (24 + bc len .wide * (2 + e)), 4 * cwc len .wide⟩
      ⟨off base (lo len (.slot .wide 7)), 4 * cwc len .wide⟩ :=
    (C.apart.sub_left (Offset.sub_base _ (by simp only [ctxBytes]; omega_using [bw, row]))).sub_right
      (Offset.sub_base _ (by omega_using [he, bl, nw, f7, bw, g, hb, est, e7, nb, ce, row, e₃, edi₃]))
  refine WP.seq (WP.mono (selectLoop_far_ok ws₃ (decide (D = e)) (by omega) span (by omega_using [he, bl, nw, f7, bw, g, hb, est, e7, nb, ce, row, e₃, edi₃]) dis ebp₃ ebx₃ edi₃ ecx₃)
    fun t ⟨O, V, _, pe, Kt⟩ => ?_)
  have K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K₁₃.mono (by decide)).trans (Kt.mono (by decide))
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← m₁₃]; exact O.mono (Nat.zero_le _) (by omega_using [he, bl, nw, f7, bw, g, hb, est, e7, nb, ce, row, e₃, edi₃])
  refine wp_movS ((h.stack 16 (by decide)).keep K₀ (by decide) Oall).readSrc fun u U _ => WP.block_nil ?_
  have ed : u.gpr .edi = s.gpr .edi := by rw [U.gpr]; exact h.edi_eq
  have Ku : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp])
      ((K₀.trans (U.keeps.mono (by decide))).mono (by decide)) ed
  have Ou : Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem := by
    rw [U.mem, ← m₁₃, bw]; exact O
  refine ⟨h.keep Ku (by decide) (by decide) (by rw [U.mem]; exact Oall), Ou, ?_, ?_, Ku⟩
  · rw [PtrAt, U.other _ (by decide), pe, ← bw, show 2 + (e + 1) = (2 + e) + 1 by omega_using [], Nat.mul_succ]
    congr 1; omega_using []
  · simp only [sv]
    rw [U.mem, V, m₁₃]
    by_cases d : D = e <;> simp [d]

/-- Slot 7 the context's entry of the digit in the window word (below 32), by scanning all 32 entries. -/
theorem select_ok (h : In Ex base bytes len args s) (C : CtxRd base bytes len args s) {D : Nat}
    (hw : w32 s.mem base winOff = D) (hD : D < 32) :
    WP isa Generate.select s fun u =>
      In Ex base bytes len args u ∧ Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem ∧
      sv u.mem base len .wide 7 = val32 s.mem (ctxAddr args) (24 + bc len .wide * (2 + D)) (cwc len .wide) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have f7 := h.slot_fit .wide (j := 7) (by decide)
  have bw := bc_eq_cwc len .wide
  have hb := bc_le h.upper' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  unfold Generate.select
  refine WP.seq (WP.mono (zero_ok h (x := .slot .wide 7) (one_ok .wide) (by rw [cb1]; omega_using [f7, est]))
    fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_using [f7, est]))
  refine WP.seq (wp_movS rfl fun s₂ U₂ _ => rowAt_ok (r := .ebp) (j := 2) (h₁.regs U₂.keeps U₂.mem) (by decide)
    U₂.gpr fun s₃ K₃ m₃ p₃ => WP.block_nil ?_)
  have K₁₃ : Keeps [.eax, .ecx, .edx, .ebp] s s₃ :=
    (K₁.trans (U₂.keeps.mono (by decide))).trans (K₃.mono (by decide))
  have m₁₃ : s₃.mem = s₁.mem := by rw [m₃, U₂.mem]
  have h₃ := h₁.regs ((U₂.keeps.mono (by decide)).trans (K₃.mono (by decide)) : Keeps [.eax, .ecx, .edx, .ebp] s₁ s₃)
    m₁₃
  have C₀ : CtxRd base bytes len args s₃ := C.keep K₁₃
  -- The context did not change: only slot 7 did.
  have far : ∀ {m m' : Mem}, Outside base (lo len (.slot .wide 7)) (bc len .wide) m m' → ∀ j < 32,
      val32 m' (ctxAddr args) (24 + bc len .wide * (2 + j)) (cwc len .wide) =
        val32 m (ctxAddr args) (24 + bc len .wide * (2 + j)) (cwc len .wide) := fun {m m'} O j hj => by
    have row := Nat.mul_le_mul_left (bc len .wide) (show 2 + j + 1 ≤ 34 by omega_using [hj])
    rw [Nat.mul_add, Nat.mul_one] at row
    refine val32_far (Outside.frame_span O (by omega_using [nw, f7, hb])) (fun r hr => ?_) (by omega)
    obtain rfl := List.mem_singleton.mp hr
    exact (C.apart.sub_left (Offset.sub_base _ (by simp only [ctxBytes]; omega_using [bw, row]))).sub_right
      (Offset.sub_base _ (by omega_using [f7, est]))
  refine WP.mono (wp_seqs_range Generate.selectStep (fun e u => In Ex base bytes len args u ∧
      Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem ∧
      PtrAt u (ctxAddr args) .ebp (24 + bc len .wide * (2 + e)) ∧
      sv u.mem base len .wide 7 = (if D < e then val32 s.mem (ctxAddr args) (24 + bc len .wide * (2 + D))
        (cwc len .wide) else 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u) 32 (fun e he u ⟨Iu, Ou, pu, Vu, Ku⟩ => ?_)
    ⟨h₃, by rw [m₁₃]; exact O₁, p₃, by simp only [sv]; rw [m₁₃, V₁]; simp, K₁₃.mono (by decide)⟩)
    fun u ⟨Iu, Ou, _, Vu, Ku⟩ => ⟨Iu, Ou, by rw [Vu]; simp [hD], Ku⟩
  have wu : w32 u.mem base winOff = D := by rw [Ou.w32 (by omega_using [est, e7, wo]) (by omega_using [wo])]; exact hw
  refine WP.mono (combSelectStep_ok Iu (C.keep Ku) he wu hD pu) fun v ⟨Iv, Ov, pv, Vv, Kv⟩ =>
    ⟨Iv, Ou.trans Ov, pv, ?_, Ku.trans Kv⟩
  rw [Vv, Vu, far Ou e he]
  by_cases d : D = e
  · subst d; simp
  · by_cases l : D < e
    · simp [d, l, show D < e + 1 by omega_using [l]]
    · simp [d, l, show ¬ D < e + 1 by omega_using [d, l]]

end

end VG.Proof.Ffdh.X86.Cached
