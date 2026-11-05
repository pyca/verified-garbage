module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Impl.Ffdh.X86.Cached
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers
import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
import VerifiedGarbage.Proof.Framework.Omega

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
    refine wp_seqs_append (WP.mono (wp_seqs_range f I n (fun e he => hs e (by omega)) h) fun u hu => ?_)
    rw [List.map_singleton, seqs_cons]
    exact WP.seq (WP.mono (hs n (by omega) u hu) fun v hv => WP.block_nil hv)

/-! ## Words of a number -/

theorem w32_of_val32 (m : Mem) (base : Addr) : ∀ (N d q : Nat), q < N →
    w32 m base (d + 4 * q) = val32 m base d N / 2 ^ (32 * q) % 2 ^ 32
  | 0, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | N + 1, d, 0, _ => by
    rw [val32, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (show w32 m base d < 2 ^ 32 from BitVec.isLt _)]
  | N + 1, d, q + 1, hq => by
    rw [val32, show d + 4 * (q + 1) = (d + 4) + 4 * q by omega, w32_of_val32 m base N (d + 4) q (by omega),
      show 32 * (q + 1) = 32 + 32 * q by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 32), Nat.div_eq_of_lt (show w32 m base d < 2 ^ 32 from BitVec.isLt _), Nat.zero_add]

/-- Bit `k` of a number from its word `⌊k / 32⌋`. -/
theorem bit_of_word (x k : Nat) :
    x / 2 ^ (32 * (k / 32)) % 2 ^ 32 / 2 ^ (k % 32) % 2 = VG.Proof.Rsa.FixedBaseComb.bit x k := by
  unfold VG.Proof.Rsa.FixedBaseComb.bit
  have h32 : k % 32 < 32 := Nat.mod_lt _ (by decide)
  conv => rhs; rw [← Nat.div_add_mod k 32, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x / 2 ^ (32 * (k / 32)) = y
  have dv : 2 ^ (k % 32) * 2 ∣ 2 ^ 32 := by
    rw [← Nat.pow_succ]; exact Nat.pow_dvd_pow 2 (by omega)
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
  have b31 : 1 ≤ b ∧ b ≤ 31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; omega
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
  have step : ∀ {b : Nat}, b ∈ [16, 8, 4, 2, 1] → ∀ {u : State} {rest : List Nat},
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
      have ecx : u.gpr .ecx = BitVec.ofNat 32 c := by rw [K.1 _ (by decide), hecx]
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
  have f13 := h.slot_fit .wide (j := 13) (by decide)
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have hb := bc_le h.upper' .wide
  unfold Generate.bit
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mov fun s₁ U₁ => wp_shr (by decide) fun s₂ U₂ => wp_addS rfl fun s₃ U₃ _ =>
    wp_addS rfl fun s₄ U₄ _ => ?_)
  have e₄ : (s₄.gpr .ecx).toNat = 4 * (k / 32) := by
    rw [U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr, hesi]
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hk]
    omega
  have K₄ : Keeps [.ecx] s s₄ := (((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps).widen U₄.keeps
  have m₄ : s₄.mem = s.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have h₄ := h.regs K₄ m₄
  refine widthC_ok h₄.width h.upper' fun s₅ K₅ m₅ e₅ => wp_cmpC rfl fun s₆ F₆ c₆ => WP.block_nil ?_
  have ecx₅ : (s₅.gpr .ecx).toNat = 4 * (k / 32) := by rw [K₅.1 _ (by decide)]; exact e₄
  rw [ecx₅, e₅, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at c₆
  have K₆ : Keeps [.ecx, .edx] s s₆ := (K₄.mono (by decide)).trans (K₅.mono (by decide)) |>.trans
    ⟨fun r _ => by rw [F₆.gpr], F₆.rd, F₆.wr⟩
  have m₆ : s₆.mem = s.mem := by rw [F₆.mem, m₅, m₄]
  have h₆ := h.regs K₆ m₆
  have esi₆ : s₆.gpr .esi = BitVec.ofNat 32 k := by rw [K₆.1 _ (by decide), hesi]
  have ecx₆ : (s₆.gpr .ecx).toNat = 4 * (k / 32) := by rw [F₆.gpr]; exact ecx₅
  have x13 := val32_lt s.mem base (lo len (.slot .wide 13)) (cwc len .wide)
  refine WP.ite (decide (4 * (k / 32) < bc len .wide)) (by simp only [eval, c₆]) (fun e => ?_)
    (fun e => wp_movS rfl fun u U _ => WP.block_nil ⟨by rw [U.mem, m₆], (K₆.mono (by decide)).trans (U.keeps.mono (by decide)), ?_⟩)
  · have lt : k / 32 < cwc len .wide := by have := of_decide_eq_true e; omega
    refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h₆.edi h₆.width h.upper'
      (by omega) fun s₇ K₇ m₇ p₇ => ?_)
    refine wp_addS rfl fun s₈ U₈ _ => ?_
    have p₈ : PtrAt s₈ base .ebp (lo len (.slot .wide 13) + 4 * (k / 32)) := by
      rw [PtrAt, U₈.gpr, BitVec.toNat_add, p₇, K₇.1 _ (by decide), ecx₆]; omega
    have K₈ : Keeps [.ecx, .edx, .ebp] s s₈ := (K₆.mono (by decide)).trans ((K₇.mono (by decide)).trans
      (U₈.keeps.mono (by decide)))
    have m₈ : s₈.mem = s.mem := by rw [U₈.mem, m₇, m₆]
    have h₈ := h.regs K₈ m₈
    refine wp_movS (VG.Proof.Mont.X86.Rt.readSrc_ptr h₈.ws p₈ (d := 0) (by omega)) fun s₉ U₉ _ => ?_
    refine wp_mov fun s₁₀ U₁₀ => wp_logicS (.inl rfl) rfl fun s₁₁ U₁₁ => WP.block_nil ?_
    have esi₈ : s₈.gpr .esi = BitVec.ofNat 32 k := by rw [K₈.1 _ (by decide), hesi]
    have ecx₁₁ : s₁₁.gpr .ecx = BitVec.ofNat 32 (k % 32) := by
      rw [U₁₁.gpr, U₁₀.gpr, U₉.other _ (by decide), esi₈]
      simp only [↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
      rw [show BitVec.toNat (31 : BitVec 32) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have eax₁₁ : (s₁₁.gpr .eax).toNat = sv s.mem base len .wide 13 / 2 ^ (32 * (k / 32)) % 2 ^ 32 := by
      rw [U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.gpr, Nat.add_zero, m₈]
      exact w32_of_val32 s.mem base (cwc len .wide) _ _ lt
    have K₁₁ : Keeps [.eax, .ecx] s₈ s₁₁ := ((U₉.keeps.mono (by decide)).widen U₁₀.keeps).widen U₁₁.keeps
    refine WP.mono (shifts_ok (Nat.mod_lt _ (by decide)) ecx₁₁ eax₁₁) fun u ⟨mu, Ku, eu⟩ => ⟨?_, ?_, ?_⟩
    · rw [mu, U₁₁.mem, U₁₀.mem, U₉.mem, m₈]
    · exact (K₈.mono (by decide)).trans ((K₁₁.mono (by decide)).trans (Ku.mono (by decide)))
    · rw [eu]; exact bit_of_word _ _
  · rw [U.gpr]
    have ge : 32 * cwc len .wide ≤ k := by have := of_decide_eq_false e; omega
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
  have O : Outside base d 4 s.mem u.mem := by rw [M.mem]; exact writeW32_outside _ _ _ (by omega_arith)
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
    have ht := h.regs K m
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
  have p16 : 2 ^ j ≤ 16 := Nat.pow_le_pow_right (show 0 < 2 by decide) (show j ≤ 4 by omega)
  unfold tooth
  simp only [List.cons_append, List.nil_append]
  rw [← List.append_nil (List.replicate j (Instr.alu .add .esi (.mem (sc rowsOff))))]
  refine WP.seq (wp_movS (readW_ok h (d := iOff) (by omega) hI (by omega)) fun s₁ U₁ _ =>
    wp_subS rfl fun s₂ U₂ _ => ?_)
  have K₂ : Keeps [.esi] s s₂ := (U₁.keeps.mono (by decide)).widen U₂.keeps
  have m₂ : s₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  refine addsMem_ok h (d := rowsOff) (by omega) hR (by omega) j m₂ K₂ fun s₃ K₃ m₃ e₃ => WP.block_nil ?_
  have k3 : i - 1 + j * R < 2 ^ 32 := by have := Nat.mul_le_mul_right R (show j ≤ 4 by omega); omega
  have esi₃ : s₃.gpr .esi = BitVec.ofNat 32 (i - 1 + j * R) := by
    rw [e₃, U₂.gpr, U₁.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), BitVec.ofNat_add_ofNat]
  have h₃ := h.regs K₃ m₃
  refine WP.seq (WP.mono (bit_ok h₃ k3 esi₃) fun s₄ ⟨m₄, K₄, e₄⟩ => ?_)
  rw [m₃] at e₄
  have h₄ := h₃.regs K₄ m₄
  refine wp_logicS (.inl rfl) rfl fun s₅ U₅ => ?_
  have v₅ : (s₅.gpr .eax).toNat = VG.Proof.Rsa.FixedBaseComb.bit (sv s.mem base len .wide 13) (i - 1 + j * R) := by
    rw [U₅.gpr]; simp only [↓reduceIte]
    rw [BitVec.toNat_and, show BitVec.toNat (1 : BitVec 32) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.pow_one, e₄]
  have bl := VG.Proof.Rsa.FixedBaseComb.bit_lt (sv s.mem base len .wide 13) (i - 1 + j * R)
  have bj : VG.Proof.Rsa.FixedBaseComb.bit (sv s.mem base len .wide 13) (i - 1 + j * R) * 2 ^ j ≤ 16 :=
    Nat.le_trans (Nat.mul_le_mul_right (2 ^ j) (Nat.le_of_lt_succ bl)) (by omega)
  refine addsSelf_ok j fun s₆ K₆ m₆ e₆ => ?_
  rw [v₅, Nat.mod_eq_of_lt (by omega)] at e₆
  have K₅₆ : Keeps [.eax] s₄ s₆ := (U₅.keeps.mono (by decide)).trans K₆
  have m₆' : s₆.mem = s.mem := by rw [m₆, U₅.mem, m₄, m₃]
  have h₆ := h.regs ((K₃.mono (by decide)).trans ((K₄.mono (by decide)).trans (K₅₆.mono (by decide))) :
    Keeps [.eax, .ecx, .edx, .ebp, .esi] s s₆) m₆'
  refine wp_orS (readW_ok h₆ (d := winOff) (v := W) (by omega) (by rw [m₆']; exact hW) (by omega)) fun s₇ U₇ => ?_
  have h₇ := h₆.regs U₇.keeps U₇.mem
  refine WP.mono (storeW_ok h₇ (d := winOff) (by omega) .eax) fun u ⟨I, O, Wu, Ku⟩ => ⟨I, ?_, ?_, ?_⟩
  · rw [U₇.mem, m₆'] at O; exact O
  · rw [Wu, U₇.gpr, BitVec.toNat_or, e₆, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
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
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ this)) (by omega)
    omega

theorem teeth_digit (bits x row : Nat) :
    teeth x row (Spec.Rsa.FixedBaseComb.rows bits) 5 = VG.Proof.Rsa.FixedBaseComb.digit bits x row := by
  simp only [teeth, VG.Proof.Rsa.FixedBaseComb.digit, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    Nat.pow_zero, Nat.mul_one]
  omega

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
  have f13 := h.slot_fit .wide (j := 13) (by decide)
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  unfold Generate.digit
  refine WP.seq (wp_movS rfl fun s₁ U₁ _ => ?_)
  have h₁ := h.regs U₁.keeps U₁.mem
  refine WP.mono (storeW_ok h₁ (d := winOff) (by omega) .eax) fun s₂ ⟨I₂, O₂, W₂, K₂⟩ => ?_
  rw [U₁.mem] at O₂
  rw [U₁.gpr] at W₂
  have K₁₂ : Keeps [.eax, .ecx, .edx, .ebp, .esi] s s₂ := (U₁.keeps.mono (by decide)).trans (K₂.mono (by decide))
  refine wp_seqs_range tooth (fun e u => In Ex base bytes len args u ∧ Outside base winOff 4 s.mem u.mem ∧
      w32 u.mem base winOff = teeth (sv s.mem base len .wide 13) (i - 1) R e ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s u) 5 (fun e he u ⟨Iu, Ou, Wu, Ku⟩ => ?_) ⟨I₂, O₂, W₂, K₁₂⟩
  have iu : w32 u.mem base iOff = i := by rw [Ou.w32 (by omega) (by omega)]; exact hI
  have ru : w32 u.mem base rowsOff = R := by rw [Ou.w32 (by omega) (by omega)]; exact hR
  have xu : sv u.mem base len .wide 13 = sv s.mem base len .wide 13 :=
    Ou.val32 (.inr (by omega_arith)) (by omega_arith)
  refine WP.mono (tooth_ok Iu (j := e) he hi iu ru hb Wu (teeth_lt _ _ _ e)) fun v ⟨Iv, Ov, Wv, Kv⟩ =>
    ⟨Iv, Ou.trans Ov, ?_, Ku.trans Kv⟩
  rw [Wv, xu, teeth]

end

end VG.Proof.Ffdh.X86.Cached
