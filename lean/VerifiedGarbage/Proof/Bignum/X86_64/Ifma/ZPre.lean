module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Exp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# RSA with AVX512_IFMA on x86-64: around the exponentiations modulo `-1 (mod 2¹⁰⁴)`

With `ammCoreZ` the exponentiations run modulo a multiple `X = 2¹⁰⁴ m - 1`
of each prime, `m = 2^(-104)` modulo the prime: `zPre`
(`Impl/Rsa/X86_64/CrtIfma.lean`) makes `m` at `oMs` and the numbers the
exponentiations start from, and `zPost` multiplies their result by the last
multiplier modulo the prime (`zBody_ok`: the three in sequence, as
`vecBody_ok` is for the other layouts).
-/
-- separate module: what only `ammCoreZ`'s layouts run; `Vec` is every layout's vector code.

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum.Amm52 (lval lval_congr)
open VG.Proof.Bignum (off word ofs Outside writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (stMem stMem_outside word_stMem cop2)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The offsets of the layout's numbers in a region. -/
theorem ZOk.slots (hz : ZOk l) : l.NB = 192 ∧ l.oK0 = 192 ∧ l.oY = 224 ∧ l.oX = 416 ∧ l.oS = 608 ∧
    l.oK1 + l.NB ≤ l.oV ∧ l.oX + l.NB ≤ l.oK1 ∧ l.oS + l.NB ≤ l.oK1 ∧ l.oV + 32 = l.oFin ∧
    l.oMs = l.oFin + 192 ∧ l.oF2 = l.oFin + 384 ∧ l.D = l.oFin + 576 ∧ l.D = 4800 ∧ l.L = 24 ∧ l.nl = 2 := by
  rw [hz]; decide

theorem ZOk.oE (hz : ZOk l) : l.oS + l.NB ≤ l.oE := by rw [hz]; decide

/-! ## A number with one limb -/

/-- Stores of `rax` at offsets of `rbx`. -/
theorem stB_ok {B : Addr} {v : BitVec 64} :
    ∀ (ds : List Nat) (s : State), s.gpr .rbx = B → s.gpr .rax = v →
      (∀ d ∈ ds, InRegions s.wr (B + BitVec.ofNat 64 d) 8) →
      WP isa (.block (ds.map fun d => .store (at_ .rbx d) .rax)) s
        fun s' => s' = { s with mem := stMem s.mem B v ds }
  | [], s, _, _, _ => WP.block_nil rfl
  | d :: rest, s, hB, hv, hw => by
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off B d) v }, ?_, ?_⟩
    · simp only [exec, eaG', hB, hv, State.store64, hw d (List.mem_cons_self ..), ite_true, off]
    · exact WP.mono (stB_ok rest _ hB hv fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => h

/-- The limbs at offset `c` of `B = rbx` zeroed, then limb `j` set to `v`. -/
theorem litLane_ok (hl : AmmOk l) {s : State} {B : Addr} {c j : Nat} {v : BitVec 64} (hB : s.gpr .rbx = B)
    (hc : c + l.NB < 2 ^ 31) (hwr : ∀ q < l.L, InRegions s.wr (B + BitVec.ofNat 64 (c + l.off q)) 8)
    (hj : j < l.L) :
    WP isa (.block (([.mov32 .rax (.imm 0)] : List Instr) ++
      (List.range l.L).map (fun q => .store (at_ .rbx (c + l.off q)) .rax) ++
      ([.movImm64 .rax v, .store (at_ .rbx (c + l.off j)) .rax] : List Instr))) s fun s' =>
      (∀ q < l.L, word s'.mem B (c + l.off q) = if q = j then v else 0) ∧ Outside B c l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hF' : ∀ q < l.L, c + l.off q + 8 ≤ c + l.NB := fun q hq => by have := off_ltN hl hq; omega
  rw [List.append_assoc, List.singleton_append, WP.block_cons_iff]
  refine ⟨s.setReg32 .rax 0, rfl, ?_⟩
  have g₀ : ∀ r, r ≠ .rax → (s.setReg32 .rax 0).gpr r = s.gpr r := fun r hr => by
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr]
  rw [WP.block_append_iff, show ((List.range l.L).map fun q => Instr.store (at_ .rbx (c + l.off q)) .rax) =
    ((List.range l.L).map fun q => c + l.off q).map (fun d => .store (at_ .rbx d) .rax) by
      simp only [List.map_map, Function.comp_def]]
  refine WP.mono (stB_ok (v := 0) _ _ ((g₀ _ (by decide)).trans hB)
    (by rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl) fun d hd => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
      exact hwr q (List.mem_range.mp hq)) fun t ht => ?_
  subst ht
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  generalize hS₁ : ({ (s.setReg32 .rax 0) with
      mem := stMem (s.setReg32 .rax 0).mem B 0 ((List.range l.L).map fun q => c + l.off q) } : State).setReg .rax v = S₁
  have bx₁ : S₁.gpr .rbx = B := by rw [← hS₁, RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact (g₀ _ (by decide)).trans hB
  have ax₁ : S₁.gpr .rax = v := by rw [← hS₁, RegUpd.gpr_setReg_self]
  have g₁ : ∀ r, r ≠ .rax → S₁.gpr r = s.gpr r := fun r hr => by
    rw [← hS₁, RegUpd.gpr_setReg_of_ne _ _ hr]; exact g₀ r hr
  have m₁ : S₁.mem = stMem s.mem B 0 ((List.range l.L).map fun q => c + l.off q) := by rw [← hS₁]; rfl
  have wr₁ : S₁.wr = s.wr := by rw [← hS₁]; rfl
  have rd₁ : S₁.rd = s.rd := by rw [← hS₁]; rfl
  have x₁ : S₁.mxcsr = s.mxcsr := by rw [← hS₁]; rfl
  have hw₁ : InRegions S₁.wr (B + BitVec.ofNat 64 (c + l.off j)) 8 := by rw [wr₁]; exact hwr j hj
  rw [WP.block_cons_iff]
  refine ⟨{ S₁ with mem := S₁.mem.writeW (off B (c + l.off j)) v }, ?_, WP.block_nil ?_⟩
  · simp only [exec, eaG', bx₁, ax₁, State.store64, hw₁, ite_true, off]
  refine ⟨fun q hq => ?_, ?_, g₁, rd₁, wr₁, x₁⟩
  · show word (S₁.mem.writeW (off B (c + l.off j)) v) B (c + l.off q) = _
    by_cases e : q = j
    · subst e; rw [ite_eq_left rfl]; exact VG.Proof.Bignum.word_writeW_self _ _ _ _
    · have hs := off_sepN hl hj hq e
      rw [ite_eq_right e, (writeW_outside _ B _ (by have := hF' j hj; omega)).word (by omega)
        (by have := hF' q hq; omega), m₁]
      exact word_stMem _ _ _ _ (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩) (fun d hd => by
          obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hd
          rw [List.mem_range] at hq'
          by_cases e' : q' = q
          · exact .inl (by rw [e'])
          · exact .inr (by have := off_sepN hl hq hq' e'; omega))
        (fun d hd => by
          obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hd
          have := hF' q' (List.mem_range.mp hq'); omega)
  · show Outside B c l.NB s.mem (S₁.mem.writeW (off B (c + l.off j)) v)
    rw [m₁]
    exact (stMem_outside _ _ _ (by omega) _ fun d hd => by
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hd
      exact ⟨by omega, hF' q' (List.mem_range.mp hq')⟩).trans
      ((writeW_outside _ B _ (by have := hF' j hj; omega)).mono (by omega) (by have := hF' j hj; omega))

/-- `litN`: the number whose limb `j` is `v`, at offset `o` of both regions. -/
theorem litN_ok (hz : ZOk l) {s : State} {B : Addr} {o j : Nat} {v : BitVec 64} (hB : s.gpr .rbx = B)
    (hs : Scr s B (l.nl * l.D)) (ho : o + l.NB ≤ l.D) (hj : j < l.L) :
    WP isa (.block (litN l o j v)) s fun s' =>
      (∀ p < l.nl, ∀ q < l.L, limb l s'.mem B (l.D * p + o) q = if q = j then v.toNat else 0) ∧
      Out2 l B o l.NB s.mem s'.mem ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mxcsr = s.mxcsr := by
  have hl := hz.amm
  obtain ⟨hNB, -, -, -, -, -, -, -, -, -, -, -, hD, hL, hnl⟩ := hz.slots
  have hF' : ∀ q < l.L, l.off q + 8 ≤ l.NB := fun q hq => off_ltN hl hq
  have hwr : ∀ (t : State), t.wr = s.wr → ∀ p < 2, ∀ q < l.L,
      InRegions t.wr (B + BitVec.ofNat 64 (l.D * p + o + l.off q)) 8 := fun t ht p hp q hq => by
    rw [ht]
    have := hF' q hq
    exact hs.st (d := l.D * p + o + l.off q) (by
      rw [hnl]; rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> omega)
  unfold litN
  rw [hnl]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append, List.flatMap_singleton]
  rw [WP.block_append_iff]
  refine WP.mono (litLane_ok hl (c := l.D * 0 + o) hB (by omega) (hwr s rfl 0 (by decide)) hj)
    fun s₁ ⟨w₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_
  refine WP.mono (litLane_ok hl (c := l.D * 1 + o) ((g₁ _ (by decide)).trans hB) (by omega)
    (hwr s₁ wr₁ 1 (by decide)) hj) fun s₂ ⟨w₂, f₂, g₂, rd₂, wr₂, x₂⟩ => ?_
  refine ⟨fun p hp q hq => ?_, (Out2.of_outside (by omega) f₁).trans (Out2.of_outside (by omega) f₂),
    fun r hr => (g₂ r hr).trans (g₁ r hr), rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩
  have key : word s₂.mem B (l.D * p + o + l.off q) = if q = j then v else 0 := by
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
    · have := hF' q hq
      rw [f₂.word (.inl (by omega)) (by omega)]; exact w₁ q hq
    · exact w₂ q hq
  show (word s₂.mem B (l.D * p + o + l.off q)).toNat = _
  rw [key]
  split <;> rfl

/-- The value of a number with one limb. -/
theorem lval_single (v j : Nat) : ∀ n, lval (fun q => if q = j then v else 0) n = if j < n then v * 2 ^ (52 * j) else 0
  | 0 => by rw [VG.Proof.Bignum.Amm52.lval_zero, ite_eq_right (Nat.not_lt_zero _)]
  | n + 1 => by
    rw [VG.Proof.Bignum.Amm52.lval_succ, lval_single v j n]
    rcases Nat.lt_trichotomy j n with h | h | h
    · rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_left (by omega), Nat.zero_mul, Nat.add_zero]
    · subst h; rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _), Nat.zero_add]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), Nat.zero_mul]

/-- The value of `litN`'s number. -/
theorem val_single {m : Mem} {B : Addr} {d j v : Nat} (hj : j < l.L)
    (h : ∀ q < l.L, limb l m B d q = if q = j then v else 0) : val52 l m B d = v * 2 ^ (52 * j) := by
  unfold val52
  rw [lval_congr h, lval_single, ite_eq_left hj]

/-! ## The arithmetic -/

/-- `V = E² / R` modulo an odd `P`, for `E² 2¹⁰⁴ = R`: `V` is `2^(-104)`
modulo `P`, at most `P`. -/
theorem mhat {V P U R E2 : Nat} (h : V * R = E2 + P * U) (hU : U < R) (hE : E2 * 2 ^ 104 = R) (hE1 : 1 ≤ E2)
    (hcop : Nat.Coprime R P) : 1 ≤ V ∧ V ≤ P ∧ P ∣ 2 ^ 104 * V - 1 := by
  have hER : E2 < R := by rw [← hE]; omega
  have h1 : 1 ≤ V := by
    rcases Nat.eq_zero_or_pos V with h0 | h0
    · rw [h0, Nat.zero_mul] at h; omega
    · exact h0
  have h2 : V ≤ P := by
    have hPU : P * U ≤ P * R := Nat.mul_le_mul_left _ (Nat.le_of_lt hU)
    have : R * V < R * (P + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm R V, Nat.mul_comm R P]; omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  refine ⟨h1, h2, ?_⟩
  have h3 : R * (2 ^ 104 * V - 1) = P * (2 ^ 104 * U) := by
    rw [Nat.mul_sub, Nat.mul_one, show R * (2 ^ 104 * V) = 2 ^ 104 * (V * R) by
      rw [Nat.mul_comm V R, Nat.mul_left_comm], h, Nat.mul_add, Nat.mul_comm (2 ^ 104) E2, hE,
      Nat.add_sub_cancel_left, Nat.mul_left_comm]
  exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left ⟨_, h3⟩

/-- A number `V ≡ c W` multiplied by `lit` over `R`, where `lit W = T R`: `c T`. -/
theorem up_cong {V' V c lit W T R P : Nat} (hR : Nat.Coprime R P) (h : V' * R % P = lit * V % P)
    (hV : V % P = c * W % P) (e : lit * W = T * R) : V' % P = c * T % P := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hV, ← Nat.mul_mod, show lit * (c * W) = c * (lit * W) from Nat.mul_left_comm _ _ _, e,
    Nat.mul_assoc]

/-- Limbs `n` and `n + 1` of a number below `2^(52 n)` are zero. -/
theorem top2_zero {f : Nat → Nat} {n : Nat} (h : lval f (n + 2) < 2 ^ (52 * n)) : f n = 0 ∧ f (n + 1) = 0 := by
  rw [show n + 2 = n + 1 + 1 from rfl, VG.Proof.Bignum.Amm52.lval_succ, VG.Proof.Bignum.Amm52.lval_succ,
    show 52 * (n + 1) = 52 * n + 52 by omega, Nat.pow_add] at h
  have hp : 0 < 2 ^ (52 * n) := Nat.two_pow_pos _
  generalize 2 ^ (52 * n) = T at h hp
  constructor
  · rcases Nat.eq_zero_or_pos (f n) with h0 | h0
    · exact h0
    · have := Nat.le_mul_of_pos_left T h0; omega
  · rcases Nat.eq_zero_or_pos (f (n + 1)) with h0 | h0
    · exact h0
    · have h1 := Nat.le_mul_of_pos_left (T * 2 ^ 52) h0
      have h2 : T ≤ T * 2 ^ 52 := Nat.le_mul_of_pos_right T (by decide)
      omega

/-- The sizes of the numbers before the exponentiations. -/
theorem ZOk.nums (hz : ZOk l) :
    l.zE < l.L ∧ 1 * 2 ^ (52 * l.zE) * (1 * 2 ^ (52 * l.zE)) * 2 ^ 104 = 2 ^ (52 * l.S) ∧
    2 ^ 104 * 2 ^ (64 * l.W) ≤ 2 ^ (52 * l.S - 16) ∧ 2 ^ (64 * l.W) ≤ 2 ^ (52 * (l.L - 2)) ∧
    1 + 2 ^ (64 * l.W) ≤ 2 ^ (52 * l.L) ∧ 1 * 2 ^ (52 * l.zE) < 2 ^ (52 * l.S) ∧
    2 ^ 51 * 2 ^ (52 * (l.L - 1)) = 2 ^ (52 * l.L - 1) ∧
    2 ^ (52 * l.L - 1) * (2 * 2 ^ (64 * l.W)) ≤ 2 ^ (52 * l.S) * 2 ^ (52 * l.L + 64 * l.W - 52 * l.S) ∧
    2 ^ (52 * l.L + 64 * l.W - 52 * l.S) + 2 ^ (52 * l.S - 16) ≤ 2 ^ (52 * l.S - 14) ∧
    2 * 2 ^ (64 * l.W) ≤ 2 ^ (52 * l.S) ∧ 2 ^ (52 * l.S - 14) ≤ 2 ^ (52 * l.L) ∧
    2 * 2 ^ (52 * l.S - 14) ≤ 2 ^ (52 * l.S) ∧ 2 * 2 ^ (52 * l.S - 15) = 2 ^ (52 * l.S - 14) := by
  rw [hz]
  exact ⟨by decide, by kernel_rfl, Nat.le_of_ble_eq_true (by kernel_rfl), Nat.le_of_ble_eq_true (by kernel_rfl),
    Nat.le_of_ble_eq_true (by kernel_rfl), Nat.le_of_ble_eq_true (by kernel_rfl), by kernel_rfl,
    Nat.le_of_ble_eq_true (by kernel_rfl), Nat.le_of_ble_eq_true (by kernel_rfl),
    Nat.le_of_ble_eq_true (by kernel_rfl), Nat.le_of_ble_eq_true (by kernel_rfl),
    Nat.le_of_ble_eq_true (by kernel_rfl), by kernel_rfl⟩

theorem gbz (hz : ZOk l) (M : Nat) : 2 * gb l M = 2 ^ (52 * l.S - 14) := by
  rw [gb, hz.z, ite_eq_left rfl]; exact hz.nums.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## The multiplications before and after the exponentiations -/

/-- `m = 2^(-104)` modulo each prime, at `oMs`: `2^(52 zE)` squared over `2^(52 S)`, by `ammCore`. -/
theorem zMh_ok (hz : ZOk l) {s : State} {B : Addr} {M k : Nat → Nat} (hB : s.gpr .rbx = B)
    (hs : Scr s B (l.nl * l.D)) (ar : Ar0 l s.mem B M k) (hodd : ∀ p < l.nl, M p % 2 = 1)
    (hMw : ∀ p < l.nl, M p < 2 ^ (64 * l.W)) :
    WP isa (.seq (.block (litN l l.oS l.zE 1)) (ammP l l.oMs l.oS l.oS)) s fun s' =>
      ArZ l s'.mem B M ∧ (∃ m₁, Out2 l B l.oS l.NB s.mem m₁ ∧ Out2 l B l.oMs l.NB m₁ s'.mem) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hl := hz.amm
  obtain ⟨hNB, eK0, eY, eX, eS, eK1, eXK, eSK, eV, eMs, eF2, eD, hD, hL, hnl⟩ := hz.slots
  obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := hz.nums
  refine WP.seq (WP.mono (litN_ok hz hB hs (by omega) n1) fun s₁ ⟨lim₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have ar₁ : Ar0 l s₁.mem B M k := ar.of_out2 hl f₁ (by omega) (by omega)
  have hlt : ∀ p < l.nl, ∀ j < l.L, limb l s₁.mem B (l.D * p + l.oS) j < 2 ^ 52 := fun p hp j hj => by
    rw [lim₁ p hp j hj]; split <;> decide
  have hval : ∀ p < l.nl, val52 l s₁.mem B (l.D * p + l.oS) = 1 * 2 ^ (52 * l.zE) := fun p hp =>
    val_single n1 (lim₁ p hp)
  refine WP.mono (ammP_ok hl ((g₁ _ (by decide)).trans hB) (hs.congr wr₁) ar₁ (by omega) (by omega) (by omega)
    fun p hp j hj => ⟨hlt p hp j hj, hlt p hp j hj⟩) fun s₂ ⟨hv, f₂, g₂, rd₂, wr₂, x₂⟩ =>
    ⟨⟨fun p hp => (hv p hp).1, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩, ⟨_, f₁, f₂⟩,
      fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 => (g₂ r r1 r2 r3 r4 r5 r6 r7 r8 r9).trans (g₁ r r1),
      rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩
  all_goals
    have hMp := hMw p hp
    obtain ⟨U, hU, he⟩ := (hv p hp).2 (by rw [hval p hp]; exact n6) (by
      rw [hval p hp]
      exact zfit' (H := 1) (by rw [Nat.mul_one, ← n2]; omega) (by omega))
    rw [hval p hp] at he
    obtain ⟨m1, m2, m3⟩ := mhat he hU n2 (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
      (Nat.mul_pos (by decide) (Nat.two_pow_pos _))) (cop2 (hodd p hp) _)
  · have hlt2 : lval (limb l s₂.mem B (l.D * p + l.oMs)) (l.L - 2 + 2) < 2 ^ (52 * (l.L - 2)) := by
      rw [show l.L - 2 + 2 = l.L by omega]
      exact Nat.lt_of_le_of_lt m2 (Nat.lt_of_lt_of_le hMp n4)
    have := top2_zero hlt2
    rwa [show l.L - 2 + 1 = l.L - 1 by omega] at this
  · exact m1
  · exact m3
  · exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_trans m2 (Nat.le_of_lt hMp))) n3

/-- A number below twice the prime times `2^(52 L - 1)` over `2^(52 S)`, in place, modulo the
multiple of the prime. -/
theorem zUp_ok (hz : ZOk l) {s : State} {B : Addr} {M : Nat → Nat} {c : Nat} (hB : s.gpr .rbx = B)
    (hs : Scr s B (l.nl * l.D)) (az : ArZ l s.mem B M) (hc : c + l.NB ≤ l.D)
    (hlit : ∀ p < l.nl, ∀ q < l.L, limb l s.mem B (l.D * p + l.oS) q = if q = l.L - 1 then 2 ^ 51 else 0)
    (g : ∀ p < l.nl, GoodS l s.mem B M c p) (hMw : ∀ p < l.nl, M p < 2 ^ (64 * l.W)) :
    WP isa (amm l c l.oS c) s fun s' =>
      (∀ p < l.nl, Good l s'.mem B M c p ∧ val52 l s'.mem B (l.D * p + c) * 2 ^ (52 * l.S) % M p =
        2 ^ (52 * l.L - 1) * val52 l s.mem B (l.D * p + c) % M p) ∧
      Out2 l B c l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hNB, eK0, eY, eX, eS, eK1, eXK, eSK, eV, eMs, eF2, eD, hD, hL, hnl⟩ := hz.slots
  obtain ⟨-, -, -, -, -, -, n7, n8, n9, n10, n11, -⟩ := hz.nums
  have hvS : ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oS) = 2 ^ (52 * l.L - 1) := fun p hp => by
    rw [val_single (by omega) (hlit p hp), n7]
  refine WP.mono (ammZ_ok hz hB hs az hc (by omega) hc fun p hp j hj =>
    ⟨by rw [hlit p hp j hj]; split <;> decide, (g p hp).lt j hj⟩) fun s' ⟨hv, rest⟩ => ⟨fun p hp => ?_, rest⟩
  have hMp := hMw p hp
  have hgv := (g p hp).v
  have hX := az.bnd p hp
  have hpos := az.pos p hp
  have hAB : 2 ^ (52 * l.L - 1) * val52 l s.mem B (l.D * p + c) <
      2 ^ (52 * l.S) * 2 ^ (52 * l.L + 64 * l.W - 52 * l.S) :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (by omega) (Nat.two_pow_pos _)) n8
  obtain ⟨Q, hQ, he⟩ := (hv p hp).2 (by omega) (by rw [hvS p hp]; exact zfit' hAB (by omega))
  rw [hvS p hp] at he
  have hb := zbound' he hQ hAB
  refine ⟨⟨(hv p hp).1, by rw [gbz hz]; omega⟩, ?_⟩
  obtain ⟨d, hd⟩ := az.dvd p hp
  rw [he, hd, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- The result of the exponentiations times the last multiplier over `2^(52 S)`, modulo the primes:
below twice the prime. -/
theorem zPost_ok (hz : ZOk l) {s : State} {B : Addr} {M k : Nat → Nat} (hB : s.gpr .rbx = B)
    (hs : Scr s B (l.nl * l.D)) (ar : Ar0 l s.mem B M k) (gy : ∀ p < l.nl, Good l s.mem B M l.oY p)
    (gf : ∀ p < l.nl, GoodS l s.mem B M l.oF2 p) :
    WP isa (zPost l) s fun s' =>
      (∀ p < l.nl, GoodS l s'.mem B M l.oY p ∧ val52 l s'.mem B (l.D * p + l.oY) * 2 ^ (52 * l.S) % M p =
        val52 l s.mem B (l.D * p + l.oY) * val52 l s.mem B (l.D * p + l.oF2) % M p) ∧
      Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hl := hz.amm
  obtain ⟨hNB, eK0, eY, eX, eS, eK1, eXK, eSK, eV, eMs, eF2, eD, hD, hL, hnl⟩ := hz.slots
  obtain ⟨-, -, -, -, -, -, -, -, -, -, n11, n12, -⟩ := hz.nums
  refine WP.mono (ammP_ok hl hB hs ar (by omega) (by omega) (by omega) fun p hp j hj =>
    ⟨(gy p hp).lt j hj, (gf p hp).lt j hj⟩) fun s' ⟨hv, rest⟩ => ⟨fun p hp => ?_, rest⟩
  have hM4 := ar.bnd p hp
  have hA := (gy p hp).v
  have hBv := (gf p hp).v
  rw [gbz hz] at hA
  have hAB : val52 l s.mem B (l.D * p + l.oY) * val52 l s.mem B (l.D * p + l.oF2) < 2 ^ (52 * l.S) * M p := by
    have h1 := Nat.mul_lt_mul'' hA hBv
    have h2 : 2 ^ (52 * l.S - 14) * (2 * M p) ≤ 2 ^ (52 * l.S) * M p := by
      rw [← Nat.mul_assoc, Nat.mul_comm _ 2]; exact Nat.mul_le_mul_right _ n12
    omega
  obtain ⟨U, hU, he⟩ := (hv p hp).2 (by omega) (zfit' hAB (by
    have : 2 ^ (52 * l.S) ≤ 2 ^ (52 * l.L) := Nat.pow_le_pow_right (by decide) (by rw [hz.S, hL]; decide)
    omega))
  have hb := zbound' he hU hAB
  exact ⟨⟨(hv p hp).1, by omega⟩, by rw [he, Nat.add_mul_mod_self_left]⟩

/-! ## Before the exponentiations -/

/-- Writes of a number outside the exponents' digits. -/
theorem Out2.dig (hz : ZOk l) {B : Addr} {o : Nat} {m m' : Mem} (h : Out2 l B o l.NB m m')
    (ho : o + l.NB ≤ l.oE ∨ l.oK1 ≤ o) (hoD : o + l.NB ≤ l.D) {p i : Nat} (hp : p < l.nl) (hi : i < l.ND) :
    dig l m' B p i = dig l m B p i := by
  have hl := hz.amm
  obtain ⟨hNB, eK0, eY, eX, eS, eK1, eXK, eSK, eV, eMs, eF2, eD, hD, hL, hnl⟩ := hz.slots
  obtain ⟨d1, d2⟩ := lay_dAt hl hi
  refine congrArg (fun b : BitVec 8 => nibOf l i b.toNat) (h _ fun p' hp' => ?_)
  rw [VG.Proof.Bignum.X86_64.AmmSym.ofs_off0 B (by rcases D_mulN hl hp with h1 | h1 <;> omega)]
  rcases D_mulN hl hp with h1 | h1 <;> rcases D_mulN hl hp' with h2 | h2 <;> omega

/-- Writes within the regions. -/
theorem Out2.toOutside (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m')
    (hoD : o + n ≤ l.D) : Outside B 0 (l.nl * l.D) m m' := fun a ha => h a fun p hp => by
  have := lane_end hl hp
  rcases ha with ha | ha <;> omega

/-- The sizes' exponents: `2^(52 L - 1) R_X = 2^cv 2^(52 S)`, and `2^dbls 2^cv = 2^(104 S - cv)`. -/
theorem ZOk.exps (hz : ZOk l) :
    2 ^ (52 * l.L - 1) * 2 ^ (64 * l.W) = 2 ^ l.cv * 2 ^ (52 * l.S) ∧
      2 ^ l.dbls * 2 ^ l.cv = 2 ^ (104 * l.S - l.cv) ∧
      2 ^ l.cv * 2 ^ (104 * l.S - l.cv) = 2 ^ (52 * l.S) * 2 ^ (52 * l.S) := by
  rw [hz]; exact ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- What the exponentiations start from, after `zPre`. -/
structure ZStart (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s s' : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) :
    Prop where
  ar : Ar l s'.mem B M k
  gx : ∀ p < l.nl, Good l s'.mem B M l.oX p
  gy : ∀ p < l.nl, Good l s'.mem B M l.oY p
  gk : ∀ p < l.nl, Good l s'.mem B M l.oK1 p
  gf : ∀ p < l.nl, Good l s'.mem B M l.oFin p
  vx : Q → ∀ p < l.nl, val52 l s'.mem B (l.D * p + l.oX) % M p = x p * 2 ^ l.cv % M p
  vy : Q → ∀ p < l.nl, val52 l s'.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ l.cv % M p
  vk : Q → ∀ p < l.nl, val52 l s'.mem B (l.D * p + l.oK1) % M p = 2 ^ (104 * l.S - l.cv) % M p
  vf : Q → ∀ p < l.nl, val52 l s'.mem B (l.D * p + l.oFin) % M p = 2 ^ (52 * l.S) % M p
  f2 : ∀ p < l.nl, GoodS l s'.mem B M l.oF2 p ∧
    val52 l s'.mem B (l.D * p + l.oF2) = val52 l s.mem B (l.D * p + l.oFin)
  dg : ∀ p < l.nl, ∀ i < l.ND, dig l s'.mem B p i = dig l s.mem B p i
  out : Outside B 0 (l.nl * l.D) s.mem s'.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr

/-- `zPre`: `m` at `oMs`; `[oK1]`, `Y` and the base times `2^(52 L - 1) 2^(-52 S)`, which leaves them
times `2^cv` and `2^(104 S - cv)`; the last multiplier at `oF2`, and 1 in Montgomery form in its place. -/
theorem zPre_ok (hz : ZOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} (hB : s.gpr .rbx = B)
    (hs : Scr s B (l.nl * l.D)) (ar : Ar0 l s.mem B M k) (hodd : ∀ p < l.nl, M p % 2 = 1)
    (hMw : ∀ p < l.nl, M p < 2 ^ (64 * l.W))
    (gx : ∀ p < l.nl, GoodS l s.mem B M l.oX p) (gy : ∀ p < l.nl, GoodS l s.mem B M l.oY p)
    (gk : ∀ p < l.nl, GoodS l s.mem B M l.oK1 p) (gf : ∀ p < l.nl, GoodS l s.mem B M l.oFin p)
    (vx : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oX) % M p = x p * 2 ^ (64 * l.W) % M p)
    (vy : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ (64 * l.W) % M p)
    (vk : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oK1) % M p = 2 ^ l.dbls * 2 ^ (64 * l.W) % M p) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (zPre l)) s fun s' => ZStart l s s' B M k x Q := by
  have hl := hz.amm
  obtain ⟨hNB, eK0, eY, eX, eS, eK1, eXK, eSK, eV, eMs, eF2, eD, hD, hL, hnl⟩ := hz.slots
  have eE := hz.oE
  obtain ⟨x1, x2, x3⟩ := hz.exps
  have hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p) := fun p hp => cop2 (hodd p hp) _
  rw [show VG.Impl.Bignum.X86_64.seqs (zPre l) = .seq (.block (litN l l.oS l.zE 1)) (.seq (ammP l l.oMs l.oS l.oS)
    (.seq (.block (litN l l.oS (l.L - 1) (BitVec.ofNat 64 (2 ^ 51)))) (.seq (amm l l.oK1 l.oS l.oK1)
    (.seq (amm l l.oY l.oS l.oY) (.seq (amm l l.oX l.oS l.oX) (.seq (.block (copyN l l.oF2 l.oFin))
    (amm l l.oFin l.oY l.oK1))))))) from rfl]
  -- `m`
  refine WP.seq (WP.mono (WP.seq_iff.1 (zMh_ok hz hB hs ar hodd hMw)) fun s₁ h₁ => WP.seq (WP.mono h₁
    fun s₂ ⟨az₂, ⟨m₁, f₁, f₂⟩, g₂, rd₂, wr₂, x₂⟩ => ?_))
  have gp₂ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
      s₂.gpr r = s.gpr r := g₂
  have hB₂ : s₂.gpr .rbx = B := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hB
  have ar₂ : Ar0 l s₂.mem B M k := (ar.of_out2 hl f₁ (by omega) (by omega)).of_out2 hl f₂ (by omega) (by omega)
  -- a slot the first two writes miss
  have k₂ : ∀ c, c + l.NB ≤ l.oS ∨ l.oS + l.NB ≤ c → c + l.NB ≤ l.oMs → ∀ p < l.nl,
      (GoodS l s.mem B M c p → GoodS l s₂.mem B M c p) ∧
      val52 l s₂.mem B (l.D * p + c) = val52 l s.mem B (l.D * p + c) := fun c h1 h2 p hp =>
    ⟨fun g => (g.of_out2 hl hp f₁ h1 (by omega) (by omega)).of_out2 hl hp f₂ (.inl h2) (by omega) (by omega),
      (f₂.val hl hp (.inl h2) (by omega) (by omega)).trans (f₁.val hl hp h1 (by omega) (by omega))⟩
  have dg₂ : ∀ p < l.nl, ∀ i < l.ND, dig l s₂.mem B p i = dig l s.mem B p i := fun p hp i hi =>
    (f₂.dig hz (.inr (by omega)) (by omega) hp hi).trans (f₁.dig hz (.inl eE) (by omega) hp hi)
  have O₂ : Outside B 0 (l.nl * l.D) s.mem s₂.mem :=
    (f₁.toOutside hl (by omega)).trans (f₂.toOutside hl (by omega))
  -- `2^(52 L - 1)`
  refine WP.seq (WP.mono (litN_ok hz hB₂ (hs.congr wr₂) (by omega) (by omega)) fun s₃ ⟨lim₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_)
  have hlit₃ : ∀ p < l.nl, ∀ q < l.L, limb l s₃.mem B (l.D * p + l.oS) q = if q = l.L - 1 then 2 ^ 51 else 0 :=
    fun p hp q hq => lim₃ p hp q hq
  have hB₃ : s₃.gpr .rbx = B := (g₃ _ (by decide)).trans hB₂
  have hs₃ : Scr s₃ B (l.nl * l.D) := hs.congr (wr₃.trans wr₂)
  have az₃ : ArZ l s₃.mem B M := az₂.of_out2 hz f₃ (.inr (by omega)) (by omega)
  have ar₃ : Ar0 l s₃.mem B M k := ar₂.of_out2 hl f₃ (by omega) (by omega)
  have k₃ : ∀ c, c + l.NB ≤ l.oS ∨ l.oS + l.NB ≤ c → c + l.NB ≤ l.oMs → ∀ p < l.nl,
      (GoodS l s.mem B M c p → GoodS l s₃.mem B M c p) ∧
      val52 l s₃.mem B (l.D * p + c) = val52 l s.mem B (l.D * p + c) := fun c h1 h2 p hp =>
    ⟨fun g => ((k₂ c h1 h2 p hp).1 g).of_out2 hl hp f₃ h1 (by omega) (by omega),
      (f₃.val hl hp h1 (by omega) (by omega)).trans (k₂ c h1 h2 p hp).2⟩
  -- `[oK1]`
  refine WP.seq (WP.mono (zUp_ok hz hB₃ hs₃ az₃ (c := l.oK1) (by omega) hlit₃
    (fun p hp => (k₃ l.oK1 (.inr (by omega)) (by omega) p hp).1 (gk p hp)) hMw)
    fun s₄ ⟨v₄, f₄, g₄, rd₄, wr₄, x₄⟩ => ?_)
  have hB₄ : s₄.gpr .rbx = B := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hB₃
  have hs₄ : Scr s₄ B (l.nl * l.D) := hs₃.congr wr₄
  have hlit₄ : ∀ p < l.nl, ∀ q < l.L, limb l s₄.mem B (l.D * p + l.oS) q = if q = l.L - 1 then 2 ^ 51 else 0 :=
    fun p hp q hq => (f₄.limb hl hp (.inl (by omega)) (by omega) (by omega) hq).trans (hlit₃ p hp q hq)
  have az₄ : ArZ l s₄.mem B M := az₃.of_out2 hz f₄ (.inr (by omega)) (by omega)
  -- `Y`
  refine WP.seq (WP.mono (zUp_ok hz hB₄ hs₄ az₄ (c := l.oY) (by omega) hlit₄
    (fun p hp => ((k₃ l.oY (.inl (by omega)) (by omega) p hp).1 (gy p hp)).of_out2 hl hp f₄ (.inl (by omega))
      (by omega) (by omega)) hMw) fun s₅ ⟨v₅, f₅, g₅, rd₅, wr₅, x₅⟩ => ?_)
  have hB₅ : s₅.gpr .rbx = B := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hB₄
  have hs₅ : Scr s₅ B (l.nl * l.D) := hs₄.congr wr₅
  have hlit₅ : ∀ p < l.nl, ∀ q < l.L, limb l s₅.mem B (l.D * p + l.oS) q = if q = l.L - 1 then 2 ^ 51 else 0 :=
    fun p hp q hq => (f₅.limb hl hp (.inr (by omega)) (by omega) (by omega) hq).trans (hlit₄ p hp q hq)
  have az₅ : ArZ l s₅.mem B M := az₄.of_out2 hz f₅ (.inr (by omega)) (by omega)
  -- the base
  refine WP.seq (WP.mono (zUp_ok hz hB₅ hs₅ az₅ (c := l.oX) (by omega) hlit₅
    (fun p hp => (((k₃ l.oX (.inl (by omega)) (by omega) p hp).1 (gx p hp)).of_out2 hl hp f₄ (.inl (by omega))
      (by omega) (by omega)).of_out2 hl hp f₅ (.inr (by omega)) (by omega) (by omega)) hMw)
    fun s₆ ⟨v₆, f₆, g₆, rd₆, wr₆, x₆⟩ => ?_)
  have hB₆ : s₆.gpr .rbx = B := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hB₅
  have hs₆ : Scr s₆ B (l.nl * l.D) := hs₅.congr wr₆
  have az₆ : ArZ l s₆.mem B M := az₅.of_out2 hz f₆ (.inr (by omega)) (by omega)
  have ar₆ : Ar0 l s₆.mem B M k :=
    ((ar₃.of_out2 hl f₄ (by omega) (by omega)).of_out2 hl f₅ (by omega) (by omega)).of_out2 hl f₆ (by omega) (by omega)
  -- the last multiplier, kept
  refine WP.seq (WP.mono (copyN_ok hl hB₆ hs₆ (o := l.oF2) (a := l.oFin) (by omega) (by omega) (.inl (by omega)))
    fun s₇ ⟨l₇, f₇, g₇, rd₇, wr₇, x₇⟩ => ?_)
  have hB₇ : s₇.gpr .rbx = B := by rw [g₇]; exact hB₆
  have hs₇ : Scr s₇ B (l.nl * l.D) := hs₆.congr wr₇
  have ar₇ : Ar l s₇.mem B M k := ⟨ar₆.of_out2 hl f₇ (by omega) (by omega),
    fun _ => az₆.of_out2 hz f₇ (.inl (by omega)) (by omega)⟩
  -- the numbers so far, where the last multiplication starts
  have GK₇ : ∀ p < l.nl, Good l s₇.mem B M l.oK1 p := fun p hp =>
    (((v₄ p hp).1.of_out2 hl hp f₅ (.inr (by omega)) (by omega) (by omega)).of_out2 hl hp f₆ (.inr (by omega))
      (by omega) (by omega)).of_out2 hl hp f₇ (.inl (by omega)) (by omega) (by omega)
  have GY₇ : ∀ p < l.nl, Good l s₇.mem B M l.oY p := fun p hp =>
    ((v₅ p hp).1.of_out2 hl hp f₆ (.inl (by omega)) (by omega) (by omega)).of_out2 hl hp f₇ (.inl (by omega))
      (by omega) (by omega)
  have GX₇ : ∀ p < l.nl, Good l s₇.mem B M l.oX p := fun p hp =>
    (v₆ p hp).1.of_out2 hl hp f₇ (.inl (by omega)) (by omega) (by omega)
  have eK₇ : ∀ p < l.nl, val52 l s₇.mem B (l.D * p + l.oK1) = val52 l s₄.mem B (l.D * p + l.oK1) := fun p hp =>
    (f₇.val hl hp (.inl (by omega)) (by omega) (by omega)).trans
      ((f₆.val hl hp (.inr (by omega)) (by omega) (by omega)).trans
        (f₅.val hl hp (.inr (by omega)) (by omega) (by omega)))
  have eY₇ : ∀ p < l.nl, val52 l s₇.mem B (l.D * p + l.oY) = val52 l s₅.mem B (l.D * p + l.oY) := fun p hp =>
    (f₇.val hl hp (.inl (by omega)) (by omega) (by omega)).trans (f₆.val hl hp (.inl (by omega)) (by omega) (by omega))
  have eX₇ : ∀ p < l.nl, val52 l s₇.mem B (l.D * p + l.oX) = val52 l s₆.mem B (l.D * p + l.oX) := fun p hp =>
    f₇.val hl hp (.inl (by omega)) (by omega) (by omega)
  -- the last multiplier, as the region left it
  have eF₆ : ∀ p < l.nl, (GoodS l s₆.mem B M l.oFin p) ∧
      val52 l s₆.mem B (l.D * p + l.oFin) = val52 l s.mem B (l.D * p + l.oFin) := fun p hp =>
    ⟨((((k₃ l.oFin (.inr (by omega)) (by omega) p hp).1 (gf p hp)).of_out2 hl hp f₄ (.inr (by omega)) (by omega)
        (by omega)).of_out2 hl hp f₅ (.inr (by omega)) (by omega) (by omega)).of_out2 hl hp f₆ (.inr (by omega))
        (by omega) (by omega),
      (f₆.val hl hp (.inr (by omega)) (by omega) (by omega)).trans
        ((f₅.val hl hp (.inr (by omega)) (by omega) (by omega)).trans
          ((f₄.val hl hp (.inr (by omega)) (by omega) (by omega)).trans
            (k₃ l.oFin (.inr (by omega)) (by omega) p hp).2))⟩
  have F2₇ : ∀ p < l.nl, GoodS l s₇.mem B M l.oF2 p ∧
      val52 l s₇.mem B (l.D * p + l.oF2) = val52 l s.mem B (l.D * p + l.oFin) := fun p hp =>
    ⟨⟨fun j hj => by rw [l₇ p hp j hj]; exact (eF₆ p hp).1.lt j hj,
      by rw [val52_of_limbs (l₇ p hp)]; exact (eF₆ p hp).1.v⟩,
      (val52_of_limbs (l₇ p hp)).trans (eF₆ p hp).2⟩
  -- 1 in Montgomery form
  refine WP.mono (amm2_ok hl hB₇ hs₇ ar₇ (o := l.oFin) (a := l.oY) (b := l.oK1) (by omega) (Nat.le_refl _)
    (by omega) (by omega) GY₇ GK₇) fun s₈ ⟨v₈, f₈, ar₈, g₈, rd₈, wr₈, x₈⟩ => ?_
  -- the congruences
  have cK : Q → ∀ p < l.nl, val52 l s₄.mem B (l.D * p + l.oK1) % M p = 2 ^ (104 * l.S - l.cv) % M p :=
    fun q p hp => by
      rw [← x2]
      refine up_cong (hR p hp) (v₄ p hp).2 ?_ x1
      rw [(k₃ l.oK1 (.inr (by omega)) (by omega) p hp).2]; exact vk q p hp
  have cY : Q → ∀ p < l.nl, val52 l s₅.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ l.cv % M p := fun q p hp => by
    refine up_cong (hR p hp) (v₅ p hp).2 ?_ x1
    rw [f₄.val hl hp (.inl (by omega)) (by omega) (by omega), (k₃ l.oY (.inl (by omega)) (by omega) p hp).2]
    exact vy q p hp
  have cX : Q → ∀ p < l.nl, val52 l s₆.mem B (l.D * p + l.oX) % M p = x p * 2 ^ l.cv % M p := fun q p hp => by
    refine up_cong (hR p hp) (v₆ p hp).2 ?_ x1
    rw [f₅.val hl hp (.inr (by omega)) (by omega) (by omega), f₄.val hl hp (.inl (by omega)) (by omega) (by omega),
      (k₃ l.oX (.inl (by omega)) (by omega) p hp).2]
    exact vx q p hp
  have k₈ : ∀ c, c + l.NB ≤ l.oFin ∨ l.oFin + l.NB ≤ c → c + l.NB ≤ l.D → ∀ p < l.nl,
      val52 l s₈.mem B (l.D * p + c) = val52 l s₇.mem B (l.D * p + c) := fun c h1 h2 p hp =>
    f₈.val hl hp h1 h2 (by omega)
  refine ⟨ar₈, fun p hp => (GX₇ p hp).of_out2 hl hp f₈ (.inl (by omega)) (by omega) (by omega),
    fun p hp => (GY₇ p hp).of_out2 hl hp f₈ (.inl (by omega)) (by omega) (by omega),
    fun p hp => (GK₇ p hp).of_out2 hl hp f₈ (.inl (by omega)) (by omega) (by omega),
    fun p hp => (v₈ p hp).1,
    fun q p hp => by rw [k₈ l.oX (.inl (by omega)) (by omega) p hp, eX₇ p hp]; exact cX q p hp,
    fun q p hp => by rw [k₈ l.oY (.inl (by omega)) (by omega) p hp, eY₇ p hp]; exact cY q p hp,
    fun q p hp => by rw [k₈ l.oK1 (.inl (by omega)) (by omega) p hp, eK₇ p hp]; exact cK q p hp,
    fun q p hp => ?_,
    fun p hp => ⟨(F2₇ p hp).1.of_out2 hl hp f₈ (.inr (by omega)) (by omega) (by omega),
      (k₈ l.oF2 (.inr (by omega)) (by omega) p hp).trans (F2₇ p hp).2⟩,
    fun p hp i hi => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 => ?_, ?_, ?_, ?_⟩
  · -- `Y [oK1] / 2^(52 S)` is `2^(52 S)`
    apply VG.Proof.Bignum.mont_cancel (hR p hp)
    rw [(v₈ p hp).2, Nat.mul_mod, eY₇ p hp, eK₇ p hp, cY q p hp, cK q p hp, ← Nat.mul_mod, Nat.one_mul, x3]
  · rw [f₈.dig hz (.inr (by omega)) (by omega) hp hi, f₇.dig hz (.inr (by omega)) (by omega) hp hi,
      f₆.dig hz (.inl (by omega)) (by omega) hp hi, f₅.dig hz (.inl (by omega)) (by omega) hp hi,
      f₄.dig hz (.inr (by omega)) (by omega) hp hi, f₃.dig hz (.inl eE) (by omega) hp hi]
    exact dg₂ p hp i hi
  · exact ((((((O₂.trans (f₃.toOutside hl (by omega))).trans (f₄.toOutside hl (by omega))).trans
      (f₅.toOutside hl (by omega))).trans (f₆.toOutside hl (by omega))).trans
      (f₇.toOutside hl (by omega))).trans (f₈.toOutside hl (by omega)))
  · rw [g₈ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₇, g₆ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₅ r r1 r2 r3 r4 r5 r6 r7 r8 r9,
      g₄ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₃ r r1, gp₂ r r1 r2 r3 r4 r5 r6 r7 r8 r9]
  · rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂]
  · rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂]
  · rw [x₈, x₇, x₆, x₅, x₄, x₃, x₂]

/-! ## The exponentiations between -/

/-- The limbs of a number the exponentiations do not write. -/
theorem OutE.limbs (hl : AmmOk l) {m m' : Mem} {B : Addr} {c p : Nat} (hp : p < l.nl) (h : OutE l B m m')
    (hY : c + l.NB ≤ l.oY ∨ l.oY + 2 * l.NB ≤ c) (hS : c + l.NB ≤ l.oS ∨ l.oS + l.NB ≤ c)
    (hV : c + l.NB ≤ l.oV ∨ l.oV + 8 ≤ c) (hT : c + l.NB ≤ l.oTab ∨ l.oTab + l.T * l.NB ≤ c)
    (hcD : c + l.NB ≤ l.D) : ∀ j < l.L, limb l m' B (l.D * p + c) j = limb l m B (l.D * p + c) j := fun j hj => by
  have := off_ltN hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, h.word_at hl hp (by omega) (by omega) (by omega) (by omega) (by omega) hl.D_bounds.2]

/-- `zPre`, the exponentiations and `zPost`: `Y ≡ x^e Fin`, below twice the prime, for each prime. -/
theorem zBody_ok (hz : ZOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {e : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (ar : Ar0 l s.mem B M k) (hodd : ∀ p < l.nl, M p % 2 = 1)
    (hMw : ∀ p < l.nl, M p < 2 ^ (64 * l.W))
    (gx : ∀ p < l.nl, GoodS l s.mem B M l.oX p) (gy : ∀ p < l.nl, GoodS l s.mem B M l.oY p)
    (gk : ∀ p < l.nl, GoodS l s.mem B M l.oK1 p) (gf : ∀ p < l.nl, GoodS l s.mem B M l.oFin p)
    (vx : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oX) % M p = x p * 2 ^ (64 * l.W) % M p)
    (vy : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ (64 * l.W) % M p)
    (vk : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oK1) % M p = 2 ^ l.dbls * 2 ^ (64 * l.W) % M p)
    (he : ∀ p < l.nl, e p < 2 ^ (8 * l.E)) (hd : ∀ p < l.nl, ∀ i < l.ND, dig l s.mem B p i = digit l (e p) i) :
    WP isa (.seq (VG.Impl.Bignum.X86_64.seqs (zPre l)) (.seq (VG.Impl.Bignum.X86_64.seqs (expLoop l)) (zPost l))) s
      fun s' =>
      (∀ p < l.nl, GoodS l s'.mem B M l.oY p ∧
        (Q → val52 l s'.mem B (l.D * p + l.oY) % M p = x p ^ e p * val52 l s.mem B (l.D * p + l.oFin) % M p)) ∧
      Outside B 0 (l.nl * l.D) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hl := hz.amm
  obtain ⟨hNB, eK0, eY, eX, eS, eK1, eXK, eSK, eV, eMs, eF2, eD, hD, hL, hnl⟩ := hz.slots
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hTK : l.oTab + l.T * l.NB ≤ l.oK1 := by omega
  have hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p) := fun p hp => cop2 (hodd p hp) _
  refine WP.seq (WP.mono (zPre_ok hz (x := x) hB hs ar hodd hMw gx gy gk gf vx vy vk) fun s₁ zs => ?_)
  have hB₁ : s₁.gpr .rbx = B := by
    rw [zs.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hB
  have hs₁ : Scr s₁ B (l.nl * l.D) := hs.congr zs.wr
  refine WP.seq (WP.mono (expLoop_ok hl ⟨hB₁, hs₁, zs.ar, hR, zs.gx, zs.gy, zs.gk, zs.vx, zs.vy, zs.vk⟩ zs.gf he
    (fun p hp i hi => by rw [zs.dg p hp i hi]; exact hd p hp i hi)) fun s₂ ⟨v₂, f₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have hB₂ : s₂.gpr .rbx = B := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hB₁
  -- the prime and the last multiplier, which the exponentiations leave
  have lM : ∀ p < l.nl, ∀ j < l.L, limb l s₂.mem B (l.D * p + oM) j = limb l s₁.mem B (l.D * p + oM) j :=
    fun p hp => f₂.limbs hl hp (.inl (by simp only [oM]; omega)) (.inl (by simp only [oM]; omega))
      (.inl (by simp only [oM]; omega)) (.inl (by simp only [oM]; omega)) (by simp only [oM]; omega)
  have lF : ∀ p < l.nl, ∀ j < l.L, limb l s₂.mem B (l.D * p + l.oF2) j = limb l s₁.mem B (l.D * p + l.oF2) j :=
    fun p hp => f₂.limbs hl hp (.inr (by omega)) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)) (by omega)
  have ar₁ := zs.ar.toAr0
  have ar₂ : Ar0 l s₂.mem B M k := by
    refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp t ht => ?_, ar₁.klt, fun p hp => ?_, ar₁.bnd⟩
    · rw [lM p hp j hj]; exact ar₁.mlt p hp j hj
    · rw [val52_of_limbs (lM p hp)]; exact ar₁.mv p hp
    · rw [Nat.add_assoc, f₂.word_at hl hp (.inl (by omega)) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
        (by omega) hl.D_bounds.2, ← Nat.add_assoc]
      exact ar₁.kw p hp t ht
    · rw [lM p hp 0 (by omega)]; exact ar₁.k0 p hp
  have gF₂ : ∀ p < l.nl, GoodS l s₂.mem B M l.oF2 p := fun p hp =>
    ⟨fun j hj => by rw [lF p hp j hj]; exact (zs.f2 p hp).1.lt j hj,
      by rw [val52_of_limbs (lF p hp)]; exact (zs.f2 p hp).1.v⟩
  refine WP.mono (zPost_ok hz hB₂ (hs₁.congr wr₂) ar₂ (fun p hp => (v₂ p hp).1) gF₂)
    fun s₃ ⟨v₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ⟨fun p hp => ⟨(v₃ p hp).1, fun q => ?_⟩, ?_,
      fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 _ r12 => ?_, by rw [rd₃, rd₂, zs.rd], by rw [wr₃, wr₂, zs.wr],
      by rw [x₃, x₂, zs.mxcsr]⟩
  · apply VG.Proof.Bignum.mont_cancel (hR p hp)
    rw [(v₃ p hp).2, val52_of_limbs (lF p hp), (zs.f2 p hp).2, Nat.mul_mod, (v₂ p hp).2 q,
      Nat.mul_mod (x p ^ e p), zs.vf q p hp, ← Nat.mul_mod (x p ^ e p), ← Nat.mul_mod, Nat.mul_right_comm]
  · exact (zs.out.trans (f₂.toOutside hl)).trans (f₃.toOutside hl (by omega))
  · rw [g₃ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₂ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12,
      zs.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9]

end VG.Proof.Bignum.X86_64.Ifma
