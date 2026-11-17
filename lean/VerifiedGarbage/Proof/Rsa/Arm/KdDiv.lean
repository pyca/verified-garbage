module

public import VerifiedGarbage.Proof.Rsa.Arm.KdNorm
public import VerifiedGarbage.Impl.Rsa.Arm.KeyDiv
public import VerifiedGarbage.Proof.Framework.Arm.Keep
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordDiv
import VerifiedGarbage.Proof.Bignum.WordTop32
public import VerifiedGarbage.Proof.Rsa.Arm.KdEst
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.MaskRow

/-! ### `Rsa.Arm.KdStep`, which this module and modules that import it used -/

section

/-! # A step's subtraction of the key checks' division on ARMv7 (`KeyDiv.step`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont VG.Impl.Bignum.Arm
  VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_str wp_ldr op2_reg op2_imm op2_lsr dpVal)
open VG.Impl.Rsa.Arm.Keys (sC ptr)

/-- `lr := w / 2 + 1` from `r9 = w`. -/
theorem dwLr_val {w : Nat} (hw : w ≤ 1024) :
    BitVec.ofNat 32 w >>> 1 + 1 = BitVec.ofNat 32 (w / 2 + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
  omega_using [hw]

theorem dw_val {w : Nat} (hw : w ≤ 1024) : BitVec.ofNat 32 w >>> 1 = BitVec.ofNat 32 (w / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [hw]

/-- The registers of a step's parts but `r7`–`r9`, which they put back. -/
abbrev divRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr]

/-- Put back `r7`–`r9` in a `Rest` over every register. -/
theorem rest_back {s t : State} {B : BitVec 32} {Z w N : Nat} {ws : List Reg} (h : Ws s B Z w N)
    (ht : Ws t B Z w N) (r : Rest ws s t) (hws : ∀ x ∈ ws, x ∈ divRegs ++ ([.r7, .r8, .r9] : List Reg) := by decide) :
    Rest divRegs s t := by
  obtain K := r.mono hws
  refine ⟨fun x hx => ?_, K.rd, K.wr, K.sp⟩
  by_cases e : x ∈ [Reg.r7, .r8, .r9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at e
    rcases e with rfl | rfl | rfl
    · rw [ht.r7, h.r7]
    · rw [ht.r8, h.r8]
    · rw [ht.r9, h.r9]
  · exact K.gpr x fun hm => (List.mem_append.mp hm).elim hx e

/-- `digit q`: word `j` of `[q]` `:= q̂ - c` (the header words `sQ` and `sC`), from `4 j` in `r1`. -/
theorem digit_ok {s : State} {B : BitVec 32} {Z w N q j : Nat} (h : Ws s B Z w N) (hq : q < N) (hN : N ≤ 256)
    (hj : j < w + 2) (h1 : s.gpr .r1 = BitVec.ofNat 32 (4 * j)) {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Ws v B Z w N → Rest [.r2, .r3, .r12] s v →
      v.mem = s.mem.writeW (off (State.addr B) (arr w q + 4 * j))
        (BitVec.ofNat 32 (slot s.mem B sQ) - BitVec.ofNat 32 (slot s.mem B sC)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (digit q ++ rest)) s Q := by
  have := h.wle
  obtain fq := h.arr_fit hq
  simp only [S] at fq
  have hz' := h.hdr_le
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  simp only [digit, List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok h (r := .r2) (by decide) (j := q) (by omega_using [hq, hN]) fun s1 p1 r1 m1 h1' => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  obtain h2 : Ws s2 B Z w N := h1'.of_upd u2 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h2 (d := sQ) (by decide) fun s3 u3 => ?_
  obtain h3 : Ws s3 B Z w N := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h3 (d := sC) (by decide) fun s4 u4 => ?_
  obtain h4 : Ws s4 B Z w N := h3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
  obtain h5 : Ws s5 B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  obtain m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  obtain a5 : State.addr (s5.gpr .r2 + BitVec.ofNat 32 0) = off (State.addr B) (arr w q + 4 * j) := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, dpVal, p1,
      r1.gpr _ (by decide), h1, BitVec.add_zero, add_ofNat_assoc]
    exact h.addr (by omega_using [hj, fq])
  obtain w5 : InRegions s5.wr (off (State.addr B) (arr w q + 4 * j)) 4 := by
    rw [u5.wr, u4.wr, u3.wr, u2.wr, r1.wr]; exact h.write (by omega_using [hj, fq])
  refine wp_str (by decide) a5 w5 fun v U => k v (h5.of_mupd U) ?_ ?_
  · exact (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (U.rest _)))))
  · rw [U.mem, u5.gpr, dpVal, u5.mem, m4, u4.gpr, u4.other .r3 (by decide), u3.gpr, u3.mem, u2.mem, m1]
    simp only [slot]
    rw [ofNat_toNat32, ofNat_toNat32]

/-- The quotient's word a step writes, for `qo = some q`. -/
def qRanges (w j : Nat) : Option Nat → List (Nat × Nat)
  | none => []
  | some q => [(arr w q + 4 * j, 4)]

/-- The quotient's array, apart from the step's. -/
def QArr (N r m t nm u : Nat) : Option Nat → Prop
  | none => True
  | some q => q < N ∧ q ≠ r ∧ q ≠ m ∧ q ≠ t ∧ q ≠ nm ∧ q ≠ u ∧ q ≠ 0

/-- The digit a step writes, `q̂ - c` from the header words. -/
def QDig (B : BitVec 32) (w j : Nat) (m m' : Mem) : Option Nat → Prop
  | none => True
  | some q => w32 m' (State.addr B) (arr w q + 4 * j) =
      (BitVec.ofNat 32 (slot m B sQ) - BitVec.ofNat 32 (slot m B sC)).toNat

/-- Words within an array outside the frame. -/
theorem keep_val {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem} (K : Keep B w js ds m m')
    {a o k : Nat} (hlo : arr w a ≤ o) (hhi : o + 4 * k ≤ arr w a + S w) (ha : ∀ x ∈ js, x ≠ a)
    (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr := by decide) (fit : arr w a + S w ≤ 2 ^ 64) :
    val32 m' (State.addr B) o k = val32 m (State.addr B) o k := by
  refine Outs.val32 K (fun x hx => ?_) (by omega_using [hhi, fit])
  simp only [ranges, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (ha y hy); simp only [S] at this hhi ⊢; omega_using [hlo, hhi, this]
  · have := hd d hd'; have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w a := Nat.le_add_right _ _; dsimp only; omega_arith

/-- The digit a step writes, `q̂` less the borrow of `Y - q̂ M`: `⌊Y / M⌋`. -/
theorem digit_math {W Y M qh U b : Nat} (hM0 : 0 < M) (hge : Y / M ≤ qh)
    (hle : qh ≤ Y / M + 1) (hU : U < W) (hb : b ≤ 1) (h1 : U + qh * M = Y + W * b) : b ≤ qh ∧ qh - b = Y / M := by
  obtain hy := Nat.div_add_mod Y M
  obtain hr := Nat.mod_lt Y hM0
  generalize Y / M = Q at hge hle hy
  generalize Y % M = R at hy hr
  rw [Nat.mul_comm M Q] at hy
  rcases (show qh = Q ∨ qh = Q + 1 by omega_using [hge, hle]) with rfl | rfl
  · rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl
    · omega_using []
    · rw [Nat.mul_one] at h1; omega_using [hU, hy, h1]
  · rw [Nat.add_mul, Nat.one_mul] at h1
    rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl
    · rw [Nat.mul_zero] at h1; omega_using [hy, hr, h1]
    · omega_using []

/-- The quotient's word a step wrote, for `qo = some q`. -/
def QOut (B : BitVec 32) (w j : Nat) (m : Mem) (d : Nat) : Option Nat → Prop
  | none => True
  | some q => w32 m (State.addr B) (arr w q + 4 * j) = d


/-! ## The fused step: `Y - q̂ M` by a row over `β^dw - M`, then `M` added back under its sign -/

/-- The top word after the multiply-subtract: `Y`'s top word, the row's carry and `- q̂`. -/
abbrev msTop (n Y L q : Nat) : Nat :=
  (2 ^ 32 - q + (Y / 2 ^ (32 * n) % 2 ^ 32 + (Y % 2 ^ (32 * n) + q * L) / 2 ^ (32 * n)) % 2 ^ 32) % 2 ^ 32

/-- The window after the multiply-subtract: the row's `n` words and the top word. -/
abbrev msV (n Y L q : Nat) : Nat := (Y % 2 ^ (32 * n) + q * L) % 2 ^ (32 * n) + 2 ^ (32 * n) * msTop n Y L q

theorem top_val32 {N a t : Nat} (hN : 0 < N) :
    a % N + N * ((t + a / N) % 2 ^ 32) = (a + N * t) % (N * 2 ^ 32) := by
  rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hN, Nat.add_comm (a / N)]

/-- The multiply-subtract is `Y - q̂ M` modulo `W = 2^(32 (n + 1))`, as `Y + W - q̂ M`. -/
theorem msV_eq {n Y M q : Nat} (hq : q < 2 ^ 32) (hM : M ≤ 2 ^ (32 * n)) (hY : Y < 2 ^ (32 * (n + 1)))
    (hP : q * M ≤ Y + 2 ^ (32 * (n + 1))) :
    msV n Y (2 ^ (32 * n) - M) q = (Y + 2 ^ (32 * (n + 1)) - q * M) % 2 ^ (32 * (n + 1)) := by
  obtain hN := Nat.two_pow_pos (32 * n)
  obtain eM : (2 : Nat) ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [Nat.mul_add, Nat.pow_add, Nat.mul_one]
  obtain hd : Y / 2 ^ (32 * n) < 2 ^ 32 := by rw [Nat.div_lt_iff_lt_mul hN, Nat.mul_comm, ← eM]; exact hY
  simp only [msV, msTop]
  rw [Nat.add_mod_mod, ← Nat.add_assoc (2 ^ 32 - q), top_val32 hN, ← eM, Nat.mod_eq_of_lt hd]
  obtain hr := Nat.div_add_mod Y (2 ^ (32 * n))
  obtain qm : q * M ≤ q * 2 ^ (32 * n) := Nat.mul_le_mul_left _ hM
  obtain e3 : q * 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 1)) := by rw [eM, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.le_of_lt hq)
  obtain key : Y % 2 ^ (32 * n) + q * (2 ^ (32 * n) - M) + 2 ^ (32 * n) * (2 ^ 32 - q + Y / 2 ^ (32 * n)) =
      Y + 2 ^ (32 * (n + 1)) - q * M := by
    rw [Nat.mul_sub, Nat.mul_add, Nat.mul_sub, Nat.mul_comm (2 ^ (32 * n)) q, ← eM]
    generalize 2 ^ (32 * n) * (Y / 2 ^ (32 * n)) = D at hr ⊢
    generalize Y % 2 ^ (32 * n) = X at hr ⊢
    generalize q * M = P at qm hP ⊢
    generalize q * 2 ^ (32 * n) = Q at qm e3 ⊢
    omega
  rw [key]

theorem msTop_lt (n Y L q : Nat) : msTop n Y L q < 2 ^ 32 := Nat.mod_lt _ (by decide)

theorem msV_div {n Y L q : Nat} : msV n Y L q / 2 ^ (32 * n) = msTop n Y L q := by
  simp only [msV]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.zero_add]

/-- `U = (Y + W - P) mod W` is `Y - P` with a borrow, for `|Y - P| < W`. -/
theorem sub_rel {W Y P U : Nat} (hU : U = (Y + W - P) % W) (hY : Y < W) (hP : P ≤ Y + W) :
    U + P = Y + W * (if Y < P then 1 else 0) ∧ U < W := by
  obtain hW : 0 < W := by omega_using [hY]
  refine ⟨?_, hU ▸ Nat.mod_lt _ hW⟩
  split
  · rw [hU, Nat.mod_eq_of_lt (by omega_arith)]; omega_using [hP]
  · rw [hU, show Y + W - P = (Y - P) + W by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [hY])]; omega_arith

/-- The sign of `U`: its top bit, for `|Y - P|` below `W / 2`. -/
theorem sub_sign {W Y P U : Nat} (hU : U + P = Y + W * (if Y < P then 1 else 0)) (hUW : U < W) (h2 : 2 ∣ W)
    (hlo : P ≤ Y → Y - P < W / 2) (hhi : Y < P → P - Y ≤ W / 2) :
    U / (W / 2) = if Y < P then 1 else 0 := by
  obtain hW : 0 < W / 2 := by have := hUW; omega_using [hUW, h2]
  split
  · rename_i h; simp only [h, ↓reduceIte, Nat.mul_one] at hU
    have := hhi h
    refine Nat.le_antisymm ?_ ((Nat.le_div_iff_mul_le hW).mpr (by omega_using [hhi, hU]))
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hW).mpr (by omega_using [hUW, h2]))
  · rename_i h; simp only [h, ↓reduceIte, Nat.mul_zero, Nat.add_zero] at hU
    exact Nat.div_eq_of_lt (by have := hlo (by omega_using [h]); omega_using [hlo, hU])

/-- A step's arithmetic: `U = Y - q̂ M` with its borrow `b`, then `M` added back for the borrow, is
`Y mod M`, for `⌊Y / M⌋ ≤ q̂ ≤ ⌊Y / M⌋ + 1`. -/
theorem step_math {W Y M qh U b : Nat} (hM0 : 0 < M) (hMW : M ≤ W) (hge : Y / M ≤ qh) (hle : qh ≤ Y / M + 1)
    (hU : U < W)
    (hb : b ≤ 1) (h1 : U + qh * M = Y + W * b) : (U + b * M) % W = Y % M := by
  obtain hy : Y / M * M + Y % M = Y := by rw [Nat.mul_comm]; exact Nat.div_add_mod Y M
  obtain hr := Nat.mod_lt Y hM0
  obtain hq : qh = Y / M ∨ qh = Y / M + 1 := by omega_using [hge, hle]
  generalize Y / M = Q at hy hq
  generalize Y % M = R at hy hr ⊢
  rcases hq with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;>
    simp only [Nat.add_mul, Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h1 ⊢
  · rw [Nat.mod_eq_of_lt hU]; omega_using [hy, h1]
  · omega_using [hU, hy, h1]
  · omega_using [hy, hr, h1]
  · rw [show U + M = R + W by omega_using [hy, h1], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [hMW, hr])]

/-- A change within a range of the frame. -/
theorem Outs.of_in {base : Addr} {o n o' n' : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : Outside base o n m m') (hr : (o', n') ∈ rs) (h1 : o' ≤ o) (h2 : o + n ≤ o' + n') : Outs base rs m m' :=
  fun x hx => h x (by have := hx _ hr; dsimp only at this; omega_using [h1, h2, this])

/-- The window (`n + 1` words) split at its top word. -/
theorem win_split {m : Mem} {A : Addr} {o n Y : Nat} (hY : val32 m A o (n + 1) = Y) :
    val32 m A o n = Y % 2 ^ (32 * n) ∧ w32 m A (o + 4 * n) = Y / 2 ^ (32 * n) := by
  rw [val32_succ] at hY
  obtain l := val32_lt m A o n
  subst hY
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l]
  · rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt l, Nat.zero_add]

/-- `mulSubW r nm`: the window `Y` at word `j` of `[r]` `:= msV`: a row of `q̂` (`sQ`) over `[nm]`'s low
`w / 2` words `L`, then the top word less `q̂` plus the row's carry; the top word's top bit into `sC`. -/
theorem mulSubW_ok {s : State} {B : BitVec 32} {Z w N r nm j : Nat} (h : Ws s B Z w N) (hr : r < N) (hnm : nm < N)
    (hrn : r ≠ nm) (hN : N ≤ 256) (h16 : slot s.mem B 16 = w) (hdw : 1 ≤ w / 2) (hJ : slot s.mem B sJ = 4 * j)
    (hj : j + w / 2 ≤ w) :
    WP isa (mulSubW r nm) s fun v => Ws v B Z w N ∧
      Outs (State.addr B) [(arr w r + 4 * j, 4 * (w / 2 + 1)), (sC, 4)] s.mem v.mem ∧
      val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) =
        msV (w / 2) (val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1))
          (val32 s.mem (State.addr B) (arr w nm) (w / 2)) (slot s.mem B sQ) ∧
      slot v.mem B sC = msTop (w / 2) (val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1))
          (val32 s.mem (State.addr B) (arr w nm) (w / 2)) (slot s.mem B sQ) / 2 ^ 31 ∧
      Rest divRegs s v := by
  have := h.wle
  have nw := h.nowrap
  obtain fr := h.arr_fit hr
  obtain fn := h.arr_fit hnm
  obtain dn := arr_disj (w := w) hrn
  have hz' := h.hdr_le
  obtain r160 : 160 ≤ arr w r := Nat.le_add_right _ _
  simp only [S] at fr fn dn
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  obtain hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega_using [nw]
  generalize eY : val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y
  generalize eL : val32 s.mem (State.addr B) (arr w nm) (w / 2) = L
  generalize eq : slot s.mem B sQ = q
  obtain ql : q < 2 ^ 32 := eq ▸ BitVec.isLt _
  obtain ⟨yLo, yHi⟩ := win_split eY
  rw [mulSubW]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  -- the window's offset
  refine ptr_ok h (r := .r0) (by decide) (j := r) (by omega_using [hr, hN]) fun s1 p1 r1 m1 h1 => ?_
  refine wp_ldrSlot h1 (d := sJ) (by decide) fun s2 U2 => WP.block_nil ?_
  obtain h2 : Ws s2 B Z w N := h1.of_upd U2 (by decide) (by decide) (by decide)
  obtain q1 : s2.gpr .r1 = BitVec.ofNat 32 (4 * j) := by rw [U2.gpr, m1, ← hJ]; exact (ofNat_toNat32 _).symm
  obtain q0 : s2.gpr .r0 = B + BitVec.ofNat 32 (arr w r) := by rw [U2.other _ (by decide), p1]
  rw [WP.seq_iff]
  simp only [List.cons_append, List.nil_append]
  -- the row's registers
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain h3 : Ws s3 B Z w N := h2.of_upd u3 (by decide) (by decide) (by decide)
  obtain p3 : s3.gpr .r0 = B + BitVec.ofNat 32 (arr w r + 4 * j) := by
    rw [u3.gpr, dpVal, q0, q1, add_ofNat_assoc]
  refine ptr_ok h3 (r := .r12) (by decide) (j := nm) (by omega_using [hnm, hN]) fun s4 p4 r4 m4 h4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  obtain h5 : Ws s5 B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h5 (d := sQ) (by decide) fun s6 u6 => ?_
  obtain h6 : Ws s6 B Z w N := h5.of_upd u6 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun u u7 => WP.block_nil ?_
  obtain hu : Ws u B Z w N := h6.of_upd u7 (by decide) (by decide) (by decide)
  obtain mu : u.mem = s.mem := u7.mem.trans (u6.mem.trans (u5.mem.trans (m4.trans (u3.mem.trans (U2.mem.trans m1)))))
  obtain restU : Rest [.r0, .r1, .r12, .lr, .r11] s u :=
    ((r1.mono (by simp)).trans ((U2.rest (by simp)).trans (u3.rest (by simp)))).trans
      ((r4.mono (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest (by simp)))))
  obtain rc : RowCtx u B Z (arr w r + 4 * j) (arr w nm) (w / 2) :=
    ⟨h.nowrap, by omega_using [hj, fr], by omega_using [fn], by omega_using [hj, dn], by rw [restU.wr]; exact h.writable⟩
  obtain x1 : (u.gpr .r1).toNat = q := by
    rw [u7.other _ (by decide), u6.gpr, u5.mem, m4, u3.mem, U2.mem, m1, ← eq]
  obtain x11 : (u.gpr .r11).toNat = 0 := by rw [u7.gpr]; rfl
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12, .lr]
    (row_ok u rc (by omega_using [hdw]) (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      r4.gpr _ (by decide), p3]) (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), p4])
      (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, h4.r9, dw_val (by omega_using [this])]))
    (by decide)) fun v ⟨inv, kv⟩ => ?_
  obtain h8 : v.gpr .r8 = B := by rw [kv.gpr _ (by decide), hu.r8]
  have vv := inv.value
  rw [x1, x11, mu, yLo, eL, Nat.add_zero] at vv
  obtain vl := val32_lt v.mem (State.addr B) (arr w r + 4 * j) (w / 2)
  obtain carry : (v.gpr .r11).toNat = (Y % 2 ^ (32 * (w / 2)) + q * L) / 2 ^ (32 * (w / 2)) := by
    rw [← vv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt vl, Nat.zero_add]
  obtain low : val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2) =
      (Y % 2 ^ (32 * (w / 2)) + q * L) % 2 ^ (32 * (w / 2)) := by
    rw [← vv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt vl]
  obtain top0 : w32 v.mem (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) = Y / 2 ^ (32 * (w / 2)) := by
    rw [inv.outside.w32 (by omega_using []) (by omega_using [hj, nw, fr]), mu, yHi]
  obtain r1v : v.gpr .r1 = BitVec.ofNat 32 q := by
    rw [inv.rest.gpr .r1 (by decide)]; apply BitVec.eq_of_toNat_eq; rw [x1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql]
  -- the top word and the sign
  obtain aT : State.addr (v.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) := by
    rw [inv.outPtr, BitVec.add_zero]; exact h.addr (by omega_using [hj, fr])
  refine wp_ldr (by decide) aT (by rw [inv.rest.rd, inv.rest.wr, restU.rd, restU.wr]; exact h.read (by omega_using [hj, fr]))
    fun v1 w1 => ?_
  refine wp_dp (op2_reg _ _) fun v2 w2 => ?_
  refine wp_dp (op2_reg _ _) fun v3 w3 => ?_
  obtain a3 : State.addr (v3.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) := by
    rw [w3.other _ (by decide), w2.other _ (by decide), w1.other _ (by decide)]; exact aT
  refine wp_str (by decide) a3 (by rw [w3.wr, w2.wr, w1.wr, inv.rest.wr, restU.wr]; exact h.write (by omega_using [hj, fr]))
    fun v4 w4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun v5 w5 => ?_
  obtain aC : State.addr (v5.gpr .r8 + BitVec.ofNat 32 sC) = off (State.addr B) sC := by
    rw [w5.other _ (by decide), w4.gpr, w3.other _ (by decide), w2.other _ (by decide), w1.other _ (by decide), h8]
    exact h.addr (by simp only [sC]; omega_using [hz'])
  obtain wC : InRegions v5.wr (off (State.addr B) sC) 4 := by
    rw [w5.wr, w4.wr, w3.wr, w2.wr, w1.wr, inv.rest.wr, restU.wr]; exact h.write (by simp only [sC]; omega_using [hz'])
  refine wp_str (by decide) aC wC fun v6 w6 => ?_
  -- the values
  obtain yt : Y / 2 ^ (32 * (w / 2)) % 2 ^ 32 = Y / 2 ^ (32 * (w / 2)) :=
    Nat.mod_eq_of_lt (by rw [← yHi]; exact BitVec.isLt _)
  obtain tv : (v3.gpr .r2).toNat = msTop (w / 2) Y L q := by
    rw [w3.gpr, dpVal, w2.gpr, dpVal, w2.other .r1 (by decide), w1.other .r1 (by decide),
      w1.other .r11 (by decide), w1.gpr, r1v, BitVec.toNat_sub, BitVec.toNat_add, carry,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql,
      show (v.mem.readW (off (State.addr B) (arr w r + 4 * j + 4 * (w / 2))) 32).toNat =
        w32 v.mem (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) from rfl, top0]
    simp only [msTop, yt]
  obtain sv : (v5.gpr .r2).toNat = msTop (w / 2) Y L q / 2 ^ 31 := by
    rw [w5.gpr, w4.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, tv]
  obtain m6 : v6.mem = (v.mem.writeW (off (State.addr B) (arr w r + 4 * j + 4 * (w / 2))) (v3.gpr .r2)).writeW
      (off (State.addr B) sC) (v5.gpr .r2) := by
    rw [w6.mem, w5.mem, w4.mem, w3.mem, w2.mem, w1.mem]
  refine kctx_ok (h.m.of (by rw [w6.wr, w5.wr, w4.wr, w3.wr, w2.wr, w1.wr, inv.rest.wr, restU.wr]))
    (by rw [w6.gpr, w5.other _ (by decide), w4.gpr, w3.other _ (by decide), w2.other _ (by decide),
      w1.other _ (by decide), h8]) (by
      simp only [slot]
      rw [m6, w32_write_ne hA (by simp only [sC]; omega_using [hz']) (by omega_using [hz']) (by simp only [sC]; omega_using []),
        w32_write_ne hA (by omega_using [hj, fr]) (by omega_using [hz']) (by omega_using [r160]), inv.outside.w32 (by omega_using [r160]) (by omega_using []), mu]
      exact h16) h.wpos this
    fun v7 h7 R7 m7 => WP.block_nil ⟨h7, ?_, ?_, ?_, ?_⟩
  · rw [m7, m6, ← mu]
    refine ((Outs.of_in (o' := arr w r + 4 * j) (n' := 4 * (w / 2 + 1)) inv.outside (by simp) (Nat.le_refl _) (by omega_using [])).trans
      (Outs.of_in (o' := arr w r + 4 * j) (n' := 4 * (w / 2 + 1)) (writeW32_outside _ _ _ (by omega_using [hj, nw, fr])) (by simp) (by omega_using []) (by omega_using []))).trans
      (Outs.of_outside (writeW32_outside _ _ _ (by simp only [sC]; omega_using [])) (by simp))
  · rw [m7, m6, val32_succ, w32_write_ne hA (by simp only [sC]; omega_using [hz']) (by omega_using [hj, fr]) (by simp only [sC]; omega_using [r160]),
      w32_write_self, tv, Outside.val32 (writeW32_outside _ _ _ (by simp only [sC]; omega_using []))
      (Or.inr (by simp only [sC]; omega_using [r160])) (by omega_using [hj, nw, fr]),
      Outside.val32 (writeW32_outside _ _ _ (by omega_using [hj, nw, fr])) (Or.inl (by omega_using [])) (by omega_using [hj, nw, fr]), low]
  · simp only [slot]; rw [m7, m6, w32_write_self, sv]
  · exact rest_back h h7 (ws := divRegs ++ [.r7, .r8, .r9]) ((((restU.mono (by decide)).trans
      (kv.mono (by decide))).trans ((w1.rest (by simp)).trans ((w2.rest (by simp)).trans ((w3.rest (by simp)).trans
      ((w4.rest _).trans ((w5.rest (by simp)).trans (w6.rest _))))))).trans (R7.mono (by decide))) (by decide)

/-- A carry into the top word: `lo' + β^n c' = X`, then the top word `t + c'`, is `X + β^n t` modulo
`β^(n+1)`. -/
theorem add_top {n lo' c' X t : Nat} (hl : lo' < 2 ^ (32 * n)) (h : lo' + 2 ^ (32 * n) * c' = X) :
    lo' + 2 ^ (32 * n) * ((t + c') % 2 ^ 32) = (X + 2 ^ (32 * n) * t) % 2 ^ (32 * (n + 1)) := by
  obtain hN := Nat.two_pow_pos (32 * n)
  obtain e1 : X % 2 ^ (32 * n) = lo' := by rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  obtain e2 : X / 2 ^ (32 * n) = c' := by
    rw [← h, Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hl, Nat.zero_add]
  rw [show 32 * (n + 1) = 32 * n + 32 by omega_using [], Nat.pow_add, ← top_val32 hN, e1, e2]

/-- `addBackW`'s part after the digit: the window `U` at word `j` of `[r]` `:= U + c M` modulo
`β^(w / 2 + 1)`, for the sign `c ≤ 1` in `sC` and `M` the low `w / 2` words of `[m]`. -/
theorem addBackT_ok {s : State} {B : BitVec 32} {Z w N r m j : Nat} (h : Ws s B Z w N) (hr : r < N) (hm : m < N)
    (hrm : r ≠ m) (hN : N ≤ 256) (hdw : 1 ≤ w / 2) (hj : j + w / 2 ≤ w)
    (h0 : s.gpr .r0 = B + BitVec.ofNat 32 (arr w r)) (h1 : s.gpr .r1 = BitVec.ofNat 32 (4 * j))
    (hc : slot s.mem B sC ≤ 1) :
    WP isa (.seq (.block (([.dp .add .r0 .r0 (.reg .r1)] : List Instr) ++ ptr .r12 m ++
        ([.mov .lr (.shifted .r9 .lsr 1), .ldr .r1 .r8 sC, .mov .r2 (.imm 0), .dp .sub .r1 .r2 (.reg .r1),
          .mov .r11 (.imm 0)] : List Instr)))
      (.seq maskRow (.block [.ldr .r2 .r0 0, .dp .add .r2 .r2 (.reg .r11), .str .r2 .r0 0]))) s fun v =>
      Ws v B Z w N ∧ Outside (State.addr B) (arr w r + 4 * j) (4 * (w / 2 + 1)) s.mem v.mem ∧
      val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) =
        (val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) +
          slot s.mem B sC * val32 s.mem (State.addr B) (arr w m) (w / 2)) % 2 ^ (32 * (w / 2 + 1)) ∧
      Rest divRegs s v := by
  have := h.wle
  have nw := h.nowrap
  obtain fr := h.arr_fit hr
  obtain fm := h.arr_fit hm
  obtain dm := arr_disj (w := w) hrm
  have hz' := h.hdr_le
  obtain r160 : 160 ≤ arr w r := Nat.le_add_right _ _
  simp only [S] at fr fm dm
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  generalize ec : slot s.mem B sC = c at hc
  rw [WP.seq_iff]
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  obtain hs1 : Ws s1 B Z w N := h.of_upd u1 (by decide) (by decide) (by decide)
  obtain p1 : s1.gpr .r0 = B + BitVec.ofNat 32 (arr w r + 4 * j) := by rw [u1.gpr, dpVal, h0, h1, add_ofNat_assoc]
  refine ptr_ok hs1 (r := .r12) (by decide) (j := m) (by omega_using [hm, hN]) fun s2 p2 r2 m2 h2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  obtain h3 : Ws s3 B Z w N := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h3 (d := sC) (by decide) fun s4 u4 => ?_
  obtain h4 : Ws s4 B Z w N := h3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  obtain h5 : Ws s5 B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  obtain h6 : Ws s6 B Z w N := h5.of_upd u6 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun u u7 => WP.block_nil ?_
  obtain hu : Ws u B Z w N := h6.of_upd u7 (by decide) (by decide) (by decide)
  obtain mu : u.mem = s.mem := u7.mem.trans (u6.mem.trans (u5.mem.trans (u4.mem.trans (u3.mem.trans (m2.trans u1.mem)))))
  obtain restU : Rest [.r0, .r12, .lr, .r1, .r2, .r11] s u :=
    ((u1.rest (by simp)).trans (r2.mono (by simp))).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest (by simp))))))
  obtain rc : RowCtx u B Z (arr w r + 4 * j) (arr w m) (w / 2) :=
    ⟨h.nowrap, by omega_using [hj, fr], by omega_using [fm], by omega_using [hj, dm], by rw [restU.wr]; exact h.writable⟩
  obtain rC : s4.gpr .r1 = BitVec.ofNat 32 c := by
    rw [u4.gpr, u3.mem, m2, u1.mem, ← ec]; exact (ofNat_toNat32 _).symm
  obtain mk : u.gpr .r1 = 0 - BitVec.ofNat 32 c := by
    rw [u7.other _ (by decide), u6.gpr, dpVal, u5.gpr, u5.other _ (by decide), rC]
  obtain mk' : u.gpr .r1 = 0 ∨ u.gpr .r1 = BitVec.allOnes 32 := by
    rw [mk]; rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl <;> decide
  obtain mc : (u.gpr .r1).toNat / (2 ^ 32 - 1) = c := by
    rw [mk]; rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl <;> decide
  rw [WP.seq_iff]
  refine WP.mono (maskRow_ok u rc (by omega_using [hdw])
    (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), r2.gpr _ (by decide), p1])
    (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), p2])
    (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.gpr, h2.r9, dw_val (by omega_using [this])]) mk') fun v ⟨vo, _, vout, _, vval, vr⟩ => ?_
  obtain hv : Ws v B Z w N := hu.rest vr
  obtain aT : State.addr (v.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) := by
    rw [vo, BitVec.add_zero]; exact h.addr (by omega_using [hj, fr])
  refine wp_ldr (by decide) aT (by rw [vr.rd, vr.wr, restU.rd, restU.wr]; exact h.read (by omega_using [hj, fr]))
    fun v1 w1 => ?_
  refine wp_dp (op2_reg _ _) fun v2 w2 => ?_
  obtain a2 : State.addr (v2.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) := by
    rw [w2.other _ (by decide), w1.other _ (by decide)]; exact aT
  refine wp_str (by decide) a2 (by rw [w2.wr, w1.wr, vr.wr, restU.wr]; exact h.write (by omega_using [hj, fr])) fun v3 w3 => ?_
  obtain hv3 : Ws v3 B Z w N :=
    ((hv.of_upd w1 (by decide) (by decide) (by decide)).of_upd w2 (by decide) (by decide) (by decide)).of_mupd w3
  refine WP.block_nil ⟨hv3, ?_, ?_, ?_⟩
  · rw [w3.mem, w2.mem, w1.mem, ← mu]
    intro x hx
    rw [writeW32_outside _ _ _ (by omega_using [hj, nw, fr]) x (by omega_using [hx]), vout x (by omega_using [hx])]
  · have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega_using [nw]
    obtain vl := val32_lt v.mem (State.addr B) (arr w r + 4 * j) (w / 2)
    obtain x11 : (u.gpr .r11).toNat = 0 := by rw [u7.gpr]; rfl
    rw [mu, mc, x11, Nat.add_zero] at vval
    rw [w3.mem, val32_succ, w32_write_self, w2.gpr, dpVal, w1.gpr, w1.other .r11 (by decide), BitVec.toNat_add,
      show (v.mem.readW (off (State.addr B) (arr w r + 4 * j + 4 * (w / 2))) 32).toNat =
        w32 v.mem (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) from rfl,
      Outside.val32 (writeW32_outside _ _ _ (by omega_using [hj, nw, fr])) (Or.inl (by omega_using [])) (by omega_using [hj, nw, fr]), w2.mem, w1.mem,
      val32_succ s.mem, vout.w32 (by omega_using []) (by omega_using [hj, nw, fr]), mu,
      add_top vl (X := val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2) +
        c * val32 s.mem (State.addr B) (arr w m) (w / 2)) vval]
    congr 1; omega_using []
  · exact rest_back h hv3 (ws := divRegs ++ [.r7, .r8, .r9]) (((restU.mono (by decide)).trans (vr.mono (by decide))).trans
      ((w1.rest (by simp)).trans ((w2.rest (by simp)).trans (w3.rest _)))) (by decide)

/-- `addBackW r m qo`: the digit for `qo = some q`, then the window `U` at word `j` of `[r]` `:= U + c M`
modulo `β^(w / 2 + 1)`, for the sign `c ≤ 1` in `sC` and `M` the low `w / 2` words of `[m]`. -/
theorem addBackW_ok {s : State} {B : BitVec 32} {Z w N r m j : Nat} (h : Ws s B Z w N) (hr : r < N) (hm : m < N)
    (hrm : r ≠ m) (hN : N ≤ 256) (hdw : 1 ≤ w / 2) (hJ : slot s.mem B sJ = 4 * j) (hj : j + w / 2 ≤ w)
    (hc : slot s.mem B sC ≤ 1) {qo : Option Nat} {t nm u : Nat} (hq : QArr N r m t nm u qo) :
    WP isa (addBackW r m qo) s fun v => Ws v B Z w N ∧
      Outs (State.addr B) ((arr w r + 4 * j, 4 * (w / 2 + 1)) :: qRanges w j qo) s.mem v.mem ∧
      val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) =
        (val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) +
          slot s.mem B sC * val32 s.mem (State.addr B) (arr w m) (w / 2)) % 2 ^ (32 * (w / 2 + 1)) ∧
      QDig B w j s.mem v.mem qo ∧ Rest divRegs s v := by
  have := h.wle
  rw [addBackW]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  refine ptr_ok h (r := .r0) (by decide) (j := r) (by omega_using [hr, hN]) fun s1 p1 r1 m1 h1 => ?_
  refine wp_ldrSlot h1 (d := sJ) (by decide) fun s2 U2 => WP.block_nil ?_
  obtain h2 : Ws s2 B Z w N := h1.of_upd U2 (by decide) (by decide) (by decide)
  obtain m2 : s2.mem = s.mem := U2.mem.trans m1
  obtain q1 : s2.gpr .r1 = BitVec.ofNat 32 (4 * j) := by rw [U2.gpr, m1, ← hJ]; exact (ofNat_toNat32 _).symm
  obtain q0 : s2.gpr .r0 = B + BitVec.ofNat 32 (arr w r) := by rw [U2.other _ (by decide), p1]
  obtain R2 : Rest divRegs s s2 := (r1.mono (by decide)).trans (U2.rest (by decide))
  rw [← m2] at hc ⊢
  rw [← m2] at hJ
  cases qo with
  | none =>
    simp only [digitOf, List.nil_append]
    exact WP.mono (addBackT_ok h2 hr hm hrm hN hdw hj q0 q1 hc) fun v ⟨W, O, V, R⟩ =>
      ⟨W, Outs.of_outside O (by simp [qRanges]), V, trivial, R2.trans R⟩
  | some q =>
    obtain ⟨hqN, hqr, hqm, -, -, -, -⟩ := hq
    have nw := h.nowrap
    obtain fq := h.arr_fit hqN
    obtain fr := h.arr_fit hr
    obtain fm := h.arr_fit hm
    obtain dqr := arr_disj (w := w) hqr
    obtain dqm := arr_disj (w := w) hqm
    obtain q160 : 160 ≤ arr w q := Nat.le_add_right _ _
    have hz' := h.hdr_le
    simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
    simp only [S] at fq fr fm dqr dqm
    simp only [digitOf, List.append_assoc]
    rw [WP.seq_iff]
    refine digit_ok h2 hqN hN (by omega_using [hj]) q1 fun x hx rx mx => ?_
    obtain ox : Outside (State.addr B) (arr w q + 4 * j) 4 s2.mem x.mem := by
      rw [mx]; exact writeW32_outside _ _ _ (by omega_using [hj, nw, fq])
    obtain tx := addBackT_ok hx hr hm hrm hN hdw hj (by rw [rx.gpr _ (by decide), q0]) (by rw [rx.gpr _ (by decide), q1])
      (by simp only [slot] at hc ⊢; rwa [ox.w32 (by simp only [sC]; omega_using [q160]) (by simp only [sC]; omega_using [])])
    rw [WP.seq_iff] at tx
    refine WP.mono tx fun y hy => WP.mono hy fun v ⟨W, O, V, R⟩ => ⟨W, ?_, ?_, ?_, ?_⟩
    · exact (Outs.of_outside ox (by simp [qRanges])).trans (Outs.of_outside O (by simp))
    · rwa [ox.val32 (by omega_using [dqr]) (by omega_using [hj, nw, fr]), ox.val32 (by omega_using [hj, dqm]) (by omega_using [nw, fm]),
        show slot x.mem B sC = slot s2.mem B sC from ox.w32 (by simp only [sC]; omega_using [q160]) (by simp only [sC]; omega_using [])] at V
    · show w32 v.mem (State.addr B) (arr w q + 4 * j) = _
      rw [O.w32 (by omega_using [dqr]) (by omega_using [hj, nw, fq]), mx, w32_write_self]
    · exact R2.trans ((rx.mono (by decide)).trans R)

/-- A header word apart from every range that changed. -/
theorem Outs.slot {B : BitVec 32} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs (State.addr B) rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) : slot m' B d = slot m B d := by
  obtain e := Outs.val32 h (d := d) (k := 1) (by simpa using hd) (by omega_using [hd'])
  simp only [val32, Nat.mul_zero, Nat.add_zero] at e
  exact e

/-- The bytes a step may change: `[t]`, `[u]`, its header words and the window. -/
abbrev stepRanges (w r t u j : Nat) (qo : Option Nat) : List (Nat × Nat) :=
  ranges w [t, u] [sMk, sQ, sU0, sU2, sC, sJ] ++ ((arr w r + 4 * j, 4 * (w / 2 + 1)) :: qRanges w j qo)

/-- `step r m t nm u`: the window `Y < 2^32 M` at word `j` of `[r]` `:= Y mod M`, for
`M = [m]` of `w / 2` words normalized by `P = 2^z` (`d`, `d₁`, `v` its top words and
reciprocal) and `[nm] = -M`; the window's offset a word down. -/
theorem step_ok {s : State} {B : BitVec 32} {Z w N r m t nm u j z : Nat} (h : Ws s B Z w N) (hr : r < N)
    (hm : m < N) (_ht : t < N) (hnm : nm < N) (_hu : u < N) (hN : N ≤ 256) (hrm : r ≠ m) (hrn : r ≠ nm)
    (h16 : slot s.mem B 16 = w) (hdw : 3 ≤ w / 2) (hJ : slot s.mem B sJ = 4 * j) (hj : j + w / 2 ≤ w)
    {Y M : Nat} (hY : val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y)
    (hM : val32 s.mem (State.addr B) (arr w m) (w / 2) = M) (hYM : Y < M * 2 ^ 32)
    (hz : z ≤ 31) (hP : slot s.mem B sP = 2 ^ z) (hMP : M * 2 ^ z < 2 ^ (32 * (w / 2)))
    (hD : slot s.mem B sD * 2 ^ 32 + slot s.mem B sD1 = M * 2 ^ z / 2 ^ (32 * (w / 2 - 2)))
    (hDn : 2 ^ 31 ≤ slot s.mem B sD) (hV : slot s.mem B sV = (2 ^ 64 - 1) / slot s.mem B sD - 2 ^ 32)
    (hnm' : val32 s.mem (State.addr B) (arr w nm) (w / 2 + 1) = 2 ^ (32 * (w / 2 + 1)) - M)
    {qo : Option Nat} (hq : QArr N r m t nm u qo) :
    WP isa (step r m t nm u qo) s fun v =>
      Ws v B Z w N ∧ val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y % M ∧
      slot v.mem B sJ = (BitVec.ofNat 32 (4 * j) - 4).toNat ∧
      Outs (State.addr B) (stepRanges w r t u j qo) s.mem v.mem ∧ QOut B w j v.mem (Y / M) qo ∧
      Rest divRegs s v := by
  have := h.wle
  have nw := h.nowrap
  obtain fr := h.arr_fit hr
  obtain gr := h.fit64 hr
  obtain gm := h.fit64 hm
  obtain gn := h.fit64 hnm
  have hz' := h.hdr_le
  obtain r160 : 160 ≤ arr w r := Nat.le_add_right _ _
  simp only [S] at fr
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  obtain hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega_using [nw]
  obtain hM0 : 0 < M := Nat.pos_of_ne_zero fun e => by
    rw [e, Nat.zero_mul, Nat.zero_div] at hD
    have := Nat.mul_le_mul_right (2 ^ 32) hDn; omega_arith
  obtain hMn : M ≤ 2 ^ (32 * (w / 2)) := by
    have : M ≤ M * 2 ^ z := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega_using [hMP, this]
  obtain eW : (2 : Nat) ^ (32 * (w / 2 + 1)) = 2 ^ (32 * (w / 2)) * 2 ^ 32 := by
    rw [Nat.mul_add, Nat.pow_add, Nat.mul_one]
  obtain hMW : M ≤ 2 ^ (32 * (w / 2 + 1)) := by rw [eW]; exact Nat.le_trans hMn (Nat.le_mul_of_pos_right _ (by decide))
  -- `[nm]`'s low words: `β^dw - M`.
  obtain hL : val32 s.mem (State.addr B) (arr w nm) (w / 2) = 2 ^ (32 * (w / 2)) - M := by
    obtain ⟨lo, -⟩ := win_split hnm'
    rw [lo, eW, show 2 ^ (32 * (w / 2)) * 2 ^ 32 - M = (2 ^ (32 * (w / 2)) - M) + 2 ^ (32 * (w / 2)) * (2 ^ 32 - 1) by
      have : 2 ^ (32 * (w / 2)) * 2 ^ 32 = 2 ^ (32 * (w / 2)) * (2 ^ 32 - 1) + 2 ^ (32 * (w / 2)) := by
        rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by decide))]
      omega_using [hMn], Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega_using [hYM, hMP])]
  rw [step]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [wp_seq_blocks, show estA r ++ estB = estimate r by simp [estA, estB, estimate], WP.seq_iff,
    ← List.append_nil (estimate r)]
  refine estimate_ok h hr hN h16 hdw hJ hj hY hYM hz hP hMP hD hDn hV
    fun t1 q hq1 hge hle ql K1 W1 R1 => WP.block_nil ?_
  obtain J1 : slot t1.mem B sJ = 4 * j := by rw [K1.slot (by decide) (by decide)]; exact hJ
  obtain s16 : slot t1.mem B 16 = w := by rw [K1.slot (by decide) (by decide)]; exact h16
  obtain Y1 : val32 t1.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y := by
    rw [keep_val K1 (a := r) (by omega_using []) (by simp only [S]; omega_using [hj]) (by simp) (fit := gr)]; exact hY
  obtain L1 : val32 t1.mem (State.addr B) (arr w nm) (w / 2) = 2 ^ (32 * (w / 2)) - M := by
    rw [keep_val K1 (a := nm) (Nat.le_refl _) (by simp only [S]; omega_using []) (by simp) (fit := gn)]; exact hL
  obtain M1 : val32 t1.mem (State.addr B) (arr w m) (w / 2) = M := by
    rw [keep_val K1 (a := m) (Nat.le_refl _) (by simp only [S]; omega_using []) (by simp) (fit := gm)]; exact hM
  -- `U = Y - q̂ M` modulo `W`, its sign into `sC`.
  rw [WP.seq_iff]
  refine WP.mono (mulSubW_ok W1 hr hnm hrn hN s16 (by omega_using [hdw]) J1 hj) fun t2 ⟨W2, O2, V2, C2, R2⟩ => ?_
  rw [Y1, L1, hq1] at V2 C2
  obtain hYW : Y < 2 ^ (32 * (w / 2 + 1)) := by
    rw [eW]; exact Nat.lt_of_lt_of_le hYM (Nat.mul_le_mul_right _ hMn)
  obtain hY' : Y / M * M + Y % M = Y := by rw [Nat.mul_comm]; exact Nat.div_add_mod Y M
  obtain hYr := Nat.mod_lt Y hM0
  obtain hqM : q * M ≤ Y + M := by
    have := Nat.mul_le_mul_right M hle; rw [Nat.add_mul, Nat.one_mul] at this; omega_using [hYM, hMP, hD, hM0, hMn, hMW, hge, hle, ql, hYW, hY', hYr, this]
  obtain U2 := msV_eq ql hMn hYW (by omega_using [hYM, hMP, hD, hM0, hMn, eW, hMW, hge, hle, ql, hYW, hY', hYr, hqM])
  obtain ⟨rel, hUW⟩ := sub_rel U2 hYW (by omega_using [hYM, hMP, hD, hM0, hMn, eW, hMW, hge, hle, ql, hYW, hY', hYr, hqM])
  obtain sgn := sub_sign rel hUW (by rw [eW]; exact Nat.dvd_trans (by decide : 2 ∣ 2 ^ 32) (Nat.dvd_mul_left _ _))
    (fun _ => by
      have : q * M ≥ Y / M * M := Nat.mul_le_mul_right M hge
      have : 2 ^ (32 * (w / 2)) ≤ 2 ^ (32 * (w / 2 + 1)) / 2 := by rw [eW]; omega_using []
      omega_arith)
    (fun _ => by
      have : 2 ^ (32 * (w / 2)) ≤ 2 ^ (32 * (w / 2 + 1)) / 2 := by rw [eW]; omega_using []
      omega_arith)
  obtain hb1 : (if Y < q * M then 1 else 0) ≤ 1 := by split <;> omega_using []
  generalize (if Y < q * M then 1 else 0) = b at rel sgn hb1
  obtain C2' : slot t2.mem B sC = b := by
    rw [C2, ← sgn, ← msV_div, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 32 * (w / 2) + 31 = 32 * (w / 2 + 1) - 1 by omega_using [],
      show 2 ^ (32 * (w / 2 + 1)) / 2 = 2 ^ (32 * (w / 2 + 1) - 1) by
        rw [show 32 * (w / 2 + 1) = (32 * (w / 2 + 1) - 1) + 1 by omega_using [], Nat.pow_succ, Nat.mul_div_cancel _ (by decide)];
        rfl]
  obtain hb : slot t2.mem B sC ≤ 1 := by rw [C2']; exact hb1
  obtain O2s : ∀ d, d + 4 ≤ 160 → d + 4 ≤ sC ∨ sC + 4 ≤ d → slot t2.mem B d = slot t1.mem B d := fun d hd hdC =>
    Outs.slot O2 (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inl (Nat.le_trans hd (Nat.le_trans r160 (Nat.le_add_right _ _)))
      · exact hdC) (by omega_using [hd])
  obtain J2 : slot t2.mem B sJ = 4 * j := by rw [O2s _ (by decide) (by decide)]; exact J1
  obtain M2 : val32 t2.mem (State.addr B) (arr w m) (w / 2) = M := by
    rw [Outs.val32 O2 (fun x hx => by
      obtain dm := arr_disj (w := w) hrm
      simp only [S] at dm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · dsimp only; omega_using [hj, dm]
      · have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w m := Nat.le_add_right _ _
        simp only [VG.Impl.Rsa.Arm.Keys.hdr] at this; exact Or.inr (Nat.le_trans (by decide) this))
      (by have := gm; simp only [S] at this; omega_using [this])]
    exact M1
  -- `M` added back under the sign, the digit.
  rw [WP.seq_iff]
  refine WP.mono (addBackW_ok W2 hr hm hrm hN (by omega_using [hdw]) J2 hj hb hq) fun t3 ⟨W3, O3, V3, D3, R3⟩ => ?_
  rw [V2, M2] at V3
  obtain V := step_math hM0 hMW hge hle hUW hb1 rel
  obtain J3 : slot t3.mem B sJ = 4 * j := by
    rw [Outs.slot O3 (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (by simp only [sJ]; omega_using [r160])
      · cases qo with
        | none => simp [qRanges] at hx
        | some qa =>
          simp only [qRanges, List.mem_singleton] at hx; subst hx
          have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w qa := Nat.le_add_right _ _
          simp only [VG.Impl.Rsa.Arm.Keys.hdr] at this
          exact Or.inl (by simp only [sJ]; omega_using [this])) (by simp only [sJ]; omega_using [])]
    exact J2
  obtain aJ : State.addr (B + BitVec.ofNat 32 sJ) = off (State.addr B) sJ := h.addr (by simp only [sJ]; omega_using [hz'])
  obtain rJ : InRegions (t3.rd ++ t3.wr) (off (State.addr B) sJ) 4 := W3.read (by simp only [sJ]; omega_using [hz'])
  obtain wJ : InRegions t3.wr (off (State.addr B) sJ) 4 := W3.write (by simp only [sJ]; omega_using [hz'])
  obtain vJ : t3.mem.readW (off (State.addr B) sJ) 32 = BitVec.ofNat 32 (4 * j) := by
    rw [← J3]; exact (ofNat_toNat32 _).symm
  refine WP.mono (WP.keep [.r0] (Q := fun v =>
      v.mem = t3.mem.writeW (off (State.addr B) sJ) (BitVec.ofNat 32 (4 * j) - 4)) (by
    krun [W3.r8, aJ, rJ, wJ, vJ]) (by decide)) fun t4 ⟨m4, R4⟩ => ?_
  obtain win4 : val32 t4.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) =
      val32 t3.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) := by
    rw [m4]; exact Outside.val32 (writeW32_outside _ _ _ (by simp only [sJ]; omega_using [])) (Or.inr (by simp only [sJ]; omega_using [r160]))
      (by omega_using [hj, nw, fr])
  refine ⟨W3.of (by rw [R4.gpr _ (by decide)]) (by rw [R4.gpr _ (by decide)]) (by rw [R4.gpr _ (by decide)]) R4.wr,
    by rw [win4, V3, C2', V], by simp only [slot]; rw [m4, w32_write_self], ?_, ?_, ?_⟩
  · have F1 : Outs (State.addr B) (stepRanges w r t u j qo) s.mem t1.mem :=
      Outs.mono (K1.mono (js' := [t, u]) (ds' := [sMk, sQ, sU0, sU2, sC, sJ])) fun x hx => List.mem_append_left _ hx
    obtain F2 : Outs (State.addr B) (stepRanges w r t u j qo) t1.mem t2.mem := Outs.mono O2 fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _ (List.mem_append_right _ (by simp))
    obtain F3 : Outs (State.addr B) (stepRanges w r t u j qo) t2.mem t3.mem :=
      Outs.mono O3 fun x hx => List.mem_append_right _ hx
    obtain F4 : Outs (State.addr B) (stepRanges w r t u j qo) t3.mem t4.mem := by
      rw [m4]
      exact Outs.mono ((keep_write (B := B) (w := w) (js := [t, u]) (ds := [sMk, sQ, sU0, sU2, sC, sJ]) t3.mem _
        (by simp) (by simp only [sJ]; omega_using []))) fun x hx => List.mem_append_left _ hx
    exact ((F1.trans F2).trans F3).trans F4
  · cases qo with
    | none => trivial
    | some qa =>
      obtain ⟨hqN, -⟩ := hq
      obtain fq := h.arr_fit hqN
      obtain q160 : 160 ≤ arr w qa := Nat.le_add_right _ _
      simp only [S] at fq
      simp only [QDig] at D3
      simp only [QOut]
      obtain sQ2 : slot t2.mem B sQ = q := by rw [O2s _ (by decide) (by decide)]; exact hq1
      obtain ⟨bq, dq⟩ := digit_math hM0 hge hle hUW hb1 rel
      rw [m4, w32_write_ne hA (by simp only [sJ]; omega_using [hz']) (by omega_using [hj, fq]) (by simp only [sJ]; omega_using [q160]), D3, sQ2, C2',
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hb1]) (by omega_using [bq]), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [ql]), dq]
  · exact (R1.mono (by decide)).trans ((R2.mono (by decide)).trans ((R3.mono (by decide)).trans (R4.mono (by decide))))

end VG.Proof.Rsa.Arm.KeyDiv

end

end

/-! # The key checks' division on ARMv7 (`KeyDiv.divW`): Algorithm D in place -/

@[expose] public section

/-! ## The reciprocal of the key checks' division on ARMv7 (`KeyDiv.recip`) -/

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv
open VG.Proof.X25519.Arm (Rest)

theorem or_bits (c g : Bool) :
    ((0 : BitVec 32) + 0 + bif c then 1 else 0) ||| ((0 : BitVec 32) + 0 + bif g then 1 else 0) =
      bif c || g then 1 else 0 := by
  cases c <;> cases g <;> decide

theorem neg_bit_and (b : Bool) (x : BitVec 32) :
    (0 - bif b then (1 : BitVec 32) else 0) &&& x = bif b then x else 0 := by
  cases b
  · simp
  · show (0 - 1 : BitVec 32) &&& x = x
    rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide]; exact BitVec.allOnes_and

theorem divBit_ok {s : State} {r d q n : Nat} (h1 : s.gpr .r1 = BitVec.ofNat 32 d)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 r) (h3 : s.gpr .r3 = BitVec.ofNat 32 q)
    (hl : s.gpr .lr = BitVec.ofNat 32 (n + 1)) (hr : r < d) (hd : d < 2 ^ 32) (hn : n + 1 < 2 ^ 32) :
    WP isa (.block divBit) s fun t =>
      t.gpr .r2 = BitVec.ofNat 32 (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) ∧
      t.gpr .r3 = BitVec.ofNat 32 (2 * q + if d ≤ 2 * r + 1 then 1 else 0) ∧
      t.gpr .lr = BitVec.ofNat 32 n ∧ t.z = (n == 0) ∧ t.gpr .r1 = s.gpr .r1 ∧ t.mem = s.mem := by
  krun [divBit, h1, h2, h3, hl]
  obtain er : (BitVec.ofNat 32 r).toNat = r := by rw [BitVec.toNat_ofNat]; omega_using [hr, hd]
  obtain ed : (BitVec.ofNat 32 d).toNat = d := by rw [BitVec.toNat_ofNat]; omega_using [hd]
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  obtain eR : (BitVec.ofNat 32 r + BitVec.ofNat 32 r + 1).toNat = (2 * r + 1) % 2 ^ 32 := by
    simp only [BitVec.toNat_add, er, e1]; omega_using []
  obtain hb : (decide (2 ^ 32 ≤ (BitVec.ofNat 32 r).toNat + (BitVec.ofNat 32 r).toNat) ||
      decide ((BitVec.ofNat 32 d).toNat ≤ (BitVec.ofNat 32 r + BitVec.ofNat 32 r + 1).toNat)) =
      decide (d ≤ 2 * r + 1) := by
    rw [er, ed, eR]
    by_cases h : d ≤ 2 * r + 1
    · simp only [h, decide_true, Bool.or_eq_true, decide_eq_true_eq]; omega_using [h]
    · simp only [h, decide_false, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega_using [hd, h]
  simp only [or_bits, hb, neg_bit_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    by_cases h : d ≤ 2 * r + 1
    · simp only [h, decide_true, Bool.cond_true, ite_true, BitVec.toNat_sub, eR, ed, BitVec.toNat_ofNat]; omega_using [hd, h]
    · simp only [h, decide_false, Bool.cond_false, ite_false, BitVec.toNat_sub, eR, BitVec.toNat_ofNat,
        show (0 : BitVec 32).toNat = 0 from rfl]; omega_using []
  · apply BitVec.eq_of_toNat_eq
    by_cases h : d ≤ 2 * r + 1
    · simp only [h, decide_true, Bool.cond_true, ite_true, BitVec.toNat_add, BitVec.toNat_ofNat, e1]; omega_using []
    · simp only [h, decide_false, Bool.cond_false, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (0 : BitVec 32).toNat = 0 from rfl]; omega_using []
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · have : BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [this]
    by_cases h : n = 0
    · subst h; rfl
    · have : (BitVec.ofNat 32 n == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro e
        have := congrArg BitVec.toNat e; simp at this; omega_arith
      rw [this]; simp [h]

def rdiv (d j : Nat) : Nat := (2 ^ 32 - 1 - d) * 2 ^ j + (2 ^ j - 1)

theorem rdiv_succ (d j : Nat) : rdiv d (j + 1) = 2 * rdiv d j + 1 := by
  unfold rdiv
  generalize 2 ^ 32 - 1 - d = K
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc, Nat.mul_comm K 2, Nat.mul_assoc]
  have := Nat.one_le_two_pow (n := j)
  omega_using [this]

/-- The loop of `recip`: from `r = 2^32 - 1 - d`, `q = 0` and the count 32,
`q = ⌊rdiv d 32 / d⌋`. -/
theorem recipLoop_ok {s : State} {d : Nat} (hd' : d < 2 ^ 32) (hd0 : 2 ^ 31 ≤ d)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 (2 ^ 32 - 1 - d)) (h1 : s.gpr .r1 = BitVec.ofNat 32 d)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 0) (hl : s.gpr .lr = BitVec.ofNat 32 32) :
    WP isa (.loop (.block divBit) .ne) s fun t => t.gpr .r3 = BitVec.ofNat 32 (rdiv d 32 / d) ∧
      t.mem = s.mem ∧ Rest [.r2, .r3, .r4, .r5, .lr] s t := by
  refine WP.loop (M := isa) (fun n t => ∃ j q r, n = 32 - j ∧ j < 32 ∧ t.gpr .r2 = BitVec.ofNat 32 r ∧
      t.gpr .r3 = BitVec.ofNat 32 q ∧ t.gpr .r1 = BitVec.ofNat 32 d ∧ t.gpr .lr = BitVec.ofNat 32 (32 - j) ∧
      r < d ∧ rdiv d j = q * d + r ∧ t.mem = s.mem ∧ Rest [.r2, .r3, .r4, .r5, .lr] s t) ?_ _ s
    ⟨0, 0, 2 ^ 32 - 1 - d, rfl, by decide, h2, h3, h1, hl, by omega_using [hd0], by simp [rdiv], rfl,
      VG.Proof.X25519.Arm.Rest.refl _ _⟩
  rintro n t ⟨j, q, r, rfl, hj, h2', h3', h1', hl', hr, hP, hm, k⟩
  refine WP.mono (WP.keep [.r2, .r3, .r4, .r5, .lr]
    (divBit_ok (n := 31 - j) h1' h2' h3' (by rw [hl']; congr 1; omega_using [hj]) hr hd' (by omega_using [])) (by decide))
    fun t' ⟨⟨e2, e3, el, ez, e1, hm'⟩, k'⟩ => ?_
  obtain ⟨hP', hr'⟩ := VG.Proof.Bignum.WordStep32.divBit_inv hP hr (show 1 < 2 by decide)
  rw [← rdiv_succ] at hP'
  obtain K := k.trans k'
  by_cases e : j + 1 = 32
  · refine .inl ⟨by simp only [eval, ez, show 31 - j = 0 by omega_using [e]]; rfl, ?_, hm'.trans hm, K⟩
    obtain e32 : rdiv d 32 = (2 * q + if d ≤ 2 * r + 1 then 1 else 0) * d +
        (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) := by rw [show (32 : Nat) = j + 1 by omega_using [e]]; exact hP'
    obtain key : ∀ Q R, R < d → (Q * d + R) / d = Q := fun Q R h' => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega_using [hd0]), Nat.div_eq_of_lt h', Nat.zero_add]
    rw [e3, e32, key _ _ hr']
  · refine .inr ⟨by simp only [eval, ez]; simp; omega_using [hj, e], 32 - (j + 1), by omega_using [hj],
      j + 1, _, _, rfl, by omega_using [hj, e], e2, e3, by rw [e1]; exact h1', by rw [el]; congr 1; omega_using [], hr', hP',
      hm'.trans hm, K⟩

open VG.Proof.Rsa.Arm.Keys VG.Proof.Mont in
/-- `recip`: `v = ⌊(2^64 - 1) / d⌋ - 2^32` at 144, for `d ≥ 2^31` at 140. -/
theorem recip_ok {s : State} {B : BitVec 32} {Z w N d : Nat} (h : Ws s B Z w N)
    (hD : slot s.mem B sD = d) (hd1 : 2 ^ 31 ≤ d) (hd2 : d < 2 ^ 32) :
    WP isa recip s fun t => slot t.mem B sV = (2 ^ 64 - 1) / d - 2 ^ 32 ∧ Keep B w [] [sV] s.mem t.mem ∧
      Rest [.r1, .r2, .r3, .r4, .r5, .lr] s t := by
  have hz := h.hdr_le
  obtain aD := h.addr (d := sD) (by simp only [sD, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  obtain rD := h.read (d := sD) (by simp only [sD, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  obtain aV := h.addr (d := sV) (by simp only [sV, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  obtain wV := h.write (d := sV) (by simp only [sV, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  obtain vD : s.mem.readW (off (State.addr B) sD) 32 = BitVec.ofNat 32 d := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd2]; exact hD
  obtain mvn : ~~~(BitVec.ofNat 32 d) = BitVec.ofNat 32 (2 ^ 32 - 1 - d) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hd2]
  rw [recip]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r1, .r2, .r3, .lr] (Q := fun u => u.gpr .r1 = BitVec.ofNat 32 d ∧
      u.gpr .r2 = BitVec.ofNat 32 (2 ^ 32 - 1 - d) ∧ u.gpr .r3 = BitVec.ofNat 32 0 ∧
      u.gpr .lr = BitVec.ofNat 32 32 ∧ u.mem = s.mem) (by
    krun [h.r8, aD, rD, vD, mvn]
    exact ⟨rfl, rfl⟩) (by decide)) fun u ⟨⟨u1, u2, u3, ul, um⟩, ku⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (recipLoop_ok hd2 hd1 u2 u1 u3 ul) fun t ⟨t3, tm, kt⟩ => ?_
  obtain r8t : t.gpr .r8 = B := by rw [kt.gpr _ (by decide), ku.gpr _ (by decide), h.r8]
  obtain wt : InRegions t.wr (off (State.addr B) sV) 4 := by rw [kt.wr, ku.wr]; exact wV
  obtain hq : rdiv d 32 / d = (2 ^ 64 - 1) / d - 2 ^ 32 := by
    rw [← VG.Proof.Bignum.WordStep32.recip_eq hd2 (by omega_using [hd1])]; rfl
  obtain hv32 : (2 ^ 64 - 1) / d - 2 ^ 32 < 2 ^ 32 := by
    have : (2 ^ 64 - 1) / d < 2 ^ 33 := by rw [Nat.div_lt_iff_lt_mul (by omega_using [hd1])]; omega_using [hd1]
    omega_using [this]
  refine WP.mono (WP.keep [] (Q := fun v => v.mem = t.mem.writeW (off (State.addr B) sV) (t.gpr .r3)) (by
    krun [r8t, aV, wt]) (by decide)) fun v ⟨vm, kv⟩ => ⟨?_, ?_, ?_⟩
  · rw [vm, slot_write_self, t3, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv32]
  · rw [vm, tm, um]; exact keep_write _ _ (by simp) (by simp only [sV]; omega_using [])
  · exact ((ku.mono (ws' := [.r1, .r2, .r3, .r4, .r5, .lr]) (by decide)).trans
      (kt.mono (by decide))).trans (kv.mono (by decide))

end VG.Proof.Rsa.Arm.KeyDiv

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp wp_dp wp_mov wp_str op2_imm op2_lsl op2_lsr op2_reg dpVal)
open VG.Impl.Rsa.Arm.Keys (copy ptr sub3)

/-! ## The arithmetic of the fold -/

/-- The window at word `j` before its step: the remainder of the words above it
shifted up a word, plus word `j` of `X`. -/
abbrev winY (X M j : Nat) : Nat := X / 2 ^ (32 * (j + 1)) % M * 2 ^ 32 + X / 2 ^ (32 * j) % 2 ^ 32

theorem winY_lt {X M j : Nat} (hM : 0 < M) : winY X M j < M * 2 ^ 32 := by
  obtain h1 := Nat.mod_lt (X / 2 ^ (32 * (j + 1))) hM
  obtain h2 := Nat.mod_lt (X / 2 ^ (32 * j)) (Nat.two_pow_pos 32)
  have := Nat.mul_le_mul_right (2 ^ 32) (show X / 2 ^ (32 * (j + 1)) % M + 1 ≤ M by omega_using [h1])
  rw [Nat.add_mul, Nat.one_mul] at this
  simp only [winY]; omega_using [h1]

/-- A step: the window's remainder is that of the words from `j` (`WordStep.wordDiv_step`). -/
theorem winY_mod (X M j : Nat) : winY X M j % M = X / 2 ^ (32 * j) % M :=
  VG.Proof.Bignum.WordStep.wordDiv_step X M 32 j

/-- The value of `[r]` a word down: the words below `j` and the remainder of those from `j`. -/
theorem fold_next (X M j : Nat) :
    X % 2 ^ (32 * (j + 1)) + 2 ^ (32 * (j + 1)) * (X / 2 ^ (32 * (j + 1)) % M) =
      X % 2 ^ (32 * j) + 2 ^ (32 * j) * winY X M j := by
  obtain e1 : X % 2 ^ (32 * (j + 1)) = X % 2 ^ (32 * j) + 2 ^ (32 * j) * (X / 2 ^ (32 * j) % 2 ^ 32) := by
    rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul]
  obtain e2 : (2 : Nat) ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
  simp only [winY]
  generalize X / 2 ^ (32 * (j + 1)) % M = A
  rw [e1, e2, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm (2 ^ 32) A]
  omega_using []

/-- The start: below `M`, the words above `j` are their own remainder. -/
theorem fold_top {X M j : Nat} (h : X / 2 ^ (32 * (j + 1)) < M) :
    X % 2 ^ (32 * j) + 2 ^ (32 * j) * winY X M j = X := by
  simp only [winY]
  rw [Nat.mod_eq_of_lt h, ← VG.Proof.Bignum.WordStep.wordDiv_digits X 32 j, Nat.mod_add_div]

/-- Three parts of a number, from its value: the low `L < 2^K`, the middle `Y` of `J` bits and
the high `H = 0` when the whole is `L' + 2^K Y'` for `L' < 2^K` and `Y' < 2^J`. -/
theorem parts_unique {K J L Y H L' Y' : Nat} (hL : L < 2 ^ K) (hL' : L' < 2 ^ K)
    (hY' : Y' < 2 ^ J) (h : L + 2 ^ K * (Y + 2 ^ J * H) = L' + 2 ^ K * Y') : L = L' ∧ Y = Y' ∧ H = 0 := by
  obtain hK := Nat.two_pow_pos K
  obtain m1 := congrArg (· % 2 ^ K) h
  obtain d1 := congrArg (· / 2 ^ K) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hL'] at m1
  simp only [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hL, Nat.div_eq_of_lt hL', Nat.zero_add] at d1
  rcases Nat.eq_zero_or_pos H with h0 | h0
  · subst h0; exact ⟨m1, by omega_using [d1], rfl⟩
  · have := Nat.mul_le_mul_left (2 ^ J) h0; omega_using [hY', d1, this]

/-! ## Frames -/

/-- A frame widened to ranges that contain its own. -/
theorem Outs.widen {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' := by
  intro x hx
  refine h x fun r hr' => ?_
  obtain ⟨r', hr'', h1, h2⟩ := hr r hr'
  have := hx r' hr''
  omega_using [h1, h2, this]

/-- Words apart from a step's frame. -/
theorem step_val {B : BitVec 32} {w r t u j : Nat} {qo : Option Nat} {m m' : Mem}
    (F : Outs (State.addr B) (stepRanges w r t u j qo) m m') {o k : Nat}
    (ht : o + 4 * k ≤ arr w t ∨ arr w t + S w ≤ o) (hu : o + 4 * k ≤ arr w u ∨ arr w u + S w ≤ o)
    (hs : VG.Impl.Rsa.Arm.Keys.hdr ≤ o)
    (hwin : o + 4 * k ≤ arr w r + 4 * j ∨ arr w r + 4 * j + 4 * (w / 2 + 1) ≤ o) (fit : o + 4 * k ≤ 2 ^ 64)
    (hq : ∀ x ∈ qRanges w j qo, o + 4 * k ≤ x.1 ∨ x.1 + x.2 ≤ o) :
    val32 m' (State.addr B) o k = val32 m (State.addr B) o k := by
  refine Outs.val32 F (fun x hx => ?_) fit
  simp only [stepRanges, ranges, List.mem_append, List.mem_map, List.mem_cons] at hx
  rcases hx with (⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩) | rfl | hx
  · simp only [List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ht
    · exact hu
  · refine .inr ?_
    dsimp only
    simp only [List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sMk, sQ, sU0, sU2, sJ, VG.Impl.Rsa.Arm.Keys.sC, VG.Impl.Rsa.Arm.Keys.hdr] at hs ⊢ <;> omega_using [hs]
  · exact hwin
  · exact hq x hx

/-- The quotient's words lie past the header. -/
theorem qRanges_hdr {w j : Nat} {qo : Option Nat} : ∀ x ∈ qRanges w j qo, VG.Impl.Rsa.Arm.Keys.hdr ≤ x.1 := by
  cases qo with
  | none => simp [qRanges]
  | some q =>
    simp only [qRanges, List.mem_singleton]; rintro _ rfl
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- A header word apart from a step's frame. -/
theorem step_slot {B : BitVec 32} {w r t u j : Nat} {qo : Option Nat} {m m' : Mem}
    (F : Outs (State.addr B) (stepRanges w r t u j qo) m m') {e : Nat} (he : e + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr)
    (hd : ∀ d ∈ [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ], e + 4 ≤ d ∨ d + 4 ≤ e) :
    slot m' B e = slot m B e := by
  have := Outs.val32 (k := 1) (d := e) F (fun x hx => ?_) (by simp only [VG.Impl.Rsa.Arm.Keys.hdr] at he; omega_using [he])
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [stepRanges, ranges, List.mem_append, List.mem_map] at hx
  rcases hx with (⟨y, -, rfl⟩ | ⟨d, hd', rfl⟩) | hx
  · have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w y := Nat.le_add_right _ _; dsimp only; omega_using [he, this]
  · exact hd d hd'
  rcases List.mem_cons.mp hx with rfl | hx
  · have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w r := Nat.le_add_right _ _; dsimp only; omega_using [he, this]
  · have := qRanges_hdr x hx; omega_using [he, this]

/-- An array's words apart from the quotient's word, for an array not the quotient. -/
theorem qRanges_apart {N r m t nm u w j a o k : Nat} {qo : Option Nat} (hq : QArr N r m t nm u qo)
    (ha : ∀ q, qo = some q → q ≠ a) (hlo : arr w a ≤ o) (hhi : o + 4 * k ≤ arr w a + S w) (hj : j < w + 2) :
    ∀ x ∈ qRanges w j qo, o + 4 * k ≤ x.1 ∨ x.1 + x.2 ≤ o := by
  cases qo with
  | none => simp [qRanges]
  | some q =>
    simp only [qRanges, List.mem_singleton]; rintro _ rfl
    have := arr_disj (w := w) (ha q rfl)
    simp only [S] at this hhi
    dsimp only
    omega_using [hlo, hhi, hj, this]

/-! ## The loop -/

/-- What the steps read and never change: `w` (16), `P = 2^z` normalizing `M = [m]`
(`w / 2` words), `d`, `d₁` and `v`, `[0]` zero and `[nm] = -M`. -/
structure Prepped (x : State) (B : BitVec 32) (w m nm z M : Nat) : Prop where
  c16 : slot x.mem B 16 = w
  hM : val32 x.mem (State.addr B) (arr w m) (w / 2) = M
  hz : z ≤ 31
  hP : slot x.mem B sP = 2 ^ z
  hMP : M * 2 ^ z < 2 ^ (32 * (w / 2))
  hD : slot x.mem B sD * 2 ^ 32 + slot x.mem B sD1 = M * 2 ^ z / 2 ^ (32 * (w / 2 - 2))
  hDn : 2 ^ 31 ≤ slot x.mem B sD
  hV : slot x.mem B sV = (2 ^ 64 - 1) / slot x.mem B sD - 2 ^ 32
  z0 : val32 x.mem (State.addr B) (arr w 0) (w / 2 + 1) = 0
  hnm : val32 x.mem (State.addr B) (arr w nm) (w / 2 + 1) = 2 ^ (32 * (w / 2 + 1)) - M

theorem Prepped.step {x x' : State} {B : BitVec 32} {Z w N r m t nm u z M j : Nat} (p : Prepped x B w m nm z M)
    (h : Ws x B Z w N) (hm : m < N) (hnm : nm < N) (hN : N ≤ 256) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u)
    (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hnr : nm ≠ r) (hnt : nm ≠ t) (hnu : nm ≠ u)
    (hj : j + w / 2 ≤ w) {qo : Option Nat} (hq : QArr N r m t nm u qo)
    (F : Outs (State.addr B) (stepRanges w r t u j qo) x.mem x'.mem) :
    Prepped x' B w m nm z M := by
  have := h.wle
  obtain gm := h.fit64 hm
  obtain g0 := h.fit64 (j := 0) (by omega)
  obtain gn := h.fit64 hnm
  obtain dmr := arr_disj (w := w) hmr
  obtain dmt := arr_disj (w := w) hmt
  obtain dmu := arr_disj (w := w) hmu
  obtain d0r := arr_disj (w := w) hr0
  obtain d0t := arr_disj (w := w) ht0
  obtain d0u := arr_disj (w := w) hu0
  obtain dnr := arr_disj (w := w) hnr
  obtain dnt := arr_disj (w := w) hnt
  obtain dnu := arr_disj (w := w) hnu
  simp only [S] at gm g0 gn dmr dmt dmu d0r d0t d0u dnr dnt dnu
  obtain sl : ∀ {e}, e + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr →
      (∀ d ∈ [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ], e + 4 ≤ d ∨ d + 4 ≤ e) →
      slot x'.mem B e = slot x.mem B e := fun he hd => step_slot F he hd
  obtain hs : ∀ a, VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w a := fun _ => Nat.le_add_right _ _
  refine ⟨?_, ?_, p.hz, ?_, p.hMP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sl (by decide) (by decide)]; exact p.c16
  · rw [step_val F (by simp only [S]; omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]) (by simp only [S]; omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]) (hs m) (by omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]) (by omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu])
      (qRanges_apart hq (fun q e => by subst e; exact hq.2.2.1) (Nat.le_refl _) (by simp only [S]; omega_using [])
        (by omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]))]; exact p.hM
  · rw [sl (by decide) (by decide)]; exact p.hP
  · rw [sl (by decide) (by decide), sl (by decide) (by decide)]; exact p.hD
  · rw [sl (by decide) (by decide)]; exact p.hDn
  · rw [sl (by decide) (by decide), sl (by decide) (by decide)]; exact p.hV
  · rw [step_val F (by simp only [S]; omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]) (by simp only [S]; omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]) (hs 0) (by omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]) (by omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu])
      (qRanges_apart hq (fun q e => by subst e; exact hq.2.2.2.2.2.2) (Nat.le_refl _) (by simp only [S]; omega_using [])
        (by omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]))]; exact p.z0
  · rw [step_val F (by simp only [S]; omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]) (by simp only [S]; omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]) (hs nm) (by omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]) (by omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu])
      (qRanges_apart hq (fun q e => by subst e; exact hq.2.2.2.2.1) (Nat.le_refl _) (by simp only [S]; omega_using [])
        (by omega_using [hj, this, gm, g0, gn, dmr, dmt, dmu, d0r, d0t, d0u, dnr, dnt, dnu]))]; exact p.hnm

theorem Prepped.M_pos {x : State} {B : BitVec 32} {w m nm z M : Nat} (p : Prepped x B w m nm z M) : 0 < M :=
  Nat.pos_of_ne_zero fun e => by
    have hD := p.hD
    rw [e, Nat.zero_mul, Nat.zero_div] at hD
    have := Nat.mul_le_mul_right (2 ^ 32) p.hDn; omega_using [hD, this]

theorem Prepped.M_lt {x : State} {B : BitVec 32} {w m nm z M : Nat} (p : Prepped x B w m nm z M) :
    M < 2 ^ (32 * (w / 2)) :=
  Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) p.hMP

/-- The quotient's array, for `qo = some q`. -/
def qList : Option Nat → List Nat
  | none => []
  | some q => [q]

/-- The quotient's digits from word `k`: `[q] = ⌊⌊X / 2^(32 k)⌋ / M⌋ 2^(32 k)`, for `qo = some q`. -/
def QV (B : BitVec 32) (w X M k : Nat) (m : Mem) : Option Nat → Prop
  | none => True
  | some q => val32 m (State.addr B) (arr w q) w = X / 2 ^ (32 * k) / M * 2 ^ (32 * k)

/-- The quotient's digits a word down: the digit of the window at word `j`. -/
theorem quo_next {X M : Nat} (j : Nat) (hM : 0 < M) :
    X / 2 ^ (32 * j) / M = X / 2 ^ (32 * (j + 1)) / M * 2 ^ 32 + winY X M j / M := by
  obtain p : (2 : Nat) ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
  obtain e : X / 2 ^ (32 * j) = X / 2 ^ (32 * (j + 1)) * 2 ^ 32 + X / 2 ^ (32 * j) % 2 ^ 32 := by
    rw [p, ← Nat.div_div_eq_div_mul]; exact (Nat.div_add_mod' _ _).symm
  obtain e2 : X / 2 ^ (32 * (j + 1)) * 2 ^ 32 + X / 2 ^ (32 * j) % 2 ^ 32 =
      winY X M j + M * (X / 2 ^ (32 * (j + 1)) / M * 2 ^ 32) := by
    simp only [winY]
    have := Nat.div_add_mod (X / 2 ^ (32 * (j + 1))) M
    generalize X / 2 ^ (32 * (j + 1)) / M = A at this ⊢
    generalize X / 2 ^ (32 * (j + 1)) % M = R at this ⊢
    rw [← this, Nat.add_mul, Nat.mul_assoc]
    omega_using []
  rw [e, e2, Nat.add_mul_div_left _ _ hM, Nat.add_comm]

/-- A number whose words below `j + 1` are zero: its word `j` set to `v`. -/
theorem quo_split {P low v hi Q : Nat} (hP : 0 < P) (hlow : low < P) (hv : v < 2 ^ 32)
    (h : low + P * (v + 2 ^ 32 * hi) = Q * (P * 2 ^ 32)) : low = 0 ∧ v = 0 ∧ hi = Q := by
  rw [show Q * (P * 2 ^ 32) = P * (2 ^ 32 * Q) by rw [Nat.mul_comm Q, Nat.mul_assoc]] at h
  obtain m1 := congrArg (· % P) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow, Nat.mul_mod_right] at m1
  rw [m1, Nat.zero_add] at h
  obtain h2 := Nat.eq_of_mul_eq_mul_left hP h
  obtain m2 := congrArg (· % 2 ^ 32) h2
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv, Nat.mul_mod_right] at m2
  rw [m2, Nat.zero_add] at h2
  exact ⟨m1, m2, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos 32) h2⟩

/-- The loop's invariant at the window at word `j`: `[r]`'s `w + 1` words are `X`'s below `j`
and `winY X M j` from `j`; `Prepped`; the quotient's digits above `j` for `qo = some q`; and
only `[r]`, `[t]`, `[u]`, `[q]` and the steps' header words changed since `s0`. -/
structure DivSt (s0 x : State) (B : BitVec 32) (Z w N r m t nm u z M X j : Nat) (qo : Option Nat := none) :
    Prop where
  ws : Ws x B Z w N
  pre : Prepped x B w m nm z M
  J : slot x.mem B sJ = 4 * j
  hj : j + w / 2 ≤ w
  val : val32 x.mem (State.addr B) (arr w r) (w + 1) = X % 2 ^ (32 * j) + 2 ^ (32 * j) * winY X M j
  keep : Keep B w ([r, t, u] ++ qList qo) [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ] s0.mem x.mem
  quo : QV B w X M (j + 1) x.mem qo
  rest : Rest divRegs s0 x

/-- A step from the invariant: the remainder of `X`'s words from `j` there, and the quotient's
digit at `j`. -/
theorem stepD_ok {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat} {qo : Option Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j qo) (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N)
    (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t)
    (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0)
    (hdw : 3 ≤ w / 2) (hq : QArr N r m t nm u qo := by trivial) :
    WP isa (step r m t nm u qo) x fun x' => Ws x' B Z w N ∧ Prepped x' B w m nm z M ∧
      slot x'.mem B sJ = (BitVec.ofNat 32 (4 * j) - 4).toNat ∧
      val32 x'.mem (State.addr B) (arr w r) (w + 1) = X % 2 ^ (32 * j) + 2 ^ (32 * j) * (X / 2 ^ (32 * j) % M) ∧
      Keep B w ([r, t, u] ++ qList qo) [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ] s0.mem x'.mem ∧
      QV B w X M j x'.mem qo ∧ Rest divRegs s0 x' := by
  have := I.ws.wle
  have hj := I.hj
  obtain gr := I.ws.fit64 hr
  obtain dt := arr_disj (w := w) hrt
  obtain du := arr_disj (w := w) hru
  simp only [S] at gr dt du
  have hM0 := I.pre.M_pos
  have hMl := I.pre.M_lt
  obtain hWY : winY X M j < 2 ^ (32 * (w / 2 + 1)) := by
    have := winY_lt (X := X) (j := j) hM0
    rw [show 32 * (w / 2 + 1) = 32 * (w / 2) + 32 by omega_using [], Nat.pow_add]
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (Nat.le_of_lt hMl))
  obtain e1 : w + 1 = j + ((w / 2 + 1) + (w - j - w / 2)) := by omega_using [hj]
  have dec := I.val
  rw [e1, val32_append, val32_append] at dec
  obtain ⟨-, hwin, hhigh⟩ := parts_unique (val32_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) hWY dec
  obtain apR : ∀ {o k}, arr w r ≤ o → o + 4 * k ≤ arr w r + S w →
      ∀ x ∈ qRanges w j qo, o + 4 * k ≤ x.1 ∨ x.1 + x.2 ≤ o := fun hlo hhi =>
    qRanges_apart hq (fun q e => by subst e; exact hq.2.1) hlo hhi (by omega_using [hj])
  refine WP.mono (step_ok I.ws hr hm ht hnm hu hN hmr.symm hnr.symm I.pre.c16 hdw I.J hj hwin
    I.pre.hM (winY_lt hM0) I.pre.hz I.pre.hP I.pre.hMP I.pre.hD I.pre.hDn I.pre.hV I.pre.hnm hq)
    fun x' ⟨W', V', J', F', D', R'⟩ => ⟨W', I.pre.step I.ws hm hnm hN hmr hmt hmu hr0 ht0 hu0 hnr htn.symm hnu hj
      hq F', J', ?_, ?_, ?_, I.rest.trans R'⟩
  · have hs : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w r := Nat.le_add_right _ _
    have hlow := I.val
    rw [e1, val32_append, val32_append, V', winY_mod,
      step_val F' (o := arr w r) (k := j) (by simp only [S]; omega_using [hj, dt]) (by simp only [S]; omega_using [hj, du]) hs (by omega_using [])
        (by omega_using [hj, gr]) (apR (Nat.le_refl _) (by simp only [S]; omega_using [hj])),
      step_val F' (o := arr w r + 4 * j + 4 * (w / 2 + 1)) (k := w - j - w / 2) (by simp only [S]; omega_using [hj, dt])
        (by simp only [S]; omega_using [hj, du]) (by omega_using [hs]) (by omega_using []) (by omega_using [hj, gr]) (apR (by omega_using []) (by simp only [S]; omega_using [hj])), hhigh]
    rw [e1, val32_append, val32_append, hhigh, hwin] at hlow
    obtain ⟨hl, -, -⟩ := parts_unique (val32_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) hWY hlow
    rw [hl, Nat.mul_zero, Nat.add_zero]
  · refine I.keep.trans (show Keep B w ([r, t, u] ++ qList qo) _ x.mem x'.mem from Outs.widen F' fun q hq' => ?_)
    obtain mA : ∀ a ∈ [r, t, u] ++ qList qo,
        (arr w a, S w) ∈ ranges w ([r, t, u] ++ qList qo) [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ] :=
      fun a ha => List.mem_append_left _ (List.mem_map_of_mem ha)
    simp only [stepRanges, List.mem_append] at hq'
    rcases hq' with hq' | hq'
    · simp only [ranges, List.mem_append, List.mem_map] at hq'
      rcases hq' with ⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩
      · refine ⟨_, mA y ?_, Nat.le_refl _, Nat.le_refl _⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp
      · exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem hd), Nat.le_refl _, Nat.le_refl _⟩
    rcases List.mem_cons.mp hq' with rfl | hq'
    · exact ⟨_, mA r (by simp), by dsimp only; omega_using [], by dsimp only; simp only [S]; omega_using [hj]⟩
    · cases qo with
      | none => simp [qRanges] at hq'
      | some qa =>
        simp only [qRanges, List.mem_singleton] at hq'
        subst hq'
        exact ⟨_, mA qa (by simp [qList]), by dsimp only; omega_using [], by dsimp only; simp only [S]; omega_using [hj]⟩
  · cases qo with
    | none => trivial
    | some qa =>
      obtain ⟨hqN, hqr, hqm, hqt, hqn, hqu, hq0⟩ := hq
      obtain gq := I.ws.fit64 hqN
      obtain q160 : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w qa := Nat.le_add_right _ _
      obtain dqt := arr_disj (w := w) hqt
      obtain dqu := arr_disj (w := w) hqu
      obtain dqr := arr_disj (w := w) hqr
      simp only [S] at gq dqt dqu dqr
      have quo := I.quo
      simp only [QV, QOut] at quo D' ⊢
      obtain sp : ∀ mm : Mem, val32 mm (State.addr B) (arr w qa) w = val32 mm (State.addr B) (arr w qa) j +
          2 ^ (32 * j) * (w32 mm (State.addr B) (arr w qa + 4 * j) +
            2 ^ 32 * val32 mm (State.addr B) (arr w qa + 4 * j + 4 * 1) (w - j - 1)) := fun mm => by
        obtain h3 := val32_append mm (State.addr B) (arr w qa) j (1 + (w - j - 1))
        obtain h4 := val32_append mm (State.addr B) (arr w qa + 4 * j) 1 (w - j - 1)
        rw [show j + (1 + (w - j - 1)) = w by omega_using [hdw, hj]] at h3
        rw [h3, h4]
        simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
      obtain apQ : ∀ {o k}, o + 4 * k ≤ arr w qa + 4 * j ∨ arr w qa + 4 * j + 4 ≤ o →
          ∀ x ∈ qRanges w j (some qa), o + 4 * k ≤ x.1 ∨ x.1 + x.2 ≤ o := fun h' => by
        simp only [qRanges, List.mem_singleton]; rintro _ rfl; exact h'
      rw [sp] at quo ⊢
      rw [step_val F' (o := arr w qa) (k := j) (by simp only [S]; omega_using [hj, dqt]) (by simp only [S]; omega_using [hj, dqu]) q160
          (by omega_using [hj, dqr]) (by omega_using [hj, gq]) (apQ (Or.inl (by omega_using []))),
        step_val F' (o := arr w qa + 4 * j + 4 * 1) (k := w - j - 1) (by simp only [S]; omega_using [hj, dqt])
          (by simp only [S]; omega_using [hj, dqu]) (by omega_using [q160]) (by omega_using [dqr]) (by omega_using [hj, gq]) (apQ (Or.inr (by omega_using []))), D']
      obtain hP := Nat.two_pow_pos (32 * j)
      obtain p1 : (2 : Nat) ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
      rw [p1] at quo
      obtain ⟨l0, -, hi⟩ := quo_split hP (val32_lt _ _ _ _) (BitVec.isLt _) quo
      rw [l0, hi, quo_next j hM0, Nat.zero_add, Nat.mul_comm (2 ^ (32 * j)), Nat.add_comm, Nat.mul_comm (2 ^ 32), p1]

theorem Prepped.of_mem {x x' : State} {B : BitVec 32} {w m nm z M : Nat} (p : Prepped x B w m nm z M)
    (e : x'.mem = x.mem) : Prepped x' B w m nm z M := by
  obtain ⟨a, b, c, d, f, g, i, k, l, n⟩ := p
  exact ⟨e ▸ a, e ▸ b, c, e ▸ d, f, e ▸ g, e ▸ i, e ▸ k, e ▸ l, e ▸ n⟩

/-- The window from the invariant. -/
theorem DivSt.window {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat} {qo : Option Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j qo) :
    val32 x.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = winY X M j := by
  have hj := I.hj
  have hM0 := I.pre.M_pos
  have hMl := I.pre.M_lt
  obtain hWY : winY X M j < 2 ^ (32 * (w / 2 + 1)) := by
    have := winY_lt (X := X) (j := j) hM0
    rw [show 32 * (w / 2 + 1) = 32 * (w / 2) + 32 by omega_using [], Nat.pow_add]
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (Nat.le_of_lt hMl))
  obtain e1 : w + 1 = j + ((w / 2 + 1) + (w - j - w / 2)) := by omega_using [hj]
  have dec := I.val
  rw [e1, val32_append, val32_append] at dec
  exact (parts_unique (val32_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) hWY dec).2.1

/-- The estimate's frame from the invariant: `Ws`, `w` and the offset. -/
theorem DivSt.est {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat} {qo : Option Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j qo) (hr : r < N) (hN : N ≤ 256) (hdw : 3 ≤ w / 2) :
    WP isa (.block (estimate r)) x fun v => Ws v B Z w N ∧ slot v.mem B 16 = w ∧ slot v.mem B sJ = 4 * j := by
  rw [← List.append_nil (estimate r)]
  exact estimate_ok I.ws hr hN I.pre.c16 hdw I.J I.hj I.window (winY_lt I.pre.M_pos) I.pre.hz I.pre.hP
    I.pre.hMP I.pre.hD I.pre.hDn I.pre.hV fun t q _ _ _ _ K W _ => WP.block_nil ⟨W,
      by rw [K.slot (by decide) (by decide)]; exact I.pre.c16, by rw [K.slot (by decide) (by decide)]; exact I.J⟩

/-- The loop's body: the step, and the condition: not zero unless `j = 1`, then the invariant
a word down. -/
theorem body_ok {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X n : Nat} {qo : Option Nat}
    (In : DivSt s0 x B Z w N r m t nm u z M X n qo) (hn : 1 ≤ n) (hr : r < N) (hm : m < N) (ht : t < N)
    (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r)
    (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0)
    (hu0 : u ≠ 0) (hdw : 3 ≤ w / 2) (hq : QArr N r m t nm u qo := by trivial) :
    WP isa (.seq (step r m t nm u qo) (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)])) x fun y =>
      isa.eval .ne y = some (!decide (n = 1)) ∧ DivSt s0 y B Z w N r m t nm u z M X (n - 1) qo := by
  have := In.ws.wle
  have hjn := In.hj
  rw [WP.seq_iff]
  refine WP.mono (stepD_ok In hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw hq)
    fun y1 ⟨W1, P1, J1, V1, K1, Q1, R1⟩ => ?_
  refine wp_ldrSlot W1 (d := sJ) (by decide) fun y2 u2 => ?_
  refine wp_cmp (op2_imm (by decide)) fun y3 f3 hz3 => WP.block_nil ?_
  obtain r0v : y2.gpr .r0 = BitVec.ofNat 32 (4 * n) - 4 := by
    rw [u2.gpr]; apply BitVec.eq_of_toNat_eq; exact J1
  obtain e4 : (BitVec.ofNat 32 (4 * n) - 4).toNat = 4 * (n - 1) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]; omega_using [hn, this, hjn]
  obtain m3 : y3.mem = y1.mem := f3.mem.trans u2.mem
  obtain W3 : Ws y3 B Z w N := (W1.of_upd u2 (by decide) (by decide) (by decide)).of (by rw [f3.gpr])
    (by rw [f3.gpr]) (by rw [f3.gpr]) f3.wr
  obtain R3 : Rest divRegs s0 y3 := R1.trans ((u2.rest (by decide)).trans (f3.rest _))
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_using [hn]⟩
  refine ⟨?_, W3, P1.of_mem m3, ?_, by omega_using [hjn], ?_, by rw [m3]; exact K1, ?_, R3⟩
  · change some (!y3.z) = some (!decide (k + 1 = 1))
    rw [hz3, r0v, show BitVec.ofNat 32 (4 * (k + 1)) - 4 - 0 = BitVec.ofNat 32 (4 * (k + 1)) - 4 from
      BitVec.sub_zero _]
    by_cases e : k = 0
    · subst e; decide
    · have : BitVec.ofNat 32 (4 * (k + 1)) - 4 ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'; rw [e4] at this; simp at this; omega_arith
      rw [show (BitVec.ofNat 32 (4 * (k + 1)) - 4 == 0) = false from beq_eq_false_iff_ne.mpr this]
      simp [e]
  · simp only [slot]; rw [m3]; simp only [slot] at J1; rw [J1, e4]
  · rw [m3, V1, Nat.add_sub_cancel, fold_next]
  · rw [m3, Nat.add_sub_cancel]; exact Q1

/-- The loop: the steps at words `j`, …, `1`, while the window's offset, a word down, is not zero. -/
theorem loop_ok {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat} {qo : Option Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j qo) (hj1 : 1 ≤ j) (hr : r < N) (hm : m < N) (ht : t < N)
    (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r)
    (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0)
    (hu0 : u ≠ 0) (hdw : 3 ≤ w / 2) (hq : QArr N r m t nm u qo := by trivial) :
    WP isa (.loop (.seq (step r m t nm u qo) (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)])) .ne) x
      fun y => DivSt s0 y B Z w N r m t nm u z M X 0 qo := by
  refine WP.loop (M := isa) (fun n y => DivSt s0 y B Z w N r m t nm u z M X n qo ∧ 1 ≤ n) ?_ j x ⟨I, hj1⟩
  rintro n y ⟨In, hn⟩
  refine WP.mono (body_ok In hn hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw hq)
    fun y' ⟨c, I'⟩ => ?_
  by_cases e : n = 1
  · left; subst e; exact ⟨by rw [c]; rfl, I'⟩
  · right; exact ⟨by rw [c]; simp [e], n - 1, by omega_using [hn], I', by omega_using [hn, e]⟩

/-! ## The preparation -/

theorem shl2_val {w : Nat} (_hw : w ≤ 1024) : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

/-- The low `k` words of a number of `n` words. -/
theorem val32_low (mem : Mem) (base : Addr) (d : Nat) {k n : Nat} (h : k ≤ n) :
    val32 mem base d k = val32 mem base d n % 2 ^ (32 * k) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [val32_append, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

/-- `-M` modulo a shorter power: `(2^(32 n) - M) mod 2^(32 k) = 2^(32 k) - M` for `0 < M < 2^(32 k)`. -/
theorem neg_low {M k n : Nat} (hkn : k ≤ n) (hM0 : 0 < M) (hM : M < 2 ^ (32 * k)) :
    (2 ^ (32 * n) - M) % 2 ^ (32 * k) = 2 ^ (32 * k) - M := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.mul_add, Nat.pow_add]
  obtain hE := Nat.two_pow_pos (32 * e)
  obtain ⟨E, hE'⟩ : ∃ E, 2 ^ (32 * e) = E + 1 := ⟨2 ^ (32 * e) - 1, by omega_using [hE]⟩
  rw [hE', Nat.mul_add, Nat.mul_one, show 2 ^ (32 * k) * E + 2 ^ (32 * k) - M = (2 ^ (32 * k) - M) + 2 ^ (32 * k) * E
    by omega_using [hM], Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega_using [hM0, hM])]

/-- The preparation's first half: `[r] := [a]` with word `w` zero, and `[nm] := -[m]`. -/
theorem prepA_ok {s : State} {B : BitVec 32} {Z w N a r m nm : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (hm : m < N) (hnm : nm < N) (hN : N ≤ 256) (hra : r ≠ a) (hr0 : r ≠ 0) (hrm : r ≠ m) (hn0 : nm ≠ 0)
    (hnm' : nm ≠ m) (hnr : nm ≠ r) {M : Nat} (hM : num s.mem B w m = M) (hM0 : 0 < M)
    (hz : num s.mem B w 0 = 0) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ v, Ws v B Z w N → val32 v.mem (State.addr B) (arr w r) (w + 1) = num s.mem B w a →
      num v.mem B w nm = 2 ^ (32 * w) - M → Keep B w [r, nm] [] s.mem v.mem → Rest opRegs s v →
      WP isa rest v Q) :
    WP isa (.seq (copy r a) (.seq (.block (ptr .r0 r ++ ([.dp .add .r0 .r0 (.shifted .r9 .lsl 2),
      .mov .r1 (.imm 0), .str .r1 .r0 0] : List Instr))) (.seq (sub3 nm 0 m) rest))) s Q := by
  have := h.wle
  have nw := h.nowrap
  obtain fr := h.arr_fit hr
  obtain gr := h.fit64 hr
  obtain g0 := h.fit64 (j := 0) (by omega_using [ha])
  obtain gm := h.fit64 hm
  simp only [S] at fr gr g0 gm
  rw [WP.seq_iff]
  refine WP.mono (copy_ok h hr ha hN hra) fun v1 ⟨W1, K1, C1, R1, _⟩ => ?_
  rw [WP.seq_iff]
  refine ptr_ok W1 (r := .r0) (by decide) (j := r) (by omega_using [hr, hN]) fun v2 p2 r2 m2 W2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun v3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun v4 u4 => ?_
  obtain a4 : State.addr (v4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * w) := by
    rw [u4.other _ (by decide), u3.gpr, dpVal, p2, W2.r9, shl2_val (by omega_using [this]), BitVec.add_zero, add_ofNat_assoc]
    exact h.addr (by omega_using [fr])
  refine wp_str (by decide) a4 (by rw [u4.wr, u3.wr, r2.wr, R1.wr]; exact h.write (by omega_using [fr]))
    fun v5 u5 => WP.block_nil ?_
  obtain W5 : Ws v5 B Z w N := ((W2.of_upd u3 (by decide) (by decide) (by decide)).of_upd u4 (by decide) (by decide)
    (by decide)).of_mupd u5
  obtain m5 : v5.mem = v1.mem.writeW (off (State.addr B) (arr w r + 4 * w)) (0 : BitVec 32) := by
    rw [u5.mem, u4.gpr, u4.mem, u3.mem, m2]
  obtain K5 : Keep B w [r] [] s.mem v5.mem := by
    rw [m5]; exact K1.trans (Keep.of_arr (d := 4 * w) (writeW32_outside _ _ _ (by omega_using [gr])) (by simp only [S]; omega_using [])
      (by simp))
  obtain V5 : val32 v5.mem (State.addr B) (arr w r) (w + 1) = num s.mem B w a := by
    rw [val32_succ, m5, w32_write_self, Outside.val32 (writeW32_outside _ _ _ (by omega_using [gr])) (by omega_using []) (by omega_using [gr])]
    simp only [num] at C1 ⊢
    rw [C1]; rfl
  obtain R5 : Rest opRegs s v5 :=
    R1.trans ((r2.mono (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest _))))
  rw [WP.seq_iff]
  refine WP.mono (sub3_ok W5 hnm (by omega_using [ha]) hm hN hn0 hnm') fun v6 ⟨W6, K6, E6, b6, R6⟩ => ?_
  obtain Z5 : num v5.mem B w 0 = 0 := by rw [K5.num (by simpa using hr0) (by simp) g0]; exact hz
  obtain M5 : num v5.mem B w m = M := by rw [K5.num (by simpa using hrm) (by simp) gm]; exact hM
  rw [Z5, M5] at E6
  obtain hb : (v6.gpr .r11).toNat = 1 := by
    rcases Nat.lt_or_ge (v6.gpr .r11).toNat 1 with h0 | h1
    · have : (v6.gpr .r11).toNat = 0 := by omega_using [h0]
      rw [this] at E6; omega
    · omega_using [b6, h1]
  rw [hb, Nat.mul_one] at E6
  refine k v6 W6 ?_ (by omega_using [E6]) ((K5.mono).trans K6.mono) (R5.trans R6)
  rw [Outs.val32 K6 (fun q hq => ?_) (by omega_using [gr])]
  · exact V5
  · simp only [ranges, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      List.map_nil, List.append_nil] at hq
    obtain ⟨y, rfl, rfl⟩ := hq
    have := arr_disj (w := w) hnr; simp only [S] at this ⊢; omega_using [this]

open VG.Proof.Bignum.NormMask32 VG.Proof.Bignum.WordTop32 in
/-- The normalization's arithmetic, for `M`'s top three words `T ≠ 0`, `U`, `V` and `z = lz T`:
`M 2^z` fits, its top two words are `norm`'s `d` and `d₁`, `d` has its top bit set, and `M`
is at least `2^(32 (k + 2))`. -/
theorem norm_math {M k T U V L : Nat}
    (hM : M = L + 2 ^ (32 * k) * V + 2 ^ (32 * k) * 2 ^ 32 * (U + 2 ^ 32 * T)) (hL : L < 2 ^ (32 * k))
    (hV : V < 2 ^ 32) (hU : U < 2 ^ 32) (hT0 : 0 < T) (hT : T < 2 ^ 32) :
    M * 2 ^ lz T < 2 ^ (32 * (k + 3)) ∧
      (T * 2 ^ lz T + U * 2 ^ lz T / 2 ^ 32) * 2 ^ 32 + (U * 2 ^ lz T % 2 ^ 32 + V * 2 ^ lz T / 2 ^ 32) =
        M * 2 ^ lz T / 2 ^ (32 * (k + 1)) ∧
      2 ^ 31 ≤ T * 2 ^ lz T + U * 2 ^ lz T / 2 ^ 32 ∧ 2 ^ (32 * (k + 2)) ≤ M ∧ lz T ≤ 31 := by
  obtain ⟨b1, b2⟩ := shifted_bounds hT0 hT (Nat.le_refl (lz T))
  simp only [↓reduceIte] at b2
  obtain hz : lz T ≤ 31 := by unfold lz; omega_using []
  obtain b3 : 2 ^ 31 ≤ T * 2 ^ lz T := by
    have := Nat.div_mul_le_self (T * 2 ^ lz T) (2 ^ 31); rw [b2, Nat.one_mul] at this
    refine Nat.le_of_not_lt fun hc => ?_
    rw [Nat.div_eq_of_lt hc] at b2; exact absurd b2 (by decide)
  obtain e2 : 2 ^ (32 * (k + 2)) = 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 := by
    rw [show 32 * (k + 2) = 32 * k + 32 + 32 by omega_using [], Nat.pow_add, Nat.pow_add]
  obtain hlow : L + 2 ^ (32 * k) * V + 2 ^ (32 * k) * 2 ^ 32 * U < 2 ^ (32 * (k + 2)) := by
    rw [e2]
    obtain h1 := Nat.mul_le_mul_left (2 ^ (32 * k)) (show V + 1 ≤ 2 ^ 32 by omega_using [hV])
    obtain h2 := Nat.mul_le_mul_left (2 ^ (32 * k) * 2 ^ 32) (show U + 1 ≤ 2 ^ 32 by omega_using [hU])
    rw [Nat.mul_add, Nat.mul_one] at h1 h2
    omega_using [hL, h1, h2]
  obtain hM' : M = (L + 2 ^ (32 * k) * V + 2 ^ (32 * k) * 2 ^ 32 * U) + 2 ^ (32 * (k + 2)) * T := by
    rw [hM, e2, Nat.mul_add, Nat.mul_assoc (2 ^ (32 * k) * 2 ^ 32) (2 ^ 32)]; omega_using []
  -- `(T + 1) 2^z ≤ 2^32`: both multiples of `2^z`.
  obtain hT1 : (T + 1) * 2 ^ lz T ≤ 2 ^ 32 := by
    obtain e : 2 ^ 32 = 2 ^ (32 - lz T) * 2 ^ lz T := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega_using [hz])]
    obtain hlt : T < 2 ^ (32 - lz T) := by rw [e] at b1; exact Nat.lt_of_mul_lt_mul_right b1
    rw [e]; exact Nat.mul_le_mul_right _ hlt
  obtain hMP : M * 2 ^ lz T < 2 ^ (32 * (k + 3)) := by
    obtain h1 : M < (T + 1) * 2 ^ (32 * (k + 2)) := by
      rw [hM', Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ (32 * (k + 2)))]; omega_using [hlow]
    obtain h2 : M * 2 ^ lz T < (T + 1) * 2 ^ lz T * 2 ^ (32 * (k + 2)) := by
      rw [Nat.mul_right_comm]; exact Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    rw [show 32 * (k + 3) = 32 + 32 * (k + 2) by omega_using [], Nat.pow_add]
    exact Nat.lt_of_lt_of_le h2 (Nat.mul_le_mul_right _ hT1)
  obtain tm := top_math (a1 := T) (a2 := U) (a3 := V) hz hL (by rw [← hM]; exact hMP)
  rw [Nat.mod_eq_of_lt b1, ← hM] at tm
  refine ⟨hMP, tm, Nat.le_trans b3 (Nat.le_add_right _ _), ?_, hz⟩
  rw [hM']
  exact Nat.le_trans (Nat.le_mul_of_pos_right _ hT0) (Nat.le_add_left _ _)

/-- The window's first word: `w - w / 2`, or `t` for `top = some t` (`winStart`). -/
abbrev jStart : Option Nat → Nat → Nat
  | none, w => w - w / 2
  | some t, _ => t

/-- What a window from word `t` needs: `1 ≤ t ≤ w - w / 2`, `4 t` an immediate, and the
dividend `X` below `2^(32 (t + w / 2))`. -/
def TopOk : Option Nat → Nat → Nat → Prop
  | none, _, _ => True
  | some t, w, X => 1 ≤ t ∧ t ≤ w - w / 2 ∧ 4 * t < 256 ∧ X < 2 ^ (32 * (t + w / 2))

theorem TopOk.facts {top : Option Nat} {w X : Nat} (h : TopOk top w X) (hX : X < 2 ^ (32 * w)) (hw : 2 ≤ w) :
    1 ≤ jStart top w ∧ jStart top w + w / 2 ≤ w ∧ X < 2 ^ (32 * (jStart top w + w / 2)) := by
  cases top with
  | none => exact ⟨by simp only [jStart]; omega_using [hw], by simp only [jStart]; omega_using [], by
      simp only [jStart]; rwa [show w - w / 2 + w / 2 = w by omega_using []]⟩
  | some t => obtain ⟨h1, h2, _, h4⟩ := h; exact ⟨h1, by simp only [jStart]; omega_using [h2], h4⟩

theorem sj_val {w : Nat} (hw : w ≤ 1024) :
    (BitVec.ofNat 32 w - BitVec.ofNat 32 w >>> 1) <<< 2 = BitVec.ofNat 32 (4 * (w - w / 2)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

/-- The window's first offset, `4 jStart`, stored at `sJ`. -/
theorem winStart_ok {x : State} {B : BitVec 32} {w : Nat} (top : Option Nat) (r8 : x.gpr .r8 = B)
    (r9 : x.gpr .r9 = BitVec.ofNat 32 w) (hw : w ≤ 1024)
    (aJ : State.addr (B + BitVec.ofNat 32 sJ) = off (State.addr B) sJ) (wJ : InRegions x.wr (off (State.addr B) sJ) 4)
    (ht : ∀ t, top = some t → 4 * t < 256) :
    WP isa (.block (winStart top)) x fun x' =>
      x'.mem = x.mem.writeW (off (State.addr B) sJ) (BitVec.ofNat 32 (4 * jStart top w)) ∧ Rest [.r0] x x' := by
  cases top with
  | none => exact WP.keep [.r0] (by simp only [winStart, jStart]; krun [r8, r9, aJ, wJ, sj_val hw]) (by decide)
  | some t =>
    obtain henc : VG.Arm.encodable (BitVec.ofNat 32 (4 * t)) = true :=
      VG.Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; have := ht t rfl; omega_using [this])
    exact WP.keep [.r0] (by simp only [winStart, jStart]; krun [r8, aJ, wJ, henc]) rfl rfl

open VG.Proof.Bignum.NormMask32 VG.Proof.Bignum.WordTop32 in
/-- The preparation's second half: `P`, `d`, `d₁` by `norm`, `v` by `recip`, and the window at
word `w - w / 2`, which starts the loop's invariant for `X`, `[r]`'s `w + 1` words. -/
theorem prepB_ok {v : State} {B : BitVec 32} {Z w N r m t nm u : Nat} (h : Ws v B Z w N) (hr : r < N) (hm : m < N)
    (hnm : nm < N) (hN : N ≤ 256) (hw6 : 6 ≤ w) (h16 : slot v.mem B 16 = w)
    {M X : Nat} (hM : num v.mem B w m = M) (hMl : M < 2 ^ (32 * (w / 2)))
    (hT0 : 0 < w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 1))) (hz : num v.mem B w 0 = 0)
    (hnmv : num v.mem B w nm = 2 ^ (32 * w) - M) (hX : val32 v.mem (State.addr B) (arr w r) (w + 1) = X)
    (hXl : X < 2 ^ (32 * w)) {top : Option Nat} (htop : TopOk top w X) :
    WP isa (.seq (norm m) (.seq recip (.block (winStart top)))) v fun x =>
      DivSt x x B Z w N r m t nm u (lz (w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)))) M X (jStart top w) ∧
      Keep B w [] [sP, sD, sD1, sV, sJ] v.mem x.mem ∧ Rest divRegs v x := by
  have := h.wle
  have nw := h.nowrap
  have hz' := h.hdr_le
  obtain gm := h.fit64 hm
  obtain g0 := h.fit64 (j := 0) (by omega_using [hr])
  obtain gn := h.fit64 hnm
  obtain fr := h.fit64 hr
  simp only [S] at gm g0 gn fr
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  obtain ⟨k, hk⟩ : ∃ k, w / 2 = k + 3 := ⟨w / 2 - 3, by omega_using [hw6]⟩
  generalize eT : w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)) = T at hT0 ⊢
  obtain hT : T < 2 ^ 32 := eT ▸ BitVec.isLt _
  obtain hMv : val32 v.mem (State.addr B) (arr w m) (k + 3) = M := by
    rw [← hk, val32_low _ _ _ (show w / 2 ≤ w by omega_using [])]; simp only [num] at hM; rw [hM, Nat.mod_eq_of_lt hMl]
  rw [val32_top3] at hMv
  obtain NM := norm_math (M := M) (k := k) (T := T) (U := w32 v.mem (State.addr B) (arr w m + 4 * (k + 1)))
    (V := w32 v.mem (State.addr B) (arr w m + 4 * k)) (L := val32 v.mem (State.addr B) (arr w m) k)
    (by rw [← eT, show arr w m + 4 * (w / 2 - 1) = arr w m + 4 * (k + 2) by omega_using [hk]]; exact hMv.symm)
    (val32_lt _ _ _ _)
    (BitVec.isLt _) (BitVec.isLt _) hT0 hT
  obtain ⟨hMP, hDv, hDn, hMge, hz31⟩ := NM
  rw [WP.seq_iff]
  refine WP.mono (norm_ok h hm hN hw6 eT (rfl : _ = w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 2)))
    (rfl : _ = w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 3))) hT0) fun x1 ⟨P1, D1, D11, K1, W1, R1⟩ => ?_
  rw [show arr w m + 4 * (w / 2 - 2) = arr w m + 4 * (k + 1) by omega_using [hk]] at D1 D11
  rw [show arr w m + 4 * (w / 2 - 3) = arr w m + 4 * k by omega_using [hk]] at D11
  rw [WP.seq_iff]
  refine WP.mono (recip_ok W1 (d := slot x1.mem B sD) rfl (by rw [D1]; exact hDn) (BitVec.isLt _))
    fun x2 ⟨V2, K2, R2⟩ => ?_
  obtain W2 : Ws x2 B Z w N := W1.rest R2
  obtain aJ : State.addr (B + BitVec.ofNat 32 sJ) = off (State.addr B) sJ := h.addr (by simp only [sJ]; omega_using [hz'])
  obtain wJ : InRegions x2.wr (off (State.addr B) sJ) 4 := W2.write (by simp only [sJ]; omega_using [hz'])
  obtain ⟨hj1, hjw, hXj⟩ := htop.facts hXl (by omega_using [hw6])
  refine WP.mono (winStart_ok top W2.r8 W2.r9 this aJ wJ fun t e => by subst e; exact htop.2.2.1)
    fun x3 ⟨m3, R3⟩ => ?_
  generalize jStart top w = j0 at hj1 hjw hXj m3 ⊢
  obtain hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega_using [nw]
  obtain W3 : Ws x3 B Z w N := W2.rest R3
  -- Header words other than `sJ` after the last store.
  obtain s3 : ∀ {e}, e + 4 ≤ 160 → (e + 4 ≤ sJ ∨ sJ + 4 ≤ e) → slot x3.mem B e = slot x2.mem B e := fun he hd => by
    simp only [slot]; rw [m3, w32_write_ne hA (by simp only [sJ]; omega_using [hz']) (by omega_using [hz', he]) hd]
  obtain a3 : ∀ {a o n}, arr w a ≤ o → o + 4 * n ≤ 2 ^ 64 →
      val32 x3.mem (State.addr B) o n = val32 v.mem (State.addr B) o n := fun {a o n} ho hf => by
    have : 160 ≤ arr w a := Nat.le_add_right _ _
    rw [m3, Outside.val32 (writeW32_outside _ _ _ (by simp only [sJ]; omega_using [])) (Or.inr (by simp only [sJ]; omega_using [ho, this])) hf]
    rw [Outs.val32 K2 (fun q hq => ?_) hf, Outs.val32 K1 (fun q hq => ?_) hf]
    · simp only [ranges, List.map_nil, List.nil_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with ⟨d, hd, rfl⟩
      rcases hd with rfl | rfl | rfl <;> simp only [sP, sD, sD1] <;> omega_using [ho, this]
    · simp only [ranges, List.map_nil, List.nil_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with ⟨d, rfl, rfl⟩
      simp only [sV]; omega_using [ho, this]
  obtain sl12 : ∀ {e}, e + 4 ≤ 160 → (∀ d ∈ [sP, sD, sD1, sV], e + 4 ≤ d ∨ d + 4 ≤ e) →
      slot x2.mem B e = slot v.mem B e := fun he hd => by
    rw [K2.slot he (fun d hd' => hd d (by simp at hd' ⊢; simp [hd'])), K1.slot he (fun d hd' => hd d (by
      simp at hd' ⊢; rcases hd' with rfl | rfl | rfl <;> simp))]
  obtain hk1 : w / 2 - 2 = k + 1 := by omega_using [hk]
  refine ⟨⟨W3, ⟨?_, ?_, hz31, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by omega_using [hjw], ?_, Keep.refl _ _ _ _ _, trivial, Rest.refl _ _⟩, ?_, ?_⟩
  · rw [s3 (by decide) (by decide), sl12 (by decide) (by decide)]; exact h16
  · rw [a3 (a := m) (Nat.le_refl _) (by omega_using [gm]), val32_low _ _ _ (show w / 2 ≤ w by omega_using [])]
    simp only [num] at hM; rw [hM, Nat.mod_eq_of_lt hMl]
  · rw [s3 (by decide) (by decide), K2.slot (by decide) (by decide)]; exact P1
  · rw [hk]; exact hMP
  · rw [s3 (by decide) (by decide), s3 (by decide) (by decide), K2.slot (by decide) (by decide),
      K2.slot (by decide) (by decide), D1, D11, hk1]; exact hDv
  · rw [s3 (by decide) (by decide), K2.slot (by decide) (by decide), D1]; exact hDn
  · rw [s3 (by decide) (by decide), s3 (by decide) (by decide), V2, K2.slot (e := sD) (by decide) (by decide)]
  · rw [a3 (a := 0) (Nat.le_refl _) (by omega_using [g0]), val32_low _ _ _ (show w / 2 + 1 ≤ w by omega_using [hw6])]
    simp only [num] at hz; rw [hz, Nat.zero_mod]
  · rw [a3 (a := nm) (Nat.le_refl _) (by omega_using [gn]), val32_low _ _ _ (show w / 2 + 1 ≤ w by omega_using [hw6])]
    simp only [num] at hnmv; rw [hnmv]
    exact neg_low (by omega_using [hw6]) (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hMge)
      (Nat.lt_of_lt_of_le hMl (Nat.pow_le_pow_right (by decide) (by omega_using [])))
  · simp only [slot]; rw [m3, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this, hjw])]
  · rw [a3 (a := r) (Nat.le_refl _) (by omega_using [fr]), hX]
    refine (fold_top ?_).symm
    obtain e : 2 ^ (32 * (j0 + w / 2)) = 2 ^ (32 * (j0 + 1)) * 2 ^ (32 * (k + 2)) := by
      rw [← Nat.pow_add]; congr 1; omega_using [hk]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [e, Nat.mul_comm] at hXj
    exact Nat.lt_of_lt_of_le hXj (Nat.mul_le_mul_right _ hMge)
  · rw [m3]
    exact ((K1.mono).trans K2.mono).trans (keep_write _ _ (by simp) (by simp only [sJ]; omega_using []))
  · exact (R1.mono (by decide)).trans ((R2.mono (by decide)).trans (R3.mono (by decide)))

/-- The preparation: the loop's invariant at the window at word `w - w / 2`. -/
theorem prep_ok {s : State} {B : BitVec 32} {Z w N a r m nm : Nat} (t u : Nat) (h : Ws s B Z w N) (ha : a < N)
    (hr : r < N) (hm : m < N) (hnm : nm < N) (hN : N ≤ 256) (hra : r ≠ a) (hmr : m ≠ r) (hnm' : nm ≠ m)
    (hnr : nm ≠ r) (hr0 : r ≠ 0) (hn0 : nm ≠ 0) (hw6 : 6 ≤ w) (h16 : slot s.mem B 16 = w) {M : Nat}
    (hM : num s.mem B w m = M) (hMl : M < 2 ^ (32 * (w / 2)))
    (hT0 : 0 < w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1))) (hz : num s.mem B w 0 = 0)
    {top : Option Nat} (htop : TopOk top w (num s.mem B w a)) :
    WP isa (prep a r m nm top) s fun x0 => (∃ z, DivSt x0 x0 B Z w N r m t nm u z M (num s.mem B w a) (jStart top w)) ∧
      Keep B w [r, nm] [sP, sD, sD1, sV, sJ] s.mem x0.mem ∧ Rest divRegs s x0 := by
  have := h.wle
  obtain gm := h.fit64 hm
  obtain g0 := h.fit64 (j := 0) (by omega_using [ha])
  simp only [S] at gm g0
  obtain hM0 : 0 < M := by
    rw [← hM]; simp only [num]
    rw [show w = (w / 2 - 1) + 1 + (w - w / 2) by omega_using [hw6], val32_append, val32_succ]
    have := Nat.mul_le_mul_left (2 ^ (32 * (w / 2 - 1))) hT0
    have := Nat.two_pow_pos (32 * (w / 2 - 1))
    obtain e : w / 2 - 1 + 1 + (w - w / 2) = w := by omega_using [hw6]
    rw [e] at *
    omega_arith
  rw [prep]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  refine prepA_ok h ha hr hm hnm hN hra hr0 hmr.symm hn0 hnm' hnr hM hM0 hz fun v W V N' K R => ?_
  obtain Mv : num v.mem B w m = M := by rw [K.num (by simp; exact ⟨hmr.symm, hnm'⟩) (by simp) gm]; exact hM
  obtain Zv : num v.mem B w 0 = 0 := by rw [K.num (by simp; exact ⟨hr0, hn0⟩) (by simp) g0]; exact hz
  obtain Tv : 0 < w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)) := by
    rw [K.word (by simp only [S]; omega_using []) (by simp; exact ⟨hmr.symm, hnm'⟩) (by simp) gm]; exact hT0
  obtain hv16 : slot v.mem B 16 = w := by rw [K.slot (by decide) (by simp)]; exact h16
  exact WP.mono (prepB_ok (t := t) (u := u) W hr hm hnm hN hw6 hv16 Mv hMl Tv Zv N' V
    (by simp only [num]; exact val32_lt _ _ _ _) htop) fun x0 ⟨I0, K0, R0⟩ =>
      ⟨⟨_, I0⟩, (K.mono).trans K0.mono, (R.mono (by decide)).trans R0⟩

/-! ## The division -/

/-- The header words the division changes. -/
abbrev divSlots : List Nat := [sP, sD, sD1, sV, sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ]

/-- The quotient's array zero, for `qo = some q`. -/
def QZ (m : Mem) (B : BitVec 32) (w : Nat) : Option Nat → Prop
  | none => True
  | some q => num m B w q = 0

/-- The preparation, with the quotient's digits above the first window (none) for `qo = some q`. -/
theorem prepQ_ok {s : State} {B : BitVec 32} {Z w N a r m nm : Nat} (t u : Nat) (h : Ws s B Z w N) (ha : a < N)
    (hr : r < N) (hm : m < N) (hnm : nm < N) (hN : N ≤ 256) (hra : r ≠ a) (hmr : m ≠ r) (hnm' : nm ≠ m)
    (hnr : nm ≠ r) (hr0 : r ≠ 0) (hn0 : nm ≠ 0) (hw6 : 6 ≤ w) (h16 : slot s.mem B 16 = w) {M : Nat}
    (hM : num s.mem B w m = M) (hMl : M < 2 ^ (32 * (w / 2)))
    (hT0 : 0 < w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1))) (hz : num s.mem B w 0 = 0)
    {top : Option Nat} (htop : TopOk top w (num s.mem B w a)) {qo : Option Nat} (hq : QArr N r m t nm u qo)
    (hq0 : QZ s.mem B w qo) :
    WP isa (prep a r m nm top) s fun x0 =>
      (∃ z, DivSt x0 x0 B Z w N r m t nm u z M (num s.mem B w a) (jStart top w) qo) ∧
      Keep B w [r, nm] [sP, sD, sD1, sV, sJ] s.mem x0.mem ∧ Rest divRegs s x0 := by
  have := h.wle
  obtain hMlo : 2 ^ (32 * (w / 2 - 1)) ≤ M := by
    rw [← hM]; simp only [num]
    rw [show w = (w / 2 - 1) + 1 + (w - w / 2) by omega_using [hw6], val32_append, val32_succ]
    have := Nat.mul_le_mul_left (2 ^ (32 * (w / 2 - 1))) hT0
    obtain e : w / 2 - 1 + 1 + (w - w / 2) = w := by omega_using [hw6]
    rw [e] at *
    omega_using [this]
  refine WP.mono (prep_ok t u h ha hr hm hnm hN hra hmr hnm' hnr hr0 hn0 hw6 h16 hM hMl hT0 hz htop)
    fun x0 ⟨⟨z0, I0⟩, K, R⟩ => ⟨⟨z0, ?_⟩, K, R⟩
  obtain ⟨-, -, hXt⟩ := htop.facts (by simp only [num]; exact val32_lt _ _ _ _) (by omega_using [hw6])
  refine ⟨I0.ws, I0.pre, I0.J, I0.hj, I0.val, Keep.refl _ _ _ _ _, ?_, Rest.refl _ _⟩
  cases qo with
  | none => trivial
  | some q =>
    obtain ⟨hqN, hqr, -, -, hqn, -⟩ := hq
    obtain gq := h.fit64 hqN
    simp only [S] at gq
    simp only [QV, QZ] at hq0 ⊢
    obtain lt : num s.mem B w a / 2 ^ (32 * (jStart top w + 1)) < M := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      refine Nat.lt_of_lt_of_le hXt ?_
      rw [show 32 * (jStart top w + w / 2) = 32 * (w / 2 - 1) + 32 * (jStart top w + 1) by omega_using [hw6], Nat.pow_add]
      exact Nat.mul_le_mul_right _ hMlo
    rw [Nat.div_eq_of_lt lt, Nat.zero_mul]
    change num x0.mem B w q = 0
    rw [K.num (by simp; exact ⟨Ne.symm hqr, Ne.symm hqn⟩) (by decide) gq]; exact hq0

/-- `divW a r m t nm u top qo`: `[r] := [a] mod M` for `M = [m]` of `w / 2` words, its top word
not zero, through `[t]`, `[nm]` and `[u]`, with `[0]` zero; word `w` of `[r]` zero; and for
`qo = some q`, `[q] := ⌊[a] / M⌋` from a zero `[q]`. -/
theorem divWG_ok {s : State} {B : BitVec 32} {Z w N a r m t nm u : Nat} (h : Ws s B Z w N) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hra : r ≠ a)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r)
    (htn : t ≠ nm) (hnu : nm ≠ u) (hnm' : nm ≠ m) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hn0 : nm ≠ 0)
    (hw6 : 6 ≤ w) (h16 : slot s.mem B 16 = w) {M : Nat} (hM : num s.mem B w m = M)
    (hMl : M < 2 ^ (32 * (w / 2))) (hT0 : 0 < w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)))
    (hz : num s.mem B w 0 = 0) {top : Option Nat} (htop : TopOk top w (num s.mem B w a))
    {qo : Option Nat} (hq : QArr N r m t nm u qo) (hq0 : QZ s.mem B w qo) :
    WP isa (divW a r m t nm u top qo) s fun v => Ws v B Z w N ∧ num v.mem B w r = num s.mem B w a % M ∧
      w32 v.mem (State.addr B) (arr w r + 4 * w) = 0 ∧ Keep B w ([r, t, u, nm] ++ qList qo) divSlots s.mem v.mem ∧
      QV B w (num s.mem B w a) M 0 v.mem qo ∧ Rest divRegs s v := by
  have := h.wle
  obtain gm := h.fit64 hm
  obtain g0 := h.fit64 (j := 0) (by omega_using [ha])
  obtain gn := h.fit64 hnm
  simp only [S] at gm g0 gn
  obtain hM0 : 0 < M := by
    rw [← hM]; simp only [num]
    rw [show w = (w / 2 - 1) + 1 + (w - w / 2) by omega_using [hw6], val32_append, val32_succ]
    have := Nat.mul_le_mul_left (2 ^ (32 * (w / 2 - 1))) hT0
    have := Nat.two_pow_pos (32 * (w / 2 - 1))
    obtain e : w / 2 - 1 + 1 + (w - w / 2) = w := by omega_using [hw6]
    rw [e] at *
    omega_arith
  rw [divW]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  refine WP.mono (prepQ_ok t u h ha hr hm hnm hN hra hmr hnm' hnr hr0 hn0 hw6 h16 hM hMl hT0 hz htop hq hq0)
    fun x0 ⟨⟨z0, I0q⟩, K, R⟩ => ?_
  rw [WP.seq_iff]
  obtain hj1 := (htop.facts (by simp only [num]; exact val32_lt _ _ _ _) (by omega_using [hw6])).1
  refine WP.mono (loop_ok I0q hj1 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0
    (by omega_using [hw6]) hq) fun x1 I1 => ?_
  refine WP.mono (stepD_ok I1 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 (by omega_using [hw6]) hq)
    fun x2 ⟨W2, _, _, V2, K2, Q2, R2⟩ => ?_
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.div_one, Nat.one_mul, Nat.zero_add] at V2
  rw [val32_succ] at V2
  obtain hlt := val32_lt x2.mem (State.addr B) (arr w r) w
  obtain hXM : num s.mem B w a % M < 2 ^ (32 * w) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hM0) (Nat.le_of_lt (Nat.lt_of_lt_of_le hMl
      (Nat.pow_le_pow_right (by decide) (by omega_using []))))
  generalize 2 ^ (32 * w) = P at hlt hXM V2
  obtain hw0 : w32 x2.mem (State.addr B) (arr w r + 4 * w) = 0 := by
    rcases Nat.eq_zero_or_pos (w32 x2.mem (State.addr B) (arr w r + 4 * w)) with e | e
    · exact e
    · have := Nat.le_mul_of_pos_right P e; omega_using [hXM, V2, this]
  refine ⟨W2, ?_, hw0, ?_, Q2, ?_⟩
  · simp only [num]; rw [hw0, Nat.mul_zero, Nat.add_zero] at V2; exact V2
  · refine (K.mono (js' := [r, t, u, nm] ++ qList qo) (fun j hj => List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega_using [hr, ht, hnm, hu, hra, hrt, hru, htu, hmr, hmt, hmu, hnr, htn, hnu, hnm', hr0, ht0, hu0, hn0, hj]))).trans
      (K2.mono (fun j hj => ?_))
    rcases List.mem_append.mp hj with hj | hj
    · exact List.mem_append_left _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega_using [hr, ht, hnm, hu, hra, hrt, hru, htu, hmr, hmt, hmu, hnr, htn, hnu, hnm', hr0, ht0, hu0, hn0, hj])
    · exact List.mem_append_right _ hj
  · exact R.trans R2

/-- `divW a r m t nm u`: `[r] := [a] mod M` for `M = [m]` of `w / 2` words, its top word not
zero, through `[t]`, `[nm]` and `[u]`, with `[0]` zero; word `w` of `[r]` zero. -/
theorem divW_ok {s : State} {B : BitVec 32} {Z w N a r m t nm u : Nat} (h : Ws s B Z w N) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hra : r ≠ a)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r)
    (htn : t ≠ nm) (hnu : nm ≠ u) (hnm' : nm ≠ m) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hn0 : nm ≠ 0)
    (hw6 : 6 ≤ w) (h16 : slot s.mem B 16 = w) {M : Nat} (hM : num s.mem B w m = M)
    (hMl : M < 2 ^ (32 * (w / 2))) (hT0 : 0 < w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)))
    (hz : num s.mem B w 0 = 0) {top : Option Nat} (htop : TopOk top w (num s.mem B w a) := by trivial) :
    WP isa (divW a r m t nm u top) s fun v => Ws v B Z w N ∧ num v.mem B w r = num s.mem B w a % M ∧
      w32 v.mem (State.addr B) (arr w r + 4 * w) = 0 ∧ Keep B w [r, t, u, nm] divSlots s.mem v.mem ∧
      Rest divRegs s v :=
  WP.mono (divWG_ok h ha hr hm ht hnm hu hN hra hrt hru htu hmr hmt hmu hnr htn hnu hnm' hr0 ht0 hu0 hn0 hw6 h16
    hM hMl hT0 hz htop (qo := none) trivial trivial) fun _ ⟨W, V, Z', K, _, R⟩ =>
      ⟨W, V, Z', K.mono (by simp [qList]), R⟩



end VG.Proof.Rsa.Arm.KeyDiv
