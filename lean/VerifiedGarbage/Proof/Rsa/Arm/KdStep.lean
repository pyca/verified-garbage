module

public import VerifiedGarbage.Proof.Rsa.Arm.KdEst
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.MaskRow
import VerifiedGarbage.Proof.Framework.Omega

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
  omega

theorem dw_val {w : Nat} (hw : w ≤ 1024) : BitVec.ofNat 32 w >>> 1 = BitVec.ofNat 32 (w / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The registers of a step's parts but `r7`–`r9`, which they put back. -/
abbrev divRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr]

/-- Put back `r7`–`r9` in a `Rest` over every register. -/
theorem rest_back {s t : State} {B : BitVec 32} {Z w N : Nat} {ws : List Reg} (h : Ws s B Z w N)
    (ht : Ws t B Z w N) (r : Rest ws s t) (hws : ∀ x ∈ ws, x ∈ divRegs ++ ([.r7, .r8, .r9] : List Reg) := by decide) :
    Rest divRegs s t := by
  have K := r.mono hws
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
  have fq := h.arr_fit hq
  simp only [S] at fq
  have hz' := h.hdr_le
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  simp only [digit, List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok h (r := .r2) (by decide) (j := q) (by omega) fun s1 p1 r1 m1 h1' => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  have h2 : Ws s2 B Z w N := h1'.of_upd u2 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h2 (d := sQ) (by decide) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h3 (d := sC) (by decide) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N := h3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
  have h5 : Ws s5 B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  have a5 : State.addr (s5.gpr .r2 + BitVec.ofNat 32 0) = off (State.addr B) (arr w q + 4 * j) := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, dpVal, p1,
      r1.gpr _ (by decide), h1, BitVec.add_zero, add_ofNat_assoc]
    exact h.addr (by omega)
  have w5 : InRegions s5.wr (off (State.addr B) (arr w q + 4 * j)) 4 := by
    rw [u5.wr, u4.wr, u3.wr, u2.wr, r1.wr]; exact h.write (by omega)
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
  refine Outs.val32 K (fun x hx => ?_) (by omega)
  simp only [ranges, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (ha y hy); simp only [S] at this hhi ⊢; omega
  · have := hd d hd'; have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w a := Nat.le_add_right _ _; dsimp only; omega

/-- The digit a step writes, `q̂` less the borrow of `Y - q̂ M`: `⌊Y / M⌋`. -/
theorem digit_math {W Y M qh U b : Nat} (hM0 : 0 < M) (hge : Y / M ≤ qh)
    (hle : qh ≤ Y / M + 1) (hU : U < W) (hb : b ≤ 1) (h1 : U + qh * M = Y + W * b) : b ≤ qh ∧ qh - b = Y / M := by
  have hy := Nat.div_add_mod Y M
  have hr := Nat.mod_lt Y hM0
  generalize Y / M = Q at hge hle hy
  generalize Y % M = R at hy hr
  rw [Nat.mul_comm M Q] at hy
  rcases (show qh = Q ∨ qh = Q + 1 by omega) with rfl | rfl
  · rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · omega
    · rw [Nat.mul_one] at h1; omega
  · rw [Nat.add_mul, Nat.one_mul] at h1
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · rw [Nat.mul_zero] at h1; omega
    · omega

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
  have hN := Nat.two_pow_pos (32 * n)
  have eM : (2 : Nat) ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [Nat.mul_add, Nat.pow_add, Nat.mul_one]
  have hd : Y / 2 ^ (32 * n) < 2 ^ 32 := by rw [Nat.div_lt_iff_lt_mul hN, Nat.mul_comm, ← eM]; exact hY
  simp only [msV, msTop]
  rw [Nat.add_mod_mod, ← Nat.add_assoc (2 ^ 32 - q), top_val32 hN, ← eM, Nat.mod_eq_of_lt hd]
  have hr := Nat.div_add_mod Y (2 ^ (32 * n))
  have qm : q * M ≤ q * 2 ^ (32 * n) := Nat.mul_le_mul_left _ hM
  have e3 : q * 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 1)) := by rw [eM, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.le_of_lt hq)
  have key : Y % 2 ^ (32 * n) + q * (2 ^ (32 * n) - M) + 2 ^ (32 * n) * (2 ^ 32 - q + Y / 2 ^ (32 * n)) =
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
  have hW : 0 < W := by omega
  refine ⟨?_, hU ▸ Nat.mod_lt _ hW⟩
  split
  · rw [hU, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [hU, show Y + W - P = (Y - P) + W by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega

/-- The sign of `U`: its top bit, for `|Y - P|` below `W / 2`. -/
theorem sub_sign {W Y P U : Nat} (hU : U + P = Y + W * (if Y < P then 1 else 0)) (hUW : U < W) (h2 : 2 ∣ W)
    (hlo : P ≤ Y → Y - P < W / 2) (hhi : Y < P → P - Y ≤ W / 2) :
    U / (W / 2) = if Y < P then 1 else 0 := by
  have hW : 0 < W / 2 := by have := hUW; omega
  split
  · rename_i h; simp only [h, ↓reduceIte, Nat.mul_one] at hU
    have := hhi h
    refine Nat.le_antisymm ?_ ((Nat.le_div_iff_mul_le hW).mpr (by omega))
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hW).mpr (by omega))
  · rename_i h; simp only [h, ↓reduceIte, Nat.mul_zero, Nat.add_zero] at hU
    exact Nat.div_eq_of_lt (by have := hlo (by omega); omega)

/-- A step's arithmetic: `U = Y - q̂ M` with its borrow `b`, then `M` added back for the borrow, is
`Y mod M`, for `⌊Y / M⌋ ≤ q̂ ≤ ⌊Y / M⌋ + 1`. -/
theorem step_math {W Y M qh U b : Nat} (hM0 : 0 < M) (hMW : M ≤ W) (hge : Y / M ≤ qh) (hle : qh ≤ Y / M + 1)
    (hU : U < W)
    (hb : b ≤ 1) (h1 : U + qh * M = Y + W * b) : (U + b * M) % W = Y % M := by
  have hy : Y / M * M + Y % M = Y := by rw [Nat.mul_comm]; exact Nat.div_add_mod Y M
  have hr := Nat.mod_lt Y hM0
  have hq : qh = Y / M ∨ qh = Y / M + 1 := by omega
  generalize Y / M = Q at hy hq
  generalize Y % M = R at hy hr ⊢
  rcases hq with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
    simp only [Nat.add_mul, Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h1 ⊢
  · rw [Nat.mod_eq_of_lt hU]; omega
  · omega
  · omega
  · rw [show U + M = R + W by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- A change within a range of the frame. -/
theorem Outs.of_in {base : Addr} {o n o' n' : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : Outside base o n m m') (hr : (o', n') ∈ rs) (h1 : o' ≤ o) (h2 : o + n ≤ o' + n') : Outs base rs m m' :=
  fun x hx => h x (by have := hx _ hr; dsimp only at this; omega)

/-- The window (`n + 1` words) split at its top word. -/
theorem win_split {m : Mem} {A : Addr} {o n Y : Nat} (hY : val32 m A o (n + 1) = Y) :
    val32 m A o n = Y % 2 ^ (32 * n) ∧ w32 m A (o + 4 * n) = Y / 2 ^ (32 * n) := by
  rw [val32_succ] at hY
  have l := val32_lt m A o n
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
  have fr := h.arr_fit hr
  have fn := h.arr_fit hnm
  have dn := arr_disj (w := w) hrn
  have hz' := h.hdr_le
  have r160 : 160 ≤ arr w r := Nat.le_add_right _ _
  simp only [S] at fr fn dn
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  generalize eY : val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y
  generalize eL : val32 s.mem (State.addr B) (arr w nm) (w / 2) = L
  generalize eq : slot s.mem B sQ = q
  have ql : q < 2 ^ 32 := eq ▸ BitVec.isLt _
  obtain ⟨yLo, yHi⟩ := win_split eY
  rw [mulSubW]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  -- the window's offset
  refine ptr_ok h (r := .r0) (by decide) (j := r) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_ldrSlot h1 (d := sJ) (by decide) fun s2 U2 => WP.block_nil ?_
  have h2 : Ws s2 B Z w N := h1.of_upd U2 (by decide) (by decide) (by decide)
  have q1 : s2.gpr .r1 = BitVec.ofNat 32 (4 * j) := by rw [U2.gpr, m1, ← hJ]; exact (ofNat_toNat32 _).symm
  have q0 : s2.gpr .r0 = B + BitVec.ofNat 32 (arr w r) := by rw [U2.other _ (by decide), p1]
  rw [WP.seq_iff]
  simp only [List.cons_append, List.nil_append]
  -- the row's registers
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := h2.of_upd u3 (by decide) (by decide) (by decide)
  have p3 : s3.gpr .r0 = B + BitVec.ofNat 32 (arr w r + 4 * j) := by
    rw [u3.gpr, dpVal, q0, q1, add_ofNat_assoc]
  refine ptr_ok h3 (r := .r12) (by decide) (j := nm) (by omega) fun s4 p4 r4 m4 h4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have h5 : Ws s5 B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h5 (d := sQ) (by decide) fun s6 u6 => ?_
  have h6 : Ws s6 B Z w N := h5.of_upd u6 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun u u7 => WP.block_nil ?_
  have hu : Ws u B Z w N := h6.of_upd u7 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u7.mem.trans (u6.mem.trans (u5.mem.trans (m4.trans (u3.mem.trans (U2.mem.trans m1)))))
  have restU : Rest [.r0, .r1, .r12, .lr, .r11] s u :=
    ((r1.mono (by simp)).trans ((U2.rest (by simp)).trans (u3.rest (by simp)))).trans
      ((r4.mono (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest (by simp)))))
  have rc : RowCtx u B Z (arr w r + 4 * j) (arr w nm) (w / 2) :=
    ⟨h.nowrap, by omega, by omega, by omega, by rw [restU.wr]; exact h.writable⟩
  have x1 : (u.gpr .r1).toNat = q := by
    rw [u7.other _ (by decide), u6.gpr, u5.mem, m4, u3.mem, U2.mem, m1, ← eq]
  have x11 : (u.gpr .r11).toNat = 0 := by rw [u7.gpr]; rfl
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12, .lr]
    (row_ok u rc (by omega) (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      r4.gpr _ (by decide), p3]) (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), p4])
      (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, h4.r9, dw_val (by omega)]))
    (by decide)) fun v ⟨inv, kv⟩ => ?_
  have h8 : v.gpr .r8 = B := by rw [kv.gpr _ (by decide), hu.r8]
  have vv := inv.value
  rw [x1, x11, mu, yLo, eL, Nat.add_zero] at vv
  have vl := val32_lt v.mem (State.addr B) (arr w r + 4 * j) (w / 2)
  have carry : (v.gpr .r11).toNat = (Y % 2 ^ (32 * (w / 2)) + q * L) / 2 ^ (32 * (w / 2)) := by
    rw [← vv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt vl, Nat.zero_add]
  have low : val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2) =
      (Y % 2 ^ (32 * (w / 2)) + q * L) % 2 ^ (32 * (w / 2)) := by
    rw [← vv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt vl]
  have top0 : w32 v.mem (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) = Y / 2 ^ (32 * (w / 2)) := by
    rw [inv.outside.w32 (by omega) (by omega), mu, yHi]
  have r1v : v.gpr .r1 = BitVec.ofNat 32 q := by
    rw [inv.rest.gpr .r1 (by decide)]; apply BitVec.eq_of_toNat_eq; rw [x1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql]
  -- the top word and the sign
  have aT : State.addr (v.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) := by
    rw [inv.outPtr, BitVec.add_zero]; exact h.addr (by omega)
  refine wp_ldr (by decide) aT (by rw [inv.rest.rd, inv.rest.wr, restU.rd, restU.wr]; exact h.read (by omega))
    fun v1 w1 => ?_
  refine wp_dp (op2_reg _ _) fun v2 w2 => ?_
  refine wp_dp (op2_reg _ _) fun v3 w3 => ?_
  have a3 : State.addr (v3.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) := by
    rw [w3.other _ (by decide), w2.other _ (by decide), w1.other _ (by decide)]; exact aT
  refine wp_str (by decide) a3 (by rw [w3.wr, w2.wr, w1.wr, inv.rest.wr, restU.wr]; exact h.write (by omega))
    fun v4 w4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun v5 w5 => ?_
  have aC : State.addr (v5.gpr .r8 + BitVec.ofNat 32 sC) = off (State.addr B) sC := by
    rw [w5.other _ (by decide), w4.gpr, w3.other _ (by decide), w2.other _ (by decide), w1.other _ (by decide), h8]
    exact h.addr (by simp only [sC]; omega)
  have wC : InRegions v5.wr (off (State.addr B) sC) 4 := by
    rw [w5.wr, w4.wr, w3.wr, w2.wr, w1.wr, inv.rest.wr, restU.wr]; exact h.write (by simp only [sC]; omega)
  refine wp_str (by decide) aC wC fun v6 w6 => ?_
  -- the values
  have yt : Y / 2 ^ (32 * (w / 2)) % 2 ^ 32 = Y / 2 ^ (32 * (w / 2)) :=
    Nat.mod_eq_of_lt (by rw [← yHi]; exact BitVec.isLt _)
  have tv : (v3.gpr .r2).toNat = msTop (w / 2) Y L q := by
    rw [w3.gpr, dpVal, w2.gpr, dpVal, w2.other .r1 (by decide), w1.other .r1 (by decide),
      w1.other .r11 (by decide), w1.gpr, r1v, BitVec.toNat_sub, BitVec.toNat_add, carry,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql,
      show (v.mem.readW (off (State.addr B) (arr w r + 4 * j + 4 * (w / 2))) 32).toNat =
        w32 v.mem (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) from rfl, top0]
    simp only [msTop, yt]
  have sv : (v5.gpr .r2).toNat = msTop (w / 2) Y L q / 2 ^ 31 := by
    rw [w5.gpr, w4.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, tv]
  have m6 : v6.mem = (v.mem.writeW (off (State.addr B) (arr w r + 4 * j + 4 * (w / 2))) (v3.gpr .r2)).writeW
      (off (State.addr B) sC) (v5.gpr .r2) := by
    rw [w6.mem, w5.mem, w4.mem, w3.mem, w2.mem, w1.mem]
  refine kctx_ok (h.m.of (by rw [w6.wr, w5.wr, w4.wr, w3.wr, w2.wr, w1.wr, inv.rest.wr, restU.wr]))
    (by rw [w6.gpr, w5.other _ (by decide), w4.gpr, w3.other _ (by decide), w2.other _ (by decide),
      w1.other _ (by decide), h8]) (by
      simp only [slot]
      rw [m6, w32_write_ne hA (by simp only [sC]; omega) (by omega) (by simp only [sC]; omega),
        w32_write_ne hA (by omega) (by omega) (by omega), inv.outside.w32 (by omega) (by omega), mu]
      exact h16) h.wpos this
    fun v7 h7 R7 m7 => WP.block_nil ⟨h7, ?_, ?_, ?_, ?_⟩
  · rw [m7, m6, ← mu]
    refine ((Outs.of_in (o' := arr w r + 4 * j) (n' := 4 * (w / 2 + 1)) inv.outside (by simp) (Nat.le_refl _) (by omega)).trans
      (Outs.of_in (o' := arr w r + 4 * j) (n' := 4 * (w / 2 + 1)) (writeW32_outside _ _ _ (by omega)) (by simp) (by omega) (by omega))).trans
      (Outs.of_outside (writeW32_outside _ _ _ (by simp only [sC]; omega)) (by simp))
  · rw [m7, m6, val32_succ, w32_write_ne hA (by simp only [sC]; omega) (by omega) (by simp only [sC]; omega),
      w32_write_self, tv, Outside.val32 (writeW32_outside _ _ _ (by simp only [sC]; omega))
      (Or.inr (by simp only [sC]; omega)) (by omega),
      Outside.val32 (writeW32_outside _ _ _ (by omega)) (Or.inl (by omega)) (by omega), low]
  · simp only [slot]; rw [m7, m6, w32_write_self, sv]
  · exact rest_back h h7 (ws := divRegs ++ [.r7, .r8, .r9]) ((((restU.mono (by decide)).trans
      (kv.mono (by decide))).trans ((w1.rest (by simp)).trans ((w2.rest (by simp)).trans ((w3.rest (by simp)).trans
      ((w4.rest _).trans ((w5.rest (by simp)).trans (w6.rest _))))))).trans (R7.mono (by decide))) (by decide)

/-- A carry into the top word: `lo' + β^n c' = X`, then the top word `t + c'`, is `X + β^n t` modulo
`β^(n+1)`. -/
theorem add_top {n lo' c' X t : Nat} (hl : lo' < 2 ^ (32 * n)) (h : lo' + 2 ^ (32 * n) * c' = X) :
    lo' + 2 ^ (32 * n) * ((t + c') % 2 ^ 32) = (X + 2 ^ (32 * n) * t) % 2 ^ (32 * (n + 1)) := by
  have hN := Nat.two_pow_pos (32 * n)
  have e1 : X % 2 ^ (32 * n) = lo' := by rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have e2 : X / 2 ^ (32 * n) = c' := by
    rw [← h, Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hl, Nat.zero_add]
  rw [show 32 * (n + 1) = 32 * n + 32 by omega, Nat.pow_add, ← top_val32 hN, e1, e2]

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
  have fr := h.arr_fit hr
  have fm := h.arr_fit hm
  have dm := arr_disj (w := w) hrm
  have hz' := h.hdr_le
  have r160 : 160 ≤ arr w r := Nat.le_add_right _ _
  simp only [S] at fr fm dm
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  generalize ec : slot s.mem B sC = c at hc
  rw [WP.seq_iff]
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  have hs1 : Ws s1 B Z w N := h.of_upd u1 (by decide) (by decide) (by decide)
  have p1 : s1.gpr .r0 = B + BitVec.ofNat 32 (arr w r + 4 * j) := by rw [u1.gpr, dpVal, h0, h1, add_ofNat_assoc]
  refine ptr_ok hs1 (r := .r12) (by decide) (j := m) (by omega) fun s2 p2 r2 m2 h2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h3 (d := sC) (by decide) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N := h3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  have h5 : Ws s5 B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  have h6 : Ws s6 B Z w N := h5.of_upd u6 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun u u7 => WP.block_nil ?_
  have hu : Ws u B Z w N := h6.of_upd u7 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u7.mem.trans (u6.mem.trans (u5.mem.trans (u4.mem.trans (u3.mem.trans (m2.trans u1.mem)))))
  have restU : Rest [.r0, .r12, .lr, .r1, .r2, .r11] s u :=
    ((u1.rest (by simp)).trans (r2.mono (by simp))).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest (by simp))))))
  have rc : RowCtx u B Z (arr w r + 4 * j) (arr w m) (w / 2) :=
    ⟨h.nowrap, by omega, by omega, by omega, by rw [restU.wr]; exact h.writable⟩
  have rC : s4.gpr .r1 = BitVec.ofNat 32 c := by
    rw [u4.gpr, u3.mem, m2, u1.mem, ← ec]; exact (ofNat_toNat32 _).symm
  have mk : u.gpr .r1 = 0 - BitVec.ofNat 32 c := by
    rw [u7.other _ (by decide), u6.gpr, dpVal, u5.gpr, u5.other _ (by decide), rC]
  have mk' : u.gpr .r1 = 0 ∨ u.gpr .r1 = BitVec.allOnes 32 := by
    rw [mk]; rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> decide
  have mc : (u.gpr .r1).toNat / (2 ^ 32 - 1) = c := by
    rw [mk]; rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> decide
  rw [WP.seq_iff]
  refine WP.mono (maskRow_ok u rc (by omega)
    (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), r2.gpr _ (by decide), p1])
    (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), p2])
    (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.gpr, h2.r9, dw_val (by omega)]) mk') fun v ⟨vo, _, vout, _, vval, vr⟩ => ?_
  have hv : Ws v B Z w N := hu.rest vr
  have aT : State.addr (v.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) := by
    rw [vo, BitVec.add_zero]; exact h.addr (by omega)
  refine wp_ldr (by decide) aT (by rw [vr.rd, vr.wr, restU.rd, restU.wr]; exact h.read (by omega))
    fun v1 w1 => ?_
  refine wp_dp (op2_reg _ _) fun v2 w2 => ?_
  have a2 : State.addr (v2.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) := by
    rw [w2.other _ (by decide), w1.other _ (by decide)]; exact aT
  refine wp_str (by decide) a2 (by rw [w2.wr, w1.wr, vr.wr, restU.wr]; exact h.write (by omega)) fun v3 w3 => ?_
  have hv3 : Ws v3 B Z w N :=
    ((hv.of_upd w1 (by decide) (by decide) (by decide)).of_upd w2 (by decide) (by decide) (by decide)).of_mupd w3
  refine WP.block_nil ⟨hv3, ?_, ?_, ?_⟩
  · rw [w3.mem, w2.mem, w1.mem, ← mu]
    intro x hx
    rw [writeW32_outside _ _ _ (by omega) x (by omega), vout x (by omega)]
  · have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
    have vl := val32_lt v.mem (State.addr B) (arr w r + 4 * j) (w / 2)
    have x11 : (u.gpr .r11).toNat = 0 := by rw [u7.gpr]; rfl
    rw [mu, mc, x11, Nat.add_zero] at vval
    rw [w3.mem, val32_succ, w32_write_self, w2.gpr, dpVal, w1.gpr, w1.other .r11 (by decide), BitVec.toNat_add,
      show (v.mem.readW (off (State.addr B) (arr w r + 4 * j + 4 * (w / 2))) 32).toNat =
        w32 v.mem (State.addr B) (arr w r + 4 * j + 4 * (w / 2)) from rfl,
      Outside.val32 (writeW32_outside _ _ _ (by omega)) (Or.inl (by omega)) (by omega), w2.mem, w1.mem,
      val32_succ s.mem, vout.w32 (by omega) (by omega), mu,
      add_top vl (X := val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2) +
        c * val32 s.mem (State.addr B) (arr w m) (w / 2)) vval]
    congr 1; omega
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
  refine ptr_ok h (r := .r0) (by decide) (j := r) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_ldrSlot h1 (d := sJ) (by decide) fun s2 U2 => WP.block_nil ?_
  have h2 : Ws s2 B Z w N := h1.of_upd U2 (by decide) (by decide) (by decide)
  have m2 : s2.mem = s.mem := U2.mem.trans m1
  have q1 : s2.gpr .r1 = BitVec.ofNat 32 (4 * j) := by rw [U2.gpr, m1, ← hJ]; exact (ofNat_toNat32 _).symm
  have q0 : s2.gpr .r0 = B + BitVec.ofNat 32 (arr w r) := by rw [U2.other _ (by decide), p1]
  have R2 : Rest divRegs s s2 := (r1.mono (by decide)).trans (U2.rest (by decide))
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
    have fq := h.arr_fit hqN
    have fr := h.arr_fit hr
    have fm := h.arr_fit hm
    have dqr := arr_disj (w := w) hqr
    have dqm := arr_disj (w := w) hqm
    have q160 : 160 ≤ arr w q := Nat.le_add_right _ _
    have hz' := h.hdr_le
    simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
    simp only [S] at fq fr fm dqr dqm
    simp only [digitOf, List.append_assoc]
    rw [WP.seq_iff]
    refine digit_ok h2 hqN hN (by omega) q1 fun x hx rx mx => ?_
    have ox : Outside (State.addr B) (arr w q + 4 * j) 4 s2.mem x.mem := by
      rw [mx]; exact writeW32_outside _ _ _ (by omega)
    have tx := addBackT_ok hx hr hm hrm hN hdw hj (by rw [rx.gpr _ (by decide), q0]) (by rw [rx.gpr _ (by decide), q1])
      (by simp only [slot] at hc ⊢; rwa [ox.w32 (by simp only [sC]; omega) (by simp only [sC]; omega)])
    rw [WP.seq_iff] at tx
    refine WP.mono tx fun y hy => WP.mono hy fun v ⟨W, O, V, R⟩ => ⟨W, ?_, ?_, ?_, ?_⟩
    · exact (Outs.of_outside ox (by simp [qRanges])).trans (Outs.of_outside O (by simp))
    · rwa [ox.val32 (by omega) (by omega), ox.val32 (by omega) (by omega),
        show slot x.mem B sC = slot s2.mem B sC from ox.w32 (by simp only [sC]; omega) (by simp only [sC]; omega)] at V
    · show w32 v.mem (State.addr B) (arr w q + 4 * j) = _
      rw [O.w32 (by omega) (by omega), mx, w32_write_self]
    · exact R2.trans ((rx.mono (by decide)).trans R)

/-- A header word apart from every range that changed. -/
theorem Outs.slot {B : BitVec 32} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs (State.addr B) rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) : slot m' B d = slot m B d := by
  have e := Outs.val32 h (d := d) (k := 1) (by simpa using hd) (by omega)
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
  have fr := h.arr_fit hr
  have gr := h.fit64 hr
  have gm := h.fit64 hm
  have gn := h.fit64 hnm
  have hz' := h.hdr_le
  have r160 : 160 ≤ arr w r := Nat.le_add_right _ _
  simp only [S] at fr
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun e => by
    rw [e, Nat.zero_mul, Nat.zero_div] at hD
    have := Nat.mul_le_mul_right (2 ^ 32) hDn; omega
  have hMn : M ≤ 2 ^ (32 * (w / 2)) := by
    have : M ≤ M * 2 ^ z := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega
  have eW : (2 : Nat) ^ (32 * (w / 2 + 1)) = 2 ^ (32 * (w / 2)) * 2 ^ 32 := by
    rw [Nat.mul_add, Nat.pow_add, Nat.mul_one]
  have hMW : M ≤ 2 ^ (32 * (w / 2 + 1)) := by rw [eW]; exact Nat.le_trans hMn (Nat.le_mul_of_pos_right _ (by decide))
  -- `[nm]`'s low words: `β^dw - M`.
  have hL : val32 s.mem (State.addr B) (arr w nm) (w / 2) = 2 ^ (32 * (w / 2)) - M := by
    obtain ⟨lo, -⟩ := win_split hnm'
    rw [lo, eW, show 2 ^ (32 * (w / 2)) * 2 ^ 32 - M = (2 ^ (32 * (w / 2)) - M) + 2 ^ (32 * (w / 2)) * (2 ^ 32 - 1) by
      have : 2 ^ (32 * (w / 2)) * 2 ^ 32 = 2 ^ (32 * (w / 2)) * (2 ^ 32 - 1) + 2 ^ (32 * (w / 2)) := by
        rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by decide))]
      omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [step]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [wp_seq_blocks, show estA r ++ estB = estimate r by simp [estA, estB, estimate], WP.seq_iff,
    ← List.append_nil (estimate r)]
  refine estimate_ok h hr hN h16 hdw hJ hj hY hYM hz hP hMP hD hDn hV
    fun t1 q hq1 hge hle ql K1 W1 R1 => WP.block_nil ?_
  have J1 : slot t1.mem B sJ = 4 * j := by rw [K1.slot (by decide) (by decide)]; exact hJ
  have s16 : slot t1.mem B 16 = w := by rw [K1.slot (by decide) (by decide)]; exact h16
  have Y1 : val32 t1.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y := by
    rw [keep_val K1 (a := r) (by omega) (by simp only [S]; omega) (by simp) (fit := gr)]; exact hY
  have L1 : val32 t1.mem (State.addr B) (arr w nm) (w / 2) = 2 ^ (32 * (w / 2)) - M := by
    rw [keep_val K1 (a := nm) (Nat.le_refl _) (by simp only [S]; omega) (by simp) (fit := gn)]; exact hL
  have M1 : val32 t1.mem (State.addr B) (arr w m) (w / 2) = M := by
    rw [keep_val K1 (a := m) (Nat.le_refl _) (by simp only [S]; omega) (by simp) (fit := gm)]; exact hM
  -- `U = Y - q̂ M` modulo `W`, its sign into `sC`.
  rw [WP.seq_iff]
  refine WP.mono (mulSubW_ok W1 hr hnm hrn hN s16 (by omega) J1 hj) fun t2 ⟨W2, O2, V2, C2, R2⟩ => ?_
  rw [Y1, L1, hq1] at V2 C2
  have hYW : Y < 2 ^ (32 * (w / 2 + 1)) := by
    rw [eW]; exact Nat.lt_of_lt_of_le hYM (Nat.mul_le_mul_right _ hMn)
  have hY' : Y / M * M + Y % M = Y := by rw [Nat.mul_comm]; exact Nat.div_add_mod Y M
  have hYr := Nat.mod_lt Y hM0
  have hqM : q * M ≤ Y + M := by
    have := Nat.mul_le_mul_right M hle; rw [Nat.add_mul, Nat.one_mul] at this; omega
  have U2 := msV_eq ql hMn hYW (by omega)
  obtain ⟨rel, hUW⟩ := sub_rel U2 hYW (by omega)
  have sgn := sub_sign rel hUW (by rw [eW]; exact Nat.dvd_trans (by decide : 2 ∣ 2 ^ 32) (Nat.dvd_mul_left _ _))
    (fun _ => by
      have : q * M ≥ Y / M * M := Nat.mul_le_mul_right M hge
      have : 2 ^ (32 * (w / 2)) ≤ 2 ^ (32 * (w / 2 + 1)) / 2 := by rw [eW]; omega
      omega)
    (fun _ => by
      have : 2 ^ (32 * (w / 2)) ≤ 2 ^ (32 * (w / 2 + 1)) / 2 := by rw [eW]; omega
      omega)
  have hb1 : (if Y < q * M then 1 else 0) ≤ 1 := by split <;> omega
  generalize (if Y < q * M then 1 else 0) = b at rel sgn hb1
  have C2' : slot t2.mem B sC = b := by
    rw [C2, ← sgn, ← msV_div, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 32 * (w / 2) + 31 = 32 * (w / 2 + 1) - 1 by omega,
      show 2 ^ (32 * (w / 2 + 1)) / 2 = 2 ^ (32 * (w / 2 + 1) - 1) by
        rw [show 32 * (w / 2 + 1) = (32 * (w / 2 + 1) - 1) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)];
        rfl]
  have hb : slot t2.mem B sC ≤ 1 := by rw [C2']; exact hb1
  have O2s : ∀ d, d + 4 ≤ 160 → d + 4 ≤ sC ∨ sC + 4 ≤ d → slot t2.mem B d = slot t1.mem B d := fun d hd hdC =>
    Outs.slot O2 (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inl (Nat.le_trans hd (Nat.le_trans r160 (Nat.le_add_right _ _)))
      · exact hdC) (by omega)
  have J2 : slot t2.mem B sJ = 4 * j := by rw [O2s _ (by decide) (by decide)]; exact J1
  have M2 : val32 t2.mem (State.addr B) (arr w m) (w / 2) = M := by
    rw [Outs.val32 O2 (fun x hx => by
      have dm := arr_disj (w := w) hrm
      simp only [S] at dm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · dsimp only; omega
      · have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w m := Nat.le_add_right _ _
        simp only [VG.Impl.Rsa.Arm.Keys.hdr] at this; exact Or.inr (Nat.le_trans (by decide) this))
      (by have := gm; simp only [S] at this; omega)]
    exact M1
  -- `M` added back under the sign, the digit.
  rw [WP.seq_iff]
  refine WP.mono (addBackW_ok W2 hr hm hrm hN (by omega) J2 hj hb hq) fun t3 ⟨W3, O3, V3, D3, R3⟩ => ?_
  rw [V2, M2] at V3
  have V := step_math hM0 hMW hge hle hUW hb1 rel
  have J3 : slot t3.mem B sJ = 4 * j := by
    rw [Outs.slot O3 (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (by simp only [sJ]; omega)
      · cases qo with
        | none => simp [qRanges] at hx
        | some qa =>
          simp only [qRanges, List.mem_singleton] at hx; subst hx
          have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w qa := Nat.le_add_right _ _
          simp only [VG.Impl.Rsa.Arm.Keys.hdr] at this
          exact Or.inl (by simp only [sJ]; omega)) (by simp only [sJ]; omega)]
    exact J2
  have aJ : State.addr (B + BitVec.ofNat 32 sJ) = off (State.addr B) sJ := h.addr (by simp only [sJ]; omega)
  have rJ : InRegions (t3.rd ++ t3.wr) (off (State.addr B) sJ) 4 := W3.read (by simp only [sJ]; omega)
  have wJ : InRegions t3.wr (off (State.addr B) sJ) 4 := W3.write (by simp only [sJ]; omega)
  have vJ : t3.mem.readW (off (State.addr B) sJ) 32 = BitVec.ofNat 32 (4 * j) := by
    rw [← J3]; exact (ofNat_toNat32 _).symm
  refine WP.mono (WP.keep [.r0] (Q := fun v =>
      v.mem = t3.mem.writeW (off (State.addr B) sJ) (BitVec.ofNat 32 (4 * j) - 4)) (by
    krun [W3.r8, aJ, rJ, wJ, vJ]) (by decide)) fun t4 ⟨m4, R4⟩ => ?_
  have win4 : val32 t4.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) =
      val32 t3.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) := by
    rw [m4]; exact Outside.val32 (writeW32_outside _ _ _ (by simp only [sJ]; omega)) (Or.inr (by simp only [sJ]; omega))
      (by omega)
  refine ⟨W3.of (by rw [R4.gpr _ (by decide)]) (by rw [R4.gpr _ (by decide)]) (by rw [R4.gpr _ (by decide)]) R4.wr,
    by rw [win4, V3, C2', V], by simp only [slot]; rw [m4, w32_write_self], ?_, ?_, ?_⟩
  · have F1 : Outs (State.addr B) (stepRanges w r t u j qo) s.mem t1.mem :=
      Outs.mono (K1.mono (js' := [t, u]) (ds' := [sMk, sQ, sU0, sU2, sC, sJ])) fun x hx => List.mem_append_left _ hx
    have F2 : Outs (State.addr B) (stepRanges w r t u j qo) t1.mem t2.mem := Outs.mono O2 fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _ (List.mem_append_right _ (by simp))
    have F3 : Outs (State.addr B) (stepRanges w r t u j qo) t2.mem t3.mem :=
      Outs.mono O3 fun x hx => List.mem_append_right _ hx
    have F4 : Outs (State.addr B) (stepRanges w r t u j qo) t3.mem t4.mem := by
      rw [m4]
      exact Outs.mono ((keep_write (B := B) (w := w) (js := [t, u]) (ds := [sMk, sQ, sU0, sU2, sC, sJ]) t3.mem _
        (by simp) (by simp only [sJ]; omega))) fun x hx => List.mem_append_left _ hx
    exact ((F1.trans F2).trans F3).trans F4
  · cases qo with
    | none => trivial
    | some qa =>
      obtain ⟨hqN, -⟩ := hq
      have fq := h.arr_fit hqN
      have q160 : 160 ≤ arr w qa := Nat.le_add_right _ _
      simp only [S] at fq
      simp only [QDig] at D3
      simp only [QOut]
      have sQ2 : slot t2.mem B sQ = q := by rw [O2s _ (by decide) (by decide)]; exact hq1
      obtain ⟨bq, dq⟩ := digit_math hM0 hge hle hUW hb1 rel
      rw [m4, w32_write_ne hA (by simp only [sJ]; omega) (by omega) (by simp only [sJ]; omega), D3, sQ2, C2',
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), dq]
  · exact (R1.mono (by decide)).trans ((R2.mono (by decide)).trans ((R3.mono (by decide)).trans (R4.mono (by decide))))

end VG.Proof.Rsa.Arm.KeyDiv
