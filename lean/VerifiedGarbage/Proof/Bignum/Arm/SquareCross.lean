module

import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.SquareState
public import VerifiedGarbage.Impl.Bignum.Arm.Square
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Bignum.Arm.SquareInit`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.SquareMath`, which only this module used -/

section

/-! # The arithmetic of ARMv7 Montgomery squaring

The square of `a = Σ a_i 2^(32 i)` is its words' squares at the even
positions plus twice the cross products `a_i a_j` (`i < j`), which the rows
`a_i a[i+1 …]` add once each. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont

/-- The first `k` rows of cross products: `Σ_{i<k} 2^(32 (2i+1)) a_i a[i+1 … n−1]`. -/
def sqCross (m : Mem) (base : Addr) (a n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sqCross m base a n k +
      2 ^ (32 * (2 * k + 1)) * (w32 m base (a + 4 * k) * val32 m base (a + 4 * (k + 1)) (n - 1 - k))

/-- The squares of the first `k` words, at the positions `2i`. -/
def diagSum (m : Mem) (base : Addr) (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => diagSum m base a k + 2 ^ (64 * k) * (w32 m base (a + 4 * k) * w32 m base (a + 4 * k))

theorem sq_split (m : Mem) (base : Addr) (a n : Nat) : ∀ k, k ≤ n →
    val32 m base a n * val32 m base a n = diagSum m base a k + 2 * sqCross m base a n k +
      2 ^ (64 * k) * (val32 m base (a + 4 * k) (n - k) * val32 m base (a + 4 * k) (n - k))
  | 0, _ => by simp only [diagSum, sqCross, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add, Nat.sub_zero]
  | k + 1, hk => by
    rw [sq_split m base a n k (by omega_using [hk])]
    obtain e : n - k = (n - 1 - k) + 1 := by omega_using [hk]
    rw [e, val32, show a + 4 * k + 4 = a + 4 * (k + 1) by omega_using [], show n - (k + 1) = n - 1 - k by omega_using []]
    simp only [diagSum, sqCross]
    obtain e1 : 2 ^ (32 * (2 * k + 1)) = 2 ^ (64 * k) * 2 ^ 32 := by
      rw [← Nat.pow_add]; congr 1 <;> omega_using []
    obtain e2 : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 32 * 2 ^ 32 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1 <;> omega
    rw [e1, e2]
    generalize w32 m base (a + 4 * k) = x
    generalize val32 m base (a + 4 * (k + 1)) (n - 1 - k) = y
    generalize 2 ^ (64 * k) = P
    generalize (2 : Nat) ^ 32 = W
    grind

theorem sq_eq (m : Mem) (base : Addr) (a n : Nat) :
    val32 m base a n * val32 m base a n = diagSum m base a n + 2 * sqCross m base a n n := by
  rw [sq_split m base a n n (Nat.le_refl _), Nat.sub_self]
  simp only [val32, Nat.mul_zero, Nat.add_zero]

/-- The last row is empty. -/
theorem sqCross_last (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) :
    sqCross m base a n n = sqCross m base a n (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_using [hn]⟩
  simp only [sqCross, Nat.add_sub_cancel, Nat.sub_self, val32, Nat.mul_zero, Nat.add_zero]

/-- Replacing the middle `j` words of `i + j + k`. -/
theorem val32_replace {m m' : Mem} {base : Addr} {d i j k : Nat}
    (lo : val32 m' base d i = val32 m base d i)
    (hi : val32 m' base (d + 4 * (i + j)) k = val32 m base (d + 4 * (i + j)) k) :
    val32 m' base d (i + j + k) + 2 ^ (32 * i) * val32 m base (d + 4 * i) j =
      val32 m base d (i + j + k) + 2 ^ (32 * i) * val32 m' base (d + 4 * i) j := by
  rw [val32_append m' base d (i + j) k, val32_append m base d (i + j) k, val32_append m' base d i j,
    val32_append m base d i j, lo, hi]
  grind

/-- The value after `n` reductions: below `2m` for an operand below `m < 2^(32 n)`. -/
theorem sq_red_bound {x M Q H R : Nat} (hx : x < M) (hM : M ≤ R) (hQ : Q < R)
    (h : R * H = x * x + Q * M) : H < 2 * M := by
  obtain h1 : x * x ≤ x * M := Nat.mul_le_mul_left _ (Nat.le_of_lt hx)
  obtain h2 : x * M < R * M := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le hx hM)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) hx)
  obtain h3 : Q * M ≤ R * M := Nat.mul_le_mul_right _ (Nat.le_of_lt hQ)
  obtain h4 : R * H < R * (2 * M) := by
    rw [h, Nat.mul_comm 2 M, ← Nat.mul_assoc, Nat.mul_two]
    omega_using [h1, h2, h3]
  exact Nat.lt_of_mul_lt_mul_left h4

end VG.Proof.Bignum.Arm

end

end


/-! # The square's metadata and its cleared product -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_mov op2_imm op2_reg op2_lsl dpVal)

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

/-- The workspace pointer, from `sp`. -/
theorem sqBase_ok (s : State) (h : SqEnv m0 base size out a mod M n inv s) (r : Reg) :
    WP isa (.block [.ldrSp r 0]) s fun t => t.gpr r = base ∧ t.mem = s.mem ∧ Rest [r] s t :=
  wp_loadStack (a := State.addr s.sp) (by decide) (by simp) h.stackRead fun t u => WP.block_nil
    ⟨u.gpr.trans h.savedNow, u.mem, u.rest (by simp)⟩

/-- The metadata's address, from the workspace at `sp`. -/
theorem sqAnchor_ok (s : State) (h : SqEnv m0 base size out a mod M n inv s) :
    WP isa sqAnchor s fun t => t.gpr .r0 = base + BitVec.ofNat 32 M ∧ t.mem = s.mem ∧
      Rest [.r0] s t := by
  have nowrap := h.nowrap
  have := h.header; have := h.fits
  rw [sqAnchor, WP.seq_iff]
  refine WP.mono (restoreBase_ok s h.stackRead h.savedNow) ?_
  rintro u ⟨p, mem, rest⟩
  obtain hu := h.of_mem mem rest
  refine wp_ldr (a := off (State.addr base) 80) (by decide) (by rw [p]; exact VG.Arm.addr_add (by omega_arith))
    (hu.read (by omega_arith)) fun t ut => WP.block_nil ?_
  exact ⟨ut.gpr.trans hu.metaNow, ut.mem.trans mem, rest.trans (ut.rest (by decide))⟩

end

/-- After `k` rows of cross products: `T` (`2n + 2` words at `M + 24`) holds
their sum, and its words from `k + n` are zero. -/
structure CrossInv (m0 : Mem) (base : BitVec 32) (size out a mod M n : Nat) (inv : BitVec 32)
    (k : Nat) (s : State) : Prop where
  env : SqEnv m0 base size out a mod M n inv s
  index : k + 1 ≤ n
  md : SqMeta s.mem base out a M n
  next : s.mem.readW (off (State.addr base) (M + 12)) 32 = base + BitVec.ofNat 32 (a + 4 * k)
  cnt : s.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 (n - 1 - k)
  tptr : s.mem.readW (off (State.addr base) (M + 20)) 32 = base + BitVec.ofNat 32 (M + 28 + 8 * k)
  value : val32 s.mem (State.addr base) (M + 24) (2 * n + 2) = sqCross m0 (State.addr base) a n k
  top : val32 s.mem (State.addr base) (M + 24 + 4 * (k + n)) (n + 2 - k) = 0

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqMeta_ok (s : State) (h : SqEnv m0 base size out a mod M n inv s)
    (p6 : s.gpr .r6 = base + BitVec.ofNat 32 M) (p7 : s.gpr .r7 = BitVec.ofNat 32 n)
    (p8 : s.gpr .r8 = base + BitVec.ofNat 32 a) (p10 : s.gpr .r10 = base + BitVec.ofNat 32 out) :
    WP isa (.block sqMeta) s fun t =>
      SqMeta t.mem base out a M n ∧
      t.mem.readW (off (State.addr base) (M + 12)) 32 = base + BitVec.ofNat 32 a ∧
      t.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 (n - 1) ∧
      t.mem.readW (off (State.addr base) (M + 20)) 32 = base + BitVec.ofNat 32 (M + 28) ∧
      Outside (State.addr base) M 24 s.mem t.mem ∧ Rest [.r1] s t := by
  have nowrap := h.nowrap
  have := h.header; have := h.fits; have := h.count
  have ws := h.workspace
  have e (d : Nat) (hd : d + 4 ≤ 24) {u : State} (hu : u.gpr .r6 = s.gpr .r6) :
      State.addr (u.gpr .r6 + BitVec.ofNat 32 d) = off (State.addr base) (M + d) :=
    sq_ea nowrap (hu.trans p6) (by omega_arith)
  have wr (d : Nat) (hd : d + 4 ≤ 24) {u : State} (hw : u.wr = s.wr) :
      InRegions u.wr (off (State.addr base) (M + d)) 4 := by
    rw [hw]; exact h.write (by omega_arith)
  unfold sqMeta
  refine wp_str (by decide) (by simpa only [Nat.add_zero] using e 0 (by decide) rfl)
    (by simpa only [Nat.add_zero] using wr 0 (by decide) rfl) fun s1 u1 => ?_
  refine wp_str (by decide) (e 4 (by decide) (by rw [u1.gpr])) (wr 4 (by decide) u1.wr) fun s2 u2 => ?_
  refine wp_str (by decide) (e 8 (by decide) (by rw [u2.gpr, u1.gpr]))
    (wr 8 (by decide) (by rw [u2.wr, u1.wr])) fun s3 u3 => ?_
  refine wp_str (by decide) (e 12 (by decide) (by rw [u3.gpr, u2.gpr, u1.gpr]))
    (wr 12 (by decide) (by rw [u3.wr, u2.wr, u1.wr])) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_str (by decide) (e 16 (by decide) (by rw [u5.other .r6 (by decide), u4.gpr, u3.gpr, u2.gpr, u1.gpr]))
    (wr 16 (by decide) (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])) fun s6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_str (by decide) (e 20 (by decide)
    (by rw [u7.other .r6 (by decide), u6.gpr, u5.other .r6 (by decide), u4.gpr, u3.gpr, u2.gpr, u1.gpr]))
    (wr 20 (by decide) (by rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])) fun t u8 => WP.block_nil ?_
  obtain g7 : s4.gpr .r7 = s.gpr .r7 := by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  obtain g6 : s6.gpr .r6 = s.gpr .r6 := by
    rw [u6.gpr, u5.other .r6 (by decide), u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  obtain v1 : s5.gpr .r1 = BitVec.ofNat 32 (n - 1) := by
    rw [u5.gpr, dpVal, g7, p7]
    change BitVec.ofNat 32 n - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
  obtain v2 : s7.gpr .r1 = base + BitVec.ofNat 32 (M + 28) := by
    rw [u7.gpr, dpVal, g6, p6]
    change base + BitVec.ofNat 32 M + BitVec.ofNat 32 28 = _
    rw [Offset.add_add]
  obtain m1 : s1.mem = s.mem.writeW (off (State.addr base) M) (BitVec.ofNat 32 n) := by rw [u1.mem, p7]
  obtain m2 : s2.mem = s1.mem.writeW (off (State.addr base) (M + 4)) (base + BitVec.ofNat 32 out) := by
    rw [u2.mem, u1.gpr, p10]
  obtain m3 : s3.mem = s2.mem.writeW (off (State.addr base) (M + 8)) (base + BitVec.ofNat 32 a) := by
    rw [u3.mem, u2.gpr, u1.gpr, p8]
  obtain m4 : s4.mem = s3.mem.writeW (off (State.addr base) (M + 12)) (base + BitVec.ofNat 32 a) := by
    rw [u4.mem, u3.gpr, u2.gpr, u1.gpr, p8]
  obtain m6 : s6.mem = s4.mem.writeW (off (State.addr base) (M + 16)) (BitVec.ofNat 32 (n - 1)) := by
    rw [u6.mem, u5.mem, v1]
  obtain m8 : t.mem = s6.mem.writeW (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (M + 28)) := by
    rw [u8.mem, u7.mem, v2]
  have o (d : Nat) (hd : d + 4 ≤ 24) (v : BitVec 32) (mem : Mem) :
      Outside (State.addr base) M 24 mem (mem.writeW (off (State.addr base) (M + d)) v) :=
    (writeW32_outside mem (State.addr base) v (by omega_arith)).mono (by omega_arith) (by omega_arith)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m8, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m6, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith),
      m4, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m3, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith),
      m2, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m1, rd_self]
  · rw [m8, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m6, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith),
      m4, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m3, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith),
      m2, rd_self]
  · rw [m8, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m6, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith),
      m4, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m3, rd_self]
  · rw [m8, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m6, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith),
      m4, rd_self]
  · rw [m8, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m6, rd_self]
  · rw [m8, rd_self]
  · have h0 : Outside (State.addr base) M 24 s.mem s1.mem := by
      rw [m1]; simpa only [Nat.add_zero] using o 0 (by decide) _ s.mem
    obtain h2 : Outside (State.addr base) M 24 s1.mem s2.mem := by rw [m2]; exact o 4 (by decide) _ _
    obtain h3 : Outside (State.addr base) M 24 s2.mem s3.mem := by rw [m3]; exact o 8 (by decide) _ _
    obtain h4 : Outside (State.addr base) M 24 s3.mem s4.mem := by rw [m4]; exact o 12 (by decide) _ _
    obtain h6 : Outside (State.addr base) M 24 s4.mem s6.mem := by rw [m6]; exact o 16 (by decide) _ _
    obtain h8 : Outside (State.addr base) M 24 s6.mem t.mem := by rw [m8]; exact o 20 (by decide) _ _
    exact h0.trans (h2.trans (h3.trans (h4.trans (h6.trans h8))))
  · exact (u1.rest _).trans ((u2.rest _).trans ((u3.rest _).trans ((u4.rest _).trans
      ((u5.rest (by decide)).trans ((u6.rest _).trans ((u7.rest (by decide)).trans (u8.rest _)))))))

theorem sqZeroArgs_ok (s : State) (h : SqEnv m0 base size out a mod M n inv s)
    (p6 : s.gpr .r6 = base + BitVec.ofNat 32 M) (p7 : s.gpr .r7 = BitVec.ofNat 32 n) :
    WP isa (.block sqZeroArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (M + 24) ∧ t.gpr .lr = BitVec.ofNat 32 (2 * n + 2) ∧
      t.gpr .r3 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r3, .lr] s t := by
  have nowrap := h.nowrap
  have := h.fits
  unfold sqZeroArgs
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u4 => WP.block_nil ?_
  refine ⟨?_, ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide), u1.gpr, dpVal, p6]
    change base + BitVec.ofNat 32 M + BitVec.ofNat 32 24 = _
    rw [Offset.add_add]
  · rw [u4.other .lr (by decide), u3.gpr, dpVal, u2.gpr, u1.other .r7 (by decide), p7,
      ofNat_shl (by omega_arith)]
    change BitVec.ofNat 32 (n * 2 ^ 1) + BitVec.ofNat 32 2 = _
    rw [BitVec.ofNat_add_ofNat, show n * 2 ^ 1 + 2 = 2 * n + 2 by omega_arith]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))

theorem sqInit_ok (s : State) (h : SqEnv m0 base size out a mod M n inv s)
    (p6 : s.gpr .r6 = base + BitVec.ofNat 32 M) (p7 : s.gpr .r7 = BitVec.ofNat 32 n)
    (p8 : s.gpr .r8 = base + BitVec.ofNat 32 a) (p10 : s.gpr .r10 = base + BitVec.ofNat 32 out) :
    WP isa sqInit s fun t => CrossInv m0 base size out a mod M n inv 0 t ∧ Rest roundClobbers s t := by
  have nowrap := h.nowrap
  have := h.fits; have := h.count
  rw [sqInit, WP.seq_iff]
  refine WP.mono (sqMeta_ok s h p6 p7 p8 p10) ?_
  rintro u ⟨md, next, cnt, tptr, outU, restU⟩
  obtain hu := h.next (Outs.of_outside (outU.mono (o' := M) (n' := 4 * (2 * n + 8)) (Nat.le_refl _) (by omega_arith)) (by simp)) restU
  rw [WP.seq_iff]
  refine WP.mono (sqZeroArgs_ok u hu ((restU.gpr .r6 (by decide)).trans p6)
    ((restU.gpr .r7 (by decide)).trans p7)) ?_
  rintro v ⟨p0, plr, p3, memV, restV⟩
  obtain hv := hu.of_mem memV restV
  obtain cv : ZeroCtx v base size (M + 24) (2 * n + 2) :=
    ⟨nowrap, by omega_arith, ⟨_, hv.workspace.writable, Region.contains_self _ _⟩⟩
  refine WP.mono (zero_ok v cv (by omega_arith) p0 plr p3) ?_
  intro t zt
  obtain outT : Outs (State.addr base) [(M, 4 * (2 * n + 8))] v.mem t.mem :=
    Outs.of_outside (zt.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith)) (by simp)
  obtain ht := hv.next outT zt.rest
  have kept (d : Nat) (hd : d + 4 ≤ 24) :
      t.mem.readW (off (State.addr base) (M + d)) 32 = u.mem.readW (off (State.addr base) (M + d)) 32 := by
    rw [← memV]
    exact outside_read32 zt.outside (by omega_arith) (by omega_arith)
  refine ⟨⟨ht, by omega_arith, md.congr fun d hd => kept d (by omega_arith), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kept 12 (by decide), next, Nat.mul_zero, Nat.add_zero]
  · rw [kept 16 (by decide), cnt, Nat.sub_zero]
  · rw [kept 20 (by decide), tptr, Nat.mul_zero, Nat.add_zero]
  · rw [zt.value]; rfl
  · have z := zt.value
    rw [show 2 * n + 2 = n + (n + 2) by omega_arith] at z
    simpa only [Nat.zero_add, Nat.sub_zero] using val32_zero_tail z
  · exact (restU.mono (by decide)).trans ((restV.mono (by decide)).trans
      (zt.rest.mono (by decide)))

end

end VG.Proof.Bignum.Arm

end

end

/-! # The square's rows of cross products -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_mov wp_subs op2_imm op2_reg dpVal ofNat_beq_zero)

/-- The head word of a zero number. -/
theorem val32_zero_head {m : Mem} {b : Addr} {d k : Nat} (h : val32 m b d (k + 1) = 0) :
    w32 m b d = 0 := by
  rw [val32] at h
  omega_using [h]

/-- The count of rows decremented, Z after the last. -/
theorem sqCount_ok (s : State) {base : BitVec 32} {size M c : Nat} (ws : Workspace s base size)
    (fit : M + 20 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hc : s.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 c) (h1 : 1 ≤ c)
    (h32 : c < 2 ^ 32) :
    WP isa (.block sqCount) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (M + 16)) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.lr] s t := by
  have nowrap := ws.nowrap
  unfold sqCount
  refine wp_ldr (by decide) (sq_ea nowrap p0 (by omega_using [fit])) (ws.read (by omega_using [fit])) fun s1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 hz => ?_
  refine wp_str_z (by decide) (sq_ea nowrap ((u2.other .r0 (by decide)).trans ((u1.other .r0 (by decide)).trans p0))
    (by omega_using [fit])) (by rw [u2.wr, u1.wr]; exact ws.write (by omega_using [fit])) fun t u3 z3 => WP.block_nil ?_
  obtain v : s2.gpr .lr = BitVec.ofNat 32 (c - 1) := by
    rw [u2.gpr, u1.gpr, hc]
    change BitVec.ofNat 32 c - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [h1])]
  refine ⟨?_, ?_, ?_⟩
  · rw [u3.mem, u2.mem, u1.mem, v]
  · rw [z3, hz, u1.gpr, hc]
    change (BitVec.ofNat 32 c - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [h1]), ofNat_beq_zero (by omega_using [h32])]
    simp only [show c - 1 = 0 ↔ c = 1 by omega_using [h1]]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest _))

theorem crossArgs_ok (s : State) {base : BitVec 32} {size M A C P : Nat} (ws : Workspace s base size)
    (fit : M + 24 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hn : s.mem.readW (off (State.addr base) (M + 12)) 32 = base + BitVec.ofNat 32 A)
    (hc : s.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 C)
    (ht : s.mem.readW (off (State.addr base) (M + 20)) 32 = base + BitVec.ofNat 32 P) :
    WP isa (.block crossArgs) s fun t =>
      t.gpr .r2 = base + BitVec.ofNat 32 A ∧ t.gpr .r12 = base + BitVec.ofNat 32 (A + 4) ∧
      t.gpr .lr = BitVec.ofNat 32 C ∧ t.gpr .r0 = base + BitVec.ofNat 32 P ∧ t.gpr .r11 = 0 ∧
      t.mem = (s.mem.writeW (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (P + 8))).writeW
        (off (State.addr base) (M + 12)) (base + BitVec.ofNat 32 (A + 4)) ∧
      Rest [.r0, .r2, .r3, .r4, .r11, .r12, .lr] s t := by
  have nowrap := ws.nowrap
  unfold crossArgs
  refine wp_ldr (by decide) (sq_ea nowrap p0 (by omega_using [fit])) (ws.read (by omega_using [fit])) fun s1 u1 => ?_
  obtain p1 := (u1.other .r0 (by decide)).trans p0
  refine wp_ldr (by decide) (sq_ea nowrap p1 (by omega_using [fit])) (by rw [u1.rd, u1.wr]; exact ws.read (by omega_using [fit]))
    fun s2 u2 => ?_
  obtain p2 := (u2.other .r0 (by decide)).trans p1
  refine wp_ldr (by decide) (sq_ea nowrap p2 (by omega_using [fit]))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact ws.read (by omega_using [fit])) fun s3 u3 => ?_
  obtain p3 := (u3.other .r0 (by decide)).trans p2
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  obtain p4 := (u4.other .r0 (by decide)).trans p3
  refine wp_str (by decide) (sq_ea nowrap p4 (by omega_using [fit]))
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact ws.write (by omega_using [fit])) fun s5 u5 => ?_
  obtain p5 : s5.gpr .r0 = base + BitVec.ofNat 32 M := by rw [u5.gpr]; exact p4
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  obtain p6 := (u6.other .r0 (by decide)).trans p5
  refine wp_str (by decide) (sq_ea nowrap p6 (by omega_using [fit]))
    (by rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact ws.write (by omega_using [fit])) fun s7 u7 => ?_
  refine wp_mov (op2_reg _ _) fun s8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u9 => WP.block_nil ?_
  obtain g2 : s2.gpr .r2 = base + BitVec.ofNat 32 A := by rw [u2.other .r2 (by decide), u1.gpr, hn]
  obtain g3 : s3.gpr .r3 = base + BitVec.ofNat 32 P := by rw [u3.gpr, u2.mem, u1.mem, ht]
  obtain v4 : s4.gpr .r4 = base + BitVec.ofNat 32 (P + 8) := by
    rw [u4.gpr, dpVal, g3]
    change base + BitVec.ofNat 32 P + BitVec.ofNat 32 8 = _
    rw [Offset.add_add]
  obtain v6 : s6.gpr .r12 = base + BitVec.ofNat 32 (A + 4) := by
    rw [u6.gpr, dpVal, u5.gpr, u4.other .r2 (by decide), u3.other .r2 (by decide), g2]
    change base + BitVec.ofNat 32 A + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
  refine ⟨?_, ?_, ?_, ?_, u9.gpr, ?_, ?_⟩
  · rw [u9.other .r2 (by decide), u8.other .r2 (by decide), u7.gpr, u6.other .r2 (by decide), u5.gpr,
      u4.other .r2 (by decide), u3.other .r2 (by decide), g2]
  · rw [u9.other .r12 (by decide), u8.other .r12 (by decide), u7.gpr, v6]
  · rw [u9.other .lr (by decide), u8.other .lr (by decide), u7.gpr, u6.other .lr (by decide), u5.gpr,
      u4.other .lr (by decide), u3.other .lr (by decide), u2.gpr, u1.mem, hc]
  · rw [u9.other .r0 (by decide), u8.gpr, u7.gpr, u6.other .r3 (by decide), u5.gpr,
      u4.other .r3 (by decide), g3]
  · rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, v6, v4]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans
      ((u5.rest _).trans ((u6.rest (by decide)).trans ((u7.rest _).trans ((u8.rest (by decide)).trans (u9.rest (by decide)))))))))

/-- The row's scalar. -/
theorem crossScalar_ok (s : State) {base : BitVec 32} {size A : Nat} (ws : Workspace s base size)
    (fit : A + 4 ≤ size) (p2 : s.gpr .r2 = base + BitVec.ofNat 32 A) :
    WP isa (.block crossScalar) s fun t =>
      t.gpr .r1 = s.mem.readW (off (State.addr base) A) 32 ∧ t.mem = s.mem ∧ Rest [.r1] s t := by
  unfold crossScalar
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea ws.nowrap p2 (imm := 0) (by omega_using [fit]))
    (ws.read fit) fun t u => WP.block_nil ⟨u.gpr, u.mem, u.rest (by decide)⟩

/-- The row's carry stored above it. -/
theorem crossCarry_ok (s : State) {base : BitVec 32} {size d : Nat} (ws : Workspace s base size)
    (fit : d + 4 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 d) :
    WP isa (.block crossCarry) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) d) (s.gpr .r11) ∧ Rest [] s t := by
  unfold crossCarry
  refine wp_str (by decide) (by simpa only [Nat.add_zero] using sq_ea ws.nowrap p0 (imm := 0) (by omega_using [fit]))
    (ws.write fit) fun t u => WP.block_nil ⟨u.mem, u.rest _⟩

/-- A row's value step: the window, extended by the zero word above it,
gains the scalar product. -/
theorem cross_value {V5 V3 P Xo Xn L L4 Q r w A : Nat} (hrep : V5 + P * Xo = V3 + P * Xn)
    (hn : Xn = L4 + Q * r) (hrow : L4 + Q * r = L + w * A + 0) (ho : Xo = L + Q * 0) :
    V5 = V3 + P * (w * A) := by
  subst hn ho
  rw [hrow] at hrep
  grind

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem crossRound_ok (s : State) {k : Nat} (h : CrossInv m0 base size out a mod M n inv k s)
    (hk : k + 2 ≤ n) :
    WP isa crossRound s fun t => CrossInv m0 base size out a mod M n inv (k + 1) t ∧
      t.z = decide (k + 2 = n) ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.sepA; have := env.aFits; have := env.header
  -- The row's window, `len` words at `o`, and the word above it.
  obtain ⟨o, ho⟩ : ∃ o, o = M + 28 + 8 * k := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, len = n - 1 - k := ⟨_, rfl⟩
  rw [crossRound, WP.seq_iff]
  refine WP.mono (sqAnchor_ok s env) ?_
  rintro s1 ⟨p1, m1, r1⟩
  obtain e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (crossArgs_ok s1 (A := a + 4 * k) (C := len) (P := o) e1.workspace (by omega_arith) p1
    (by rw [m1]; exact h.next) (by rw [m1, hlen]; exact h.cnt) (by rw [m1, ho]; exact h.tptr)) ?_
  rintro s2 ⟨g2, g12, glr, g0, g11, m2, r2⟩
  obtain o2a := writeW32_outside s1.mem (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (o + 8))
    (by omega_arith)
  obtain o2b := writeW32_outside (s1.mem.writeW (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (o + 8)))
    (State.addr base) (d := M + 12) (base + BitVec.ofNat 32 (a + 4 * k + 4)) (by omega_arith)
  rw [← m2] at o2b
  obtain O2 : Outside (State.addr base) (M + 12) 12 s1.mem s2.mem :=
    (o2a.mono (by omega_arith) (by omega_arith)).trans (o2b.mono (by omega_arith) (by omega_arith))
  obtain e2 := e1.next (Outs.of_outside (O2.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) r2
  rw [WP.seq_iff]
  refine WP.mono (crossScalar_ok s2 e2.workspace (by omega_arith) g2) ?_
  rintro s3 ⟨g1, m3, r3⟩
  obtain e3 := e2.of_mem m3 r3
  obtain ctx : RowCtx s3 base size o (a + 4 * (k + 1)) len :=
    ⟨nowrap, by omega_arith, by omega_arith, by omega_arith, e3.workspace.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (row_ok s3 ctx (by omega_arith) ((r3.gpr .r0 (by decide)).trans g0)
    (by rw [r3.gpr .r12 (by decide), g12, show a + 4 * k + 4 = a + 4 * (k + 1) by omega_arith])
    ((r3.gpr .lr (by decide)).trans glr)) ?_
  intro s4 ri
  obtain e4 := e3.next (Outs.of_outside (ri.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith)
    (by omega_arith)) (by simp)) ri.rest
  rw [WP.seq_iff]
  refine WP.mono (crossCarry_ok s4 e4.workspace (d := o + 4 * len) (by omega_arith) ri.outPtr) ?_
  rintro s5 ⟨m5, r5⟩
  obtain o5 := writeW32_outside s4.mem (State.addr base) (d := o + 4 * len) (s4.gpr .r11) (by omega_arith)
  rw [← m5] at o5
  obtain OW : Outside (State.addr base) o (4 * len + 4) s3.mem s5.mem :=
    (ri.outside.mono (by omega_arith) (by omega_arith)).trans (o5.mono (by omega_arith) (by omega_arith))
  obtain e5 := e4.next (Outs.of_outside (o5.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) r5
  rw [WP.seq_iff]
  refine WP.mono (sqAnchor_ok s5 e5) ?_
  rintro s6 ⟨p6, m6, r6⟩
  obtain e6 := e5.of_mem m6 r6
  obtain cnt6 : s6.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 len := by
    rw [m6, outside_read32 OW (by omega_arith) (by omega_arith), m3, m2, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith),
      rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m1, hlen]
    exact h.cnt
  refine WP.mono (sqCount_ok s6 e6.workspace (by omega_arith) p6 cnt6 (by omega_arith) (by omega_arith)) ?_
  rintro t ⟨m7, z7, r7⟩
  obtain o7 := writeW32_outside s6.mem (State.addr base) (d := M + 16) (BitVec.ofNat 32 (len - 1)) (by omega_arith)
  rw [← m7] at o7
  obtain et := e6.next (Outs.of_outside (o7.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) r7
  -- Everything but the metadata's words from `M + 12` and the row.
  obtain all : Outs (State.addr base) [(M + 12, 12), (o, 4 * len + 4)] s.mem t.mem := by
    obtain A1 : Outs (State.addr base) [(M + 12, 12), (o, 4 * len + 4)] s1.mem s2.mem :=
      Outs.of_outside O2 (by simp)
    obtain A2 : Outs (State.addr base) [(M + 12, 12), (o, 4 * len + 4)] s3.mem s5.mem :=
      Outs.of_outside OW (by simp)
    obtain A3 : Outs (State.addr base) [(M + 12, 12), (o, 4 * len + 4)] s6.mem t.mem :=
      Outs.of_outside (o7.mono (o' := M + 12) (n' := 12) (by omega_arith) (by omega_arith)) (by simp)
    rw [m1] at A1; rw [m3] at A2; rw [m6] at A3
    exact A1.trans (A2.trans A3)
  -- The value.
  obtain aw := e2.aWord (j := k) (by omega_arith)
  obtain av := e3.aVal (d := a + 4 * (k + 1)) (k := len) (by omega_arith) (by omega_arith)
  obtain v3 : val32 s3.mem (State.addr base) (M + 24) (2 * n + 2) = sqCross m0 (State.addr base) a n k := by
    rw [m3, O2.val32 (by omega_arith) (by omega_arith), m1]; exact h.value
  obtain rep := val32_replace (m := s3.mem) (m' := s5.mem) (base := State.addr base) (d := M + 24)
    (i := 2 * k + 1) (j := n - k) (k := n + 1 - k) (OW.val32 (by omega_arith) (by omega_arith))
    (OW.val32 (by omega_arith) (by omega_arith))
  rw [show 2 * k + 1 + (n - k) + (n + 1 - k) = 2 * n + 2 by omega_arith,
    show M + 24 + 4 * (2 * k + 1) = o by omega_arith, show n - k = len + 1 by omega_arith] at rep
  obtain xn : val32 s5.mem (State.addr base) o len = val32 s4.mem (State.addr base) o len :=
    o5.val32 (by omega_arith) (by omega_arith)
  obtain wn : w32 s5.mem (State.addr base) (o + 4 * len) = (s4.gpr .r11).toNat := by
    rw [m5, w32_write_self]
  obtain wo : w32 s3.mem (State.addr base) (o + 4 * len) = 0 := by
    rw [m3, O2.w32 (by omega_arith) (by omega_arith), m1, show o + 4 * len = M + 24 + 4 * (k + n) by omega_arith]
    have z := h.top
    rw [show n + 2 - k = (n + 1 - k) + 1 by omega_arith] at z
    exact val32_zero_head z
  have row := ri.value
  rw [(r3.gpr .r11 (by decide)).trans g11, g1] at row
  change _ = _ + w32 s2.mem (State.addr base) (a + 4 * k) * _ + (0 : BitVec 32).toNat at row
  rw [aw, show a + 4 * (k + 1) = a + 4 * (k + 1) from rfl] at row
  obtain vt : val32 t.mem (State.addr base) (M + 24) (2 * n + 2) = val32 s5.mem (State.addr base) (M + 24) (2 * n + 2) := by
    rw [o7.val32 (by omega_arith) (by omega_arith), m6]
  refine ⟨⟨et, by omega_arith, h.md.of_outs all (by simp; omega_arith) (by omega_arith), ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [m7, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m6, outside_read32 OW (by omega_arith) (by omega_arith), m3, m2,
      rd_self, show a + 4 * k + 4 = a + 4 * (k + 1) by omega_arith]
  · rw [m7, rd_self, hlen, show n - 1 - k - 1 = n - 1 - (k + 1) by omega_arith]
  · rw [m7, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m6, outside_read32 OW (by omega_arith) (by omega_arith), m3, m2,
      rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), rd_self, ho, show M + 28 + 8 * k + 8 = M + 28 + 8 * (k + 1) by omega_arith]
  · rw [vt]
    have := cross_value rep (by rw [val32_succ, xn, wn]) row (by rw [val32_succ, wo])
    rw [this, v3, av, hlen]
    rfl
  · rw [all.val32 (by simp; omega_arith) (by omega_arith)]
    have z := h.top
    rw [show n + 2 - k = 1 + (n + 2 - (k + 1)) by omega_arith] at z
    obtain z' := val32_zero_tail z
    rwa [show M + 24 + 4 * (k + n) + 4 * 1 = M + 24 + 4 * (k + 1 + n) by omega_arith] at z'
  · rw [z7, hlen]; simp only [show n - 1 - k = 1 ↔ k + 2 = n by omega_arith]
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((ri.rest.mono (by decide)).trans
      ((r5.mono (by decide)).trans ((r6.mono (by decide)).trans
      (r7.mono (by decide)))))))

theorem crossRows_ok (s : State) (h : CrossInv m0 base size out a mod M n inv 0 s) :
    WP isa crossRows s fun t => CrossInv m0 base size out a mod M n inv (n - 1) t ∧
      Rest roundClobbers s t := by
  have hn := h.env.count
  let loopInv := fun k t => ∃ i, i + k = n - 1 ∧ 0 < k ∧
    CrossInv m0 base size out a mod M n inv i t ∧ Rest roundClobbers s t
  unfold crossRows
  refine WP.loop (M := isa) loopInv ?_ (n - 1) s ?_
  · intro k t hk
    obtain ⟨i, hik, hk, hi, rest⟩ := hk
    refine WP.mono (crossRound_ok t hi (by omega_using [hik, hk])) ?_
    rintro u ⟨hu, hz, ru⟩
    by_cases he : i + 2 = n
    · left
      refine ⟨?_, by rw [show n - 1 = i + 1 by omega_using [he]]; exact hu, rest.trans ru⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, he], hu, rest.trans ru⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · exact ⟨0, by omega_using [], by omega_using [hn], h, Rest.refl _ _⟩

end

end VG.Proof.Bignum.Arm
