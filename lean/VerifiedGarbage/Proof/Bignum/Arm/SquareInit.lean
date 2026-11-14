module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareState
public import VerifiedGarbage.Impl.Bignum.Arm.Square
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

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
    have e : n - k = (n - 1 - k) + 1 := by omega_using [hk]
    rw [e, val32, show a + 4 * k + 4 = a + 4 * (k + 1) by omega_using [], show n - (k + 1) = n - 1 - k by omega_using []]
    simp only [diagSum, sqCross]
    have e1 : 2 ^ (32 * (2 * k + 1)) = 2 ^ (64 * k) * 2 ^ 32 := by
      rw [← Nat.pow_add]; congr 1 <;> omega_using []
    have e2 : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 32 * 2 ^ 32 := by
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
  have h1 : x * x ≤ x * M := Nat.mul_le_mul_left _ (Nat.le_of_lt hx)
  have h2 : x * M < R * M := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le hx hM)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) hx)
  have h3 : Q * M ≤ R * M := Nat.mul_le_mul_right _ (Nat.le_of_lt hQ)
  have h4 : R * H < R * (2 * M) := by
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
  have hu := h.of_mem mem rest
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
  have g7 : s4.gpr .r7 = s.gpr .r7 := by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  have g6 : s6.gpr .r6 = s.gpr .r6 := by
    rw [u6.gpr, u5.other .r6 (by decide), u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  have v1 : s5.gpr .r1 = BitVec.ofNat 32 (n - 1) := by
    rw [u5.gpr, dpVal, g7, p7]
    change BitVec.ofNat 32 n - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
  have v2 : s7.gpr .r1 = base + BitVec.ofNat 32 (M + 28) := by
    rw [u7.gpr, dpVal, g6, p6]
    change base + BitVec.ofNat 32 M + BitVec.ofNat 32 28 = _
    rw [Offset.add_add]
  have m1 : s1.mem = s.mem.writeW (off (State.addr base) M) (BitVec.ofNat 32 n) := by rw [u1.mem, p7]
  have m2 : s2.mem = s1.mem.writeW (off (State.addr base) (M + 4)) (base + BitVec.ofNat 32 out) := by
    rw [u2.mem, u1.gpr, p10]
  have m3 : s3.mem = s2.mem.writeW (off (State.addr base) (M + 8)) (base + BitVec.ofNat 32 a) := by
    rw [u3.mem, u2.gpr, u1.gpr, p8]
  have m4 : s4.mem = s3.mem.writeW (off (State.addr base) (M + 12)) (base + BitVec.ofNat 32 a) := by
    rw [u4.mem, u3.gpr, u2.gpr, u1.gpr, p8]
  have m6 : s6.mem = s4.mem.writeW (off (State.addr base) (M + 16)) (BitVec.ofNat 32 (n - 1)) := by
    rw [u6.mem, u5.mem, v1]
  have m8 : t.mem = s6.mem.writeW (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (M + 28)) := by
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
    have h2 : Outside (State.addr base) M 24 s1.mem s2.mem := by rw [m2]; exact o 4 (by decide) _ _
    have h3 : Outside (State.addr base) M 24 s2.mem s3.mem := by rw [m3]; exact o 8 (by decide) _ _
    have h4 : Outside (State.addr base) M 24 s3.mem s4.mem := by rw [m4]; exact o 12 (by decide) _ _
    have h6 : Outside (State.addr base) M 24 s4.mem s6.mem := by rw [m6]; exact o 16 (by decide) _ _
    have h8 : Outside (State.addr base) M 24 s6.mem t.mem := by rw [m8]; exact o 20 (by decide) _ _
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
  have hu := h.next (Outs.of_outside (outU.mono (o' := M) (n' := 4 * (2 * n + 8)) (Nat.le_refl _) (by omega_arith)) (by simp)) restU
  rw [WP.seq_iff]
  refine WP.mono (sqZeroArgs_ok u hu ((restU.gpr .r6 (by decide)).trans p6)
    ((restU.gpr .r7 (by decide)).trans p7)) ?_
  rintro v ⟨p0, plr, p3, memV, restV⟩
  have hv := hu.of_mem memV restV
  have cv : ZeroCtx v base size (M + 24) (2 * n + 2) :=
    ⟨nowrap, by omega_arith, ⟨_, hv.workspace.writable, Region.contains_self _ _⟩⟩
  refine WP.mono (zero_ok v cv (by omega_arith) p0 plr p3) ?_
  intro t zt
  have outT : Outs (State.addr base) [(M, 4 * (2 * n + 8))] v.mem t.mem :=
    Outs.of_outside (zt.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith)) (by simp)
  have ht := hv.next outT zt.rest
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
