module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareState
public import VerifiedGarbage.Proof.Bignum.Arm.Zero
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
  refine wp_ldr (a := off (State.addr base) 80) (by decide) (by rw [p]; exact VG.Arm.addr_add (by omega))
    (hu.read (by omega)) fun t ut => WP.block_nil ?_
  exact ⟨ut.gpr.trans hu.metaNow, ut.mem.trans mem, rest.trans (ut.rest (by simp))⟩

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
    sq_ea nowrap (hu.trans p6) (by omega)
  have wr (d : Nat) (hd : d + 4 ≤ 24) {u : State} (hw : u.wr = s.wr) :
      InRegions u.wr (off (State.addr base) (M + d)) 4 := by
    rw [hw]; exact h.write (by omega)
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
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
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
    (writeW32_outside mem (State.addr base) v (by omega)).mono (by omega) (by omega)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m8, rd_other _ (by omega) (by omega) (by omega), m6, rd_other _ (by omega) (by omega) (by omega),
      m4, rd_other _ (by omega) (by omega) (by omega), m3, rd_other _ (by omega) (by omega) (by omega),
      m2, rd_other _ (by omega) (by omega) (by omega), m1, rd_self]
  · rw [m8, rd_other _ (by omega) (by omega) (by omega), m6, rd_other _ (by omega) (by omega) (by omega),
      m4, rd_other _ (by omega) (by omega) (by omega), m3, rd_other _ (by omega) (by omega) (by omega),
      m2, rd_self]
  · rw [m8, rd_other _ (by omega) (by omega) (by omega), m6, rd_other _ (by omega) (by omega) (by omega),
      m4, rd_other _ (by omega) (by omega) (by omega), m3, rd_self]
  · rw [m8, rd_other _ (by omega) (by omega) (by omega), m6, rd_other _ (by omega) (by omega) (by omega),
      m4, rd_self]
  · rw [m8, rd_other _ (by omega) (by omega) (by omega), m6, rd_self]
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
      ((u5.rest (by simp)).trans ((u6.rest _).trans ((u7.rest (by simp)).trans (u8.rest _)))))))

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
      ofNat_shl (by omega)]
    change BitVec.ofNat 32 (n * 2 ^ 1) + BitVec.ofNat 32 2 = _
    rw [BitVec.ofNat_add_ofNat, show n * 2 ^ 1 + 2 = 2 * n + 2 by omega]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))

theorem sqInit_ok (s : State) (h : SqEnv m0 base size out a mod M n inv s)
    (p6 : s.gpr .r6 = base + BitVec.ofNat 32 M) (p7 : s.gpr .r7 = BitVec.ofNat 32 n)
    (p8 : s.gpr .r8 = base + BitVec.ofNat 32 a) (p10 : s.gpr .r10 = base + BitVec.ofNat 32 out) :
    WP isa sqInit s fun t => CrossInv m0 base size out a mod M n inv 0 t ∧ Rest roundClobbers s t := by
  have nowrap := h.nowrap
  have := h.fits; have := h.count
  rw [sqInit, WP.seq_iff]
  refine WP.mono (sqMeta_ok s h p6 p7 p8 p10) ?_
  rintro u ⟨md, next, cnt, tptr, outU, restU⟩
  have hu := h.next (Outs.of_outside (outU.mono (o' := M) (n' := 4 * (2 * n + 8)) (Nat.le_refl _) (by omega)) (by simp)) restU
  rw [WP.seq_iff]
  refine WP.mono (sqZeroArgs_ok u hu ((restU.gpr .r6 (by simp)).trans p6)
    ((restU.gpr .r7 (by simp)).trans p7)) ?_
  rintro v ⟨p0, plr, p3, memV, restV⟩
  have hv := hu.of_mem memV restV
  have cv : ZeroCtx v base size (M + 24) (2 * n + 2) :=
    ⟨nowrap, by omega, ⟨_, hv.workspace.writable, Region.contains_self _ _⟩⟩
  refine WP.mono (zero_ok v cv (by omega) p0 plr p3) ?_
  intro t zt
  have outT : Outs (State.addr base) [(M, 4 * (2 * n + 8))] v.mem t.mem :=
    Outs.of_outside (zt.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega)) (by simp)
  have ht := hv.next outT zt.rest
  have kept (d : Nat) (hd : d + 4 ≤ 24) :
      t.mem.readW (off (State.addr base) (M + d)) 32 = u.mem.readW (off (State.addr base) (M + d)) 32 := by
    rw [← memV]
    exact outside_read32 zt.outside (by omega) (by omega)
  refine ⟨⟨ht, by omega, md.congr fun d hd => kept d (by omega), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kept 12 (by decide), next, Nat.mul_zero, Nat.add_zero]
  · rw [kept 16 (by decide), cnt, Nat.sub_zero]
  · rw [kept 20 (by decide), tptr, Nat.mul_zero, Nat.add_zero]
  · rw [zt.value]; rfl
  · have z := zt.value
    rw [show 2 * n + 2 = n + (n + 2) by omega] at z
    simpa only [Nat.zero_add, Nat.sub_zero] using val32_zero_tail z
  · exact (restU.mono (by simp [roundClobbers])).trans ((restV.mono (by simp [roundClobbers])).trans
      (zt.rest.mono (by simp [roundClobbers])))

end

end VG.Proof.Bignum.Arm
