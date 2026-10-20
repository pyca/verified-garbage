module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Store
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ChaCha20-Poly1305 on AArch64, 64 to 256 bytes: the data XORed with its keystream

`Short.xor16` and `Short.xor1` XOR `x11` blocks of 16 bytes, and of 1 byte,
at `x10` into `x9`; `Short.xorKs` XORs the data, `x23` bytes at `x22`, with
the keystream at `ctx + 128`: its whole blocks of 16 bytes, then the rest.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Short

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Short
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_subImm wp_mov wp_ldrb wp_strb wp_eor32 wp_lsr
  eval_nonzero_ofNat eval_zero ofNat_beq_zero xor_setWidth writeW8_apply sub_ofNat add_ofNat)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)

/-- The bytes `[0, n)` at `D`, a region of `w * c` bytes. -/
abbrev dR' (D : Addr) (n : Nat) : Region := ⟨D, n⟩

/-- What the loops need: `c` blocks of `w` bytes at `D` may be written, at `P`
read, and the two do not overlap or wrap around. -/
structure XH (s : State) (D P : Addr) (n : Nat) : Prop where
  wD : ∀ i w, i + w ≤ n → InRegions s.wr (D + BitVec.ofNat 64 i) w
  rP : ∀ i w, i + w ≤ n → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) w
  rD : ∀ i w, i + w ≤ n → InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) w
  dj : (⟨D, n⟩ : Region).Disjoint ⟨P, n⟩
  wrapD : D.toNat + n ≤ 2 ^ 64
  wrapP : P.toNat + n ≤ 2 ^ 64

/-- After `j` of the `n` blocks of `w` bytes, from `s₀`, in which `x9 = D`,
`x10 = P` and `x11 = n`. -/
structure XI (s₀ : State) (D P : Addr) (w n j : Nat) (s : State) : Prop where
  x9 : s.gpr .x9 = D + BitVec.ofNat 64 (w * j)
  x10 : s.gpr .x10 = P + BitVec.ofNat 64 (w * j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (n - j)
  keep : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨D, w * j⟩] s₀.mem s.mem
  data : ∀ i < w * j, s.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) ^^^
    s₀.mem (P + BitVec.ofNat 64 i)

theorem XI.zero {s₀ : State} {D P : Addr} {w n : Nat} (h9 : s₀.gpr .x9 = D) (h10 : s₀.gpr .x10 = P)
    (h11 : s₀.gpr .x11 = BitVec.ofNat 64 n) : XI s₀ D P w n 0 s₀ :=
  ⟨by simp [h9], by simp [h10], by simp [h11], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
    fun i hi => absurd hi (by omega)⟩

/-- The loop, from its step. -/
theorem xloop_ok {body : List Instr} {s₀ s : State} {D P : Addr} {w n : Nat} (hn : 0 < n)
    (hn' : n < 2 ^ 64) (hs : XI s₀ D P w n 0 s)
    (hstep : ∀ j < n, ∀ s, XI s₀ D P w n j s → WP isa (.block body) s (XI s₀ D P w n (j + 1))) :
    WP isa (.loop (.block body) (.nonzero .x .x11)) s (XI s₀ D P w n n) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ j < n ∧ XI s₀ D P w n j s)
    (fun m s ⟨j, hm, hj, hI⟩ => WP.mono (hstep j hj s hI) fun s' h' => ?_) n s ⟨0, by simp, hn, hs⟩
  have hz := eval_nonzero_ofNat s' .x11 (k := n - (j + 1)) (by omega) h'.x11
  by_cases hl : j + 1 = n
  · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
  · exact .inr ⟨by rw [hz]; simp; omega, n - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, show off < 4096 * 16 by omega, ho, and_self, ite_true, Option.bind_some,
    State.load, h, Option.map_some]

/-- A byte `[D + i]` outside a write at `D + a`. -/
theorem write_out {m : Mem} {D : Addr} {a i n : Nat} {v : BitVec (8 * n)} (h : i < a ∨ a + n ≤ i)
    (hi : i < 2 ^ 64) (ha : a + n ≤ 2 ^ 64) :
    m.write (D + BitVec.ofNat 64 a) n v (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  refine Mem.write_apply fun h' => ?_
  rw [Offset.lt_iff _ D ha, Mem.sub_ofNat_toNat D hi] at h'
  omega

/-- The vector loop's body. -/
abbrev body16 : List Instr :=
  [.ldrq .v0 .x9 0, .ldrq .v1 .x10 0, .vop (.logic .eor .v0 .v0 .v1), .strq .v0 .x9 0,
    .addImm .x .x9 .x9 16, .addImm .x .x10 .x10 16, .subImm .x .x11 .x11 1]

theorem xor16_eq : xor16 = .loop (.block body16) (.nonzero .x .x11) := rfl

theorem step16_ok {s₀ s : State} {D P : Addr} {n j : Nat} (hh : XH s₀ D P (16 * n)) (hj : j < n)
    (h : XI s₀ D P 16 n j s) : WP isa (.block body16) s (XI s₀ D P 16 n (j + 1)) := by
  have hA : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 0) 16 := by
    rw [h.x9, h.rd, h.wr, BitVec.add_zero]; exact hh.rD _ _ (by omega)
  have hB : InRegions (s.rd ++ s.wr) (s.gpr .x10 + BitVec.ofNat 64 0) 16 := by
    rw [h.x10, h.rd, h.wr, BitVec.add_zero]; exact hh.rP _ _ (by omega)
  have hW : InRegions s.wr (s.gpr .x9 + BitVec.ofNat 64 0) 16 := by
    rw [h.x9, h.wr, BitVec.add_zero]; exact hh.wD _ _ (by omega)
  have core : WP isa (.block body16) s fun s' =>
      s'.mem = s.mem.write (D + BitVec.ofNat 64 (16 * j)) 16
        (s.mem.read (D + BitVec.ofNat 64 (16 * j)) 16 ^^^ s.mem.read (P + BitVec.ofNat 64 (16 * j)) 16) ∧
      s'.gpr .x9 = s.gpr .x9 + BitVec.ofNat 64 16 ∧ s'.gpr .x10 = s.gpr .x10 + BitVec.ofNat 64 16 ∧
      s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine WP.block_cons_iff.mpr ⟨_, exec_ldrq (by decide) hA, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_ldrq (off := 0) (by decide) (by simpa only [RegUpd.gpr_setV, RegUpd.rd_setV,
      RegUpd.wr_setV] using hB), ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_strq (off := 0) (by decide) (by simpa only [RegUpd.gpr_setV,
      RegUpd.wr_setV] using hW), ?_⟩
    refine wp_addImm (by decide) fun s₅ u₅ => wp_addImm (by decide) fun s₆ u₆ =>
      wp_subImm (by decide) fun s₇ u₇ => WP.block_nil ?_
    refine ⟨?_, ?_, ?_, ?_, fun r h9 h10 h11 => ?_, ?_, ?_⟩
    · rw [u₇.mem, u₆.mem, u₅.mem]
      simp only [RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_setV_self, h.x9, h.x10, BitVec.add_zero]
      rw [RegUpd.v_setV_of_ne _ _ (by decide), RegUpd.v_setV_self]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; rfl
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide)]; rfl
    · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide)]; rfl
    · rw [u₇.other _ h11, u₆.other _ h10, u₅.other _ h9]; rfl
    · rw [u₇.rd, u₆.rd, u₅.rd]; rfl
    · rw [u₇.wr, u₆.wr, u₅.wr]; rfl
  refine WP.mono (WP.withSp core) fun s' ⟨⟨hm, x9', x10', x11', g, rd', wr'⟩, sp'⟩ => ?_
  have hs : ∀ i < 16 * n, s.mem (P + BitVec.ofNat 64 i) = s₀.mem (P + BitVec.ofNat 64 i) := fun i hi =>
    h.frame.bytes (R := ⟨P, 16 * n⟩) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hh.dj.symm.sub_right (Region.sub_prefix (by omega)))
      (show 16 * n ≤ 2 ^ 64 by have := hh.wrapP; omega) (show i < 16 * n from hi)
  refine ⟨by rw [x9', h.x9, add_ofNat]; congr 2, by rw [x10', h.x10, add_ofNat]; congr 2,
    by rw [x11', h.x11, sub_ofNat (by omega)]; congr 1, fun r h9 h10 h11 h12 h13 => by
      rw [g r h9 h10 h11, h.keep r h9 h10 h11 h12 h13], by rw [sp', h.sp], by rw [rd', h.rd],
    by rw [wr', h.wr], ?_, fun i hi => ?_⟩
  · rw [hm]
    exact (h.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).write
      (List.mem_singleton_self _) _ (Offset.contains_base D (by omega) (by have := hh.wrapD; omega))
  · have hwrap := hh.wrapD
    rw [hm]
    by_cases hi' : i < 16 * j
    · rw [write_out (by omega) (by omega) (by omega), h.data i hi']
    · have e : D + BitVec.ofNat 64 i = D + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (i - 16 * j) := by
        rw [add_ofNat]; congr 2; omega
      have e' : P + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (i - 16 * j) = P + BitVec.ofNat 64 i := by
        rw [add_ofNat]; congr 2; omega
      have hd : s.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) :=
        h.frame _ fun r hr hc => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [Region.Contains, Mem.sub_ofNat_toNat D (show i < 2 ^ 64 by omega)] at hc
          omega
      rw [e, VG.Proof.ChaCha20.AArch64.Neon4.xor_write_byte _ _ _ (by omega),
        VG.Proof.ChaCha20.AArch64.Neon4.byte_read16 _ _ (by omega), e', ← e, hd, hs i (by omega)]

/-- The byte loop's body. -/
abbrev body1 : List Instr :=
  [.ldrb .x12 .x9 0, .ldrb .x13 .x10 0, .logic .eor .w .x12 .x12 .x13, .strb .x12 .x9 0,
    .addImm .x .x9 .x9 1, .addImm .x .x10 .x10 1, .subImm .x .x11 .x11 1]

theorem xor1_eq : xor1 = .loop (.block body1) (.nonzero .x .x11) := rfl

theorem step1_ok {s₀ s : State} {D P : Addr} {n j : Nat} (hh : XH s₀ D P (1 * n)) (hj : j < n)
    (h : XI s₀ D P 1 n j s) : WP isa (.block body1) s (XI s₀ D P 1 n (j + 1)) := by
  have hj1 : 1 * j = j := Nat.one_mul j
  have hA : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hh.rD _ _ (by omega)
  have hB : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hh.rP _ _ (by omega)
  have hW : InRegions s.wr (D + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hh.wD _ _ (by omega)
  have x9 : s.gpr .x9 + BitVec.ofNat 64 0 = D + BitVec.ofNat 64 j := by rw [h.x9, hj1, BitVec.add_zero]
  have x10 : s.gpr .x10 + BitVec.ofNat 64 0 = P + BitVec.ofNat 64 j := by rw [h.x10, hj1, BitVec.add_zero]
  have core : WP isa (.block body1) s fun s' =>
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 j)
        (s.mem (D + BitVec.ofNat 64 j) ^^^ s.mem (P + BitVec.ofNat 64 j)) ∧
      s'.gpr .x9 = s.gpr .x9 + BitVec.ofNat 64 1 ∧ s'.gpr .x10 = s.gpr .x10 + BitVec.ofNat 64 1 ∧
      s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_ldrb (by decide) x9 hA fun s₁ u₁ => ?_
    refine wp_ldrb (by decide) (by rw [u₁.other _ (by decide), x10]) (by rw [u₁.rd, u₁.wr]; exact hB)
      fun s₂ u₂ => ?_
    refine wp_eor32 fun s₃ u₃ => ?_
    refine wp_strb (by decide) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), x9])
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hW) fun s₄ m₄ => ?_
    refine wp_addImm (by decide) fun s₅ u₅ => wp_addImm (by decide) fun s₆ u₆ =>
      wp_subImm (by decide) fun s₇ u₇ => WP.block_nil ?_
    have g₄ : ∀ r, r ≠ .x12 → r ≠ .x13 → s₄.gpr r = s.gpr r := fun r h12 h13 => by
      rw [m₄.gpr, u₃.other _ h12, u₂.other _ h13, u₁.other _ h12]
    refine ⟨?_, ?_, ?_, ?_, fun r h9 h10 h11 h12 h13 => ?_, ?_, ?_⟩
    · rw [u₇.mem, u₆.mem, u₅.mem, m₄.mem, u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₃.mem, u₂.mem,
        u₁.mem, xor_setWidth]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide) (by decide)]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄ _ (by decide) (by decide)]
    · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄ _ (by decide) (by decide)]
    · rw [u₇.other _ h11, u₆.other _ h10, u₅.other _ h9, g₄ r h12 h13]
    · rw [u₇.rd, u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₇.wr, u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine WP.mono (WP.withSp core) fun s' ⟨⟨hm, x9', x10', x11', g, rd', wr'⟩, sp'⟩ => ?_
  have hwrap := hh.wrapD
  have hs : ∀ i < 1 * n, s.mem (P + BitVec.ofNat 64 i) = s₀.mem (P + BitVec.ofNat 64 i) := fun i hi =>
    h.frame.bytes (R := ⟨P, 1 * n⟩) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hh.dj.symm.sub_right (Region.sub_prefix (by omega)))
      (show 1 * n ≤ 2 ^ 64 by have := hh.wrapP; omega) (show i < 1 * n from hi)
  refine ⟨by rw [x9', h.x9, add_ofNat]; congr 2, by rw [x10', h.x10, add_ofNat]; congr 2,
    by rw [x11', h.x11, sub_ofNat (by omega)]; congr 1, fun r h9 h10 h11 h12 h13 => by
      rw [g r h9 h10 h11 h12 h13, h.keep r h9 h10 h11 h12 h13], by rw [sp', h.sp], by rw [rd', h.rd],
    by rw [wr', h.wr], ?_, fun i hi => ?_⟩
  · rw [hm]
    exact (h.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base D (by omega) (by omega))
  · rw [hm, writeW8_apply]
    by_cases hi' : i < j
    · rw [ite_eq_right_iff.mpr fun e => absurd e (Offset.add_ofNat_ne D (by omega) (by omega) (by omega)),
        h.data i (by omega)]
    · have hij : i = j := by omega
      subst hij
      have hd : s.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) :=
        h.frame _ fun r hr hc => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [Region.Contains, Mem.sub_ofNat_toNat D (show i < 2 ^ 64 by omega)] at hc
          omega
      simp only [ite_true]
      rw [hd, hs i (by omega)]

variable {e : Bool}

/-- The data's keystream, at `ctx + 128`. -/
abbrev kp' (s₀ : State) : Addr := off (cx s₀) 128

theorem toNat_add_le (p : Addr) (a : Nat) : (p + BitVec.ofNat 64 a).toNat ≤ p.toNat + a := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)

/-- The loops' regions: `m` bytes from `o + a` bytes into the data and from
`a` bytes into the keystream. -/
theorem xh {s₀ s : State} (hp : APre e s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {o a m : Nat} (h : o + a + m ≤ L s₀) (hb : a + m ≤ 256) :
    XH s (dp s₀ + BitVec.ofNat 64 (o + a)) (kp' s₀ + BitVec.ofNat 64 a) m := by
  have wd := hp.wrap_d
  have wc := hp.wrap_c
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have wD : ∀ i w, i + w ≤ m → InRegions s.wr (dp s₀ + BitVec.ofNat 64 (o + a) + BitVec.ofNat 64 i) w :=
    fun i w hi => by
      rw [add_ofNat, hwr]
      exact ⟨dR s₀, hp.d_wr, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨wD, fun i w hi => ?_, fun i w hi => ?_, ?_, ?_, ?_⟩
  · rw [add_ofNat, kp', off_add, hrd, hwr]; exact hp.in_ctx' (by omega)
  · obtain ⟨r, hr, hc⟩ := wD i w hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [kp', off_add]
    exact (hp.c_d.symm.sub_left (Offset.sub_base _ h)).sub_right (sub_ctx s₀ (by omega))
  · have := toNat_add_le (dp s₀) (o + a); omega
  · rw [kp', off_add]; have := toNat_add_le (cx s₀) (128 + a); omega

theorem setup_ok {s₀ s : State} {D : Addr} {n : Nat} (hn : n < 2 ^ 64) (hx21 : s.gpr .x21 = cx s₀)
    (hx22 : s.gpr .x22 = D) (hx23 : s.gpr .x23 = BitVec.ofNat 64 n) :
    WP isa (.block [mov .x9 .x22, .addImm .x .x10 .x21 128, .lsr .x .x11 .x23 4]) s fun s' =>
      s'.gpr .x9 = D ∧ s'.gpr .x10 = kp' s₀ ∧ s'.gpr .x11 = BitVec.ofNat 64 (n / 16) ∧
      Kept [] s s' ∧ ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r := by
  have h : WP isa (.block [mov .x9 .x22, .addImm .x .x10 .x21 128, .lsr .x .x11 .x23 4]) s fun s' =>
      s'.gpr .x9 = D ∧ s'.gpr .x10 = kp' s₀ ∧ s'.gpr .x11 = BitVec.ofNat 64 (n / 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r :=
    wp_mov fun s₁ u₁ => wp_addImm (by decide) fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx22],
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hx21],
        by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx23, shr4_ofNat hn],
        by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.mem, u₂.mem, u₁.mem],
        fun r h9 h10 h11 => by rw [u₃.other _ h11, u₂.other _ h10, u₁.other _ h9]⟩
  exact WP.mono (WP.kept h rfl) fun s' ⟨⟨h9, h10, h11, hrd, hwr, hm, hg'⟩, hg, hsp⟩ =>
    ⟨h9, h10, h11, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hg'⟩

theorem rest_ok {s : State} {n : Nat} (hn : n < 2 ^ 64) (hx23 : s.gpr .x23 = BitVec.ofNat 64 n) :
    WP isa (.block [.lsl .x .x11 .x23 60, .lsr .x .x11 .x11 60]) s fun s' =>
      s'.gpr .x11 = BitVec.ofNat 64 (n % 16) ∧
      (∀ r, r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h : WP isa (.block [.lsl .x .x11 .x23 60, .lsr .x .x11 .x11 60]) s fun s' =>
      s'.gpr .x11 = BitVec.ofNat 64 (n % 16) ∧
      (∀ r, r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
    wp_lsl (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.gpr, u₁.gpr, shl_shr60, hx23, toNat_ofNat_lt hn],
        fun r hr => by rw [u₂.other _ hr, u₁.other _ hr],
        by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  exact h

/-- A loop guarded by `x11 ≠ 0`, from its step. -/
theorem guarded_ok {body : List Instr} {s₀ : State} {D P : Addr} {w n : Nat} (hn' : n < 2 ^ 64)
    (h11 : s₀.gpr .x11 = BitVec.ofNat 64 n) (h9 : s₀.gpr .x9 = D) (h10 : s₀.gpr .x10 = P)
    (hstep : ∀ j < n, ∀ s, XI s₀ D P w n j s → WP isa (.block body) s (XI s₀ D P w n (j + 1))) :
    WP isa (.ite (.zero .x .x11) (.block []) (.loop (.block body) (.nonzero .x .x11))) s₀
      (XI s₀ D P w n n) := by
  refine WP.ite (decide (n = 0)) (by
      have e : isa.eval (.zero .x .x11) s₀ = some (s₀.gpr .x11 == 0) := eval_zero s₀ .x11
      rw [e, h11, ofNat_beq_zero hn']) (fun h => ?_) (fun h => ?_)
  · have h0 : n = 0 := by simpa using h
    subst h0
    exact WP.block_nil (XI.zero h9 h10 h11)
  · have h0 : n ≠ 0 := by simpa using h
    exact xloop_ok (by omega) hn' (XI.zero h9 h10 h11) hstep

/-- The `n ≤ 256` bytes `o` bytes into the data XORed with the keystream. -/
theorem xorKsAt_ok {s₀ s : State} (hp : APre e s₀) {o n : Nat} (hn : n ≤ 256) (hon : o + n ≤ L s₀)
    (hx21 : s.gpr .x21 = cx s₀) (hx22 : s.gpr .x22 = dp s₀ + BitVec.ofNat 64 o)
    (hx23 : s.gpr .x23 = BitVec.ofNat 64 n) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa xorKs s fun s' => Kept [dR s₀] s s' ∧ (∀ i < n,
      s'.mem (dp s₀ + BitVec.ofNat 64 (o + i)) = s.mem (dp s₀ + BitVec.ofNat 64 (o + i)) ^^^
        s.mem (kp' s₀ + BitVec.ofNat 64 i)) ∧
      Frame [⟨dp s₀ + BitVec.ofNat 64 o, n⟩] s.mem s'.mem ∧
      ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x13] → s'.gpr r = s.gpr r := by
  have wd := hp.wrap_d
  have hn' : n < 2 ^ 64 := by omega
  unfold xorKs
  refine WP.seq (WP.mono (setup_ok hn' hx21 hx22 hx23) fun s₁ ⟨x9₁, x10₁, x11₁, k₁, gs₁⟩ => ?_)
  have hh₁ : XH s₁ (dp s₀ + BitVec.ofNat 64 o) (kp' s₀) (16 * (n / 16)) := by
    have := xh hp (by rw [k₁.rd, hrd]) (by rw [k₁.wr, hwr]) (o := o) (a := 0) (m := 16 * (n / 16))
      (by omega) (by omega)
    simpa only [Nat.add_zero, BitVec.add_zero] using this
  refine WP.seq (WP.mono (guarded_ok (w := 16) (by omega) x11₁ x9₁ x10₁
    fun j hj s h => step16_ok hh₁ hj h) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (WP.withSp (rest_ok (s := s₂) hn' (by
      rw [h₂.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
        k₁.cs _ (by decide) (by decide), hx23]))) fun s₃ ⟨⟨x11₃, g₃, m₃, rd₃, wr₃⟩, sp₃⟩ => ?_)
  have hh₃ : XH s₃ (dp s₀ + BitVec.ofNat 64 (o + 16 * (n / 16)))
      (kp' s₀ + BitVec.ofNat 64 (16 * (n / 16))) (1 * (n % 16)) :=
    xh hp (by rw [rd₃, h₂.rd, k₁.rd, hrd]) (by rw [wr₃, h₂.wr, k₁.wr, hwr]) (by omega) (by omega)
  refine WP.mono (guarded_ok (w := 1) (by omega) x11₃ (by rw [g₃ _ (by decide), h₂.x9, add_ofNat])
    (by rw [g₃ _ (by decide), h₂.x10]) fun j hj s h => step1_ok hh₃ hj h) fun s₄ h₄ => ?_
  have m₁ : s₁.mem = s.mem := k₁.mem_eq
  have hn16 : 16 * (n / 16) + n % 16 = n := Nat.div_add_mod _ _
  have F : Frame [⟨dp s₀ + BitVec.ofNat 64 o, n⟩] s.mem s₄.mem := by
    rw [← m₁]
    refine (h₂.frame.sub fun r hr => ?_).trans ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · rw [← m₃]
      exact h₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [← add_ofNat]
        exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩
  refine ⟨⟨fun r hr h30 => ?_, by rw [h₄.sp, sp₃, h₂.sp, k₁.sp], ?_, ?_, ?_⟩, fun i hi => ?_, F,
    fun r hr => ?_⟩
  · have hpr : ∀ r ∈ preserved, r ∉ [Reg.x9, .x10, .x11, .x12, .x13] := by decide
    have hne : ∀ x ∈ [Reg.x9, .x10, .x11, .x12, .x13], r ≠ x := by
      intro x hx he; subst he; exact hpr r hr hx
    rw [h₄.keep r (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp)),
      g₃ r (hne _ (by simp)),
      h₂.keep r (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp)),
      k₁.cs r hr h30]
  · rw [h₄.rd, rd₃, h₂.rd, k₁.rd]
  · rw [h₄.wr, wr₃, h₂.wr, k₁.wr]
  · exact F.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩
  · have hs₂ : ∀ k < n, s₂.mem (kp' s₀ + BitVec.ofNat 64 k) = s.mem (kp' s₀ + BitVec.ofNat 64 k) :=
      fun k hk => by
        rw [← m₁]
        exact h₂.frame.bytes (R := ⟨kp' s₀, n⟩) (by
          intro r hr; simp only [List.mem_singleton] at hr; subst hr
          exact (hp.c_d.sub_left (sub_ctx s₀ (k := 128) (n := n) (by omega))).sub_right
            (Offset.sub_base _ (by omega)))
          (show n ≤ 2 ^ 64 by omega) hk
    rw [← add_ofNat]
    by_cases hi' : i < 16 * (n / 16)
    · have e₄ : s₄.mem (dp s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) =
          s₃.mem (dp s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
        h₄.frame.bytes (R := ⟨dp s₀ + BitVec.ofNat 64 o, 16 * (n / 16)⟩) (by
          intro r hr; simp only [List.mem_singleton] at hr; subst hr
          rw [← add_ofNat]
          exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)) (show 16 * (n / 16) ≤ 2 ^ 64 by omega) hi'
      rw [e₄, m₃, h₂.data i hi', m₁]
    · have e : dp s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i =
          dp s₀ + BitVec.ofNat 64 (o + 16 * (n / 16)) + BitVec.ofNat 64 (i - 16 * (n / 16)) := by
        rw [add_ofNat, add_ofNat]; congr 2; omega
      have e' : kp' s₀ + BitVec.ofNat 64 (16 * (n / 16)) + BitVec.ofNat 64 (i - 16 * (n / 16)) =
          kp' s₀ + BitVec.ofNat 64 i := by
        rw [add_ofNat]; congr 2; omega
      have hd := h₄.data (i - 16 * (n / 16)) (by omega)
      rw [← e, e', m₃] at hd
      rw [hd, hs₂ i hi]
      congr 1
      rw [← m₁]
      exact h₂.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains, Mem.sub_ofNat_toNat _ (show i < 2 ^ 64 by omega)] at hc
        omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h10, h11, h12, h13⟩ := hr
    rw [h₄.keep r h9 h10 h11 h12 h13, g₃ r h11, h₂.keep r h9 h10 h11 h12 h13, gs₁ r h9 h10 h11]

theorem xorKs_ok {s₀ s : State} (hp : APre e s₀) (hL : L s₀ ≤ 256) (hx21 : s.gpr .x21 = cx s₀)
    (hx22 : s.gpr .x22 = dp s₀) (hx23 : s.gpr .x23 = s₀.gpr .x5) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    WP isa xorKs s fun s' => Kept [dR s₀] s s' ∧ ∀ i < L s₀,
      s'.mem (dp s₀ + BitVec.ofNat 64 i) = s.mem (dp s₀ + BitVec.ofNat 64 i) ^^^
        s.mem (kp' s₀ + BitVec.ofNat 64 i) := by
  refine (xorKsAt_ok hp (o := 0) hL (by omega) hx21 (by rw [hx22, BitVec.add_zero])
    (by rw [hx23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hrd hwr).mono
    fun s' ⟨k, d, _, _⟩ => ⟨k, fun i hi => by simpa only [Nat.zero_add] using d i hi⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Short
