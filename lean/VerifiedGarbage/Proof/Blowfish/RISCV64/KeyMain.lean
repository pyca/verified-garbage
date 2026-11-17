module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Ecb
public import VerifiedGarbage.Proof.Blowfish.RISCV64.Run
public import VerifiedGarbage.Spec.Blowfish
public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Blowfish.RISCV64.Cipher
public import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Blowfish.Schedule
public import VerifiedGarbage.Impl.Blowfish.Table
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-! ### `Blowfish.RISCV64.KeyInit`, which only this module used -/

section

/-!
# Blowfish on RISC-V, key expansion: the initial schedule

`initSteps_run`: the 1042 words of the initial schedule's image, as
immediates, into the frame at `t0`; `table_byte`: its bytes are the image's.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64

theorem initWord32_byte (i : Nat) {b : Nat} (hb : b < 4) :
    (initWord32 i).extractLsb' (8 * b) 8 = Impl.Blowfish.initByte (4 * i + b) := by
  simp only [initWord32, List.range, List.range.loop, List.foldl_cons, List.foldl_nil]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) [hj, decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge]

theorem flatMap_range_succ {α : Type} (f : Nat → List α) (k : Nat) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- An aligned word's offset of an aligned base. -/
theorem al4 {p : Addr} (hp : p.toNat % 4 = 0) (d : Nat) (hd : 4 * d < 2 ^ 64) :
    (p + BitVec.ofNat 64 (4 * d)).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * d) hd]
  have := p.isLt
  omega_using [hp]

theorem initStep_run (u : State) {S : Addr} {i : Nat} (hi : i < 1042)
    (h0 : u.gpr .t0 = S + BitVec.ofNat 64 (4 * i)) (hal : S.toNat % 4 = 0)
    (hw : InRegions u.wr (S + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (initStep i)) u fun t =>
      t.mem = u.mem.writeW (S + BitVec.ofNat 64 (4 * i)) (initWord32 i) ∧
      t.gpr .t0 = S + BitVec.ofNat 64 (4 * (i + 1)) ∧ Keep [.t4, .t0] u t := by
  have ha := al4 hal i (by omega_using [hi])
  refine WP.mono (WP.keep [.t4, .t0] (Q := fun t =>
    t.mem = u.mem.writeW (S + BitVec.ofNat 64 (4 * i)) (initWord32 i) ∧
      t.gpr .t0 = S + BitVec.ofNat 64 (4 * (i + 1))) ?_ (by rfl) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold initStep
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.li32_ok (d := .t4) (initWord32 i)) fun v e => ?_
  subst e
  brun [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, h0, hw, ha, lo_sext]
  rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add, show 4 * i + 4 = 4 * (i + 1) by omega_using []]

/-- The first `k` words. -/
theorem initSteps_run {S : Addr} {t : State} (h0 : t.gpr .t0 = S) (hal : S.toNat % 4 = 0)
    (hW : ∀ i < 1042, InRegions t.wr (S + BitVec.ofNat 64 (4 * i)) 4) :
    ∀ k ≤ 1042, WP isa (.block ((List.range k).flatMap initStep)) t fun t' =>
      (∀ i < k, t'.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = initWord32 i) ∧
      t'.gpr .t0 = S + BitVec.ofNat 64 (4 * k) ∧
      Frame [⟨S, 4168⟩] t.mem t'.mem ∧ Keep [.t4, .t0] t t'
  | 0, _ => WP.block_nil ⟨fun i hi => absurd hi (by omega_using []), by rw [h0]; simp, Frame.refl _ _, Keep.refl _ _⟩
  | k + 1, hk => by
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (initSteps_run h0 hal hW k (by omega_using [hk])) fun u ⟨d, p, f, kp⟩ => ?_
    refine WP.mono (initStep_run u (i := k) (by omega_using [hk]) p hal (by rw [kp.2.2]; exact hW k (by omega_using [hk])))
      fun v ⟨m, pv, kv⟩ => ⟨fun i hi => ?_, pv, ?_, (kp.trans kv).mono (by decide)⟩
    · rw [m]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep S (by omega_using [hi]) (by omega_arith) (by omega_using [hk])) (by decide)]
        exact d i hi
      · exact Mem.readW_writeW_self32 _ _ _
    · rw [m]
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base S (by omega_using [hk]) (by omega_using [hk]))

/-- The table's bytes are the initial schedule's. -/
theorem table_byte {m : Mem} {T : Addr}
    (held : ∀ i < 1042, m.readW (T + BitVec.ofNat 64 (4 * i)) 32 = initWord32 i)
    {o : Nat} (ho : o < 4168) : m (T + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := by
  have e := initWord32_byte (o / 4) (b := o % 4) (Nat.mod_lt _ (by decide))
  rw [show 4 * (o / 4) + o % 4 = o by omega_using []] at e
  rw [← e, ← held _ (by omega_using [ho]), ← Mem.readW_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show 4 * (o / 4) + o % 4 = o by omega_using []]

end VG.Proof.Blowfish.RISCV64

end

end

/-! ### `Blowfish.RISCV64.KeyP`, which only this module used -/

section

/-!
# Blowfish on RISC-V, key expansion: the keyed P-array

`keyP_run`: the 18 P-array entries XORed in place with the key's words,
cycling through the key's bytes.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem ofNat_sub_beq {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c == (0 : BitVec 64)) = decide (a = c) := by
  have := ofNat_sub_bne ha hc
  simp only [bne] at this
  cases h : (BitVec.ofNat 64 a - BitVec.ofNat 64 c == (0 : BitVec 64)) <;> rw [h] at this <;> cases e : decide (a = c) <;>
    simp_all

theorem keyByte_run (s : State) {K : Addr} {L c : Nat} (hc : c < L) (hL : L < 2 ^ 64)
    (hK : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 c) 1) (h3 : s.gpr .a0 = K)
    (h4 : s.gpr .a1 = BitVec.ofNat 64 L) (h9 : s.gpr .t1 = BitVec.ofNat 64 c) :
    WP isa keyByte s fun t =>
      t.gpr .t2 = (s.gpr .t2 <<< 8) ||| (s.mem (K + BitVec.ofNat 64 c)).setWidth 64 ∧
      t.gpr .t1 = BitVec.ofNat 64 ((c + 1) % L) ∧ t.mem = s.mem ∧ Keep [.t1, .t2, .t3, .t4] s t := by
  unfold keyByte
  apply WP.seq
  refine WP.mono (WP.keep [.t1, .t2, .t3, .t4] (Q := fun t =>
      t.gpr .t2 = (s.gpr .t2 <<< 8) ||| (s.mem (K + BitVec.ofNat 64 c)).setWidth 64 ∧
      t.gpr .t1 = BitVec.ofNat 64 (c + 1) ∧ t.gpr .t4 = BitVec.ofNat 64 (c + 1) - BitVec.ofNat 64 L ∧
      t.mem = s.mem) ?_ (by decide) rfl) fun u ⟨⟨u10, u9, u12, um⟩, uk⟩ => ?_
  · brun [h3, h4, h9, hK]
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
    exact ⟨rfl, rfl⟩
  refine WP.ite (decide (c + 1 = L)) (by rw [tmp, Steps.eval_zero, u12, ofNat_sub_beq (by omega_using [hc, hL]) hL]) (fun h => ?_)
    (fun h => ?_)
  · have e : c + 1 = L := by simpa using h
    refine WP.mono (WP.keep [.t1] (Q := fun t => t.gpr .t1 = 0#64 ∧ t.mem = u.mem) (by brun)
      (by decide) rfl) fun t ⟨⟨t9, tm⟩, tk⟩ => ⟨by rw [tk.gpr (by decide), u10], ?_, by rw [tm, um],
        (uk.trans tk).mono (by decide)⟩
    rw [t9, e, Nat.mod_self]
  · have e : c + 1 ≠ L := by simpa using h
    exact WP.block_nil ⟨u10, by rw [u9, Nat.mod_eq_of_lt (by omega_using [hc, e])], um, uk⟩

theorem lo_shl8 (x : BitVec 64) : lo (x <<< 8) = lo x <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    show i < 64 by omega_using [hi], show i - 8 < 32 by omega_using [hi]]

theorem lo_byte (b : BitVec 8) : lo (b.setWidth 64) = b.zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth]
  by_cases h : i < 8 <;> simp [h, show i < 64 by omega_using [hi]]

/-- What a keyed P-array entry needs: entry `i` writable at `a6`, the key's
bytes readable at `a0`, its length in `a1` and the next byte's offset in
`t1`. -/
structure KeyWordEnv (S K : Addr) (L i : Nat) (s : State) : Prop where
  lt : i < 18
  L0 : 0 < L
  L64 : L < 2 ^ 64
  key : ∀ c < L, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 c) 1
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 L
  a6 : s.gpr .a6 = S + BitVec.ofNat 64 (4096 + 4 * i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 ((4 * i) % L)
  wrP : InRegions s.wr (S + BitVec.ofNat 64 (4096 + 4 * i)) 4
  al : (S + BitVec.ofNat 64 (4096 + 4 * i)).toNat % 4 = 0

/-- The registers the P-array loop writes. -/
def keyPRegs : List Reg := [.a6, .t1, .t2, .t3, .t4, .t5]

theorem keyWord_run {S K : Addr} {L i : Nat} {s : State} (E : KeyWordEnv S K L i s) :
    WP isa Impl.Blowfish.RISCV64.keyWord s fun t =>
      t.mem = s.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * i))
        (s.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i) ∧
      t.gpr .t1 = BitVec.ofNat 64 ((4 * (i + 1)) % L) ∧
      t.gpr .a6 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) ∧ t.gpr .t5 = s.gpr .t5 - 1#64 ∧
      Keep keyPRegs s t := by
  have hL0 := E.L0
  unfold Impl.Blowfish.RISCV64.keyWord
  apply WP.seq
  refine WP.mono (WP.keep [.t2] (Q := fun t => t.gpr .t2 = 0#64 ∧ t.mem = s.mem) (by brun)
    (by decide) rfl) fun t₀ ⟨⟨a₀, m₀⟩, k₀⟩ => ?_
  obtain step : ∀ (t : State) (m : Nat), Keep [.t1, .t2, .t3, .t4] s t → t.mem = s.mem →
      t.gpr .t1 = BitVec.ofNat 64 ((4 * i + m) % L) →
      ∀ {Q : State → Prop}, (∀ t', t'.gpr .t2 = (t.gpr .t2 <<< 8) |||
        ((bytesAt s.mem K L).getD ((4 * i + m) % L) 0).setWidth 64 →
        t'.gpr .t1 = BitVec.ofNat 64 ((4 * i + (m + 1)) % L) →
        Keep [.t1, .t2, .t3, .t4] s t' → t'.mem = s.mem → Q t') →
      WP isa keyByte t Q := by
    intro t m kt mt h9 Q k
    refine WP.mono (keyByte_run t (K := K) (Nat.mod_lt _ hL0) E.L64 (by rw [kt.2.1, kt.2.2]; exact E.key _ (Nat.mod_lt _ hL0))
      (by rw [kt.gpr (by decide)]; exact E.a0) (by rw [kt.gpr (by decide)]; exact E.a1) h9)
      fun t' ⟨a, b, c, d⟩ => k t' ?_ ?_ ((kt.trans d).mono (by decide)) (c.trans mt)
    · rw [a, bytesAt_getD _ _ (Nat.mod_lt _ hL0), mt]
    · rw [b, mod_succ _ _ hL0, Nat.add_assoc]
  obtain hlen : (bytesAt s.mem K L).length = L := by simp [bytesAt]
  apply WP.seq
  refine step t₀ 0 (k₀.mono (by decide)) m₀ (by rw [k₀.gpr (by decide), E.t1, Nat.add_zero]) fun t₁ a₁ b₁ c₁ d₁ => ?_
  apply WP.seq
  refine step t₁ 1 c₁ d₁ b₁ fun t₂ a₂ b₂ c₂ d₂ => ?_
  apply WP.seq
  refine step t₂ 2 c₂ d₂ b₂ fun t₃ a₃ b₃ c₃ d₃ => ?_
  apply WP.seq
  refine step t₃ 3 c₃ d₃ b₃ fun t₄ a₄ b₄ c₄ d₄ => ?_
  obtain kw : lo (t₄.gpr .t2) = keyWord (bytesAt s.mem K L) i := by
    rw [a₄, a₃, a₂, a₁, a₀, keyWord_eq, hlen]
    simp only [lo_or, lo_shl8, lo_byte, lo_zero]
    rfl
  obtain r8₄ : t₄.gpr .a6 = S + BitVec.ofNat 64 (4096 + 4 * i) := by rw [c₄.gpr (by decide), E.a6]
  obtain r17₄ : t₄.gpr .t5 = s.gpr .t5 := c₄.gpr (by decide)
  refine WP.mono (WP.keep [.a6, .t3, .t5] (Q := fun t =>
      t.mem = s.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * i))
        (s.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i) ∧
      t.gpr .a6 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) ∧ t.gpr .t5 = s.gpr .t5 - 1#64) ?_
    (by decide) rfl) fun t ⟨⟨tm, t8, t17⟩, tk⟩ => ⟨tm, ?_, t8, t17, (c₄.trans tk).mono (by decide)⟩
  · have hP : InRegions (t₄.rd ++ t₄.wr) (S + BitVec.ofNat 64 (4096 + 4 * i)) 4 := by
      rw [c₄.2.1, c₄.2.2]; obtain ⟨r, hr, hc⟩ := E.wrP; exact ⟨r, List.mem_append_right _ hr, hc⟩
    obtain hW : InRegions t₄.wr (S + BitVec.ofNat 64 (4096 + 4 * i)) 4 := by rw [c₄.2.2]; exact E.wrP
    brun [r8₄, r17₄, d₄, hP, hW, E.al]
    refine ⟨?_, ?_⟩
    · rw [lo32_xor, lo32_ext, ← kw]
    · rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]
      congr 2
  · rw [tk.gpr (by decide), b₄, show 4 * i + (3 + 1) = 4 * (i + 1) by omega_using []]

/-- What the P-array loop needs, of the state it starts in. -/
structure KeyPEnv (S K : Addr) (L : Nat) (s : State) : Prop where
  L0 : 0 < L
  L64 : L < 2 ^ 64
  key : ∀ c < L, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 c) 1
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 L
  a7 : s.gpr .a7 = S
  wrS : Writable s.wr S
  keyS : ∀ c < L, ¬ (⟨S, 4168⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1
  al : S.toNat % 4 = 0

/-- After `i` entries. -/
structure KeyPInv (S K : Addr) (L : Nat) (s₀ : State) (i : Nat) (u : State) : Prop where
  le : i ≤ 18
  t1 : u.gpr .t1 = BitVec.ofNat 64 ((4 * i) % L)
  a6 : u.gpr .a6 = S + BitVec.ofNat 64 (4096 + 4 * i)
  t5 : u.gpr .t5 = BitVec.ofNat 64 (18 - i)
  done : ∀ j < i, u.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    s₀.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * j)) 32 ^^^ keyWord (bytesAt s₀.mem K L) j
  frame : Frame [⟨S + BitVec.ofNat 64 4096, 4 * i⟩] s₀.mem u.mem
  keep : Keep keyPRegs s₀ u

theorem keyP_step {S K : Addr} {L : Nat} {s₀ : State} (E : KeyPEnv S K L s₀) {i : Nat} (hi : i < 18)
    {u : State} (I : KeyPInv S K L s₀ i u) :
    WP isa Impl.Blowfish.RISCV64.keyWord u (fun u' => KeyPInv S K L s₀ (i + 1) u' ∧
      u'.gpr .t5 = BitVec.ofNat 64 (18 - (i + 1))) := by
  have hrd : u.rd = s₀.rd := I.keep.2.1
  have hwr : u.wr = s₀.wr := I.keep.2.2
  obtain W : KeyWordEnv S K L i u := by
    refine ⟨hi, E.L0, E.L64, by rw [hrd, hwr]; exact E.key, by rw [I.keep.gpr (by decide)]; exact E.a0,
      by rw [I.keep.gpr (by decide)]; exact E.a1, I.a6, I.t1, ?_, al_add E.al (by omega_using []) (by omega_using [hi])⟩
    rw [hwr]; exact E.wrS _ _ (by omega_using [hi]) (by omega_using [])
  refine WP.mono (keyWord_run W) fun u' ⟨m', r9', r8', r17', k'⟩ => ?_
  obtain hT : u.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      s₀.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 :=
    I.frame.readW (r := ⟨S + BitVec.ofNat 64 (4096 + 4 * i), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [← Offset.add_add]
        exact Offset.disjoint (S + BitVec.ofNat 64 4096) (d := 4 * i) (n := 4) (e := 0) (k := 4 * i)
          (.inr (by omega_using [])) (by omega_using [hi]) (by omega_using [hi]) |> fun h => by rwa [BitVec.add_zero] at h) (by decide)
  obtain hB : bytesAt u.mem K L = bytesAt s₀.mem K L :=
    bytesAt_frame I.frame fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact E.keyS c hc (Offset.sub_base S (d := 4096) (n := 4 * i) (k := 4168) (by omega_using [hi]) _ hcon)
  obtain r17'' : u'.gpr .t5 = BitVec.ofNat 64 (18 - (i + 1)) := by
    rw [r17', I.t5]; apply BitVec.eq_of_toNat_eq; simp; omega_using [hi]
  refine ⟨⟨by omega_using [hi], r9', r8', r17'', fun j hj => ?_, ?_, (I.keep.trans k').mono (by decide)⟩, r17''⟩
  · rw [m', hT, hB]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep S (by omega_using [hj]) (by omega_arith) (by omega_using [hi])) (by decide)]
      exact I.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m']
    refine Frame.writeW (Frame.sub I.frame fun r hr => ⟨⟨S + BitVec.ofNat 64 4096, 4 * (i + 1)⟩,
      List.mem_singleton_self _, ?_⟩) (List.mem_singleton_self _) _ ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega_using [])
    · rw [← Offset.add_add]
      exact Offset.contains_base _ (by omega_using []) (by omega_using [hi])

theorem keyP_run {S K : Addr} {L : Nat} {s₀ : State} (E : KeyPEnv S K L s₀) :
    WP isa keyP s₀ (KeyPInv S K L s₀ 18) := by
  unfold keyP
  apply WP.seq
  refine WP.mono (WP.keep [.a6, .t1, .t5] (Q := fun t => t.gpr .t1 = 0#64 ∧
      t.gpr .a6 = S + BitVec.ofNat 64 4096 ∧ t.gpr .t5 = BitVec.ofNat 64 18 ∧ t.mem = s₀.mem)
    (by
      brun [E.a7, pOff]
      rw [Offset.add_add, Offset.add_add]) (by decide) rfl) fun s₁ ⟨⟨a, b, c, d⟩, k⟩ => ?_
  obtain I₀ : KeyPInv S K L s₀ 0 s₁ :=
    ⟨by omega_using [], by rw [a]; simp, b, c, fun j hj => absurd hj (by omega_using []), by rw [d]; exact Frame.refl _ _,
      k.mono (by decide)⟩
  refine WP.loop (M := isa) (fun m u => ∃ i, i < 18 ∧ m = 18 - i ∧ KeyPInv S K L s₀ i u)
    ?_ 18 s₁ ⟨0, by omega_using [], rfl, I₀⟩
  intro m u ⟨i, hi, hm, I⟩
  refine WP.mono (keyP_step E hi I) fun u' ⟨I', z'⟩ => ?_
  rw [Steps.eval_nonzero, z', ofNat_bne_zero' (by omega_using [])]
  by_cases h : i + 1 = 18
  · left; exact ⟨by simp [h], h ▸ I'⟩
  · right
    exact ⟨by simp; omega_using [hi, h], 18 - (i + 1), by omega_using [hi, hm], i + 1, by omega_using [hi, h], rfl, I'⟩

end VG.Proof.Blowfish.RISCV64

end

end

/-! ### `Blowfish.RISCV64.KeyEnc`, which only this module used -/

section

/-!
# Blowfish on RISCV64, key expansion: the encryptions

`encryptP_run` and `encryptS_run`: the 521 encryptions of the key schedule,
each under the schedule as written so far, their outputs into the P-array
and then the S-boxes' planes (`ksIter`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The registers the encryptions write. -/
def encRegs : List Reg := [.a0, .a1, .a3, .a4, .a5, .a6, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- After `j` encryptions, from the state `s₀` before them: the schedule at
`S` and the last output. -/
structure EncInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop where
  sched : scheduleAt u.mem S = (ksIter key j).1
  halves : (lo (u.gpr .a3), lo (u.gpr .a4)) = ((ksIter key j).2.1, (ksIter key j).2.2)
  keep : Keep encRegs s₀ u
  frame : Frame [⟨S, 4168⟩] s₀.mem u.mem

/-- What the encryptions need of the state before them. -/
structure EncEnv (S : Addr) (s₀ : State) : Prop where
  sch : s₀.gpr .a7 = S
  al : S.toNat % 4 = 0
  al8 : S.toNat % 8 = 0
  wS : Writable s₀.wr S

theorem ord_true : ord true = id := rfl

/-- The encryption of the last output. -/
theorem enc_cipher {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} {u : State}
    (I : EncInv key S s₀ j u) :
    WP isa (cipher true) u fun u' =>
      (lo (u'.gpr .a3), lo (u'.gpr .a4)) =
        encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2 ∧
        Keep cRegs u u' ∧ u'.mem = u.mem := by
  obtain LE : LookEnv u := by
    refine ⟨fun o _ ho => ?_, fun o _ ho => ?_, by rw [I.keep.gpr (by decide), E.sch]; exact E.al,
      by rw [I.keep.gpr (by decide), E.sch]; exact E.al8⟩
    · rw [I.keep.gpr (by decide), E.sch, I.keep.2.1, I.keep.2.2]
      obtain ⟨r, hr, hc⟩ := E.wS o 4 ho (by omega_arith)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [I.keep.gpr (by decide), E.sch, I.keep.2.1, I.keep.2.2]
      obtain ⟨r, hr, hc⟩ := E.wS o 8 ho (by omega_arith)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (cipher_run LE true) fun u' ⟨h, k, m⟩ => ⟨?_, k, m⟩
  obtain e1 := congrArg Prod.fst I.halves
  obtain e2 := congrArg Prod.snd I.halves
  simp only at e1 e2
  rw [h, I.keep.gpr (by decide), E.sch, I.sched, ord_true, e1, e2]; rfl

theorem ksIter_step (key : List Byte) {j : Nat} (hj : j < 521) :
    ksIter key (j + 1) =
      (((ksIter key j).1.set (2 * j) (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1
          (by omega_using [hj])).set (2 * j + 1)
          (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 (by omega_using [hj]),
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1,
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2) := by
  rw [ksIter_succ, ksStep, set!_eq_set _ (by omega_using [hj]), set!_eq_set _ (by omega_using [hj])]

/-! ## The P-array -/

theorem storeP_run (u : State) {a : Addr} (h16 : u.gpr .a1 = a) (w0 : InRegions u.wr a 4)
    (w4 : InRegions u.wr (a + BitVec.ofNat 64 4) 4) (al0 : a.toNat % 4 = 0)
    (al4 : (a + BitVec.ofNat 64 4).toNat % 4 = 0) :
    WP isa (.block storeP) u fun t =>
      t.mem = (u.mem.writeW a (lo (u.gpr .a3))).writeW (a + BitVec.ofNat 64 4) (lo (u.gpr .a4)) ∧
      t.gpr .a1 = a + 8#64 ∧ t.gpr .a0 = u.gpr .a0 - 1#64 ∧ Keep [.a1, .a0] u t := by
  refine WP.mono (WP.keep [.a1, .a0] (Q := fun t =>
      t.mem = (u.mem.writeW a (lo (u.gpr .a3))).writeW (a + BitVec.ofNat 64 4) (lo (u.gpr .a4)) ∧
      t.gpr .a1 = a + 8#64 ∧ t.gpr .a0 = u.gpr .a0 - 1#64) ?_ (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold storeP
  brun [h16, w0, w4, al0, al4]

/-- After `j` of the first nine encryptions. -/
structure PInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop extends
    EncInv key S s₀ j u where
  le : j ≤ 9
  ptr : u.gpr .a1 = S + BitVec.ofNat 64 (4096 + 8 * j)
  cnt : u.gpr .a0 = BitVec.ofNat 64 (9 - j)

theorem encP_step {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} (hj : j < 9)
    {u : State} (I : PInv key S s₀ j u) :
    WP isa (.seq (cipher true) (.block storeP)) u fun u' =>
      PInv key S s₀ (j + 1) u' ∧ u'.gpr .a0 = BitVec.ofNat 64 (9 - (j + 1)) := by
  apply WP.seq
  refine WP.mono (enc_cipher E I.toEncInv) fun v ⟨hv, kv, mv⟩ => ?_
  obtain wr : v.wr = s₀.wr := by rw [kv.2.2, I.keep.2.2]
  obtain a0 : S + BitVec.ofNat 64 (4096 + 8 * j) = S + BitVec.ofNat 64 (4096 + 4 * (2 * j)) := by
    congr 2; omega_using []
  obtain a4 : S + BitVec.ofNat 64 (4096 + 8 * j) + BitVec.ofNat 64 4 =
      S + BitVec.ofNat 64 (4096 + 4 * (2 * j + 1)) := Offset.add_add_eq _ (by omega_using [])
  refine WP.mono (storeP_run v (a := S + BitVec.ofNat 64 (4096 + 8 * j)) (by rw [kv.gpr (by decide), I.ptr])
    (by rw [wr, a0]; exact E.wS _ _ (by omega_using [hj]) (by omega_using []))
    (by rw [wr, a4]; exact E.wS _ _ (by omega_using [hj]) (by omega_using []))
    (by rw [a0, show 4096 + 4 * (2 * j) = 4 * (1024 + 2 * j) by omega_using []]; exact al4 E.al _ (by omega_using [hj]))
    (by rw [a4, show 4096 + 4 * (2 * j + 1) = 4 * (1024 + 2 * j + 1) by omega_using []]; exact al4 E.al _ (by omega_using [hj])))
    fun t ⟨tm, t16, t17, tk⟩ => ?_
  obtain c17 : t.gpr .a0 = BitVec.ofNat 64 (9 - (j + 1)) := by
    rw [t17, kv.gpr (by decide), I.cnt]; apply BitVec.eq_of_toNat_eq; simp; omega_using [hj]
  refine ⟨⟨⟨?_, ?_, ((I.keep.trans kv).trans tk).mono (by decide), ?_⟩, by omega_using [hj], ?_, c17⟩, c17⟩
  · rw [tm, a4, a0, scheduleAt_writeW_P _ _ (by omega_using [hj]), scheduleAt_writeW_P _ _ (by omega_using [hj]), mv, I.sched,
      ksIter_step key (by omega_using [hj]), ← hv]
  · rw [tk.gpr (by decide), tk.gpr (by decide), ksIter_step key (by omega_using [hj]), ← hv]
  · rw [tm, mv]
    refine (I.frame.writeW List.mem_cons_self _ ?_).writeW List.mem_cons_self _ ?_
    · rw [a0]; exact Offset.contains_base S (by omega_using [hj]) (by omega_using [hj])
    · rw [a4]; exact Offset.contains_base S (by omega_using [hj]) (by omega_using [hj])
  · rw [t16, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
    congr 2

theorem encryptP_run {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {u : State}
    (I : EncInv key S s₀ 0 u) :
    WP isa encryptP u (PInv key S s₀ 9) := by
  unfold encryptP
  apply WP.seq
  refine WP.mono (WP.keep [.a1, .a0] (Q := fun t => t.gpr .a1 = S + BitVec.ofNat 64 4096 ∧
      t.gpr .a0 = BitVec.ofNat 64 9 ∧ t.mem = u.mem)
    (by brun [I.keep.gpr (show Reg.a7 ∉ encRegs by decide), E.sch, pOff]; rw [Offset.add_add, Offset.add_add]) (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ?_
  obtain I₀ : PInv key S s₀ 0 t :=
    ⟨⟨by rw [c]; exact I.sched, by rw [k.gpr (by decide), k.gpr (by decide)]; exact I.halves,
      (I.keep.trans k).mono (by decide), by rw [c]; exact I.frame⟩, by omega_using [], a, b⟩
  refine WP.loop (M := isa) (fun m v => ∃ j, j < 9 ∧ m = 9 - j ∧ PInv key S s₀ j v)
    ?_ 9 t ⟨0, by omega_using [], rfl, I₀⟩
  intro m v ⟨j, hj, hm, J⟩
  refine WP.mono (encP_step E hj J) fun v' ⟨J', z'⟩ => ?_
  rw [Steps.eval_nonzero_ofNat _ _ (by omega_using []) z']
  by_cases h : j + 1 = 9
  · left; exact ⟨by simp [h], h ▸ J'⟩
  · right
    exact ⟨by simp; omega_using [hj, h], 9 - (j + 1), by omega_using [hj, hm], j + 1, by omega_using [hj, h], rfl, J'⟩

/-! ## The S-boxes -/

/-- The offset of S-box entry `sDone j`'s first plane. -/
def sOff (j : Nat) : Nat := 1024 * (sDone j / 256) + sDone j % 256

theorem sOff_entry {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) {b k : Nat} (hk : k < 2) :
    sOff j + (256 * b + k) = entryOff (2 * j + k) b := by
  rw [← entryOff_sbox h9 hj k hk, sOff]

theorem sOff_lt {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) : sOff j ≤ 3326 := by
  unfold sOff sDone; omega

theorem sOff_succ {j : Nat} (h9 : 9 ≤ j) :
    sOff (j + 1) = if (sOff j + 2) % 256 = 0 then sOff j + 2 + 768 else sOff j + 2 := by
  unfold sOff sDone; split <;> omega_arith

/-- The bytes of `x` and `y` into the planes of S-box entries `q` and `q + 1`
of the schedule at `S`. -/
def sW (m : Mem) (S : Addr) (q : Nat) (x y : BitVec 32) : Mem :=
  (((((((m.write (S + BitVec.ofNat 64 q) 1 (x.extractLsb' 0 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 256) 1 (x.extractLsb' 8 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 512) 1 (x.extractLsb' 16 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 768) 1 (x.extractLsb' 24 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 1) 1 (y.extractLsb' 0 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 257) 1 (y.extractLsb' 8 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 513) 1 (y.extractLsb' 16 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 769) 1 (y.extractLsb' 24 8)

theorem sW_sched (m : Mem) (S : Addr) {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) (x y : BitVec 32) :
    scheduleAt (sW m S (sOff j) x y) S = ((scheduleAt m S).set (2 * j) x (by omega_using [hj])).set (2 * j + 1) y
      (by omega_using [hj]) := by
  obtain e : ∀ b k, k < 2 → S + BitVec.ofNat 64 (sOff j) + BitVec.ofNat 64 (256 * b + k) =
      S + BitVec.ofNat 64 (entryOff (2 * j + k) b) := fun b k hk => by
    rw [Offset.add_add, sOff_entry h9 hj hk]
  obtain e' : ∀ o b k, k < 2 → o = 256 * b + k → S + BitVec.ofNat 64 (sOff j) + BitVec.ofNat 64 o =
      S + BitVec.ofNat 64 (entryOff (2 * j + k) b) := fun o b k hk ho => by rw [ho]; exact e b k hk
  obtain e0 : S + BitVec.ofNat 64 (sOff j) = S + BitVec.ofNat 64 (entryOff (2 * j + 0) 0) := by
    have := e 0 0 (by decide); rwa [BitVec.add_zero] at this
  unfold sW
  rw [e' 256 1 0 (by decide) rfl, e' 512 2 0 (by decide) rfl, e' 768 3 0 (by decide) rfl,
    e' 1 0 1 (by decide) rfl, e' 257 1 1 (by decide) rfl, e' 513 2 1 (by decide) rfl,
    e' 769 3 1 (by decide) rfl, e0, scheduleAt_write_bytes _ _ (by omega_using [hj]), Nat.add_zero,
    scheduleAt_write_bytes _ _ (by omega_using [hj])]

theorem write1_eq (m : Mem) (a : Addr) (v : BitVec 8) : m.write a 1 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem sW_frame (m : Mem) (S : Addr) {q : Nat} (hq : q + 770 ≤ 4168) (x y : BitVec 32) :
    Frame [⟨S, 4168⟩] m (sW m S q x y) := by
  obtain c : ∀ e, e < 770 → Region.Contains ⟨S, 4168⟩ (S + BitVec.ofNat 64 q + BitVec.ofNat 64 e) (8 / 8) :=
    fun e he => by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hq, he]) (by omega_using [hq, he])
  obtain c0 : Region.Contains ⟨S, 4168⟩ (S + BitVec.ofNat 64 q) (8 / 8) :=
    Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])
  unfold sW
  simp only [write1_eq]
  exact (((((((((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _
    (c 256 (by decide))).writeW List.mem_cons_self _ (c 512 (by decide))).writeW List.mem_cons_self _
    (c 768 (by decide))).writeW List.mem_cons_self _ (c 1 (by decide))).writeW List.mem_cons_self _
    (c 257 (by decide))).writeW List.mem_cons_self _ (c 513 (by decide))).writeW List.mem_cons_self _
    (c 769 (by decide)))

theorem byte0 (g : BitVec 64) : g.setWidth 8 = (lo g).extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi, show i < 32 by omega_using [hi]]

theorem extract_shr (x : BitVec 32) {k : Nat} (hk : k + 8 ≤ 32) :
    (x >>> k).extractLsb' 0 8 = x.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show i < 32 by omega_using [hi], show k + i < 32 by omega_using [hk, hi], Nat.add_comm]

def storeSHead : List Instr :=
  storeEntry xL 0 ++ storeEntry xR 1 ++ [.addi ptr ptr 2, .sub tmp ptr sch, .shift .sll .d tmp tmp 56]

theorem storeSHead_run (u : State) {S : Addr} {q : Nat} (hq : q + 770 ≤ 4168) (h16 : u.gpr .a1 = S + BitVec.ofNat 64 q)
    (h3 : u.gpr .a7 = S) (hw : Writable u.wr S) :
    WP isa (.block storeSHead) u fun t =>
      t.mem = sW u.mem S q (lo (u.gpr .a3)) (lo (u.gpr .a4)) ∧ t.gpr .a1 = S + BitVec.ofNat 64 (q + 2) ∧
      t.gpr .t4 = BitVec.ofNat 64 (q + 2) <<< 56 ∧ Keep [.t4, .a1] u t := by
  refine WP.mono (WP.keep [.t4, .a1] (Q := fun t =>
      t.mem = sW u.mem S q (lo (u.gpr .a3)) (lo (u.gpr .a4)) ∧ t.gpr .a1 = S + BitVec.ofNat 64 (q + 2) ∧
      t.gpr .t4 = BitVec.ofNat 64 (q + 2) <<< 56) ?_ (by decide) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  obtain c : ∀ e, e < 770 → InRegions u.wr (S + BitVec.ofNat 64 q + BitVec.ofNat 64 e) 1 :=
    fun e he => by rw [Offset.add_add]; exact hw _ _ (by omega_using [hq, he]) (by omega_using [])
  obtain c0 : InRegions u.wr (S + BitVec.ofNat 64 q) 1 := hw _ _ (by omega_using [hq]) (by omega_using [])
  obtain w256 := c 256 (by decide); have w512 := c 512 (by decide); have w768 := c 768 (by decide)
  obtain w1 := c 1 (by decide); have w257 := c 257 (by decide); have w513 := c 513 (by decide)
  obtain w769 := c 769 (by decide)
  unfold storeSHead storeEntry
  brun [h16, h3, c0, w256, w512, w768, w1, w257, w513, w769]
  refine ⟨?_, ?_, ?_⟩
  · simp only [sW, byte0, lo_sext, extract_shr _ (k := 8) (by decide), extract_shr _ (k := 16) (by decide),
      extract_shr _ (k := 24) (by decide)]
  · rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, Offset.add_add]
  · rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, Offset.add_add, Offset.add_sub_cancel_left]

/-- `n << 56` is zero iff the low byte of `n` is. -/
theorem shl56_beq {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n <<< 56 == (0 : BitVec 64)) = decide (n % 256 = 0) := by
  obtain e : (BitVec.ofNat 64 n <<< 56 = 0#64) ↔ n % 256 = 0 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, 
        Nat.mod_eq_of_lt hn] at this
      omega_using [this]
    · intro h
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, 
        Nat.mod_eq_of_lt hn]
      omega_using [h]
  by_cases h : n % 256 = 0
  · simp [e.mpr h, h]
  · have : ¬ BitVec.ofNat 64 n <<< 56 = 0#64 := fun h' => h (e.mp h')
    simp [this, h]

/-- After `j` encryptions, the first nine into the P-array. -/
structure SInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop extends
    EncInv key S s₀ j u where
  ge : 9 ≤ j
  le : j ≤ 521
  ptr : u.gpr .a1 = S + BitVec.ofNat 64 (sOff j)
  cnt : u.gpr .a0 = BitVec.ofNat 64 (521 - j)

theorem encS_step {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} (hj : j < 521)
    {u : State} (I : SInv key S s₀ j u) :
    WP isa (.seq (cipher true) storeS) u fun u' =>
      SInv key S s₀ (j + 1) u' ∧ u'.gpr .a0 = BitVec.ofNat 64 (521 - (j + 1)) := by
  have h9 := I.ge
  obtain hq := sOff_lt h9 hj
  apply WP.seq
  refine WP.mono (enc_cipher E I.toEncInv) fun v ⟨hv, kv, mv⟩ => ?_
  obtain Kv : Keep encRegs s₀ v := (I.keep.trans kv).mono (by decide)
  unfold storeS
  apply WP.seq
  refine WP.mono (storeSHead_run v (S := S) (q := sOff j) (by omega_using [hq]) (by rw [kv.gpr (by decide), I.ptr])
    (by rw [Kv.gpr (by decide), E.sch]) (by rw [Kv.2.2]; exact E.wS)) fun t ⟨tm, t16, t12, tk⟩ => ?_
  obtain Kt : Keep encRegs s₀ t := (Kv.trans tk).mono (by decide)
  obtain hsch : scheduleAt t.mem S = (ksIter key (j + 1)).1 := by
    rw [tm, sW_sched _ _ h9 hj, mv, I.sched, ksIter_step key hj, ← hv]
  obtain hhalf : (lo (t.gpr .a3), lo (t.gpr .a4)) = ((ksIter key (j + 1)).2.1, (ksIter key (j + 1)).2.2) := by
    rw [tk.gpr (by decide), tk.gpr (by decide), ksIter_step key hj, ← hv]
  obtain hfr : Frame [⟨S, 4168⟩] s₀.mem t.mem := by
    rw [tm, mv]; exact I.frame.trans (sW_frame _ _ (by omega_using [hq]) _ _)
  obtain h17 : t.gpr .a0 = BitVec.ofNat 64 (521 - j) := by
    rw [tk.gpr (by decide), kv.gpr (by decide), I.cnt]
  apply WP.seq
  refine WP.mono (Q := fun (w : State) => w.gpr .a1 = S + BitVec.ofNat 64 (sOff (j + 1)) ∧ w.mem = t.mem ∧
      Keep [.a1] t w) ?_ fun w ⟨w16, wm, wk⟩ => ?_
  · refine WP.ite (decide ((sOff j + 2) % 256 = 0)) (by show isa.eval (.zero .t4) t = _; rw [Steps.eval_zero, t12, shl56_beq (by omega_using [hq])])
      (fun h => ?_) (fun h => ?_)
    · have h' : (sOff j + 2) % 256 = 0 := by simpa using h
      refine WP.mono (WP.keep [.a1] (Q := fun (w : State) =>
        w.gpr .a1 = S + BitVec.ofNat 64 (sOff (j + 1)) ∧ w.mem = t.mem) ?_ (by decide) rfl)
        fun w ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
      brun [t16]
      rw [show (768#64 : BitVec 64) = BitVec.ofNat 64 768 from rfl, Offset.add_add, sOff_succ h9,
        ite_eq_left h']
    · have h' : ¬ (sOff j + 2) % 256 = 0 := by simpa using h
      exact WP.block_nil ⟨by rw [t16, sOff_succ h9, ite_eq_right h'], rfl, Keep.refl _ _⟩
  · have Kw : Keep encRegs s₀ w := (Kt.trans wk).mono (by decide)
    refine WP.mono (WP.keep [.a0] (Q := fun x => x.gpr .a0 = BitVec.ofNat 64 (521 - (j + 1)) ∧
        x.mem = w.mem) ?_ (by decide) rfl) fun x ⟨⟨x17, xm⟩, xk⟩ => ?_
    · brun [wk.gpr (show Reg.a0 ∉ [Reg.a1] by decide), h17]
      apply BitVec.eq_of_toNat_eq; simp; omega_using [hj]
    refine ⟨⟨⟨by rw [xm, wm]; exact hsch, ?_, (Kw.trans xk).mono (by decide), by rw [xm, wm]; exact hfr⟩,
      by omega_using [h9], by omega_using [hj], by rw [xk.gpr (by decide)]; exact w16, x17⟩, x17⟩
    rw [xk.gpr (by decide), xk.gpr (by decide), wk.gpr (by decide), wk.gpr (by decide)]
    exact hhalf

theorem encryptS_run {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {u : State}
    (I : PInv key S s₀ 9 u) :
    WP isa encryptS u (SInv key S s₀ 521) := by
  unfold encryptS
  apply WP.seq
  refine WP.mono (WP.keep [.a1, .a0] (Q := fun t => t.gpr .a1 = S ∧
      t.gpr .a0 = BitVec.ofNat 64 512 ∧ t.mem = u.mem)
    (by brun [I.keep.gpr (show Reg.a7 ∉ encRegs by decide), E.sch, BitVec.or_self]) (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ?_
  obtain I₀ : SInv key S s₀ 9 t :=
    ⟨⟨by rw [c]; exact I.sched, by rw [k.gpr (by decide), k.gpr (by decide)]; exact I.halves,
      (I.keep.trans k).mono (by decide), by rw [c]; exact I.frame⟩, by omega_using [], by omega_using [],
      by rw [a]; simp [sOff, sDone], b⟩
  refine WP.loop (M := isa) (fun m v => ∃ j, 9 ≤ j ∧ j < 521 ∧ m = 521 - j ∧ SInv key S s₀ j v)
    ?_ 512 t ⟨9, by omega_using [], by omega_using [], rfl, I₀⟩
  intro m v ⟨j, hj9, hj, hm, J⟩
  refine WP.mono (encS_step E hj J) fun v' ⟨J', z'⟩ => ?_
  rw [Steps.eval_nonzero_ofNat _ _ (by omega_using []) z']
  by_cases h : j + 1 = 521
  · left; exact ⟨by simp [h], h ▸ J'⟩
  · right
    exact ⟨by simp; omega_using [hj, h], 521 - (j + 1), by omega_using [hj, hm], j + 1, by omega_using [hj9], by omega_using [hj, h], rfl, J'⟩

end VG.Proof.Blowfish.RISCV64

end

end


/-!
# Blowfish on RISC-V: key expansion

`expandKey_wp`: the schedule at `a2` becomes the expansion of the key at
`a0`, built in the frame of 4176 bytes below the stack pointer, copied out,
and the frame zeroed (`Zeroed`) before it is freed.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- What key expansion may assume: the key readable, the schedule writable,
apart from each other and from the 4176 bytes below the stack pointer, and
a valid key length. -/
structure KeyPre (s : State) : Prop where
  valid : validKey (s.gpr .a1).toNat
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩]
  wr : s.wr = [⟨s.gpr .a2, 4168⟩]
  keyS : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a2, 4168⟩
  al : s.sp.toNat % 16 = 0
  sp : 4176 ≤ s.sp.toNat
  stackKey : (⟨s.sp - 4176, 4176⟩ : Region).Disjoint ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
  stackSched : (⟨s.sp - 4176, 4176⟩ : Region).Disjoint ⟨s.gpr .a2, 4168⟩

theorem expandKey_wp {s : State} (h : KeyPre s) :
    WP isa Impl.Blowfish.RISCV64.expandKey s fun s' =>
      scheduleAt s'.mem (s.gpr .a2) = expandKey (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
  have hv := h.valid
  unfold validKey at hv
  obtain hF : frameBase s = s.sp - 4176 := frameBase_eq s
  obtain hFal : (frameBase s).toNat % 16 = 0 := frameBase_al s h.al h.sp
  -- The frame's regions.
  obtain fK : (⟨frameBase s, 4168⟩ : Region).Disjoint ⟨s.gpr .a0, (s.gpr .a1).toNat⟩ :=
    h.stackKey.sub_left (by rw [hF]; exact Region.sub_prefix (by decide))
  obtain fS : (⟨frameBase s, 4168⟩ : Region).Disjoint ⟨s.gpr .a2, 4168⟩ :=
    h.stackSched.sub_left (by rw [hF]; exact Region.sub_prefix (by decide))
  obtain keyIn : ∀ c < (s.gpr .a1).toNat,
      (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Contains (s.gpr .a0 + BitVec.ofNat 64 c) 1 :=
    fun c hc => Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc])
  obtain keyFrame : ∀ {m m' : Mem} {r : Region}, (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint r →
      Frame [r] m m' → bytesAt m' (s.gpr .a0) (s.gpr .a1).toNat = bytesAt m (s.gpr .a0) (s.gpr .a1).toNat :=
    fun hd hf => bytesAt_frame hf fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd _ (keyIn c hc) hcon
  obtain W : Writable (inner s).wr (frameBase s) := frame_writable s
  refine inFrame_wp h.sp ?_
  unfold expandMain initSchedule
  -- The initial schedule.
  apply WP.seq
  rw [show ∀ l : List Instr, Instr.addSp sch 0 :: Instr.addi rowPtr sch 0 :: l =
      ([.addSp sch 0, .addi rowPtr sch 0] : List Instr) ++ l from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.a7, .t0] (Q := fun t => t.gpr .a7 = frameBase s ∧ t.gpr .t0 = frameBase s ∧
      t.mem = s.mem) (by brun [inner_sp, inner_mem]; all_goals rfl) (by decide) rfl)
    fun a ⟨⟨a7, a0, am⟩, ak⟩ => ?_
  refine WP.mono (initSteps_run (S := frameBase s) a0 (by omega_using [hFal]) (fun i hi => by
      rw [ak.2.2]; exact W _ _ (by omega_using [hi]) (by omega_using [])) 1042 (Nat.le_refl _))
    fun t₁ ⟨held, _, F₁, k₁⟩ => ?_
  rw [am] at F₁
  obtain hT : ∀ o < 4168, t₁.mem (frameBase s + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o :=
    fun o ho => table_byte held ho
  obtain B₁ : bytesAt t₁.mem (s.gpr .a0) (s.gpr .a1).toNat = bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat :=
    keyFrame fK.symm F₁
  obtain g₁ : ∀ r, r ∉ [Reg.t4, .t0] → r ∉ [Reg.a7, .t0] → t₁.gpr r = s.gpr r := fun r h1 h2 =>
    (k₁.gpr h1).trans ((ak.gpr h2).trans (by rw [inner_gpr]))
  obtain rd₁ : t₁.rd = s.rd := k₁.2.1.trans ak.2.1
  obtain wr₁ : t₁.wr = (inner s).wr := k₁.2.2.trans ak.2.2
  -- The keyed P-array.
  obtain E : KeyPEnv (frameBase s) (s.gpr .a0) (s.gpr .a1).toNat t₁ := by
    refine ⟨by omega_using [hv], (s.gpr .a1).isLt, fun c hc => ?_, g₁ _ (by decide) (by decide),
      by rw [g₁ _ (by decide) (by decide)]; simp, (k₁.gpr (by decide)).trans a7, by rw [wr₁]; exact W,
      fun c hc hcon => fK _ hcon (keyIn c hc), by omega_using [hFal]⟩
    rw [rd₁, h.rd]; exact ⟨_, List.mem_append_left _ List.mem_cons_self, keyIn c hc⟩
  apply WP.seq
  refine WP.mono (keyP_run E) fun t₂ I₂ => ?_
  obtain hS₂ : ∀ o < 4096, t₂.mem (frameBase s + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := fun o ho => by
    rw [← hT o (by omega_using [ho])]
    refine I₂.frame _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint (frameBase s) (d := o) (n := 1) (e := 4096) (k := 4 * 18) (.inl (by omega_using [ho]))
      (by omega_using [ho]) (by omega_using []) _ (Region.contains_self _ _) hc
  obtain hK₂ : scheduleAt t₂.mem (frameBase s) = keyed (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
    refine keyed_of_mem hS₂ fun i hi => ?_
    rw [I₂.done i hi, table_P hT hi, B₁]
  obtain g₂ : ∀ r, r ∉ keyPRegs → t₂.gpr r = t₁.gpr r := fun r hr => I₂.keep.gpr hr
  -- The setup of the encryptions.
  apply WP.seq
  refine WP.mono (WP.keep [.a3, .a4] (Q := fun t => t.gpr .a3 = 0#64 ∧ t.gpr .a4 = 0#64 ∧ t.mem = t₂.mem)
    (by brun; all_goals rfl) (by decide) rfl) fun t₃ ⟨⟨b₃, c₃, m₃⟩, k₃⟩ => ?_
  obtain wr₃ : t₃.wr = (inner s).wr := by rw [k₃.2.2, I₂.keep.2.2, wr₁]
  obtain EE : EncEnv (frameBase s) t₃ :=
    ⟨by rw [k₃.gpr (by decide), g₂ _ (by decide), (k₁.gpr (by decide))]; exact a7, by omega_using [hFal], by omega_using [hFal],
      by rw [wr₃]; exact W⟩
  obtain I₃ : EncInv (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (frameBase s) t₃ 0 t₃ :=
    ⟨by rw [m₃, hK₂, ksIter_zero], by rw [b₃, c₃, ksIter_zero]; rfl, Keep.refl _ _, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (encryptP_run EE I₃) fun t₄ I₄ => ?_
  apply WP.seq
  refine WP.mono (encryptS_run EE I₄) fun t₅ I₅ => ?_
  obtain g₅ : ∀ r, r ∉ encRegs → r ∉ [Reg.a3, .a4] → r ∉ keyPRegs → r ∉ [Reg.t4, .t0] → r ∉ [Reg.a7, .t0] →
      t₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 =>
    (I₅.keep.gpr h1).trans ((k₃.gpr h2).trans ((g₂ r h3).trans (g₁ r h4 h5)))
  obtain a7₅ : t₅.gpr .a7 = frameBase s := by
    rw [I₅.keep.gpr (by decide), k₃.gpr (by decide), g₂ _ (by decide), k₁.gpr (by decide)]; exact a7
  obtain wr₅ : t₅.wr = (inner s).wr := by rw [I₅.keep.2.2, wr₃]
  obtain rd₅ : t₅.rd = s.rd := by rw [I₅.keep.2.1, k₃.2.1, I₂.keep.2.1, rd₁]
  obtain hK₅ : scheduleAt t₅.mem (frameBase s) = expandKey (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
    rw [I₅.sched, expandKey_eq]
  -- The schedule copied out.
  apply WP.seq
  refine WP.mono (WP.keep [.t0, .t4] (Q := fun t => t.gpr .t0 = frameBase s ∧ t.gpr .t4 = BitVec.ofNat 64 4168 ∧
      t.mem = t₅.mem) (by unfold li4168; brun [a7₅, shl_4168]; all_goals rfl) (by decide) rfl)
    fun c ⟨⟨c0, c4, cm⟩, ck⟩ => ?_
  obtain a2c : c.gpr .a2 = s.gpr .a2 := by
    rw [ck.gpr (by decide)]; exact g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain wrc : c.wr = (inner s).wr := ck.2.2.trans wr₅
  apply WP.seq
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .t0) (dst := .a2) (cnt := .t4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c (N := 4168) (by decide) (by decide) c4
    (fun i hi => by
      rw [c0]; obtain ⟨r, hr, hc⟩ := W i 1 (by omega_using [hi]) (by omega_using [])
      exact ⟨r, List.mem_append_right _ (by rw [wrc]; exact hr), hc⟩)
    (fun i hi => ⟨⟨s.gpr .a2, 4168⟩, by rw [wrc, inner_wr, h.wr]; simp,
      by rw [a2c]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (by rw [a2c, c0]; exact sep_of_disjoint fS.symm))
    fun d ⟨dc, df, dk⟩ => ?_
  rw [a2c, c0, cm] at dc
  rw [a2c] at df
  obtain hKd : scheduleAt d.mem (s.gpr .a2) = expandKey (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
    rw [scheduleAt_copy dc, hK₅]
  obtain a7d : d.gpr .a7 = frameBase s := by rw [dk.gpr (by decide), ck.gpr (by decide)]; exact a7₅
  obtain wrd : d.wr = (inner s).wr := dk.2.2.trans wrc
  -- The frame zeroed.
  unfold wipe
  apply WP.seq
  refine WP.mono (WP.keep [.t1, .t0, .t4] (Q := fun t => t.gpr .t0 = frameBase s ∧
      t.gpr .t4 = BitVec.ofNat 64 522 ∧ t.gpr .t1 = 0#64 ∧ t.mem = d.mem) (by brun [a7d]) (by decide) rfl)
    fun f ⟨⟨f0, f4, f1, fm⟩, fk⟩ => ?_
  refine WP.mono (fillLoop_ok (v := .t1) (ptr := .t0) (cnt := .t4) (by decide) (by decide) (by decide) f
    (N := 522) (by decide) (by decide) f4 (by rw [f0]; omega_using [hFal])
    (fun i hi => by rw [fk.2.2, wrd, f0]; exact frame_in s (by omega_using [hi]) (by omega_using [])))
    fun t ⟨_, tf, _⟩ m u fl => ?_
  rw [f0, fm] at tf
  show scheduleAt m (s.gpr .a2) = _
  -- The `free` loses the frame's bytes, which lie apart from the schedule.
  rw [scheduleAt_eq_of_frame _ fl fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stackSched.sub_left (r₁' := ⟨frameBase s, 4176⟩) (by
        rw [hF]; exact Region.sub_prefix (by decide))).symm,
    scheduleAt_eq_of_frame _ tf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stackSched.sub_left (r₁' := ⟨frameBase s, 8 * 522⟩) (by
        rw [hF]; exact Region.sub_prefix (by decide))).symm, hKd]

end VG.Proof.Blowfish.RISCV64
