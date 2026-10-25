module

import VerifiedGarbage.Proof.Blowfish.RISCV64.Lookup
import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
public import VerifiedGarbage.Proof.Blowfish.RISCV64.Run
public import VerifiedGarbage.Proof.Blowfish.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Blowfish
public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

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
  refine WP.ite (decide (c + 1 = L)) (by rw [tmp, Steps.eval_zero, u12, ofNat_sub_beq (by omega) hL]) (fun h => ?_)
    (fun h => ?_)
  · have e : c + 1 = L := by simpa using h
    refine WP.mono (WP.keep [.t1] (Q := fun t => t.gpr .t1 = 0#64 ∧ t.mem = u.mem) (by brun)
      (by decide) rfl) fun t ⟨⟨t9, tm⟩, tk⟩ => ⟨by rw [tk.gpr (by decide), u10], ?_, by rw [tm, um],
        (uk.trans tk).mono (by decide)⟩
    rw [t9, e, Nat.mod_self]
  · have e : c + 1 ≠ L := by simpa using h
    exact WP.block_nil ⟨u10, by rw [u9, Nat.mod_eq_of_lt (by omega)], um, uk⟩

theorem lo_shl8 (x : BitVec 64) : lo (x <<< 8) = lo x <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    show i < 64 by omega, show i - 8 < 32 by omega]

theorem lo_byte (b : BitVec 8) : lo (b.setWidth 64) = b.zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth]
  by_cases h : i < 8 <;> simp [h, show i < 64 by omega]

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
  have step : ∀ (t : State) (m : Nat), Keep [.t1, .t2, .t3, .t4] s t → t.mem = s.mem →
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
  have hlen : (bytesAt s.mem K L).length = L := by simp [bytesAt]
  apply WP.seq
  refine step t₀ 0 (k₀.mono (by decide)) m₀ (by rw [k₀.gpr (by decide), E.t1, Nat.add_zero]) fun t₁ a₁ b₁ c₁ d₁ => ?_
  apply WP.seq
  refine step t₁ 1 c₁ d₁ b₁ fun t₂ a₂ b₂ c₂ d₂ => ?_
  apply WP.seq
  refine step t₂ 2 c₂ d₂ b₂ fun t₃ a₃ b₃ c₃ d₃ => ?_
  apply WP.seq
  refine step t₃ 3 c₃ d₃ b₃ fun t₄ a₄ b₄ c₄ d₄ => ?_
  have kw : lo (t₄.gpr .t2) = keyWord (bytesAt s.mem K L) i := by
    rw [a₄, a₃, a₂, a₁, a₀, keyWord_eq, hlen]
    simp only [lo_or, lo_shl8, lo_byte, lo_zero]
    rfl
  have r8₄ : t₄.gpr .a6 = S + BitVec.ofNat 64 (4096 + 4 * i) := by rw [c₄.gpr (by decide), E.a6]
  have r17₄ : t₄.gpr .t5 = s.gpr .t5 := c₄.gpr (by decide)
  refine WP.mono (WP.keep [.a6, .t3, .t5] (Q := fun t =>
      t.mem = s.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * i))
        (s.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i) ∧
      t.gpr .a6 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) ∧ t.gpr .t5 = s.gpr .t5 - 1#64) ?_
    (by decide) rfl) fun t ⟨⟨tm, t8, t17⟩, tk⟩ => ⟨tm, ?_, t8, t17, (c₄.trans tk).mono (by decide)⟩
  · have hP : InRegions (t₄.rd ++ t₄.wr) (S + BitVec.ofNat 64 (4096 + 4 * i)) 4 := by
      rw [c₄.2.1, c₄.2.2]; obtain ⟨r, hr, hc⟩ := E.wrP; exact ⟨r, List.mem_append_right _ hr, hc⟩
    have hW : InRegions t₄.wr (S + BitVec.ofNat 64 (4096 + 4 * i)) 4 := by rw [c₄.2.2]; exact E.wrP
    brun [r8₄, r17₄, d₄, hP, hW, E.al]
    refine ⟨?_, ?_⟩
    · rw [lo32_xor, lo32_ext, ← kw]
    · rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]
      congr 2
  · rw [tk.gpr (by decide), b₄, show 4 * i + (3 + 1) = 4 * (i + 1) by omega]

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
  have W : KeyWordEnv S K L i u := by
    refine ⟨hi, E.L0, E.L64, by rw [hrd, hwr]; exact E.key, by rw [I.keep.gpr (by decide)]; exact E.a0,
      by rw [I.keep.gpr (by decide)]; exact E.a1, I.a6, I.t1, ?_, al_add E.al (by omega) (by omega)⟩
    rw [hwr]; exact E.wrS _ _ (by omega) (by omega)
  refine WP.mono (keyWord_run W) fun u' ⟨m', r9', r8', r17', k'⟩ => ?_
  have hT : u.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      s₀.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 :=
    I.frame.readW (r := ⟨S + BitVec.ofNat 64 (4096 + 4 * i), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [← Offset.add_add]
        exact Offset.disjoint (S + BitVec.ofNat 64 4096) (d := 4 * i) (n := 4) (e := 0) (k := 4 * i)
          (.inr (by omega)) (by omega) (by omega) |> fun h => by rwa [BitVec.add_zero] at h) (by decide)
  have hB : bytesAt u.mem K L = bytesAt s₀.mem K L :=
    bytesAt_frame I.frame fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact E.keyS c hc (Offset.sub_base S (d := 4096) (n := 4 * i) (k := 4168) (by omega) _ hcon)
  have r17'' : u'.gpr .t5 = BitVec.ofNat 64 (18 - (i + 1)) := by
    rw [r17', I.t5]; apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨⟨by omega, r9', r8', r17'', fun j hj => ?_, ?_, (I.keep.trans k').mono (by decide)⟩, r17''⟩
  · rw [m', hT, hB]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep S (by omega) (by omega) (by omega)) (by decide)]
      exact I.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m']
    refine Frame.writeW (Frame.sub I.frame fun r hr => ⟨⟨S + BitVec.ofNat 64 4096, 4 * (i + 1)⟩,
      List.mem_singleton_self _, ?_⟩) (List.mem_singleton_self _) _ ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega)
    · rw [← Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)

theorem keyP_run {S K : Addr} {L : Nat} {s₀ : State} (E : KeyPEnv S K L s₀) :
    WP isa keyP s₀ (KeyPInv S K L s₀ 18) := by
  unfold keyP
  apply WP.seq
  refine WP.mono (WP.keep [.a6, .t1, .t5] (Q := fun t => t.gpr .t1 = 0#64 ∧
      t.gpr .a6 = S + BitVec.ofNat 64 4096 ∧ t.gpr .t5 = BitVec.ofNat 64 18 ∧ t.mem = s₀.mem)
    (by
      brun [E.a7, pOff]
      rw [Offset.add_add, Offset.add_add]) (by decide) rfl) fun s₁ ⟨⟨a, b, c, d⟩, k⟩ => ?_
  have I₀ : KeyPInv S K L s₀ 0 s₁ :=
    ⟨by omega, by rw [a]; simp, b, c, fun j hj => absurd hj (by omega), by rw [d]; exact Frame.refl _ _,
      k.mono (by decide)⟩
  refine WP.loop (M := isa) (fun m u => ∃ i, i < 18 ∧ m = 18 - i ∧ KeyPInv S K L s₀ i u)
    ?_ 18 s₁ ⟨0, by omega, rfl, I₀⟩
  intro m u ⟨i, hi, hm, I⟩
  refine WP.mono (keyP_step E hi I) fun u' ⟨I', z'⟩ => ?_
  rw [Steps.eval_nonzero, z', ofNat_bne_zero' (by omega)]
  by_cases h : i + 1 = 18
  · left; exact ⟨by simp [h], h ▸ I'⟩
  · right
    exact ⟨by simp; omega, 18 - (i + 1), by omega, i + 1, by omega, rfl, I'⟩

end VG.Proof.Blowfish.RISCV64
