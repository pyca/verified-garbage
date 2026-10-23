module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Lookup
public import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Blowfish on PPC64LE, key expansion: the keyed P-array

`keyP_run`: the 18 P-array entries XORed in place with the key's words,
cycling through the key's bytes.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

theorem ofNat_sub_beq {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c == 0#64) = decide (a = c) := by
  have := ofNat_sub_bne ha hc
  simp only [bne] at this
  cases h : (BitVec.ofNat 64 a - BitVec.ofNat 64 c == 0#64) <;> rw [h] at this <;> cases e : decide (a = c) <;>
    simp_all

theorem keyByte_run (s : State) {K : Addr} {L c : Nat} (hc : c < L) (hL : L < 2 ^ 64)
    (hK : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 c) 1) (h3 : s.gpr .r3 = K)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 L) (h9 : s.gpr .r9 = BitVec.ofNat 64 c) :
    WP isa keyByte s fun t =>
      t.gpr .r10 = (s.gpr .r10 <<< 8) ||| (s.mem (K + BitVec.ofNat 64 c)).setWidth 64 ∧
      t.gpr .r9 = BitVec.ofNat 64 ((c + 1) % L) ∧ t.mem = s.mem ∧ Keep [.r9, .r10, .r11, .r12] s t := by
  unfold keyByte
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r10, .r11, .r12] (Q := fun t =>
      t.gpr .r10 = (s.gpr .r10 <<< 8) ||| (s.mem (K + BitVec.ofNat 64 c)).setWidth 64 ∧
      t.gpr .r9 = BitVec.ofNat 64 (c + 1) ∧ t.gpr .r12 = BitVec.ofNat 64 (c + 1) - BitVec.ofNat 64 L ∧
      t.mem = s.mem) ?_ (by decide) rfl) fun u ⟨⟨u10, u9, u12, um⟩, uk⟩ => ?_
  · brun [h3, h4, h9, hK]
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
    exact ⟨rfl, rfl⟩
  refine WP.ite (decide (c + 1 = L)) (by rw [tmp, eval_zero, u12, ofNat_sub_beq (by omega) hL]) (fun h => ?_)
    (fun h => ?_)
  · have e : c + 1 = L := by simpa using h
    refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = 0#64 ∧ t.mem = u.mem) (by brun)
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

/-- What a keyed P-array entry needs: entry `i` writable at `r8`, the key's
bytes readable at `r3`, its length in `r4` and the next byte's offset in
`r9`. -/
structure KeyWordEnv (S K : Addr) (L i : Nat) (s : State) : Prop where
  lt : i < 18
  L0 : 0 < L
  L64 : L < 2 ^ 64
  key : ∀ c < L, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 c) 1
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 L
  r8 : s.gpr .r8 = S + BitVec.ofNat 64 (4096 + 4 * i)
  r9 : s.gpr .r9 = BitVec.ofNat 64 ((4 * i) % L)
  wrP : InRegions s.wr (S + BitVec.ofNat 64 (4096 + 4 * i)) 4

/-- The registers the P-array loop writes. -/
def keyPRegs : List Reg := [.r8, .r9, .r10, .r11, .r12, .r17]

theorem keyWord_run {S K : Addr} {L i : Nat} {s : State} (E : KeyWordEnv S K L i s) :
    WP isa Impl.Blowfish.PPC64LE.keyWord s fun t =>
      t.mem = s.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * i))
        (s.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i) ∧
      t.gpr .r9 = BitVec.ofNat 64 ((4 * (i + 1)) % L) ∧
      t.gpr .r8 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) ∧ t.gpr .r17 = s.gpr .r17 - 1#64 ∧
      Keep keyPRegs s t := by
  have hL0 := E.L0
  unfold Impl.Blowfish.PPC64LE.keyWord
  apply WP.seq
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = 0#64 ∧ t.mem = s.mem) (by brun)
    (by decide) rfl) fun t₀ ⟨⟨a₀, m₀⟩, k₀⟩ => ?_
  have step : ∀ (t : State) (m : Nat), Keep [.r9, .r10, .r11, .r12] s t → t.mem = s.mem →
      t.gpr .r9 = BitVec.ofNat 64 ((4 * i + m) % L) →
      ∀ {Q : State → Prop}, (∀ t', t'.gpr .r10 = (t.gpr .r10 <<< 8) |||
        ((bytesAt s.mem K L).getD ((4 * i + m) % L) 0).setWidth 64 →
        t'.gpr .r9 = BitVec.ofNat 64 ((4 * i + (m + 1)) % L) →
        Keep [.r9, .r10, .r11, .r12] s t' → t'.mem = s.mem → Q t') →
      WP isa keyByte t Q := by
    intro t m kt mt h9 Q k
    refine WP.mono (keyByte_run t (K := K) (Nat.mod_lt _ hL0) E.L64 (by rw [kt.2.1, kt.2.2]; exact E.key _ (Nat.mod_lt _ hL0))
      (by rw [kt.gpr (by decide)]; exact E.r3) (by rw [kt.gpr (by decide)]; exact E.r4) h9)
      fun t' ⟨a, b, c, d⟩ => k t' ?_ ?_ ((kt.trans d).mono (by decide)) (c.trans mt)
    · rw [a, bytesAt_getD _ _ (Nat.mod_lt _ hL0), mt]
    · rw [b, mod_succ _ _ hL0, Nat.add_assoc]
  have hlen : (bytesAt s.mem K L).length = L := by simp [bytesAt]
  apply WP.seq
  refine step t₀ 0 (k₀.mono (by decide)) m₀ (by rw [k₀.gpr (by decide), E.r9, Nat.add_zero]) fun t₁ a₁ b₁ c₁ d₁ => ?_
  apply WP.seq
  refine step t₁ 1 c₁ d₁ b₁ fun t₂ a₂ b₂ c₂ d₂ => ?_
  apply WP.seq
  refine step t₂ 2 c₂ d₂ b₂ fun t₃ a₃ b₃ c₃ d₃ => ?_
  apply WP.seq
  refine step t₃ 3 c₃ d₃ b₃ fun t₄ a₄ b₄ c₄ d₄ => ?_
  have kw : lo (t₄.gpr .r10) = keyWord (bytesAt s.mem K L) i := by
    rw [a₄, a₃, a₂, a₁, a₀, keyWord_eq, hlen]
    simp only [lo_or, lo_shl8, lo_byte, lo_zero]
    rfl
  have r8₄ : t₄.gpr .r8 = S + BitVec.ofNat 64 (4096 + 4 * i) := by rw [c₄.gpr (by decide), E.r8]
  have r17₄ : t₄.gpr .r17 = s.gpr .r17 := c₄.gpr (by decide)
  refine WP.mono (WP.keep [.r8, .r11, .r17] (Q := fun t =>
      t.mem = s.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * i))
        (s.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i) ∧
      t.gpr .r8 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) ∧ t.gpr .r17 = s.gpr .r17 - 1#64) ?_
    (by decide) rfl) fun t ⟨⟨tm, t8, t17⟩, tk⟩ => ⟨tm, ?_, t8, t17, (c₄.trans tk).mono (by decide)⟩
  · have hP : InRegions (t₄.rd ++ t₄.wr) (S + BitVec.ofNat 64 (4096 + 4 * i)) 4 := by
      rw [c₄.2.1, c₄.2.2]; obtain ⟨r, hr, hc⟩ := E.wrP; exact ⟨r, List.mem_append_right _ hr, hc⟩
    have hW : InRegions t₄.wr (S + BitVec.ofNat 64 (4096 + 4 * i)) 4 := by rw [c₄.2.2]; exact E.wrP
    brun [r8₄, r17₄, d₄, hP, hW]
    refine ⟨?_, ?_⟩
    · simp only [lo_xor, lo_ext, kw]
    · rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]
      congr 2
  · rw [tk.gpr (by decide), b₄, show 4 * i + (3 + 1) = 4 * (i + 1) by omega]

/-- What the P-array loop needs, of the state it starts in. -/
structure KeyPEnv (S K : Addr) (L : Nat) (s : State) : Prop where
  L0 : 0 < L
  L64 : L < 2 ^ 64
  key : ∀ c < L, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 c) 1
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 L
  r5 : s.gpr .r5 = S
  wrS : (⟨S, 4168⟩ : Region) ∈ s.wr
  keyS : ∀ c < L, ¬ (⟨S, 4168⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1

/-- After `i` entries. -/
structure KeyPInv (S K : Addr) (L : Nat) (s₀ : State) (i : Nat) (u : State) : Prop where
  le : i ≤ 18
  r9 : u.gpr .r9 = BitVec.ofNat 64 ((4 * i) % L)
  r8 : u.gpr .r8 = S + BitVec.ofNat 64 (4096 + 4 * i)
  r17 : u.gpr .r17 = BitVec.ofNat 64 (18 - i)
  done : ∀ j < i, u.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    s₀.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * j)) 32 ^^^ keyWord (bytesAt s₀.mem K L) j
  frame : Frame [⟨S + BitVec.ofNat 64 4096, 4 * i⟩] s₀.mem u.mem
  keep : Keep keyPRegs s₀ u

theorem keyP_step {S K : Addr} {L : Nat} {s₀ : State} (E : KeyPEnv S K L s₀) {i : Nat} (hi : i < 18)
    {u : State} (I : KeyPInv S K L s₀ i u) :
    WP isa Impl.Blowfish.PPC64LE.keyWord u (fun u' => KeyPInv S K L s₀ (i + 1) u' ∧
      u'.gpr .r17 = BitVec.ofNat 64 (18 - (i + 1))) := by
  have hrd : u.rd = s₀.rd := I.keep.2.1
  have hwr : u.wr = s₀.wr := I.keep.2.2
  have W : KeyWordEnv S K L i u := by
    refine ⟨hi, E.L0, E.L64, by rw [hrd, hwr]; exact E.key, by rw [I.keep.gpr (by decide)]; exact E.r3,
      by rw [I.keep.gpr (by decide)]; exact E.r4, I.r8, I.r9, ?_⟩
    rw [hwr]; exact ⟨_, E.wrS, Offset.contains_base S (by omega) (by omega)⟩
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
  have r17'' : u'.gpr .r17 = BitVec.ofNat 64 (18 - (i + 1)) := by
    rw [r17', I.r17]; apply BitVec.eq_of_toNat_eq; simp; omega
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
  refine WP.mono (WP.keep [.r8, .r9, .r17] (Q := fun t => t.gpr .r9 = 0#64 ∧
      t.gpr .r8 = S + BitVec.ofNat 64 4096 ∧ t.gpr .r17 = BitVec.ofNat 64 18 ∧ t.mem = s₀.mem)
    (by brun [E.r5, pOff]) (by decide) rfl) fun s₁ ⟨⟨a, b, c, d⟩, k⟩ => ?_
  have I₀ : KeyPInv S K L s₀ 0 s₁ :=
    ⟨by omega, by rw [a]; simp, b, c, fun j hj => absurd hj (by omega), by rw [d]; exact Frame.refl _ _,
      k.mono (by decide)⟩
  refine WP.loop (M := isa) (fun m u => ∃ i, i < 18 ∧ m = 18 - i ∧ KeyPInv S K L s₀ i u)
    ?_ 18 s₁ ⟨0, by omega, rfl, I₀⟩
  intro m u ⟨i, hi, hm, I⟩
  refine WP.mono (keyP_step E hi I) fun u' ⟨I', z'⟩ => ?_
  rw [cnt, eval_nonzero, z', ofNat_bne_zero (by omega)]
  by_cases h : i + 1 = 18
  · left; exact ⟨by simp [h], h ▸ I'⟩
  · right
    exact ⟨by simp; omega, 18 - (i + 1), by omega, i + 1, by omega, rfl, I'⟩

end VG.Proof.Blowfish.PPC64LE
