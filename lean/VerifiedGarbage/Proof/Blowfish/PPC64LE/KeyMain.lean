module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Blowfish.PPC64LE
public import VerifiedGarbage.Impl.Blowfish.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Blowfish.PPC64LE.Lookup
public import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Blowfish
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Cipher
public import VerifiedGarbage.Proof.Blowfish.KeySched
import VerifiedGarbage.Proof.Blowfish.Schedule
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `Blowfish.PPC64LE.KeyInit`, which only this module used -/

section

/-!
# Blowfish on PPC64LE, key expansion: the initial schedule

`initSteps_run`: the 521 doublewords of the initial schedule's image, as
immediates, into the schedule at `r5`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE

/-- Doubleword `i` of the initial schedule. -/
def initStep (i : Nat) : List Instr :=
  movImm64 tmp (Impl.Blowfish.initWord i) ++ ([.store .d tmp .r5 (8 * i)] : List Instr)

theorem initSchedule_eq : initSchedule = (List.range 521).flatMap initStep := rfl

theorem flatMap_range_succ {α : Type} (f : Nat → List α) (k : Nat) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem initStep_run (u : State) {S : Addr} {i : Nat} (hi : i < 521) (h5 : u.gpr .r5 = S)
    (hw : InRegions u.wr (S + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (initStep i)) u fun t =>
      t.mem = u.mem.writeW (S + BitVec.ofNat 64 (8 * i)) (Impl.Blowfish.initWord i) ∧ Keep [.r12] u t := by
  refine WP.mono (WP.keep [.r12] (Q := fun t =>
    t.mem = u.mem.writeW (S + BitVec.ofNat 64 (8 * i)) (Impl.Blowfish.initWord i)) ?_
    (by rfl) rfl)
    fun t ⟨a, b⟩ => ⟨a, b⟩
  unfold initStep movImm64
  brun [h5, hw, show 8 * i < 32768 by omega_using [hi], show 8 * i % 4 = 0 by omega_using []]
  exact congrArg _ (movImm64_eq _)

/-- The first `k` doublewords. -/
theorem initSteps_run {S : Addr} {t : State} (h5 : t.gpr .r5 = S) (hW : (⟨S, 4168⟩ : Region) ∈ t.wr) :
    ∀ k ≤ 521, WP isa (.block ((List.range k).flatMap initStep)) t fun t' =>
      (∀ i < k, t'.mem.readW (S + BitVec.ofNat 64 (8 * i)) 64 = Impl.Blowfish.initWord i) ∧
      Frame [⟨S, 4168⟩] t.mem t'.mem ∧ Keep [.r12] t t'
  | 0, _ => WP.block_nil ⟨fun i hi => absurd hi (by omega_using []), Frame.refl _ _, Keep.refl _ _⟩
  | k + 1, hk => by
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (initSteps_run h5 hW k (by omega_using [hk])) fun u ⟨d, f, kp⟩ => ?_
    refine WP.mono (initStep_run u (i := k) (by omega_using [hk]) (by rw [kp.gpr (by decide)]; exact h5)
      ⟨_, by rw [kp.2.2]; exact hW, Offset.contains_base S (by omega_using [hk]) (by omega_using [hk])⟩)
      fun v ⟨m, kv⟩ => ⟨fun i hi => ?_, ?_, (kp.trans kv).mono (by decide)⟩
    · rw [m]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep S (by omega_using [hi]) (by omega_arith) (by omega_using [hk])) (by decide)]
        exact d i hi
      · exact Mem.readW_writeW_self64 _ _ _
    · rw [m]
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base S (by omega_using [hk]) (by omega_using [hk]))

end VG.Proof.Blowfish.PPC64LE

end

end

/-! ### `Blowfish.PPC64LE.KeyP`, which only this module used -/

section

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
  refine WP.ite (decide (c + 1 = L)) (by rw [tmp, eval_zero, u12, ofNat_sub_beq (by omega_using [hc, hL]) hL]) (fun h => ?_)
    (fun h => ?_)
  · have e : c + 1 = L := by simpa using h
    refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = 0#64 ∧ t.mem = u.mem) (by brun)
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
  obtain step : ∀ (t : State) (m : Nat), Keep [.r9, .r10, .r11, .r12] s t → t.mem = s.mem →
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
  obtain hlen : (bytesAt s.mem K L).length = L := by simp [bytesAt]
  apply WP.seq
  refine step t₀ 0 (k₀.mono (by decide)) m₀ (by rw [k₀.gpr (by decide), E.r9, Nat.add_zero]) fun t₁ a₁ b₁ c₁ d₁ => ?_
  apply WP.seq
  refine step t₁ 1 c₁ d₁ b₁ fun t₂ a₂ b₂ c₂ d₂ => ?_
  apply WP.seq
  refine step t₂ 2 c₂ d₂ b₂ fun t₃ a₃ b₃ c₃ d₃ => ?_
  apply WP.seq
  refine step t₃ 3 c₃ d₃ b₃ fun t₄ a₄ b₄ c₄ d₄ => ?_
  obtain kw : lo (t₄.gpr .r10) = keyWord (bytesAt s.mem K L) i := by
    rw [a₄, a₃, a₂, a₁, a₀, keyWord_eq, hlen]
    simp only [lo_or, lo_shl8, lo_byte, lo_zero]
    rfl
  obtain r8₄ : t₄.gpr .r8 = S + BitVec.ofNat 64 (4096 + 4 * i) := by rw [c₄.gpr (by decide), E.r8]
  obtain r17₄ : t₄.gpr .r17 = s.gpr .r17 := c₄.gpr (by decide)
  refine WP.mono (WP.keep [.r8, .r11, .r17] (Q := fun t =>
      t.mem = s.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * i))
        (s.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i) ∧
      t.gpr .r8 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) ∧ t.gpr .r17 = s.gpr .r17 - 1#64) ?_
    (by decide) rfl) fun t ⟨⟨tm, t8, t17⟩, tk⟩ => ⟨tm, ?_, t8, t17, (c₄.trans tk).mono (by decide)⟩
  · have hP : InRegions (t₄.rd ++ t₄.wr) (S + BitVec.ofNat 64 (4096 + 4 * i)) 4 := by
      rw [c₄.2.1, c₄.2.2]; obtain ⟨r, hr, hc⟩ := E.wrP; exact ⟨r, List.mem_append_right _ hr, hc⟩
    obtain hW : InRegions t₄.wr (S + BitVec.ofNat 64 (4096 + 4 * i)) 4 := by rw [c₄.2.2]; exact E.wrP
    brun [r8₄, r17₄, d₄, hP, hW]
    refine ⟨?_, ?_⟩
    · simp only [lo_xor, lo_ext, kw]
    · rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]
      congr 2
  · rw [tk.gpr (by decide), b₄, show 4 * i + (3 + 1) = 4 * (i + 1) by omega_using []]

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
  obtain W : KeyWordEnv S K L i u := by
    refine ⟨hi, E.L0, E.L64, by rw [hrd, hwr]; exact E.key, by rw [I.keep.gpr (by decide)]; exact E.r3,
      by rw [I.keep.gpr (by decide)]; exact E.r4, I.r8, I.r9, ?_⟩
    rw [hwr]; exact ⟨_, E.wrS, Offset.contains_base S (by omega_using [hi]) (by omega_using [hi])⟩
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
  obtain r17'' : u'.gpr .r17 = BitVec.ofNat 64 (18 - (i + 1)) := by
    rw [r17', I.r17]; apply BitVec.eq_of_toNat_eq; simp; omega_using [hi]
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
  refine WP.mono (WP.keep [.r8, .r9, .r17] (Q := fun t => t.gpr .r9 = 0#64 ∧
      t.gpr .r8 = S + BitVec.ofNat 64 4096 ∧ t.gpr .r17 = BitVec.ofNat 64 18 ∧ t.mem = s₀.mem)
    (by brun [E.r5, pOff]) (by decide) rfl) fun s₁ ⟨⟨a, b, c, d⟩, k⟩ => ?_
  obtain I₀ : KeyPInv S K L s₀ 0 s₁ :=
    ⟨by omega_using [], by rw [a]; simp, b, c, fun j hj => absurd hj (by omega_using []), by rw [d]; exact Frame.refl _ _,
      k.mono (by decide)⟩
  refine WP.loop (M := isa) (fun m u => ∃ i, i < 18 ∧ m = 18 - i ∧ KeyPInv S K L s₀ i u)
    ?_ 18 s₁ ⟨0, by omega_using [], rfl, I₀⟩
  intro m u ⟨i, hi, hm, I⟩
  refine WP.mono (keyP_step E hi I) fun u' ⟨I', z'⟩ => ?_
  rw [cnt, eval_nonzero, z', ofNat_bne_zero (by omega_using [])]
  by_cases h : i + 1 = 18
  · left; exact ⟨by simp [h], h ▸ I'⟩
  · right
    exact ⟨by simp; omega_using [hi, h], 18 - (i + 1), by omega_using [hi, hm], i + 1, by omega_using [hi, h], rfl, I'⟩

end VG.Proof.Blowfish.PPC64LE

end

end

/-! ### `Blowfish.PPC64LE.KeyEnc`, which only this module used -/

section

/-!
# Blowfish on PPC64LE, key expansion: the encryptions

`encryptP_run` and `encryptS_run`: the 521 encryptions of the key schedule,
each under the schedule as written so far, their outputs into the P-array
and then the S-boxes' planes (`ksIter`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-- The registers the encryptions write. -/
def encRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17]

/-- After `j` encryptions, from the state `s₀` before them: the schedule at
`S` and the last output. -/
structure EncInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop where
  sched : scheduleAt u.mem S = (ksIter key j).1
  halves : (lo (u.gpr .r4), lo (u.gpr .r5)) = ((ksIter key j).2.1, (ksIter key j).2.2)
  keep : Keep encRegs s₀ u
  frame : Frame [⟨S, 4168⟩] s₀.mem u.mem

/-- What the encryptions need of the state before them. -/
structure EncEnv (S : Addr) (s₀ : State) : Prop where
  r3 : s₀.gpr .r3 = S
  r0 : s₀.gpr .r0 = 0#64
  wS : (⟨S, 4168⟩ : Region) ∈ s₀.wr

theorem ord_true : ord true = id := rfl

/-- The encryption of the last output. -/
theorem enc_cipher {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} {u : State}
    (I : EncInv key S s₀ j u) :
    WP isa (cipher true) u fun u' =>
      (lo (u'.gpr .r4), lo (u'.gpr .r5)) =
        encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2 ∧
        Keep cRegs u u' ∧ u'.mem = u.mem := by
  obtain LE : LookEnv u := by
    refine ⟨fun o n ho => ?_, by rw [I.keep.gpr (by decide)]; exact E.r0⟩
    rw [I.keep.gpr (by decide), E.r3, I.keep.2.1, I.keep.2.2]
    exact ⟨_, List.mem_append_right _ E.wS, Offset.contains_base S ho (by omega_arith)⟩
  refine WP.mono (cipher_run LE true) fun u' ⟨h, k, m⟩ => ⟨?_, k, m⟩
  obtain e1 := congrArg Prod.fst I.halves
  obtain e2 := congrArg Prod.snd I.halves
  simp only at e1 e2
  rw [h, I.keep.gpr (by decide), E.r3, I.sched, ord_true, e1, e2]; rfl

theorem ksIter_step (key : List Byte) {j : Nat} (hj : j < 521) :
    ksIter key (j + 1) =
      (((ksIter key j).1.set (2 * j) (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1
          (by omega_arith)).set (2 * j + 1)
          (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 (by omega_arith),
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1,
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2) := by
  rw [ksIter_succ, ksStep, set!_eq_set _ (by omega_arith), set!_eq_set _ (by omega_arith)]

/-! ## The P-array -/

theorem storeP_run (u : State) {a : Addr} (h16 : u.gpr .r16 = a) (w0 : InRegions u.wr a 4)
    (w4 : InRegions u.wr (a + BitVec.ofNat 64 4) 4) :
    WP isa (.block storeP) u fun t =>
      t.mem = (u.mem.writeW a (lo (u.gpr .r4))).writeW (a + BitVec.ofNat 64 4) (lo (u.gpr .r5)) ∧
      t.gpr .r16 = a + 8#64 ∧ t.gpr .r17 = u.gpr .r17 - 1#64 ∧ Keep [.r16, .r17] u t := by
  refine WP.mono (WP.keep [.r16, .r17] (Q := fun t =>
      t.mem = (u.mem.writeW a (lo (u.gpr .r4))).writeW (a + BitVec.ofNat 64 4) (lo (u.gpr .r5)) ∧
      t.gpr .r16 = a + 8#64 ∧ t.gpr .r17 = u.gpr .r17 - 1#64) ?_ (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold storeP
  brun [h16, w0, w4]

/-- After `j` of the first nine encryptions. -/
structure PInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop extends
    EncInv key S s₀ j u where
  le : j ≤ 9
  ptr : u.gpr .r16 = S + BitVec.ofNat 64 (4096 + 8 * j)
  cnt : u.gpr .r17 = BitVec.ofNat 64 (9 - j)

theorem encP_step {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} (hj : j < 9)
    {u : State} (I : PInv key S s₀ j u) :
    WP isa (.seq (cipher true) (.block storeP)) u fun u' =>
      PInv key S s₀ (j + 1) u' ∧ u'.gpr .r17 = BitVec.ofNat 64 (9 - (j + 1)) := by
  apply WP.seq
  refine WP.mono (enc_cipher E I.toEncInv) fun v ⟨hv, kv, mv⟩ => ?_
  obtain wr : v.wr = s₀.wr := by rw [kv.2.2, I.keep.2.2]
  obtain a0 : S + BitVec.ofNat 64 (4096 + 8 * j) = S + BitVec.ofNat 64 (4096 + 4 * (2 * j)) := by
    congr 2; omega_arith
  obtain a4 : S + BitVec.ofNat 64 (4096 + 8 * j) + BitVec.ofNat 64 4 =
      S + BitVec.ofNat 64 (4096 + 4 * (2 * j + 1)) := Offset.add_add_eq _ (by omega_arith)
  refine WP.mono (storeP_run v (a := S + BitVec.ofNat 64 (4096 + 8 * j)) (by rw [kv.gpr (by decide), I.ptr])
    (by rw [wr]; exact ⟨_, E.wS, Offset.contains_base S (by omega_arith) (by omega_arith)⟩)
    (by rw [wr, a4]; exact ⟨_, E.wS, Offset.contains_base S (by omega_arith) (by omega_arith)⟩))
    fun t ⟨tm, t16, t17, tk⟩ => ?_
  obtain c17 : t.gpr .r17 = BitVec.ofNat 64 (9 - (j + 1)) := by
    rw [t17, kv.gpr (by decide), I.cnt]; apply BitVec.eq_of_toNat_eq; simp; omega_arith
  refine ⟨⟨⟨?_, ?_, ((I.keep.trans kv).trans tk).mono (by decide), ?_⟩, by omega_arith, ?_, c17⟩, c17⟩
  · rw [tm, a4, a0, scheduleAt_writeW_P _ _ (by omega_arith), scheduleAt_writeW_P _ _ (by omega_arith), mv, I.sched,
      ksIter_step key (by omega_arith), ← hv]
  · rw [tk.gpr (by decide), tk.gpr (by decide), ksIter_step key (by omega_arith), ← hv]
  · rw [tm, mv]
    refine (I.frame.writeW List.mem_cons_self _ ?_).writeW List.mem_cons_self _ ?_
    · rw [a0]; exact Offset.contains_base S (by omega_arith) (by omega_arith)
    · rw [a4]; exact Offset.contains_base S (by omega_arith) (by omega_arith)
  · rw [t16, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
    congr 2

theorem encryptP_run {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {u : State}
    (I : EncInv key S s₀ 0 u) :
    WP isa encryptP u (PInv key S s₀ 9) := by
  unfold encryptP
  apply WP.seq
  refine WP.mono (WP.keep [.r16, .r17] (Q := fun t => t.gpr .r16 = S + BitVec.ofNat 64 4096 ∧
      t.gpr .r17 = BitVec.ofNat 64 9 ∧ t.mem = u.mem)
    (by brun [I.keep.gpr (show Reg.r3 ∉ encRegs by decide), E.r3, pOff]) (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ?_
  obtain I₀ : PInv key S s₀ 0 t :=
    ⟨⟨by rw [c]; exact I.sched, by rw [k.gpr (by decide), k.gpr (by decide)]; exact I.halves,
      (I.keep.trans k).mono (by decide), by rw [c]; exact I.frame⟩, by omega_arith, a, b⟩
  refine WP.loop (M := isa) (fun m v => ∃ j, j < 9 ∧ m = 9 - j ∧ PInv key S s₀ j v)
    ?_ 9 t ⟨0, by omega_arith, rfl, I₀⟩
  intro m v ⟨j, hj, hm, J⟩
  refine WP.mono (encP_step E hj J) fun v' ⟨J', z'⟩ => ?_
  rw [cnt, eval_nonzero, z', ofNat_bne_zero (by omega_arith)]
  by_cases h : j + 1 = 9
  · left; exact ⟨by simp [h], h ▸ J'⟩
  · right
    exact ⟨by simp; omega_arith, 9 - (j + 1), by omega_arith, j + 1, by omega_arith, rfl, J'⟩

/-! ## The S-boxes -/

/-- The offset of S-box entry `sDone j`'s first plane. -/
def sOff (j : Nat) : Nat := 1024 * (sDone j / 256) + sDone j % 256

theorem sOff_entry {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) {b k : Nat} (hk : k < 2) :
    sOff j + (256 * b + k) = entryOff (2 * j + k) b := by
  rw [← entryOff_sbox h9 hj k hk, sOff]

theorem sOff_lt {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) : sOff j ≤ 3326 := by
  unfold sOff sDone; omega_arith

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
    scheduleAt (sW m S (sOff j) x y) S = ((scheduleAt m S).set (2 * j) x (by omega_arith)).set (2 * j + 1) y
      (by omega_arith) := by
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
    e' 769 3 1 (by decide) rfl, e0, scheduleAt_write_bytes _ _ (by omega_arith), Nat.add_zero,
    scheduleAt_write_bytes _ _ (by omega_arith)]

theorem write1_eq (m : Mem) (a : Addr) (v : BitVec 8) : m.write a 1 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem sW_frame (m : Mem) (S : Addr) {q : Nat} (hq : q + 770 ≤ 4168) (x y : BitVec 32) :
    Frame [⟨S, 4168⟩] m (sW m S q x y) := by
  obtain c : ∀ e, e < 770 → Region.Contains ⟨S, 4168⟩ (S + BitVec.ofNat 64 q + BitVec.ofNat 64 e) (8 / 8) :=
    fun e he => by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain c0 : Region.Contains ⟨S, 4168⟩ (S + BitVec.ofNat 64 q) (8 / 8) :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  unfold sW
  simp only [write1_eq]
  exact (((((((((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _
    (c 256 (by decide))).writeW List.mem_cons_self _ (c 512 (by decide))).writeW List.mem_cons_self _
    (c 768 (by decide))).writeW List.mem_cons_self _ (c 1 (by decide))).writeW List.mem_cons_self _
    (c 257 (by decide))).writeW List.mem_cons_self _ (c 513 (by decide))).writeW List.mem_cons_self _
    (c 769 (by decide)))

theorem byte0 (g : BitVec 64) : g.setWidth 8 = (lo g).extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi, show i < 32 by omega_arith]

theorem extract_shr (x : BitVec 32) {k : Nat} (hk : k + 8 ≤ 32) :
    (x >>> k).extractLsb' 0 8 = x.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show i < 32 by omega_arith, show k + i < 32 by omega_arith, Nat.add_comm]

def storeSHead : List Instr :=
  storeEntry xL 0 ++ storeEntry xR 1 ++ [.addi ptr ptr 2, .sub tmp ptr sch, .lsl tmp tmp 56]

theorem storeSHead_run (u : State) {S : Addr} {q : Nat} (hq : q + 770 ≤ 4168) (h16 : u.gpr .r16 = S + BitVec.ofNat 64 q)
    (h3 : u.gpr .r3 = S) (hw : (⟨S, 4168⟩ : Region) ∈ u.wr) :
    WP isa (.block storeSHead) u fun t =>
      t.mem = sW u.mem S q (lo (u.gpr .r4)) (lo (u.gpr .r5)) ∧ t.gpr .r16 = S + BitVec.ofNat 64 (q + 2) ∧
      t.gpr .r12 = BitVec.ofNat 64 (q + 2) <<< 56 ∧ Keep [.r12, .r16] u t := by
  refine WP.mono (WP.keep [.r12, .r16] (Q := fun t =>
      t.mem = sW u.mem S q (lo (u.gpr .r4)) (lo (u.gpr .r5)) ∧ t.gpr .r16 = S + BitVec.ofNat 64 (q + 2) ∧
      t.gpr .r12 = BitVec.ofNat 64 (q + 2) <<< 56) ?_ (by decide) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  obtain c : ∀ e, e < 770 → InRegions u.wr (S + BitVec.ofNat 64 q + BitVec.ofNat 64 e) 1 :=
    fun e he => ⟨_, hw, by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain c0 : InRegions u.wr (S + BitVec.ofNat 64 q) 1 := ⟨_, hw, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain w256 := c 256 (by decide); have w512 := c 512 (by decide); have w768 := c 768 (by decide)
  obtain w1 := c 1 (by decide); have w257 := c 257 (by decide); have w513 := c 513 (by decide)
  obtain w769 := c 769 (by decide)
  unfold storeSHead storeEntry
  brun [h16, h3, c0, w256, w512, w768, w1, w257, w513, w769]
  refine ⟨?_, ?_, ?_⟩
  · simp only [sW, byte0, lo_ext, extract_shr _ (k := 8) (by decide), extract_shr _ (k := 16) (by decide),
      extract_shr _ (k := 24) (by decide)]
  · rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, Offset.add_add]
  · rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, Offset.add_add, Offset.add_sub_cancel_left]

/-- `n << 56` is zero iff the low byte of `n` is. -/
theorem shl56_beq {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n <<< 56 == 0#64) = decide (n % 256 = 0) := by
  obtain e : (BitVec.ofNat 64 n <<< 56 = 0#64) ↔ n % 256 = 0 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, 
        Nat.mod_eq_of_lt hn] at this
      omega_arith
    · intro h
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, 
        Nat.mod_eq_of_lt hn]
      omega_arith
  by_cases h : n % 256 = 0
  · simp [e.mpr h, h]
  · have : ¬ BitVec.ofNat 64 n <<< 56 = 0#64 := fun h' => h (e.mp h')
    simp [this, h]

/-- After `j` encryptions, the first nine into the P-array. -/
structure SInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop extends
    EncInv key S s₀ j u where
  ge : 9 ≤ j
  le : j ≤ 521
  ptr : u.gpr .r16 = S + BitVec.ofNat 64 (sOff j)
  cnt : u.gpr .r17 = BitVec.ofNat 64 (521 - j)

theorem encS_step {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} (hj : j < 521)
    {u : State} (I : SInv key S s₀ j u) :
    WP isa (.seq (cipher true) storeS) u fun u' =>
      SInv key S s₀ (j + 1) u' ∧ u'.gpr .r17 = BitVec.ofNat 64 (521 - (j + 1)) := by
  have h9 := I.ge
  obtain hq := sOff_lt h9 hj
  apply WP.seq
  refine WP.mono (enc_cipher E I.toEncInv) fun v ⟨hv, kv, mv⟩ => ?_
  obtain Kv : Keep encRegs s₀ v := (I.keep.trans kv).mono (by decide)
  unfold storeS
  apply WP.seq
  refine WP.mono (storeSHead_run v (S := S) (q := sOff j) (by omega_arith) (by rw [kv.gpr (by decide), I.ptr])
    (by rw [Kv.gpr (by decide), E.r3]) (by rw [Kv.2.2]; exact E.wS)) fun t ⟨tm, t16, t12, tk⟩ => ?_
  obtain Kt : Keep encRegs s₀ t := (Kv.trans tk).mono (by decide)
  obtain hsch : scheduleAt t.mem S = (ksIter key (j + 1)).1 := by
    rw [tm, sW_sched _ _ h9 hj, mv, I.sched, ksIter_step key hj, ← hv]
  obtain hhalf : (lo (t.gpr .r4), lo (t.gpr .r5)) = ((ksIter key (j + 1)).2.1, (ksIter key (j + 1)).2.2) := by
    rw [tk.gpr (by decide), tk.gpr (by decide), ksIter_step key hj, ← hv]
  obtain hfr : Frame [⟨S, 4168⟩] s₀.mem t.mem := by
    rw [tm, mv]; exact I.frame.trans (sW_frame _ _ (by omega_arith) _ _)
  obtain h17 : t.gpr .r17 = BitVec.ofNat 64 (521 - j) := by
    rw [tk.gpr (by decide), kv.gpr (by decide), I.cnt]
  apply WP.seq
  refine WP.mono (Q := fun (w : State) => w.gpr .r16 = S + BitVec.ofNat 64 (sOff (j + 1)) ∧ w.mem = t.mem ∧
      Keep [.r16] t w) ?_ fun w ⟨w16, wm, wk⟩ => ?_
  · refine WP.ite (decide ((sOff j + 2) % 256 = 0)) (by rw [tmp, eval_zero, t12, shl56_beq (by omega_arith)])
      (fun h => ?_) (fun h => ?_)
    · have h' : (sOff j + 2) % 256 = 0 := by simpa using h
      refine WP.mono (WP.keep [.r16] (Q := fun (w : State) =>
        w.gpr .r16 = S + BitVec.ofNat 64 (sOff (j + 1)) ∧ w.mem = t.mem) ?_ (by decide) rfl)
        fun w ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
      brun [t16]
      rw [show (768#64 : BitVec 64) = BitVec.ofNat 64 768 from rfl, Offset.add_add, sOff_succ h9,
        ite_eq_left h']
    · have h' : ¬ (sOff j + 2) % 256 = 0 := by simpa using h
      exact WP.block_nil ⟨by rw [t16, sOff_succ h9, ite_eq_right h'], rfl, Keep.refl _ _⟩
  · have Kw : Keep encRegs s₀ w := (Kt.trans wk).mono (by decide)
    refine WP.mono (WP.keep [.r17] (Q := fun x => x.gpr .r17 = BitVec.ofNat 64 (521 - (j + 1)) ∧
        x.mem = w.mem) ?_ (by decide) rfl) fun x ⟨⟨x17, xm⟩, xk⟩ => ?_
    · brun [wk.gpr (show Reg.r17 ∉ [Reg.r16] by decide), h17]
      apply BitVec.eq_of_toNat_eq; simp; omega_arith
    refine ⟨⟨⟨by rw [xm, wm]; exact hsch, ?_, (Kw.trans xk).mono (by decide), by rw [xm, wm]; exact hfr⟩,
      by omega_arith, by omega_arith, by rw [xk.gpr (by decide)]; exact w16, x17⟩, x17⟩
    rw [xk.gpr (by decide), xk.gpr (by decide), wk.gpr (by decide), wk.gpr (by decide)]
    exact hhalf

theorem encryptS_run {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {u : State}
    (I : PInv key S s₀ 9 u) :
    WP isa encryptS u (SInv key S s₀ 521) := by
  unfold encryptS
  apply WP.seq
  refine WP.mono (WP.keep [.r16, .r17] (Q := fun t => t.gpr .r16 = S ∧
      t.gpr .r17 = BitVec.ofNat 64 512 ∧ t.mem = u.mem)
    (by brun [I.keep.gpr (show Reg.r3 ∉ encRegs by decide), E.r3, BitVec.or_self]) (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ?_
  obtain I₀ : SInv key S s₀ 9 t :=
    ⟨⟨by rw [c]; exact I.sched, by rw [k.gpr (by decide), k.gpr (by decide)]; exact I.halves,
      (I.keep.trans k).mono (by decide), by rw [c]; exact I.frame⟩, by omega_arith, by omega_arith,
      by rw [a]; simp [sOff, sDone], b⟩
  refine WP.loop (M := isa) (fun m v => ∃ j, 9 ≤ j ∧ j < 521 ∧ m = 521 - j ∧ SInv key S s₀ j v)
    ?_ 512 t ⟨9, by omega_arith, by omega_arith, rfl, I₀⟩
  intro m v ⟨j, hj9, hj, hm, J⟩
  refine WP.mono (encS_step E hj J) fun v' ⟨J', z'⟩ => ?_
  rw [cnt, eval_nonzero, z', ofNat_bne_zero (by omega_arith)]
  by_cases h : j + 1 = 521
  · left; exact ⟨by simp [h], h ▸ J'⟩
  · right
    exact ⟨by simp; omega_arith, 521 - (j + 1), by omega_arith, j + 1, by omega_arith, by omega_arith, rfl, J'⟩

end VG.Proof.Blowfish.PPC64LE

end

end


/-!
# Blowfish on PPC64LE: key expansion

`expandKey_wp`: the schedule at `r5` becomes the expansion of the key at
`r3`; our caller's `r14`–`r17` are saved in the working space at `r6` and
restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-- What key expansion may assume: the key readable, the schedule and the
working space writable, apart, and a valid key length. -/
structure KeyPre (s : State) : Prop where
  valid : validKey (s.gpr .r4).toNat
  rd : s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
  wr : s.wr = [⟨s.gpr .r5, 4168⟩, ⟨s.gpr .r6, 32⟩]
  keyS : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r5, 4168⟩
  keyB : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 32⟩
  SB : (⟨s.gpr .r5, 4168⟩ : Region).Disjoint ⟨s.gpr .r6, 32⟩

/-- What key expansion guarantees. -/
structure KeyPost (s s' : State) : Prop where
  sched : scheduleAt s'.mem (s.gpr .r5) = expandKey (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  saved : ∀ r ∈ saved.map Prod.fst, s'.gpr r = s.gpr r

theorem saved_fits' : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide
theorem saved_lt' : ∀ p ∈ saved, p.2 + 8 ≤ 32 := by decide

theorem save_eq' : save = Spill.saveCode .r6 saved := rfl
theorem restore_eq' : restore = Spill.restoreCode .r6 saved := rfl

theorem expandKey_wp {s : State} (h : KeyPre s) : WP isa Impl.Blowfish.PPC64LE.expandKey s (KeyPost s) := by
  have hv := h.valid
  let K := s.gpr .r3
  let L := (s.gpr .r4).toNat
  let S := s.gpr .r5
  let B := s.gpr .r6
  obtain sR : (⟨S, 4168⟩ : Region) ∈ s.wr := by rw [h.wr]; simp [S]
  obtain bR : (⟨B, 32⟩ : Region) ∈ s.wr := by rw [h.wr]; simp [B]
  obtain slot : ∀ p ∈ saved, Region.Sub ⟨B + BitVec.ofNat 64 p.2, 8⟩ ⟨B, 32⟩ := fun p hp =>
    Offset.sub_base _ (saved_lt' p hp)
  obtain keyIn : ∀ c < L, (⟨K, L⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1 := fun c hc =>
    Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc])
  -- frames that miss the key
  obtain keyFrame : ∀ {m m' : Mem} {r : Region}, (⟨K, L⟩ : Region).Disjoint r → Frame [r] m m' →
      bytesAt m' K L = bytesAt m K L := fun hd hf =>
    bytesAt_frame hf fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd _ (keyIn c hc) hcon
  unfold Impl.Blowfish.PPC64LE.expandKey
  apply WP.seq
  rw [save_eq']
  refine Spill.save_ok (by decide) saved_fits' (fun p hp =>
    ⟨_, bR, Offset.contains_base _ (saved_lt' p hp) (by have := saved_lt' p hp; omega_using [this])⟩) ?_
  let M₀ := Spill.saveMem s.mem B s.gpr saved
  obtain F₀ : Frame [⟨B, 32⟩] s.mem M₀ := Spill.saveMem_frame_base (fun p hp => saved_lt' p hp) (by decide) _ _ _
  rw [initSchedule_eq]
  refine WP.mono (initSteps_run (t := { s with mem := M₀ }) (S := S) rfl sR 521 (Nat.le_refl _))
    fun t₁ ⟨held, F₁, k₁⟩ => ?_
  -- the table's bytes
  obtain hT : ∀ o < 4168, t₁.mem (S + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := fun o ho =>
    table_byte (fun i hi => by rw [held i hi, initWords_getD hi]) ho
  obtain B₁ : bytesAt t₁.mem K L = bytesAt s.mem K L := by
    rw [keyFrame h.keyS F₁]; exact keyFrame h.keyB F₀
  obtain r₁ : t₁.rd = s.rd ∧ t₁.wr = s.wr := ⟨k₁.2.1, k₁.2.2⟩
  obtain E : KeyPEnv S K L t₁ := by
    refine ⟨by unfold validKey at hv; omega, (s.gpr .r4).isLt, fun c hc => ?_, k₁.gpr (by decide),
      by rw [k₁.gpr (by decide)]; simp [L], k₁.gpr (by decide), by rw [r₁.2]; exact sR,
      fun c hc hcon => h.keyS _ (keyIn c hc) hcon⟩
    rw [r₁.1, r₁.2, h.rd]; exact ⟨_, List.mem_cons_self, keyIn c hc⟩
  apply WP.seq
  refine WP.mono (keyP_run E) fun t₂ I₂ => ?_
  obtain hS₂ : ∀ o < 4096, t₂.mem (S + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := fun o ho => by
    rw [← hT o (by omega_using [ho])]
    refine I₂.frame _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint S (d := o) (n := 1) (e := 4096) (k := 4 * 18) (.inl (by omega_using [ho])) (by omega_using [ho]) (by omega_using [])
      _ (Region.contains_self _ _) hc
  obtain hK₂ : scheduleAt t₂.mem S = keyed (bytesAt s.mem K L) := by
    refine keyed_of_mem hS₂ fun i hi => ?_
    rw [I₂.done i hi, table_P hT hi, B₁]
  -- the setup of the encryptions
  obtain r₂ : t₂.rd = s.rd ∧ t₂.wr = s.wr := by rw [I₂.keep.2.1, I₂.keep.2.2]; exact r₁
  apply WP.seq
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r5] (Q := fun t => t.gpr .r0 = 0#64 ∧ t.gpr .r3 = S ∧
      t.gpr .r4 = 0#64 ∧ t.gpr .r5 = 0#64 ∧ t.mem = t₂.mem)
    (by brun [I₂.keep.gpr (show Reg.r5 ∉ keyPRegs by decide), k₁.gpr (show Reg.r5 ∉ [Reg.r12] by decide),
      BitVec.or_self]; rfl) (by decide) rfl) fun t₃ ⟨⟨z₃, a₃, b₃, c₃, m₃⟩, k₃⟩ => ?_
  obtain EE : EncEnv S t₃ := ⟨a₃, z₃, by rw [k₃.2.2, r₂.2]; exact sR⟩
  obtain I₃ : EncInv (bytesAt s.mem K L) S t₃ 0 t₃ :=
    ⟨by rw [m₃, hK₂, ksIter_zero], by rw [b₃, c₃, ksIter_zero]; rfl, Keep.refl _ _, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (encryptP_run EE I₃) fun t₄ I₄ => ?_
  apply WP.seq
  refine WP.mono (encryptS_run EE I₄) fun t₅ I₅ => ?_
  -- restore
  rw [restore_eq']
  obtain r6 : t₅.gpr .r6 = B := by
    rw [I₅.keep.gpr (by decide), k₃.gpr (by decide), I₂.keep.gpr (by decide), k₁.gpr (by decide)]
  obtain dSlots : ∀ p ∈ saved, ∀ r ∈ [(⟨S, 4168⟩ : Region)], Region.Disjoint ⟨B + BitVec.ofNat 64 p.2, 8⟩ r :=
    fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.SB.symm.sub_left (slot p hp))
  obtain hsv : Spill.Saved B s.gpr saved t₅.mem := by
    obtain s₀ : Spill.Saved B s.gpr saved M₀ := Spill.saveMem_saved (by decide) s.mem B s.gpr
    obtain s₁ := s₀.frame F₁ dSlots
    obtain s₂ := s₁.frame I₂.frame fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dSlots p hp _ List.mem_cons_self).sub_right (by
        rw [← Offset.add_add_eq S (a := 4096) (b := 0) rfl, BitVec.add_zero]
        exact Offset.sub_base S (by omega_using []))
    obtain s₃ : Spill.Saved B s.gpr saved t₃.mem := by rw [m₃]; exact s₂
    exact s₃.frame I₅.frame dSlots
  refine WP.mono (Spill.restore_wp (by decide) r6 saved_fits' (by decide) (fun p hp => ?_) hsv)
    fun s' R => ⟨?_, fun r hr => ?_⟩
  · rw [I₅.keep.2.1, I₅.keep.2.2, k₃.2.1, k₃.2.2, r₂.1, r₂.2]
    exact ⟨_, List.mem_append_right _ bR, Offset.contains_base _ (saved_lt' p hp)
      (by have := saved_lt' p hp; omega_using [this])⟩
  · rw [R.mem, I₅.sched, expandKey_eq]
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact R.gpr p hp

end VG.Proof.Blowfish.PPC64LE
