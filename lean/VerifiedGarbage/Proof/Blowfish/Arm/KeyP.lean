import VerifiedGarbage.Proof.Blowfish.Arm.KeyInit

/-!
# Blowfish on ARMv7: the key into the P-array

`keyP_run`: Pᵢ ^= the `i`-th 32 bits of the key (at `r0`, `r1` bytes long),
cycling through its bytes, for the 18 entries of the schedule at `r2`.
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- The key offset after `c`, advanced: back to 0 at the key length. -/
theorem key_next (c L : Nat) (hL : 0 < L) (hL' : L < 2 ^ 32) :
    (if (BitVec.ofNat 32 (c % L) + 1#32 - BitVec.ofNat 32 L == 0#32) = true then 0#32
      else BitVec.ofNat 32 (c % L) + 1#32) = BitVec.ofNat 32 ((c + 1) % L) := by
  have hb := Nat.mod_lt c hL
  have ht : (BitVec.ofNat 32 (c % L) + 1#32).toNat = c % L + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c % L < 2 ^ 32 by omega)]
    change (c % L + 1) % 2 ^ 32 = _
    omega
  have ha : (c + 1) % L = (c % L + 1) % L := by simp only [Nat.add_mod, Nat.mod_mod]
  have e : (BitVec.ofNat 32 (c % L) + 1#32 - BitVec.ofNat 32 L == 0#32) = decide (c % L + 1 = L) := by
    rw [show BitVec.ofNat 32 (c % L) + 1#32 = BitVec.ofNat 32 (c % L + 1) from
      BitVec.eq_of_toNat_eq (by rw [ht, BitVec.toNat_ofNat]; omega)]
    exact ofNat_sub_beq (by omega) hL'
  rw [e]
  by_cases h : c % L + 1 = L
  · simp only [decide_eq_true h, ↓reduceIte]; rw [ha, h, Nat.mod_self]
  · rw [decide_eq_false h]
    simp only [Bool.false_eq_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt (show c % L + 1 < L by omega),
      Nat.mod_eq_of_lt (show c % L + 1 < 2 ^ 32 by omega)]

/-- The key bytes: `key` at `Kk`, `L` bytes long. -/
structure KeyEnv (Kk : BitVec 32) (L : Nat) (u : State) : Prop where
  r0 : u.gpr .r0 = Kk
  r1 : u.gpr .r1 = BitVec.ofNat 32 L
  pos : 0 < L
  small : L ≤ 56
  fit : Kk.toNat + L ≤ 2 ^ 32
  rd : InRegions (u.rd ++ u.wr) (State.addr Kk) L

theorem keyByte_run (u : State) {Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u) (c : Nat)
    (h4 : u.gpr .r4 = BitVec.ofNat 32 (c % L)) :
    WP isa keyByte u fun t =>
      t.gpr .r5 = (u.gpr .r5 <<< 8) ||| (u.mem (State.addr Kk + BitVec.ofNat 64 (c % L))).setWidth 32 ∧
        t.gpr .r4 = BitVec.ofNat 32 ((c + 1) % L) ∧ t.mem = u.mem ∧ Keep [.r4, .r5, .r6, .r7] u t := by
  have hc := Nat.mod_lt c E.pos
  have fit := E.fit
  have ea : State.addr (Kk + BitVec.ofNat 32 (c % L) + BitVec.ofNat 32 0) =
      State.addr Kk + BitVec.ofNat 64 (c % L) := by rw [BitVec.add_zero, addr_add (by omega)]
  have hr : InRegions (u.rd ++ u.wr) (State.addr Kk + BitVec.ofNat 64 (c % L)) 1 := inRegions_off E.rd (by omega)
  unfold keyByte
  apply WP.seq
  refine WP.mono (WP.keep [.r4, .r5, .r6, .r7] (Q := fun t =>
      t.gpr .r5 = (u.gpr .r5 <<< 8) ||| (u.mem (State.addr Kk + BitVec.ofNat 64 (c % L))).setWidth 32 ∧
      t.gpr .r4 = BitVec.ofNat 32 (c % L) + 1#32 ∧
      t.z = (BitVec.ofNat 32 (c % L) + 1#32 - BitVec.ofNat 32 L == 0#32) ∧ t.mem = u.mem)
    (by brun [E.r0, E.r1, h4, ea, hr]) (by decide)) fun v ⟨⟨v5, v4, vz, vm⟩, vk⟩ => ?_
  have nx := key_next c L E.pos (by have := E.small; omega)
  refine WP.ite _ (by rw [eval_eq, vz]) (fun hz => ?_) (fun hz => ?_)
  · rw [hz] at nx
    refine WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = 0#32 ∧ t.gpr .r5 = v.gpr .r5 ∧ t.mem = v.mem)
      (by brun) (by decide)) fun t ⟨⟨t4, t5, tm⟩, tk⟩ =>
        ⟨by rw [t5, v5], by rw [t4, ← nx]; rfl, by rw [tm, vm], vk.trans_sub tk (by decide)⟩
  · rw [hz] at nx
    exact WP.block_nil ⟨v5, by rw [v4, ← nx]; rfl, vm, vk⟩

theorem KeyEnv.keep {Kk : BitVec 32} {L : Nat} {u t : State} (E : KeyEnv Kk L u) {rs : List Reg}
    (h : Keep rs u t) (h0 : Reg.r0 ∉ rs) (h1 : Reg.r1 ∉ rs) : KeyEnv Kk L t :=
  ⟨by rw [h.gpr h0, E.r0], by rw [h.gpr h1, E.r1], E.pos, E.small, E.fit, by rw [keep_reads h]; exact E.rd⟩

/-- The key's byte `c` (mod its length) in memory `m`. -/
abbrev kb (m : Mem) (Kk : BitVec 32) (L c : Nat) : Word :=
  (m (State.addr Kk + BitVec.ofNat 64 (c % L))).setWidth 32

/-- The tail of `keyWord`. -/
def keyTail : List Instr :=
  [.ldr .r6 .r12 0, .dp .eor .r6 .r6 (.reg .r5), .str .r6 .r12 0, .dp .add .r12 .r12 (imm 4),
   .subs .r8 .r8 (imm 1)]

/-- The key word of entry `w`: four bytes, the first the most significant,
then `keyTail`. -/
theorem keyWord_run (u : State) {Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u) (w : Nat)
    (h4 : u.gpr .r4 = BitVec.ofNat 32 ((4 * w) % L)) {Q : State → Prop}
    (hQ : ∀ t, t.gpr .r5 = (((((0 : Word) <<< 8 ||| kb u.mem Kk L (4 * w + 0)) <<< 8 |||
          kb u.mem Kk L (4 * w + 1)) <<< 8 ||| kb u.mem Kk L (4 * w + 2)) <<< 8 ||| kb u.mem Kk L (4 * w + 3)) →
        t.gpr .r4 = BitVec.ofNat 32 ((4 * (w + 1)) % L) → t.mem = u.mem → Keep [.r4, .r5, .r6, .r7] u t →
        WP isa (.block keyTail) t Q) :
    WP isa Impl.Blowfish.Arm.keyWord u Q := by
  unfold Impl.Blowfish.Arm.keyWord
  apply WP.seq
  refine WP.mono (WP.keep [.r5] (Q := fun t => t.gpr .r5 = 0 ∧ t.mem = u.mem) (by brun; rfl) (by decide))
    fun t0 ⟨⟨a5, am⟩, ak⟩ => ?_
  apply WP.seq
  refine WP.mono (keyByte_run t0 (E.keep ak (by decide) (by decide)) (4 * w + 0)
    (by rw [ak.gpr (by decide), h4, Nat.add_zero])) fun t1 ⟨b5, b4, bm, bk⟩ => ?_
  apply WP.seq
  refine WP.mono (keyByte_run t1 ((E.keep ak (by decide) (by decide)).keep bk (by decide) (by decide))
    (4 * w + 1) b4) fun t2 ⟨c5, c4, cm, ck⟩ => ?_
  apply WP.seq
  refine WP.mono (keyByte_run t2 (((E.keep ak (by decide) (by decide)).keep bk (by decide) (by decide)).keep ck
    (by decide) (by decide)) (4 * w + 2) c4) fun t3 ⟨d5, d4, dm, dk⟩ => ?_
  apply WP.seq
  refine WP.mono (keyByte_run t3 ((((E.keep ak (by decide) (by decide)).keep bk (by decide) (by decide)).keep ck
    (by decide) (by decide)).keep dk (by decide) (by decide)) (4 * w + 3) d4) fun t4 ⟨e5, e4, em, ek⟩ => ?_
  exact hQ t4 (by rw [e5, d5, c5, b5, a5, dm, cm, bm, am]) (by rw [e4]; congr 2)
    (by rw [em, dm, cm, bm, am]) (((((ak.trans bk).trans ck).trans dk).trans ek).mono (by decide))

theorem kb_keyWord (m : Mem) (Kk : BitVec 32) {L : Nat} (hL : 0 < L) (w : Nat) :
    (((((0 : Word) <<< 8 ||| kb m Kk L (4 * w + 0)) <<< 8 ||| kb m Kk L (4 * w + 1)) <<< 8 |||
      kb m Kk L (4 * w + 2)) <<< 8 ||| kb m Kk L (4 * w + 3)) = Spec.Blowfish.keyWord (bytesAt m (State.addr Kk) L) w := by
  have hl : (bytesAt m (State.addr Kk) L).length = L := by simp [bytesAt]
  rw [keyWord_eq, hl, bytesAt_getD _ _ (Nat.mod_lt _ hL), bytesAt_getD _ _ (Nat.mod_lt _ hL),
    bytesAt_getD _ _ (Nat.mod_lt _ hL), bytesAt_getD _ _ (Nat.mod_lt _ hL)]

theorem keyTail_run (t : State) {K V : BitVec 32} {a : Addr} (w : Nat)
    (h12 : t.gpr .r12 = K + BitVec.ofNat 32 (4096 + 4 * w)) (h5 : t.gpr .r5 = V)
    (ea : State.addr (K + BitVec.ofNat 32 (4096 + 4 * w) + BitVec.ofNat 32 0) = a)
    (hw : InRegions t.wr a 4) :
    WP isa (.block keyTail) t fun t' =>
      t'.mem = t.mem.writeW a (t.mem.readW a 32 ^^^ V) ∧
      t'.gpr .r12 = K + BitVec.ofNat 32 (4096 + 4 * (w + 1)) ∧
      t'.gpr .r8 = t.gpr .r8 - 1#32 ∧ t'.z = (t.gpr .r8 - 1#32 == 0#32) := by
  have hr := region_in (rs := t.rd) hw
  unfold keyTail
  brun [h12, h5, ea, hw, hr]
  rw [ofs_add]; congr 2

/-- After the key words of entries `0, …, w - 1`, from `u₀`. -/
structure KPInv (u₀ : State) (K Kk : BitVec 32) (L w : Nat) (t : State) : Prop where
  le : w ≤ 18
  r4 : t.gpr .r4 = BitVec.ofNat 32 ((4 * w) % L)
  r12 : t.gpr .r12 = K + BitVec.ofNat 32 (4096 + 4 * w)
  r8 : t.gpr .r8 = BitVec.ofNat 32 (18 - w)
  keep : Keep [.r4, .r5, .r6, .r7, .r8, .r12] u₀ t
  done : ∀ j < w, t.mem.readW (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    u₀.mem.readW (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) 32 ^^^
      Spec.Blowfish.keyWord (bytesAt u₀.mem (State.addr Kk) L) j
  rest : ∀ j, w ≤ j → j < 18 → t.mem.readW (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    u₀.mem.readW (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) 32
  frame : Frame [⟨State.addr K + BitVec.ofNat 64 4096, 72⟩] u₀.mem t.mem

theorem keyStep {u₀ : State} {K Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u₀) (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (hw : InRegions u₀.wr (State.addr K + BitVec.ofNat 64 4096) 72)
    (hd : Region.Disjoint ⟨State.addr Kk, L⟩ ⟨State.addr K + BitVec.ofNat 64 4096, 72⟩)
    {w : Nat} (hw18 : w < 18) {t : State} (I : KPInv u₀ K Kk L w t) :
    WP isa Impl.Blowfish.Arm.keyWord t fun t' =>
      KPInv u₀ K Kk L (w + 1) t' ∧ t'.z = (BitVec.ofNat 32 (18 - (w + 1)) == 0#32) := by
  have Et := E.keep I.keep (by decide) (by decide)
  refine keyWord_run t Et w I.r4 fun v v5 v4 vm vk => ?_
  have ea : State.addr (K + BitVec.ofNat 32 (4096 + 4 * w) + BitVec.ofNat 32 0) =
      State.addr K + BitVec.ofNat 64 (4096 + 4 * w) := by rw [BitVec.add_zero, addr_add (by omega)]
  have hwv : InRegions v.wr (State.addr K + BitVec.ofNat 64 (4096 + 4 * w)) 4 := by
    rw [vk.2.2.1, I.keep.2.2.1, ← Offset.add_add]; exact inRegions_off hw (by omega)
  refine WP.mono (WP.keep [.r6, .r8, .r12] (keyTail_run v w (by rw [vk.gpr (by decide), I.r12]) v5 ea hwv)
    (by decide)) fun t' ⟨⟨tm, t12, t8, tz⟩, tk⟩ => ?_
  -- the key's bytes are where they were
  have hkey : bytesAt t.mem (State.addr Kk) L = bytesAt u₀.mem (State.addr Kk) L :=
    bytesAt_frame I.frame fun c hc r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact fun h => hd _ (Offset.contains_base _ (by omega) (by have := E.fit; omega)) h
  have hv8 : v.gpr .r8 = BitVec.ofNat 32 (18 - w) := by rw [vk.gpr (by decide), I.r8]
  have h8 : BitVec.ofNat 32 (18 - w) - 1#32 = BitVec.ofNat 32 (18 - (w + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have sepw : ∀ j, j < 18 → j ≠ w → Mem.Sep (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) (32 / 8)
      (State.addr K + BitVec.ofNat 64 (4096 + 4 * w)) (32 / 8) :=
    fun j hj hne => Offset.sep _ (by omega) (by omega) (by omega)
  refine ⟨⟨by omega, by rw [tk.gpr (by decide), v4], t12, by rw [t8, hv8, h8],
    (I.keep.trans (vk.trans tk)).mono (by decide), fun j hj => ?_, fun j h1 h2 => ?_, ?_⟩, by rw [tz, hv8, h8]⟩
  · rw [tm, vm]
    by_cases e : j = w
    · subst e
      rw [Mem.readW_writeW_self32, I.rest j (by omega) hw18, kb_keyWord _ _ E.pos, hkey]
    · rw [Mem.readW_writeW_sep (sepw j (by omega) e) (by decide)]; exact I.done j (by omega)
  · rw [tm, vm, Mem.readW_writeW_sep (sepw j h2 (by omega)) (by decide)]; exact I.rest j (by omega) h2
  · rw [tm, vm]
    exact I.frame.writeW List.mem_cons_self _ (Offset.contains (e := 4096) (k := 72) (d := 4096 + 4 * w)
      (n := 4) _ (by omega) (by omega) (by omega))

theorem keyP_run {u₀ : State} {K Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u₀) (h2 : u₀.gpr .r2 = K)
    (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (hw : InRegions u₀.wr (State.addr K + BitVec.ofNat 64 4096) 72)
    (hd : Region.Disjoint ⟨State.addr Kk, L⟩ ⟨State.addr K + BitVec.ofNat 64 4096, 72⟩) :
    WP isa keyP u₀ (KPInv u₀ K Kk L 18) := by
  unfold keyP
  apply WP.seq
  refine WP.mono (WP.keep [.r4, .r8, .r12] (Q := fun t => t.gpr .r4 = 0#32 ∧
      t.gpr .r12 = K + BitVec.ofNat 32 4096 ∧ t.gpr .r8 = BitVec.ofNat 32 18 ∧ t.mem = u₀.mem)
    (by brun [h2, pOff]) (by decide)) fun u₁ ⟨⟨a4, a12, a8, am⟩, ak⟩ => ?_
  have I0 : KPInv u₀ K Kk L 0 u₁ :=
    ⟨by decide, by rw [a4, Nat.mul_zero, Nat.zero_mod], by rw [a12], by rw [a8], ak.mono (by decide),
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ _ => by rw [am], by rw [am]; exact Frame.refl _ _⟩
  refine WP.loop (M := isa) (Q := KPInv u₀ K Kk L 18)
    (fun (n : Nat) (v : State) => ∃ w, w < 18 ∧ n = 18 - w ∧ KPInv u₀ K Kk L w v) ?_ 18 u₁ ⟨0, by decide, rfl, I0⟩
  intro n v ⟨w, hw', hn, J⟩
  refine WP.mono (keyStep E fit hw hd hw' J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : w + 1 = 18
  · left
    exact ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    have nz : BitVec.ofNat 32 (18 - (w + 1)) ≠ 0#32 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega, w + 1, by omega, rfl, J'⟩

end VG.Proof.Blowfish.Arm
