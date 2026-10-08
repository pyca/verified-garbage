import VerifiedGarbage.Proof.Camellia.AArch64.KaKb
import VerifiedGarbage.Proof.Camellia.AArch64.KeyContract

/-!
# The Camellia key schedule on AArch64: its parts

As on x86-64: the prologue saves the callee-saved registers, sets the masks
and stores the planes of `Sigma1 … Sigma6` as a table of subkeys
(`ekPrologue_ok`, the planes by evaluation: `sigmaStores_ok`);
`loadKey_wp` loads `KL` and `KR` into their slots, and `loadValues_ok`
byte-swaps the four values into registers.
-/

namespace VG.Proof.Camellia.AArch64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 t2 u7 kp movR ldS stS eorR imm)
open VG.Proof.Camellia (HalfRel pair hiW loW pos)

/-! ## Single instructions -/

/-- `str r, [sb, #8 k]`, as slots. -/
theorem st_ok {s : State} {k : Nat} (r : Reg) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k < slots) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ slotW s' k = s.gpr r ∧
      (∀ j < slots, j ≠ k → slotW s' j = slotW s j) ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, m, g, rd, wr⟩ := stS_slot (k := k) r rfl hscr hk
  refine ⟨s', e, ?_, fun j hj hjk => ?_, g, by rw [m]; exact frame_slot _ hk, rd, wr⟩
  · rw [slotW_store m g hk hk, ite_eq_left rfl]
  · rw [slotW_store m g hj hk, ite_eq_right hjk]

/-- `ldr d, [r, #k]`. -/
theorem ldAt_ok (s : State) (d r : Reg) {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 k) 8) :
    ∃ s', runBlock isa [.ldr .x d r k] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64 ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x hk hr],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r' h => RegUpd.gpr_write_of_ne _ _ _ h, rfl, rfl, rfl⟩

/-! ## The table of `Sigma1 … Sigma6` -/

theorem sigmaStores_dst :
    (sigmas.all fun x => (sigmaStores x).all fun i => dstOf i == some t0 || dstOf i == none) = true := by
  decide +kernel

/-- The stores of `sigmaOne x`: the planes of `x` to the entry at `kp`. -/
theorem sigmaStores_ok {x : BitVec 64} (hx : x ∈ sigmas) (s : State) {r : Region} (hr : r ∈ s.wr) {off : Nat}
    (hb : s.gpr kp = r.base + BitVec.ofNat 64 off) (hlen : off + 64 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa (sigmaStores x) s = some s' ∧
      (∀ j < 8, s'.mem.readW (wordAddr (s.gpr kp) j) 64 = keyPlane x j) ∧
      Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem ∧ (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have hchk := List.all_eq_true.mp sigma_checks x hx
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hok : Ok sigCfg s := Ok.of_off hr hb hlen hn rfl
  have hrel : Rel (LaneRel 1 0) sigCfg (fun _ => none) (linEnvG [] [] []) s := by
    refine ⟨fun r a h => ?_, fun k a _ h => ?_, fun _ _ _ h => ?_, fun _ _ h => ?_⟩ <;>
      simp [linEnvG] at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  have hdst := List.all_eq_true.mp sigmaStores_dst x hx
  have hall : ∀ r, r ≠ t0 → ((sigmaStores x).all fun i => dstOf i != some r) = true := fun r hr => by
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hdst ⊢
    intro i hi
    rcases hdst i hi with h | h <;> simp [h, Ne.symm hr]
  refine ⟨s', hs', fun j hj => ?_, ?_, fun r hr => p.other r (by simp [hall r hr]), p.rd, p.wr⟩
  · have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at h
    have hr := p.rel.slot j _ (by simp only [sigCfg]; omega) h
    simp only [sigCfg] at hr
    have hb' : s'.gpr kp = s.gpr kp := p.base
    rw [hb'] at hr
    apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [hr.2 q hq, par_zero, Bool.xor_false]
    rfl
  · have := p.frame
    simpa [slotRegion, sigCfg] using this

/-- `sigmaOne x`: the planes of `x` to the entry at `kp`, and `kp` to the next. -/
theorem sigmaOne_ok {x : BitVec 64} (hx : x ∈ sigmas) (s : State) {r : Region} (hr : r ∈ s.wr) {off : Nat}
    (hb : s.gpr kp = r.base + BitVec.ofNat 64 off) (hlen : off + 64 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa (sigmaOne x) s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * j)) 64 = keyPlane x j) ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 ∧ Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, f₁, g₁, rd₁, wr₁⟩ := sigmaStores_ok hx s hr hb hlen hn
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 64 (by decide)
  refine ⟨s₂, by rw [sigmaOne_eq, runBlock_append', e₁, Option.bind_some, e₂], fun j hj => by
      rw [m₂]; exact v₁ j hj,
    by rw [a₂, g₁ _ (by decide)], by rw [m₂]; exact f₁, fun r h1 h2 => by rw [o₂ r h2, g₁ r h1],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem sigmaList_ok {b : Addr} (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) :
    ∀ (xs : List (BitVec 64)) (e : Nat) (s : State), (∀ x ∈ xs, x ∈ sigmas) → (⟨b, 8 * slots⟩ : Region) ∈ s.wr →
      s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e) → e + xs.length ≤ 34 →
      ∃ s', runBlock isa (xs.flatMap sigmaOne) s = some s' ∧
        (∀ i < xs.length, ∀ j < 8, entryW s'.mem b (e + i) j = keyPlane (xs.getD i 0) j) ∧
        Frame [⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64 * xs.length⟩] s.mem s'.mem ∧
        s'.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + xs.length)) ∧
        (∀ r, r ≠ t0 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], e, s, _, _, hr, _ => ⟨s, rfl, fun i hi => absurd hi (by simp), Frame.refl _ _, by simpa using hr,
      fun _ _ _ => rfl, rfl, rfl⟩
  | x :: xs, e, s, hxs, hscr, hr, hl => by
    rw [slots_eq] at hfit
    have hk := keySlot_eq
    simp only [List.length_cons] at hl
    obtain ⟨s₁, e₁, v₁, r₁, f₁, g₁, rd₁, wr₁⟩ := sigmaOne_ok (hxs x List.mem_cons_self) s hscr
      (off := 8 * keySlot + 64 * e) hr (by simp only [slots_eq]; omega) (by show 8 * slots < 2 ^ 64; rw [slots_eq]; decide)
    obtain ⟨s', e', v', f', r', g', rd', wr'⟩ := sigmaList_ok hfit xs (e + 1) s₁
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) (by rw [wr₁]; exact hscr)
      (by rw [r₁, hr, addr_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega])
      (by omega)
    refine ⟨s', by rw [List.flatMap_cons, runBlock_append', e₁, Option.bind_some, e'], fun i hi j hj => ?_,
      ?_, by rw [r', List.length_cons, show e + 1 + xs.length = e + (xs.length + 1) by omega],
      fun r h1 h2 => by rw [g' r h1 h2, g₁ r h1 h2], by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rcases i with _ | i
      · rw [entryW, Nat.add_zero, ← addr_add, ← hr]
        refine (f'.readW (Region.contains_self _ _) (fun r hr' => ?_) (by decide)).trans (v₁ j hj)
        simp only [List.mem_singleton] at hr'; subst hr'
        rw [hr, addr_add]
        exact VG.Offset.disjoint b (by omega) (by omega) (by omega)
      · rw [show e + (i + 1) = e + 1 + i by omega]
        exact v' i (by simpa using hi) j hj
    · refine Frame.trans (f₁.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩)
        (f'.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
        (simp only [List.mem_singleton] at hr'; subst hr')
      · rw [hr]; exact Region.sub_prefix (by simp only [List.length_cons]; omega)
      · exact VG.Offset.sub b (by omega) (by simp only [List.length_cons]; omega)

/-- The table's entries `0 … 5` hold `Sigma1 … Sigma6`, as `KeyCtx` reads them. -/
theorem sigmas_rel {m : Mem} {b : Addr}
    (h : ∀ i < 6, ∀ j < 8, entryW m b i j = keyPlane (sigmas.getD i 0) j) :
    ∀ i < 6, HalfRel (entryW m b i) fun _ => sigE i := fun i hi bb hb c hc j hj => by
  rw [h i hi j hj]; exact sigma_planes _ hb hc hj

/-! ## Loading the key -/

/-- A step that writes only `t0`, `t1` and `u7`. -/
structure Pure (s s' : State) : Prop where
  mem : s'.mem = s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Pure.refl (s : State) : Pure s s := ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl⟩

theorem Pure.trans {s₁ s₂ s₃ : State} (h₁ : Pure s₁ s₂) (h₂ : Pure s₂ s₃) : Pure s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, fun r h0 h1 h2 => (h₂.regs r h0 h1 h2).trans (h₁.regs r h0 h1 h2), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

theorem Pure.of1 {s s' : State} {d : Reg} (hd : d = t0 ∨ d = t1 ∨ d = u7) (hm : s'.mem = s.mem)
    (hg : ∀ r, r ≠ d → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pure s s' :=
  ⟨hm, fun r h0 h1 h2 => hg r (by rcases hd with rfl | rfl | rfl <;> with_reducible assumption), hrd, hwr⟩

/-- A store of `t0` to slot `k`. -/
structure StOk (s s' : State) (k : Nat) : Prop where
  val : slotW s' k = s.gpr t0
  keep : ∀ j < slots, j ≠ k → slotW s' j = slotW s j
  gpr : s'.gpr = s.gpr
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem stOk {s : State} {k : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < slots) :
    ∃ s', runBlock isa [stS k t0] s = some s' ∧ StOk s s' k := by
  obtain ⟨s', e, v, kp, g, f, rd, wr⟩ := st_ok (k := k) t0 hscr hk
  exact ⟨s', e, v, kp, g, f, rd, wr⟩

/-- `KR`'s words stored: what each branch of `loadKey` leaves. -/
structure KrPost (s s' : State) (V : BitVec 64 × BitVec 64) : Prop where
  kr : WordsAt s' krSlot V
  keep : ∀ k < slots, k ≠ krSlot → k ≠ krSlot + 1 → slotW s' k = slotW s k
  regs : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem StOk.frame' {s₀ s s' : State} {k : Nat} (hf : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s.mem)
    (hb : s.gpr sb = s₀.gpr sb) (h : StOk s s' k) : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s'.mem :=
  hf.trans (by have := h.frame; rw [hb] at this; exact this)

theorem krPost_of {s s₁ s₂ s₃ s₄ : State} {V : BitVec 64 × BitVec 64}
    (p₁ : Pure s s₁) (h₂ : StOk s₁ s₂ krSlot) (p₃ : Pure s₂ s₃) (h₄ : StOk s₃ s₄ (krSlot + 1))
    (hu : WordOf (s₁.gpr t0) V.1) (hv : WordOf (s₃.gpr t0) V.2) : KrPost s s₄ V := by
  obtain ⟨-, hr, -, -, -, -, -, hS⟩ := kaKb_slots
  have hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide) (by decide) (by decide)
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide) (by decide) (by decide), h₂.gpr, hb₁]
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k :=
    slotW_eq_of p₃.mem (by rw [p₃.regs _ (by decide) (by decide) (by decide)])
  have f₂ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₂.mem :=
    StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  refine ⟨⟨?_, ?_⟩, fun k hk h1 h2 => by rw [h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁],
    fun r h0 h1 h2 => by rw [h₄.gpr, p₃.regs r h0 h1 h2, h₂.gpr, p₁.regs r h0 h1 h2],
    StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄,
    by rw [h₄.rd, p₃.rd, h₂.rd, p₁.rd], by rw [h₄.wr, p₃.wr, h₂.wr, p₁.wr]⟩
  · rw [h₄.keep _ (by omega) (by omega), hs₃, h₂.val]; exact hu
  · rw [h₄.val]; exact hv

theorem allOnes_eq : BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide

/-- `loadKey`: `KL`'s and `KR`'s halves, as words, in their slots. -/
theorem loadKey_wp {s : State} {len : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hkey : (⟨s.gpr .x0, len⟩ : Region) ∈ s.rd) (hfit : (s.gpr .x0).toNat + len ≤ 2 ^ 64)
    (hks : Region.Disjoint ⟨s.gpr .x0, len⟩ ⟨s.gpr sb, 8 * slots⟩)
    (hlen : s.gpr .x3 = BitVec.ofNat 64 len) (hl : len = 16 ∨ len = 24 ∨ len = 32) :
    WP isa loadKey s fun s' =>
      WordsAt s' klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).1,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).1) ∧
      WordsAt s' krSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).2,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).2) ∧
      (∀ k < slots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl', hr', -, -, -, -, -, hS⟩ := kaKb_slots
  obtain ⟨hK0, hK1, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .x0) hl
  -- The key's words, read after stores to the scratch buffer.
  have hkw : ∀ {t : State}, t.rd = s.rd → t.gpr .x0 = s.gpr .x0 →
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem t.mem → ∀ d, d % 8 = 0 → d + 8 ≤ len →
      ∃ t', runBlock isa [.ldr .x t0 .x0 d] t = some t' ∧ Pure t t' ∧
        WordOf (t'.gpr t0) (Spec.Camellia.wordAt s.mem (s.gpr .x0 + BitVec.ofNat 64 d)) := by
    intro t hrd hdi hf d hd8 hd
    obtain ⟨t', e, a, o, m, rd, wr⟩ := ldAt_ok t t0 .x0 (k := d) ⟨hd8, by omega⟩ (by
      rw [hrd, hdi]; exact ⟨_, List.mem_append_left _ hkey, VG.Offset.contains_base _ (by omega) (by omega)⟩)
    refine ⟨t', e, Pure.of1 (Or.inl rfl) m o rd wr, ?_⟩
    rw [a, hdi, hf.readW (r := ⟨s.gpr .x0 + BitVec.ofNat 64 d, 64 / 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hks.sub_left (VG.Offset.sub_base _ (by omega))) (by decide)]
    exact wordOf_readW _ _
  have hz : s.gpr .x0 + BitVec.ofNat 64 0 = s.gpr .x0 := by simp
  have hscrOf : ∀ {t : State}, t.gpr sb = s.gpr sb → t.wr = s.wr → (⟨t.gpr sb, 8 * slots⟩ : Region) ∈ t.wr :=
    fun hb hw => by rw [hb, hw]; exact hscr
  have hn : ∀ {r : Reg}, r = t0 ∨ r = t1 ∨ r = u7 → sb ≠ r ∧ Reg.x0 ≠ r ∧ Reg.x3 ≠ r := by
    intro r hr; rcases hr with rfl | rfl | rfl <;> decide
  unfold loadKey
  -- `KL`.
  obtain ⟨s₁, e₁, p₁, w₁⟩ := hkw rfl rfl (Frame.refl _ _) 0 (by decide) (by omega)
  have hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide) (by decide) (by decide)
  obtain ⟨s₂, e₂, h₂⟩ := stOk (k := klSlot) (hscrOf hb₁ p₁.wr) (by omega)
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [h₂.gpr, hb₁]
  have f₂ := StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  obtain ⟨s₃, e₃, p₃, w₃⟩ := hkw (by rw [h₂.rd, p₁.rd]) (by rw [h₂.gpr, p₁.regs _ (by decide) (by decide) (by decide)])
    f₂ 8 (by decide) (by omega)
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide) (by decide) (by decide), hb₂]
  obtain ⟨s₄, e₄, h₄⟩ := stOk (k := klSlot + 1) (hscrOf hb₃ (by rw [p₃.wr, h₂.wr, p₁.wr])) (by omega)
  have f₄ := StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ t1 .x3 (imm := 16) (by decide)
  have p₅ : Pure s₄ s₅ := Pure.of1 (Or.inr (Or.inl rfl)) m₅ g₅ rd₅ wr₅
  have hg₅ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s₅.gpr r = s.gpr r := fun r h0 h1 h2 => by
    rw [p₅.regs r h0 h1 h2, h₄.gpr, p₃.regs r h0 h1 h2, h₂.gpr, p₁.regs r h0 h1 h2]
  have hb₅ : s₅.gpr sb = s.gpr sb := hg₅ _ (by decide) (by decide) (by decide)
  have hs₅ : ∀ k, slotW s₅ k = slotW s₄ k := slotW_eq_of m₅ (p₅.regs _ (by decide) (by decide) (by decide))
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k :=
    slotW_eq_of p₃.mem (p₃.regs _ (by decide) (by decide) (by decide))
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  have f₅ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₅.mem := by rw [m₅]; exact f₄
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, h₄.rd, p₃.rd, h₂.rd, p₁.rd]
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, h₄.wr, p₃.wr, h₂.wr, p₁.wr]
  have hkl : WordsAt s₅ klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).1,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).1) := by
    refine ⟨?_, ?_⟩
    · rw [hs₅, h₄.keep _ (by omega) (by omega), hs₃, h₂.val, hK0, ← hz]; exact w₁
    · rw [hs₅, h₄.val, hK1]; exact w₃
  have hother : ∀ k < slots, k ≠ klSlot → k ≠ klSlot + 1 → slotW s₅ k = slotW s k := fun k hk h1 h2 => by
    rw [hs₅, h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁]
  have hx3 : s₄.gpr .x3 = BitVec.ofNat 64 len := by
    rw [h₄.gpr, p₃.regs _ (by decide) (by decide) (by decide), h₂.gpr, p₁.regs _ (by decide) (by decide) (by decide),
      hlen]
  have hz₅ : (s₅.gpr t1 == 0) = decide (len = 16) := by
    rw [z₅, hx3, VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [show ([.ldr .x t0 .x0 0, stS klSlot t0, .ldr .x t0 .x0 8, stS (klSlot + 1) t0,
        .subImm .x t1 .x3 16] : List Instr) =
        [.ldr .x t0 .x0 0] ++ ([stS klSlot t0] ++ ([.ldr .x t0 .x0 8] ++
          ([stS (klSlot + 1) t0] ++ [.subImm .x t1 .x3 16]))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅], ?_⟩)
  refine WP.mono (Q := fun s' => KrPost s₅ s' (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).2,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).2))
    (WP.ite (decide (len = 16)) ((eval_zero s₅ t1).trans (by rw [hz₅])) (fun h16 => ?_) (fun h16 => ?_))
    fun s' h => ?_
  · -- A key of 16 bytes: `KR = 0`.
    have h16 : len = 16 := by simpa using h16
    obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := movz_ok s₅ t0 (v := 0) (by decide)
    have p₆ : Pure s₅ s₆ := Pure.of1 (Or.inl rfl) m₆ o₆ rd₆ wr₆
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf (by rw [o₆ _ (by decide), hb₅]) (by rw [wr₆, wr₅']))
      (by omega)
    obtain ⟨s₈, e₈, h₈⟩ := stOk (k := krSlot + 1)
      (hscrOf (by rw [h₇.gpr, o₆ _ (by decide), hb₅]) (by rw [h₇.wr, wr₆, wr₅'])) (by omega)
    refine WP.of_runBlock ⟨s₈, by
      rw [show ([.movz .x t0 0 0, stS krSlot t0, stS (krSlot + 1) t0] : List Instr) =
          [.movz .x t0 (BitVec.ofNat 16 0) 0] ++ ([stS krSlot t0] ++ [stS (krSlot + 1) t0]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈],
      krPost_of p₆ h₇ (Pure.refl _) h₈ (by rw [a₆, hK2, ite_eq_left h16]; exact WordOf.zero)
        (by rw [h₇.gpr, a₆, hK3, ite_eq_left h16]; exact WordOf.zero)⟩
  · have h16 : len ≠ 16 := by simpa using h16
    obtain ⟨s₆, e₆, p₆, w₆⟩ := hkw (by rw [rd₅']) (hg₅ _ (by decide) (by decide) (by decide)) f₅ 16
      (by decide) (by omega)
    have hb₆ : s₆.gpr sb = s.gpr sb := by rw [p₆.regs _ (by decide) (by decide) (by decide), hb₅]
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf hb₆ (by rw [p₆.wr, wr₅'])) (by omega)
    obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := subI_ok s₇ t1 .x3 (imm := 24) (by decide)
    have p₈ : Pure s₇ s₈ := Pure.of1 (Or.inr (Or.inl rfl)) m₈ g₈ rd₈ wr₈
    have hb₈ : s₈.gpr sb = s.gpr sb := by rw [p₈.regs _ (by decide) (by decide) (by decide), h₇.gpr, hb₆]
    have f₈ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₈.mem := by
      rw [m₈]; exact StOk.frame' (by rw [p₆.mem]; exact f₅) hb₆ h₇
    have hz₈ : (s₈.gpr t1 == 0) = decide (len = 24) := by
      rw [z₈, h₇.gpr, p₆.regs _ (by decide) (by decide) (by decide), hg₅ _ (by decide) (by decide) (by decide),
        hlen, VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    refine WP.seq (WP.of_runBlock ⟨s₈, by
      rw [show ([.ldr .x t0 .x0 16, stS krSlot t0, .subImm .x t1 .x3 24] : List Instr) =
          [.ldr .x t0 .x0 16] ++ ([stS krSlot t0] ++ [.subImm .x t1 .x3 24]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈], ?_⟩)
    refine WP.ite (decide (len = 24)) ((eval_zero s₈ t1).trans (by rw [hz₈])) (fun h24 => ?_) (fun h24 => ?_)
    · have h24 : len = 24 := by simpa using h24
      obtain ⟨s₉a, e₉a, a₉a, o₉a, m₉a, rd₉a, wr₉a⟩ := movz_ok s₈ u7 (v := 0) (by decide)
      obtain ⟨s₉b, e₉b, a₉b, o₉b, m₉b, rd₉b, wr₉b⟩ := subI_ok s₉a u7 u7 (imm := 1) (by decide)
      obtain ⟨s₉, e₉, a₉, o₉, m₉, rd₉, wr₉⟩ := eor_ok s₉b t0 t0 u7
      have p₉ : Pure s₈ s₉ := (Pure.of1 (Or.inr (Or.inr rfl)) m₉a o₉a rd₉a wr₉a).trans
        ((Pure.of1 (Or.inr (Or.inr rfl)) m₉b o₉b rd₉b wr₉b).trans (Pure.of1 (Or.inl rfl) m₉ o₉ rd₉ wr₉))
      have hnot : s₉.gpr t0 = ~~~ s₈.gpr t0 := by
        rw [a₉, o₉b _ (by decide), o₉a _ (by decide), a₉b, a₉a, allOnes_eq, BitVec.xor_allOnes]
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [p₉.regs _ (by decide) (by decide) (by decide), hb₈])
          (by rw [p₉.wr, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.movz .x u7 0 0, .subImm .x u7 u7 1, eorR t0 t0 u7, stS (krSlot + 1) t0] : List Instr) =
            [.movz .x u7 (BitVec.ofNat 16 0) 0] ++ ([.subImm .x u7 u7 1] ++ ([eorR t0 t0 u7] ++
              [stS (krSlot + 1) t0])) from rfl,
          runBlock_append', e₉a, Option.bind_some, runBlock_append', e₉b, Option.bind_some,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans p₉) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [hnot, g₈ _ (by decide), h₇.gpr, hK3, ite_eq_right h16, ite_eq_left h24]; exact w₆.not)⟩
    · have h24 : len ≠ 24 := by simpa using h24
      obtain ⟨s₉, e₉, p₉, w₉⟩ := hkw (by rw [rd₈, h₇.rd, p₆.rd, rd₅'])
        (by rw [g₈ _ (by decide), h₇.gpr, p₆.regs _ (by decide) (by decide) (by decide),
          hg₅ _ (by decide) (by decide) (by decide)]) f₈ 24 (by decide) (by omega)
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [p₉.regs _ (by decide) (by decide) (by decide), hb₈])
          (by rw [p₉.wr, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.ldr .x t0 .x0 24, stS (krSlot + 1) t0] : List Instr) =
            [.ldr .x t0 .x0 24] ++ [stS (krSlot + 1) t0] from rfl,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans p₉) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [hK3, ite_eq_right h16, ite_eq_right h24]; exact w₉)⟩
  · -- Both.
    refine ⟨hkl.congr (h.keep _ (by omega) (by omega) (by omega)) (h.keep _ (by omega) (by omega) (by omega)),
      h.kr, fun k hk h1 => by rw [h.keep k hk (by omega) (by omega), hother k hk (by omega) (by omega)],
      fun r h0 h1 h2 => by rw [h.regs r h0 h1 h2, hg₅ r h0 h1 h2],
      f₅.trans (by have := h.frame; rw [hb₅] at this; exact this),
      by rw [h.rd, rd₅'], by rw [h.wr, wr₅']⟩

/-! ## The schedule's bytes -/

/-! ## Loading the values -/

def lvChunk (v k : Nat) : List Instr :=
  [ldS (hiReg v) k, .rev (hiReg v) (hiReg v), ldS (loReg v) (k + 1), .rev (loReg v) (loReg v)]

theorem loadValues_eq :
    loadValues = lvChunk 0 klSlot ++ (lvChunk 1 krSlot ++ (lvChunk 2 kaSlot ++ lvChunk 3 kbSlot)) := rfl

theorem regs_lt4 {v : Nat} (hv : v < 4) : hiReg v ≠ sb ∧ loReg v ≠ sb ∧ hiReg v ≠ loReg v := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem lvChunk_ok {s : State} {v k : Nat} (hv : v < 4) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < slots) :
    ∃ s', runBlock isa (lvChunk v k) s = some s' ∧ s'.gpr (hiReg v) = rev64 (slotW s k) ∧
      s'.gpr (loReg v) = rev64 (slotW s (k + 1)) ∧
      (∀ r, r ≠ hiReg v → r ≠ loReg v → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨n1, n2, n3⟩ := regs_lt4 hv
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (k := k) (hiReg v) rfl hscr (by omega)
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := rev_ok s₁ (hiReg v) (hiReg v)
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ n1.symm, o₁ _ n1.symm]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := ldS_ok (k := k + 1) (loReg v) hb₂ (by rw [wr₂, wr₁]; exact hscr) hk
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := rev_ok s₃ (loReg v) (loReg v)
  refine ⟨s₄, ?_, ?_, ?_, fun r h1 h2 => by rw [o₄ r h2, o₃ r h2, o₂ r h1, o₁ r h1],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [lvChunk, show ([ldS (hiReg v) k, .rev (hiReg v) (hiReg v), ldS (loReg v) (k + 1),
        .rev (loReg v) (loReg v)] : List Instr) = [ldS (hiReg v) k] ++ ([.rev (hiReg v) (hiReg v)] ++
          ([ldS (loReg v) (k + 1)] ++ [.rev (loReg v) (loReg v)])) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, e₄]
  · rw [o₄ _ n3, o₃ _ n3, a₂, a₁]
  · rw [a₄, a₃, slotW_eq_of (by rw [m₂, m₁]) hb₂]

/-- `loadValues`: the four values' halves, byte-swapped into `hiReg v` and `loReg v`. -/
theorem loadValues_ok {s : State} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (vs : List (BitVec 128))
    (hw : ∀ v < 4, WordsAt s ([klSlot, krSlot, kaSlot, kbSlot].getD v 0) (hiW (vs.getD v 0), loW (vs.getD v 0))) :
    ∃ s', runBlock isa loadValues s = some s' ∧
      (∀ v < 4, s'.gpr (hiReg v) = hiW (vs.getD v 0) ∧ s'.gpr (loReg v) = loW (vs.getD v 0)) ∧
      (∀ r, (∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl, hr, hW, hA, hB, -, -, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, h₁, l₁, o₁, m₁, rd₁, wr₁⟩ := lvChunk_ok (v := 0) (k := klSlot) (by decide) hscr (by omega)
  have hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (by decide) (by decide)
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ hb₁
  obtain ⟨s₂, e₂, h₂, l₂, o₂, m₂, rd₂, wr₂⟩ := lvChunk_ok (v := 1) (k := krSlot) (by decide)
    (by rw [hb₁, wr₁]; exact hscr) (by omega)
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide), hb₁]
  have hs₂ : ∀ k, slotW s₂ k = slotW s k := fun k => by rw [slotW_eq_of m₂ (by rw [hb₂, hb₁]), hs₁]
  obtain ⟨s₃, e₃, h₃, l₃, o₃, m₃, rd₃, wr₃⟩ := lvChunk_ok (v := 2) (k := kaSlot) (by decide)
    (by rw [hb₂, wr₂, wr₁]; exact hscr) (by omega)
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [o₃ _ (by decide) (by decide), hb₂]
  have hs₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by rw [slotW_eq_of m₃ (by rw [hb₃, hb₂]), hs₂]
  obtain ⟨s₄, e₄, h₄, l₄, o₄, m₄, rd₄, wr₄⟩ := lvChunk_ok (v := 3) (k := kbSlot) (by decide)
    (by rw [hb₃, wr₃, wr₂, wr₁]; exact hscr) (by omega)
  refine ⟨s₄, by rw [loadValues_eq, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂,
      Option.bind_some, runBlock_append', e₃, Option.bind_some, e₄], fun v hv => ?_,
    fun r hr => by
      obtain ⟨a0, b0⟩ := hr 0 (by decide); obtain ⟨a1, b1⟩ := hr 1 (by decide)
      obtain ⟨a2, b2⟩ := hr 2 (by decide); obtain ⟨a3, b3⟩ := hr 3 (by decide)
      rw [o₄ r a3 b3, o₃ r a2 b2, o₂ r a1 b1, o₁ r a0 b0],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl
  · have w := hw 0 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), o₂ _ (by decide) (by decide), h₁]
      exact rev_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), o₂ _ (by decide) (by decide), l₁]
      exact rev_of_wordOf w.2
  · have w := hw 1 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), h₂, hs₁]
      exact rev_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), l₂, hs₁]
      exact rev_of_wordOf w.2
  · have w := hw 2 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), h₃, hs₂]; exact rev_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), l₃, hs₂]; exact rev_of_wordOf w.2
  · have w := hw 3 (by decide)
    exact ⟨by rw [h₄, hs₃]; exact rev_of_wordOf w.1, by rw [l₄, hs₃]; exact rev_of_wordOf w.2⟩

/-! ## The prologue -/

/-- A frame of slots below the tail buffer's. -/
theorem frame_tail {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : k < tailSlot) :
    Frame [⟨b, 8 * tailSlot⟩] m (m.writeW (wordAddr b k) v) :=
  frame_writeW v (by rw [wordAddr]; rw [tailSlot_eq] at hk; exact VG.Offset.sub_base _ (by rw [tailSlot_eq]; omega))

theorem sreg_ne' (i : Nat) (hi : i < 10) : sreg i ≠ sb ∧ sreg i ≠ .x3 := by
  revert i; decide

theorem ekPrologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .x3 = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr)
    (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) :
    ∃ s, runBlock isa ([movR sb .x3, movR .x3 .x1] ++ saveRegs ++ setSlots layerMasks ++ tableSetup ++
        sigmas.flatMap sigmaOne) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .x3 = s₀.gpr .x1 ∧
      (∀ r, r ≠ sb → r ≠ .x3 → r ≠ t0 → r ≠ kp → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧
      (∀ i < 6, ∀ j < 8, entryW s.mem b i j = keyPlane (sigmas.getD i 0) j) ∧
      Frame [⟨b, 8 * tailSlot⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hk := keySlot_eq
  have ht := tailSlot_eq
  have hsv := savedSlot_eq
  have hS := slots_eq
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .x3
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁a .x3 .x1
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), r₁a, hb]
  have g₁ : ∀ r, r ≠ sb → r ≠ .x3 → s₁.gpr r = s₀.gpr r := fun r h1 h2 => by rw [o₁ r h2, o₁a r h1]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁, wr₁a]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) (by rw [wr₂, wr₁, wr₁a]; exact hw)
    (by rw [g₂, hb₁])
  have hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), g₂, hb₁]
  obtain ⟨s₄, e₄, k₄, o₄, m₄, rd₄, wr₄⟩ := setKp_ok s₃
  have hb₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), hb₃]
  obtain ⟨s₅, e₅, v₅, f₅, r₅, g₅, rd₅, wr₅⟩ := sigmaList_ok hfit sigmas 0 s₄ (fun x hx => hx)
    (by rw [wr₄, wr₃, wr₂, wr₁, wr₁a]; exact hw)
    (by rw [k₄, hb₃]; simp) (by decide)
  have hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide), hb₄]
  -- The slots outside the table keep their values.
  have hs₅ : ∀ k, k < keySlot ∨ keySlot + 48 ≤ k → k < slots → slotW s₅ k = slotW s₃ k := fun k h1 h2 => by
    simp only [slotW, hb₅, hb₃]
    rw [← m₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [wordAddr, Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
    exact VG.Offset.disjoint b (by omega) (by omega) (by omega)
  refine ⟨s₅, ?_, hb₅, ?_, fun r h1 h2 h3 h4 => ?_, fun i hi => ?_, fun kv hkv => ?_,
    fun i hi j hj => ?_, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁, rd₁a],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁, wr₁a]⟩
  · rw [runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      show ([movR sb .x3, movR .x3 .x1] : List Instr) = [movR sb .x3] ++ [movR .x3 .x1] from rfl,
      runBlock_append', e₁a, Option.bind_some, e₁, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some, e₅]
  · rw [g₅ _ (by decide) (by decide), o₄ _ (by decide), g₃ _ (by decide), g₂, r₁, o₁a _ (by decide)]
  · rw [g₅ r h3 h4, o₄ r h4, g₃ r h3, g₂, g₁ r h1 h2]
  · have n := sreg_ne' i hi
    have := sv₂ i hi
    rw [show s₁.gpr (sreg i) = s₀.gpr (sreg i) from g₁ _ n.1 n.2] at this
    rw [← this]
    have h' := hs₅ (savedSlot + i) (Or.inr (by omega)) (by omega)
    simp only [slotW, hb₅, hb₃] at h'
    rw [h']
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by omega) (by omega)
  · have := mask_lt hkv
    rw [hs₅ _ (Or.inl this) (by omega)]
    exact v₃ kv hkv
  · have := v₅ i (by simpa [sigmas] using hi) j hj
    rw [Nat.zero_add] at this
    exact this
  · have f₂' : Frame [⟨b, 8 * tailSlot⟩] s₁.mem s₂.mem := f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base b (by omega)⟩
    have f₃' : Frame [⟨b, 8 * tailSlot⟩] s₂.mem s₃.mem := f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega)⟩
    have f₅' : Frame [⟨b, 8 * tailSlot⟩] s₄.mem s₅.mem := f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
      exact VG.Offset.sub_base b (by omega)⟩
    rw [m₁, m₁a] at f₂'
    rw [m₄] at f₅'
    exact f₂'.trans (f₃'.trans f₅')

end VG.Proof.Camellia.AArch64
