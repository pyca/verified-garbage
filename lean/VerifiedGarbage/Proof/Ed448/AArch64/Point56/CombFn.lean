import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Body
import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Fast.VSave

/-!
# Ed448's comb on AArch64: the two affine additions, as a function

Untrusted: everything here is checked by Lean. `vg_ed448_r56_comb_add`
(`combAddFn`) runs the comb's two affine additions (`combBody_ok`, by
`addAffine_ok`), whose AdvSIMD products use every vector register: so it keeps
`x21`–`x28` in the upper halves of `v8`–`v15`, whose lower halves are
callee-saved, stores those at `CSAVE` (`stqs_ok`), and loads them back
(`ldqs_ok`) at the end. The additions store only to slots 0–5 and 10–18 and
the products' coefficients but `CSAVE` (`combStores`, `Exec.storeFrame`), so
the saved registers survive them (`combAddFn_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64 VG.Impl.Ed448.AArch64.Point56
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.Curve448.AArch64.Neon (V ldq stq)
open VG.Proof.Curve448.AArch64.Neon (exec_ldq exec_stq off_add st_outside read16_write scr_of setMem setMem_mem
  V_ne)
open VG.Proof.X448.AArch64 (Scr Keeps off limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env ofs_off')
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (temps addAffine_ok affEnv)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-! ## The saves -/

theorem stqs_ok {s : State} {base : Addr} (hs : Scr s base) {O : Nat} (hO : O % 16 = 0) (hO' : O + 128 ≤ 8192) :
    WP isa (.block ((List.range 8).map fun k => stq (8 + k) (O + 16 * k))) s fun t =>
      (∀ k < 8, t.mem.read (off base (O + 16 * k)) 16 = s.v (V (8 + k))) ∧
      Outside base O 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  have e : ((List.range 8).map fun k => stq (8 + k) (O + 16 * k)) =
      (List.range 8).flatMap fun k => [stq (8 + k) (O + 16 * k)] := rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.mem.read (off base (O + 16 * k)) 16 = s.v (V (8 + k))) ∧
    Outside base O 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv
    (fun n t hn ⟨tv, tO, tg, tvv, tr, tw, tsp⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl, rfl⟩)
    fun t ⟨tv, tO, tg, tvv, tr, tw, tsp⟩ => ⟨fun k hk => by rw [tv k hk], tO, tg, tvv, tr, tw, tsp⟩
  have ts : Scr t base := VG.Proof.Curve448.AArch64.Neon.scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_stq ts (8 + n) (d := O + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, tO.trans ((st_outside _ _ _ (by omega)).mono (by omega) (by omega)),
      tg, tvv, tr, tw, tsp⟩⟩
  simp only [setMem_mem]
  by_cases h : k = n
  · subst h; rw [read16_write, tvv]
  · rw [((st_outside t.mem base (t.v (V (8 + n))) (d := O + 16 * n) (by omega))).read16 (by omega)
      (by omega)]
    exact tv k (by omega)

theorem ldqs_ok {s : State} {base : Addr} (hs : Scr s base) {O : Nat} (hO : O % 16 = 0) (hO' : O + 128 ≤ 8192) :
    WP isa (.block ((List.range 8).map fun k => ldq (8 + k) (O + 16 * k))) s fun t =>
      (∀ k < 8, t.v (V (8 + k)) = s.mem.read (off base (O + 16 * k)) 16) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have e : ((List.range 8).map fun k => ldq (8 + k) (O + 16 * k)) =
      (List.range 8).flatMap fun k => [ldq (8 + k) (O + 16 * k)] := rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.v (V (8 + k)) = s.mem.read (off base (O + 16 * k)) 16) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tg, tr, tw, tsp⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl, rfl⟩
  have ts : Scr t base := VG.Proof.Curve448.AArch64.Neon.scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq ts (8 + n) (d := O + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, by rw [RegUpd.mem_setV, tm], by rw [RegUpd.gpr_setV, tg],
      by rw [RegUpd.rd_setV, tr], by rw [RegUpd.wr_setV, tw], by rw [RegUpd.sp_setV, tsp]⟩⟩
  by_cases h : k = n
  · subst h; rw [RegUpd.v_setV_self, tm]
  · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega))]
    exact tv k (by omega)

/-! ## The additions -/

/-- Where the comb's additions store: slots 0–5 and 10–18, and the products' coefficients but
`CSAVE`. -/
def combOk (d : Nat) : Bool :=
  (64 ≤ d && d + 8 ≤ 832) || (1344 ≤ d && d + 8 ≤ 2496) || (3584 ≤ d && d + 8 ≤ 3968) ||
    (4096 ≤ d && d + 8 ≤ 4736)

/-- Where the function stores: slots 0–5 and 10–18, and the products' coefficients. -/
def fnOk (d : Nat) : Bool := (64 ≤ d && d + 8 ≤ 832) || (1344 ≤ d && d + 8 ≤ 2496) || (3584 ≤ d && d + 8 ≤ 4736)

/-- The additions' code. -/
abbrev combBody : List Instr :=
  Impl.X448.AArch64.Base.addAffine (slot (0 : Index).val) (slot (1 : Index).val) (slot (2 : Index).val)
    (slot (6 : Index).val) (slot (7 : Index).val) ++
  Impl.X448.AArch64.Base.addAffine (slot (3 : Index).val) (slot (4 : Index).val) (slot (5 : Index).val)
    (slot (8 : Index).val) (slot (9 : Index).val)

theorem combStores : ∀ i ∈ instrs (.block combBody : Prog isa), storesAt combOk i = true := by
  rw [← List.all_eq_true, ← Code.allInstrs_eq]; decide +kernel

/-- What the additions change: both sums' slots and the temporaries. -/
abbrev combSlots : List Index := (temps ++ [2, 0, 1]) ++ (temps ++ [5, 3, 4])

/-- **Both additions**, from every slot's limbs below `Ib` and 0 in slot 19. -/
theorem combBody_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (.block combBody) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base combSlots s.mem t.mem ∧
      (∀ i : Index, i.val < 6 → Bnd Mb t.mem base (slot i.val)) ∧
      EV t.mem base = affEnv 3 4 5 8 9 (affEnv 0 1 2 6 7 (EV s.mem base)) := by
  rw [WP.block_append_iff]
  refine WP.mono (addAffine_ok 0 1 2 6 7 (by decide) (by decide) (by decide) hs hb hz
    (VG.Proof.X448.AArch64.Fast.indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (VG.Proof.X448.AArch64.Fast.indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (VG.Proof.X448.AArch64.Fast.indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (VG.Proof.X448.AArch64.Fast.indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)))
    fun t1 ⟨k1, b1, s1, m0, m1, m2, e1⟩ => ?_
  refine WP.mono (addAffine_ok 3 4 5 8 9 (by decide) (by decide) (by decide) (k1.scr hs) b1
    (s1.bnd (by decide) hz)
    (VG.Proof.X448.AArch64.Fast.indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (VG.Proof.X448.AArch64.Fast.indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (VG.Proof.X448.AArch64.Fast.indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (VG.Proof.X448.AArch64.Fast.indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)))
    fun t ⟨k2, b2, s2, m3, m4, m5, e2⟩ => ⟨k1.trans k2, b2, s1.append s2, fun i hi => ?_, by rw [e2, e1]⟩
  have h6 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
    rcases i with ⟨_ | _ | _ | _ | _ | _ | n, h⟩ <;> simp_all <;> omega
  rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact s2.bnd (by decide) m0
  · exact s2.bnd (by decide) m1
  · exact s2.bnd (by decide) m2
  · exact m3
  · exact m4
  · exact m5

/-! ## The function -/

/-- The memory the function leaves, from `m`. -/
abbrev CombMem (base : Addr) (m m' : Mem) : Prop :=
  BEnv m' base ∧ Same base combSlots m m' ∧ (∀ i : Index, i.val < 6 → Bnd Mb m' base (slot i.val)) ∧
    EV m' base = affEnv 3 4 5 8 9 (affEnv 0 1 2 6 7 (EV m base)) ∧ ∀ a, Unstored fnOk base a → m' a = m a

/-- The lanes the function keeps `x21`–`x28` in. -/
abbrev cks : List (Reg × VReg × Nat) :=
  [(.x21, .v8, 1), (.x22, .v9, 1), (.x23, .v10, 1), (.x24, .v11, 1), (.x25, .v12, 1), (.x26, .v13, 1),
    (.x27, .v14, 1), (.x28, .v15, 1)]

theorem csave_eq : csave = ([.addImm .x .x3 .x0 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++ insOf cks) ++
    (List.range 8).map (fun k => stq (8 + k) (CSAVE + 16 * k)) := rfl

theorem crestore_eq : crestore = (List.range 8).map (fun k => ldq (8 + k) (CSAVE + 16 * k)) ++ umovOf cks := rfl

theorem cks_V : ∀ k < 8, (cks.getD k (.x21, .v8, 1)).2.1 = V (8 + k) ∧
    (cks.getD k (.x21, .v8, 1)).1 = Impl.X448.AArch64.Fast.saved k ∧ (cks.getD k (.x21, .v8, 1)) ∈ cks := by
  decide

theorem preservedV_V : ∀ r ∈ preservedV, ∃ k < 8, r = V (8 + k) := by decide

/-- A byte the function does not store to is not in `CSAVE`. -/
theorem unstored_csave {base a : Addr} (h : Unstored fnOk base a) : ofs base a < CSAVE ∨ CSAVE + 128 ≤ ofs base a := by
  by_contra hc
  simp only [CSAVE, not_or, Nat.not_lt] at hc
  refine h (ofs base a) (by simp only [fnOk]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega) ?_
  rw [show base + BitVec.ofNat 64 (ofs base a) = a by simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega]
  simp

/-- A byte of `CSAVE` is not stored to by the additions. -/
theorem csave_unstored (base : Addr) {i : Nat} (hi : CSAVE ≤ i) (hi' : i < CSAVE + 128) :
    Unstored combOk base (off base i) := by
  intro d hd hlt
  simp only [combOk, CSAVE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd hi hi'
  rw [off, Offset.add_sub_add_left] at hlt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hlt
  omega

/-- **The comb's two additions, as a function**: from `ws` in `x0`, every slot's limbs below `Ib`
and 0 in slot 19, both sums, every register outside `fclob` (or kept) restored but `x3` and `x12`,
and the low halves of `v8`–`v15` restored. -/
theorem combAddFn_ok {s : State} (h : FnPre s) (hz : Bnd Mb s.mem (s.gpr .x0) (slot (19 : Index).val)) :
    WP isa combAddFn s fun u => FnPost false fclob s u (CombMem (s.gpr .x0) s.mem) ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x0 = b := ⟨_, rfl⟩
  rw [hbase] at hz ⊢
  unfold combAddFn
  rw [WP.seq_iff, csave_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (regs_ok s) fun s₀ ⟨g3, g12, gk, gm, gr, gw, gsp, gv⟩ => ?_
  refine WP.mono (insOf_ok cks s₀ (by decide) (by decide)) fun s₁ ⟨hg, hm, hr, hw, hsp, hls, hlo⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨by rw [hg, g3, hbase], by rw [hg, g12], by rw [hw, gw, ← hbase]; exact h.wr,
    by rw [← hbase]; exact h.nowrap⟩
  refine WP.mono (stqs_ok hs₁ (O := CSAVE) (by decide) (by decide)) fun s₂ ⟨sv₂, o₂, g₂, v₂, r₂, w₂, sp₂⟩ => ?_
  have hs₂ : Scr s₂ base := VG.Proof.Curve448.AArch64.Neon.scr_of hs₁ g₂ w₂
  have hm₂ : ∀ i : Index, ∀ j < 8, limbs s₂.mem base (slot i.val) j = limbs s.mem base (slot i.val) j :=
    fun i j hj => by
      rw [o₂.limbs (Or.inl (by have := i.isLt; simp only [slot, CSAVE]; omega)) (by have := i.isLt; simp only [slot]; omega)
        (by omega), hm, gm]
  have hb₂ : BEnv s₂.mem base := fun i j hj => by rw [hm₂ i j hj]; rw [← hbase]; exact h.env i j hj
  have hz₂ : Bnd Mb s₂.mem base (slot (19 : Index).val) := fun j hj => by rw [hm₂ 19 j hj]; exact hz j hj
  obtain ⟨tb, s₃, he, k₃, b₃, sm₃, bnd₃, e₃⟩ := combBody_ok hs₂ hb₂ hz₂
  obtain ⟨g3₃, f₃⟩ := Exec.storeFrame combStores he
  rw [hs₂.x3] at f₃
  rw [WP.seq_iff]
  refine ⟨tb, s₃, he, ?_⟩
  dsimp only
  have hs₃ := k₃.scr hs₂
  rw [crestore_eq, WP.block_append_iff]
  refine WP.mono (ldqs_ok hs₃ (O := CSAVE) (by decide) (by decide)) fun s₄ ⟨v₄, m₄, g₄, r₄, w₄, sp₄⟩ => ?_
  refine WP.mono (WP.preservedV (umovOf_ok cks s₄ (by decide) (by decide)) (by decide +kernel))
    fun u ⟨⟨um, ur, uw, usp, uls, uoth⟩, uvv⟩ => ?_
  -- `v8`–`v15` as saved, from `CSAVE`, which the additions keep.
  have vk : ∀ k < 8, s₄.v (V (8 + k)) = s₁.v (V (8 + k)) := fun k hk => by
    rw [v₄ k hk, ← sv₂ k hk]
    exact Mem.read_congr fun i hi => by
      rw [off_add]; exact f₃ _ (csave_unstored base (by simp only [CSAVE]; omega) (by simp only [CSAVE]; omega))
  have ck : ∀ x ∈ cks, ∃ k < 8, x.2.1 = V (8 + k) := by decide
  have kept : (VG.Impl.Ed448.AArch64.keptRegs false).map Prod.fst = cks.map Prod.fst := rfl
  have hfn : ∀ r, r ∉ cks.map Prod.fst → r ∉ fclob → u.gpr r = s₂.gpr r := fun r h1 h2 => by
    rw [uoth r h1, g₄, k₃.regs.1 r h2]
  refine ⟨⟨fun r hr h3 h12 => ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, fun i hi j hj => ?_, ?_, ?_, fun a ha => ?_⟩⟩,
    fun r hr => ?_⟩
  · by_cases hk : r ∈ cks.map Prod.fst
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      obtain ⟨k, hk8, hkv⟩ := ck x hx
      rw [uls x hx, ← gk _ h3 h12, ← hls x hx, laneOf, laneOf, hkv, vk k hk8]
    · have hf : r ∉ fclob := hr.resolve_right (fun e => hk (kept ▸ e))
      rw [hfn r hk hf, g₂, hg, gk r h3 h12]
  · rw [uoth _ (by decide), g₄, g3₃, hs₂.x3]; try exact hbase.symm
  · rw [uoth _ (by decide), g₄, k₃.regs.1 _ (by decide), hs₂.mask]
  · rw [ur, r₄, k₃.regs.2.1, r₂, hr, gr]
  · rw [uw, w₄, k₃.regs.2.2, w₂, hw, gw]
  · rw [usp, sp₄, Exec.sp he, sp₂, hsp, gsp]
  · rw [um, m₄]; exact b₃
  · rw [um, m₄, sm₃ i hi j hj, hm₂ i j hj]
  · rw [um, m₄]; exact bnd₃
  · rw [um, m₄, e₃]
    congr 2
    funext i
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (hm₂ i))
  · have hc : Unstored combOk base a := fun d hd => ha d (by
      simp only [combOk, fnOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd ⊢; omega)
    rw [um, m₄, f₃ a hc, o₂ a (unstored_csave ha), hm, gm]
  · obtain ⟨k, hk8, rfl⟩ := preservedV_V r hr
    rw [uvv _ hr, vk k hk8]
    have h0 := hlo (V (8 + k)) 0 (by decide) (by revert k; decide)
    simp only [laneOf, Nat.mul_zero] at h0
    rw [h0, gv]

end VG.Proof.Ed448.AArch64.Point56
