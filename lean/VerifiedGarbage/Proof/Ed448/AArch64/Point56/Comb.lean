import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Body
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Verified
import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Base.Step
import VerifiedGarbage.Proof.X448.AArch64.Fast.VSave

/-!
# Ed448's comb on AArch64: the additions as a function, and the steps calling it

Untrusted: everything here is checked by Lean. One module, so that few others
import the AdvSIMD products' algebra (`ci/check_lean_speed.py`).

* `vg_ed448_r56_comb_add` (`combAddFn`) runs the comb's two affine additions
  (`combBody_ok`, by `addAffine_ok`), whose AdvSIMD products use every vector
  register: so it keeps `x21`–`x28` in the upper halves of `v8`–`v15`, whose
  lower halves are callee-saved, stores those at `CSAVE` (`stqs_ok`), and
  loads them back (`ldqs_ok`) at the end. The additions store only to slots
  0–5 and 10–18 and the products' coefficients but `CSAVE` (`combStores`,
  `Exec.storeFrame`), so the saved registers survive them (`combAddFn_ok`).
* `fnCallV_ok`: `fnCall_ok` for a function that keeps the low halves of
  `v8`–`v15` by restoring them, rather than by never writing them.
  `combAddCall_ok`: a call of `vg_ed448_r56_comb_add`, as the inlined
  additions.
* `combStep`: step `j` of the comb, both entries negated first and added by
  one call of `vg_ed448_r56_comb_add` (`combAddCall_ok`), takes the invariant
  (`StepInv`) from `j` to `j + 1` but for the return address, which the call
  overwrites and the loop keeps in a lane of `v8` (`StepInvC`). `combLoop_ok`:
  the loop, between that lane's save and restore.
* The function meets `combAddContract` of `Spec/Ed448/Point56.lean`, with no
  stack: the proof against `combF`, from `combAddFn_ok`. The sums are `affPt`
  of each point with `(x : y : 1)` (`affEnv_A`, `affEnv_B`; the first addition
  keeps what the second reads, `affEnv_keep`), which is `pointAdd`
  (`affPt_eq`, `addPt_eq`), and the bytes kept are those no store covers
  (`keeps_of_unstored`). Constant time by taint tracking: only the pointer, in
  `x0`, is public, and every address is `ws` plus a constant.
-/

/-! # The two affine additions, as a function -/

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

theorem csave_eq : csave = (([.addImm .x .x3 .x0 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] : List Instr) ++
    insOf cks) ++
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
  refine WP.mono (WP.preservedV (umovOf_ok cks s₄ (by decide) (by decide)) (by lit_decide))
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

/-! # Calls of the additions -/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

/-- **A call** of a function `fn` that, from `ws` (`base`) in `x0`, every slot's limbs below `Ib`
and `P` of the memory, ends in `FnPost` with `Q` of the memories and the low halves of
`v8`–`v15` restored, which keeps the memory outside the slots and the products'
coefficients. -/
theorem fnCallV_ok {name : String} {c : Bool} {rs : List Reg} {fn : Prog isa} {base : Addr}
    {P : Mem → Prop} {Q : Mem → Mem → Prop}
    (hrs : ∀ r, r ∉ .x30 :: fclob → r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst)
    (hpk : ∀ r ∈ preserved, r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst)
    (hfn : ∀ t, FnPre t → t.gpr .x0 = base → P t.mem → WP isa fn t fun u => FnPost c rs t u (Q t.mem) ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hframe : ∀ m m', Q m m' → Outside2 base 64 2816 ACC 1152 m m') (hnf : fn.noFrames = true)
    {s : State} (hs : Scr s base) (hb : BEnv s.mem base) (hp : P s.mem) :
    WP isa (fnCall name fn) s fun t => CKeep base s t ∧ Q s.mem t.mem := by
  have hpres : ∀ r ∈ preserved, (r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst) ∧ r ≠ .x3 ∧ r ≠ .x12 :=
    fun r hr => ⟨hpk r hr, by revert hr; cases r <;> decide,
      by revert hr; cases r <;> decide⟩
  unfold fnCall
  rw [WP.seq_iff]
  refine WP.of_runBlock ⟨s.write .x .x0 (s.gpr .x3 + BitVec.ofNat 64 0), ?_, ?_⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      show (0 : Nat) < 4096 from by decide, ite_true, BitVec.setWidth_eq]
  generalize hs1 : s.write .x .x0 (s.gpr .x3 + BitVec.ofNat 64 0) = s1
  have g0 : s1.gpr .x0 = base := by
    rw [← hs1, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero, hs.x3]
  have gk : ∀ r, r ≠ .x0 → s1.gpr r = s.gpr r := fun r hr => by
    rw [← hs1, RegUpd.gpr_write_of_ne _ _ _ hr]
  have m1 : s1.mem = s.mem := by rw [← hs1]; rfl
  have r1 : s1.rd = s.rd := by rw [← hs1]; rfl
  have w1 : s1.wr = s.wr := by rw [← hs1]; rfl
  have sp1 : s1.sp = s.sp := by rw [← hs1]; rfl
  have v1 : s1.v = s.v := by rw [← hs1]; rfl
  have hcov : Covers [⟨base, 8192⟩] s1.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton.mp hr, w1]; exact hs.wr
  refine WP.callV (k := fnK c rs base P Q) (rd := []) (wr := [⟨base, 8192⟩]) ?hv
    ⟨rfl, rfl, by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0], hs.nowrap,
      by rw [State.withRegions_mem, State.callEntry_mem, m1]; exact hb,
      by rw [State.withRegions_mem, State.callEntry_mem, m1]; exact hp⟩
    (Covers.right hcov) hcov ?_ hnf
  case hv =>
    intro t ⟨_, hwr, hx0, hn, hbt, hpt⟩
    have fp : FnPre t := ⟨by rw [hwr, hx0]; exact List.mem_singleton_self _, by rw [hx0]; exact hn,
      by rw [hx0]; exact hbt⟩
    obtain ⟨tr, t', he, hpost, hv⟩ := hfn t fp hx0 hpt
    exact ⟨tr, t', he, ⟨fun r hr => hpost.1 r (hpres r hr).1 (hpres r hr).2.1 (hpres r hr).2.2,
      hpost.2.2.2.2.2.1, hv⟩, hpost⟩
  intro t hrd hwr hsp _ _ _ hv ⟨hg, h3, h12, _, _, _, hq⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, m1] at hg h3 h12 hq
  refine ⟨⟨⟨fun r hr => ?_, by rw [hrd, r1], by rw [hwr, w1]⟩, by rw [hsp, sp1], hframe _ _ hq,
    fun r hr => by rw [hv r hr, v1]⟩, hq⟩
  by_cases e3 : r = .x3
  · subst e3; rw [h3, State.callEntry_gpr _ (by decide), g0, hs.x3]
  by_cases e12 : r = .x12
  · subst e12; rw [h12, hs.mask]
  have hl : r ∉ VG.AArch64.linkRegs := by
    simp only [List.mem_cons, not_or] at hr
    simp only [VG.AArch64.linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, hr.1⟩ <;> intro h <;> subst h <;> exact absurd hr.2 (by decide)
  have h0 : r ≠ .x0 := fun h => by subst h; exact hr (by decide)
  rw [hg r (hrs r hr) e3 e12, State.callEntry_gpr _ hl, gk r h0]

theorem fnOk_slots : ∀ d, fnOk d = true → 64 ≤ d ∧ d + 8 ≤ 2880 ∨ 3584 ≤ d ∧ d + 8 ≤ 4736 := by
  intro d hd; simp only [fnOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd; omega

/-- **A call of `vg_ed448_r56_comb_add`**, as the inlined additions. -/
theorem combAddCall_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa Point56.combAddCall s fun t => CKeep base s t ∧ CombMem base s.mem t.mem :=
  fnCallV_ok (c := false) (P := fun m => Bnd Mb m base (slot (19 : Index).val))
    (fun r hr => .inl fun h => hr (List.mem_cons_of_mem _ h)) (by decide)
    (fun t ht h0 hp => by
      refine WP.mono (combAddFn_ok ht (by rw [h0]; exact hp)) fun u hu => ?_
      rw [h0] at hu; exact hu)
    (fun m m' hq => outside2_of fnOk_slots hq.2.2.2.2) (by decide +kernel) hs hb hz

end VG.Proof.Ed448.AArch64.Point56

/-! # The steps, calling the additions -/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base VG.Impl.Ed448.AArch64.Point56
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (nib mag addPt addPt_rep basePt negAff baseEntry_ok nib_lt mag_lt combG oddSumZ evenSumZ)
open VG.Proof.X448.AArch64.Base (StepInv Bits TblAt Masks Selected digits_ok select_ok selected_env negate_ok
  next_ok entrySlots entry_eq acc_step affEnv affPt_eq pt temps zero_env)
open VG.Proof.Ed448 (Rep baseAff)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `StepInv` but for the return address, kept in the low half of `v8`. -/
structure StepInvC (n : Nat) (s₀ : State) (base : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ n
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  bits : Bits n base k s.mem
  odd : Rep (pt (EV s.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k j) • baseAff)
  even : Rep (pt (EV s.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k j) • baseAff)
  lane : (s.v .v8).extractLsb' 0 64 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem
  tbl : TblAt s base (s₀.syms combSym)

theorem combStep_eq (n : Nat) : combStep n =
    .seq (.block digits) (.seq (.block select) (.seq (.block (
      negate (slot (6 : Index).val) (BITS + 4) (slot (10 : Index).val) ++
      negate (slot (8 : Index).val) BITS (slot (10 : Index).val))) (.seq combAddCall
      (.block ([.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n] : List Instr))))) := rfl

theorem digits_keepsV : (Code.block digits : Prog isa).allInstrs keepsV = true := by lit_decide
theorem select_keepsV : (Code.block select : Prog isa).allInstrs keepsV = true := by lit_decide
theorem negO_keepsV : (Code.block (negate (slot (6 : Index).val) (BITS + 4) (slot (10 : Index).val)) : Prog isa).allInstrs
    keepsV = true := by lit_decide
theorem negE_keepsV : (Code.block (negate (slot (8 : Index).val) BITS (slot (10 : Index).val)) : Prog isa).allInstrs
    keepsV = true := by lit_decide
theorem next_keepsV (n : Nat) :
    (Code.block ([.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n] : List Instr) : Prog isa).allInstrs keepsV =
      true := rfl

/-- An addition's environment keeps every slot but its result's and the temporaries. -/
theorem affEnv_keep (x1 y1 z1 x2 y2 : Index) (e : Env) (i : Index)
    (hi : i ∉ [x1, y1, z1, 10, 11, 12, 13, 14, 15, 16, 17, 18]) : affEnv x1 y1 z1 x2 y2 e i = e i := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  obtain ⟨h1, h2, h3, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hi
  simp only [affEnv, VG.Proof.X448.AArch64.opCopy, Function.update_apply, h1, h2, h3, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, ite_false]

theorem bits_of_out2 {base : Addr} {n k : Nat} {s : State} {m m' : Mem} (hn : n ≤ 57) (hs : Scr s base)
    (h : Bits n base k m) (hk : Outside2 base 64 2816 ACC 1152 m m') : Bits n base k m' := fun q hq => by
  have hn := hs.nowrap
  rw [hk _ (by rw [VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
  exact h q hq

theorem combStep_ok {n : Nat} (hn : n ≤ 57) {s₀ s : State} {base : Addr} {k j : Nat}
    (h : StepInvC n s₀ base k j s) (hj : j < n) (hsy : s.syms = s₀.syms) :
    WP isa (combStep n) s fun t =>
      (t.gpr .x9 != 0) = decide (j + 1 ≠ n) ∧ StepInvC n s₀ base k (j + 1) t := by
  obtain ⟨_, hs, hb, hz, hc, hbits, hodd, heven, hlane, hout, hrd, hwr, hmem, htbl⟩ := h
  have no := nib_lt k (2 * j + 1)
  have ne := nib_lt k (2 * j)
  rw [combStep_eq n]
  -- The digits.
  refine WP.seq (WP.mono_syms (WP.preservedV (digits_ok hs hn hj hc hbits) digits_keepsV)
    fun t1 ⟨⟨d1, m1⟩, v1⟩ sy1 => ?_)
  have hs1 : Scr t1 base := hs.of_keeps d1.keeps (by decide)
  have hb1 : BEnv t1.mem base := by rw [m1]; exact hb
  have hm1 : Masks (mag (nib k (2 * j + 1))) (mag (nib k (2 * j))) t1 :=
    ⟨d1.oddMask, d1.evenMask, d1.oddZero, d1.evenZero⟩
  have hc1 : t1.gpr .x19 = BitVec.ofNat 64 j := by rw [d1.keeps.1 _ (by decide)]; exact hc
  -- The selection.
  have tb1 : TblAt t1 base (s₀.syms combSym) :=
    htbl.of_far (by rw [d1.keeps.2.1, d1.keeps.2.2]) fun x _ => by rw [m1]
  refine WP.seq (WP.mono (WP.preservedV (select_ok hs1 tb1 (by rw [sy1, hsy]) (by omega) hc1 (mag_lt no)
    (mag_lt ne) hm1) select_keepsV) fun t2 ⟨h2, v2⟩ => ?_)
  obtain ⟨b2, s2, v6, v7, v8, v9, bnd2⟩ := selected_env hs1 hb1 h2
  have hs2 : Scr t2 base := hs1.of_keeps h2.2.2 (by decide)
  have hc2 : t2.gpr .x19 = BitVec.ofNat 64 j := by rw [h2.2.2.1 _ (by decide)]; exact hc1
  have bits2 : Bits n base k t2.mem := fun q hq => by
    have hn := hs.nowrap
    have ho : VG.Proof.X448.AArch64.ofs base (off base (BITS + q)) = BITS + q :=
      VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [BITS]; omega)
    rw [h2.2.1 _ (by rw [ho]; simp only [OX, BITS, slot]; omega), m1]
    exact hbits q hq
  have z2 : ∀ w < 8, limbs t2.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s2 19 (by decide) w hw]; rw [m1]; exact hz w hw
  have e1 : EV t1.mem base = EV s.mem base := by rw [m1]
  -- Both entries, negated for negative digits.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.preservedV (negate_ok hs2 b2 (k := k) (i := 2 * j + 1)
    (o := BITS + 4) 6 (by decide) hn (by omega) (by omega) (by simp only [BITS]; omega)
    (by simp only [BITS]; omega) hc2 bits2 (bnd2 6 (by decide)) (zero_env z2).2) negO_keepsV)
    fun t3 ⟨⟨k3, b3, s3, e3⟩, v3⟩ => ?_
  refine WP.mono (WP.preservedV (negate_ok (k3.scr hs2) b3 (k := k) (j := j) (i := 2 * j) (o := BITS) 8 (by decide) hn
    (by omega) (by omega) (by omega) (by simp only [BITS]; omega) (by rw [k3.regs.1 _ (by decide)]; exact hc2)
    (VG.Proof.X448.AArch64.Base.Bits.of_fkeep hn hs2 bits2 k3) (s3.bnd (by decide) (bnd2 8 (by decide)))
    (s3.bnd (by decide) (zero_env z2).2)) negE_keepsV) fun t5 ⟨⟨k5, b5, s5, e5⟩, v5'⟩ => ?_
  have hs3 := k3.scr hs2
  have hs5 := k5.scr hs3
  have z5 : ∀ w < 8, limbs t5.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s5 19 (by decide) w hw, s3 19 (by decide) w hw]; exact z2 w hw
  have hc5 : t5.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k5.regs.1 .x19 (by decide), k3.regs.1 .x19 (by decide)]; exact hc2
  -- Both added, by a call.
  refine WP.seq (WP.mono (combAddCall_ok hs5 b5 (zero_env z5).2) fun t6 ⟨k6, b6, s6, _, e6, _⟩ => ?_)
  have hs6 := k6.scr hs5
  have hc6 : t6.gpr .x19 = BitVec.ofNat 64 j := by rw [k6.regs.1 .x19 (by decide)]; exact hc5
  -- The counter.
  refine WP.mono (WP.preservedV (next_ok t6 hn hj hc6) (next_keepsV n)) fun t7 ⟨⟨c7, n7, k7, m7⟩, vn7⟩ =>
    ⟨n7, ?_⟩
  have hs7 : Scr t7 base := hs6.of_keeps k7 (by decide)
  have z6 : ∀ w < 8, limbs t6.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s6 19 (by decide) w hw]; exact z5 w hw
  -- Values of the slots along the way.
  have e2s : ∀ i : Index, i ∉ entrySlots → EV t2.mem base i = EV s.mem base i := fun i hi => by
    rw [Same.env s2 hi, e1]
  have z2v : EV t2.mem base 19 = 0 := (zero_env z2).1
  have t3o : ∀ i : Index, i ≠ 6 → i ≠ 10 → EV t3.mem base i = EV t2.mem base i := fun i h6 h10 => by
    rw [e3]; simp only [VG.Proof.X448.AArch64.opSwap, Function.update_apply, h6, h10, ite_false]
  have t36 : EV t3.mem base 6 =
      if decide (nib k (2 * j + 1) < 8) then EV t2.mem base 19 - EV t2.mem base 6 else EV t2.mem base 6 := by
    rw [e3]; simp only [VG.Proof.X448.AArch64.opSwap, Function.update_apply, show (6 : Index) ≠ 10 by decide, ite_false, ite_true]
  have t5o : ∀ i : Index, i ≠ 8 → i ≠ 10 → EV t5.mem base i = EV t3.mem base i := fun i h8 h10 => by
    rw [e5]; simp only [VG.Proof.X448.AArch64.opSwap, Function.update_apply, h8, h10, ite_false]
  have t58 : EV t5.mem base 8 =
      if decide (nib k (2 * j) < 8) then EV t3.mem base 19 - EV t3.mem base 8 else EV t3.mem base 8 := by
    rw [e5]; simp only [VG.Proof.X448.AArch64.opSwap, Function.update_apply, show (8 : Index) ≠ 10 by decide, ite_false, ite_true]
  have t5v : ∀ i : Index, i ≠ 6 → i ≠ 8 → i ≠ 10 → EV t5.mem base i = EV t2.mem base i := fun i h6 h8 h10 => by
    rw [t5o i h8 h10, t3o i h6 h10]
  have t56 : EV t5.mem base 6 = EV t3.mem base 6 := t5o 6 (by decide) (by decide)
  -- The accumulators.
  have pA : pt (EV t6.mem base) 0 1 2 = addPt (pt (EV s.mem base) 0 1 2)
      (basePt (if nib k (2 * j + 1) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j + 1))))
        else Impl.X448.baseTable j (mag (nib k (2 * j + 1))))) := by
    have kB : pt (affEnv 3 4 5 8 9 (affEnv 0 1 2 6 7 (EV t5.mem base))) 0 1 2 =
        pt (affEnv 0 1 2 6 7 (EV t5.mem base)) 0 1 2 := by
      simp only [pt]
      rw [affEnv_keep _ _ _ _ _ _ 0 (by decide), affEnv_keep _ _ _ _ _ _ 1 (by decide),
        affEnv_keep _ _ _ _ _ _ 2 (by decide)]
    rw [e6, kB, VG.Proof.X448.AArch64.Base.affEnv_A,
      t5v 0 (by decide) (by decide) (by decide), t5v 1 (by decide) (by decide) (by decide),
      t5v 2 (by decide) (by decide) (by decide), t56, t36, t5v 7 (by decide) (by decide) (by decide),
      t5v 19 (by decide) (by decide) (by decide), z2v, v6, v7, e2s 0 (by decide), e2s 1 (by decide),
      e2s 2 (by decide), affPt_eq, entry_eq _ 0 rfl]
    rfl
  have pB : pt (EV t6.mem base) 3 4 5 = addPt (pt (EV s.mem base) 3 4 5)
      (basePt (if nib k (2 * j) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j))))
        else Impl.X448.baseTable j (mag (nib k (2 * j))))) := by
    rw [e6, VG.Proof.X448.AArch64.Base.affEnv_B,
      affEnv_keep _ _ _ _ _ _ 3 (by decide), affEnv_keep _ _ _ _ _ _ 4 (by decide),
      affEnv_keep _ _ _ _ _ _ 5 (by decide), affEnv_keep _ _ _ _ _ _ 8 (by decide),
      affEnv_keep _ _ _ _ _ _ 9 (by decide), affEnv_keep _ _ _ _ _ _ 19 (by decide),
      t5v 3 (by decide) (by decide) (by decide), t5v 4 (by decide) (by decide) (by decide),
      t5v 5 (by decide) (by decide) (by decide), t58, t3o 8 (by decide) (by decide),
      t3o 19 (by decide) (by decide), t5v 9 (by decide) (by decide) (by decide),
      t5v 19 (by decide) (by decide) (by decide), z2v, v8, v9, e2s 3 (by decide), e2s 4 (by decide),
      e2s 5 (by decide), affPt_eq, entry_eq _ 0 rfl]
    rfl
  have fk : ∀ r, r ∉ .x30 :: fclob → r ∉ [Reg.x19, .x9] → t7.gpr r = t5.gpr r := fun r h1 h2 => by
    rw [k7.1 r h2, k6.regs.1 r h1]
  have hk35 : FKeep base t2 t5 := k3.trans k5
  have bits7 : Bits n base k t7.mem := by
    rw [m7]
    exact bits_of_out2 hn hs5
      (VG.Proof.X448.AArch64.Base.Bits.of_fkeep hn hs3 (VG.Proof.X448.AArch64.Base.Bits.of_fkeep hn hs2 bits2 k3) k5)
      k6.mem
  refine ⟨by omega, hs7, by rw [m7]; exact b6, by rw [m7]; exact z6, c7, bits7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show pt (EV t7.mem base) 0 1 2 = pt (EV t6.mem base) 0 1 2 by rw [m7], pA]
    have := addPt_rep hodd (baseEntry_ok j (nib k (2 * j + 1)) (by omega) no)
    rw [acc_step] at this
    exact this
  · rw [show pt (EV t7.mem base) 3 4 5 = pt (EV t6.mem base) 3 4 5 by rw [m7], pB]
    have := addPt_rep heven (baseEntry_ok j (nib k (2 * j)) (by omega) ne)
    rw [acc_step] at this
    exact this
  · rw [vn7 .v8 (by decide), k6.v .v8 (by decide), v5' .v8 (by decide), v3 .v8 (by decide), v2 .v8 (by decide),
      v1 .v8 (by decide)]
    exact hlane
  · rw [fk .x20 (by decide) (by decide), k5.regs.1 .x20 (by decide), k3.regs.1 .x20 (by decide),
      h2.2.2.1 .x20 (by decide), d1.keeps.1 .x20 (by decide)]; exact hout
  · rw [k7.2.1, k6.regs.2.1, k5.regs.2.1, k3.regs.2.1, h2.2.2.2.1, d1.keeps.2.1]; exact hrd
  · rw [k7.2.2, k6.regs.2.2, k5.regs.2.2, k3.regs.2.2, h2.2.2.2.2, d1.keeps.2.2]; exact hwr
  · rw [m7]
    refine Outside2.trans hmem ?_
    rw [← m1]
    exact (((VG.Proof.X448.AArch64.Base.Selected.outside2 h2).trans k3.mem).trans k5.mem).trans k6.mem
  · refine htbl.of_outside2 (by rw [k7.2.1, k6.regs.2.1, k5.regs.2.1, k3.regs.2.1,
      h2.2.2.2.1, d1.keeps.2.1, k7.2.2, k6.regs.2.2, k5.regs.2.2, k3.regs.2.2,
      h2.2.2.2.2, d1.keeps.2.2]) ?_
    rw [m7, ← m1]
    exact (((VG.Proof.X448.AArch64.Base.Selected.outside2 h2).trans k3.mem).trans k5.mem).trans k6.mem

/-- **The comb's loop, calling the additions**, as `loop_ok`: `StepInv` from step 0 to `n`, with
the return address kept in a lane of `v8` across it. -/
theorem combLoop_ok {n : Nat} (hn : n ≤ 57) (hn1 : 1 ≤ n) {s₀ s : State} {base : Addr} {k : Nat}
    (h : StepInv n s₀ base k 0 s) (hsy : s.syms = s₀.syms) :
    WP isa (combLoop n) s fun t => StepInv n s₀ base k n t := by
  unfold combLoop
  rw [WP.seq_iff]
  refine WP.mono_syms (insOf_ok [(.x30, .v8, 0)] s (by decide) (by decide))
    fun t₁ ⟨g₁, m₁, r₁, w₁, _, l₁, _⟩ sy₁ => ?_
  have h₁ : StepInvC n s₀ base k 0 t₁ :=
    ⟨h.bound, h.scr.of_keeps (rs := []) ⟨fun r _ => by rw [g₁], r₁, w₁⟩ (by decide), m₁ ▸ h.env, m₁ ▸ h.zero,
      by rw [g₁]; exact h.counter, m₁ ▸ h.bits, m₁ ▸ h.odd, m₁ ▸ h.even,
      (l₁ _ List.mem_cons_self).trans h.lr, by rw [g₁]; exact h.out, by rw [r₁]; exact h.rd,
      by rw [w₁]; exact h.wr, m₁ ▸ h.mem,
      h.tbl.of_far (by rw [r₁, w₁]) fun x _ => by rw [m₁]⟩
  rw [WP.seq_iff]
  refine WP.mono (WP.loop (M := isa) (body := combStep n) (c := .nonzero .x .x9)
    (Q := fun t => StepInvC n s₀ base k n t)
    (fun m (t : State) => 1 ≤ m ∧ m ≤ n ∧ StepInvC n s₀ base k (n - m) t ∧ t.syms = s₀.syms) ?_ n t₁
    ⟨hn1, le_refl _, by rw [Nat.sub_self]; exact h₁, sy₁.trans hsy⟩) fun t ht => ?_
  · intro m t ⟨h1, h2, ht, htsy⟩
    refine WP.mono_syms (combStep_ok hn ht (by omega) htsy) fun u ⟨hz, hu⟩ usy => ?_
    simp only [eval, State.read, BitVec.setWidth_eq, hz]
    by_cases hm : m = 1
    · subst hm
      rw [show n - 1 + 1 = n by omega] at hu ⊢
      exact .inl ⟨by simp, hu⟩
    · refine .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ?_,
        usy.trans htsy⟩
      rw [show n - (m - 1) = n - m + 1 by omega]
      exact hu
  · refine WP.mono (umovOf_ok [(.x30, .v8, 0)] t (by decide) (by decide)) fun u ⟨um, ur, uw, _, ul, uo⟩ => ?_
    have ku : Keeps [.x30] t u := ⟨fun r hr => uo r (by simpa using hr), ur, uw⟩
    exact ⟨ht.bound, ht.scr.of_keeps ku (by decide), um ▸ ht.env, um ▸ ht.zero,
      by rw [ku.1 _ (by decide)]; exact ht.counter, um ▸ ht.bits, um ▸ ht.odd, um ▸ ht.even,
      (ul _ List.mem_cons_self).trans ht.lane, by rw [ku.1 _ (by decide)]; exact ht.out,
      by rw [ur]; exact ht.rd, by rw [uw]; exact ht.wr, um ▸ ht.mem,
      ht.tbl.of_far (by rw [ur, uw]) fun x _ => by rw [um]⟩

end VG.Proof.Ed448.AArch64.Point56

/-! # `vg_ed448_r56_comb_add`, verified -/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt affEnv affPt_eq)
open VG.Spec.X448.Field56 (slotAt elemAt Bounded Res)
open VG.Spec.Ed448.Point56 (pointAt affineAt combWritten)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

def combF : Contract AArch64.isa where
  pre s := fPre s ∧ Bounded s.mem (s.gpr .x0) ∧ Res s.mem (s.gpr .x0) 19 ∧
    elemAt s.mem (s.gpr .x0) (slotAt 19) = 0
  post s s' := Bounded s'.mem (s.gpr .x0) ∧ (∀ n < 6, Res s'.mem (s.gpr .x0) n) ∧
    pointAt s'.mem (s.gpr .x0) 0 = Spec.Ed448.pointAdd (pointAt s.mem (s.gpr .x0) 0) (affineAt s.mem (s.gpr .x0) 6) ∧
    pointAt s'.mem (s.gpr .x0) 3 = Spec.Ed448.pointAdd (pointAt s.mem (s.gpr .x0) 3) (affineAt s.mem (s.gpr .x0) 8) ∧
    Spec.X448.Field56.Keeps (s.gpr .x0) combWritten s.mem s'.mem
  pub := fPub

theorem pointAt_eqN (m : Mem) (ws : Addr) (n : Nat) (x y z : Index) (hx : x.val = n) (hy : y.val = n + 1)
    (hz : z.val = n + 2) : pointAt m ws n = pt (EV m ws) x y z := by
  simp only [pointAt, pt]
  subst hx; rw [← hy, ← hz, elemAt_eq, elemAt_eq, elemAt_eq]

theorem affineAt_eq (m : Mem) (ws : Addr) (n : Nat) (x y : Index) (hx : x.val = n) (hy : y.val = n + 1) :
    affineAt m ws n = ⟨EV m ws x, EV m ws y, 1⟩ := by
  simp only [affineAt]
  subst hx; rw [← hy, elemAt_eq, elemAt_eq]

theorem fnOk_combWritten : ∀ d, fnOk d = true → d + 8 ≤ 8192 ∧ ∃ r ∈ combWritten, r.1 ≤ d ∧ d + 8 ≤ r.2 := by
  intro d hd
  simp only [fnOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd
  simp only [combWritten, Spec.X448.Field56.own, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, slotAt, Spec.X448.Field56.accAt, Spec.X448.Field56.accEnd]
  omega

theorem comb_arm (s : State) (hs : combF.pre s) :
    ∃ t s', Exec isa Point56.combAddFn s t s' ∧ abiPreserved s s' ∧ combF.post s s' := by
  obtain ⟨hp, hb, hr, hz⟩ := hs
  have hz' : EV s.mem (s.gpr .x0) 19 = 0 := by rw [← hz]; exact (elemAt_eq _ _ 19).symm
  obtain ⟨t, u, he, hpost, hv⟩ := combAddFn_ok (fnPre_of hp hb) hr
  obtain ⟨b, -, hres, e, hf⟩ := hpost.2.2.2.2.2.2
  obtain ⟨hg, hsp⟩ := abi_of hpost (by decide)
  refine ⟨t, u, he, ⟨hg, hsp, hv⟩, (bounded_iff _ _).mpr b,
    fun n hn => hres ⟨n, by omega⟩ hn, ?_, ?_, keeps_of_unstored fnOk_combWritten hf⟩
  · rw [pointAt_eqN _ _ 0 0 1 2 rfl rfl rfl, pointAt_eqN _ _ 0 0 1 2 rfl rfl rfl, affineAt_eq _ _ 6 6 7 rfl rfl, e]
    simp only [pt]
    rw [affEnv_keep _ _ _ _ _ _ 0 (by decide), affEnv_keep _ _ _ _ _ _ 1 (by decide),
      affEnv_keep _ _ _ _ _ _ 2 (by decide)]
    rw [show (⟨affEnv 0 1 2 6 7 (EV s.mem (s.gpr .x0)) 0, affEnv 0 1 2 6 7 (EV s.mem (s.gpr .x0)) 1,
        affEnv 0 1 2 6 7 (EV s.mem (s.gpr .x0)) 2⟩ : Spec.Ed448.Point) =
        pt (affEnv 0 1 2 6 7 (EV s.mem (s.gpr .x0))) 0 1 2 from rfl,
      VG.Proof.X448.AArch64.Base.affEnv_A, hz', affPt_eq, VG.Proof.X448.addPt_eq]
  · rw [pointAt_eqN _ _ 3 3 4 5 rfl rfl rfl, pointAt_eqN _ _ 3 3 4 5 rfl rfl rfl, affineAt_eq _ _ 8 8 9 rfl rfl, e,
      VG.Proof.X448.AArch64.Base.affEnv_B,
      affEnv_keep _ _ _ _ _ _ 3 (by decide), affEnv_keep _ _ _ _ _ _ 4 (by decide),
      affEnv_keep _ _ _ _ _ _ 5 (by decide), affEnv_keep _ _ _ _ _ _ 8 (by decide),
      affEnv_keep _ _ _ _ _ _ 9 (by decide), affEnv_keep _ _ _ _ _ _ 19 (by decide), hz', affPt_eq,
      VG.Proof.X448.addPt_eq]
    rfl

theorem comb_ct : ConstantTime isa combF.pre combF.pub Point56.combAddFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ hp => ⟨hp.2, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.1⟩) (by taint_decide)

theorem combAddFn_verified :
    Verified AArch64.target Point56.combAddFn (Spec.Ed448.Point56.combAddContract AArch64.abi) :=
  Verified.of_correct comb_arm comb_ct
    { pre := by sig_implies_pre [Spec.Ed448.Point56.combAddContract, Spec.Ed448.Point56.sig,
        Spec.Ed448.Point56.zeroSlot, combF, fPre, fPub, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ed448.Point56.combAddContract, Spec.Ed448.Point56.sig, Spec.Ed448.Point56.zeroSlot,
          combF, fPre, fPub, AArch64.abi, AArch64.argRegs]
        exact h
      pub := by sig_implies_pub [Spec.Ed448.Point56.combAddContract, Spec.Ed448.Point56.sig,
        Spec.Ed448.Point56.zeroSlot, combF, fPre, fPub, AArch64.abi, AArch64.argRegs]
      sat := ⟨satState, by
        unfold Spec.Ed448.Point56.combAddContract
        exact Sig.contract_pre_of_check (by decide +kernel) (by
          sig_reduce [Sig.wfPre, Spec.Ed448.Point56.sig, Spec.Ed448.Point56.zeroSlot, AArch64.abi,
            AArch64.argRegs, satState]
          exact ⟨by decide, sat_bounded, sat_res 19 (by decide), sat_zero⟩)⟩ }

end VG.Proof.Ed448.AArch64.Point56
