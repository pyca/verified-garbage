module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Encrypt
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Bitslicing the round keys, on PPC64LE

The key loop of `vg_aes_ctr32` and of the block functions bitslices each
round key (loaded as four identical blocks) with `toBs` and stores it in
the scratch buffer, from the last round key down, as on x86-64
(`Proof/Aes/X86_64/Group.lean`). The loads and stores are checked by
evaluation over the naming domain (`Bitslice.names`), `toBs` by its proof
(`Encrypt.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Aes.PPC64LE VG.Proof.Aes
open VG.Spec.Aes (roundKey)

/-- An access at an offset of a region. -/
theorem in_off {rs : List Region} {b : Addr} {len : Nat} (hr : (⟨b, len⟩ : Region) ∈ rs)
    {off n : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    InRegions rs (b + BitVec.ofNat 64 off) n :=
  ⟨_, hr, Offset.contains_base b h (by omega_arith)⟩

/-! ## Loading a round key -/

def loadCfg : Cfg := { base := sb, slots := 0, ext := .r3, exts := 2 }

def loadPost (e : Env Nat) : Bool :=
  (List.range 4).all fun b => e.reg (q b) == some 0 && e.reg (q (b + 4)) == some 1

theorem keyLoad_check :
    check (names 64) loadCfg (fun k => some k) keyLoad { reg := fun _ => none, slot := fun _ => none }
      loadPost = true := by
  decide +kernel

theorem keyLoad_writes :
    restRegs.all (fun r => keyLoad.all fun i => dstOf i != some r) = true := by
  decide +kernel

/-- The registers the key loop writes. -/
def keyWrites : List Reg := sboxWrites ++ [.r3, .r4, .r5]

theorem keyLoad_ok {s : State} {r : Region} {off : Nat} (hr : r ∈ s.rd ++ s.wr)
    (hb : s.gpr .r3 = r.base + BitVec.ofNat 64 off) (hoff : off + 16 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      (∀ b < 4, s'.gpr (q b) = s.mem.readW (wordAddr (s.gpr .r3) 0) 64 ∧
        s'.gpr (q (b + 4)) = s.mem.readW (wordAddr (s.gpr .r3) 1) 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ keyLoad_check
  have hok : Ok loadCfg s := Ok.of_ext (r := r) hr hb (by simp [loadCfg]; omega_arith) hn rfl
  let V : Nat → BitVec 64 := fun k => s.mem.readW (wordAddr (s.gpr .r3) k) 64
  have hrel : Rel (NameRel V) loadCfg (fun k => some k) { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_,
      fun _ _ h => by cases h⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  refine ⟨s', hs', fun b hb => ?_, p.rd, p.wr, ?_, fun r hr => p.other r ?_⟩
  · have := List.all_eq_true.mp hpost b (List.mem_range.mpr hb)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨p.rel.reg _ _ this.1, p.rel.reg _ _ this.2⟩
  · funext x
    exact p.frame x fun r' hr' hc => by
      simp only [List.mem_singleton] at hr'; subst hr'
      simp [slotRegion, loadCfg, Region.Contains] at hc
  · exact Bool.ne_false_of_eq_true (List.all_eq_true.mp keyLoad_writes r (not_sboxWrites r hr))

/-! ## Storing it -/

def storeCfg : Cfg := { base := .r5, slots := 8, ext := .r5, exts := 0 }

def storeEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)), slot := fun _ => none }

def storePost (e : Env Nat) : Bool := (List.range 8).all fun k => e.slot k == some k

theorem keyStore_check : check (names 64) storeCfg (fun _ => none) keyStore storeEnv storePost = true := by
  decide +kernel

theorem keyStore_noDst : keyStore.all (fun i => dstOf i == none) = true := by decide +kernel

theorem keyStore_ok {s : State} {r : Region} {off : Nat} (hr : r ∈ s.wr)
    (hb : s.gpr .r5 = r.base + BitVec.ofNat 64 off) (hoff : off + 64 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa keyStore s = some s' ∧
      (∀ k < 8, s'.mem.readW (wordAddr (s.gpr .r5) k) 64 = s.gpr (q k)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr .r5, 64⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ keyStore_check
  have hok : Ok storeCfg s := Ok.of_off (r := r) hr hb (by simp [storeCfg]; omega_arith) hn rfl
  let V : Nat → BitVec 64 := fun k => s.gpr (q k)
  have hrel : Rel (NameRel V) storeCfg (fun _ => none) storeEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [storeCfg] at hk),
      fun _ _ h => by cases h⟩
    simp only [storeEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot k k hk this
    rw [p.base] at h
    exact h
  · funext r
    exact p.other r (by
      have : (keyStore.all fun i => dstOf i != some r) = true :=
        List.all_eq_true.mpr fun i hi => by
          rw [beq_iff_eq.mp (List.all_eq_true.mp keyStore_noDst i hi)]
          rfl
      simp [this])

/-! ## Stepping back -/

theorem keyStep_ok (s : State) :
    ∃ s', runBlock isa keyStep s = some s' ∧
      s'.gpr .r3 = s.gpr .r3 - 16 ∧ s'.gpr .r5 = s.gpr .r5 - 64 ∧ s'.gpr .r4 = s.gpr .r4 - 1 ∧
      (∀ r, r ≠ .r3 → r ≠ .r5 → r ≠ .r4 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by rw [keyStep, runBlock_cons, exec_subi (by decide) (by decide), runStep_some,
    runBlock_cons, exec_subi (by decide) (by decide), runStep_some,
    runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil], ?_⟩
  simp only [State.write]
  refine ⟨by simp, by simp, by simp, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial, trivial,
    trivial⟩

/-! ## Readings and regions -/

theorem readW_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 8) (ht : t < 8) :
    (m.readW a 64).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, ht, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_setWidth]
  simp [show 8 * i + t < 64 by omega_arith]

theorem base_sub (b : Addr) {lx ly : Nat} (h : lx ≤ ly) (hy : ly < 2 ^ 64) :
    Region.Sub ⟨b, lx⟩ ⟨b + BitVec.ofNat 64 0, ly⟩ := by
  intro a h
  simp only [Region.Contains] at h ⊢
  bv_omega

/-! ## The loop -/

/-- Where the loop runs: the scratch buffer at `b`, the key schedule `w`
at `sc` (as the bytes there). -/
structure KSetup (s₀ : State) (b sc : Addr) (R : Nat) (w : List Byte) : Prop where
  scr : (⟨b, 2048⟩ : Region) ∈ s₀.wr
  base : s₀.gpr sb = b
  sch : (⟨sc, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr
  sep : Region.Disjoint ⟨sc, 240⟩ ⟨b, 2048⟩
  rounds : R ≤ 14
  w : ∀ i < 16 * (R + 1), w.getD i 0 = s₀.mem (sc + BitVec.ofNat 64 i)

/-- The address of bitsliced round key `i`. -/
abbrev keyAddr (b : Addr) (R i : Nat) : Addr := b + BitVec.ofNat 64 (1920 - 64 * (R - i))

/-- The memory the key loop writes. -/
abbrev kRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 0, 320⟩, ⟨b + BitVec.ofNat 64 1024, 1024⟩]

/-- Before bitslicing round key `j`. -/
structure KInv (s₀ : State) (b sc : Addr) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  r4 : s.gpr .r4 = BitVec.ofNat 64 (j + 1)
  r3 : s.gpr .r3 = sc + BitVec.ofNat 64 (16 * j)
  r5 : s.gpr .r5 = keyAddr b R j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame (kRegions b) s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R →
    KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i)

/-- After the loop. -/
structure KDone (s₀ : State) (b : Addr) (R : Nat) (w : List Byte) (s : State) : Prop where
  r5 : s.gpr .r5 = keyAddr b R 0 - 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame (kRegions b) s₀.mem s.mem
  keys : ∀ i ≤ R, KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i)

theorem roundKey_getD {w : List Byte} {j i : Nat} (hi : i < 16) :
    (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
  simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true,
    List.getElem?_drop]

theorem frame_regions (b : Addr) : ∀ r ∈ kRegions b, Region.Sub r ⟨b + BitVec.ofNat 64 0, 2048⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub b (by omega_arith) (by omega_arith)
  · exact Offset.sub b (by omega_arith) (by omega_arith)

theorem wordAddr_off (b : Addr) (x k : Nat) : wordAddr (b + BitVec.ofNat 64 x) k = b + BitVec.ofNat 64 (x + 8 * k) := by
  rw [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem readW_off_frame {m m' : Mem} {b : Addr} {rs : List Region} (hf : Frame rs m m') {x : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 x, 8⟩ r) :
    m'.readW (b + BitVec.ofNat 64 x) 64 = m.readW (b + BitVec.ofNat 64 x) 64 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The schedule's bytes are those of `w`. -/
theorem KInv.sched {s₀ : State} {b sc : Addr} {R : Nat} {w : List Byte} (hk : KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) {i : Nat} (hi16 : i < 16) :
    s.mem (sc + BitVec.ofNat 64 (16 * j + i)) = (roundKey w j).getD i 0 := by
  have hjR := hi.hj
  have hR := hk.rounds
  rw [roundKey_getD hi16, hk.w _ (by omega_arith)]
  refine hi.frame _ fun r hr hc => ?_
  have hsub := frame_regions b r hr
  refine hk.sep _ ?_ (by simpa using hsub _ hc)
  simp only [Region.Contains]
  rw [show sc + BitVec.ofNat 64 (16 * j + i) - sc = BitVec.ofNat 64 (16 * j + i) from
      VG.Offset.add_sub_cancel_left _ _,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- The round key as a state. -/
def rkv (w : List Byte) (j : Nat) : Spec.Aes.State := Vector.ofFn fun i => (roundKey w j).getD i 0

theorem keyRel_of_bs {K : Nat → BitVec 64} {w : List Byte} {j : Nat}
    (h : BsRel K fun _ => rkv w j) : KeyRel K (roundKey w j) := by
  intro b hb i hi
  rw [h b hb i hi, getD_eq _ hi, rkv, Vector.getElem_ofFn]

theorem keyWrites_not (r : Reg) (hr : r ∉ keyWrites) :
    r ∉ sboxWrites ∧ r ≠ .r3 ∧ r ≠ .r5 ∧ r ≠ .r4 := by
  revert hr; cases r <;> decide

theorem add_ofNat_sub (b : Addr) {x y : Nat} (h : y ≤ x) :
    b + BitVec.ofNat 64 x - BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x - y) := by
  rw [show x = (x - y) + y by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_succ_sub_one (j : Nat) : BitVec.ofNat 64 (j + 1) - 1 = BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

theorem keyAddr_pred (b : Addr) {R j : Nat} (hR : R ≤ 14) (hj : 0 < j) (hjR : j ≤ R) :
    keyAddr b R j - 64 = keyAddr b R (j - 1) := by
  simp only [keyAddr]
  have T := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (show (List.range 15).all (fun R =>
      (List.range 15).all fun j => decide (j ≤ R → 0 < j →
        1920 - 64 * (R - j) = (1920 - 64 * (R - (j - 1))) + 64)) = true by decide +kernel) R
      (List.mem_range.mpr (by omega_using [hR]))) j (List.mem_range.mpr (by omega_using [hR, hjR])))
  rw [T hjR hj, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_ne_zero {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j != 0) = decide (j ≠ 0) := by
  by_cases h0 : j = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 j ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
      exact h0 this
    simpa [h0] using this

theorem eval_nonzero_ofNat {s : State} {r : Reg} {j : Nat} (hr : s.gpr r = BitVec.ofNat 64 j)
    (h : j < 2 ^ 64) : isa.eval (.nonzero .d r) s = some (decide (j ≠ 0)) := by
  simp only [PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, hr, ofNat_ne_zero h]

theorem keyBody_ok {s₀ : State} {b sc : Addr} {R : Nat} {w : List Byte} (hk : KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) :
    WP isa (.block keyBody) s fun s' =>
      (j = 0 ∧ isa.eval (.nonzero .d .r4) s' = some false ∧ KDone s₀ b R w s') ∨
      (0 < j ∧ isa.eval (.nonzero .d .r4) s' = some true ∧ KInv s₀ b sc R w (j - 1) s') := by
  have hR := hk.rounds
  have hjR := hi.hj
  have hsb : s.gpr sb = b := by rw [hi.keep sb (by decide), hk.base]
  simp only [keyBody]
  repeat rw [WP.block_append_iff (M := isa)]
  -- Load the round key.
  obtain ⟨s₁, hs₁, hq₁, hrd₁, hwr₁, hm₁, hoth₁⟩ := keyLoad_ok (r := ⟨sc, 240⟩) (off := 16 * j)
    (by rw [hi.rd, hi.wr]; exact hk.sch) hi.r3 (by simp only; omega_arith) (by simp only; omega_arith)
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hin : InRel (Q s₁) fun _ => rkv w j := by
    intro bb hb i hi16 t ht
    have hbyte := hi.sched hk hi16
    rw [getD_eq _ hi16, rkv, Vector.getElem_ofFn]
    simp only [Q]
    by_cases h8 : i < 8
    · rw [show bb + 4 * (i / 8) = bb by omega_arith, (hq₁ bb hb).1, show i % 8 = i by omega_arith,
        readW_bit _ _ h8 ht, wordAddr, hi.r3, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega_arith
    · rw [show bb + 4 * (i / 8) = bb + 4 by omega_arith, (hq₁ bb hb).2, readW_bit _ _ (by omega_arith) ht,
        wordAddr, hi.r3, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega_arith
  -- Bitslice it.
  have hsb₁ : s₁.gpr sb = b := by rw [hoth₁ sb (by decide), hsb]
  have hok₁ : Ok linCfg s₁ := Ok.of_region (r := ⟨b, 2048⟩) (by rw [hwr₁, hi.wr]; exact hk.scr)
    hsb₁.symm (by simp only [linCfg]; omega) (by show 2048 < 2 ^ 64; decide) rfl
  obtain ⟨s₂, hs₂, hq₂, hrd₂, hwr₂, hoth₂, hfr₂⟩ := toBs_ok hok₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have hbs₂ := bs_of_in hq₂ hin
  -- Store it.
  have hr5₂ : s₂.gpr .r5 = keyAddr b R j := by
    rw [hoth₂ .r5 (by decide), hoth₁ .r5 (by decide), hi.r5]
  obtain ⟨s₃, hs₃, hst₃, hrd₃, hwr₃, hg₃, hfr₃⟩ := keyStore_ok (r := ⟨b, 2048⟩)
    (off := 1920 - 64 * (R - j)) (by rw [hwr₂, hwr₁, hi.wr]; exact hk.scr) hr5₂
    (by simp only; omega_arith) (by simp only; omega_arith)
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  -- Step back.
  obtain ⟨s₄, hs₄, hr3₄, hr5₄, hr4₄, hoth₄, hm₄, hrd₄, hwr₄⟩ := keyStep_ok s₃
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  -- What is kept.
  have hkeep : ∀ r, r ∉ keyWrites → s₄.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := keyWrites_not r hr
    rw [hoth₄ r h2 h3 h4, hg₃, hoth₂ r h1, hoth₁ r h1, hi.keep r hr]
  have hfr : Frame (kRegions b) s₀.mem s₄.mem := by
    rw [hm₄]
    refine hi.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hfr₂.sub fun r hr => ⟨_, List.mem_cons_self .., ?_⟩)
      (hfr₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, linCfg, hsb₁]
      exact base_sub b (by decide) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hr5₂]
      exact Offset.sub b (by omega_arith) (by omega_arith)
  -- The keys stored before.
  have hold : ∀ i, j < i → i ≤ R →
      KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i) := by
    intro i hji hiR
    refine keyRel_congr (hi.done i hji hiR) fun k hk => ?_
    simp only [keyAddr, wordAddr_off]
    rw [hm₄, readW_off_frame hfr₃ fun r hr => ?_, readW_off_frame hfr₂ fun r hr => ?_, hm₁]
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, linCfg, hsb₁]
      exact Offset.disjoint_base b (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hr5₂]
      exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  -- The key stored now.
  have hnew : KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R j) k) 64) (roundKey w j) :=
    keyRel_congr (keyRel_of_bs hbs₂) fun k hk => by rw [hm₄, ← hr5₂, hst₃ k hk]
  have hr4 : s₃.gpr .r4 = BitVec.ofNat 64 (j + 1) := by
    rw [hg₃, hoth₂ .r4 (by decide), hoth₁ .r4 (by decide), hi.r4]
  have hr3 : s₃.gpr .r3 = sc + BitVec.ofNat 64 (16 * j) := by
    rw [hg₃, hoth₂ .r3 (by decide), hoth₁ .r3 (by decide), hi.r3]
  have hr5 : s₃.gpr .r5 = keyAddr b R j := by rw [hg₃, hr5₂]
  have hrd : s₄.rd = s₀.rd := by rw [hrd₄, hrd₃, hrd₂, hrd₁, hi.rd]
  have hwr : s₄.wr = s₀.wr := by rw [hwr₄, hwr₃, hwr₂, hwr₁, hi.wr]
  have hr4' : s₄.gpr .r4 = BitVec.ofNat 64 j := by rw [hr4₄, hr4, ofNat_succ_sub_one]
  have hev := eval_nonzero_ofNat hr4' (by omega_arith)
  by_cases h0 : j = 0
  · subst h0
    refine .inl ⟨rfl, by simpa using hev, ⟨by rw [hr5₄, hr5], hrd, hwr, hkeep, hfr, fun i hiR => ?_⟩⟩
    by_cases hi0 : i = 0
    · subst hi0; exact hnew
    · exact hold i (by omega_arith) hiR
  · refine .inr ⟨by omega_arith, by simpa [h0] using hev, ⟨by omega_arith, ?_, ?_, ?_, hrd, hwr, hkeep, hfr, ?_⟩⟩
    · rw [hr4', show j - 1 + 1 = j by omega_arith]
    · rw [hr3₄, hr3, show 16 * (j - 1) = 16 * j - 16 by omega_arith]
      exact add_ofNat_sub sc (y := 16) (by omega_arith)
    · rw [hr5₄, hr5]; exact keyAddr_pred b hk.rounds (by omega_arith) hi.hj
    · intro i hi' hiR
      by_cases hij : i = j
      · subst hij; exact hnew
      · exact hold i (by omega_arith) hiR

theorem keyLoop_ok {s₀ : State} {b sc : Addr} {R : Nat} {w : List Byte} (hk : KSetup s₀ b sc R w)
    {s : State} (hi : KInv s₀ b sc R w R s) :
    WP isa (.loop (.block keyBody) (.nonzero .d .r4)) s (KDone s₀ b R w) := by
  refine WP.loop (M := isa) (KInv s₀ b sc R w) (fun n s hs => ?_) R s hi
  refine WP.mono (keyBody_ok hk hs) fun s' h => ?_
  rcases h with ⟨_, hcf, hd⟩ | ⟨hn, hcf, hi'⟩
  · exact .inl ⟨hcf, hd⟩
  · exact .inr ⟨hcf, n - 1, by omega_arith, hi'⟩

end VG.Proof.Aes.PPC64LE
