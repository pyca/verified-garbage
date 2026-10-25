module

public import VerifiedGarbage.Proof.Aes.RISCV64.Encrypt
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes

/-!
# Bitslicing the round keys, on RISC-V

As on PPC64LE (`Proof/Aes/PPC64LE/Keys.lean`): the key loop of
`vg_aes_ctr32` and of the block functions bitslices each round key (loaded
as four identical blocks, a byte at a time, `Bytes.loadLE64_ok`) with
`toBs` and stores it in the scratch buffer, from the last round key down.
The stores are checked by evaluation over the naming domain
(`Bitslice.names`), `toBs` by its proof (`Layers.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Wp VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes
open VG.Spec.Aes (roundKey)

/-! ## Loading a round key -/

theorem q_ne : ∀ i < 8, q i ≠ t0 ∧ q i ≠ t1 ∧ q i ≠ .a0 := by decide

theorem keyLoad_ok {s : State} {sc : Addr} {off : Nat} (hr : (⟨sc, 240⟩ : Region) ∈ s.rd ++ s.wr)
    (hb : s.gpr .a0 = sc + BitVec.ofNat 64 off) (hoff : off + 16 ≤ 240) :
    WP isa (.block keyLoad) s fun s' =>
      (∀ b < 4, s'.gpr (q b) = s.mem.readW (wordAddr (s.gpr .a0) 0) 64 ∧
        s'.gpr (q (b + 4)) = s.mem.readW (wordAddr (s.gpr .a0) 1) 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) := by
  have hin : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 d) 4 :=
    fun d hd => ⟨_, hr, by rw [hb, Offset.add_add]; exact Offset.contains_base sc (by omega) (by omega)⟩
  simp only [keyLoad]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Bytes.loadLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hin 0 (by omega)) (hin 4 (by omega))) fun s₁ ⟨h0, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have a₁ : s₁.gpr .a0 = s.gpr .a0 := g₁ _ (by decide) (by decide) (by decide)
  refine WP.mono (Bytes.loadLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [a₁, rd₁, wr₁]; exact hin 8 (by omega))
    (by rw [a₁, rd₁, wr₁]; exact hin 12 (by omega))) fun s₂ ⟨h4, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have q0 : s₂.gpr (q 0) = s.mem.readW (wordAddr (s.gpr .a0) 0) 64 := by
    rw [g₂ _ (by decide) (by decide) (by decide), h0]
  have q4 : s₂.gpr (q 4) = s.mem.readW (wordAddr (s.gpr .a0) 1) 64 := by
    rw [h4, a₁, m₁]
  simp only [movR]
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  have k0 : s₈.gpr (q 0) = s₂.gpr (q 0) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]
  have k4 : s₈.gpr (q 4) = s₂.gpr (q 4) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]
  refine ⟨fun b hb => ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · have e4' : s₅.gpr (q 4) = s₂.gpr (q 4) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    · exact ⟨k0.trans q0, k4.trans q4⟩
    · refine ⟨?_, ?_⟩
      · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, q0]
      · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, e4', q4]
    · refine ⟨?_, ?_⟩
      · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), q0]
      · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), e4', q4]
    · refine ⟨?_, ?_⟩
      · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), q0]
      · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), e4', q4]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁]
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, m₁]
  · have hn : r ≠ q 1 ∧ r ≠ q 2 ∧ r ≠ q 3 ∧ r ≠ q 5 ∧ r ≠ q 6 ∧ r ≠ q 7 ∧ r ≠ q 0 ∧ r ≠ q 4 ∧
        r ≠ t0 ∧ r ≠ t1 := by
      revert hr; cases r <;> decide
    obtain ⟨n1, n2, n3, n5, n6, n7, n0, n4, nt0, nt1⟩ := hn
    rw [u₈.other _ n7, u₇.other _ n6, u₆.other _ n5, u₅.other _ n3, u₄.other _ n2, u₃.other _ n1,
      g₂ _ n4 nt0 nt1, g₁ _ n0 nt0 nt1]

/-! ## Storing it -/

def storeCfg : Cfg := { base := .a2, slots := 8, ext := .a2, exts := 0 }

def storeEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map .v, slot := fun _ => none }

def storePost (e : Env Nat) : Bool := (List.range 8).all fun k => e.slot k == some k

theorem keyStore_check : check (names 64) storeCfg (fun _ => none) keyStore storeEnv storePost = true := by
  decide +kernel

theorem keyStore_noDst : keyStore.all (fun i => dst i == none) = true := by decide +kernel

theorem nameRel_fun {V : Nat → BitVec 64} (a : Nat) (x y : BitVec 64) (hx : NameRel V a x)
    (hy : NameRel V a y) : x = y := hx.trans hy.symm

theorem keyStore_ok {s : State} {X : Addr} (hs : Scr s X 2048) {off : Nat}
    (hb : s.gpr .a2 = s.gpr sb + BitVec.ofNat 64 off) (hoff : off + 64 ≤ 2040) (h8 : off % 8 = 0) :
    ∃ s', runBlock isa keyStore s = some s' ∧
      (∀ k < 8, s'.mem.readW (wordAddr (s.gpr .a2) k) 64 = s.gpr (q k)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr .a2, 64⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ keyStore_check
  have hal : (s.gpr .a2).toNat % 8 = 0 := by rw [hb, hs.base]; exact align_al_add X h8
  have hok : Ok storeCfg s :=
    { slotIn := fun k hk => ⟨_, hs.wr, by
        show (⟨X, 2048⟩ : Region).Contains (wordAddr (s.gpr .a2) k) 8
        rw [wordAddr, hb, Offset.add_add]
        exact hs.contains (by simp only [storeCfg] at hk; omega) (by decide)⟩
      extIn := fun k hk => by simp [storeCfg] at hk
      baseAl := hal
      extAl := hal
      slots := by simp [storeCfg]
      sep := fun k _ j hj => by simp [storeCfg] at hj }
  let V : Nat → BitVec 64 := fun k => s.gpr (q k)
  have hrel : Rel (NameRel V) storeCfg (fun _ => none) storeEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [storeCfg] at hk)⟩
    simp only [storeEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have h1 := List.find?_some hk
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) nameRel_fun hok hrel he
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, p.sp, ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot k k hk this
    rw [p.base] at h
    exact h
  · funext r
    exact p.other r (by
      have : (keyStore.all fun i => dst i != some r) = true :=
        List.all_eq_true.mpr fun i hi => by
          rw [beq_iff_eq.mp (List.all_eq_true.mp keyStore_noDst i hi)]
          rfl
      simp [this])

/-! ## Stepping back -/

theorem ofInt_neg (k : Nat) (hk : k < 2048) : BitVec.ofInt 64 (-(k : Int)) = -BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_neg, BitVec.toNat_ofNat]
  omega

theorem keyStep_ok (s : State) :
    ∃ s', runBlock isa keyStep s = some s' ∧
      s'.gpr .a0 = s.gpr .a0 - 16 ∧ s'.gpr .a2 = s.gpr .a2 - 64 ∧ s'.gpr .a1 = s.gpr .a1 - 1 ∧
      (∀ r, r ≠ .a0 → r ≠ .a2 → r ≠ .a1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by rw [keyStep, runBlock_cons, exec_addi (by decide), runStep_some,
    runBlock_cons, exec_addi (by decide), runStep_some,
    runBlock_cons, exec_addi (by decide), runStep_some, runBlock_nil], ?_⟩
  simp only [State.write]
  refine ⟨?_, ?_, ?_, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial, trivial, trivial, trivial⟩
  · simp only [ite_true, show ¬ (Reg.a0 = Reg.a1) by decide, show ¬ (Reg.a0 = Reg.a2) by decide,
      ite_false, BitVec.sub_eq_add_neg]
    rfl
  · simp only [ite_true, show ¬ (Reg.a2 = Reg.a1) by decide, ite_false, BitVec.sub_eq_add_neg]
    rfl
  · simp only [ite_true, BitVec.sub_eq_add_neg]
    rfl

/-! ## Readings and regions -/

theorem readW_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 8) (ht : t < 8) :
    (m.readW a 64).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, ht, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_setWidth]
  simp [show 8 * i + t < 64 by omega_arith]

/-! ## The loop -/

/-- Where the loop runs: the scratch buffer at `X`, rounded to `b`, with
the masks; the key schedule `w` at `sc` (as the bytes there). -/
structure KSetup (s₀ : State) (X b sc : Addr) (R : Nat) (w : List Byte) : Prop where
  scr : Scr s₀ X 2048
  base : s₀.gpr sb = b
  masks : MasksAt s₀.mem b allKs
  sch : (⟨sc, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr
  sep : Region.Disjoint ⟨sc, 240⟩ ⟨X, 2048⟩
  rounds : R ≤ 14
  w : ∀ i < 16 * (R + 1), w.getD i 0 = s₀.mem (sc + BitVec.ofNat 64 i)

/-- The address of bitsliced round key `i`. -/
abbrev keyAddr (b : Addr) (R i : Nat) : Addr := b + BitVec.ofNat 64 (1920 - 64 * (R - i))

/-- The memory the key loop writes. -/
abbrev kRegions (b : Addr) : List Region := [⟨b, 320⟩, ⟨b + BitVec.ofNat 64 1024, 960⟩]

/-- The registers the key loop writes. -/
def keyWrites : List Reg := sboxWrites ++ [.a0, .a1, .a2]

/-- Before bitslicing round key `j`. -/
structure KInv (s₀ : State) (b sc : Addr) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  a1 : s.gpr .a1 = BitVec.ofNat 64 (j + 1)
  a0 : s.gpr .a0 = sc + BitVec.ofNat 64 (16 * j)
  a2 : s.gpr .a2 = keyAddr b R j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame (kRegions b) s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R →
    KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i)

/-- After the loop. -/
structure KDone (s₀ : State) (b : Addr) (R : Nat) (w : List Byte) (s : State) : Prop where
  a2 : s.gpr .a2 = keyAddr b R 0 - 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame (kRegions b) s₀.mem s.mem
  keys : ∀ i ≤ R, KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i)

theorem roundKey_getD {w : List Byte} {j i : Nat} (hi : i < 16) :
    (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
  simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true,
    List.getElem?_drop]

theorem frame_regions {s₀ : State} {X b : Addr} (hs : Scr s₀ X 2048) (hb : s₀.gpr sb = b) :
    ∀ r ∈ kRegions b, Region.Sub r ⟨X, 2048⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have := pad_lt X
  rcases hr with rfl | rfl
  · rw [← hb, hs.base]; exact Offset.sub_base X (by omega)
  · rw [← hb]; exact hs.sub (by omega)

theorem wordAddr_off (b : Addr) (x k : Nat) : wordAddr (b + BitVec.ofNat 64 x) k = b + BitVec.ofNat 64 (x + 8 * k) := by
  rw [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem readW_off_frame {m m' : Mem} {b : Addr} {rs : List Region} (hf : Frame rs m m') {x : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 x, 8⟩ r) :
    m'.readW (b + BitVec.ofNat 64 x) 64 = m.readW (b + BitVec.ofNat 64 x) 64 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The schedule's bytes are those of `w`. -/
theorem KInv.sched {s₀ : State} {X b sc : Addr} {R : Nat} {w : List Byte}
    (hk : KSetup s₀ X b sc R w) {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) {i : Nat}
    (hi16 : i < 16) : s.mem (sc + BitVec.ofNat 64 (16 * j + i)) = (roundKey w j).getD i 0 := by
  have hjR := hi.hj
  have hR := hk.rounds
  rw [roundKey_getD hi16, hk.w _ (by omega_arith)]
  refine hi.frame _ fun r hr hc => ?_
  have hsub := frame_regions hk.scr hk.base r hr
  refine hk.sep _ ?_ (hsub _ hc)
  simp only [Region.Contains]
  rw [show sc + BitVec.ofNat 64 (16 * j + i) - sc = BitVec.ofNat 64 (16 * j + i) from
      VG.Offset.add_sub_cancel_left _ _,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- The masks stay. -/
theorem masks_kept {m₀ m : Mem} {b : Addr} (hf : Frame (kRegions b) m₀ m) (hm : MasksAt m₀ b allKs) :
    MasksAt m b allKs := by
  intro k v hk
  have := allKs_slots _ hk
  rw [← hm k v hk]
  refine hf.readW (r := ⟨wordAddr b k, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base b (by omega) (by omega)
  · exact Offset.disjoint b (by omega) (by omega) (by omega)

/-- The round key as a state. -/
def rkv (w : List Byte) (j : Nat) : Spec.Aes.State := Vector.ofFn fun i => (roundKey w j).getD i 0

theorem keyRel_of_bs {K : Nat → BitVec 64} {w : List Byte} {j : Nat}
    (h : BsRel K fun _ => rkv w j) : KeyRel K (roundKey w j) := by
  intro b hb i hi
  rw [h b hb i hi, getD_eq _ hi, rkv, Vector.getElem_ofFn]

theorem keyWrites_not (r : Reg) (hr : r ∉ keyWrites) :
    r ∉ sboxWrites ∧ r ≠ .a0 ∧ r ≠ .a2 ∧ r ≠ .a1 := by
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
    (h : j < 2 ^ 64) : isa.eval (.nonzero r) s = some (decide (j ≠ 0)) := by
  simp only [RISCV64.eval, hr, ofNat_ne_zero h]

theorem keyBody_ok {s₀ : State} {X b sc : Addr} {R : Nat} {w : List Byte}
    (hk : KSetup s₀ X b sc R w) {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) :
    WP isa (.block keyBody) s fun s' =>
      (j = 0 ∧ isa.eval (.nonzero .a1) s' = some false ∧ KDone s₀ b R w s') ∨
      (0 < j ∧ isa.eval (.nonzero .a1) s' = some true ∧ KInv s₀ b sc R w (j - 1) s') := by
  have hR := hk.rounds
  have hjR := hi.hj
  have hsb : s.gpr sb = b := by rw [hi.keep sb (by decide), hk.base]
  have hscr : Scr s X 2048 := hk.scr.congr hi.wr (by rw [hsb, hk.base])
  simp only [keyBody]
  repeat rw [WP.block_append_iff (M := isa)]
  -- Load the round key.
  refine WP.mono (keyLoad_ok (sc := sc) (off := 16 * j) (by rw [hi.rd, hi.wr]; exact hk.sch) hi.a0
    (by omega_arith)) fun s₁ ⟨hq₁, hrd₁, hwr₁, hsp₁, hm₁, hoth₁⟩ => ?_
  have hin : InRel (Q s₁) fun _ => rkv w j := by
    intro bb hb i hi16 t ht
    have hbyte := hi.sched hk hi16
    rw [getD_eq _ hi16, rkv, Vector.getElem_ofFn]
    simp only [Q]
    by_cases h8 : i < 8
    · rw [show bb + 4 * (i / 8) = bb by omega_arith, (hq₁ bb hb).1, show i % 8 = i by omega_arith,
        readW_bit _ _ h8 ht, wordAddr, hi.a0, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega_arith
    · rw [show bb + 4 * (i / 8) = bb + 4 by omega_arith, (hq₁ bb hb).2, readW_bit _ _ (by omega_arith) ht,
        wordAddr, hi.a0, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega_arith
  -- Bitslice it.
  have hsb₁ : s₁.gpr sb = b := by rw [hoth₁ sb (by decide), hsb]
  have hscr₁ : Scr s₁ X 2048 := hscr.congr hwr₁ (by rw [hsb₁, hsb])
  have hks₁ : MasksAt s₁.mem (s₁.gpr sb) bsKs := by
    rw [hm₁, hsb₁]
    exact masksAt_sub (masks_kept hi.frame hk.masks) fun p hp => by
      simp only [allKs, List.mem_append]; exact .inl (.inl hp)
  obtain ⟨s₂, hs₂, hq₂, hrd₂, hwr₂, hsp₂, hoth₂, hfr₂⟩ :=
    toBs_ok (hscr₁.okExts rfl rfl rfl (by decide) (by decide)) hks₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have hbs₂ := bs_of_in hq₂ hin
  have hm₂ : s₂.mem = s₁.mem := by
    funext x
    exact hfr₂ x fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      simp [slotRegion, bsCfg, Region.Contains] at hc
  -- Store it.
  have hr5₂ : s₂.gpr .a2 = keyAddr b R j := by
    rw [hoth₂ .a2 (by decide), hoth₁ .a2 (by decide), hi.a2]
  have hscr₂ : Scr s₂ X 2048 := hscr₁.congr hwr₂ (hoth₂ sb (by decide))
  obtain ⟨s₃, hs₃, hst₃, hrd₃, hwr₃, hsp₃, hg₃, hfr₃⟩ := keyStore_ok hscr₂
    (off := 1920 - 64 * (R - j)) (by rw [hr5₂, hoth₂ sb (by decide), hsb₁]) (by omega_arith)
    (by omega_arith)
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  -- Step back.
  obtain ⟨s₄, hs₄, hr3₄, hr5₄, hr4₄, hoth₄, hm₄, hrd₄, hwr₄, hsp₄⟩ := keyStep_ok s₃
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  -- What is kept.
  have hkeep : ∀ r, r ∉ keyWrites → s₄.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := keyWrites_not r hr
    rw [hoth₄ r h2 h3 h4, hg₃, hoth₂ r h1, hoth₁ r h1, hi.keep r hr]
  have hfr : Frame (kRegions b) s₀.mem s₄.mem := by
    rw [hm₄]
    refine hi.frame.trans ?_
    rw [← hm₁, ← hm₂]
    refine hfr₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hr5₂]
    exact Offset.sub b (by omega_arith) (by omega_arith)
  -- The keys stored before.
  have hold : ∀ i, j < i → i ≤ R →
      KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i) := by
    intro i hji hiR
    refine keyRel_congr (hi.done i hji hiR) fun k hk => ?_
    simp only [keyAddr, wordAddr_off]
    rw [hm₄, readW_off_frame hfr₃ fun r hr => ?_, hm₂, hm₁]
    simp only [List.mem_singleton] at hr; subst hr
    rw [hr5₂]
    exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  -- The key stored now.
  have hnew : KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R j) k) 64) (roundKey w j) :=
    keyRel_congr (keyRel_of_bs hbs₂) fun k hk => by rw [hm₄, ← hr5₂, hst₃ k hk]
  have hr4 : s₃.gpr .a1 = BitVec.ofNat 64 (j + 1) := by
    rw [hg₃, hoth₂ .a1 (by decide), hoth₁ .a1 (by decide), hi.a1]
  have hr3 : s₃.gpr .a0 = sc + BitVec.ofNat 64 (16 * j) := by
    rw [hg₃, hoth₂ .a0 (by decide), hoth₁ .a0 (by decide), hi.a0]
  have hr5 : s₃.gpr .a2 = keyAddr b R j := by rw [hg₃, hr5₂]
  have hrd : s₄.rd = s₀.rd := by rw [hrd₄, hrd₃, hrd₂, hrd₁, hi.rd]
  have hwr : s₄.wr = s₀.wr := by rw [hwr₄, hwr₃, hwr₂, hwr₁, hi.wr]
  have hsp : s₄.sp = s₀.sp := by rw [hsp₄, hsp₃, hsp₂, hsp₁, hi.sp]
  have hr4' : s₄.gpr .a1 = BitVec.ofNat 64 j := by rw [hr4₄, hr4, ofNat_succ_sub_one]
  have hev := eval_nonzero_ofNat hr4' (by omega_arith)
  by_cases h0 : j = 0
  · subst h0
    refine .inl ⟨rfl, by simpa using hev, ⟨by rw [hr5₄, hr5], hrd, hwr, hsp, hkeep, hfr,
      fun i hiR => ?_⟩⟩
    by_cases hi0 : i = 0
    · subst hi0; exact hnew
    · exact hold i (by omega_arith) hiR
  · refine .inr ⟨by omega_arith, by simpa [h0] using hev, ⟨by omega_arith, ?_, ?_, ?_, hrd, hwr, hsp,
      hkeep, hfr, ?_⟩⟩
    · rw [hr4', show j - 1 + 1 = j by omega_arith]
    · rw [hr3₄, hr3, show 16 * (j - 1) = 16 * j - 16 by omega_arith]
      exact add_ofNat_sub sc (y := 16) (by omega_arith)
    · rw [hr5₄, hr5]; exact keyAddr_pred b hk.rounds (by omega_arith) hi.hj
    · intro i hi' hiR
      by_cases hij : i = j
      · subst hij; exact hnew
      · exact hold i (by omega_arith) hiR

theorem keyLoop_ok {s₀ : State} {X b sc : Addr} {R : Nat} {w : List Byte}
    (hk : KSetup s₀ X b sc R w) {s : State} (hi : KInv s₀ b sc R w R s) :
    WP isa (.loop (.block keyBody) (.nonzero .a1)) s (KDone s₀ b R w) := by
  refine WP.loop (M := isa) (KInv s₀ b sc R w) (fun n s hs => ?_) R s hi
  refine WP.mono (keyBody_ok hk hs) fun s' h => ?_
  rcases h with ⟨_, hcf, hd⟩ | ⟨hn, hcf, hi'⟩
  · exact .inl ⟨hcf, hd⟩
  · exact .inr ⟨hcf, n - 1, by omega_arith, hi'⟩

end VG.Proof.Aes.RISCV64
