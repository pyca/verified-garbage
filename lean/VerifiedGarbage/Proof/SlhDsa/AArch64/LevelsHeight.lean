module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.LevelsGroup
public import VerifiedGarbage.Proof.SlhDsa.AArch64.LevelsScan
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.Lemmas

-- separate module: the heights, apart from the whole function (`LevelsMain`), to keep each build short.

/-!
# SLH-DSA on AArch64: `levels`, the heights

As on x86-64 (`Proof/SlhDsa/X86_64/LevelsLevel.lean`, `LevelsHeight.lean`):
the loop of the groups of a height (`level_ok`): the nodes of height `z + 1`
from those of height `z` (`step`), written over the first of them; a height
(`height_ok`): the scan, then the groups; and the loop of the heights.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Levels

open VG VG.AArch64 VG.AArch64.Steps VG.Proof.SlhDsa.AArch64.Blocks VG.Proof.SlhDsa.AArch64.Wots4
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64
open VG.Proof.SlhDsa.X86_64.Levels (step getD_step length_step upNodes_succ length_upNodes)

variable {p : Params} {σ : State} {S AU : Addr} {idx c h z₀ : Nat} {pkSeed a16 : List Byte}

/-- `H` for the SHAKE parameter sets: SHAKE256 of `PK.seed ‖ ADRS ‖ M`. -/
theorem H_shake (hf : p.family = .shake) (pk : List Byte) (a : Adrs) (M : List Byte) :
    H p pk a M = shake256 (pk ++ a ++ M) p.n := by
  simp only [H, hf, shakeAdrs]

/-- The condition of the groups' loop: `j + 4` below the nodes' number. -/
theorem eval_lt {s : State} {a b : Nat} (h : s.gpr .x9 = (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63)
    (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) : isa.eval (.nonzero .x .x9) s = some (decide (a < b)) := by
  show some ((s.gpr .x9).setWidth 64 != 0) = _
  rw [BitVec.setWidth_eq, h]
  have e : ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63).toNat = if a < b then 1 else 0 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega_using [ha]), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_using [hb]),
      Nat.shiftRight_eq_div_pow]
    split <;> rename_i hab <;> omega_using [hab, ha, hb]
  by_cases hab : a < b
  · rw [decide_eq_true hab]
    have : (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 ≠ 0 := fun h' => by
      have := congrArg BitVec.toNat h'; rw [e, ite_eq_left hab] at this; exact absurd this (by decide)
    simpa using this
  · rw [decide_eq_false hab]
    have : (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = 0 := BitVec.eq_of_toNat_eq (by rw [e, ite_eq_right hab]; rfl)
    simp [this]

/-- What a height's groups may change. -/
abbrev lvF (p : Params) (S : Addr) (c : Nat) : List Region :=
  (List.range 4).map (lR p S) ++ [⟨S, workUsed⟩, ⟨at' S Layout.oN, (c + 8) * p.n⟩]

/-- Before group `j` of height `z + 1`, from the state `t₀` at the level's start. -/
structure LvI (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (t₀ : State) (L : List (List Byte)) (z P j : Nat)
    (u : State) : Prop where
  base : Base hE u
  vk : VK u t₀
  keep : ∀ g ∈ [Reg.x21, .x22, .x23, .x25, .x26, .x27], u.gpr g = t₀.gpr g
  x24 : u.gpr .x24 = BitVec.ofNat 64 j
  new : ∀ i < j, i < P → bytesAt u.mem (at' S (Layout.oN + i * p.n)) p.n =
    (step p pkSeed a16 (tyA σ S) (kpA σ S) (baseA σ S) z L).getD i []
  old : ∀ i, 2 * j ≤ i → i < 2 * P → bytesAt u.mem (at' S (Layout.oN + i * p.n)) p.n = L.getD i []
  fr : Frame (lvF p S c) t₀.mem u.mem

theorem bytesAt_two (m : Mem) (S : Addr) (o n : Nat) :
    bytesAt m (at' S o) (2 * n) = bytesAt m (at' S o) n ++ bytesAt m (at' S (o + n)) n := by
  rw [Nat.two_mul, bytesAt_split]

/-- What a height's groups start from: the state `t₀` after the scan and the halving. -/
structure LvStart (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (t₀ : State) (L : List (List Byte)) (z P : Nat) :
    Prop where
  base : Base hE t₀
  x22 : t₀.gpr .x22 = BitVec.ofNat 64 z
  z14 : z < 14
  x27 : t₀.gpr .x27 = BitVec.ofNat 64 (baseA σ S / 2 ^ (z + 1))
  x24 : t₀.gpr .x24 = BitVec.ofNat 64 0
  x23 : t₀.gpr .x23 = BitVec.ofNat 64 P
  P1 : 1 ≤ P
  Pc : 2 * P ≤ c
  len : L.length = 2 * P
  nodes : ∀ i < 2 * P, bytesAt t₀.mem (at' S (Layout.oN + i * p.n)) p.n = L.getD i []

theorem LvStart.lvi0 {hE : Entry p σ S AU idx c h z₀ pkSeed a16} {t₀ : State} {L : List (List Byte)} {z P : Nat}
    (hs : LvStart hE t₀ L z P) : LvI hE t₀ L z P 0 t₀ :=
  ⟨hs.base, VK.refl _, fun _ _ => rfl, by rw [hs.x24],
    fun i hi => absurd hi (by omega_using []), fun i _ hi => hs.nodes i hi, Frame.refl _ _⟩

/-- A group of height `z + 1`. -/
theorem levelStep_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {z P : Nat} {L : List (List Byte)} {t₀ : State} (hs : LvStart hE t₀ L z P) {g : Nat} (hjP : 4 * g < P) {u : State}
    (hI : LvI hE t₀ L z P (4 * g) u) :
    WP isa (Tree.levelBody ⟨p.n, p.len⟩ name T.code) u fun u' => LvI hE t₀ L z P (4 * (g + 1)) u' ∧
      u'.gpr .x9 = (BitVec.ofNat 64 (4 * g + 4) - BitVec.ofNat 64 P) >>> 63 := by
  have hn := hz.n32
  have h16 := a16_length hE.env
  have hc13 := hE.c_le hz
  have hbase : baseA σ S < 2 ^ 32 := hE.v1
  have hB : baseA σ S / 2 ^ (z + 1) ≤ baseA σ S / 2 := by
    rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]; exact Nat.div_le_self _ _
  have h22 := hs.x22
  have h27 := hs.x27
  have h23 := hs.x23
  have hz14 := hs.z14
  have hPc := hs.Pc
  have hlen := hs.len
  have hu22 : u.gpr .x22 = BitVec.ofNat 64 z := by rw [hI.keep _ (by decide), h22]
  have hu27 : u.gpr .x27 = BitVec.ofNat 64 (baseA σ S / 2 ^ (z + 1)) := by rw [hI.keep _ (by decide), h27]
  have hu23 : u.gpr .x23 = BitVec.ofNat 64 P := by rw [hI.keep _ (by decide), h23]
  refine WP.mono (group_ok hE hz T name (j := 4 * g) hI.base hu22 hz14 hu27 hI.x24 hu23
    (by omega_using [hB, hbase, hjP, hc13, hPc]) (by omega_using [hjP, hPc])) fun u' ⟨hb', gp⟩ => ?_
  -- the group's frame, as the nodes' places it leaves
  have hfit : ∀ i, i + 1 ≤ c + 8 → Layout.oN + i * p.n + p.n ≤ 29120 := fun i hi => node_fit hE hi
  have keepN : ∀ i, i < 2 * P → (i < 4 * g ∨ 4 * g + 4 ≤ i) →
      bytesAt u'.mem (at' S (Layout.oN + i * p.n)) p.n = bytesAt u.mem (at' S (Layout.oN + i * p.n)) p.n := by
    intro i hi hii
    have hf₁ := hfit i (by omega_using [hi, hPc])
    refine bytesAt_frame gp.frame (fun r hr => ?_) (by omega_using [hn])
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (⟨k, hk, rfl⟩ | rfl) | ⟨k, hk, rfl⟩
    · exact Entry.dscr (Or.inr (by rw [laneA_eq, oN_eq]; omega_using [hk, hn])) (by omega_using [hf₁])
        (by rw [laneA_eq]; omega_using [hk, hn])
    · exact (Offset.disjoint_base S (by rw [oN_eq]; simp only [workUsed]; omega_using []) (by omega_using [hf₁]))
    · dsimp only [oR]; rw [oR_off]
      have hf₂ := hfit (4 * g + k) (by omega_using [hk, hjP, hPc])
      rcases hii with hii | hii
      · refine Entry.dscr (Or.inl ?_) (by omega_using [hf₁]) (by omega_using [hf₂])
        have := Nat.mul_le_mul_right p.n (show i + 1 ≤ 4 * g + k by omega_using [hii])
        rw [Nat.succ_mul] at this; omega_using [this]
      · refine Entry.dscr (Or.inr ?_) (by omega_using [hf₁]) (by omega_using [hf₂])
        have := Nat.mul_le_mul_right p.n (show 4 * g + k + 1 ≤ i by omega_using [hii, hk])
        rw [Nat.succ_mul] at this; omega_using [this]
  have hI' : LvI hE t₀ L z P (4 * (g + 1)) u' := by
    refine ⟨hb', VK.trans gp.vk hI.vk, fun r hr => by rw [gp.keep r hr, hI.keep r hr], by rw [gp.x24]; rfl,
      fun i hi hiP => ?_, fun i hi hiP => ?_, ?_⟩
    · by_cases hlo : i < 4 * g
      · rw [keepN i (by omega_using [hiP]) (Or.inl hlo), hI.new i hlo hiP]
      · have hk : i - 4 * g < 4 := by omega_using [hi, hlo]
        have e := gp.nodes (i - 4 * g) hk
        rw [show 4 * g + (i - 4 * g) = i by omega_using [hlo]] at e
        rw [e, getD_step _ _ _ _ _ _ _ _ (by rw [hlen]; omega_using [hiP]), H_shake hz.shake,
          nodeAdrs_fld h16, show baseA σ S / 2 ^ (z + 1) + 4 * g + (i - 4 * g) = baseA σ S / 2 ^ (z + 1) + i by
            omega_using [hlo]]
        congr 2
        rw [show Layout.oN + 2 * (4 * g) * p.n + 2 * p.n * (i - 4 * g) = Layout.oN + 2 * i * p.n by
            rw [show 2 * i = 2 * (4 * g) + 2 * (i - 4 * g) by omega_using [hlo], Nat.add_mul,
              Nat.mul_comm 2 (i - 4 * g), Nat.mul_assoc (i - 4 * g), Nat.mul_comm (i - 4 * g)]; omega_using [],
          bytesAt_two, hI.old (2 * i) (by omega_using [hlo]) (by omega_using [hiP]),
          show Layout.oN + 2 * i * p.n + p.n = Layout.oN + (2 * i + 1) * p.n by
            rw [Nat.add_mul (2 * i) 1 p.n, Nat.one_mul]; omega_using [],
          hI.old (2 * i + 1) (by omega_using [hlo]) (by omega_using [hiP])]
    · rw [keepN i hiP (Or.inr (by omega_using [hi])), hI.old i (by omega_using [hi]) hiP]
    · refine hI.fr.trans (gp.frame.sub fun r hr => ?_)
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (⟨k, hk, rfl⟩ | rfl) | ⟨k, hk, rfl⟩
      · exact ⟨_, by simp only [lvF, List.mem_append, List.mem_map, List.mem_range]; exact Or.inl ⟨k, hk, rfl⟩,
          fun _ h => h⟩
      · exact ⟨_, by simp [lvF], fun _ h => h⟩
      · refine ⟨⟨at' S Layout.oN, (c + 8) * p.n⟩, by simp [lvF], ?_⟩
        dsimp only [oR]; rw [oR_off]
        refine Offset.sub S (by omega_using []) ?_
        have := Nat.mul_le_mul_right p.n (show 4 * g + k + 1 ≤ c + 8 by omega_using [hk, hjP, hPc])
        rw [Nat.succ_mul] at this; omega_using [this]
  exact ⟨hI', gp.x9⟩

/-- The groups of height `z + 1`, from the `2P` nodes `L` of height `z`. -/
theorem level_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {z P : Nat} {L : List (List Byte)} {t₀ : State} (hs : LvStart hE t₀ L z P) :
    WP isa (.loop (Tree.levelBody ⟨p.n, p.len⟩ name T.code) (.nonzero .x .x9)) t₀ fun t' =>
      ∃ j, P ≤ j ∧ LvI hE t₀ L z P j t' := by
  have hc13 := hE.c_le hz
  have hPc := hs.Pc
  let G := (P + 3) / 4
  refine WP.loop (M := isa) (Inv := fun m u => ∃ g, m = G - g ∧ g < G ∧ LvI hE t₀ L z P (4 * g) u)
    (fun m u hI => ?_) G t₀ ⟨0, by omega_using [], by have := hs.P1; omega_using [this], hs.lvi0⟩
  obtain ⟨g, rfl, hg, hI⟩ := hI
  have hjP : 4 * g < P := by omega_using [hg]
  refine WP.mono (levelStep_ok hE hz T name hs hjP hI) fun u' ⟨hI', h9⟩ => ?_
  have ev := eval_lt h9 (by omega_using [hjP, hc13, hPc]) (by omega_using [hjP, hc13, hPc])
  by_cases hc' : 4 * g + 4 < P
  · exact Or.inr ⟨by rw [ev, decide_eq_true hc'], G - (g + 1), by omega_using [hg, hc'], g + 1, rfl,
      by omega_using [hc'], hI'⟩
  · exact Or.inl ⟨by rw [ev, decide_eq_false hc'], 4 * (g + 1), by omega_using [hc'], hI'⟩

/-! ## A height -/

theorem wp_seq_seq {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a b) s fun t => WP isa c t Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h' => WP.seq h')

theorem kv_scan (L : Layout) :
    ((.seq (.block Tree.scanInit) (.loop (.block (Tree.scanBody L)) (.nonzero .x .x9)) : Prog isa)).allInstrs keepsV = true := by
  rw [Code.allInstrs_eq]
  simp only [instrs, List.all_append, scanBody_eq, kv_flatMap _ fun w => (rfl : (xorWord w).all keepsV = true)]
  rfl

/-- The nodes at the entry state, and those of height `z₀ + r` above them. -/
abbrev L0 (p : Params) (σ : State) (S : Addr) (c : Nat) : List (List Byte) := nodesAt p σ.mem (at' S Layout.oN) c
abbrev up (p : Params) (σ : State) (S : Addr) (c z₀ : Nat) (pkSeed a16 : List Byte) (r : Nat) : List (List Byte) :=
  upNodes p pkSeed a16 (tyA σ S) (kpA σ S) (baseA σ S) z₀ (L0 p σ S c) r

/-- The authentication path's node `r` at the entry state. -/
abbrev oldA (p : Params) (σ : State) (AU : Addr) (r : Nat) : List Byte := bytesAt σ.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n

/-- Before height `z₀ + r`. -/
structure HI (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (r : Nat) (u : State) : Prop where
  base : Base hE u
  vk : VK u σ
  x21 : u.gpr .x21 = AU + BitVec.ofNat 64 (r * p.n)
  x22 : u.gpr .x22 = BitVec.ofNat 64 (z₀ + r)
  x23 : u.gpr .x23 = BitVec.ofNat 64 (2 ^ (h - r))
  x25 : u.gpr .x25 = BitVec.ofNat 64 (idx / 2 ^ (z₀ + r))
  x26 : u.gpr .x26 = BitVec.ofNat 64 (capB σ S / 2 ^ (z₀ + r))
  x27 : u.gpr .x27 = BitVec.ofNat 64 (baseA σ S / 2 ^ (z₀ + r + 1))
  nodes : ∀ i < 2 ^ (h - r), bytesAt u.mem (at' S (Layout.oN + i * p.n)) p.n = (up p σ S c z₀ pkSeed a16 r).getD i []
  auth : ∀ r' < h, bytesAt u.mem (AU + BitVec.ofNat 64 (r' * p.n)) p.n =
    if r' < r then xorB (oldA p σ AU r') (pick p.n (up p σ S c z₀ pkSeed a16 r') (capB σ S / 2 ^ (z₀ + r')) idx (z₀ + r'))
    else oldA p σ AU r'

theorem length_L0 : (L0 p σ S c).length = c := by simp [L0, nodesAt]

theorem length_up (hE : Entry p σ S AU idx c h z₀ pkSeed a16) {r : Nat} (hr : r ≤ h) :
    (up p σ S c z₀ pkSeed a16 r).length = 2 ^ (h - r) := by
  rw [up, length_upNodes, length_L0, hE.cnt, Nat.pow_div hr (by decide)]

theorem pow_half {h r : Nat} (hr : r < h) : 2 ^ (h - r) / 2 = 2 ^ (h - (r + 1)) := by
  rw [show h - r = h - (r + 1) + 1 by omega_using [hr], Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]

theorem pow_lt {h r : Nat} (hh : h ≤ 14) : 2 ^ (h - r) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) (by omega_using [hh])

theorem path_disj (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {r : Nat} (hr : r < h) :
    ∀ R ∈ lvF p S c, Region.Disjoint ⟨AU + BitVec.ofNat 64 (r * p.n), p.n⟩ R := by
  have hn := hz.n32
  have hfit := hE.nodes_fit
  have hl : r * p.n + p.n ≤ h * p.n := by
    have := Nat.mul_le_mul_right p.n (show r + 1 ≤ h by omega_using [hr]); rwa [Nat.succ_mul] at this
  intro R hR
  simp only [lvF, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with ⟨k, hk, rfl⟩ | rfl | rfl
  · exact hE.dAU hl (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn])
  · exact (hE.reg.out_scr.sub_left (Offset.sub_base AU hl)).sub_right (Region.sub_prefix (by rw [oSigTmp_eq]; decide))
  · exact hE.dAU hl (by rw [oSigTmp_eq]; omega_using [hfit])

/-- Two nodes of the path. -/
theorem path_two (hE : Entry p σ S AU idx c h z₀ pkSeed a16) {r r' : Nat} (hr : r < h) (hr' : r' < h) (hne : r ≠ r') :
    Region.Disjoint ⟨AU + BitVec.ofNat 64 (r * p.n), p.n⟩ ⟨AU + BitVec.ofNat 64 (r' * p.n), p.n⟩ := by
  have hfit := hE.reg.out_fit; simp only at hfit
  have hl : ∀ {x}, x < h → x * p.n + p.n ≤ h * p.n := fun {x} hx => by
    have := Nat.mul_le_mul_right p.n (show x + 1 ≤ h by omega_using [hx]); rwa [Nat.succ_mul] at this
  have hc : r * p.n + p.n ≤ r' * p.n ∨ r' * p.n + p.n ≤ r * p.n := by
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · left; have := Nat.mul_le_mul_right p.n (show r + 1 ≤ r' by omega_using [h']); rwa [Nat.succ_mul] at this
    · right; have := Nat.mul_le_mul_right p.n (show r' + 1 ≤ r by omega_using [h']); rwa [Nat.succ_mul] at this
  exact Offset.disjoint AU hc (by omega_using [hl hr, hfit]) (by omega_using [hl hr', hfit])

theorem kv_halve : Tree.halve.all keepsV = true := rfl
theorem kv_next (L : Layout) : (Tree.nextHeight L).all keepsV = true := rfl

/-- After the scan of height `z₀ + r`, from `u`. -/
def ScanQ0 (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (r : Nat) (u t₁ : State) : Prop :=
  Base hE t₁ ∧ (∀ g ∉ SR, g ≠ .x13 → t₁.gpr g = u.gpr g) ∧
    bytesAt t₁.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n = xorB (bytesAt u.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n)
      (pick p.n (up p σ S c z₀ pkSeed a16 r) (capB σ S / 2 ^ (z₀ + r)) idx (z₀ + r)) ∧
    Frame [⟨AU + BitVec.ofNat 64 (r * p.n), p.n⟩] u.mem t₁.mem

/-- The scan of height `z₀ + r`. -/
theorem scan_part (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {r : Nat} (hr : r < h) {u : State}
    (hI : HI hE r u) :
    WP isa (.seq (.block Tree.scanInit) (.loop (.block (Tree.scanBody ⟨p.n, p.len⟩)) (.nonzero .x .x9))) u
      fun t₁ => ScanQ0 hE r u t₁ ∧ VK t₁ u := by
  have hn := hz.n32
  have hh := hE.h_le
  have hc13 := hE.c_le hz
  have hcnt := hE.cnt
  have hidx := hE.idx32
  have hcap : capB σ S < 2 ^ 32 := hE.v0
  have hbase : baseA σ S < 2 ^ 32 := hE.v1
  have hpow : 2 ^ (h - r) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega_using [])
  have hl : r * p.n + p.n ≤ h * p.n := by
    have := Nat.mul_le_mul_right p.n (show r + 1 ≤ h by omega_using [hr]); rwa [Nat.succ_mul] at this
  let c' := 2 ^ (h - r)
  have hnd : ∀ i < c', at' S Layout.oN + BitVec.ofNat 64 (i * p.n) = at' S (Layout.oN + i * p.n) := fun _ _ => ofNat_add' _ _ _
  have hfitn : ∀ i < c', Layout.oN + i * p.n + p.n ≤ 29120 := fun i hi => node_fit hE (by omega_using [hi, hpow, hcnt])
  exact WP.preservedV (scan_ok hz (ND := at' S Layout.oN) (AP := AU + BitVec.ofNat 64 (r * p.n))
    (c := c') (I := idx / 2 ^ (z₀ + r)) (A := capB σ S / 2 ^ (z₀ + r)) hI.base.x20 hI.x21 hI.x23 hI.x25 hI.x26
    (Nat.one_le_two_pow) (by omega_using [hpow, hcnt, hc13]) (by have := Nat.div_le_self idx (2 ^ (z₀ + r)); omega_using [this, hidx])
    (by have := Nat.div_le_self (capB σ S) (2 ^ (z₀ + r)); omega_using [this, hcap])
    (fun i hi => by rw [hnd i hi]; exact hE.inScr' hI.base.wr (by omega_using [hfitn i hi]))
    (hE.inAU hI.base.wr hl (by have := hz.n16; omega_using [this]))
    (fun i hi => by rw [hnd i hi]; exact hE.dAU hl (by rw [oSigTmp_eq]; omega_using [hfitn i hi]))
    (Q := fun t₁ => ScanQ0 hE r u t₁)
    fun t₁ hg₁ sp₁ rd₁ wr₁ by₁ f₁ => ⟨hI.base.ofFrame rd₁ wr₁ sp₁
        (fun g hg => hg₁ g (by rcases lr_mem hg with rfl | rfl | rfl <;> decide) (by rcases lr_mem hg with rfl | rfl | rfl <;> decide))
        f₁ (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact ⟨⟨AU, h * p.n⟩, by simp [lch], Offset.sub_base AU hl⟩)
        (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact (hE.dAU hl (by rw [oSigTmp_eq]; decide)).symm),
      hg₁, scan_pick (length_up hE (by omega_using [hr])) (fun i hi => by rw [hnd i hi]; exact hI.nodes i hi) by₁, f₁⟩)
    (kv_scan _)

/-- The halving after the scan: what the groups start from. -/
theorem halve_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {r : Nat} (hr : r < h) {u t₁ : State}
    (hI : HI hE r u) (hq : ScanQ0 hE r u t₁) :
    WP isa (.block Tree.halve) t₁ fun t₃ => LvStart hE t₃ (up p σ S c z₀ pkSeed a16 r) (z₀ + r) (2 ^ (h - (r + 1))) := by
  have hn := hz.n32
  have hh := hE.h_le
  have hc13 := hE.c_le hz
  have hcnt := hE.cnt
  have hidx := hE.idx32
  have hcap : capB σ S < 2 ^ 32 := hE.v0
  have hbase : baseA σ S < 2 ^ 32 := hE.v1
  have hpow : 2 ^ (h - r) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega_using [])
  have hl : r * p.n + p.n ≤ h * p.n := by
    have := Nat.mul_le_mul_right p.n (show r + 1 ≤ h by omega_using [hr]); rwa [Nat.succ_mul] at this
  let c' := 2 ^ (h - r)
  have hnd : ∀ i < c', at' S Layout.oN + BitVec.ofNat 64 (i * p.n) = at' S (Layout.oN + i * p.n) := fun _ _ => ofNat_add' _ _ _
  have hfitn : ∀ i < c', Layout.oN + i * p.n + p.n ≤ 29120 := fun i hi => node_fit hE (by omega_using [hi, hpow, hcnt])
  obtain ⟨hb₁, hg₁, hp₁, hf₁⟩ := hq
  let P := 2 ^ (h - (r + 1))
  have hPc : 2 * P = c' := by
    show 2 * 2 ^ (h - (r + 1)) = 2 ^ (h - r)
    rw [show h - r = h - (r + 1) + 1 by omega_using [hr], Nat.pow_succ, Nat.mul_comm]
  refine wp_vk kv_halve (wp_lsr (by decide) fun t₂ u₂ => wp_movz fun t₃ u₃ => WP.block_nil fun hv₃ => ?_)
  have hb₃ : Base hE t₃ := hb₁.regs (by rw [u₃.mem, u₂.mem]) (by rw [u₃.rd, u₂.rd]) (by rw [u₃.wr, u₂.wr])
    (by rw [u₃.sp, u₂.sp]) fun g hg => by
      rcases lr_mem hg with rfl | rfl | rfl <;> rw [u₃.other _ (by decide), u₂.other _ (by decide)]
  have k₃ : ∀ g ∉ SR, g ≠ .x13 → g ≠ .x23 → t₃.gpr g = u.gpr g := fun g h₁ h₂ h₃ => by
    rw [u₃.other _ (nt' h₁ .x24), u₂.other _ h₃, hg₁ g h₁ h₂]
  have h23 : t₃.gpr .x23 = BitVec.ofNat 64 P := by
    rw [u₃.other _ (by decide), u₂.gpr, hg₁ _ (by decide) (by decide), hI.x23,
      shr1 (by have := pow_lt (h := h) (r := r) (by omega_using [hh]); omega_using [this]), pow_half hr]
  have hm₃ : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
  have hnodes₁ : ∀ i < c', bytesAt t₁.mem (at' S (Layout.oN + i * p.n)) p.n = (up p σ S c z₀ pkSeed a16 r).getD i [] :=
    fun i hi => by
      rw [bytesAt_frame hf₁ (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact (hE.dAU hl (by rw [oSigTmp_eq]; omega_using [hfitn i hi])).symm) (by omega_using [hn]),
        hI.nodes i hi]
  exact ⟨hb₃,
    by rw [k₃ _ (by decide) (by decide) (by decide), hI.x22], by omega_using [hr, hh],
    by rw [k₃ _ (by decide) (by decide) (by decide), hI.x27], by rw [u₃.gpr]; rfl, h23, Nat.one_le_two_pow,
    by rw [hPc]; omega_using [hpow, hcnt], by rw [hPc]; exact length_up hE (by omega_using [hr]),
    fun i hi => by rw [hm₃]; exact hnodes₁ i (by omega_using [hi, hPc])⟩

/-- Height `z₀ + r`: the scan, then the nodes of the height above. -/
theorem height_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {r : Nat} (hr : r < h) {u : State} (hI : HI hE r u) :
    WP isa (Tree.heightBody ⟨p.n, p.len⟩ name T.code) u fun u' => HI hE (r + 1) u' ∧
      u'.gpr .x9 = BitVec.ofNat 64 (2 ^ (h - (r + 1))) - BitVec.ofNat 64 1 := by
  have hn := hz.n32
  have hh := hE.h_le
  have hc13 := hE.c_le hz
  have hcnt := hE.cnt
  have hidx := hE.idx32
  have hcap : capB σ S < 2 ^ 32 := hE.v0
  have hbase : baseA σ S < 2 ^ 32 := hE.v1
  have hpow : 2 ^ (h - r) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega_using [])
  have hl : r * p.n + p.n ≤ h * p.n := by
    have := Nat.mul_le_mul_right p.n (show r + 1 ≤ h by omega_using [hr]); rwa [Nat.succ_mul] at this
  let c' := 2 ^ (h - r)
  have hnd : ∀ i < c', at' S Layout.oN + BitVec.ofNat 64 (i * p.n) = at' S (Layout.oN + i * p.n) := fun _ _ => ofNat_add' _ _ _
  have hfitn : ∀ i < c', Layout.oN + i * p.n + p.n ≤ 29120 := fun i hi => node_fit hE (by omega_using [hi, hpow, hcnt])
  unfold Tree.heightBody
  refine wp_seq_seq (WP.mono (WP.preservedV (scan_ok hz (ND := at' S Layout.oN) (AP := AU + BitVec.ofNat 64 (r * p.n))
    (c := c') (I := idx / 2 ^ (z₀ + r)) (A := capB σ S / 2 ^ (z₀ + r)) hI.base.x20 hI.x21 hI.x23 hI.x25 hI.x26
    (Nat.one_le_two_pow) (by omega_using [hpow, hcnt, hc13]) (by have := Nat.div_le_self idx (2 ^ (z₀ + r)); omega_using [this, hidx])
    (by have := Nat.div_le_self (capB σ S) (2 ^ (z₀ + r)); omega_using [this, hcap])
    (fun i hi => by rw [hnd i hi]; exact hE.inScr' hI.base.wr (by omega_using [hfitn i hi]))
    (hE.inAU hI.base.wr hl (by have := hz.n16; omega_using [this]))
    (fun i hi => by rw [hnd i hi]; exact hE.dAU hl (by rw [oSigTmp_eq]; omega_using [hfitn i hi]))
    (Q := fun t₁ => Base hE t₁ ∧ (∀ g ∉ SR, g ≠ .x13 → t₁.gpr g = u.gpr g) ∧
      bytesAt t₁.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n = xorB (bytesAt u.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n)
        (pick p.n (up p σ S c z₀ pkSeed a16 r) (capB σ S / 2 ^ (z₀ + r)) idx (z₀ + r)) ∧
      Frame [⟨AU + BitVec.ofNat 64 (r * p.n), p.n⟩] u.mem t₁.mem)
    fun t₁ hg₁ sp₁ rd₁ wr₁ by₁ f₁ => ⟨hI.base.ofFrame rd₁ wr₁ sp₁
        (fun g hg => hg₁ g (by rcases lr_mem hg with rfl | rfl | rfl <;> decide) (by rcases lr_mem hg with rfl | rfl | rfl <;> decide))
        f₁ (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact ⟨⟨AU, h * p.n⟩, by simp [lch], Offset.sub_base AU hl⟩)
        (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact (hE.dAU hl (by rw [oSigTmp_eq]; decide)).symm),
      hg₁, scan_pick (length_up hE (by omega_using [hr])) (fun i hi => by rw [hnd i hi]; exact hI.nodes i hi) by₁, f₁⟩)
    (kv_scan _)) fun t₁ ⟨⟨hb₁, hg₁, hp₁, hf₁⟩, hv₁⟩ => ?_)
  let P := 2 ^ (h - (r + 1))
  have hPc : 2 * P = c' := by
    show 2 * 2 ^ (h - (r + 1)) = 2 ^ (h - r)
    rw [show h - r = h - (r + 1) + 1 by omega_using [hr], Nat.pow_succ, Nat.mul_comm]
  refine WP.seq (wp_vk kv_halve (wp_lsr (by decide) fun t₂ u₂ => wp_movz fun t₃ u₃ => WP.block_nil fun hv₃ => ?_))
  have hb₃ : Base hE t₃ := hb₁.regs (by rw [u₃.mem, u₂.mem]) (by rw [u₃.rd, u₂.rd]) (by rw [u₃.wr, u₂.wr])
    (by rw [u₃.sp, u₂.sp]) fun g hg => by
      rcases lr_mem hg with rfl | rfl | rfl <;> rw [u₃.other _ (by decide), u₂.other _ (by decide)]
  have k₃ : ∀ g ∉ SR, g ≠ .x13 → g ≠ .x23 → t₃.gpr g = u.gpr g := fun g h₁ h₂ h₃ => by
    rw [u₃.other _ (nt' h₁ .x24), u₂.other _ h₃, hg₁ g h₁ h₂]
  have h23 : t₃.gpr .x23 = BitVec.ofNat 64 P := by
    rw [u₃.other _ (by decide), u₂.gpr, hg₁ _ (by decide) (by decide), hI.x23,
      shr1 (by have := pow_lt (h := h) (r := r) (by omega_using [hh]); omega_using [this]), pow_half hr]
  have hm₃ : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
  have hnodes₁ : ∀ i < c', bytesAt t₁.mem (at' S (Layout.oN + i * p.n)) p.n = (up p σ S c z₀ pkSeed a16 r).getD i [] :=
    fun i hi => by
      rw [bytesAt_frame hf₁ (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact (hE.dAU hl (by rw [oSigTmp_eq]; omega_using [hfitn i hi])).symm) (by omega_using [hn]),
        hI.nodes i hi]
  refine WP.seq (WP.mono (level_ok hE hz T name (z := z₀ + r) (P := P) (L := up p σ S c z₀ pkSeed a16 r) ⟨hb₃,
    by rw [k₃ _ (by decide) (by decide) (by decide), hI.x22], by omega_using [hr, hh],
    by rw [k₃ _ (by decide) (by decide) (by decide), hI.x27], by rw [u₃.gpr]; rfl, h23, Nat.one_le_two_pow,
    by rw [hPc]; omega_using [hpow, hcnt], by rw [hPc]; exact length_up hE (by omega_using [hr]),
    fun i hi => by rw [hm₃]; exact hnodes₁ i (by omega_using [hi, hPc])⟩) fun t₄ ⟨j, hj, hLv⟩ => ?_)
  refine wp_vk (kv_next _) ?_
  simp only [Tree.nextHeight]
  refine wp_addImm (by omega_using [hn]) fun v₁ w₁ => wp_addImm (by decide) fun v₂ w₂ => wp_lsr (by decide) fun v₃ w₃ =>
    wp_lsr (by decide) fun v₄ w₄ => wp_lsr (by decide) fun v₅ w₅ => wp_subImm (by decide) fun v₆ w₆ =>
      WP.block_nil fun hv₆ => ?_
  have k₄ : ∀ g ∈ [Reg.x21, .x22, .x23, .x25, .x26, .x27], t₄.gpr g = t₃.gpr g := hLv.keep
  have hm : v₆.mem = t₄.mem := by rw [w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]
  have hb₆ : Base hE v₆ := hLv.base.regs hm (by rw [w₆.rd, w₅.rd, w₄.rd, w₃.rd, w₂.rd, w₁.rd])
    (by rw [w₆.wr, w₅.wr, w₄.wr, w₃.wr, w₂.wr, w₁.wr]) (by rw [w₆.sp, w₅.sp, w₄.sp, w₃.sp, w₂.sp, w₁.sp]) fun g hg => by
      rcases lr_mem hg with rfl | rfl | rfl <;>
        rw [w₆.other _ (by decide), w₅.other _ (by decide), w₄.other _ (by decide), w₃.other _ (by decide),
          w₂.other _ (by decide), w₁.other _ (by decide)]
  have hshr : ∀ {x m : Nat}, x < 2 ^ 32 → BitVec.ofNat 64 (x / 2 ^ m) >>> 1 = BitVec.ofNat 64 (x / 2 ^ (m + 1)) :=
    fun {x m} hx => by
      rw [shr1 (by have := Nat.div_le_self x (2 ^ m); omega_using [this, hx]), div_pow_succ]
  refine ⟨⟨hb₆, VK.trans hv₆ (VK.trans hLv.vk (VK.trans hv₃ (VK.trans hv₁ hI.vk))), ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => ?_, fun r' hr' => ?_⟩, ?_⟩
  · rw [w₆.other _ (by decide), w₅.other _ (by decide), w₄.other _ (by decide), w₃.other _ (by decide),
      w₂.other _ (by decide), w₁.gpr, k₄ _ (by decide), k₃ _ (by decide) (by decide) (by decide), hI.x21, ofNat_add',
      Nat.succ_mul]
  · rw [w₆.other _ (by decide), w₅.other _ (by decide), w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr,
      w₁.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide) (by decide) (by decide), hI.x22, ← BitVec.ofNat_add,
      Nat.add_assoc]
  · rw [w₆.other _ (by decide), w₅.other _ (by decide), w₄.other _ (by decide), w₃.other _ (by decide),
      w₂.other _ (by decide), w₁.other _ (by decide), k₄ _ (by decide), h23]
  · rw [w₆.other _ (by decide), w₅.other _ (by decide), w₄.other _ (by decide), w₃.gpr, w₂.other _ (by decide),
      w₁.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide) (by decide) (by decide), hI.x25, hshr hidx,
      Nat.add_assoc]
  · rw [w₆.other _ (by decide), w₅.other _ (by decide), w₄.gpr, w₃.other _ (by decide), w₂.other _ (by decide),
      w₁.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide) (by decide) (by decide), hI.x26, hshr hcap,
      Nat.add_assoc]
  · rw [w₆.other _ (by decide), w₅.gpr, w₄.other _ (by decide), w₃.other _ (by decide), w₂.other _ (by decide),
      w₁.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide) (by decide) (by decide), hI.x27, hshr hbase]; rfl
  · rw [hm, hLv.new i (by omega_using [hi, hj]) hi, up, up, upNodes_succ]
  · rw [hm, bytesAt_frame hLv.fr (path_disj hE hz hr') (by omega_using [hn]), hm₃]
    by_cases e : r' = r
    · subst e
      rw [hp₁, hI.auth r' hr', ite_eq_right (Nat.lt_irrefl _), ite_eq_left (Nat.lt_succ_self _)]
    · rw [bytesAt_frame hf₁ (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact path_two hE hr' hr e) (by omega_using [hn]),
        hI.auth r' hr']
      by_cases hlt : r' < r
      · rw [ite_eq_left hlt, ite_eq_left (by omega_using [hlt])]
      · rw [ite_eq_right hlt, ite_eq_right (by omega_using [hlt, e])]
  · rw [w₆.gpr, w₅.other _ (by decide), w₄.other _ (by decide), w₃.other _ (by decide), w₂.other _ (by decide),
      w₁.other _ (by decide), k₄ _ (by decide), h23]

end VG.Proof.SlhDsa.AArch64.Levels
