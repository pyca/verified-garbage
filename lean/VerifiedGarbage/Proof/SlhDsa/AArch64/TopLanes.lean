module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# SLH-DSA (SHAKE) on AArch64: the lanes' `PK.seed` and addresses

The blocks the functions the Rust code calls share, in `scratch` (`x19`):
`seedLanes_ok` (`PK.seed` to every lane) and `treeLanes_ok` (every lane's
layer and tree addresses).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_x wp_movz wp_strx wp_strw)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64

/-! ## Blocks of the functions the Rust code calls -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- The blocks of a `flatMap` over `range K` followed by `is`, one at a time. -/
theorem wp_rangeFlatMap {f : Nat → List Instr} {P : Nat → State → Prop} :
    ∀ (K : Nat) {s : State} {is : List Instr}, P 0 s →
      (∀ j < K, ∀ t (is' : List Instr), P j t → (∀ t', P (j + 1) t' → WP isa (.block is') t' Q) →
        WP isa (.block (f j ++ is')) t Q) →
      (∀ t, P K t → WP isa (.block is) t Q) →
      WP isa (.block ((List.range K).flatMap f ++ is)) s Q
  | 0, _, _, h0, _, k => by simpa using k _ h0
  | K + 1, _, is, h0, hs, k => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    exact wp_rangeFlatMap K h0 (fun j hj => hs j (by omega_using [hj])) fun t ht => hs K (by omega_using []) t is ht k

theorem laneA_eq (k : Nat) : Layout.laneA k = 3136 + 128 * k := rfl
theorem laneB_eq (k : Nat) : Layout.laneB k = 3648 + 2208 * k := rfl
theorem oPkSeed_eq : Layout.oPkSeed = 1728 := rfl

/-- A range of `scratch`. -/
theorem scr_in {wr : List Region} {S : Addr} (hw : (⟨S, scratchLen⟩ : Region) ∈ wr) {o n : Nat}
    (h : o + n ≤ 65536) : InRegions wr (at' S o) n :=
  ⟨_, hw, Offset.contains_base S (by simpa [scratchLen] using h) (by omega_using [h])⟩

theorem scr_in' {rd wr : List Region} {S : Addr} (hw : (⟨S, scratchLen⟩ : Region) ∈ wr) {o n : Nat}
    (h : o + n ≤ 65536) : InRegions (rd ++ wr) (at' S o) n := InRegions.rdwr (scr_in hw h)

/-- The lanes' `PK.seed`. -/
def seedRegions (n : Nat) (S : Addr) : List Region :=
  (List.range 4).flatMap fun j => [⟨at' S (Layout.laneA j), n⟩, ⟨at' S (Layout.laneB j), n⟩]

/-- After the copies of `PK.seed` to the lanes `j` below `c`. -/
structure SeedI (n : Nat) (s : State) (S : Addr) (c : Nat) (t : State) : Prop where
  keep : Keep [.x14] s t
  frame : Frame (seedRegions n S) s.mem t.mem
  lanes : ∀ j < c, bytesAt t.mem (at' S (Layout.laneA j)) n = bytesAt s.mem (at' S Layout.oPkSeed) n ∧
    bytesAt t.mem (at' S (Layout.laneB j)) n = bytesAt s.mem (at' S Layout.oPkSeed) n

/-- `seedLanes`: `PK.seed` (at `oPkSeed`) to every lane of `A` and `B`. -/
theorem seedLanes_ok {p : Spec.SlhDsa.Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr}
    (hS : s.gpr .x19 = S) (hw : (⟨S, scratchLen⟩ : Region) ∈ s.wr)
    (k : ∀ s', SeedI p.n s S 4 s' → WP isa (.block is) s' Q) :
    WP isa (.block (Shake.seedLanes p ++ is)) s Q := by
  have h8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  simp only [Shake.seedLanes]
  refine wp_rangeFlatMap 4 ⟨Keep.refl _ _, Frame.refl _ _, fun j hj => absurd hj (by omega_using [])⟩
    (fun j hj t is' ht k' => ?_) k
  have g19 : t.gpr .x19 = S := by rw [ht.keep.get .x19 (by simp), hS]
  have hwt : (⟨S, scratchLen⟩ : Region) ∈ t.wr := by rw [ht.keep.wr]; exact hw
  -- `PK.seed` is apart from every lane
  have pkd : ∀ r ∈ seedRegions p.n S, Region.Disjoint ⟨at' S Layout.oPkSeed, p.n⟩ r := by
    intro r hr
    simp only [seedRegions, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨i, hi, rfl | rfl⟩ := hr
    · exact Offset.disjoint S (by rw [oPkSeed_eq, laneA_eq]; omega_using [hn32])
        (by rw [oPkSeed_eq]; omega_using [hn32]) (by rw [laneA_eq]; omega_using [hn32, hi])
    · exact Offset.disjoint S (by rw [oPkSeed_eq, laneB_eq]; omega_using [hn32])
        (by rw [oPkSeed_eq]; omega_using [hn32]) (by rw [laneB_eq]; omega_using [hn32, hi])
  have pkt : ∀ {u : State}, Frame (seedRegions p.n S) s.mem u.mem →
      bytesAt u.mem (at' S Layout.oPkSeed) p.n = bytesAt s.mem (at' S Layout.oPkSeed) p.n :=
    fun hf => bytesAt_frame hf pkd (by omega_using [hn32])
  have memA : (⟨at' S (Layout.laneA j), p.n⟩ : Region) ∈ seedRegions p.n S := by
    simp only [seedRegions, List.mem_flatMap, List.mem_range]; exact ⟨j, hj, by simp⟩
  have memB : (⟨at' S (Layout.laneB j), p.n⟩ : Region) ∈ seedRegions p.n S := by
    simp only [seedRegions, List.mem_flatMap, List.mem_range]; exact ⟨j, hj, by simp⟩
  have dA : Region.Disjoint ⟨S + BitVec.ofNat 64 (Layout.laneA j), p.n⟩ ⟨S + BitVec.ofNat 64 Layout.oPkSeed, p.n⟩ :=
    Offset.disjoint S (by rw [laneA_eq, oPkSeed_eq]; omega) (by rw [laneA_eq]; omega) (by rw [oPkSeed_eq]; omega)
  have dB : Region.Disjoint ⟨S + BitVec.ofNat 64 (Layout.laneB j), p.n⟩ ⟨S + BitVec.ofNat 64 Layout.oPkSeed, p.n⟩ :=
    Offset.disjoint S (by rw [laneB_eq, oPkSeed_eq]; omega) (by rw [laneB_eq]; omega) (by rw [oPkSeed_eq]; omega)
  rw [List.append_assoc]
  refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.laneA j) (d₁ := Layout.oPkSeed) (w := p.n / 8)
    ⟨by decide, by decide,
    ⟨by rw [oPkSeed_eq], by rw [oPkSeed_eq]; omega_using [h8, hn32]⟩,
    ⟨by rw [laneA_eq]; omega_using [hn8], by rw [laneA_eq]; omega_using [h8, hn32, hj]⟩,
    (by rw [g19, h8]; exact scr_in' hwt (by rw [oPkSeed_eq]; omega_using [hn32])),
    (by rw [g19, h8]; exact scr_in hwt (by rw [laneA_eq]; omega_using [hn32, hj])),
    (by rw [g19, h8]; exact dA)⟩ fun t₁ k₁ f₁ b₁ => ?_
  rw [g19, h8] at f₁ b₁
  have g19' : t₁.gpr .x19 = S := by rw [k₁.get .x19 (by simp), g19]
  have hwt₁ : (⟨S, scratchLen⟩ : Region) ∈ t₁.wr := by rw [k₁.wr]; exact hwt
  have F₁ : Frame (seedRegions p.n S) s.mem t₁.mem := ht.frame.trans (f₁.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact memA)
  refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.laneB j) (d₁ := Layout.oPkSeed) (w := p.n / 8)
    ⟨by decide, by decide,
    ⟨by rw [oPkSeed_eq], by rw [oPkSeed_eq]; omega_using [h8, hn32]⟩,
    ⟨by rw [laneB_eq]; omega_using [hn8], by rw [laneB_eq]; omega_using [h8, hn32, hj]⟩,
    (by rw [g19', h8]; exact scr_in' hwt₁ (by rw [oPkSeed_eq]; omega_using [hn32])),
    (by rw [g19', h8]; exact scr_in hwt₁ (by rw [laneB_eq]; omega_using [hn32, hj])),
    (by rw [g19', h8]; exact dB)⟩ fun t₂ k₂ f₂ b₂ => k' t₂ ?_
  rw [g19', h8] at f₂ b₂
  have F₂ : Frame (seedRegions p.n S) s.mem t₂.mem := F₁.trans (f₂.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact memB)
  have dAB : Region.Disjoint ⟨at' S (Layout.laneA j), p.n⟩ ⟨at' S (Layout.laneB j), p.n⟩ :=
    Offset.disjoint S (by rw [laneA_eq, laneB_eq]; omega_using [hn32, hj]) (by rw [laneA_eq]; omega_using [hn32, hj])
      (by rw [laneB_eq]; omega_using [hn32, hj])
  refine ⟨(ht.keep.trans (k₁.trans k₂)).mono (by simp), F₂, fun i hi => ?_⟩
  by_cases e : i = j
  · subst e
    refine ⟨?_, ?_⟩
    · rw [bytesAt_frame f₂ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAB)
        (by omega_using [hn32]), b₁, pkt ht.frame]
    · rw [b₂, pkt F₁]
  · have hi' : i < j := by omega_using [hi, e]
    have dA : ∀ r ∈ [(⟨at' S (Layout.laneA j), p.n⟩ : Region)], Region.Disjoint ⟨at' S (Layout.laneA i), p.n⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint S (by rw [laneA_eq, laneA_eq]; omega_using [hn32, hj, hi'])
        (by rw [laneA_eq]; omega_using [hn32, hj, hi']) (by rw [laneA_eq]; omega_using [hn32, hj])
    have dB : ∀ r ∈ [(⟨at' S (Layout.laneB j), p.n⟩ : Region)], Region.Disjoint ⟨at' S (Layout.laneB i), p.n⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint S (by rw [laneB_eq, laneB_eq]; omega_using [hn32, hj, hi'])
        (by rw [laneB_eq]; omega_using [hn32, hj, hi']) (by rw [laneB_eq]; omega_using [hn32, hj])
    have dAB' : ∀ r ∈ [(⟨at' S (Layout.laneB j), p.n⟩ : Region)], Region.Disjoint ⟨at' S (Layout.laneA i), p.n⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint S (by rw [laneA_eq, laneB_eq]; omega_using [hn32, hj, hi'])
        (by rw [laneA_eq]; omega_using [hn32, hj, hi']) (by rw [laneB_eq]; omega_using [hn32, hj])
    have dBA : ∀ r ∈ [(⟨at' S (Layout.laneA j), p.n⟩ : Region)], Region.Disjoint ⟨at' S (Layout.laneB i), p.n⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint S (by rw [laneB_eq, laneA_eq]; omega_using [hn32, hj, hi'])
        (by rw [laneB_eq]; omega_using [hn32, hj, hi']) (by rw [laneA_eq]; omega_using [hn32, hj])
    obtain ⟨hA, hB⟩ := ht.lanes i hi'
    refine ⟨?_, ?_⟩
    · rw [bytesAt_frame f₂ dAB' (by omega_using [hn32]), bytesAt_frame f₁ dA (by omega_using [hn32]), hA]
    · rw [bytesAt_frame f₂ dB (by omega_using [hn32]), bytesAt_frame f₁ dBA (by omega_using [hn32]), hB]

theorem rev64_byte (v : BitVec 64) {j : Nat} (hj : j < 8) :
    (rev64 v).extractLsb' (8 * j) 8 = v.extractLsb' (8 * (7 - j)) 8 := by
  ext r hr
  simp only [BitVec.getElem_extractLsb', rev64, VG.AArch64.getLsbD_append_block _ _ _ hr]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := omega_using [hr]) only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul, BitVec.getLsbD_extractLsb', decide_eq_true, Bool.true_and, Nat.add_comm]

theorem bytesAt_add (m : Mem) (a : Addr) (k l : Nat) :
    bytesAt m a (k + l) = bytesAt m a k ++ bytesAt m (a + BitVec.ofNat 64 k) l := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, addr_add]

/-- The eight bytes of a write of `rev64 x`: `x`, big-endian. -/
theorem bytesAt_rev64 (m : Mem) (a : Addr) (x : BitVec 64) :
    bytesAt (m.writeW a (rev64 x)) a 8 = Spec.SlhDsa.toByte x.toNat 8 := by
  simp only [bytesAt, Spec.SlhDsa.toByte]
  refine List.map_congr_left fun j hj => ?_
  have hj' := List.mem_range.mp hj
  rw [MlKem.AArch64.KeyGen.writeW64_byte _ _ _ hj', rev64_byte _ hj']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 - 1 - j = 7 - j by omega_using [], Nat.pow_mul]

theorem toByte_12 {T : Nat} (hT : T < 2 ^ 64) : Spec.SlhDsa.toByte T 12 = Spec.SlhDsa.toByte 0 4 ++ Spec.SlhDsa.toByte T 8 := by
  simp only [Spec.SlhDsa.toByte, show (12 : Nat) = 4 + 8 from rfl, List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have : T / 256 ^ (4 + 8 - 1 - i) = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hT (by
      rw [show (2 : Nat) ^ 64 = 256 ^ 8 by decide]; exact Nat.pow_le_pow_right (by decide) (by omega_using [hi'])))
    simp only [this, Nat.zero_div]

/-- The 16 bytes of a lane's layer and tree addresses. -/
theorem layerTree_eq {L T : Nat} (hT : T < 2 ^ 64) :
    Proof.SlhDsa.layerTree L T = Spec.SlhDsa.toByte L 4 ++ (Spec.SlhDsa.toByte 0 4 ++ Spec.SlhDsa.toByte T 8) := by
  simp only [Proof.SlhDsa.layerTree, toByte_12 hT]

/-- Lane `k`'s (`b = 0`: `A`, else `B`) address. -/
def laneAdrs (n k b : Nat) : Nat := (if b = 0 then Layout.laneA k else Layout.laneB k) + n

/-- The lanes' layer and tree addresses. -/
def adrsRegions (n : Nat) (S : Addr) : List Region :=
  (List.range 4).flatMap fun k => (List.range 2).map fun b => ⟨at' S (laneAdrs n k b), 16⟩

theorem laneAdrs_lt {n k b : Nat} (hn : n ≤ 32) (hk : k < 4) (_hb : b < 2) :
    3136 + n ≤ laneAdrs n k b ∧ laneAdrs n k b + 16 ≤ 11000 := by
  simp only [laneAdrs, laneA_eq, laneB_eq]; split <;> omega

theorem laneAdrs_disj {n k b k' b' : Nat} (hn : n ≤ 32) (hk : k < 4) (hk' : k' < 4) (hb : b < 2) (hb' : b' < 2)
    (h : 2 * k + b ≠ 2 * k' + b') : laneAdrs n k b + 16 ≤ laneAdrs n k' b' ∨ laneAdrs n k' b' + 16 ≤ laneAdrs n k b := by
  simp only [laneAdrs, laneA_eq, laneB_eq]; split <;> split <;> omega

/-- After the stores of the lanes before `(k, b)` (`2k + b` of them). -/
structure TreeI (n : Nat) (s : State) (S : Addr) (v12 : BitVec 64) (v13 : BitVec 32) (a16 : List Byte) (c : Nat)
    (t : State) : Prop where
  keep : Keep [.x12, .x13, .x14] s t
  x19 : t.gpr .x19 = S
  x12 : t.gpr .x12 = v12
  x13 : (t.gpr .x13).setWidth 32 = v13
  x14 : t.gpr .x14 = 0
  frame : Frame (adrsRegions n S) s.mem t.mem
  done : ∀ k < 4, ∀ b < 2, 2 * k + b < c → bytesAt t.mem (at' S (laneAdrs n k b)) 16 = a16

theorem mem_adrsRegions {n k b : Nat} {S : Addr} (hk : k < 4) (hb : b < 2) :
    (⟨at' S (laneAdrs n k b), 16⟩ : Region) ∈ adrsRegions n S := by
  simp only [adrsRegions, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨k, hk, b, hb, rfl⟩

theorem frame_sub {rs : List Region} {m m' : Mem} {r : Region} (hf : Frame [r] m m') (hr : r ∈ rs) : Frame rs m m' :=
  hf.mono fun r' h => by simp only [List.mem_singleton] at h; subst h; exact hr

/-- The stores of lane `(k, b)`'s address. -/
private theorem lane_ok {n : Nat} (hn : n ≤ 32) (hn8 : n % 8 = 0) {S : Addr} {L T : Nat} (hL : L < 2 ^ 32)
    (hT : T < 2 ^ 64)
    {c k b : Nat} (hk : k < 4) (hb : b < 2) (hc : c = 2 * k + b) {t : State} {rest : List Instr}
    (hw : (⟨S, scratchLen⟩ : Region) ∈ s.wr)
    (ht : TreeI n s S (rev64 (BitVec.ofNat 64 T)) (rev32 (BitVec.ofNat 32 L)) (Proof.SlhDsa.layerTree L T) c t)
    (k' : ∀ t', TreeI n s S (rev64 (BitVec.ofNat 64 T)) (rev32 (BitVec.ofNat 32 L)) (Proof.SlhDsa.layerTree L T)
      (c + 1) t' → WP isa (.block rest) t' Q) :
    WP isa (.block (([.str .w .x13 .x19 (laneAdrs n k b), .str .w .x14 .x19 (laneAdrs n k b + 4),
      .str .x .x12 .x19 (laneAdrs n k b + 8)] : List Instr) ++ rest)) t Q := by
  obtain ⟨l₁, l₂⟩ := laneAdrs_lt (n := n) hn hk hb
  have h8 : laneAdrs n k b % 8 = 0 := by simp only [laneAdrs, laneA_eq, laneB_eq]; split <;> omega
  have hwt : (⟨S, scratchLen⟩ : Region) ∈ t.wr := by rw [ht.keep.wr]; exact hw
  simp only [List.cons_append, List.nil_append]
  refine wp_strw (a := at' S (laneAdrs n k b)) ⟨by omega, by omega⟩ (by rw [ht.x19])
    (scr_in hwt (by omega)) fun t₁ m₁ => ?_
  refine wp_strw (a := at' S (laneAdrs n k b + 4)) ⟨by omega, by omega⟩ (by rw [m₁.gpr, ht.x19])
    (by rw [m₁.wr]; exact scr_in hwt (by omega)) fun t₂ m₂ => ?_
  refine wp_strx (a := at' S (laneAdrs n k b + 8)) ⟨by omega, by omega⟩ (by rw [m₂.gpr, m₁.gpr, ht.x19])
    (by rw [m₂.wr, m₁.wr]; exact scr_in hwt (by omega)) fun t₃ m₃ => k' t₃ ?_
  have g : t₃.gpr = t.gpr := by rw [m₃.gpr, m₂.gpr, m₁.gpr]
  have reg : Region.Sub ⟨at' S (laneAdrs n k b), 16⟩ ⟨at' S (laneAdrs n k b), 16⟩ := fun _ h => h
  have F : Frame [⟨at' S (laneAdrs n k b), 16⟩] t.mem t₃.mem := by
    have s1 : Region.Sub ⟨at' S (laneAdrs n k b), 4⟩ ⟨at' S (laneAdrs n k b), 16⟩ := Region.sub_prefix (by decide)
    have s2 : Region.Sub ⟨at' S (laneAdrs n k b + 4), 4⟩ ⟨at' S (laneAdrs n k b), 16⟩ := Offset.sub S (by omega) (by omega)
    have s3 : Region.Sub ⟨at' S (laneAdrs n k b + 8), 8⟩ ⟨at' S (laneAdrs n k b), 16⟩ := Offset.sub S (by omega) (by omega)
    have f1 := (frame_writeW32 t.mem (at' S (laneAdrs n k b)) ((t.gpr .x13).setWidth 32)).sub
      (rs' := [⟨at' S (laneAdrs n k b), 16⟩]) fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact s1⟩
    have f2 := (frame_writeW32 t₁.mem (at' S (laneAdrs n k b + 4)) ((t₁.gpr .x14).setWidth 32)).sub
      (rs' := [⟨at' S (laneAdrs n k b), 16⟩]) fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact s2⟩
    have f3 := (frame_writeW64 t₂.mem (at' S (laneAdrs n k b + 8)) (t₂.gpr .x12)).sub
      (rs' := [⟨at' S (laneAdrs n k b), 16⟩]) fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact s3⟩
    rw [m₃.mem]; refine Frame.trans ?_ f3
    rw [m₂.mem]; refine Frame.trans ?_ f2
    rw [m₁.mem]; exact f1
  refine ⟨(ht.keep.trans (m₁.keep.trans (m₂.keep.trans m₃.keep))).mono (by simp), by rw [g, ht.x19],
    by rw [g, ht.x12], by rw [g, ht.x13], by rw [g, ht.x14],
    ht.frame.trans (frame_sub F (mem_adrsRegions hk hb)), fun k₀ hk₀ b₀ hb₀ hc₀ => ?_⟩
  by_cases e : 2 * k₀ + b₀ = c
  · have ek : k₀ = k ∧ b₀ = b := by omega
    obtain ⟨rfl, rfl⟩ := ek
    have d12 : ∀ r ∈ [(⟨at' S (laneAdrs n k₀ b₀ + 8), 8⟩ : Region)],
        Region.Disjoint ⟨at' S (laneAdrs n k₀ b₀), 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega)
    have d2 : ∀ r ∈ [(⟨at' S (laneAdrs n k₀ b₀ + 8), 8⟩ : Region)],
        Region.Disjoint ⟨at' S (laneAdrs n k₀ b₀ + 4), 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega)
    have d1 : ∀ r ∈ [(⟨at' S (laneAdrs n k₀ b₀ + 4), 4⟩ : Region)],
        Region.Disjoint ⟨at' S (laneAdrs n k₀ b₀), 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega)
    rw [show (16 : Nat) = 4 + (4 + 8) from rfl, bytesAt_add, bytesAt_add, addr_add, addr_add, Nat.add_assoc,
      show 4 + 4 = 8 from rfl, layerTree_eq hT]
    have hT' : (BitVec.ofNat 64 T).toNat = T := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT]
    congr 1
    · rw [m₃.mem, bytesAt_frame (frame_writeW64 _ _ _) d12 (by decide), m₂.mem, bytesAt_frame (frame_writeW32 _ _ _) d1 (by decide),
        m₁.mem, bytesAt_writeW32, ht.x13, rev32_bytes32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL]
    congr 1
    · rw [m₃.mem, bytesAt_frame (frame_writeW64 _ _ _) d2 (by decide), m₂.mem, bytesAt_writeW32, m₁.gpr, ht.x14]
      exact toByte4_eq _ _ fun j _ => by simp
    · rw [m₃.mem, m₂.gpr, m₁.gpr, ht.x12, bytesAt_rev64, hT']
  · rw [bytesAt_frame F (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := laneAdrs_lt (n := n) hn hk₀ hb₀
      exact Offset.disjoint S (laneAdrs_disj hn hk₀ hk hb₀ hb (by omega)) (by omega) (by omega)) (by decide)]
    exact ht.done k₀ hk₀ b₀ hb₀ (by omega)

/-- `treeLanes p layer tree`: every lane's layer and tree addresses, the
16 bytes `layerTree L T` of the layer `L` (below `2³²`) in `layer` and the
tree `T` in `tree`, through `x12`–`x14`. -/
theorem treeLanes_ok {p : Spec.SlhDsa.Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {layer tree : Reg}
    (hlt : layer ≠ .x12) {S : Addr} (hS : s.gpr .x19 = S) (hw : (⟨S, scratchLen⟩ : Region) ∈ s.wr)
    (hL : (s.gpr layer).toNat < 2 ^ 32)
    (k : ∀ s', Keep [.x12, .x13, .x14] s s' → Frame (adrsRegions p.n S) s.mem s'.mem →
      (∀ j < 4, ∀ b < 2, bytesAt s'.mem (at' S (laneAdrs p.n j b)) 16 =
        Proof.SlhDsa.layerTree (s.gpr layer).toNat (s.gpr tree).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (Shake.treeLanes p layer tree ++ is)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  simp only [Shake.treeLanes, List.cons_append, List.append_assoc]
  rw [List.nil_append]
  refine MlKem.AArch64.WP.cons (s' := s.write .x .x12 (rev64 (s.read .x tree))) rfl ?_
  refine MlKem.AArch64.WP.cons exec_rev32 ?_
  refine wp_movz fun t₃ o₃ e₃ => ?_
  have o₁ := MlKem.AArch64.only_write s .x .x12 (rev64 (s.read .x tree))
  have o₂ := only_write_w (s.write .x .x12 (rev64 (s.read .x tree))) .x13
    (rev32 ((s.write .x .x12 (rev64 (s.read .x tree))).read .w layer))
  have hT : (s.gpr tree).toNat < 2 ^ 64 := (s.gpr tree).isLt
  refine wp_rangeFlatMap (P := fun j t => TreeI p.n s S (rev64 (BitVec.ofNat 64 (s.gpr tree).toNat))
      (rev32 (BitVec.ofNat 32 (s.gpr layer).toNat)) (Proof.SlhDsa.layerTree (s.gpr layer).toNat (s.gpr tree).toNat)
      (2 * j) t) 4 ⟨((o₁.trans (o₂.trans o₃)).keep).mono (by simp), ?_, ?_, ?_, ?_, by rw [o₃.mem]; exact Frame.refl _ _, fun _ _ _ _ h => absurd h (by omega)⟩
    (fun j hj t is' ht k' => ?_) (fun t ht => k t ht.keep ht.frame fun j hj b hb => ht.done j hj b hb (by omega))
  · rw [o₃.get .x19 (by simp), o₂.get .x19 (by simp), o₁.get .x19 (by simp), hS]
  · rw [o₃.get .x12 (by simp), o₂.get .x12 (by simp), MlKem.AArch64.write_x_gpr, read_x, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [o₃.get .x13 (by simp), write_w_low]
    rw [show (s.write .x .x12 (rev64 (s.read .x tree))).read .w layer = (s.gpr layer).setWidth 32 by
      unfold State.read; exact congrArg _ (o₁.get layer (by simpa using hlt))]
    congr 1
  · rw [e₃]; rfl
  · refine wp_rangeFlatMap (P := fun b t => TreeI p.n s S (rev64 (BitVec.ofNat 64 (s.gpr tree).toNat))
      (rev32 (BitVec.ofNat 32 (s.gpr layer).toNat)) (Proof.SlhDsa.layerTree (s.gpr layer).toNat (s.gpr tree).toNat)
      (2 * j + b) t) 2 ht (fun b hb t' is'' ht' k'' => ?_) (fun t' ht' => k' t' (by
        rw [show 2 * (j + 1) = 2 * j + 2 by omega]; exact ht'))
    exact lane_ok hn32 hn8 hL hT hj hb rfl hw ht' k''

end

end VG.Proof.SlhDsa.AArch64
