module

-- separate module: the trees of `forsSign`, a stage of its proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsTopRoot
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, the trees

`treeBody` (`Impl/SlhDsa/AArch64/Fors.lean`), tree `t`: its index, its
signature zeroed (`tree0_ok`), its subtrees, the heights above them, the
next tree (`tree_ok`); its pass of the loop (`tree_step`), and the loop of
the `k` trees (`trees_ok`). As x86-64's `ForsMain.lean`, with the counters
in `x23`, `x24` and `x27`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Fors (s)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.SlhDsa.X86_64.Fors (node sib acc acc_zero)

variable {p : Params}

/-- The length of a tree's signature. -/
abbrev tsl (p : Params) : Nat := (p.a + 1) * p.n

/-- What the trees need of the state `t₀` before them. -/
structure MC (p : Params) (S SG : Addr) (t₀ : State) : Prop where
  hz : Sz p
  a6 : 6 ≤ p.a
  a14 : p.a ≤ 14
  k1 : 1 ≤ p.k
  k35 : p.k ≤ 35
  k2 : p.k * 2 ^ p.a < 2 ^ 32
  x19 : t₀.gpr .x19 = S
  kp : (t₀.gpr .x20).toNat < 2 ^ 32
  w : (⟨S, 65536⟩ : Region) ∈ t₀.wr
  wG : (⟨SG, p.k * tsl p⟩ : Region) ∈ t₀.wr
  Gf : SG.toNat + p.k * tsl p ≤ 2 ^ 64
  fit : S.toNat + 65536 ≤ 2 ^ 64
  Gd : Region.Disjoint ⟨SG, p.k * tsl p⟩ ⟨S, Layout.oSigTmp⟩

/-- What the trees change. -/
abbrev treeW (p : Params) (S SG : Addr) : List Region :=
  [⟨S, workUsed⟩, ⟨at' S (Layout.oFrame 3), Layout.frameLen⟩, ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩,
    ⟨at' S Layout.oRoots, 1024⟩, ⟨at' S (Layout.laneB 0 + p.n + 32), 1120⟩, ⟨SG, p.k * tsl p⟩] ++
  (List.range 4).map fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)

/-- The state before tree `tt`, from the state `t₀` before the trees, the
trees' indices `ix`. -/
structure TL (p : Params) (S SG : Addr) (pk a16 sk : List Byte) (ix : Nat → Nat) (t₀ : State) (tt : Nat)
    (t : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x21 → r ≠ .x23 → r ≠ .x24 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → r ≠ .x30 →
    t.gpr r = t₀.gpr r
  x23 : t.gpr .x23 = BitVec.ofNat 64 tt
  x24 : t.gpr .x24 = SG + BitVec.ofNat 64 (tt * tsl p)
  x27 : t.gpr .x27 = BitVec.ofNat 64 (tt * 2 ^ p.a)
  sp : t.sp = t₀.sp
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  vcs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (t₀.v r).extractLsb' 0 64
  env : Env p t.mem S pk a16
  skat : SkAt p t.mem S sk
  fidx : ∀ i < p.k, t.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (ix i)
  skp : ∀ t' < tt, ∀ j < p.n, t.mem (SG + BitVec.ofNat 64 (t' * tsl p + j)) =
    skv p pk a16 sk (t₀.gpr .x20).toNat (t' * 2 ^ p.a + ix t') j
  auth : ∀ t' < tt, ∀ r < p.a, bytesAt t.mem (SG + BitVec.ofNat 64 (t' * tsl p + p.n + r * p.n)) p.n =
    node p sk pk a16 (t₀.gpr .x20).toNat (t' * 2 ^ (p.a - r) + sib (ix t') r) r
  roots : ∀ t' < tt, bytesAt t.mem (at' S (rootAt p.n t')) p.n = node p sk pk a16 (t₀.gpr .x20).toNat t' p.a
  frame : Frame (treeW p S SG) t₀.mem t.mem

theorem MC.dxs {S SG : Addr} {t₀ : State} (M : MC p S SG t₀) {o l : Nat} (h : o + l ≤ p.k * tsl p) {R : Region}
    (hR : Region.Sub R ⟨S, Layout.oSigTmp⟩) : Region.Disjoint ⟨SG + BitVec.ofNat 64 o, l⟩ R :=
  (M.Gd.sub_left (Offset.sub_base SG h)).sub_right hR

/-! ## The first block of a tree -/

/-- The first block of `treeBody`. -/
abbrev t0List (n a : Nat) : List Instr :=
  ([.lsl .x .x9 .x23 3, .add .x .x9 .x9 .x19, .ldr .x .x21 .x9 Layout.oFidx] : List Instr) ++
    Impl.SlhDsa.AArch64.zeroWords .x24 0 ((a + 1) * n / 8) ++ ([.movz .x .x25 0 0] : List Instr)

/-- What the first block of tree `tt` leaves, besides the subtrees' loop's entry. -/
structure T0 (p : Params) (S SG : Addr) (tt : Nat) (t t₁ : State) : Prop where
  keep : Keep [.x9, .x21, .x14, .x25] t t₁
  frame : Frame [⟨SG + BitVec.ofNat 64 (tt * tsl p), tsl p⟩] t.mem t₁.mem

theorem shl3 (x : Nat) : BitVec.ofNat 64 x <<< 3 = BitVec.ofNat 64 (x * 8) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 3 = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_mul_ofNat]

theorem tsl_le (hn32 : p.n ≤ 32) (ha : p.a ≤ 14) : tsl p ≤ 480 := Nat.mul_le_mul (show p.a + 1 ≤ 15 by omega) hn32

/-- The subtrees' loop's invariant at its entry, the tree's signature zeroed. -/
theorem st0 (hz : Sz p) (ha : p.a ≤ 14) {S AU : Addr} {pk a16 sk : List Byte} {kp tt idx : Nat} {t₁ : State}
    (h25 : t₁.gpr .x25 = 0) (hE : Env p t₁.mem S pk a16) (hs : SkAt p t₁.mem S sk)
    (hz0 : ∀ q < tsl p, t₁.mem (AU + BitVec.ofNat 64 q) = 0) :
    ST p S AU pk a16 sk kp tt idx t₁ 0 t₁ := by
  have hn32 := hz.n32
  have hzB : ∀ o, o + p.n ≤ tsl p → bytesAt t₁.mem (AU + BitVec.ofNat 64 o) p.n = toByte 0 p.n := fun o ho =>
    bytesAt_eq (by simp [toByte]) fun i hi => by
      rw [addr_add, hz0 _ (by omega), Proof.SlhDsa.toByte_zero]; simp [hi]
  have hrn : ∀ r < p.a, p.n + r * p.n + p.n ≤ tsl p := fun r hr => by
    have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega); rw [Nat.succ_mul] at this
    simp only [tsl]; rw [Nat.add_mul, Nat.one_mul]; omega
  refine ⟨fun _ _ _ _ _ => rfl, by rw [h25, Nat.zero_mul]; rfl, rfl, rfl, rfl, fun _ _ => rfl, hE, hs,
    fun j hj => by rw [ite_eq_right (by omega)]; exact hz0 j (by simp only [tsl]; rw [Nat.add_mul]; omega),
    fun r hr => by rw [acc_zero, addr_add]; exact hzB _ (hrn r (by have := s_le p.a; omega)),
    fun r _ h₂ => by rw [addr_add]; exact hzB _ (hrn r h₂),
    fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩

/-- Tree `tt`'s index, its signature zeroed: the subtrees' loop's entry. -/
theorem tree0_ok {S SG : Addr} {pk a16 sk : List Byte} {ix : Nat → Nat} {t₀ : State} (M : MC p S SG t₀)
    (hix : ∀ i < p.k, ix i < 2 ^ p.a) {tt : Nat} (htt : tt < p.k) {t : State}
    (hI : TL p S SG pk a16 sk ix t₀ tt t) :
    WP isa (.block (t0List p.n p.a)) t fun t₁ =>
      SC p S SG (SG + BitVec.ofNat 64 (tt * tsl p)) (p.k * tsl p) (tt * tsl p) tt (ix tt) t₁ ∧
      ST p S (SG + BitVec.ofNat 64 (tt * tsl p)) pk a16 sk (t₁.gpr .x20).toNat tt (ix tt) t₁ 0 t₁ ∧
      T0 p S SG tt t t₁ := by
  have hz := M.hz
  have hn32 := hz.n32
  have hn16 := hz.n16
  have hT := tsl_le hn32 M.a14
  have hT1 : 16 ≤ tsl p := by have := Nat.mul_le_mul (show 1 ≤ p.a + 1 by omega) hn16; simp only [tsl]; omega
  have hkt : (tt + 1) * tsl p ≤ p.k * tsl p := Nat.mul_le_mul_right _ htt
  rw [Nat.succ_mul] at hkt
  have e8 : 8 * ((p.a + 1) * p.n / 8) = tsl p :=
    Nat.mul_div_cancel' (Nat.dvd_mul_left_of_dvd (by have := hz.n8; omega) _)
  have eF : Layout.oFidx = 2048 := rfl
  have g : ∀ r ∈ preserved, r ≠ .x21 → r ≠ .x23 → r ≠ .x24 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → r ≠ .x30 →
      t.gpr r = t₀.gpr r := hI.cs
  have h19 : t.gpr .x19 = S := by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), M.x19]
  have hw : (⟨S, 65536⟩ : Region) ∈ t.wr := by rw [hI.wr]; exact M.w
  have hwG : (⟨SG, p.k * tsl p⟩ : Region) ∈ t.wr := by rw [hI.wr]; exact M.wG
  simp only [t0List, List.append_assoc, List.cons_append]
  refine wp_lsl (by decide) fun t₁ u₁ => wp_addr fun t₂ u₂ => ?_
  have h9 : t₂.gpr .x9 = at' S (tt * 8) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.x23, h19, shl3, at', BitVec.add_comm]
  refine MlKem.AArch64.wp_ldrx (a := at' S (Layout.oFidx + 8 * tt)) (by decide)
    (by rw [h9, at_add, show tt * 8 + Layout.oFidx = Layout.oFidx + 8 * tt by omega])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_scr' hw (by have := M.k35; rw [eF]; omega)) fun t₃ o₃ e₃ => ?_
  have k₃ : Keep [.x9, .x21] t t₃ := (((upK u₁).trans (upK u₂)).trans o₃.keep).mono (by simp)
  have hm₃ : t₃.mem = t.mem := by rw [o₃.mem, u₂.mem, u₁.mem]
  have hAU : t₃.gpr .x24 + BitVec.ofNat 64 0 = SG + BitVec.ofNat 64 (tt * tsl p) := by
    rw [BitVec.add_zero, k₃.get .x24, hI.x24]
  refine zeroWords_ok (by decide) ⟨by decide, by rw [Nat.zero_add, e8]; omega⟩ (by
      rw [hAU, e8, k₃.wr]
      exact ⟨_, hwG, Offset.contains_base SG (by omega) (by have := M.Gf; omega)⟩) fun t₄ k₄ f₄ z₄ => ?_
  rw [hAU, e8] at f₄ z₄
  refine wp_movz fun t₅ u₅ => WP.block_nil ?_
  have k₅ : Keep [.x9, .x21, .x14, .x25] t t₅ := ((k₃.trans k₄).trans (upK u₅)).mono (by simp)
  have hm₅ : t₅.mem = t₄.mem := u₅.mem
  have g₅ : ∀ r ∈ preserved, r ≠ .x21 → r ≠ .x23 → r ≠ .x24 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → r ≠ .x30 →
      t₅.gpr r = t₀.gpr r := fun r hr h₁ h₂ h₃ h₄ h₅ h₆ h₇ => by
    rw [k₅.gpr r (by revert r; decide), g r hr h₁ h₂ h₃ h₄ h₅ h₆ h₇]
  have kp₅ : t₅.gpr .x20 = t₀.gpr .x20 :=
    g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have C : SC p S SG (SG + BitVec.ofNat 64 (tt * tsl p)) (p.k * tsl p) (tt * tsl p) tt (ix tt) t₅ := by
    refine ⟨hz, M.a6, M.a14, by rw [k₅.get .x19, h19], by rw [kp₅]; exact M.kp, ?_, hix tt htt,
      by rw [k₅.get .x24, hI.x24], by rw [k₅.get .x27, hI.x27], by rw [k₅.wr]; exact hw, by rw [k₅.wr]; exact hwG,
      rfl, by omega, M.Gf, M.fit, M.Gd, ?_⟩
    · rw [u₅.other _ (by decide), k₄.get .x21, e₃, u₂.mem, u₁.mem, hI.fidx tt htt]
    · have := Nat.mul_le_mul_right (2 ^ p.a) (show tt + 1 ≤ p.k by omega); have := M.k2; omega
  -- the tree's signature zeroed
  have hF : Frame [⟨SG + BitVec.ofNat 64 (tt * tsl p), tsl p⟩] t.mem t₅.mem := by rw [hm₅, ← hm₃]; exact f₄
  have hsig : ∀ {R : Region}, Region.Sub R ⟨S, Layout.oSigTmp⟩ →
      ∀ r ∈ [(⟨SG + BitVec.ofNat 64 (tt * tsl p), tsl p⟩ : Region)], Region.Disjoint R r := fun hR r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (M.dxs (by omega) hR).symm
  have hz0 : ∀ q < tsl p, t₅.mem (SG + BitVec.ofNat 64 (tt * tsl p) + BitVec.ofNat 64 q) = 0 := fun q hq => by
    have := congrArg (·.getD q 0) z₄
    simp only [getD_bytesAt _ _ hq] at this
    rw [hm₅, this]; simp [hq]
  refine ⟨C, st0 hz M.a14 (u₅.gpr.trans (by rfl))
    (env_keep hn32 hI.env hF fun r hr k hk =>
      ⟨hsig (Offset.sub_base S (by rw [laneA_eq, show Layout.oSigTmp = 30144 from rfl]; omega)) r hr,
        hsig (Offset.sub_base S (by rw [laneB_eq, show Layout.oSigTmp = 30144 from rfl]; omega)) r hr⟩)
    (sk_keep hI.skat hF (hsig (Offset.sub_base S (by
      rw [show Layout.oSkSeed = 1664 from rfl, show Layout.oSigTmp = 30144 from rfl]; omega))) (by omega)) hz0,
    k₅, hF⟩

/-! ## The rest of a tree -/

/-- What a tree's subtrees and heights change, but the tree's signature, is below `oSigTmp`. -/
theorem topW_low (hn32 : p.n ≤ 32) (S AU : Addr) {tt : Nat} (htk : (tt + 1) * p.n ≤ 1120) :
    ∀ r ∈ subW p S AU ++ [⟨at' S (rootAt p.n tt), p.n⟩], r = ⟨AU, tsl p⟩ ∨ Region.Sub r ⟨S, Layout.oSigTmp⟩ := by
  have eT : Layout.oSigTmp = 30144 := rfl
  intro r hr
  simp only [subW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩) | rfl
  · exact .inr (Region.sub_prefix (by rw [show workUsed = 1008 from rfl, eT]; omega))
  · exact .inr (Offset.sub_base S (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl, eT]; omega))
  · exact .inr (Offset.sub_base S (by rw [show Layout.oN = 12480 from rfl, show Layout.nodeSlots = 520 from rfl, eT] <;> omega))
  · exact .inr (Offset.sub_base S (by rw [show Layout.oRoots = 29120 from rfl, eT] <;> omega))
  · exact .inl rfl
  · exact .inr (Offset.sub_base S (by rw [laneA_eq, eT]; omega))
  · have h' := htk
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact .inr (Offset.sub_base S (by simp only [rootAt]; rw [show Layout.laneB 0 = 3648 from rfl, eT]; omega))

/-- The parts of `scratch` below the lanes (but frame 3) a tree keeps. -/
theorem topW_keepLow (hn32 : p.n ≤ 32) {S AU : Addr} {tt : Nat} (htk : (tt + 1) * p.n ≤ 1120)
    (hA : Region.Disjoint ⟨AU, tsl p⟩ ⟨S, Layout.oSigTmp⟩) {o l : Nat} (h₀ : 1008 ≤ o) (h₁ : o + l ≤ 3136)
    (h₂ : o + l ≤ 1408 ∨ 1536 ≤ o) :
    ∀ r ∈ subW p S AU ++ [⟨at' S (rootAt p.n tt), p.n⟩], Region.Disjoint ⟨at' S o, l⟩ r := by
  intro r hr
  simp only [subW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩) | rfl
  · exact work_disj S h₀ (by omega)
  · exact disj_scr S (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl]; omega)
      (by omega) (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl]; omega)
  · exact disj_scr S (by rw [show Layout.oN = 12480 from rfl]; omega) (by omega)
      (by rw [show Layout.oN = 12480 from rfl, show Layout.nodeSlots = 520 from rfl]; omega)
  · exact disj_scr S (by rw [show Layout.oRoots = 29120 from rfl]; omega) (by omega)
      (by rw [show Layout.oRoots = 29120 from rfl]; omega)
  · exact (hA.sub_right (Offset.sub_base S (by rw [show Layout.oSigTmp = 30144 from rfl]; omega))).symm
  · exact disj_scr S (by rw [laneA_eq]; omega) (by omega) (by rw [laneA_eq]; omega)
  · exact disj_scr S (by simp only [rootAt]; rw [show Layout.laneB 0 = 3648 from rfl]; omega) (by omega)
      (by simp only [rootAt]; rw [show Layout.laneB 0 = 3648 from rfl]; rw [Nat.add_mul, Nat.one_mul] at htk; omega)

/-- The state after tree `tt`, from what its parts leave. -/
theorem tree_post {S SG : Addr} {pk a16 sk : List Byte} {ix : Nat → Nat} {t₀ t t₁ t₃ t₈ : State}
    (M : MC p S SG t₀) {tt : Nat} (htt : tt < p.k) (hI : TL p S SG pk a16 sk ix t₀ tt t) (K : T0 p S SG tt t t₁)
    (P : TopP p S (SG + BitVec.ofNat 64 (tt * tsl p)) pk a16 sk (t₀.gpr .x20).toNat tt (ix tt) t₁ t₃)
    (hk : Keep [.x24, .x10, .x27, .x23, .x9] t₃ t₈) (hm : t₈.mem = t₃.mem)
    (h23 : t₈.gpr .x23 = BitVec.ofNat 64 (tt + 1)) (h24 : t₈.gpr .x24 = SG + BitVec.ofNat 64 ((tt + 1) * tsl p))
    (h27 : t₈.gpr .x27 = BitVec.ofNat 64 ((tt + 1) * 2 ^ p.a)) :
    TL p S SG pk a16 sk ix t₀ (tt + 1) t₈ := by
  have hz := M.hz
  have hn32 := hz.n32
  have hT := tsl_le hn32 M.a14
  have hkt : (tt + 1) * tsl p ≤ p.k * tsl p := Nat.mul_le_mul_right _ htt
  have hkt' : (tt + 1) * tsl p = tt * tsl p + tsl p := Nat.succ_mul _ _
  have htk : (tt + 1) * p.n ≤ 1120 := by have := Nat.mul_le_mul (show tt + 1 ≤ 35 by have := M.k35; omega) hn32; omega
  have hA : Region.Disjoint ⟨SG + BitVec.ofNat 64 (tt * tsl p), tsl p⟩ ⟨S, Layout.oSigTmp⟩ :=
    M.dxs (by omega) (fun _ h => h)
  -- the trees' signatures before `tt`, and the bytes of `scratch` the tree keeps
  have sigK : ∀ {o l : Nat}, o + l ≤ tt * tsl p →
      ∀ r ∈ subW p S (SG + BitVec.ofNat 64 (tt * tsl p)) ++ [⟨at' S (rootAt p.n tt), p.n⟩],
        Region.Disjoint ⟨SG + BitVec.ofNat 64 o, l⟩ r := fun h r hr => by
    rcases topW_low hn32 S _ htk r hr with rfl | hr'
    · exact Offset.disjoint SG (.inl h) (by have := M.Gf; omega) (by have := M.Gf; omega)
    · exact M.dxs (by omega) hr'
  have sigK0 : ∀ {o l : Nat}, o + l ≤ tt * tsl p →
      ∀ r ∈ [(⟨SG + BitVec.ofNat 64 (tt * tsl p), tsl p⟩ : Region)], Region.Disjoint ⟨SG + BitVec.ofNat 64 o, l⟩ r :=
    fun h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint SG (.inl h) (by have := M.Gf; omega) (by have := M.Gf; omega)
  have scrK0 : ∀ {o l : Nat}, o + l ≤ 30144 →
      ∀ r ∈ [(⟨SG + BitVec.ofNat 64 (tt * tsl p), tsl p⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r :=
    fun h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hA.sub_right (Offset.sub_base S (by rw [show Layout.oSigTmp = 30144 from rfl]; exact h))).symm
  refine ⟨fun r hr h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_, h23, h24, h27, by rw [hk.sp, P.sp, K.keep.sp, hI.sp],
    by rw [hk.rd, P.rd, K.keep.rd, hI.rd], by rw [hk.wr, P.wr, K.keep.wr, hI.wr],
    fun r hr => by rw [hk.vcs r hr, P.vcs r hr, K.keep.vcs r hr, hI.vcs r hr], by rw [hm]; exact P.env,
    by rw [hm]; exact P.skat, fun i hi => ?_, fun t' ht' j hj => ?_, fun t' ht' r hr => ?_, fun t' ht' => ?_, ?_⟩
  · rw [hk.gpr r (by revert r; decide), P.cs r hr h₄ h₅ h₇, K.keep.gpr r (by revert r; decide),
      hI.cs r hr h₁ h₂ h₃ h₄ h₅ h₆ h₇]
  · have := M.k35
    rw [hm, readW_frame P.frame (topW_keepLow hn32 htk hA (by rw [show Layout.oFidx = 2048 from rfl]; omega)
        (by rw [show Layout.oFidx = 2048 from rfl]; omega) (.inr (by rw [show Layout.oFidx = 2048 from rfl]; omega))),
      readW_frame K.frame (scrK0 (by rw [show Layout.oFidx = 2048 from rfl]; omega))]
    exact hI.fidx i hi
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
    · have : t' * tsl p + tsl p ≤ tt * tsl p := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht'
      have hj' : t' * tsl p + j + 1 ≤ tt * tsl p := by
        have : p.n ≤ tsl p := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        omega
      rw [hm, byte_frame P.frame (sigK hj'), byte_frame K.frame (sigK0 hj')]
      exact hI.skp t' ht' j hj
    · rw [hm, ← addr_add]; exact P.skp j hj
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
    · have : t' * tsl p + tsl p ≤ tt * tsl p := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht'
      have hrn : t' * tsl p + p.n + r * p.n + p.n ≤ tt * tsl p := by
        have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega); rw [Nat.succ_mul] at this
        simp only [tsl] at *; rw [Nat.add_mul, Nat.one_mul] at *; omega
      rw [hm, bytesAt_frame P.frame (sigK hrn) (by omega), bytesAt_frame K.frame (sigK0 hrn) (by omega)]
      exact hI.auth t' ht' r hr
    · rw [hm, ← addr_add, ← addr_add]; exact P.auth r hr
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
    · have hl := Nat.mul_le_mul_right p.n (show t' + 1 ≤ tt by omega)
      rw [Nat.add_mul, Nat.one_mul] at hl htk
      have eB : Layout.laneB 0 = 3648 := rfl
      rw [hm, bytesAt_frame P.frame (fun r hr => ?_) (by omega), bytesAt_frame K.frame
        (scrK0 (by simp only [rootAt]; rw [eB]; omega)) (by omega)]
      · exact hI.roots t' ht'
      · simp only [subW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
          List.mem_range] at hr
        rcases hr with ((rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩) | rfl
        · exact work_disj S (by simp only [rootAt]; rw [eB]; omega) (by simp only [rootAt]; rw [eB]; omega)
        · exact disj_scr S (by simp only [rootAt]; rw [eB, show Layout.oFrame 3 = 1408 from rfl,
            show Layout.frameLen = 128 from rfl]; omega) (by simp only [rootAt]; rw [eB]; omega)
            (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl]; omega)
        · exact disj_scr S (by simp only [rootAt]; rw [eB, show Layout.oN = 12480 from rfl]; omega)
            (by simp only [rootAt]; rw [eB]; omega)
            (by rw [show Layout.oN = 12480 from rfl, show Layout.nodeSlots = 520 from rfl]; omega)
        · exact disj_scr S (by simp only [rootAt]; rw [eB, show Layout.oRoots = 29120 from rfl]; omega)
            (by simp only [rootAt]; rw [eB]; omega) (by rw [show Layout.oRoots = 29120 from rfl]; omega)
        · exact (hA.sub_right (Offset.sub_base S (by
            simp only [rootAt]; rw [eB, show Layout.oSigTmp = 30144 from rfl]; omega))).symm
        · exact disj_scr S (by simp only [rootAt]; rw [eB, laneA_eq]; omega) (by simp only [rootAt]; rw [eB]; omega)
            (by rw [laneA_eq]; omega)
        · exact disj_scr S (by simp only [rootAt]; rw [Nat.add_mul] at *; omega) (by simp only [rootAt]; rw [eB]; omega)
            (by simp only [rootAt]; rw [eB]; omega)
    · rw [hm]; exact P.root
  · have mem : ∀ {x : Region}, x ∈ treeW p S SG → ∃ r' ∈ treeW p S SG, Region.Sub x r' := fun h => ⟨_, h, fun _ h => h⟩
    have hsub : Region.Sub ⟨SG + BitVec.ofNat 64 (tt * tsl p), tsl p⟩ ⟨SG, p.k * tsl p⟩ := Offset.sub_base SG (by omega)
    rw [hm]
    refine hI.frame.trans ((K.frame.sub fun x hx => ?_).trans (P.frame.sub fun x hx => ?_))
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, by simp, hsub⟩
    · simp only [subW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
        List.mem_range] at hx
      rcases hx with ((rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩) | rfl
      · exact mem (by simp)
      · exact mem (by simp)
      · exact mem (by simp)
      · exact mem (by simp)
      · exact ⟨_, by simp, hsub⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), fun _ h => h⟩
      · exact ⟨⟨at' S (Layout.laneB 0 + p.n + 32), 1120⟩, by simp, Offset.sub S (by simp only [rootAt]; omega)
          (by simp only [rootAt]; rw [Nat.add_mul, Nat.one_mul] at htk; omega)⟩

/-- Tree `tt`. -/
theorem tree_ok (T : Thash4Impl p.n) (name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code).noFrames = true)
    {S SG : Addr} {pk a16 sk : List Byte} {ix : Nat → Nat} {t₀ : State} (M : MC p S SG t₀)
    (hix : ∀ i < p.k, ix i < 2 ^ p.a) {tt : Nat} (htt : tt < p.k) {t : State}
    (hI : TL p S SG pk a16 sk ix t₀ tt t) :
    WP isa (Impl.SlhDsa.AArch64.Fors.treeBody ⟨p.n, p.len⟩ p.a p.k name ln T.code) t fun t' =>
      t'.gpr .x9 = BitVec.ofNat 64 (tt + 1) - BitVec.ofNat 64 p.k ∧ TL p S SG pk a16 sk ix t₀ (tt + 1) t' := by
  have hz := M.hz
  have hn32 := hz.n32
  have hT := tsl_le hn32 M.a14
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) M.a14
  have h14 : (2 : Nat) ^ 14 = 16384 := rfl
  have htk : (tt + 1) * p.n ≤ 1120 := by have := Nat.mul_le_mul (show tt + 1 ≤ 35 by have := M.k35; omega) hn32; omega
  unfold Impl.SlhDsa.AArch64.Fors.treeBody
  refine WP.seq (WP.mono (tree0_ok M hix htt hI) fun t₁ ⟨C, H0, K⟩ => ?_)
  have kp₁ : t₁.gpr .x20 = t₀.gpr .x20 := by
    rw [K.keep.get .x20, hI.cs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  have h23₁ : t₁.gpr .x23 = BitVec.ofNat 64 tt := by rw [K.keep.get .x23, hI.x23]
  refine WP.seq (WP.mono (subs_ok T name ln hL hLf C H0) fun t₂ H2 => ?_)
  refine WP.seq (WP.mono (top_ok hL hLf C h23₁ htk H2) fun t₃ P => ?_)
  rw [kp₁] at P
  simp only [List.cons_append]
  have hT' : (p.a + 1) * p.n ≤ 480 := hT
  refine wp_addi (by omega) fun t₄ u₄ => movV_ok (by omega) fun t₅ o₅ e₅ => wp_addr fun t₆ u₆ =>
    wp_addi (by decide) fun t₇ u₇ => wp_subi (by have := M.k35; omega) fun t₈ u₈ => WP.block_nil ?_
  have hk : Keep [.x24, .x10, .x27, .x23, .x9] t₃ t₈ :=
    (((((upK u₄).trans o₅.keep).trans (upK u₆)).trans (upK u₇)).trans (upK u₈)).mono (by simp)
  have hm : t₈.mem = t₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, o₅.mem, u₄.mem]
  have c₃ : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → t₃.gpr r = t₁.gpr r := P.cs
  have h23 : t₈.gpr .x23 = BitVec.ofNat 64 (tt + 1) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), o₅.get .x23, u₄.other _ (by decide),
      c₃ _ (by decide) (by decide) (by decide) (by decide), h23₁, BitVec.ofNat_add_ofNat]
  refine ⟨by rw [u₈.gpr, ← u₈.other .x23 (by decide), h23], tree_post M htt hI K P hk hm h23 ?_ ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), o₅.get .x24, u₄.gpr,
      c₃ _ (by decide) (by decide) (by decide) (by decide), C.x24, addr_add, Nat.succ_mul]
    congr 2; simp only [tsl, Nat.succ_mul]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, o₅.get .x27, e₅, u₄.other _ (by decide),
      c₃ _ (by decide) (by decide) (by decide) (by decide), C.x27, BitVec.ofNat_add_ofNat, Nat.succ_mul]

/-- The loop of trees' invariant at the measure `m` (the passes left). -/
abbrev TI (p : Params) (S SG : Addr) (pk a16 sk : List Byte) (ix : Nat → Nat) (t₀ : State) (m : Nat)
    (t : State) : Prop :=
  ∃ tt, tt + m = p.k ∧ 0 < m ∧ TL p S SG pk a16 sk ix t₀ tt t

/-- A pass of the loop of trees. -/
theorem tree_step (T : Thash4Impl p.n) (name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code).noFrames = true)
    {S SG : Addr} {pk a16 sk : List Byte} {ix : Nat → Nat} {t₀ : State} (M : MC p S SG t₀)
    (hix : ∀ i < p.k, ix i < 2 ^ p.a) :
    ∀ m t, TI p S SG pk a16 sk ix t₀ m t →
      WP isa (Impl.SlhDsa.AArch64.Fors.treeBody ⟨p.n, p.len⟩ p.a p.k name ln T.code) t fun t' =>
        isa.eval (.nonzero .x .x9) t' = some (decide (m ≠ 1)) ∧
        (decide (m ≠ 1) = false → TL p S SG pk a16 sk ix t₀ p.k t') ∧
        (decide (m ≠ 1) = true → m - 1 < m ∧ TI p S SG pk a16 sk ix t₀ (m - 1) t') := by
  intro m t ⟨tt, ht, hm, hI⟩
  refine WP.mono (tree_ok T name ln hL hLf M hix (by omega) hI) fun t' ⟨h9, hI'⟩ => ?_
  have := M.k35
  refine ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · show some (t'.read .x .x9 != 0) = _
    rw [State.read, BitVec.setWidth_eq, h9, nz_sub (by omega) (by omega)]
    congr 1; simp only [decide_eq_decide]; omega
  · have : m = 1 := by simpa using hc
    rw [show p.k = tt + 1 by omega]; exact hI'
  · simp only [decide_eq_true_eq] at hc
    exact ⟨by omega, tt + 1, by omega, by omega, hI'⟩

/-- The loop of the `k` trees. -/
theorem trees_ok (T : Thash4Impl p.n) (name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code).noFrames = true)
    {S SG : Addr} {pk a16 sk : List Byte} {ix : Nat → Nat} {t₀ : State} (M : MC p S SG t₀)
    (hix : ∀ i < p.k, ix i < 2 ^ p.a) (hI : TL p S SG pk a16 sk ix t₀ 0 t₀) :
    WP isa (.loop (Impl.SlhDsa.AArch64.Fors.treeBody ⟨p.n, p.len⟩ p.a p.k name ln T.code) (.nonzero .x .x9)) t₀
      (TL p S SG pk a16 sk ix t₀ p.k) :=
  wpLoop (fun m => decide (m ≠ 1)) (fun m => m - 1) (tree_step T name ln hL hLf M hix) p.k
    ⟨0, by omega, M.k1, hI⟩

end VG.Proof.SlhDsa.AArch64.Fors
