module

-- separate module: the subtrees of a FORS tree, a stage of `forsSign`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsSubH
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, the subtrees of a tree

`subtreeBody` (`Impl/SlhDsa/AArch64/Fors.lean`), a subtree: its leaves, its
heights, the next subtree (`sub_ok`); its pass of the loop (`sub_step`), and
the loop of the `2^(a-s)` subtrees of tree `t` (`subs_ok`): the private key
value of the tree's index and its authentication path's nodes below height
`s` in the signature, the subtree roots at `oRoots`. As x86-64's
`ForsSub.lean`, with the counters in `x25` and `x26`.
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
open VG.Proof.SlhDsa.X86_64.Fors (node sib acc acc_succ)

variable {p : Params}

/-- What the tree's loops need of their entry state `t₀`: the tree `tt`
of index `idx`, its signature at `AU`, `dA` bytes into the signature buffer
`⟨SG, L⟩`. -/
structure SC (p : Params) (S SG AU : Addr) (L dA tt idx : Nat) (t₀ : State) : Prop where
  hz : Sz p
  a6 : 6 ≤ p.a
  a14 : p.a ≤ 14
  x19 : t₀.gpr .x19 = S
  kp : (t₀.gpr .x20).toNat < 2 ^ 32
  x21 : t₀.gpr .x21 = BitVec.ofNat 64 idx
  idx : idx < 2 ^ p.a
  x24 : t₀.gpr .x24 = AU
  x27 : t₀.gpr .x27 = BitVec.ofNat 64 (tt * 2 ^ p.a)
  w : (⟨S, 65536⟩ : Region) ∈ t₀.wr
  wG : (⟨SG, L⟩ : Region) ∈ t₀.wr
  AU : AU = SG + BitVec.ofNat 64 dA
  dA : dA + (p.a + 1) * p.n ≤ L
  Gf : SG.toNat + L ≤ 2 ^ 64
  fit : S.toNat + 65536 ≤ 2 ^ 64
  Gd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩
  tt : (tt + 1) * 2 ^ p.a < 2 ^ 32

/-- What the subtrees change. -/
abbrev subW (p : Params) (S AU : Addr) : List Region :=
  [⟨S, workUsed⟩, ⟨at' S (Layout.oFrame 3), Layout.frameLen⟩, ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩,
    ⟨at' S Layout.oRoots, 1024⟩, ⟨AU, (p.a + 1) * p.n⟩] ++
  (List.range 4).map fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)

/-- The state before subtree `u` of tree `tt`, from the entry state `t₀` of
the loop (the tree's signature zeroed). -/
structure ST (p : Params) (S AU : Addr) (pk a16 sk : List Byte) (kp tt idx : Nat)
    (t₀ : State) (u : Nat) (t : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → t.gpr r = t₀.gpr r
  x25 : t.gpr .x25 = BitVec.ofNat 64 (u * 2 ^ s p.a)
  sp : t.sp = t₀.sp
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  vcs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (t₀.v r).extractLsb' 0 64
  env : Env p t.mem S pk a16
  skat : SkAt p t.mem S sk
  skp : ∀ j < p.n, t.mem (AU + BitVec.ofNat 64 j) =
    if idx < u * 2 ^ s p.a then skv p pk a16 sk kp (tt * 2 ^ p.a + idx) j else 0
  auth : ∀ r < s p.a, bytesAt t.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
    acc p sk pk a16 kp tt idx (s p.a) p.a r u
  high : ∀ r, s p.a ≤ r → r < p.a → bytesAt t.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
    toByte 0 p.n
  roots : ∀ u' < u, bytesAt t.mem (at' S (Layout.oRoots + u' * p.n)) p.n =
    node p sk pk a16 kp (tt * 2 ^ (p.a - s p.a) + u') (s p.a)
  frame : Frame (subW p S AU) t₀.mem t.mem

theorem mul_pow_div (u : Nat) {s r : Nat} (h : r ≤ s) : u * 2 ^ s / 2 ^ r = u * 2 ^ (s - r) := by
  rw [show 2 ^ s = 2 ^ (s - r) * 2 ^ r by rw [← Nat.pow_add, Nat.sub_add_cancel h], ← Nat.mul_assoc,
    Nat.mul_div_cancel _ (Nat.two_pow_pos r)]

theorem pres_ne (r : Reg) (hr : r ∈ preserved) (h : r ≠ .x25) : r ∉ [.x25, .x10, .x9] := by
  revert r; decide

theorem xor_zero8 (x : Byte) : x ^^^ (0 : Byte) = x := BitVec.xor_zero

/-- What `levels` changes is below `oSigTmp`. -/
theorem lc_low (hn32 : p.n ≤ 32) (S : Addr) {c : Nat} (hc : (c + 8) * p.n ≤ 32 * Layout.nodeSlots) :
    ∀ r ∈ levelsChanges p S (at' S Layout.oN) c, Region.Sub r ⟨S, Layout.oSigTmp⟩ := by
  intro r hr
  simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rw [show Layout.nodeSlots = 520 from rfl] at hc
  rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
  · exact Offset.sub_base S (by rw [laneA_eq, show Layout.oSigTmp = 30144 from rfl]; omega)
  · exact Region.sub_prefix (by rw [show workUsed = 1008 from rfl, show Layout.oSigTmp = 30144 from rfl]; omega)
  · exact Offset.sub_base S (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl,
      show Layout.oSigTmp = 30144 from rfl]; omega)
  · exact Offset.sub_base S (by rw [show Layout.oN = 12480 from rfl, show Layout.oSigTmp = 30144 from rfl]; omega)

/-- What the loop of leaves changes, but `⟨AU, n⟩`, is below `oSigTmp`. -/
theorem lw_low (hn32 : p.n ≤ 32) (S AU : Addr) :
    ∀ r ∈ loopW p.n S AU, r = ⟨AU, p.n⟩ ∨ Region.Sub r ⟨S, Layout.oSigTmp⟩ := by
  intro r hr
  simp only [loopW, laneRs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hr
  rcases hr with (rfl | rfl | rfl) | ⟨k, hk, rfl⟩
  · exact .inr (Region.sub_prefix (by rw [show workUsed = 1008 from rfl, show Layout.oSigTmp = 30144 from rfl]; omega))
  · exact .inr (Offset.sub_base S (by rw [show Layout.oN = 12480 from rfl, show Layout.nodeSlots = 520 from rfl, show Layout.oSigTmp = 30144 from rfl]; omega))
  · exact .inl rfl
  · exact .inr (Offset.sub_base S (by rw [laneA_eq, show Layout.oSigTmp = 30144 from rfl]; omega))

/-- The work in `scratch` at `o` the work at `0` misses. -/
theorem work_disj (S : Addr) {o l : Nat} (h₀ : 1008 ≤ o) (h₁ : o + l ≤ 65536) :
    Region.Disjoint ⟨at' S o, l⟩ ⟨S, workUsed⟩ := by
  have := disj_scr S (o := o) (l := l) (o' := 0) (l' := workUsed) (.inr (by rw [show workUsed = 1008 from rfl]; omega))
    h₁ (by rw [show workUsed = 1008 from rfl]; omega)
  rwa [show at' S 0 = S from (scr0 S).symm] at this

/-- The parts of `scratch` a subtree's heights keep. -/
theorem subH_keep (hn32 : p.n ≤ 32) {S AU : Addr} {u : Nat}
    (hA : Region.Disjoint ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩ ⟨S, Layout.oSigTmp⟩) (hu : u < 32)
    {o l : Nat} (h₀ : 1008 ≤ o) (h₁ : o + l ≤ 30144) (h₂ : o + l ≤ 1408 ∨ 1536 ≤ o)
    (h₃ : ∀ k < 4, o + l ≤ Layout.laneA k + p.n + 16 ∨ Layout.laneA k + 3 * p.n + 32 ≤ o)
    (h₄ : o + l ≤ Layout.oN ∨ Layout.oN + (2 ^ s p.a + 8) * p.n ≤ o)
    (h₅ : o + l ≤ Layout.oRoots + u * p.n ∨ Layout.oRoots + u * p.n + p.n ≤ o) :
    ∀ r ∈ levelsChanges p S (at' S Layout.oN) (2 ^ s p.a) ++
      [⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩, ⟨at' S (Layout.oVar 3 0), 32⟩,
        ⟨at' S (Layout.oRoots + u * 2 ^ s p.a / 2 ^ s p.a * p.n), p.n⟩], Region.Disjoint ⟨at' S o, l⟩ r := by
  have hP := pow_s_le p.a
  have hcnt : (2 ^ s p.a + 8) * p.n ≤ 520 * 32 := Nat.mul_le_mul (by omega) hn32
  have hRn : u * p.n + p.n ≤ 1024 := by
    have := Nat.mul_le_mul (show u + 1 ≤ 32 by omega) hn32; rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hR : u * 2 ^ s p.a / 2 ^ s p.a = u := Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  have eN : Layout.oN = 12480 := rfl
  have eR : Layout.oRoots = 29120 := rfl
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
    · exact disj_scr S (by rcases h₃ k hk with h | h <;> [left; right] <;> omega) (by omega)
        (by rw [laneA_eq]; omega)
    · exact work_disj S h₀ (by omega)
    · exact disj_scr S (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl]; omega)
        (by omega) (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl]; omega)
    · exact disj_scr S (by omega) (by omega) (by rw [eN] at h₄ ⊢; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hA.sub_right (Offset.sub_base S (by rw [show Layout.oSigTmp = 30144 from rfl]; omega))).symm
    · exact disj_scr S (by rw [var3_eq]; omega) (by omega) (by rw [var3_eq]; omega)
    · rw [hR]; exact disj_scr S (by omega) (by omega) (by rw [eR]; omega)

/-- The parts of `scratch` the loop of leaves keeps. -/
theorem loopW_keep (hn32 : p.n ≤ 32) {S AU : Addr} (hAUd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩)
    {o l : Nat} (h₀ : 1008 ≤ o) (h₁ : o + l ≤ 30144)
    (h₃ : ∀ k < 4, o + l ≤ Layout.laneA k + p.n + 16 ∨ Layout.laneA k + 2 * p.n + 32 ≤ o)
    (h₄ : o + l ≤ Layout.oN ∨ Layout.oRoots ≤ o) : ∀ r ∈ loopW p.n S AU, Region.Disjoint ⟨at' S o, l⟩ r := by
  have eN : Layout.oN = 12480 := rfl
  have eR : Layout.oRoots = 29120 := rfl
  intro r hr
  simp only [loopW, laneRs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hr
  rcases hr with (rfl | rfl | rfl) | ⟨k, hk, rfl⟩
  · exact work_disj S h₀ (by omega)
  · exact disj_scr S (by rw [eN, show Layout.nodeSlots = 520 from rfl]; rw [eN, eR] at h₄; omega) (by omega)
      (by rw [eN, show Layout.nodeSlots = 520 from rfl]; omega)
  · exact (hAUd.sub_right (Offset.sub_base S (by rw [show Layout.oSigTmp = 30144 from rfl]; omega))).symm
  · exact disj_scr S (by rcases h₃ k hk with h | h <;> [left; right] <;> omega) (by omega)
      (by rw [laneA_eq]; omega)

/-- A subtree. -/
theorem sub_ok (T : Thash4Impl p.n) (name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code).noFrames = true)
    {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte} {t₀ : State}
    (C : SC p S SG AU L dA tt idx t₀) {u : Nat} {t : State} (hu : u < 2 ^ (p.a - s p.a))
    (hI : ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ u t) :
    WP isa (Impl.SlhDsa.AArch64.Fors.subtreeBody ⟨p.n, p.len⟩ p.a name ln T.code) t fun t' =>
      t'.gpr .x9 = BitVec.ofNat 64 ((u + 1) * 2 ^ s p.a) - BitVec.ofNat 64 (2 ^ p.a) ∧
      ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ (u + 1) t' := by
  have hz := C.hz
  have hn32 := hz.n32
  have hn16 := hz.n16
  have hs6 := s_ge C.a6
  have hsa := s_le p.a
  have hs9 := s_le9 p.a
  have hP := pow_s_le p.a
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) C.a14
  have h14 : (2 : Nat) ^ 14 = 16384 := rfl
  have hidx32 : idx < 2 ^ 32 := by have := C.idx; omega
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel hsa]
  have hu1' : u * 2 ^ s p.a + 2 ^ s p.a ≤ 2 ^ p.a := by
    rw [← Nat.succ_mul, ← hUs]; exact Nat.mul_le_mul_right _ hu
  have has : p.a - s p.a ≤ 5 := by have := C.a14; simp only [Impl.SlhDsa.AArch64.Fors.s]; omega
  have hU32 : 2 ^ (p.a - s p.a) ≤ 32 :=
    calc 2 ^ (p.a - s p.a) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) has
      _ = 32 := rfl
  have htt := C.tt
  rw [Nat.succ_mul] at htt
  have hX : tt * 2 ^ p.a + u * 2 ^ s p.a + 2 ^ s p.a < 2 ^ 32 := by omega
  have han : (p.a + 1) * p.n = p.n + p.a * p.n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hsn : s p.a * p.n ≤ p.a * p.n := Nat.mul_le_mul_right _ hsa
  have hAN : (p.a + 1) * p.n ≤ 15 * 32 := Nat.mul_le_mul (by have := C.a14; omega) hn32
  have hdAn := C.dA
  have eN : Layout.oN = 12480 := rfl
  have eR : Layout.oRoots = 29120 := rfl
  have eT : Layout.oSigTmp = 30144 := rfl
  have eSk : Layout.oSkSeed = 1664 := rfl
  have hcnt : (2 ^ s p.a + 8) * p.n ≤ 32 * Layout.nodeSlots := by
    rw [show Layout.nodeSlots = 520 from rfl]; have := Nat.mul_le_mul (show 2 ^ s p.a + 8 ≤ 520 by omega) hn32; omega
  -- the signature against `scratch`
  have hAUo : ∀ o, AU + BitVec.ofNat 64 o = at' SG (dA + o) := fun o => by
    rw [C.AU, at', BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have dXs : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n → ∀ {R : Region}, Region.Sub R ⟨S, Layout.oSigTmp⟩ →
      Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ R := fun {o l} h {R} hR =>
    (C.Gd.sub_left (by rw [hAUo]; exact Offset.sub_base SG (by omega))).sub_right hR
  have dA0 : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n → p.n ≤ o →
      Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ ⟨AU, p.n⟩ := fun {o l} h h' => by
    have := Offset.disjoint AU (d := o) (n := l) (e := 0) (k := p.n) (.inr (by omega)) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have hAUd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩ := by
    have := dXs (o := 0) (l := p.n) (by omega) (fun _ h => h); rwa [BitVec.add_zero] at this
  have hout : InRegions t₀.wr AU p.n :=
    ⟨_, C.wG, by rw [C.AU]; exact Offset.contains_base SG (by omega) (by have := C.Gf; omega)⟩
  -- the registers of `t`
  have g : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → t.gpr r = t₀.gpr r := hI.cs
  unfold Impl.SlhDsa.AArch64.Fors.subtreeBody
  refine WP.seq (wp_movz fun t₁ u₁ => WP.block_nil ?_)
  have g₁ : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → t₁.gpr r = t₀.gpr r := fun r hr h₁ h₂ h₃ => by
    rw [u₁.other r h₂, g r hr h₁ h₂ h₃]
  have kp₁ : t₁.gpr .x20 = t₀.gpr .x20 := g₁ _ (by decide) (by decide) (by decide) (by decide)
  have hdv4 : 2 ^ s p.a ∣ tt * 2 ^ p.a := Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hsa) _
  -- the leaves
  refine WP.seq (WP.mono (leaves_ok hz T name (by omega) (S := S) (AU := AU) (V4 := tt * 2 ^ p.a)
    (U2 := u * 2 ^ s p.a) (idx := idx) (pk := pk) (a16 := a16) (sk := sk)
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), C.x19]) (by rw [kp₁]; exact C.kp)
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), C.x21]) hidx32
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), C.x24])
    (by rw [u₁.other _ (by decide), hI.x25]) (by rw [u₁.gpr]; rfl)
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), C.x27])
    (by rw [u₁.wr, hI.wr]; exact C.w) C.fit hX (by rw [u₁.wr, hI.wr]; exact hout) hAUd
    (by rw [u₁.mem]; exact hI.env) (by rw [u₁.mem]; exact hI.skat)) fun t₂ L₂ => ?_)
  rw [kp₁] at L₂
  have g₂ : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → t₂.gpr r = t₀.gpr r := fun r hr h₁ h₂ h₃ => by
    rw [L₂.cs r hr h₂ h₃, g₁ r hr h₁ h₂ h₃]
  have kp₂ : t₂.gpr .x20 = t₀.gpr .x20 := g₂ _ (by decide) (by decide) (by decide) (by decide)
  have h25₂ : t₂.gpr .x25 = BitVec.ofNat 64 (u * 2 ^ s p.a) := by
    rw [L₂.cs _ (by decide) (by decide) (by decide), u₁.other _ (by decide), hI.x25]
  have hw₂ : t₂.wr = t₀.wr := by rw [L₂.wr, u₁.wr, hI.wr]
  -- the heights
  refine WP.seq (WP.mono (subH_ok hz hL hLf (S := S) (SG := SG) (AU := AU) (L := L) (dA := dA)
    (U2 := u * 2 ^ s p.a) (V4 := tt * 2 ^ p.a) (idx := idx) (pk := pk) (a16 := a16) (sk := sk)
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), C.x19]) (by rw [kp₂]; exact C.kp)
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), C.x21]) hidx32
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), C.x24]) h25₂
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), C.x27]) (by omega)
    (by rw [hw₂]; exact C.w) (by rw [hw₂]; exact C.wG) C.AU (by omega) C.Gf C.fit C.Gd (by omega) L₂.env
    hdv4 (Nat.dvd_mul_left _ _) (by rw [Nat.mul_div_cancel _ (Nat.two_pow_pos _)]; omega)
    (fun i hi => by rw [kp₂]; exact L₂.nodes i hi)) fun t₃ H => ?_)
  rw [kp₂] at H
  -- the next subtree
  simp only [List.singleton_append]
  refine wp_addi (by omega) fun t₄ u₄ => movV_ok (by omega) fun t₅ o₅ e₅ => wp_subr fun t₆ u₆ => WP.block_nil ?_
  have k₆ : Keep [.x25, .x10, .x9] t₃ t₆ := (((upK u₄).trans o₅.keep).trans (upK u₆)).mono (by simp)
  have hm₆ : t₆.mem = t₃.mem := by rw [u₆.mem, o₅.mem, u₄.mem]
  have h25₄ : t₄.gpr .x25 = BitVec.ofNat 64 ((u + 1) * 2 ^ s p.a) := by
    rw [u₄.gpr, H.cs _ (by decide) (by decide), h25₂, BitVec.ofNat_add_ofNat, Nat.succ_mul]
  have h25₆ : t₆.gpr .x25 = BitVec.ofNat 64 ((u + 1) * 2 ^ s p.a) := by
    rw [u₆.other _ (by decide), o₅.get .x25, h25₄]
  -- the parts of memory
  have hRn : ∀ u' < 32, u' * p.n + p.n ≤ 1024 := fun u' hu' => by
    have := Nat.mul_le_mul (show u' + 1 ≤ 32 by omega) hn32; rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hR : u * 2 ^ s p.a / 2 ^ s p.a = u := Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  have hsHP : ∀ r ∈ levelsChanges p S (at' S Layout.oN) (2 ^ s p.a) ++
      [⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩, ⟨at' S (Layout.oVar 3 0), 32⟩,
        ⟨at' S (Layout.oRoots + u * 2 ^ s p.a / 2 ^ s p.a * p.n), p.n⟩],
      r = ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩ ∨ Region.Sub r ⟨S, Layout.oSigTmp⟩ := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact .inr (lc_low hn32 S hcnt r hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (Offset.sub_base S (by rw [var3_eq, eT]; omega))
      · exact .inr (Offset.sub_base S (by rw [hR, eR, eT]; have := hRn u (by omega); omega))
  -- the signature from `t` to `t₆`
  have sig₁ : ∀ o l, o + l ≤ (p.a + 1) * p.n → (o + l ≤ p.n ∨ p.n + s p.a * p.n ≤ o) →
      bytesAt t₆.mem (AU + BitVec.ofNat 64 o) l = bytesAt t₂.mem (AU + BitVec.ofNat 64 o) l := fun o l h₀ h => by
    rw [hm₆]
    refine bytesAt_frame H.frame (fun r hr => ?_) (by omega)
    rcases hsHP r hr with rfl | hr'
    · exact Offset.disjoint AU (d := o) (n := l) (e := p.n) (k := s p.a * p.n) (by omega) (by omega) (by omega)
    · exact dXs h₀ hr'
  have sig₂ : ∀ o l, o + l ≤ (p.a + 1) * p.n → p.n ≤ o →
      bytesAt t₂.mem (AU + BitVec.ofNat 64 o) l = bytesAt t.mem (AU + BitVec.ofNat 64 o) l := fun o l h₀ h => by
    rw [bytesAt_frame L₂.frame (fun r hr => ?_) (by omega), u₁.mem]
    rcases lw_low hn32 S AU r hr with rfl | hr'
    · exact dA0 h₀ h
    · exact dXs h₀ hr'
  refine ⟨by rw [u₆.gpr, o₅.get .x25, h25₄, e₅], ?_⟩
  have hdisA : Region.Disjoint ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩ ⟨S, Layout.oSigTmp⟩ :=
    dXs (o := p.n) (by omega) (fun _ h => h)
  have hA2 : ∀ r, AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n) = AU + BitVec.ofNat 64 (p.n + r * p.n) :=
    fun r => by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hByte : ∀ j < p.n, t₆.mem (AU + BitVec.ofNat 64 j) = t₂.mem (AU + BitVec.ofNat 64 j) := fun j hj => by
    rw [hm₆]
    refine byte_frame H.frame fun r hr => ?_
    rcases hsHP r hr with rfl | hr'
    · exact Offset.disjoint AU (d := j) (n := 1) (e := p.n) (k := s p.a * p.n) (.inl (by omega)) (by omega) (by omega)
    · exact dXs (by omega) hr'
  have hsk₆ : SkAt p t₆.mem S sk := by
    rw [hm₆]
    exact sk_keep L₂.skat H.frame (subH_keep hn32 hdisA (by omega) (by rw [eSk]; omega) (by rw [eSk]; omega) (.inr (by rw [eSk]; omega))
      (fun k hk => .inl (by rw [eSk, laneA_eq]; omega)) (.inl (by rw [eSk, eN]; omega))
      (.inl (by rw [eSk, eR]; omega))) (by omega)
  refine ⟨fun r hr h₁ h₂ h₃ => by rw [k₆.gpr r (pres_ne r hr h₁), H.cs r hr h₃, g₂ r hr h₁ h₂ h₃], h25₆,
    by rw [k₆.sp, H.sp, L₂.sp, u₁.sp, hI.sp], by rw [k₆.rd, H.rd, L₂.rd, u₁.rd, hI.rd],
    by rw [k₆.wr, H.wr, hw₂], fun r hr => by rw [k₆.vcs r hr, H.vcs r hr, L₂.vcs r hr, u₁.v, hI.vcs r hr],
    by rw [hm₆]; exact H.env, hsk₆, fun j hj => ?_, fun r hr => ?_, fun r h₁ h₂ => ?_, fun u' hu' => ?_, ?_⟩
  · -- the private key value
    rw [hByte j hj, L₂.skb j hj, u₁.mem, hI.skp j hj, Nat.succ_mul]
    by_cases e₁ : u * 2 ^ s p.a ≤ idx ∧ idx < u * 2 ^ s p.a + 2 ^ s p.a
    · rw [ite_eq_left e₁, ite_eq_right (by omega), ite_eq_left (by omega), xor_zero8]
    · rw [ite_eq_right e₁]
      by_cases e₂ : idx < u * 2 ^ s p.a
      · rw [ite_eq_left e₂, ite_eq_left (by omega)]
      · rw [ite_eq_right e₂, ite_eq_right (by omega)]
  · -- the path below height `s`
    have hrn : p.n + r * p.n + p.n ≤ (p.a + 1) * p.n := by
      have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega); rw [Nat.succ_mul] at this; omega
    rw [hm₆, H.auth r hr, hA2, sig₂ _ _ hrn (by omega), ← hA2, hI.auth r hr, mul_pow_div u (Nat.le_of_lt hr),
      mul_pow_div tt (by omega)]
    exact acc_succ p sk pk a16 _ hn32 tt idx (s p.a) p.a r u
  · -- the path above it, still zero
    have hrn : p.n + r * p.n + p.n ≤ (p.a + 1) * p.n := by
      have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega); rw [Nat.succ_mul] at this; omega
    have hsr : s p.a * p.n ≤ r * p.n := Nat.mul_le_mul_right _ h₁
    rw [hA2, sig₁ _ _ hrn (.inr (by omega)), sig₂ _ _ hrn (by omega), ← hA2]
    exact hI.high r h₁ h₂
  · -- the subtree roots
    have hun := hRn u' (by omega)
    by_cases e : u' = u
    · subst e
      rw [hm₆]
      have hroot := H.root
      rw [hR, div_add_dvd hdv4, hR, mul_pow_div tt hsa] at hroot
      exact hroot
    · have hlt : u' < u := by omega
      have hul : u' * p.n + p.n ≤ u * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
      rw [hm₆, bytesAt_frame H.frame (subH_keep hn32 hdisA (by omega) (by rw [eR]; omega) (by rw [eR]; omega) (.inr (by rw [eR]; omega))
          (fun k hk => .inr (by rw [eR, laneA_eq]; omega)) (.inr (by rw [eR, eN]; rw [show Layout.nodeSlots = 520 from rfl] at hcnt; omega))
          (.inl (by omega))) (by omega),
        bytesAt_frame L₂.frame (loopW_keep hn32 hAUd (by rw [eR]; omega) (by rw [eR]; omega)
          (fun k hk => .inr (by rw [eR, laneA_eq]; omega)) (.inr (by omega))) (by omega), u₁.mem]
      exact hI.roots u' hlt
  · -- the frame
    have mem : ∀ {x : Region}, x ∈ subW p S AU → ∃ r' ∈ subW p S AU, Region.Sub x r' := fun h => ⟨_, h, fun _ h => h⟩
    have tail : ∀ k < 4, (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region) ∈ subW p S AU :=
      fun k hk => List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
    have F₂ : Frame (subW p S AU) t₁.mem t₂.mem := L₂.frame.sub fun x hx => by
      simp only [loopW, laneRs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
        List.mem_range] at hx
      rcases hx with (rfl | rfl | rfl) | ⟨k, hk, rfl⟩
      · exact mem (by simp)
      · exact mem (by simp)
      · exact ⟨⟨AU, (p.a + 1) * p.n⟩, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨_, tail k hk, Region.sub_prefix (by omega)⟩
    have F₃ : Frame (subW p S AU) t₂.mem t₃.mem := H.frame.sub fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
        · exact ⟨_, tail k hk, fun _ h => h⟩
        · exact mem (by simp)
        · exact mem (by simp)
        · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp, Region.sub_prefix (by omega)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨⟨AU, (p.a + 1) * p.n⟩, by simp, Offset.sub_base AU (by omega)⟩
        · exact ⟨⟨at' S (Layout.oFrame 3), Layout.frameLen⟩, by simp, Offset.sub S
            (by rw [var3_eq, show Layout.oFrame 3 = 1408 from rfl]; omega)
            (by rw [var3_eq, show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl]; omega)⟩
        · exact ⟨⟨at' S Layout.oRoots, 1024⟩, by simp, Offset.sub S (by omega)
            (by rw [hR]; have := hRn u (by omega); omega)⟩
    rw [u₁.mem] at F₂
    rw [hm₆]
    exact hI.frame.trans (F₂.trans F₃)

/-- The loop of subtrees' invariant at the measure `m` (the passes left). -/
abbrev SI (p : Params) (S AU : Addr) (pk a16 sk : List Byte) (kp tt idx : Nat) (t₀ : State) (m : Nat)
    (t : State) : Prop :=
  ∃ u, u + m = 2 ^ (p.a - s p.a) ∧ 0 < m ∧ ST p S AU pk a16 sk kp tt idx t₀ u t

/-- A pass of the loop of subtrees. -/
theorem sub_step (T : Thash4Impl p.n) (name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code).noFrames = true)
    {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte} {t₀ : State}
    (C : SC p S SG AU L dA tt idx t₀) :
    ∀ m t, SI p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ m t →
      WP isa (Impl.SlhDsa.AArch64.Fors.subtreeBody ⟨p.n, p.len⟩ p.a name ln T.code) t fun t' =>
        isa.eval (.nonzero .x .x9) t' = some (decide (m ≠ 1)) ∧
        (decide (m ≠ 1) = false → ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ (2 ^ (p.a - s p.a)) t') ∧
        (decide (m ≠ 1) = true → m - 1 < m ∧ SI p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ (m - 1) t') := by
  intro m t ⟨u, hu, hm, hI⟩
  refine WP.mono (sub_ok T name ln hL hLf C (by omega) hI) fun t' ⟨h9, hI'⟩ => ?_
  have hsa := s_le p.a
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel hsa]
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) C.a14
  have h14 : (2 : Nat) ^ 14 = 16384 := rfl
  have hle : (u + 1) * 2 ^ s p.a ≤ 2 ^ p.a := by rw [← hUs]; exact Nat.mul_le_mul_right _ (by omega)
  have hiff : (u + 1) * 2 ^ s p.a ≠ 2 ^ p.a ↔ m ≠ 1 := by
    rw [← hUs]
    constructor
    · intro h e; apply h; rw [show u + 1 = 2 ^ (p.a - s p.a) by omega]
    · intro h e; have := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) e; omega
  refine ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · show some (t'.read .x .x9 != 0) = _
    rw [State.read, BitVec.setWidth_eq, h9, nz_sub (by omega) (by omega)]
    congr 1; simp only [decide_eq_decide]; exact hiff
  · have : m = 1 := by simpa using hc
    rw [show 2 ^ (p.a - s p.a) = u + 1 by omega]; exact hI'
  · simp only [decide_eq_true_eq] at hc
    exact ⟨by omega, u + 1, by omega, by omega, hI'⟩

/-- The loop of the `2^(a-s)` subtrees of a tree. -/
theorem subs_ok (T : Thash4Impl p.n) (name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name T.code).noFrames = true)
    {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte} {t₀ : State}
    (C : SC p S SG AU L dA tt idx t₀) (hI : ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ 0 t₀) :
    WP isa (.loop (Impl.SlhDsa.AArch64.Fors.subtreeBody ⟨p.n, p.len⟩ p.a name ln T.code) (.nonzero .x .x9)) t₀
      (ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ (2 ^ (p.a - s p.a))) :=
  wpLoop (fun m => decide (m ≠ 1)) (fun m => m - 1) (sub_step T name ln hL hLf C)
    (2 ^ (p.a - s p.a)) ⟨0, by omega, Nat.two_pow_pos _, hI⟩

end VG.Proof.SlhDsa.AArch64.Fors
