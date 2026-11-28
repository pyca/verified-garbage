module

-- separate module: the loop of trees, which `ForsFront` does not rebuild when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsTop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `forsSign`, the loop of trees

`treeBody`, tree `t`: its signature and its root (`tree_ok`), and the loop of
the `k` trees (`trees_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout copyWords)
open VG.Impl.SlhDsa.X86_64.Fors
open VG.Proof.SlhDsa (fld)

/-- What the trees need of the state `t₀` before them. -/
structure MC (p : Params) (stack : Nat) (S SG : Addr) (t₀ : State) : Prop where
  hf : p.family = .shake
  hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32
  a6 : 6 ≤ p.a
  a14 : p.a ≤ 14
  k1 : 1 ≤ p.k
  k35 : p.k ≤ 35
  bx : t₀.gpr .rbx = S
  kp : (t₀.gpr .r12).toNat < 2 ^ 32
  w : (⟨S, 2 ^ 16⟩ : Region) ∈ t₀.wr
  wG : (⟨SG, p.k * ((p.a + 1) * p.n)⟩ : Region) ∈ t₀.wr
  Gf : SG.toNat + p.k * ((p.a + 1) * p.n) ≤ 2 ^ 64
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  stk : (below (t₀.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩
  Gd : Region.Disjoint ⟨SG, p.k * ((p.a + 1) * p.n)⟩ ⟨S, Layout.oSigTmp⟩
  Gs : Region.Disjoint ⟨SG, p.k * ((p.a + 1) * p.n)⟩ (below (t₀.gpr .rsp) stack)

/-- What the trees change. -/
abbrev treeW (p : Params) (S SG sp : Addr) (stack : Nat) : List Region :=
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (Layout.oVar 2 0), 40⟩, ⟨at' S (Layout.oFrame 4), 128⟩,
    ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, ⟨at' S Layout.oRoots, 1024⟩,
    ⟨at' S (Layout.laneB 0 + p.n + 32), 1120⟩, ⟨SG, p.k * ((p.a + 1) * p.n)⟩, below sp stack] ++
  (List.range 4).map fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)

/-- The state before tree `tt`, from the state `t₀` before the trees, the
trees' indices `ix`. -/
structure TL (p : Params) (stack : Nat) (S SG : Addr) (pkSeed a16 skSeed : List Byte) (ix : Nat → Nat)
    (t₀ : State) (tt : Nat) (t : State) : Prop where
  cs : ∀ r ∈ calleeSaved, r ≠ .r13 → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mx : t.mxcsr.extractLsb' 6 10 = t₀.mxcsr.extractLsb' 6 10
  env : Env p t.mem S pkSeed a16
  sk : SkAt p t.mem S skSeed
  v0 : t.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt
  v1 : t.mem.readW (at' S (Layout.oVar 2 1)) 64 = SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))
  v4 : t.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 (tt * 2 ^ p.a)
  fidx : ∀ i < p.k, t.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (ix i)
  skp : ∀ t' < tt, ∀ j < p.n, t.mem (SG + BitVec.ofNat 64 (t' * ((p.a + 1) * p.n) + j)) =
    skv p pkSeed a16 skSeed (t₀.gpr .r12).toNat (t' * 2 ^ p.a + ix t') j
  auth : ∀ t' < tt, ∀ r < p.a, bytesAt t.mem (SG + BitVec.ofNat 64 (t' * ((p.a + 1) * p.n) + p.n + r * p.n)) p.n =
    node p skSeed pkSeed a16 (t₀.gpr .r12).toNat (t' * 2 ^ (p.a - r) + sib (ix t') r) r
  roots : ∀ t' < tt, bytesAt t.mem (at' S (Layout.laneB 0 + p.n + 32 + t' * p.n)) p.n =
    node p skSeed pkSeed a16 (t₀.gpr .r12).toNat t' p.a
  frame : Frame (treeW p S SG (t₀.gpr .rsp) stack) t₀.mem t.mem

theorem mem_cs {r : Reg} (h : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The state after tree `tt`, from what its parts leave. -/
theorem tree_post {p : Params} {stack : Nat} {S SG : Addr} {pkSeed a16 skSeed : List Byte} {ix : Nat → Nat}
    {t₀ : State} (M : MC p stack S SG t₀) {tt : Nat} (htt : tt < p.k) {t t₁ t₂ t₃ t₄ : State}
    (hI : TL p stack S SG pkSeed a16 skSeed ix t₀ tt t)
    (g₁ : ∀ g, g ≠ .rax → g ≠ .r13 → g ≠ .rsi → t₁.gpr g = t.gpr g) (r₁ : t₁.rd = t.rd) (w₁ : t₁.wr = t.wr)
    (mx₁ : t₁.mxcsr = t.mxcsr)
    (f₁ : Frame [⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩, ⟨at' S (Layout.oVar 2 2), 8⟩] t.mem t₁.mem)
    (P : TopP p stack S (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))) pkSeed a16 skSeed (t₁.gpr .r12).toNat tt (ix tt)
      t₁ t₂ t₃)
    (g₄ : ∀ g, g ≠ .rax → t₄.gpr g = t₃.gpr g) (r₄ : t₄.rd = t₃.rd) (w₄ : t₄.wr = t₃.wr) (mx₄ : t₄.mxcsr = t₃.mxcsr)
    (v0₄ : t₄.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 (tt + 1))
    (v1₄ : t₄.mem.readW (at' S (Layout.oVar 2 1)) 64 =
      SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)) + BitVec.ofNat 64 ((p.a + 1) * p.n))
    (v4₄ : t₄.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 (tt * 2 ^ p.a + 2 ^ p.a))
    (f₄ : Frame [⟨at' S (Layout.oVar 2 0), 16⟩, ⟨at' S (Layout.oVar 2 4), 8⟩] t₃.mem t₄.mem) :
    TL p stack S SG pkSeed a16 skSeed ix t₀ (tt + 1) t₄ := by
  have hn := M.hn
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hkt : (tt + 1) * ((p.a + 1) * p.n) ≤ p.k * ((p.a + 1) * p.n) := Nat.mul_le_mul_right _ htt
  have hkt' : (tt + 1) * ((p.a + 1) * p.n) = tt * ((p.a + 1) * p.n) + (p.a + 1) * p.n := Nat.succ_mul _ _
  have htk : (tt + 1) * p.n ≤ 1120 := by
    have := Nat.mul_le_mul (show tt + 1 ≤ 35 by omega_using [htt, M.k35]) hn32; omega_using [this]
  have hsubA : Region.Sub ⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩
      ⟨SG, p.k * ((p.a + 1) * p.n)⟩ := Offset.sub_base SG (by omega_using [hkt, hkt'])
  have kA : ∀ q, q < 31648 → (q < 2720 ∨ 2728 ≤ q) → t₁.mem (at' S q) = t.mem (at' S q) := fun q hq h =>
    keepS f₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((M.Gd.sub_left hsubA).sub_right (Offset.sub_base S (by
          rw [show Layout.oSigTmp = 31648 from rfl]; omega_using [hq]))).symm
      · exact dS S (by rw [oVar2]; omega_using [h]) (by omega_using [hq]) (by rw [oVar2]; omega_using [])
  have hcs₁ : ∀ r ∈ calleeSaved, r ≠ .r13 → t₁.gpr r = t₀.gpr r := fun r hr h13 => by
    obtain ⟨h0, _, _, h3, _⟩ := mem_cs hr
    rw [g₁ _ h0 h13 h3, hI.cs r hr h13]
  -- the parts of memory each step keeps
  have eB : Layout.laneB 0 = 3808 := rfl
  have htn : tt * p.n + p.n ≤ 1120 := by rw [← Nat.succ_mul]; exact htk
  have hsp₁ : t₁.gpr .rsp = t₀.gpr .rsp := hcs₁ _ (by simp [calleeSaved]) (by decide)
  have dP : ∀ (X : Region), (∀ R, Region.Sub R ⟨S, Layout.oSigTmp⟩ → X.Disjoint R) → X.Disjoint (below (t₀.gpr .rsp) stack) →
      X.Disjoint ⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩ →
      ∀ r ∈ subW p S (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))) (t₁.gpr .rsp) stack ++
        [⟨at' S (Layout.laneB 0 + p.n + 32 + tt * p.n), p.n⟩], X.Disjoint r := fun X hlow hstk hau r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hr
    rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩) | rfl
    · exact hlow _ (Region.sub_prefix (by decide))
    · exact hlow _ (Offset.sub_base S (by decide))
    · exact hlow _ (Offset.sub_base S (by decide))
    · exact hlow _ (Offset.sub_base S (by decide))
    · exact hlow _ (Offset.sub_base S (by decide))
    · exact hlow _ (Offset.sub_base S (by decide))
    · exact hau
    · rw [hsp₁]; exact hstk
    · exact hlow _ (Offset.sub_base S (by rw [laneA_eq, show Layout.oSigTmp = 31648 from rfl]; omega_using [hk, hn32]))
    · exact hlow _ (Offset.sub_base S (by rw [eB, show Layout.oSigTmp = 31648 from rfl]; omega_using [htn, hn32]))
  have dE : ∀ (X : Region), (∀ R, Region.Sub R ⟨S, Layout.oSigTmp⟩ → X.Disjoint R) →
      ∀ r ∈ [(⟨at' S (Layout.oVar 2 0), 16⟩ : Region), ⟨at' S (Layout.oVar 2 4), 8⟩], X.Disjoint r := fun X hlow r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hlow _ (Offset.sub_base S (by decide))
  have dA : ∀ (X : Region), (∀ R, Region.Sub R ⟨S, Layout.oSigTmp⟩ → X.Disjoint R) →
      X.Disjoint ⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩ →
      ∀ r ∈ [(⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩ : Region), ⟨at' S (Layout.oVar 2 2), 8⟩],
        X.Disjoint r := fun X hlow hau r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hau
    · exact hlow _ (Offset.sub_base S (by decide))
  -- scratch below `oSigTmp`, outside what the tree changes
  have keepG : ∀ o l, o + l ≤ p.k * ((p.a + 1) * p.n) →
      (o + l ≤ tt * ((p.a + 1) * p.n) ∨ (tt + 1) * ((p.a + 1) * p.n) ≤ o) →
      bytesAt t₄.mem (SG + BitVec.ofNat 64 o) l = bytesAt t.mem (SG + BitVec.ofNat 64 o) l := fun o l h₀ h => by
    have hX : Region.Sub ⟨SG + BitVec.ofNat 64 o, l⟩ ⟨SG, p.k * ((p.a + 1) * p.n)⟩ := Offset.sub_base SG h₀
    have hlow : ∀ R, Region.Sub R ⟨S, Layout.oSigTmp⟩ → Region.Disjoint ⟨SG + BitVec.ofNat 64 o, l⟩ R :=
      fun R hR => (M.Gd.sub_left hX).sub_right hR
    have hau : Region.Disjoint ⟨SG + BitVec.ofNat 64 o, l⟩ ⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩ :=
      Offset.disjoint SG (by omega_using [h, hkt']) (by have := M.Gf; omega_using [h₀, this])
        (by have := M.Gf; omega_using [hkt, hkt', this])
    have hl : l ≤ 2 ^ 64 := by have := M.Gf; omega_using [h₀, this]
    rw [bytesAt_frame f₄ (dE _ hlow) hl, bytesAt_frame P.frame (dP _ hlow (M.Gs.sub_left hX) hau) hl,
      bytesAt_frame f₁ (dA _ hlow hau) hl]
  have keepS4 : ∀ q, q < 31648 → 1600 ≤ q → (q < 2368 ∨ 2400 ≤ q) → (q < 2704 ∨ 2744 ≤ q) → (q < 2912 ∨ 3040 ≤ q) →
      (q < 12640 ∨ 30304 ≤ q) → (∀ k < 4, q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 16 + (16 + 2 * p.n) ≤ q) →
      (q < 3808 + p.n + 32 + tt * p.n ∨ 3808 + p.n + 32 + tt * p.n + p.n ≤ q) →
      t₄.mem (at' S q) = t.mem (at' S q) := fun q hq h₀ h₁ h₂ h₃ h₄ h₅ h₆ => by
    have hlow : ∀ R, Region.Sub R ⟨S, Layout.oSigTmp⟩ → Region.Disjoint ⟨at' S q, 1⟩ R → Region.Disjoint ⟨at' S q, 1⟩ R :=
      fun _ _ h => h
    rw [keepS f₄ fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dS S (by rw [oVar2]; omega_using [h₂]) (by omega_using [hq]) (by decide)
        · exact dS S (by rw [oVar2]; omega_using [h₂]) (by omega_using [hq]) (by decide),
      keepS P.frame fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hr
        rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩) | rfl
        · exact Offset.disjoint_base S h₀ (by omega_using [hq])
        · exact dS S (by omega_using [h₁]) (by omega_using [hq]) (by decide)
        · exact dS S (by rw [oVar2]; omega_using [h₂]) (by omega_using [hq]) (by decide)
        · exact dS S (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega_using [h₃]) (by omega_using [hq]) (by decide)
        · exact dS S (by rw [show Layout.oN = 12640 from rfl, show Layout.nodeSlots = 520 from rfl]; omega_using [h₄])
            (by omega_using [hq]) (by decide)
        · exact dS S (by rw [show Layout.oRoots = 29280 from rfl]; omega_using [h₄]) (by omega_using [hq]) (by decide)
        · exact ((M.Gd.sub_left hsubA).sub_right (Offset.sub_base S (by
            rw [show Layout.oSigTmp = 31648 from rfl]; omega_using [hq]))).symm
        · rw [hsp₁]; exact (M.stk.sub_right (Levels.sub_scr S (by omega_using [hq]))).symm
        · exact dS S (h₅ k hk |>.imp (by omega_using []) id) (by omega_using [hq]) (by rw [laneA_eq]; omega_using [hk, hn32])
        · exact dS S (by rw [eB]; omega_using [h₆]) (by omega_using [hq]) (by rw [eB]; omega_using [htn, hn32]),
      kA q hq (by omega_using [h₂])]
  have hkp₁ : t₁.gpr .r12 = t₀.gpr .r12 := hcs₁ _ (by simp [calleeSaved]) (by decide)
  have endG : ∀ o l, o + l ≤ p.k * ((p.a + 1) * p.n) →
      bytesAt t₄.mem (SG + BitVec.ofNat 64 o) l = bytesAt t₃.mem (SG + BitVec.ofNat 64 o) l := fun o l h₀ =>
    bytesAt_frame f₄ (dE _ fun R hR => (M.Gd.sub_left (Offset.sub_base SG h₀)).sub_right hR)
      (by have := M.Gf; omega_using [h₀, this])
  have bytesB : ∀ {m m' : Mem} {x : Addr}, bytesAt m' x 1 = bytesAt m x 1 → m' x = m x := fun h => by
    simpa [bytesAt] using h
  refine ⟨fun r hr h13 => ?_, by rw [r₄, P.fix.rd, r₁, hI.rd], by rw [w₄, P.fix.wr, w₁, hI.wr],
    by rw [mx₄, P.fix.mx, mx₁, hI.mx], ?_, ?_, v0₄, by rw [v1₄, Levels.add_add, ← hkt'],
    by rw [v4₄, Nat.succ_mul], fun i hi => ?_, fun t' ht' j hj => ?_, fun t' ht' r hr => ?_, fun t' ht' => ?_, ?_⟩
  · obtain ⟨h0, _⟩ := mem_cs hr
    rw [g₄ _ h0, P.fix.cs r hr, hcs₁ r hr h13]
  · refine env_bytes hn32 P.env fun q hq => keepS f₄ fun r hr => ?_
    simp only [EnvB] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact dS S (by rw [oVar2]; omega_using [hq]) (by omega_using [hq]) (by decide)
  · refine sk_bytes P.sk fun q h₁ h₂ => keepS f₄ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact dS S (by rw [oVar2]; omega_using [h₁]) (by omega_using [h₂, hn32]) (by decide)
  · rw [← hI.fidx i hi]
    exact Mem.readW_congr fun j hj => by
      rw [Levels.add_add]
      exact keepS4 _ (by rw [show Layout.oFidx = 31328 from rfl]; omega_using [hi, hj, M.k35])
        (by rw [show Layout.oFidx = 31328 from rfl]; omega_using []) (.inr (by rw [show Layout.oFidx = 31328 from rfl]; omega_using []))
        (.inr (by rw [show Layout.oFidx = 31328 from rfl]; omega_using []))
        (.inr (by rw [show Layout.oFidx = 31328 from rfl]; omega_using []))
        (.inr (by rw [show Layout.oFidx = 31328 from rfl]; omega_using []))
        (fun k hk => .inr (by rw [show Layout.oFidx = 31328 from rfl, laneA_eq]; omega_using [hk, hn32]))
        (.inr (by rw [show Layout.oFidx = 31328 from rfl]; omega_using [htn, hn32]))
  · by_cases e : t' = tt
    · subst e
      have := Nat.le_mul_of_pos_left p.n (show 0 < p.a + 1 by omega_using [])
      rw [bytesB (endG _ 1 (by omega_using [hj, hkt, hkt', this])), ← Levels.add_add, P.skp j hj, hkp₁]
    · have hlt : t' < tt := by omega_using [ht', e]
      have hle : (t' + 1) * ((p.a + 1) * p.n) ≤ tt * ((p.a + 1) * p.n) := Nat.mul_le_mul_right _ hlt
      have h1' : (t' + 1) * ((p.a + 1) * p.n) = t' * ((p.a + 1) * p.n) + (p.a + 1) * p.n := Nat.succ_mul _ _
      have := Nat.le_mul_of_pos_left p.n (show 0 < p.a + 1 by omega_using [])
      rw [bytesB (keepG _ 1 (by omega_using [hj, hle, h1', hkt, hkt', this]) (.inl (by omega_using [hj, hle, h1', this])))]
      exact hI.skp t' hlt j hj
  · have hrn : p.n + r * p.n + p.n ≤ (p.a + 1) * p.n := by
      have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega_using [hr]); rw [Nat.succ_mul] at this
      rw [Nat.add_mul, Nat.one_mul]; omega_using [this]
    by_cases e : t' = tt
    · subst e
      rw [endG _ _ (by omega_using [hrn, hkt, hkt']), show t' * ((p.a + 1) * p.n) + p.n + r * p.n =
        t' * ((p.a + 1) * p.n) + (p.n + r * p.n) by omega_using [], ← Levels.add_add, ← Levels.add_add, P.auth r hr, hkp₁]
    · have hlt : t' < tt := by omega_using [ht', e]
      have hle : (t' + 1) * ((p.a + 1) * p.n) ≤ tt * ((p.a + 1) * p.n) := Nat.mul_le_mul_right _ hlt
      have h1' : (t' + 1) * ((p.a + 1) * p.n) = t' * ((p.a + 1) * p.n) + (p.a + 1) * p.n := Nat.succ_mul _ _
      rw [keepG _ _ (by omega_using [hrn, hle, h1', hkt, hkt']) (.inl (by omega_using [hrn, hle, h1']))]
      exact hI.auth t' hlt r hr
  · have eB' : Layout.laneB 0 = 3808 := rfl
    by_cases e : t' = tt
    · subst e
      rw [← hkp₁, ← P.root]
      refine bytesAt_ext fun i hi => ?_
      rw [Levels.add_add]
      refine keepS f₄ fun r hr => ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dS S (by rw [oVar2, eB']; omega_using [hi]) (by rw [eB']; omega_using [htn, hi, hn32]) (by decide)
    · have hlt : t' < tt := by omega_using [ht', e]
      have hle : t' * p.n + p.n ≤ tt * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
      rw [← hI.roots t' hlt]
      refine bytesAt_ext fun i hi => ?_
      rw [Levels.add_add]
      exact keepS4 _ (by rw [eB']; omega_using [htn, hle, hi, hn32]) (by rw [eB']; omega_using [])
        (.inr (by rw [eB']; omega_using [])) (.inr (by rw [eB']; omega_using [])) (.inr (by rw [eB']; omega_using []))
        (.inl (by rw [eB']; omega_using [htn, hle, hi, hn32]))
        (fun k hk => .inr (by rw [laneA_eq, eB']; omega_using [hk, hn32])) (.inl (by rw [eB']; omega_using [hle, hi]))
  · -- the frame
    have mem : ∀ {x : Region}, x ∈ treeW p S SG (t₀.gpr .rsp) stack → ∃ r' ∈ treeW p S SG (t₀.gpr .rsp) stack,
        Region.Sub x r' := fun h => ⟨_, h, fun _ h => h⟩
    have sig : ∃ r' ∈ treeW p S SG (t₀.gpr .rsp) stack,
        Region.Sub ⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩ r' := ⟨_, by simp, hsubA⟩
    refine hI.frame.trans ((f₁.sub fun x hx => ?_).trans ((P.frame.sub fun x hx => ?_).trans (f₄.sub fun x hx => ?_)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact sig
      · exact ⟨⟨at' S (Layout.oVar 2 0), 40⟩, by simp, Offset.sub S (by decide) (by decide)⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hx
      rcases hx with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩) | rfl
      · exact mem (by simp)
      · exact mem (by simp)
      · exact ⟨⟨at' S (Layout.oVar 2 0), 40⟩, by simp, Offset.sub S (by decide) (by decide)⟩
      · exact mem (by simp)
      · exact mem (by simp)
      · exact mem (by simp)
      · exact sig
      · rw [hsp₁]; exact mem (by simp)
      · exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), fun _ h => h⟩
      · exact ⟨⟨at' S (Layout.laneB 0 + p.n + 32), 1120⟩, by simp, Offset.sub S (by omega_using [])
          (by omega_using [htn])⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨⟨at' S (Layout.oVar 2 0), 40⟩, by simp, Offset.sub S (by decide) (by decide)⟩
      · exact ⟨⟨at' S (Layout.oVar 2 0), 40⟩, by simp, Offset.sub S (by decide) (by decide)⟩


/-- Tree `tt`. -/
theorem tree_ok {p : Params} (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG : Addr} {pkSeed a16 skSeed : List Byte} {ix : Nat → Nat} {t₀ : State}
    (M : MC p stack S SG t₀) (hix : ∀ i < p.k, ix i < 2 ^ p.a) {tt : Nat} (htt : tt < p.k) {t : State}
    (hI : TL p stack S SG pkSeed a16 skSeed ix t₀ tt t) :
    WP isa (treeBody ⟨p.n, p.len⟩ p.a p.k name ln T.code) t fun t' =>
      t'.zf = some (decide (tt + 1 = p.k)) ∧ TL p stack S SG pkSeed a16 skSeed ix t₀ (tt + 1) t' := by
  have hn := M.hn
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hAN : (p.a + 1) * p.n ≤ 15 * 32 := Nat.mul_le_mul (by omega_using [M.a14]) hn32
  have hkt : (tt + 1) * ((p.a + 1) * p.n) ≤ p.k * ((p.a + 1) * p.n) := Nat.mul_le_mul_right _ htt
  have hkt' : (tt + 1) * ((p.a + 1) * p.n) = tt * ((p.a + 1) * p.n) + (p.a + 1) * p.n := Nat.succ_mul _ _
  have hbx : t.gpr .rbx = S := by rw [hI.cs _ (by simp [calleeSaved]) (by decide), M.bx]
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [hI.wr]; exact M.w
  have hwG : (⟨SG, p.k * ((p.a + 1) * p.n)⟩ : Region) ∈ t.wr := by rw [hI.wr]; exact M.wG
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) M.a14
  have htt2 : (tt + 1) * 2 ^ p.a < 2 ^ 32 := by
    have := Nat.mul_le_mul (show tt + 1 ≤ 35 by omega_using [htt, M.k35]) h2a; omega_using [this]
  unfold treeBody
  refine WP.seq (WP.mono (treeA_ok (p := p) (S := S) (SG := SG) (L := p.k * ((p.a + 1) * p.n))
    (dA := tt * ((p.a + 1) * p.n)) (tt := tt) (idx := ix tt) hbx hw hwG rfl (by omega_using [hkt, hkt']) M.Gf hn8 hI.v0
    (by omega_using [htt, M.k35]) hI.v1 (hI.fidx tt htt) M.Gd) fun t₁ ⟨g₁, r13₁, r₁, w₁, mx₁, z₁, v2₁, f₁⟩ => ?_)
  have hsubA : Region.Sub ⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩
      ⟨SG, p.k * ((p.a + 1) * p.n)⟩ := Offset.sub_base SG (by omega_using [hkt, hkt'])
  have kA : ∀ q, q < 31648 → (q < 2720 ∨ 2728 ≤ q) → t₁.mem (at' S q) = t.mem (at' S q) := fun q hq h =>
    keepS f₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((M.Gd.sub_left hsubA).sub_right (Offset.sub_base S (by
          rw [show Layout.oSigTmp = 31648 from rfl]; omega_using [hq]))).symm
      · exact dS S (by rw [oVar2]; omega_using [h]) (by omega_using [hq]) (by rw [oVar2]; omega_using [])
  have kAw : ∀ i, i < 9 → i ≠ 2 → t₁.mem.readW (at' S (Layout.oVar 2 i)) 64 = t.mem.readW (at' S (Layout.oVar 2 i)) 64 :=
    fun i hi h2 => Mem.readW_congr fun j hj => by
      rw [Levels.add_add, oVar2]; exact kA _ (by omega_using [hi, hj]) (by omega_using [hi, hj, h2])
  have hcs₁ : ∀ r ∈ calleeSaved, r ≠ .r13 → t₁.gpr r = t₀.gpr r := fun r hr h13 => by
    obtain ⟨h0, _, _, h3, _⟩ := mem_cs hr
    rw [g₁ _ h0 h13 h3, hI.cs r hr h13]
  have hE₁ : Env p t₁.mem S pkSeed a16 := env_bytes hn32 hI.env fun q hq => kA q
    (by simp only [EnvB] at hq; omega_using [hq]) (by simp only [EnvB] at hq; omega_using [hq])
  have hsk₁ : SkAt p t₁.mem S skSeed := sk_bytes hI.sk fun q h₁ h₂ => kA q (by omega_using [h₂, hn32]) (.inr (by omega_using [h₁]))
  have C : SC p stack S SG (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))) (p.k * ((p.a + 1) * p.n))
      (tt * ((p.a + 1) * p.n)) tt (ix tt) t₁ :=
    ⟨M.hf, hn, M.a6, M.a14, by rw [hcs₁ _ (by simp [calleeSaved]) (by decide), M.bx],
      by rw [hcs₁ _ (by simp [calleeSaved]) (by decide)]; exact M.kp, r13₁, hix tt htt,
      by rw [w₁]; exact hw, by rw [w₁]; exact hwG, rfl, by omega_using [hkt, hkt'], M.Gf, M.fit,
      by rw [hcs₁ _ (by simp [calleeSaved]) (by decide)]; exact M.stk, M.Gd,
      by rw [hcs₁ _ (by simp [calleeSaved]) (by decide)]; exact M.Gs, htt2⟩
  have hz : ∀ o, o + p.n ≤ (p.a + 1) * p.n →
      bytesAt t₁.mem (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)) + BitVec.ofNat 64 o) p.n = toByte 0 p.n := fun o ho =>
    bytesAt_eq_of (by simp [toByte]) fun i hi => by
      rw [Levels.add_add, z₁ _ (by omega_using [ho, hi]), toByte_zero]; simp [hi]
  have ST0 : ST p stack S (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))) pkSeed a16 skSeed (t₁.gpr .r12).toNat tt (ix tt)
      t₁ 0 t₁ :=
    ⟨Fix.refl _, hE₁, hsk₁, by rw [kAw 1 (by decide) (by decide), hI.v1], by rw [v2₁, Nat.zero_mul],
      by rw [kAw 4 (by decide) (by decide), hI.v4], fun j hj => by
        have := Nat.le_mul_of_pos_left p.n (show 0 < p.a + 1 by omega_using [])
        rw [ite_eq_right (by omega_using []), z₁ j (by omega_using [hj, this])],
      fun r hr => by
        rw [acc_zero, Levels.add_add (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))), hz _ (by
          have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega_using [hr, s_le p.a]); rw [Nat.succ_mul] at this
          rw [Nat.add_mul, Nat.one_mul]; omega_using [this])],
      fun r _ h₂ => by
        rw [Levels.add_add (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))), hz _ (by
          have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega_using [h₂]); rw [Nat.succ_mul] at this
          rw [Nat.add_mul, Nat.one_mul]; omega_using [this])],
      fun _ h => absurd h (by omega_using []), Frame.refl _ _⟩
  have hU0 : 0 < 2 ^ (p.a - s p.a) := Nat.two_pow_pos _
  refine WP.seq (WP.mono (subs_ok T name ln hst hs63 C (u := 0) hU0 (by omega_using []) ST0) fun t₂ S₂ => ?_)
  have h0₂ : t₂.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt := by
    rw [← hI.v0, ← kAw 0 (by decide) (by decide)]
    exact keepSW S₂.frame fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩
      · exact Offset.disjoint_base S (by rw [oVar2]; omega_using []) (by rw [oVar2]; omega_using [])
      · exact dS S (by rw [oVar2]; omega_using []) (by rw [oVar2]; omega_using []) (by decide)
      · exact dS S (by rw [oVar2, oVar2]; omega_using []) (by rw [oVar2]; omega_using []) (by rw [oVar2]; omega_using [])
      · exact dS S (by rw [oVar2]; decide) (by rw [oVar2]; omega_using []) (by decide)
      · exact dS S (by rw [oVar2]; decide) (by rw [oVar2]; omega_using []) (by decide)
      · exact dS S (by rw [oVar2]; decide) (by rw [oVar2]; omega_using []) (by decide)
      · exact ((M.Gd.sub_left hsubA).sub_right (Offset.sub_base S (by
          rw [oVar2, show Layout.oSigTmp = 31648 from rfl]; omega_using []))).symm
      · rw [hcs₁ _ (by simp [calleeSaved]) (by decide)]
        exact (M.stk.sub_right (Levels.sub_scr S (by rw [oVar2]; omega_using []))).symm
      · exact dS S (by rw [oVar2, laneA_eq]; omega_using []) (by rw [oVar2]; omega_using [])
          (by rw [laneA_eq]; omega_using [hk, hn32])
  have htk : (tt + 1) * p.n ≤ 1120 := by
    have := Nat.mul_le_mul (show tt + 1 ≤ 35 by omega_using [htt, M.k35]) hn32; omega_using [this]
  refine WP.seq (WP.mono (top_ok T name ln hst hs63 C htk S₂ h0₂) fun t₃ P => ?_)
  have hbx₃ : t₃.gpr .rbx = S := by rw [P.fix.cs _ (by simp [calleeSaved]), hcs₁ _ (by simp [calleeSaved]) (by decide), M.bx]
  have hw₃ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₃.wr := by rw [P.fix.wr, w₁]; exact hw
  have h2a31 : 2 ^ p.a < 2 ^ 31 := by have : (2 : Nat) ^ 14 = 16384 := rfl; omega_using [h2a, this]
  refine WP.mono (treeEnd_ok (AU := SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))) (V4 := tt * 2 ^ p.a) (D := (p.a + 1) * p.n) (A := 2 ^ p.a) (K := p.k) hbx₃ hw₃ (by omega_using [hAN])
    h2a31 (by omega_using [M.k35]) (by rw [P.vars 0 (by decide) (by decide) (by decide), h0₂])
    (by rw [P.vars 1 (by decide) (by decide) (by decide), S₂.v1])
    (by rw [P.vars 4 (by decide) (by decide) (by decide), S₂.v4]) (by omega_using [htt, M.k35]))
    fun t₄ ⟨g₄, r₄, w₄, mx₄, v0₄, v1₄, v4₄, z₄, f₄⟩ => ⟨z₄, ?_⟩
  exact tree_post M htt hI g₁ r₁ w₁ mx₁ f₁ P g₄ r₄ w₄ mx₄ v0₄ v1₄ v4₄ f₄

/-- The loop of the trees, from tree `tt` on. -/
theorem trees_ok {p : Params} (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG : Addr} {pkSeed a16 skSeed : List Byte} {ix : Nat → Nat} {t₀ : State}
    (M : MC p stack S SG t₀) (hix : ∀ i < p.k, ix i < 2 ^ p.a) {tt m : Nat} {t : State} (hm : 0 < m) (htm : tt + m = p.k)
    (hI : TL p stack S SG pkSeed a16 skSeed ix t₀ tt t) :
    WP isa (.loop (treeBody ⟨p.n, p.len⟩ p.a p.k name ln T.code) .ne) t
      (TL p stack S SG pkSeed a16 skSeed ix t₀ p.k) := by
  let I : Nat → State → Prop := fun m v => ∃ tt, tt + m = p.k ∧ 0 < m ∧ TL p stack S SG pkSeed a16 skSeed ix t₀ tt v
  refine Levels.wpLoop (I := I) (fun m => decide (1 < m)) (fun m => m - 1) (fun m v ⟨tt, ht, hm, H⟩ => ?_) m ⟨tt, htm, hm, hI⟩
  refine WP.mono (tree_ok T name ln hst hs63 M hix (by omega_using [ht, hm]) H) fun v' ⟨hz, H'⟩ => ?_
  refine ⟨by rw [eval_ne hz]; congr 1; by_cases h : 1 < m <;> simp [h] <;> omega_using [h, ht, hm], fun hc => ?_, fun hc => ?_⟩
  · have := of_decide_eq_false hc
    rw [show p.k = tt + 1 by omega_using [this, ht, hm]]; exact H'
  · have := of_decide_eq_true hc
    exact ⟨by omega_using [this], tt + 1, by omega_using [ht, this], by omega_using [this], H'⟩

end VG.Proof.SlhDsa.X86_64.Fors
