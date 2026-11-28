module

-- separate module: the whole of `forsSign`'s correctness, rebuilt without its constant-time proof's taint checks

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsMain
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTSets
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, the whole function

The prologue (frame 2's saves, the indices, the trees' counters:
`front_ok`), the trees (`ForsMain.lean`), `T_k` of the roots (`pk_ok`,
`ForsFront.lean`) and the restores (`fin_ok`), and so `forsContract`'s
postcondition with the calling convention kept (`fors_wp`, `fors_correct`).
As x86-64's `ForsSign.lean`.
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
open VG.Proof.SlhDsa.X86_64.Fors (node sib index_eq)

variable {p : Params}

theorem As.k2 (h : As p) : p.k * 2 ^ p.a < 2 ^ 32 := by
  obtain ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ := h <;>
    (rw [h₂, h₃]; decide)

theorem sigLen_eq (p : Params) : p.forsSigLen = p.k * tsl p := by
  simp only [Params.forsSigLen, tsl]; rw [Nat.add_comm 1 p.a, Nat.mul_assoc]

/-- What the prologue leaves for the rest, from the entry state `σ`. -/
structure Front (p : Params) (σ : State) (S SG : Addr) (t₀ : State) : Prop where
  M : MC p S SG t₀
  x20 : t₀.gpr .x20 = σ.gpr .x2
  cs : ∀ r ∈ preserved, r ∉ Impl.SlhDsa.AArch64.Fors.saved → t₀.gpr r = σ.gpr r
  sp : t₀.sp = σ.sp
  rd : t₀.rd = σ.rd
  wr : t₀.wr = σ.wr
  vcs : ∀ r ∈ preservedV, (t₀.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64
  saved : ∀ i (h : i < Impl.SlhDsa.AArch64.Fors.saved.length),
    t₀.mem.readW (S + BitVec.ofNat 64 (Layout.oSave 2 0 + 8 * i)) 64 = σ.gpr Impl.SlhDsa.AArch64.Fors.saved[i]
  frame : Frame [⟨at' S (Layout.oSave 2 0), 72⟩, ⟨at' S Layout.oFidx, 8 * p.k⟩] σ.mem t₀.mem

theorem ixv_lt (m : Mem) (S : Addr) (a i : Nat) : ixv m S a i < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The prologue: frame 2's saves, the indices, the trees' counters. -/
theorem front_ok (hA : As p) (hz : Sz p) {σ : State} {S SG : Addr} {pk a16 : List Byte}
    (hS : σ.gpr .x0 = S) (hG : σ.gpr .x1 = SG) (hR : Regions σ S [] ⟨SG, p.forsSigLen⟩)
    (hE : Env p σ.mem S pk a16) (hkp : (σ.gpr .x2).toNat < 2 ^ 32) :
    WP isa (.block (Impl.SlhDsa.AArch64.Fors.pro ++ Impl.SlhDsa.AArch64.Fors.indices p.a p.k ++
        ([.movz .x .x23 0 0, .movz .x .x27 0 0] : List Instr))) σ fun t₀ =>
      Front p σ S SG t₀ ∧ TL p S SG pk a16 (bytesAt σ.mem (at' S Layout.oSkSeed) p.n) (ixv σ.mem S p.a) t₀ 0 t₀ := by
  obtain ⟨-, ha6, ha14, hk1, hk35, hka, -⟩ := hA.facts
  have hn32 := hz.n32
  have hL := sigLen_eq p
  have hwS := regions_scr hR
  have hwG := regions_out hR
  have eS : Layout.oSave 2 0 = 1280 := rfl
  have eF : Layout.oFidx = 2048 := rfl
  have eD : Layout.oDigest = 1792 := rfl
  simp only [Impl.SlhDsa.AArch64.Fors.pro, Impl.SlhDsa.AArch64.saveRegs, Impl.SlhDsa.AArch64.Thash4.mov,
    List.append_assoc, List.cons_append, List.nil_append]
  refine saveRegsAt_ok (o := Layout.oSave 2 0) (b := .x0) (rs := Impl.SlhDsa.AArch64.Fors.saved)
    ⟨by decide, by decide⟩ (by rw [hS]; exact in_scr hwS (by decide)) fun t₁ k₁ sv₁ f₁ => ?_
  rw [hS] at sv₁ f₁
  refine wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_mov fun t₄ u₄ => ?_
  have k₄ : Keep [.x19, .x24, .x20] t₁ t₄ := (((upK u₂).trans (upK u₃)).trans (upK u₄)).mono (by simp)
  have hm₄ : t₄.mem = t₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have h19 : t₄.gpr .x19 = S := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, k₁.get .x0, hS]
  have h24 : t₄.gpr .x24 = SG := by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), k₁.get .x1, hG]
  have h20 : t₄.gpr .x20 = σ.gpr .x2 := by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), k₁.get .x2]
  have hw₄ : t₄.wr = σ.wr := by rw [k₄.wr, k₁.wr]
  refine indices_ok ha14 (by omega) (by omega) h19 (by rw [hw₄]; exact hwS) fun v hv => ?_
  refine wp_movz fun w₁ u₅ => wp_movz fun w₂ u₆ => WP.block_nil ?_
  have k₆ : Keep [.x23, .x27] v w₂ := ((upK u₅).trans (upK u₆)).mono (by simp)
  have hm₆ : w₂.mem = v.mem := by rw [u₆.mem, u₅.mem]
  have g : ∀ r, r ∉ [Reg.x19, .x24, .x20, .x9, .x10, .x23, .x27] → w₂.gpr r = σ.gpr r := fun r hr => by
    rw [k₆.gpr r (notin_of hr), hv.gpr r (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide)),
      k₄.gpr r (notin_of hr), k₁.gpr r (by simp)]
  have h23 : w₂.gpr .x23 = BitVec.ofNat 64 0 := by rw [u₆.other _ (by decide), u₅.gpr]; rfl
  have h27 : w₂.gpr .x27 = BitVec.ofNat 64 0 := by rw [u₆.gpr]; rfl
  have g19 : w₂.gpr .x19 = S := by rw [k₆.get .x19, hv.gpr _ (by decide) (by decide), h19]
  have g24 : w₂.gpr .x24 = SG := by rw [k₆.get .x24, hv.gpr _ (by decide) (by decide), h24]
  have g20 : w₂.gpr .x20 = σ.gpr .x2 := by rw [k₆.get .x20, hv.gpr _ (by decide) (by decide), h20]
  have hw : w₂.wr = σ.wr := by rw [k₆.wr, hv.wr, hw₄]
  have hlow : ∀ {o l : Nat}, (o + l ≤ 1280 ∨ 1352 ≤ o) → (o + l ≤ 2048 ∨ 2048 + 8 * p.k ≤ o) → o + l ≤ 65536 →
      ∀ r ∈ [(⟨at' S (Layout.oSave 2 0), 72⟩ : Region), ⟨at' S Layout.oFidx, 8 * p.k⟩],
        Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ h₃ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_scr S (by rw [eS]; omega) h₃ (by rw [eS]; omega)
    · exact disj_scr S (by rw [eF]; omega) h₃ (by rw [eF]; omega)
  have Fr : Frame [⟨at' S (Layout.oSave 2 0), 72⟩, ⟨at' S Layout.oFidx, 8 * p.k⟩] σ.mem w₂.mem := by
    rw [hm₆]
    refine (f₁.sub fun r hr => ?_).trans ((show Frame _ t₁.mem v.mem by rw [← hm₄]; exact hv.frame).mono
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  have hb : ∀ q, 1352 ≤ q → q < 2048 → t₄.mem (at' S q) = σ.mem (at' S q) := fun q h₁ h₂ => by
    rw [hm₄]
    refine byte_frame f₁ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact disj_scr S (o' := Layout.oSave 2 0) (l' := 8 * Impl.SlhDsa.AArch64.Fors.saved.length)
      (.inr (by rw [eS, show 8 * Impl.SlhDsa.AArch64.Fors.saved.length = 72 from rfl]; omega)) (by omega) (by decide)
  have hix : ∀ i < p.k, ixv t₄.mem S p.a i = ixv σ.mem S p.a i := fun i hi => by
    have : i * p.a / 8 + 3 ≤ 64 := by have := Nat.mul_le_mul_right p.a (show i ≤ p.k by omega); omega
    simp only [ixv]
    rw [hb _ (by rw [eD]; omega) (by rw [eD]; omega), hb _ (by rw [eD]; omega) (by rw [eD]; omega),
      hb _ (by rw [eD]; omega) (by rw [eD]; omega)]
  refine ⟨⟨⟨hz, ha6, ha14, hk1, hk35, hA.k2, g19, by rw [g20]; exact hkp, by rw [hw]; exact hwS,
      by rw [hw, ← hL]; exact hwG, by have := hR.out_fit; simp only at this; rw [← hL]; exact this, hR.scr_fit,
      by rw [← hL]; exact hR.out_scr⟩, g20,
    fun r hr hs => g r (by revert r; decide), by rw [k₆.sp, hv.sp, k₄.sp, k₁.sp], by rw [k₆.rd, hv.rd, k₄.rd, k₁.rd],
    hw, fun r hr => by rw [k₆.vcs r hr, hv.vr, k₄.vcs r hr, k₁.vcs r hr], fun i h => ?_, Fr⟩,
    ⟨fun _ _ _ _ _ _ _ _ _ => rfl, h23, by rw [g24, Nat.zero_mul, BitVec.add_zero], by rw [h27, Nat.zero_mul], rfl, rfl,
      rfl, fun _ _ => rfl, env_keep hn32 hE Fr fun r hr k hk => ⟨hlow (.inr (by rw [laneA_eq]; omega))
        (.inr (by rw [laneA_eq]; omega)) (by rw [laneA_eq]; omega) r hr, hlow (.inr (by rw [laneB_eq]; omega))
        (.inr (by rw [laneB_eq]; omega)) (by rw [laneB_eq]; omega) r hr⟩,
      sk_keep rfl Fr (hlow (.inr (by rw [show Layout.oSkSeed = 1664 from rfl]; omega)) (.inl (by
        rw [show Layout.oSkSeed = 1664 from rfl]; omega)) (by rw [show Layout.oSkSeed = 1664 from rfl]; omega)) (by omega),
      fun i hi => by rw [hm₆, hv.idx i hi, hix i hi], fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩⟩
  rw [hm₆, readW_frame hv.frame fun r hr => ?_, hm₄]
  · exact sv₁ i h
  · simp only [List.mem_singleton] at hr; subst hr
    have : i < 9 := h
    exact disj_scr S (o := Layout.oSave 2 0 + 8 * i) (.inl (by rw [eS, eF]; omega)) (by rw [eS]; omega) (by rw [eF]; omega)

/-! ## The signature, the indices and the public key -/

theorem bytesAt_addA (m : Mem) (A : Addr) (x y : Nat) :
    bytesAt m A (x + y) = bytesAt m A x ++ bytesAt m (A + BitVec.ofNat 64 x) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

/-- The bytes of `c` strings of `L` bytes from `A`. -/
theorem bytesAt_flatA (m : Mem) (A : Addr) (L : Nat) : ∀ c,
    bytesAt m A (c * L) = (List.range c).flatMap fun t => bytesAt m (A + BitVec.ofNat 64 (t * L)) L
  | 0 => by simp [bytesAt]
  | c + 1 => by
    rw [Nat.succ_mul, bytesAt_addA, bytesAt_flatA m A L c, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The signature the trees leave at `SG`: each tree's private key value,
then its authentication path. -/
theorem sig_eq (hn32 : p.n ≤ 32) {m : Mem} {SG : Addr} {md sk pk a16 : List Byte} {kp : Nat}
    (h16 : a16.length = 16) (hkp : kp < 2 ^ 32) {ix : Nat → Nat}
    (hix : ∀ i < p.k, ix i = (base2b md p.a p.k).getD i 0)
    (skp : ∀ t' < p.k, ∀ j < p.n, m (SG + BitVec.ofNat 64 (t' * tsl p + j)) = skv p pk a16 sk kp (t' * 2 ^ p.a + ix t') j)
    (auth : ∀ t' < p.k, ∀ r < p.a, bytesAt m (SG + BitVec.ofNat 64 (t' * tsl p + p.n + r * p.n)) p.n =
      node p sk pk a16 kp (t' * 2 ^ (p.a - r) + sib (ix t') r) r) :
    bytesAt m SG (p.k * tsl p) = forsSign p md sk pk (forsAdrs a16 kp) := by
  rw [bytesAt_flatA, forsSign_eq]
  refine Proof.SlhDsa.flatMap_range_congr fun i hi => ?_
  rw [forsSigPart, ← hix i hi, show tsl p = p.n + p.a * p.n by simp only [tsl]; rw [Nat.add_mul, Nat.one_mul, Nat.add_comm],
    bytesAt_addA m, bytesAt_flatA]
  congr 1
  · rw [forsSkGen, X86_64.Fors.sk_adrs h16 kp hkp]
    refine bytesAt_eq_of (Proof.SlhDsa.prf_length hn32 _ _ _) fun j hj => ?_
    rw [addr_add, show p.n + p.a * p.n = tsl p by simp only [tsl]; rw [Nat.add_mul, Nat.one_mul, Nat.add_comm],
      skp i hi j hj]
    rfl
  · refine Proof.SlhDsa.flatMap_range_congr fun r hr => ?_
    rw [addr_add, addr_add, show p.n + p.a * p.n = tsl p by simp only [tsl]; rw [Nat.add_mul, Nat.one_mul, Nat.add_comm],
      ← Nat.add_assoc]
    exact auth i hi r hr

/-- The indices `ixv` are `base_2b(md, a, k)`. -/
theorem ix_eq (hA : As p) (m : Mem) (S : Addr) : ∀ i < p.k, ixv m S p.a i = (base2b (mdAt p m S) p.a p.k).getD i 0 := by
  obtain ⟨-, ha6, ha14, -, -, -, -⟩ := hA.facts
  intro i hi
  have hlen : (mdAt p m S).length = (p.k * p.a + 7) / 8 := bytesAt_length _ _ _
  have hia : i * p.a + p.a ≤ p.k * p.a := by
    have := Nat.mul_le_mul_right p.a (show i + 1 ≤ p.k by omega); rw [Nat.succ_mul] at this; exact this
  have gd : ∀ j, j < (p.k * p.a + 7) / 8 → ∀ q, q = Layout.oDigest + j →
      (m (at' S q)).toNat = ((mdAt p m S).getD j 0).toNat := fun j hj q hq => by
    rw [mdAt, getD_bytesAt _ _ (show j < p.mdLen from hj), at_add, hq]
  refine (index_eq hlen ha14 hi (gd _ (by omega) _ rfl) (fun h => gd _ (by rw [hlen] at h; exact h) _ (by omega))
    (fun h => gd _ (by rw [hlen] at h; exact h) _ (by omega)) (BitVec.isLt _) (BitVec.isLt _)).symm

theorem T_shake (hz : Sz p) (pk : List Byte) (a : Adrs) (M : List Byte) :
    T p pk a M = Spec.Sha3.shake256 (pk ++ a ++ M) p.n := by
  simp only [T, hz.shake, shakeAdrs]

/-- The roots, `n` bytes each. -/
theorem bytesAt_flatS (m : Mem) (S : Addr) (b n : Nat) :
    ∀ L, bytesAt m (at' S b) (L * n) = (List.range L).flatMap fun i => bytesAt m (at' S (b + i * n)) n
  | 0 => by simp [bytesAt]
  | L + 1 => by
    rw [Nat.add_mul, Nat.one_mul, bytesAt_cat, bytesAt_flatS m S b n L, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

theorem laneTA_mem (S : Addr) {k : Nat} (hk : k < 4) :
    (⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩ : Region) ∈ changes p S := by
  simp only [changes, laneTails, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  exact .inl (.inr ⟨k, hk, .inl rfl⟩)

theorem laneTB_mem (S : Addr) {k : Nat} (hk : k < 4) :
    (⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩ : Region) ∈ changes p S := by
  simp only [changes, laneTails, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  exact .inl (.inr ⟨k, hk, .inr (.inl rfl)⟩)

/-- What `forsSign` changes, from its parts' frames. -/
theorem frame_all (hz : Sz p) (hk35 : p.k ≤ 35) {S SG : Addr} {m₀ m₁ m₂ m₃ : Mem}
    (F₀ : Frame [⟨at' S (Layout.oSave 2 0), 72⟩, ⟨at' S Layout.oFidx, 8 * p.k⟩] m₀ m₁)
    (F₁ : Frame (treeW p S SG) m₁ m₂) (F₂ : Frame (pkW p.n S) m₂ m₃) :
    Frame (changes p S ++ [⟨SG, p.forsSigLen⟩]) m₀ m₃ := by
  have hn32 := hz.n32
  have hL := sigLen_eq p
  have ch : ∀ {r : Region}, r ∈ changes p S → ∃ R ∈ changes p S ++ [⟨SG, p.forsSigLen⟩], Region.Sub r r :=
    fun h => ⟨_, List.mem_append_left _ h, fun _ h => h⟩
  have chs : ∀ {r R : Region}, R ∈ changes p S → Region.Sub r R →
      ∃ R' ∈ changes p S ++ [⟨SG, p.forsSigLen⟩], Region.Sub r R' :=
    fun h h' => ⟨_, List.mem_append_left _ h, h'⟩
  refine (F₀.sub fun r hr => ?_).trans ((F₁.sub fun r hr => ?_).trans (F₂.sub fun r hr => ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact chs (R := ⟨at' S Layout.oVars, 4 * Layout.frameLen⟩) (by simp [changes]) (Offset.sub S (by decide) (by decide))
    · exact chs (R := ⟨at' S Layout.oFidx, 320⟩) (by simp [changes]) (Region.sub_prefix (by omega))
  · simp only [treeW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩
    · exact chs (R := ⟨S, workUsed⟩) (by simp [changes]) (fun _ h => h)
    · exact chs (R := ⟨at' S Layout.oVars, 4 * Layout.frameLen⟩) (by simp [changes]) (Offset.sub S (by decide) (by decide))
    · exact chs (R := ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩) (by simp [changes]) (fun _ h => h)
    · exact chs (R := ⟨at' S Layout.oRoots, 1024⟩) (by simp [changes]) (fun _ h => h)
    · exact chs (laneTB_mem S (k := 0) (by decide)) (Offset.sub S (by omega)
        (by rw [show Layout.laneB 0 = 3648 from rfl, show Layout.strideB = 2208 from rfl]; omega))
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), Region.sub_prefix (by rw [hL])⟩
    · exact chs (laneTA_mem S hk) (Region.sub_prefix (by rw [show Layout.strideA = 128 from rfl]; omega))
  · simp only [pkW, Wots4.t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
    rcases hr with (rfl | ⟨j, hj, rfl⟩ | rfl) | rfl
    · exact chs (laneTB_mem S (k := 0) (by decide)) (Region.sub_prefix (by
        rw [show Layout.strideB = 2208 from rfl]; omega))
    · exact chs (laneTB_mem S hj) (by
        simp only [Layout.laneB, Layout.oB, Layout.strideB]; exact Offset.sub S (by omega) (by omega))
    · exact chs (R := ⟨S, workUsed⟩) (by simp [changes]) (fun _ h => h)
    · exact chs (R := ⟨at' S Layout.oMsg, 64⟩) (by simp [changes]) (Region.sub_prefix (by omega))

/-- What `pkFors` changes is below `oSigTmp`, apart from frame 2 and the lanes' `PK.seed` and `a16`. -/
theorem pkW_low (hz : Sz p) (S : Addr) :
    ∀ r ∈ pkW p.n S, Region.Sub r ⟨S, Layout.oSigTmp⟩ ∧ Region.Disjoint ⟨at' S (Layout.oSave 2 0), 72⟩ r ∧
      ∀ k < 4, Region.Disjoint ⟨at' S (Layout.laneA k), p.n + 16⟩ r ∧
        Region.Disjoint ⟨at' S (Layout.laneB k), p.n + 16⟩ r := by
  have hn32 := hz.n32
  have eT : Layout.oSigTmp = 30144 := rfl
  have eS : Layout.oSave 2 0 = 1280 := rfl
  have eM : Layout.oMsg = 1984 := rfl
  intro r hr
  simp only [pkW, Wots4.t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
  rcases hr with (rfl | ⟨j, hj, rfl⟩ | rfl) | rfl
  · rw [show Layout.laneB 0 = 3648 from rfl]
    refine ⟨Offset.sub_base S (by rw [eT]; omega), disj_scr S (by rw [eS]; omega) (by rw [eS]; omega) (by omega),
      fun k hk => ⟨disj_scr S (by rw [laneA_eq]; omega) (by rw [laneA_eq]; omega) (by omega), ?_⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact disj_scr S (by rw [laneB_eq]; omega) (by rw [laneB_eq]; omega) (by omega)
    · exact disj_scr S (by rw [laneB_eq]; omega) (by rw [laneB_eq]; omega) (by omega)
  · simp only [Layout.oB, Layout.strideB]
    refine ⟨Offset.sub_base S (by rw [eT]; omega), disj_scr S (by rw [eS]; omega) (by rw [eS]; omega) (by omega),
      fun k hk => ⟨disj_scr S (by rw [laneA_eq]; omega) (by rw [laneA_eq]; omega) (by omega), ?_⟩⟩
    rw [laneB_eq]
    rcases Nat.lt_or_ge k j with h | h
    · exact disj_scr S (.inl (by have := Nat.mul_le_mul_left 2208 (show k + 1 ≤ j by omega); omega)) (by omega) (by omega)
    · rcases Nat.lt_or_ge j k with h' | h'
      · exact disj_scr S (.inr (by have := Nat.mul_le_mul_left 2208 (show j + 1 ≤ k by omega); omega)) (by omega)
          (by omega)
      · obtain rfl : k = j := by omega
        exact disj_scr S (.inl (by omega)) (by omega) (by omega)
  · refine ⟨Region.sub_prefix (by rw [show workUsed = 1008 from rfl, eT]; omega), ?_, fun k hk => ⟨?_, ?_⟩⟩
    · exact work_disj S (by rw [eS]; omega) (by rw [eS]; omega)
    · exact work_disj S (by rw [laneA_eq]; omega) (by rw [laneA_eq]; omega)
    · exact work_disj S (by rw [laneB_eq]; omega) (by rw [laneB_eq]; omega)
  · refine ⟨Offset.sub_base S (by rw [eM, eT]; omega), disj_scr S (by rw [eS, eM]; omega) (by rw [eS]; omega)
      (by rw [eM]; omega), fun k hk => ⟨disj_scr S (by rw [laneA_eq, eM]; omega) (by rw [laneA_eq]; omega)
      (by rw [eM]; omega), disj_scr S (by rw [laneB_eq, eM]; omega) (by rw [laneB_eq]; omega) (by rw [eM]; omega)⟩⟩

/-- `T_k` of the roots, and the restores. -/
theorem fin_ok (hA : As p) (hz : Sz p) (T : Thash4Impl p.n) (name : String) {σ : State} {S SG : Addr}
    {pk a16 : List Byte} (hS : σ.gpr .x0 = S) (hG : σ.gpr .x1 = SG) (hE : Env p σ.mem S pk a16) {t₀ t₁ : State}
    (F : Front p σ S SG t₀)
    (H : TL p S SG pk a16 (bytesAt σ.mem (at' S Layout.oSkSeed) p.n) (ixv σ.mem S p.a) t₀ p.k t₁) :
    WP isa (.seq (Impl.SlhDsa.AArch64.Fors.pkFors ⟨p.n, p.len⟩ p.k name T.code)
      (.block (Impl.SlhDsa.AArch64.restoreRegs 2 Impl.SlhDsa.AArch64.Fors.saved))) t₁ fun s' =>
      abiPreserved σ s' ∧ (forsContract p).post σ s' := by
  obtain ⟨-, ha6, ha14, hk1, hk35, -, hk2⟩ := hA.facts
  have hn32 := hz.n32
  have M := F.M
  have hL := sigLen_eq p
  have c₁ := H.cs
  have h19 : t₁.gpr .x19 = S := by
    rw [c₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), M.x19]
  have h20 : t₁.gpr .x20 = σ.gpr .x2 := by
    rw [c₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), F.x20]
  have hw₁ : (⟨S, 65536⟩ : Region) ∈ t₁.wr := by rw [H.wr]; exact M.w
  have hkp : (σ.gpr .x2).toNat < 2 ^ 32 := by rw [← F.x20]; exact M.kp
  have hknB : p.k * p.n + p.n + 32 ≤ Layout.strideB := by
    have := Nat.mul_le_mul hk35 hn32; rw [show Layout.strideB = 2208 from rfl]; omega
  refine WP.seq (pk_ok hz T name hknB (by omega) h19 (by rw [h20]; exact hkp) hw₁ M.fit
    fun t' r' w' sp' cs' vcs' msg' f' => ?_)
  have h19' : t'.gpr .x19 = S := by rw [cs' _ (by decide) (by decide), h19]
  rw [show Impl.SlhDsa.AArch64.restoreRegs 2 Impl.SlhDsa.AArch64.Fors.saved =
      Impl.SlhDsa.AArch64.restoreRegsAt 1280 Impl.SlhDsa.AArch64.Fors.saved from rfl,
    ← List.append_nil (Impl.SlhDsa.AArch64.restoreRegsAt _ _)]
  refine restoreRegsAt_ok (by decide) (by decide)
    (by rw [h19', r', w']; exact in_scr' hw₁ (by decide)) fun t'' o'' g'' => MlKem.AArch64.wp_nil ?_
  -- the saved registers
  have hsv : ∀ i (h : i < Impl.SlhDsa.AArch64.Fors.saved.length),
      t'.mem.readW (S + BitVec.ofNat 64 (1280 + 8 * i)) 64 = σ.gpr Impl.SlhDsa.AArch64.Fors.saved[i] := fun i h => by
    have hi : i < 9 := h
    have hd : ∀ r ∈ treeW p S SG, Region.Disjoint ⟨at' S (1280 + 8 * i), 8⟩ r := fun r hr => by
      simp only [treeW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
        List.mem_range] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩
      · exact work_disj S (by omega) (by omega)
      · exact disj_scr S (by rw [show Layout.oFrame 3 = 1408 from rfl]; omega) (by omega)
          (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl]; omega)
      · exact disj_scr S (by rw [show Layout.oN = 12480 from rfl]; omega) (by omega)
          (by rw [show Layout.oN = 12480 from rfl, show Layout.nodeSlots = 520 from rfl]; omega)
      · exact disj_scr S (by rw [show Layout.oRoots = 29120 from rfl]; omega) (by omega)
          (by rw [show Layout.oRoots = 29120 from rfl]; omega)
      · exact disj_scr S (by rw [show Layout.laneB 0 = 3648 from rfl]; omega) (by omega)
          (by rw [show Layout.laneB 0 = 3648 from rfl]; omega)
      · exact (M.dxs (o := 0) (l := p.k * tsl p) (by omega) (Offset.sub_base S (by rw [show Layout.oSigTmp = 30144 from rfl]; omega))).symm
          |>.sub_right (by rw [BitVec.add_zero]; exact fun _ h => h)
      · exact disj_scr S (by rw [laneA_eq]; omega) (by omega) (by rw [laneA_eq]; omega)
    rw [show S + BitVec.ofNat 64 (1280 + 8 * i) = at' S (1280 + 8 * i) from rfl,
      readW_frame f' fun r hr => (Offset.sub S (e := Layout.oSave 2 0) (k := 72) (d := 1280 + 8 * i) (n := 8)
        (by rw [show Layout.oSave 2 0 = 1280 from rfl]; omega) (by rw [show Layout.oSave 2 0 = 1280 from rfl]; omega) |>
        (pkW_low hz S r hr).2.1.sub_left), readW_frame H.frame hd]
    exact F.saved i h
  have hg : ∀ i (h : i < 9), t''.gpr (Impl.SlhDsa.AArch64.Fors.saved[i]'h) = σ.gpr (Impl.SlhDsa.AArch64.Fors.saved[i]'h) :=
    fun i h => by rw [g'' i h, h19']; exact hsv i h
  have hcs : ∀ r ∈ preserved, r ∉ Impl.SlhDsa.AArch64.Fors.saved → t''.gpr r = σ.gpr r := fun r hr hs => by
    rw [o''.gpr r hs, cs' r hr (by intro e; subst e; exact hs (by decide)),
      c₁ r hr (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide), F.cs r hr hs]
  refine ⟨⟨fun r hr => ?_, by rw [o''.sp, sp', H.sp, F.sp],
    fun r hr => by rw [o''.vcs r hr, vcs' r hr, H.vcs r hr, F.vcs r hr]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg 0 (by decide)
    · exact hg 1 (by decide)
    · exact hg 2 (by decide)
    · exact hcs _ (by decide) (by decide)
    · exact hg 3 (by decide)
    · exact hg 4 (by decide)
    · exact hg 5 (by decide)
    · exact hg 6 (by decide)
    · exact hg 7 (by decide)
    · exact hcs _ (by decide) (by decide)
    · exact hg 8 (by decide)
  -- the postcondition
  intro pk' a' sk' hE' hsk'
  simp only [hS] at hE' hsk' ⊢
  rw [hG]
  obtain ⟨rfl, rfl⟩ := env_unique hE hE'
  unfold SkAt at hsk'
  subst hsk'
  have h16 : a16.length = 16 := env_a16 hE
  have hm : t''.mem = t'.mem := o''.mem
  have hsig : bytesAt t''.mem SG p.forsSigLen = bytesAt t₁.mem SG (p.k * tsl p) := by
    rw [hm, hL]
    exact bytesAt_frame f' (fun r hr => (M.dxs (o := 0) (l := p.k * tsl p) (by omega) (pkW_low hz S r hr).1).sub_left
      (by rw [BitVec.add_zero]; exact fun _ h => h)) (by have := M.Gf; omega)
  have hsF : bytesAt t''.mem SG p.forsSigLen =
      forsSign p (mdAt p σ.mem S) (bytesAt σ.mem (at' S Layout.oSkSeed) p.n) pk (forsAdrs a16 (σ.gpr .x2).toNat) := by
    rw [hsig]
    have hskp := H.skp
    have hauth := H.auth
    rw [F.x20] at hskp hauth
    exact sig_eq hn32 h16 hkp (ix_eq hA σ.mem S) hskp hauth
  refine ⟨by rw [hm]; exact env_keep hn32 H.env f' fun r hr k hk => (pkW_low hz S r hr).2.2 k hk, hsF, ?_,
    by rw [hm]; exact frame_all hz hk35 F.frame H.frame f'⟩
  rw [← hsF, hsF, hm, msg', forsPkFromSig_forsSign hn32 hk2 _ _ _ (X86_64.Fors.forsAdrs_length h16 _),
    X86_64.Fors.roots_adrs h16 _ hkp, T_shake hz, h20,
    show p.n + 16 = p.n + 16 from rfl, bytesAt_cat, H.env.seedB 0 (by decide), H.env.adrsB 0 (by decide),
    bytesAt_flatS]
  have hroots := H.roots
  rw [F.x20] at hroots
  rw [Proof.SlhDsa.flatMap_range_congr fun i hi => hroots i hi]
  simp only [Proof.SlhDsa.fld, pkF, List.append_assoc, FORS_ROOTS]

/-! ## The whole function -/

/-- `forsSign`, from `forsContract`'s precondition: its postcondition, with
the calling convention kept. -/
theorem fors_wp (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (t4name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true)
    {σ : State} (hpre : (forsContract p).pre σ) :
    WP isa (Impl.SlhDsa.AArch64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k t4name ln T.code) σ fun s' =>
      abiPreserved σ s' ∧ (forsContract p).post σ s' := by
  obtain ⟨hR, ⟨pk, a16, hE⟩, hkp⟩ := hpre
  generalize hS : σ.gpr .x0 = S at hR hE
  generalize hG : σ.gpr .x1 = SG at hR
  unfold Impl.SlhDsa.AArch64.Fors.forsSign
  refine WP.seq (WP.mono (front_ok hA hz hS hG hR hE hkp) fun t₀ ⟨F, I⟩ => ?_)
  refine WP.seq (WP.mono (trees_ok T t4name ln hL hLf F.M (fun i _ => ixv_lt _ _ _ i) I) fun t₁ H => ?_)
  exact fin_ok hA hz T t4name hS hG hE F H

/-- The first part of `Verified`. -/
theorem fors_correct (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (t4name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true) :
    ∀ s, (forsContract p).pre s → ∃ t s',
      Exec isa (Impl.SlhDsa.AArch64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k t4name ln T.code) s t s' ∧
        abiPreserved s s' ∧ (forsContract p).post s s' :=
  fun s h => by
    obtain ⟨t, s', e, abi, post⟩ := fors_wp hz hA T t4name ln hL hLf h
    exact ⟨t, s', e, abi, post⟩

end VG.Proof.SlhDsa.AArch64.Fors
