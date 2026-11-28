module

-- separate module: four leaves of a FORS subtree, and their loop, a stage of `forsSign`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCap
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, four leaves of a subtree

`leafBody` (`Impl/SlhDsa/AArch64/Fors.lean`) as a whole (`leaf_ok`): the
lanes' addresses and `SK.seed` (`blockA_ok`), `PRF` by `thash4`, the
capture of the private key value of the tree's index (`capB_ok`), `F` by
`thash4`, the outputs to the nodes (`out_ok`). As x86-64's `leaf_ok`
(`Proof/SlhDsa/X86_64/ForsLeaf.lean`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.SlhDsa (fld)

variable {p : Params}

/-- Leaf `x` of the FORS trees, as the code computes it. -/
abbrev leafv (p : Params) (pkSeed a16 skSeed : List Byte) (kp x : Nat) : List Byte :=
  F p pkSeed (fld a16 3 kp 0 x) (prf p pkSeed skSeed (fld a16 6 kp 0 x))

/-- Byte `j` of the private key value of leaf `x`. -/
abbrev skv (p : Params) (pkSeed a16 skSeed : List Byte) (kp x j : Nat) : Byte :=
  (prf p pkSeed skSeed (fld a16 6 kp 0 x)).getD j 0

/-- The lanes `A` from their fields on. -/
abbrev laneRs (n : Nat) (S : Addr) : List Region :=
  (List.range 4).map fun k => (⟨at' S (Layout.laneA k + n + 16), 16 + n⟩ : Region)

/-- What four leaves change. -/
abbrev leafW (n : Nat) (S AU : Addr) (J : Nat) : List Region :=
  [⟨S, workUsed⟩, ⟨at' S (Layout.oN + J * n), 4 * n⟩, ⟨AU, n⟩] ++ laneRs n S

/-! ## `Env` and `SK.seed` across a frame -/

theorem env_keep (hn32 : p.n ≤ 32) {m m' : Mem} {S : Addr} {pk a : List Byte} {rs : List Region}
    (he : Env p m S pk a) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∀ k < 4, Region.Disjoint ⟨at' S (Layout.laneA k), p.n + 16⟩ r ∧
      Region.Disjoint ⟨at' S (Layout.laneB k), p.n + 16⟩ r) : Env p m' S pk a := by
  have hA : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 →
      bytesAt m' (at' S (Layout.laneA k + o)) l = bytesAt m (at' S (Layout.laneA k + o)) l :=
    fun k hk o l h => bytesAt_frame hf (fun r hr => (hd r hr k hk).1.sub_left (Offset.sub S (by omega) (by omega)))
      (by omega)
  have hB : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 →
      bytesAt m' (at' S (Layout.laneB k + o)) l = bytesAt m (at' S (Layout.laneB k + o)) l :=
    fun k hk o l h => bytesAt_frame hf (fun r hr => (hd r hr k hk).2.sub_left (Offset.sub S (by omega) (by omega)))
      (by omega)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [← he.seedA k hk, ← Nat.add_zero (Layout.laneA k), hA k hk 0 p.n (by omega)]
  · rw [← he.seedB k hk, ← Nat.add_zero (Layout.laneB k), hB k hk 0 p.n (by omega)]
  · rw [← he.adrsA k hk, hA k hk p.n 16 (by omega)]
  · rw [← he.adrsB k hk, hB k hk p.n 16 (by omega)]

theorem sk_keep {m m' : Mem} {S : Addr} {sk : List Byte} {rs : List Region} (hs : SkAt p m S sk)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨at' S Layout.oSkSeed, p.n⟩ r) (hn : p.n ≤ 2 ^ 64) :
    SkAt p m' S sk := by
  unfold SkAt at hs ⊢; rw [bytesAt_frame hf hd hn, hs]

/-- The regions four leaves change are apart from the lanes' `PK.seed` and
`a16`, and from `SK.seed`. -/
theorem leafW_disj (hz : Sz p) {S AU : Addr} {J : Nat} (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩)
    (hJ : (J + 4) * p.n ≤ 32 * Layout.nodeSlots) {o l : Nat} (hol : o + l ≤ Layout.oA ∨
      (∃ k < 4, (o = Layout.laneA k ∨ o = Layout.laneB k) ∧ l = p.n + 16)) (hl : o + l ≤ 29120) (h₀ : workUsed ≤ o) :
    ∀ r ∈ leafW p.n S AU J, Region.Disjoint ⟨at' S o, l⟩ r := by
  have hn32 := hz.n32
  have eN : Layout.oN = 12480 := rfl
  have eA : Layout.oA = 3136 := rfl
  rw [show Layout.nodeSlots = 520 from rfl, Nat.add_mul] at hJ
  intro r hr
  simp only [leafW, laneRs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hr
  rcases hr with (rfl | rfl | rfl) | ⟨k, hk, rfl⟩
  · exact Offset.disjoint_base S h₀ (by omega)
  · refine disj_scr S ?_ (by omega) (by rw [eN]; omega)
    rcases hol with h | ⟨k, hk, h | h, rfl⟩
    · left; rw [eN]; rw [eA] at h; omega
    · left; rw [eN, h, laneA_eq]; omega
    · left; rw [eN, h, laneB_eq]; omega
  · exact (au_disj hd (by rw [show Layout.oSigTmp = 30144 from rfl]; omega)).symm
  · refine disj_scr S ?_ (by omega) (by rw [laneA_eq]; omega)
    rcases hol with h | ⟨k', hk', h | h, rfl⟩
    · left; rw [laneA_eq]; rw [eA] at h; omega
    · rw [h] at hl; rw [h, laneA_eq, laneA_eq]; rw [laneA_eq] at hl
      rcases Nat.lt_or_ge k k' with h' | h'
      · right
        have := Nat.mul_le_mul_left 128 (show k + 1 ≤ k' by omega)
        omega
      · left; omega
    · right; rw [h, laneB_eq, laneA_eq]; omega

/-- `Env` and `SK.seed` across what four leaves change. -/
theorem leafW_env (hz : Sz p) {S AU : Addr} {J : Nat} {m m' : Mem} {pk a sk : List Byte}
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) (hJ : (J + 4) * p.n ≤ 32 * Layout.nodeSlots)
    (he : Env p m S pk a) (hs : SkAt p m S sk) (hf : Frame (leafW p.n S AU J) m m') :
    Env p m' S pk a ∧ SkAt p m' S sk := by
  have hn32 := hz.n32
  refine ⟨env_keep hn32 he hf fun r hr k hk => ⟨?_, ?_⟩, sk_keep hs hf (fun r hr => ?_) (by omega)⟩
  · exact leafW_disj hz hd hJ (.inr ⟨k, hk, .inl rfl, rfl⟩) (by rw [laneA_eq]; omega)
      (by rw [laneA_eq]; simp only [workUsed]; omega) r hr
  · exact leafW_disj hz hd hJ (.inr ⟨k, hk, .inr rfl, rfl⟩) (by rw [laneB_eq]; omega)
      (by rw [laneB_eq]; simp only [workUsed]; omega) r hr
  · exact leafW_disj hz hd hJ (.inl (by simp only [Layout.oSkSeed, Layout.oKeys, Layout.oA]; omega))
      (by simp only [Layout.oSkSeed, Layout.oKeys]; omega) (by simp only [Layout.oSkSeed, Layout.oKeys, workUsed]; omega) r hr

/-! ## The lanes' addresses and `SK.seed` -/

/-- What the first block of `leafBody` leaves: lane `k`'s fields for leaf
`X + k` with the type `FORS_PRF`, its message `SK.seed`. -/
structure APost (p : Params) (S : Addr) (t t' : State) (kp X : Nat) : Prop where
  keep : Keep [.x9, .x10, .x11, .x14] t t'
  fld : ∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 16)) 16 = lfld 6 kp (X + k)
  msg : ∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n = bytesAt t.mem (at' S Layout.oSkSeed) p.n
  frame : Frame (laneRs p.n S) t.mem t'.mem

/-- Lanes `k` and `k'` from their fields on are apart. -/
theorem lane_disj (hn32 : p.n ≤ 32) (S : Addr) {k k' : Nat} (o l : Nat) (hk : k < 4) (hk' : k' < 4) (hne : k ≠ k')
    (ho : 16 ≤ o) (hl : o + l ≤ 32 + p.n) :
    Region.Disjoint ⟨at' S (Layout.laneA k + p.n + o), l⟩ ⟨at' S (Layout.laneA k' + p.n + 16), 16 + p.n⟩ := by
  refine disj_scr S ?_ (by rw [laneA_eq]; omega) (by rw [laneA_eq]; omega)
  rw [laneA_eq, laneA_eq]
  rcases Nat.lt_or_ge k k' with h | h
  · left; have := Nat.mul_le_mul_left 128 (show k + 1 ≤ k' by omega); omega
  · right; have := Nat.mul_le_mul_left 128 (show k' + 1 ≤ k by omega); omega

theorem blockA_ok (hz : Sz p) {S : Addr} {V4 U2 J : Nat} {t : State} (h19 : t.gpr .x19 = S)
    (hKP : (t.gpr .x20).toNat < 2 ^ 32) (h25 : t.gpr .x25 = BitVec.ofNat 64 U2)
    (h26 : t.gpr .x26 = BitVec.ofNat 64 J) (h27 : t.gpr .x27 = BitVec.ofNat 64 V4) (hX : V4 + U2 + J + 4 < 2 ^ 32)
    (hw : (⟨S, 65536⟩ : Region) ∈ t.wr) :
    WP isa (.block (([.add .x .x10 .x27 .x25, .add .x .x10 .x10 .x26] : List Instr) ++
        (List.range 4).flatMap (fun k => Impl.SlhDsa.AArch64.Fors.leafAdrs ⟨p.n, p.len⟩ 6 k ++
          Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).msgOff) .x19 Layout.oSkSeed
            ((⟨p.n, p.len⟩ : Layout).n / 8)))) t
      fun t' => APost p S t t' (t.gpr .x20).toNat (V4 + U2 + J) := by
  have hn32 := hz.n32
  simp only [List.cons_append, List.nil_append]
  refine wp_addr fun t₁ u₁ => wp_addr fun t₂ u₂ => ?_
  have k₂ : Keep [.x10] t t₂ := ((upK u₁).trans (upK u₂)).mono (by simp)
  have hx₂ : t₂.gpr .x10 = BitVec.ofNat 64 (V4 + U2 + J) := by
    rw [u₂.gpr, u₁.gpr, u₁.other .x26 (by decide), h25, h26, h27, BitVec.ofNat_add_ofNat,
      BitVec.ofNat_add_ofNat]
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  rw [← List.append_nil (List.flatMap _ _)]
  refine wp_flatRange (P := fun K u => Keep [.x9, .x10, .x11, .x14] t u ∧ u.gpr .x10 = BitVec.ofNat 64 (V4 + U2 + J) ∧
      (∀ k < K, bytesAt u.mem (at' S (Layout.laneA k + p.n + 16)) 16 = lfld 6 (t.gpr .x20).toNat (V4 + U2 + J + k) ∧
        bytesAt u.mem (at' S (Layout.laneA k + p.n + 32)) p.n = bytesAt t.mem (at' S Layout.oSkSeed) p.n) ∧
      Frame (laneRs p.n S) t.mem u.mem) 4
    ⟨k₂.mono (by simp), hx₂, fun _ h => absurd h (by omega), by rw [hm₂]; exact Frame.refl _ _⟩
    (fun K hK u is' ⟨ku, xu, bu, fu⟩ kk => ?_) fun u ⟨ku, xu, bu, fu⟩ =>
      WP.block_nil ⟨ku, fun k hk => (bu k hk).1, fun k hk => (bu k hk).2, fu⟩
  have hsk : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' → (∀ r ∈ rs, ∃ k < 4, r = ⟨at' S (Layout.laneA k + p.n + 16), 16 + p.n⟩) →
      bytesAt m' (at' S Layout.oSkSeed) p.n = bytesAt m (at' S Layout.oSkSeed) p.n := fun hf hr =>
    bytesAt_frame hf (fun r h => by
      obtain ⟨k, hk, rfl⟩ := hr r h
      exact disj_scr S (by simp only [Layout.oSkSeed, Layout.oKeys]; rw [laneA_eq]; omega)
        (by simp only [Layout.oSkSeed, Layout.oKeys]; omega) (by rw [laneA_eq]; omega)) (by omega)
  have hlr : ∀ r ∈ laneRs p.n S, ∃ k < 4, r = ⟨at' S (Layout.laneA k + p.n + 16), 16 + p.n⟩ := fun r hr => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr; exact ⟨k, List.mem_range.mp hk, rfl⟩
  refine lane_ok hz (x := V4 + U2 + J + K) (ty := 6) hK (by rw [ku.get .x19, h19]) (by rw [ku.get .x20]; exact hKP)
    (by rw [Nat.add_sub_cancel]; exact xu) (by omega) (by omega) (by rw [ku.wr]; exact hw) fun u' l' => kk u' ?_
  have hf' := l'.frame
  have lf := l'.fld
  rw [ku.get .x20] at lf
  refine ⟨(ku.trans l'.keep).mono (by simp), by rw [l'.keep.get .x10, xu], fun k hk => ?_,
    fu.trans (hf'.sub fun r hr => ?_)⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · have hne : k ≠ K := by omega
      refine ⟨?_, ?_⟩
      · rw [bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact lane_disj hn32 S 16 16 (by omega) hK hne (Nat.le_refl _) (by omega)) (by omega)]
        exact (bu k hk').1
      · rw [bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact lane_disj hn32 S 32 p.n (by omega) hK hne (by omega) (by omega)) (by omega)]
        exact (bu k hk').2
    · exact ⟨lf, by rw [l'.msg, hsk fu hlr]⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_map.mpr ⟨K, List.mem_range.mpr hK, rfl⟩, fun _ h => h⟩

/-! ## Four leaves -/

/-- A lane of `A`: `PK.seed ‖ a16 ‖` its fields `‖` its message. -/
theorem lane_bytes {m : Mem} {S : Addr} {pk a16 F16 M : List Byte} {k L : Nat}
    (hE : Env p m S pk a16) (hk : k < 4) (hf : bytesAt m (at' S (Layout.laneA k + p.n + 16)) 16 = F16)
    (hm : bytesAt m (at' S (Layout.laneA k + p.n + 32)) L = M) :
    bytesAt m (at' S (Layout.laneA k)) (p.n + 32 + L) = pk ++ (a16 ++ F16) ++ M := by
  rw [show p.n + 32 + L = p.n + (16 + (16 + L)) by omega, bytesAt_cat, bytesAt_cat, bytesAt_cat,
    show Layout.laneA k + p.n + 16 + 16 = Layout.laneA k + p.n + 32 by omega, hE.seedA k hk, hE.adrsA k hk,
    hf, hm, List.append_assoc, List.append_assoc]

theorem prf_shake (hz : Sz p) (pk sk : List Byte) (a : Adrs) : prf p pk sk a = shake256 (pk ++ a ++ sk) p.n := by
  simp only [prf, hz.shake, shakeAdrs]

theorem F_shake (hz : Sz p) (pk : List Byte) (a : Adrs) (M : List Byte) : F p pk a M = shake256 (pk ++ a ++ M) p.n := by
  simp only [F, hz.shake, shakeAdrs]

/-- What a call of `thash4` on the lanes `A` changes. -/
theorem t4ch_mem {n : Nat} {S : Addr} {r : Region} (h : r ∈ Wots4.t4ch n S Layout.oA Layout.strideA) :
    r = ⟨S, workUsed⟩ ∨ ∃ j < 4, r = ⟨at' S (Layout.laneA j + n + 32), n⟩ := by
  simp only [Wots4.t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨j, hj, rfl⟩ | rfl
  · exact .inr ⟨j, hj, by rw [laneA_eq]; simp only [Layout.oA, Layout.strideA]; congr 3; omega⟩
  · exact .inl rfl

/-- A part of `scratch` past `work` and apart from the lanes' messages is
apart from what a call of `thash4` on the lanes `A` changes. -/
theorem t4ch_disj (hn32 : p.n ≤ 32) {S : Addr} {o l : Nat} (h₀ : workUsed ≤ o) (hl : o + l ≤ 65536)
    (h : ∀ j < 4, o + l ≤ Layout.laneA j + p.n + 32 ∨ Layout.laneA j + p.n + 32 + p.n ≤ o) :
    ∀ r ∈ Wots4.t4ch p.n S Layout.oA Layout.strideA, Region.Disjoint ⟨at' S o, l⟩ r := fun r hr => by
  rcases t4ch_mem hr with rfl | ⟨j, hj, rfl⟩
  · exact Offset.disjoint_base S h₀ (by omega)
  · exact disj_scr S (h j hj) hl (by rw [laneA_eq]; omega)

theorem t4ch_au {S AU : Addr} (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) (hn32 : p.n ≤ 32) :
    ∀ r ∈ Wots4.t4ch p.n S Layout.oA Layout.strideA, Region.Disjoint ⟨AU, p.n⟩ r := fun r hr => by
  rcases t4ch_mem hr with rfl | ⟨j, hj, rfl⟩
  · have h₀ : workUsed ≤ Layout.oSigTmp := by
      rw [show Layout.oSigTmp = 30144 from rfl, show workUsed = 1008 from rfl]; omega
    exact hd.sub_right (Region.sub_prefix h₀)
  · exact au_disj hd (by rw [laneA_eq, show Layout.oSigTmp = 30144 from rfl]; omega)

theorem t4ch_sub (hn32 : p.n ≤ 32) {S AU : Addr} {J : Nat} :
    ∀ r ∈ Wots4.t4ch p.n S Layout.oA Layout.strideA, ∃ R ∈ leafW p.n S AU J, Region.Sub r R := fun r hr => by
  rcases t4ch_mem hr with rfl | ⟨j, hj, rfl⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩),
      Offset.sub S (by omega) (by omega)⟩

/-- What `leafBody` does: four leaves `V4 + U2 + J` to that plus 3 (`V4`
the first of the tree, `U2` of the subtree, `J` in it), their nodes; the
private key value of the tree's index `idx` XORed into the signature at `AU`
if it is one of them; the next leaf `J + 4` in `x26`, and `x9 = J + 4 - P`. -/
structure LeafP (p : Params) (S AU : Addr) (pkSeed a16 skSeed : List Byte) (kp V4 U2 J idx P : Nat)
    (t t' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x26 → r ≠ .x30 → t'.gpr r = t.gpr r
  x26 : t'.gpr .x26 = BitVec.ofNat 64 (J + 4)
  x9 : t'.gpr .x9 = BitVec.ofNat 64 (J + 4) - BitVec.ofNat 64 P
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  vcs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  env : Env p t'.mem S pkSeed a16
  skat : SkAt p t'.mem S skSeed
  nodes : ∀ k < 4, bytesAt t'.mem (at' S (Layout.oN + (J + k) * p.n)) p.n = leafv p pkSeed a16 skSeed kp (V4 + U2 + J + k)
  sk : ∀ j < p.n, t'.mem (AU + BitVec.ofNat 64 j) =
    if U2 + J ≤ idx ∧ idx < U2 + J + 4 then skv p pkSeed a16 skSeed kp (V4 + idx) j ^^^ t.mem (AU + BitVec.ofNat 64 j)
    else t.mem (AU + BitVec.ofNat 64 j)
  frame : Frame (leafW p.n S AU J) t.mem t'.mem

theorem pow_s_lt (a : Nat) : 2 ^ Impl.SlhDsa.AArch64.Fors.s a < 4096 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (Nat.min_le_right a 9)) (by decide)

theorem keep_pres (r : Reg) (hr : r ∈ preserved) (h26 : r ≠ .x26) : r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x26] := by
  revert r; decide

theorem keep_pres0 (r : Reg) (hr : r ∈ preserved) : r ∉ [.x9, .x10, .x11, .x12, .x13, .x14] := by
  revert r; decide

theorem notin_of {r : Reg} {L l : List Reg} (hr : r ∉ L) (hl : ∀ x ∈ l, x ∈ L := by decide) : r ∉ l :=
  fun h => hr (hl r h)

/-- A part of `scratch` apart from the type fields and the signature is
apart from what the capture changes. -/
theorem cap_disj (hn32 : p.n ≤ 32) {S AU : Addr} (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) {o l : Nat}
    (hl : o + l ≤ 29120) (h : ∀ k < 4, o + l ≤ Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 20 ≤ o) :
    ∀ r ∈ (⟨AU, p.n⟩ : Region) :: typeRs p.n S, Region.Disjoint ⟨at' S o, l⟩ r := fun r hr => by
  rcases List.mem_cons.mp hr with rfl | hr
  · exact (au_disj hd (by rw [show Layout.oSigTmp = 30144 from rfl]; omega)).symm
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    have hk' := List.mem_range.mp hk
    exact disj_scr S (by have := h k hk'; omega) (by omega) (by rw [laneA_eq]; omega)

theorem leaf_ok (hz : Sz p) (T : Thash4Impl p.n) (name : String) {S AU : Addr} {V4 U2 J idx : Nat}
    {pk a16 sk : List Byte} {t : State}
    (h19 : t.gpr .x19 = S) (hKP : (t.gpr .x20).toNat < 2 ^ 32) (h21 : t.gpr .x21 = BitVec.ofNat 64 idx)
    (hidx : idx < 2 ^ 32) (h24 : t.gpr .x24 = AU) (h25 : t.gpr .x25 = BitVec.ofNat 64 U2)
    (h26 : t.gpr .x26 = BitVec.ofNat 64 J) (h27 : t.gpr .x27 = BitVec.ofNat 64 V4)
    (hw : (⟨S, 65536⟩ : Region) ∈ t.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (hE : Env p t.mem S pk a16) (hsk : SkAt p t.mem S sk) (hX : V4 + U2 + J + 4 < 2 ^ 32)
    (hJ : (J + 4) * p.n ≤ 32 * Layout.nodeSlots) (hout : InRegions t.wr AU p.n)
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) :
    WP isa (Impl.SlhDsa.AArch64.Fors.leafBody ⟨p.n, p.len⟩ p.a name T.code) t
      (LeafP p S AU pk a16 sk (t.gpr .x20).toNat V4 U2 J idx (2 ^ Impl.SlhDsa.AArch64.Fors.s p.a) t) := by
  have hn32 := hz.n32
  have eT : Layout.oSigTmp = 30144 := rfl
  have eN : Layout.oN = 12480 := rfl
  have hJ' := hJ
  rw [show Layout.nodeSlots = 520 from rfl, Nat.add_mul] at hJ'
  have hlR : ∀ r ∈ laneRs p.n S, ∃ R ∈ leafW p.n S AU J, Region.Sub r R := fun r hr =>
    ⟨r, List.mem_append_right _ hr, fun _ h => h⟩
  have hauL : ∀ r ∈ laneRs p.n S, Region.Disjoint ⟨AU, p.n⟩ r := fun r hr => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact au_disj hd (by rw [laneA_eq, eT]; have := List.mem_range.mp hk; omega)
  unfold Impl.SlhDsa.AArch64.Fors.leafBody
  -- the lanes' addresses and `SK.seed`
  refine WP.seq (WP.mono (blockA_ok hz h19 hKP h25 h26 h27 hX hw) fun a ha => ?_)
  have fA : Frame (leafW p.n S AU J) t.mem a.mem := ha.frame.sub hlR
  obtain ⟨envA, -⟩ := leafW_env hz hd hJ hE hsk fA
  have hinA : ∀ k < 4, bytesAt a.mem (at' S (Layout.laneA k)) (2 * p.n + 32) =
      pk ++ fld a16 6 (t.gpr .x20).toNat 0 (V4 + U2 + J + k) ++ sk := fun k hk => by
    rw [show 2 * p.n + 32 = p.n + 32 + p.n by omega, lane_bytes envA hk (ha.fld k hk) ((ha.msg k hk).trans hsk)]
    rfl
  -- `PRF`
  refine WP.seq (acall_ok hz T name (t := a) (by rw [ha.keep.get .x19, h19]) (by rw [ha.keep.wr]; exact hw) hfit
    fun a' ha' => ?_)
  have prfA : ∀ k < 4, bytesAt a'.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      prf p pk sk (fld a16 6 (t.gpr .x20).toNat 0 (V4 + U2 + J + k)) := fun k hk => by
    rw [ha'.out k hk, hinA k hk, prf_shake hz]
  have ga : ∀ r ∈ preserved, r ≠ .x30 → a'.gpr r = t.gpr r := fun r hr h₂ => by
    rw [ha'.cs r hr h₂, ha.keep.get r (notin_of (keep_pres0 r hr))]
  have hka : ∀ r ∈ preservedV, (a'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64 := fun r hr => by
    rw [ha'.vcs r hr, ha.keep.vcs r hr]
  have hwa : a'.wr = t.wr := by rw [ha'.wr, ha.keep.wr]
  have fA' : Frame (leafW p.n S AU J) t.mem a'.mem := fA.trans (ha'.frame.sub (t4ch_sub hn32))
  have auA : ∀ j < p.n, a'.mem (AU + BitVec.ofNat 64 j) = t.mem (AU + BitVec.ofNat 64 j) := fun j hj => by
    rw [ha'.frame.bytes (R := ⟨AU, p.n⟩) (t4ch_au hd hn32) (by show p.n ≤ 2 ^ 64; omega) hj,
      ha.frame.bytes (R := ⟨AU, p.n⟩) hauL (by show p.n ≤ 2 ^ 64; omega) hj]
  have restA : ∀ k < 4, bytesAt a.mem (at' S (Layout.laneA k + p.n + 16 + 4)) 12 =
      toByte (t.gpr .x20).toNat 4 ++ (toByte 0 4 ++ toByte (V4 + U2 + J + k) 4) := fun k hk => by
    have e := (bytesAt_cat a.mem S (Layout.laneA k + p.n + 16) 4 12).symm.trans (ha.fld k hk)
    exact (List.append_inj e (by rw [bytesAt_length, toByte_length])).2
  -- the capture
  refine WP.seq (WP.mono (capB_ok hz (U2 := U2) (J := J) (idx := idx) (t := a')
    (by rw [ga .x19 (by decide) (by decide), h19]) (by rw [ga .x21 (by decide) (by decide), h21])
    (by rw [ga .x24 (by decide) (by decide), h24]) (by rw [ga .x25 (by decide) (by decide), h25])
    (by rw [ga .x26 (by decide) (by decide), h26]) (by omega) hidx (by rw [hwa]; exact hw) (by rw [hwa]; exact hout) hd)
    fun b hb => ?_)
  have gb : ∀ r ∈ preserved, r ≠ .x30 → b.gpr r = t.gpr r := fun r hr h₂ => by
    rw [hb.keep.get r (notin_of (keep_pres0 r hr)), ga r hr h₂]
  have hwb : b.wr = t.wr := by rw [hb.keep.wr, hwa]
  have fB : Frame (leafW p.n S AU J) t.mem b.mem := fA'.trans (hb.frame.sub fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨_, by simp, fun _ h => h⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨k, hk, rfl⟩), Offset.sub S (by omega) (by omega)⟩)
  obtain ⟨envB, -⟩ := leafW_env hz hd hJ hE hsk fB
  have restB : ∀ k < 4, bytesAt b.mem (at' S (Layout.laneA k + p.n + 16 + 4)) 12 =
      bytesAt a.mem (at' S (Layout.laneA k + p.n + 16 + 4)) 12 := fun k hk => by
    rw [bytesAt_frame hb.frame (cap_disj hn32 hd (by rw [laneA_eq]; omega) fun k' hk' => by
        rw [laneA_eq, laneA_eq]
        rcases Nat.lt_or_ge k k' with h | h
        · left; have := Nat.mul_le_mul_left 128 (show k + 1 ≤ k' by omega); omega
        · right; omega) (by omega),
      bytesAt_frame ha'.frame (t4ch_disj hn32 (by rw [laneA_eq]; simp only [workUsed]; omega)
        (by rw [laneA_eq]; omega) fun j hj => by
          rw [laneA_eq, laneA_eq]
          rcases Nat.lt_or_ge j k with h | h
          · right; have := Nat.mul_le_mul_left 128 (show j + 1 ≤ k by omega); omega
          · left; have := Nat.mul_le_mul_left 128 h; omega) (by omega)]
  have inB : ∀ k < 4, bytesAt b.mem (at' S (Layout.laneA k)) (2 * p.n + 32) =
      pk ++ fld a16 3 (t.gpr .x20).toNat 0 (V4 + U2 + J + k) ++
        prf p pk sk (fld a16 6 (t.gpr .x20).toNat 0 (V4 + U2 + J + k)) := fun k hk => by
    have hf : bytesAt b.mem (at' S (Layout.laneA k + p.n + 16)) 16 = lfld 3 (t.gpr .x20).toNat (V4 + U2 + J + k) := by
      refine (bytesAt_cat b.mem S _ 4 12).trans ?_
      rw [hb.ty k hk, restB k hk, restA k hk]
    have hm : bytesAt b.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
        prf p pk sk (fld a16 6 (t.gpr .x20).toNat 0 (V4 + U2 + J + k)) := by
      rw [bytesAt_frame hb.frame (cap_disj hn32 hd (by rw [laneA_eq]; omega) fun k' hk' => by
          rw [laneA_eq, laneA_eq]
          rcases Nat.lt_or_ge k k' with h | h
          · left; have := Nat.mul_le_mul_left 128 (show k + 1 ≤ k' by omega); omega
          · right; omega) (by omega), prfA k hk]
    rw [show 2 * p.n + 32 = p.n + 32 + p.n by omega, lane_bytes envB hk hf hm]
    rfl
  -- `F`
  refine WP.seq (acall_ok hz T name (t := b) (by rw [gb .x19 (by decide) (by decide), h19]) (by rw [hwb]; exact hw)
    hfit fun b' hb' => ?_)
  have FB : ∀ k < 4, bytesAt b'.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      leafv p pk a16 sk (t.gpr .x20).toNat (V4 + U2 + J + k) := fun k hk => by
    rw [hb'.out k hk, inB k hk]; exact (F_shake hz _ _ _).symm
  have gb' : ∀ r ∈ preserved, r ≠ .x30 → b'.gpr r = t.gpr r := fun r hr h₂ => by rw [hb'.cs r hr h₂, gb r hr h₂]
  have fB' : Frame (leafW p.n S AU J) t.mem b'.mem := fB.trans (hb'.frame.sub (t4ch_sub hn32))
  -- the nodes
  refine WP.mono (out_ok hz (J := J) (P := 2 ^ Impl.SlhDsa.AArch64.Fors.s p.a)
    (by rw [gb' .x19 (by decide) (by decide), h19]) (by rw [gb' .x26 (by decide) (by decide), h26])
    (by rw [hb'.wr, hwb]; exact hw) hJ (pow_s_lt p.a)) fun c hc => ?_
  have hnd : Region.Disjoint ⟨AU, p.n⟩ ⟨at' S (Layout.oN + J * p.n), 4 * p.n⟩ := au_disj hd (by rw [eT, eN]; omega)
  have fC : Frame (leafW p.n S AU J) t.mem c.mem := fB'.trans (hc.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  obtain ⟨envC, skC⟩ := leafW_env hz hd hJ hE hsk fC
  refine ⟨fun r hr h₁ h₂ => ?_, hc.x26, hc.x9, ?_, ?_, ?_, fun r hr => ?_, envC, skC, fun k hk => ?_,
    fun j hj => ?_, fC⟩
  · rw [hc.keep.get r (notin_of (keep_pres r hr h₁)), gb' r hr h₂]
  · rw [hc.keep.sp, hb'.sp, hb.keep.sp, ha'.sp, ha.keep.sp]
  · rw [hc.keep.rd, hb'.rd, hb.keep.rd, ha'.rd, ha.keep.rd]
  · rw [hc.keep.wr, hb'.wr, hwb]
  · rw [hc.keep.vcs r hr, hb'.vcs r hr, hb.keep.vcs r hr, hka r hr]
  · rw [hc.out k hk, FB k hk]
  · rw [hc.frame.bytes (R := ⟨AU, p.n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hnd)
        (by show p.n ≤ 2 ^ 64; omega) hj,
      hb'.frame.bytes (R := ⟨AU, p.n⟩) (t4ch_au hd hn32) (by show p.n ≤ 2 ^ 64; omega) hj, hb.sk j hj, auA j hj]
    by_cases hc' : U2 + J ≤ idx ∧ idx < U2 + J + 4
    · rw [ite_eq_left hc', ite_eq_left hc', ← getD_bytesAt a'.mem (at' S (Layout.laneA (idx - (U2 + J)) + p.n + 32)) hj,
        prfA _ (by omega),
        show V4 + U2 + J + (idx - (U2 + J)) = V4 + idx by omega]
    · rw [ite_eq_right hc', ite_eq_right hc']


/-! ## The loop of leaves -/

/-- What the loop of leaves changes. -/
abbrev loopW (n : Nat) (S AU : Addr) : List Region :=
  [⟨S, workUsed⟩, ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, ⟨AU, n⟩] ++ laneRs n S

/-- The state of the loop of leaves after `J` leaves of the subtree from
`U2` of the tree from `V4`, from its entry state `t₀`. -/
structure LS (p : Params) (S AU : Addr) (pkSeed a16 skSeed : List Byte) (kp V4 U2 idx : Nat)
    (t₀ : State) (J : Nat) (u : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x26 → r ≠ .x30 → u.gpr r = t₀.gpr r
  x26 : u.gpr .x26 = BitVec.ofNat 64 J
  sp : u.sp = t₀.sp
  rd : u.rd = t₀.rd
  wr : u.wr = t₀.wr
  vcs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t₀.v r).extractLsb' 0 64
  env : Env p u.mem S pkSeed a16
  skat : SkAt p u.mem S skSeed
  nodes : ∀ i < J, bytesAt u.mem (at' S (Layout.oN + i * p.n)) p.n = leafv p pkSeed a16 skSeed kp (V4 + U2 + i)
  skb : ∀ j < p.n, u.mem (AU + BitVec.ofNat 64 j) =
    if U2 ≤ idx ∧ idx < U2 + J then skv p pkSeed a16 skSeed kp (V4 + idx) j ^^^ t₀.mem (AU + BitVec.ofNat 64 j)
    else t₀.mem (AU + BitVec.ofNat 64 j)
  frame : Frame (loopW p.n S AU) t₀.mem u.mem

/-- The loop's invariant at the measure `m` (the passes left). -/
abbrev LI (p : Params) (S AU : Addr) (pkSeed a16 skSeed : List Byte) (kp V4 U2 idx : Nat)
    (t₀ : State) (m : Nat) (u : State) : Prop :=
  ∃ J, J + 4 * m = 2 ^ Impl.SlhDsa.AArch64.Fors.s p.a ∧ 0 < m ∧ LS p S AU pkSeed a16 skSeed kp V4 U2 idx t₀ J u

/-- `subs` of a public counter, and the loop's condition after it. -/
theorem nz_sub {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y != 0) = decide (x ≠ y) := by
  have : (BitVec.ofNat 64 x - BitVec.ofNat 64 y = 0) ↔ x = y := by
    constructor
    · intro e
      have e2 := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at e2
      omega
    · rintro rfl; simp
  rw [bne, show ((BitVec.ofNat 64 x - BitVec.ofNat 64 y) == 0) = decide (x = y) from by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact this]
  simp

theorem pow_s_le (a : Nat) : 2 ^ Impl.SlhDsa.AArch64.Fors.s a ≤ 512 :=
  Nat.pow_le_pow_right (by decide) (Nat.min_le_right a 9)

/-- A pass of the loop of leaves. -/
theorem leaves_step (hz : Sz p) (T : Thash4Impl p.n) (name : String) {S AU : Addr} {V4 U2 idx : Nat}
    {pk a16 sk : List Byte} {t₀ : State}
    (h19 : t₀.gpr .x19 = S) (hKP : (t₀.gpr .x20).toNat < 2 ^ 32) (h21 : t₀.gpr .x21 = BitVec.ofNat 64 idx)
    (hidx : idx < 2 ^ 32) (h24 : t₀.gpr .x24 = AU) (h25 : t₀.gpr .x25 = BitVec.ofNat 64 U2)
    (h27 : t₀.gpr .x27 = BitVec.ofNat 64 V4) (hw : (⟨S, 65536⟩ : Region) ∈ t₀.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (hX : V4 + U2 + 2 ^ Impl.SlhDsa.AArch64.Fors.s p.a < 2 ^ 32) (hout : InRegions t₀.wr AU p.n)
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) :
    ∀ m u, LI p S AU pk a16 sk (t₀.gpr .x20).toNat V4 U2 idx t₀ m u →
      WP isa (Impl.SlhDsa.AArch64.Fors.leafBody ⟨p.n, p.len⟩ p.a name T.code) u fun u' =>
        isa.eval (.nonzero .x .x9) u' = some (decide (m ≠ 1)) ∧
        (decide (m ≠ 1) = false →
          LS p S AU pk a16 sk (t₀.gpr .x20).toNat V4 U2 idx t₀ (2 ^ Impl.SlhDsa.AArch64.Fors.s p.a) u') ∧
        (decide (m ≠ 1) = true → m - 1 < m ∧ LI p S AU pk a16 sk (t₀.gpr .x20).toNat V4 U2 idx t₀ (m - 1) u') := by
  have hn32 := hz.n32
  have eN : Layout.oN = 12480 := rfl
  have hP := pow_s_le p.a
  intro m u ⟨J, hJm, hm, hI⟩
  have hJ : (J + 4) * p.n ≤ 32 * Layout.nodeSlots := by
    rw [show Layout.nodeSlots = 520 from rfl]
    have := Nat.mul_le_mul (show J + 4 ≤ 512 by omega) hn32; omega
  have g : ∀ r ∈ preserved, r ≠ .x26 → r ≠ .x30 → u.gpr r = t₀.gpr r := hI.cs
  refine WP.mono (leaf_ok hz T name (V4 := V4) (U2 := U2) (J := J) (idx := idx) (pk := pk) (a16 := a16) (sk := sk)
    (by rw [g .x19 (by decide) (by decide) (by decide), h19])
    (by rw [g .x20 (by decide) (by decide) (by decide)]; exact hKP)
    (by rw [g .x21 (by decide) (by decide) (by decide), h21]) hidx
    (by rw [g .x24 (by decide) (by decide) (by decide), h24]) (by rw [g .x25 (by decide) (by decide) (by decide), h25])
    hI.x26 (by rw [g .x27 (by decide) (by decide) (by decide), h27]) (by rw [hI.wr]; exact hw) hfit hI.env hI.skat
    (by omega) hJ (by rw [hI.wr]; exact hout) hd) fun u' lp => ?_
  rw [g .x20 (by decide) (by decide) (by decide)] at lp
  have hI' : LS p S AU pk a16 sk (t₀.gpr .x20).toNat V4 U2 idx t₀ (J + 4) u' := by
    refine ⟨fun r hr h₁ h₂ => by rw [lp.cs r hr h₁ h₂, g r hr h₁ h₂], lp.x26, by rw [lp.sp, hI.sp],
      by rw [lp.rd, hI.rd], by rw [lp.wr, hI.wr], fun r hr => by rw [lp.vcs r hr, hI.vcs r hr], lp.env, lp.skat,
      fun i hi => ?_, fun j hj => ?_, hI.frame.trans (lp.frame.sub fun r hr => ?_)⟩
    · by_cases hi' : i < J
      · have := Nat.mul_le_mul_right p.n (show i + 1 ≤ J by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        have hJ' := hJ
        rw [show Layout.nodeSlots = 520 from rfl, Nat.add_mul] at hJ'
        rw [bytesAt_frame lp.frame (fun r hr => by
          simp only [leafW, laneRs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
            List.mem_range] at hr
          rcases hr with (rfl | rfl | rfl) | ⟨k, hk, rfl⟩
          · exact Offset.disjoint_base S (by rw [eN]; simp only [workUsed]; omega) (by omega)
          · exact disj_scr S (by omega) (by rw [eN]; omega) (by rw [eN]; omega)
          · exact (au_disj hd (by rw [eN, show Layout.oSigTmp = 30144 from rfl]; omega)).symm
          · exact disj_scr S (by rw [laneA_eq, eN]; omega) (by rw [eN]; omega) (by rw [laneA_eq]; omega)) (by omega)]
        exact hI.nodes i hi'
      · obtain ⟨c, hc4, rfl⟩ : ∃ c, c < 4 ∧ i = J + c := ⟨i - J, by omega, by omega⟩
        rw [lp.nodes c hc4, Nat.add_assoc]
    · rw [lp.sk j hj, hI.skb j hj]
      by_cases h1 : U2 + J ≤ idx ∧ idx < U2 + J + 4
      · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left (by omega)]
      · rw [ite_eq_right h1]
        by_cases h2 : U2 ≤ idx ∧ idx < U2 + J
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]
    · simp only [leafW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | hr
      · exact ⟨⟨S, workUsed⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp,
          Offset.sub S (by omega) (by rw [show Layout.nodeSlots = 520 from rfl] at hJ ⊢; rw [Nat.add_mul] at hJ; omega)⟩
      · exact ⟨⟨AU, p.n⟩, by simp, fun _ h => h⟩
      · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩
  refine ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · show some (u'.read .x .x9 != 0) = _
    rw [State.read, BitVec.setWidth_eq, lp.x9, nz_sub (by omega) (by omega)]
    congr 1; simp only [decide_eq_decide]; omega
  · have : J + 4 = 2 ^ Impl.SlhDsa.AArch64.Fors.s p.a := by
      simp only [decide_eq_false_iff_not, Decidable.not_not] at hc; omega
    rw [← this]; exact hI'
  · simp only [decide_eq_true_eq] at hc
    exact ⟨by omega, J + 4, by omega, by omega, hI'⟩

/-- The loop of leaves: `2^s / 4` passes of four. -/
theorem leaves_ok (hz : Sz p) (T : Thash4Impl p.n) (name : String) (hs2 : 2 ≤ Impl.SlhDsa.AArch64.Fors.s p.a)
    {S AU : Addr} {V4 U2 idx : Nat} {pk a16 sk : List Byte} {t₀ : State}
    (h19 : t₀.gpr .x19 = S) (hKP : (t₀.gpr .x20).toNat < 2 ^ 32) (h21 : t₀.gpr .x21 = BitVec.ofNat 64 idx)
    (hidx : idx < 2 ^ 32) (h24 : t₀.gpr .x24 = AU) (h25 : t₀.gpr .x25 = BitVec.ofNat 64 U2)
    (h26 : t₀.gpr .x26 = 0) (h27 : t₀.gpr .x27 = BitVec.ofNat 64 V4) (hw : (⟨S, 65536⟩ : Region) ∈ t₀.wr)
    (hfit : S.toNat + 65536 ≤ 2 ^ 64) (hX : V4 + U2 + 2 ^ Impl.SlhDsa.AArch64.Fors.s p.a < 2 ^ 32)
    (hout : InRegions t₀.wr AU p.n) (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩)
    (hE : Env p t₀.mem S pk a16) (hsk : SkAt p t₀.mem S sk) :
    WP isa (.loop (Impl.SlhDsa.AArch64.Fors.leafBody ⟨p.n, p.len⟩ p.a name T.code) (.nonzero .x .x9)) t₀
      (LS p S AU pk a16 sk (t₀.gpr .x20).toNat V4 U2 idx t₀ (2 ^ Impl.SlhDsa.AArch64.Fors.s p.a)) := by
  have h4 : 2 ^ Impl.SlhDsa.AArch64.Fors.s p.a = 4 * 2 ^ (Impl.SlhDsa.AArch64.Fors.s p.a - 2) := by
    rw [show Impl.SlhDsa.AArch64.Fors.s p.a = Impl.SlhDsa.AArch64.Fors.s p.a - 2 + 2 by omega, Nat.pow_add,
      Nat.add_sub_cancel]; omega
  exact wpLoop (fun m => decide (m ≠ 1)) (fun m => m - 1)
    (leaves_step hz T name h19 hKP h21 hidx h24 h25 h27 hw hfit hX hout hd)
    (2 ^ (Impl.SlhDsa.AArch64.Fors.s p.a - 2)) ⟨0, by omega, Nat.one_le_two_pow,
      ⟨fun _ _ _ _ => rfl, by rw [h26]; rfl, rfl, rfl, rfl, fun _ _ => rfl, hE, hsk,
        fun _ h => absurd h (Nat.not_lt_zero _), fun j _ => by rw [ite_eq_right (by omega)], Frame.refl _ _⟩⟩

end VG.Proof.SlhDsa.AArch64.Fors
