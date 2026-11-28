module

-- separate module: the heights of a FORS tree above its subtrees as a whole, a stage of `forsSign`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsTop
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, the tree's root

`topHeights` (`Impl/SlhDsa/AArch64/Fors.lean`) from the end of the
subtrees' loop (`top_ok`): for `s = a`, the root is the one subtree root
(`top_eq`); for `s < a`, `levels` over the subtree roots (`top_lt`); then
the root to lane 0 of the lanes `B` (`topFin`). As x86-64's `top_ok`
(`Proof/SlhDsa/X86_64/ForsTop.lean`).
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
open VG.Proof.SlhDsa.X86_64.Fors (node sib acc acc_all sib_lt up_node pick_eq xorB_zero_left)

variable {p : Params}

theorem SC.dxs {S SG AU : Addr} {L dA tt idx : Nat} {t₀ : State} (C : SC p S SG AU L dA tt idx t₀) {o l : Nat}
    (h : o + l ≤ (p.a + 1) * p.n) {R : Region} (hR : Region.Sub R ⟨S, Layout.oSigTmp⟩) :
    Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ R := by
  have hd := C.dA
  refine (C.Gd.sub_left ?_).sub_right hR
  rw [C.AU, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact Offset.sub_base SG (by omega)

/-- The state before the root's copy to lane `B`. -/
structure TopIn (p : Params) (S AU : Addr) (pk a16 sk : List Byte) (kp tt idx : Nat) (t₀ v : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → v.gpr r = t₀.gpr r
  sp : v.sp = t₀.sp
  rd : v.rd = t₀.rd
  wr : v.wr = t₀.wr
  vcs : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (t₀.v r).extractLsb' 0 64
  env : Env p v.mem S pk a16
  skat : SkAt p v.mem S sk
  skp : ∀ j < p.n, v.mem (AU + BitVec.ofNat 64 j) = skv p pk a16 sk kp (tt * 2 ^ p.a + idx) j
  auth : ∀ r < p.a, bytesAt v.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
    node p sk pk a16 kp (tt * 2 ^ (p.a - r) + sib idx r) r
  frame : Frame (subW p S AU) t₀.mem v.mem

/-- What tree `tt`'s heights above its subtrees leave. -/
structure TopP (p : Params) (S AU : Addr) (pk a16 sk : List Byte) (kp tt idx : Nat) (t₀ v : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → v.gpr r = t₀.gpr r
  sp : v.sp = t₀.sp
  rd : v.rd = t₀.rd
  wr : v.wr = t₀.wr
  vcs : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (t₀.v r).extractLsb' 0 64
  env : Env p v.mem S pk a16
  skat : SkAt p v.mem S sk
  skp : ∀ j < p.n, v.mem (AU + BitVec.ofNat 64 j) = skv p pk a16 sk kp (tt * 2 ^ p.a + idx) j
  auth : ∀ r < p.a, bytesAt v.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
    node p sk pk a16 kp (tt * 2 ^ (p.a - r) + sib idx r) r
  root : bytesAt v.mem (at' S (rootAt p.n tt)) p.n = node p sk pk a16 kp tt p.a
  frame : Frame (subW p S AU ++ [⟨at' S (rootAt p.n tt), p.n⟩]) t₀.mem v.mem

theorem pres_ne3 (r : Reg) (hr : r ∈ preserved) : r ∉ [.x10, .x11, .x14] := by
  revert r; decide

/-- The root, at `S + R`, to lane 0 of the lanes `B`. -/
theorem topFin {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte} {t₀ v : State}
    (C : SC p S SG AU L dA tt idx t₀) (h23 : t₀.gpr .x23 = BitVec.ofNat 64 tt) (htk : (tt + 1) * p.n ≤ 1120)
    {R : Nat} (hR : R % 8 = 0) (hR' : 4832 ≤ R) (hR'' : R + p.n ≤ 30144)
    (hI : TopIn p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ v)
    (hroot : bytesAt v.mem (at' S R) p.n = node p sk pk a16 (t₀.gpr .x20).toNat tt p.a) :
    WP isa (.block (rbList p.n R)) v (TopP p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀) := by
  have hz := C.hz
  have hn32 := hz.n32
  have eB : Layout.laneB 0 = 3648 := rfl
  have htn : tt * p.n + p.n ≤ 1120 := by rw [Nat.add_mul, Nat.one_mul] at htk; omega
  have hslot : Region.Sub ⟨at' S (rootAt p.n tt), p.n⟩ ⟨S, Layout.oSigTmp⟩ :=
    Offset.sub_base S (by simp only [rootAt]; rw [eB, show Layout.oSigTmp = 30144 from rfl]; omega)
  refine rootB_ok hz (by rw [hI.cs _ (by decide) (by decide) (by decide) (by decide), C.x19])
    (by rw [hI.cs _ (by decide) (by decide) (by decide) (by decide), h23]) htk hR hR' hR''
    (by rw [hI.wr]; exact C.w) fun u' k' c' f' => ?_
  have dsl : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n →
      ∀ r ∈ [(⟨at' S (rootAt p.n tt), p.n⟩ : Region)], Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ r :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact C.dxs h hslot
  refine ⟨fun r hr h₁ h₂ h₃ => by rw [k'.gpr r (pres_ne3 r hr), hI.cs r hr h₁ h₂ h₃], by rw [k'.sp, hI.sp],
    by rw [k'.rd, hI.rd], by rw [k'.wr, hI.wr], fun r hr => by rw [k'.vcs r hr, hI.vcs r hr],
    env_keep hn32 hI.env f' fun r hr k hk => ?_, sk_keep hI.skat f' (fun r hr => ?_) (by omega),
    fun j hj => ?_, fun r hr => ?_, by rw [c', hroot], ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨disj_scr S (by simp only [rootAt]; rw [laneA_eq, eB]; omega) (by rw [laneA_eq]; omega)
        (by simp only [rootAt]; rw [eB]; omega), ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact disj_scr S (by simp only [rootAt]; rw [eB]; omega) (by rw [eB]; omega)
        (by simp only [rootAt]; rw [eB]; omega)
    · exact disj_scr S (by simp only [rootAt]; rw [laneB_eq, eB]; omega) (by rw [laneB_eq]; omega)
        (by simp only [rootAt]; rw [eB]; omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact disj_scr S (by simp only [rootAt]; rw [eB, show Layout.oSkSeed = 1664 from rfl]; omega)
      (by rw [show Layout.oSkSeed = 1664 from rfl]; omega) (by simp only [rootAt]; rw [eB]; omega)
  · rw [byte_frame f' (fun r hr => (dsl (o := j) (l := 1) (by rw [Nat.add_mul]; omega) r hr)), hI.skp j hj]
  · have hrn : p.n + r * p.n + p.n ≤ (p.a + 1) * p.n := by
      have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega); rw [Nat.succ_mul] at this
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [addr_add, bytesAt_frame f' (dsl hrn) (by omega), ← addr_add]; exact hI.auth r hr
  · exact (hI.frame.mono fun r hr => List.mem_append_left _ hr).trans (f'.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)

/-- After the subtrees' loop, the path below height `s` is the tree's, and the
private key value is the index's. -/
theorem topIn_of {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte} {t₀ t : State}
    (C : SC p S SG AU L dA tt idx t₀) (hI : ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ (2 ^ (p.a - s p.a)) t) :
    (∀ j < p.n, t.mem (AU + BitVec.ofNat 64 j) = skv p pk a16 sk (t₀.gpr .x20).toNat (tt * 2 ^ p.a + idx) j) ∧
    ∀ r < s p.a, bytesAt t.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
      node p sk pk a16 (t₀.gpr .x20).toNat (tt * 2 ^ (p.a - r) + sib idx r) r := by
  have hsa := s_le p.a
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel hsa]
  exact ⟨fun j hj => by rw [hI.skp j hj, hUs, ite_eq_left C.idx],
    fun r hr => by rw [hI.auth r hr]; exact acc_all p sk pk a16 _ C.idx hsa hr⟩

/-- `topHeights` for `s = a`: the one subtree root is the tree's. -/
theorem top_eq {name ln : String} {t4 : Prog isa} {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte}
    {t₀ t : State} (C : SC p S SG AU L dA tt idx t₀) (h23 : t₀.gpr .x23 = BitVec.ofNat 64 tt)
    (htk : (tt + 1) * p.n ≤ 1120) (hc : ¬ s p.a < p.a)
    (hI : ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ (2 ^ (p.a - s p.a)) t) :
    WP isa (Impl.SlhDsa.AArch64.Fors.topHeights ⟨p.n, p.len⟩ p.a name ln t4) t
      (TopP p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀) := by
  have hsa := s_le p.a
  have he : s p.a = p.a := by omega
  have hn32 := C.hz.n32
  obtain ⟨hskp, hauth⟩ := topIn_of C hI
  unfold Impl.SlhDsa.AArch64.Fors.topHeights
  rw [ite_eq_right hc, show Impl.SlhDsa.AArch64.Fors.rootOff p.a = Layout.oRoots from ite_eq_right hc]
  refine WP.seq (MlKem.AArch64.wp_nil ?_)
  refine topFin C h23 htk (R := Layout.oRoots) (by decide) (by decide) (by rw [show Layout.oRoots = 29120 from rfl]; omega)
    ⟨hI.cs, hI.sp, hI.rd, hI.wr, hI.vcs, hI.env, hI.skat, hskp, fun r hr => hauth r (by omega), hI.frame⟩ ?_
  have := hI.roots 0 (Nat.two_pow_pos _)
  rw [Nat.zero_mul, Nat.add_zero, Nat.add_zero, he, Nat.sub_self, Nat.pow_zero, Nat.mul_one] at this
  exact this

theorem bytesAt_chunk {m m' : Mem} {a b : Addr} {X i l : Nat} (h : bytesAt m a X = bytesAt m' b X) (hi : i + l ≤ X) :
    bytesAt m (a + BitVec.ofNat 64 i) l = bytesAt m' (b + BitVec.ofNat 64 i) l := by
  refine bytesAt_ext fun q hq => ?_
  have := congrArg (·.getD (i + q) 0) h
  simp only [getD_bytesAt _ _ (show i + q < X by omega)] at this
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact this

/-- `topHeights` for `s < a`: `levels` over the subtree roots. -/
theorem top_lt {name ln : String} {t4 : Prog isa}
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name t4) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name t4).noFrames = true)
    {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte}
    {t₀ t : State} (C : SC p S SG AU L dA tt idx t₀) (h23 : t₀.gpr .x23 = BitVec.ofNat 64 tt)
    (htk : (tt + 1) * p.n ≤ 1120) (hc : s p.a < p.a)
    (hI : ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ (2 ^ (p.a - s p.a)) t) :
    WP isa (Impl.SlhDsa.AArch64.Fors.topHeights ⟨p.n, p.len⟩ p.a name ln t4) t
      (TopP p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀) := by
  have hz := C.hz
  have hn32 := hz.n32
  have hn16 := hz.n16
  have hsa := s_le p.a
  have hs9 := s_le9 p.a
  have hU := pow_as_le C.a14
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) C.a14
  have h14 : (2 : Nat) ^ 14 = 16384 := rfl
  have hidx : idx < 2 ^ 32 := by have := C.idx; omega
  have htt := C.tt
  rw [Nat.succ_mul] at htt
  have eN : Layout.oN = 12480 := rfl
  have eT : Layout.oSigTmp = 30144 := rfl
  have hUn : 2 ^ (p.a - s p.a) * p.n ≤ 1024 := by have := Nat.mul_le_mul hU hn32; omega
  have hcnt : (2 ^ (p.a - s p.a) + 8) * p.n ≤ 32 * Layout.nodeSlots := by
    rw [show Layout.nodeSlots = 520 from rfl]; have := Nat.mul_le_mul (show 2 ^ (p.a - s p.a) + 8 ≤ 520 by omega) hn32
    omega
  have han : (p.a + 1) * p.n = p.n + s p.a * p.n + (p.a - s p.a) * p.n := by
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' hsa, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hAN : (p.a + 1) * p.n ≤ 15 * 32 := Nat.mul_le_mul (by have := C.a14; omega) hn32
  obtain ⟨hskp, hauth⟩ := topIn_of C hI
  have g : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → t.gpr r = t₀.gpr r := hI.cs
  unfold Impl.SlhDsa.AArch64.Fors.topHeights
  rw [ite_eq_left hc, show Impl.SlhDsa.AArch64.Fors.rootOff p.a = Layout.oN from ite_eq_left hc]
  refine WP.seq (WP.seq (WP.mono (tbc_ok hz C.a14 hc (S := S) (SG := SG) (AU := AU) (L := L) (dA := dA)
    (V4 := tt * 2 ^ p.a) (idx := idx) (pk := pk) (a16 := a16)
    (by rw [g _ (by decide) (by decide) (by decide) (by decide), C.x19])
    (by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact C.kp)
    (by rw [g _ (by decide) (by decide) (by decide) (by decide), C.x21]) hidx
    (by rw [g _ (by decide) (by decide) (by decide) (by decide), C.x24])
    (by rw [g _ (by decide) (by decide) (by decide) (by decide), C.x27]) (by omega)
    (by rw [hI.wr]; exact C.w) (by rw [hI.wr]; exact C.wG) C.AU C.dA C.Gf C.fit C.Gd hI.env) fun v hc => ?_))
  have hv := hc.tb
  refine WP.callV hL.1 hc.pre hc.c₁ hc.c₂ (fun s' h₁ h₂ h₃ _ h₅ _ h₇ hpost => ?_) hLf
  have h2h : (BitVec.ofNat 64 (2 ^ (p.a - s p.a))).toNat = 2 ^ (p.a - s p.a) := by rw [BitVec.toNat_ofNat]; omega
  have hx24 : t.gpr .x24 = AU := by rw [g _ (by decide) (by decide) (by decide) (by decide), C.x24]
  have E0 : (v.callEntry.withRegions [] (tbW p.n p.a S AU)).gpr .x0 = S := by
    rw [entry_gpr _ _ _ (by decide), hv.x0]
  have E1 : (v.callEntry.withRegions [] (tbW p.n p.a S AU)).gpr .x1 = at' S Layout.oN := by
    rw [entry_gpr _ _ _ (by decide), hv.x1]
  have E2 : ((v.callEntry.withRegions [] (tbW p.n p.a S AU)).gpr .x2).toNat = 2 ^ (p.a - s p.a) := by
    rw [entry_gpr _ _ _ (by decide), hv.x2, h2h]
  have E3 : ((v.callEntry.withRegions [] (tbW p.n p.a S AU)).gpr .x3).toNat = s p.a := by
    rw [entry_gpr _ _ _ (by decide), hv.x3, BitVec.toNat_ofNat]; omega
  have E4 : (v.callEntry.withRegions [] (tbW p.n p.a S AU)).gpr .x4 = AU + BitVec.ofNat 64 (p.n + s p.a * p.n) := by
    rw [entry_gpr _ _ _ (by decide), hv.x4, hx24]
  have E5 : ((v.callEntry.withRegions [] (tbW p.n p.a S AU)).gpr .x5).toNat = idx := by
    rw [entry_gpr _ _ _ (by decide), hv.x5, g _ (by decide) (by decide) (by decide) (by decide), C.x21,
      BitVec.toNat_ofNat]; omega
  have hlog : heightsOf (v.callEntry.withRegions [] (tbW p.n p.a S AU)) = p.a - s p.a := by
    simp only [heightsOf]; rw [E2, Nat.log2_two_pow]
  have hV0 : (varAt v.mem S 3 0).toNat = 0 := by rw [hv.v0]; rfl
  have hV1 : (varAt v.mem S 3 1).toNat = tt * 2 ^ p.a := by
    rw [hv.v1, g _ (by decide) (by decide) (by decide) (by decide), C.x27, BitVec.toNat_ofNat]; omega
  have hV2 : (varAt v.mem S 3 2).toNat = FORS_TREE := by rw [hv.v2]; rfl
  have hV3 : (varAt v.mem S 3 3).toNat = (t₀.gpr .x20).toNat := by
    rw [hv.v3, g _ (by decide) (by decide) (by decide) (by decide)]
  simp only [levelsContract, E0, E1, E2, E3, E4, E5, hlog, State.withRegions_mem, State.callEntry_mem,
    hV0, hV1, hV2, hV3, Nat.zero_div] at hpost
  obtain ⟨env₂, root₂, auth₂, fr₂⟩ := hpost pk a16 hc.env
  -- the subtree roots `levels` started from
  have hL0 : ∀ j < 2 ^ (p.a - s p.a), (nodesAt p v.mem (at' S Layout.oN) (2 ^ (p.a - s p.a))).getD j [] =
      node p sk pk a16 (t₀.gpr .x20).toNat (tt * 2 ^ p.a / 2 ^ s p.a + j) (s p.a) := fun j hj => by
    have hjn : j * p.n + p.n ≤ 2 ^ (p.a - s p.a) * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    rw [nodesAt_getD _ _ hj, mul_pow_div tt hsa, ← hI.roots j hj, bytesAt_chunk hv.nodes hjn, at_add]
  have hup := up_node p sk pk a16 (t₀.gpr .x20).toNat (L := nodesAt p v.mem (at' S Layout.oN) (2 ^ (p.a - s p.a)))
    (nodesAt_length _ _ _) (by rw [Nat.add_sub_cancel' hsa]; exact Nat.dvd_mul_left _ _) hL0
  -- what the block and the call change
  have hvar : Region.Sub ⟨at' S (Layout.oVar 3 0), 32⟩ ⟨S, Layout.oSigTmp⟩ :=
    Offset.sub_base S (by rw [var3_eq, eT]; omega)
  have hnod : Region.Sub ⟨at' S Layout.oN, 2 ^ (p.a - s p.a) * p.n⟩ ⟨S, Layout.oSigTmp⟩ :=
    Offset.sub_base S (by rw [eN, eT]; omega)
  have dTB : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n →
      ∀ r ∈ [(⟨at' S Layout.oN, 2 ^ (p.a - s p.a) * p.n⟩ : Region), ⟨at' S (Layout.oVar 3 0), 32⟩],
        Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ r := fun h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact C.dxs h hnod
    · exact C.dxs h hvar
  have dLv : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n → (o + l ≤ p.n + s p.a * p.n) →
      ∀ r ∈ levelsChanges p S (at' S Layout.oN) (2 ^ (p.a - s p.a)) ++
        [⟨AU + BitVec.ofNat 64 (p.n + s p.a * p.n), (p.a - s p.a) * p.n⟩],
        Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ r := fun h h' r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact C.dxs h (lc_low hn32 S hcnt r hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint AU (.inl h') (by omega) (by omega)
  have hA2 : ∀ x y, AU + BitVec.ofNat 64 x + BitVec.ofNat 64 y = AU + BitVec.ofNat 64 (x + y) := addr_add AU
  refine topFin C h23 htk (R := Layout.oN) (by decide) (by decide) (by rw [eN]; omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · intro r hr h₁' h₂' h₃'
    rw [h₅ r hr h₃', hv.keep.gpr r (by revert r; decide), g r hr h₁' h₂' h₃']
  · rw [h₃, hv.keep.sp, hI.sp]
  · rw [h₁, hv.keep.rd, hI.rd]
  · rw [h₂, hv.keep.wr, hI.wr]
  · intro r hr; rw [h₇ r hr, hv.keep.vcs r hr, hI.vcs r hr]
  · exact env₂
  · refine sk_keep (sk_keep hI.skat hv.frame (fun r hr => ?_) (by omega)) fr₂ (fun r hr => ?_) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact disj_scr S (by rw [eN, show Layout.oSkSeed = 1664 from rfl]; omega)
          (by rw [show Layout.oSkSeed = 1664 from rfl]; omega) (by rw [eN]; omega)
      · exact disj_scr S (by rw [var3_eq, show Layout.oSkSeed = 1664 from rfl]; omega)
          (by rw [show Layout.oSkSeed = 1664 from rfl]; omega) (by rw [var3_eq]; omega)
    · rcases List.mem_append.mp hr with hr | hr
      · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
        · exact disj_scr S (by rw [laneA_eq, show Layout.oSkSeed = 1664 from rfl]; omega)
            (by rw [show Layout.oSkSeed = 1664 from rfl]; omega) (by rw [laneA_eq]; omega)
        · exact work_disj S (by rw [show Layout.oSkSeed = 1664 from rfl]; omega) (by rw [show Layout.oSkSeed = 1664 from rfl]; omega)
        · exact disj_scr S (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl, show Layout.oSkSeed = 1664 from rfl]; omega)
            (by rw [show Layout.oSkSeed = 1664 from rfl]; omega)
            (by rw [show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl]; omega)
        · exact disj_scr S (by rw [eN, show Layout.oSkSeed = 1664 from rfl]; omega)
            (by rw [show Layout.oSkSeed = 1664 from rfl]; omega)
            (by rw [eN]; rw [show Layout.nodeSlots = 520 from rfl] at hcnt; omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact (C.dxs (o := p.n + s p.a * p.n) (l := (p.a - s p.a) * p.n) (by omega)
          (Offset.sub_base S (by rw [eT, show Layout.oSkSeed = 1664 from rfl]; omega))).symm
  · intro j hj
    rw [byte_frame fr₂ (dLv (o := j) (l := 1) (by rw [han]; omega) (by omega)),
      byte_frame hv.frame (dTB (o := j) (l := 1) (by rw [han]; omega)), hskp j hj]
  · intro r hr
    have hrn : p.n + r * p.n + p.n ≤ (p.a + 1) * p.n := by
      have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega); rw [Nat.succ_mul] at this
      rw [Nat.add_mul, Nat.one_mul]; omega
    by_cases hrs : r < s p.a
    · have hrs' : p.n + r * p.n + p.n ≤ p.n + s p.a * p.n := by
        have := Nat.mul_le_mul_right p.n (show r + 1 ≤ s p.a by omega); rw [Nat.succ_mul] at this; omega
      rw [hA2, bytesAt_frame fr₂ (dLv hrn hrs') (by omega), bytesAt_frame hv.frame (dTB hrn) (by omega), ← hA2]
      exact hauth r hrs
    · obtain ⟨r', rfl⟩ : ∃ r', r = s p.a + r' := ⟨r - s p.a, by omega⟩
      have hr' : r' < p.a - s p.a := by omega
      have e₁ : AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 ((s p.a + r') * p.n) =
          AU + BitVec.ofNat 64 (p.n + s p.a * p.n) + BitVec.ofNat 64 (r' * p.n) := by
        rw [hA2, hA2, Nat.add_mul, Nat.add_assoc]
      rw [e₁, auth₂ r' hr', ← e₁, hA2, bytesAt_frame hv.frame (dTB hrn) (by omega), ← hA2,
        hI.high (s p.a + r') (by omega) (by omega)]
      obtain ⟨hlen, hget⟩ := hup r' (by omega)
      rw [pick_eq hlen (fun x => node p sk pk a16 (t₀.gpr .x20).toNat (tt * 2 ^ (p.a - (s p.a + r')) + x) (s p.a + r'))
        (fun j hj => by rw [hget j hj, mul_pow_div tt (by omega), Nat.zero_add]), ite_eq_left ⟨Nat.zero_le _, by
          rw [Nat.zero_add, Nat.sub_sub]; exact sib_lt C.idx (by omega)⟩]
      exact xorB_zero_left (forsNode_length hn32 _ _ _ _ _)
  · refine hI.frame.trans ((hv.frame.sub fun x hx => ?_).trans (fr₂.sub fun x hx => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp, Region.sub_prefix (by
          rw [show Layout.nodeSlots = 520 from rfl]; omega)⟩
      · exact ⟨⟨at' S (Layout.oFrame 3), Layout.frameLen⟩, by simp, Offset.sub S
          (by rw [var3_eq, show Layout.oFrame 3 = 1408 from rfl]; omega)
          (by rw [var3_eq, show Layout.oFrame 3 = 1408 from rfl, show Layout.frameLen = 128 from rfl]; omega)⟩
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
        · exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp, Region.sub_prefix hcnt⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨⟨AU, (p.a + 1) * p.n⟩, by simp, Offset.sub_base AU (by omega)⟩
  · rw [root₂]
    have e := (hup (p.a - s p.a) (Nat.le_refl _)).2 0 (by simp)
    rw [Nat.add_sub_cancel' hsa, Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.add_zero] at e
    exact e

/-- `topHeights`, from the end of the subtrees' loop. -/
theorem top_ok {name ln : String} {t4 : Prog isa}
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name t4) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ name t4).noFrames = true)
    {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte}
    {t₀ t : State} (C : SC p S SG AU L dA tt idx t₀) (h23 : t₀.gpr .x23 = BitVec.ofNat 64 tt)
    (htk : (tt + 1) * p.n ≤ 1120)
    (hI : ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ (2 ^ (p.a - s p.a)) t) :
    WP isa (Impl.SlhDsa.AArch64.Fors.topHeights ⟨p.n, p.len⟩ p.a name ln t4) t
      (TopP p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀) := by
  by_cases hc : s p.a < p.a
  · exact top_lt hL hLf C h23 htk hc hI
  · exact top_eq C h23 htk hc hI

end VG.Proof.SlhDsa.AArch64.Fors
