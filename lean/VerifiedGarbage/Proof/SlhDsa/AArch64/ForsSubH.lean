module

-- separate module: the call of `levels` in a FORS subtree, a stage of `forsSign`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsSub
public import VerifiedGarbage.Proof.SlhDsa.ForsSpec
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, the heights of a subtree

`subtreeHeights` (`Impl/SlhDsa/AArch64/Fors.lean`) as a whole: `levels`'s
parameters and arguments (`sb_ok`, `ForsSub.lean`), its precondition
(`sbc_ok`), the call, and the subtree's root copied to the subtree roots
(`rc_ok`): `subH_ok`, as x86-64's `subHeights_ok`
(`Proof/SlhDsa/X86_64/ForsTree.lean`).
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
open VG.Proof.SlhDsa.X86_64.Fors (node sib up_node pick_eq)

variable {p : Params}

theorem entry_gpr (v : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (v.callEntry.withRegions rd wr).gpr r = v.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem s_le9 (a : Nat) : s a ≤ 9 := Nat.min_le_right _ _

theorem s_le (a : Nat) : s a ≤ a := Nat.min_le_left _ _

theorem s_ge {a : Nat} (h : 6 ≤ a) : 6 ≤ s a := Nat.le_min.mpr ⟨h, by decide⟩

/-- The regions of the call of `levels` in a subtree. -/
abbrev sbW (n a : Nat) (S AU : Addr) : List Region :=
  [⟨S, scratchLen⟩, ⟨AU + BitVec.ofNat 64 n, s a * n⟩]

/-- The state before the call of `levels` in a subtree. -/
structure SBC (p : Params) (S AU : Addr) (pk a16 : List Byte) (u v : State) : Prop where
  sb : SB u v S p.n p.a
  env : Env p v.mem S pk a16
  pre : (levelsContract p).pre (v.callEntry.withRegions [] (sbW p.n p.a S AU))
  c₁ : Covers ([] ++ sbW p.n p.a S AU) (v.rd ++ v.wr)
  c₂ : Covers (sbW p.n p.a S AU) v.wr

/-- Frame 3's variables are apart from the lanes. -/
theorem var3_lanes (hn32 : p.n ≤ 32) (S : Addr) :
    ∀ r ∈ [(⟨at' S (Layout.oVar 3 0), 32⟩ : Region)], ∀ k < 4,
      Region.Disjoint ⟨at' S (Layout.laneA k), p.n + 16⟩ r ∧ Region.Disjoint ⟨at' S (Layout.laneB k), p.n + 16⟩ r := by
  intro r hr k hk
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨disj_scr S (by rw [laneA_eq, var3_eq]; omega) (by rw [laneA_eq]; omega) (by rw [var3_eq]; omega),
    disj_scr S (by rw [laneB_eq, var3_eq]; omega) (by rw [laneB_eq]; omega) (by rw [var3_eq]; omega)⟩

/-- The first block of `subtreeHeights`, and `levels`'s precondition after it. -/
theorem sbc_ok (hz : Sz p) {S SG AU : Addr} {L dA U2 V4 idx : Nat} {pk a16 : List Byte} {u : State}
    (h19 : u.gpr .x19 = S) (hKP : (u.gpr .x20).toNat < 2 ^ 32) (h21 : u.gpr .x21 = BitVec.ofNat 64 idx)
    (hidx : idx < 2 ^ 32) (h24 : u.gpr .x24 = AU) (h25 : u.gpr .x25 = BitVec.ofNat 64 U2)
    (h27 : u.gpr .x27 = BitVec.ofNat 64 V4) (hX : V4 + U2 < 2 ^ 32)
    (hw : (⟨S, 65536⟩ : Region) ∈ u.wr) (hwG : (⟨SG, L⟩ : Region) ∈ u.wr) (hAU : AU = SG + BitVec.ofNat 64 dA)
    (hdA : dA + p.n + s p.a * p.n ≤ L) (hGf : SG.toNat + L ≤ 2 ^ 64) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (hGd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩) (hs1 : 1 ≤ s p.a) (hE : Env p u.mem S pk a16) :
    WP isa (.block (sbList p.n p.a)) u (SBC p S AU pk a16 u) := by
  have hn32 := hz.n32
  have hs9 := s_le9 p.a
  have hP := pow_s_le p.a
  refine sb_ok hz h19 hw fun v hv => ?_
  have hve : Env p v.mem S pk a16 := env_keep hn32 hE hv.frame (var3_lanes hn32 S)
  have h2h : (BitVec.ofNat 64 (2 ^ s p.a)).toNat = 2 ^ s p.a := by rw [BitVec.toNat_ofNat]; omega
  have hlog : heightsOf (v.callEntry.withRegions [] (sbW p.n p.a S AU)) = s p.a := by
    simp only [heightsOf]; rw [entry_gpr _ _ _ (by decide), hv.x2, h2h, Nat.log2_two_pow]
  have hsn : 1 ≤ s p.a * p.n := Nat.mul_pos hs1 (by have := hz.n16; omega)
  have hAUn : AU + BitVec.ofNat 64 p.n = at' SG (dA + p.n) := by
    rw [hAU, at', BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hsub : Region.Sub ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩ ⟨SG, L⟩ := by
    rw [hAUn]; exact Offset.sub_base SG (by omega)
  have hx4 : (v.callEntry.withRegions [] (sbW p.n p.a S AU)).gpr .x4 = AU + BitVec.ofNat 64 p.n := by
    rw [entry_gpr _ _ _ (by decide), hv.x4, h24]
  have hx0 : (v.callEntry.withRegions [] (sbW p.n p.a S AU)).gpr .x0 = S := by
    rw [entry_gpr _ _ _ (by decide), hv.x0]
  have hvm : ∀ i, varAt (v.callEntry.withRegions [] (sbW p.n p.a S AU)).mem S 3 i = varAt v.mem S 3 i := fun _ => rfl
  have hc : Covers (sbW p.n p.a S AU) v.wr := Covers.of_sub fun r hr => by
    rw [hv.keep.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hw, 0, scr0 S, by simp [scratchLen]⟩
    · exact ⟨_, hwG, dA + p.n, hAUn, by omega⟩
  refine ⟨hv, hve, ⟨?_, ⟨pk, a16, by rw [hx0]; exact hve⟩,
    by rw [hx0, entry_gpr _ _ _ (by decide), hv.x1], by rw [hlog]; exact hs1,
    by rw [hlog, entry_gpr _ _ _ (by decide), hv.x3]; simp; omega,
    by rw [hlog, entry_gpr _ _ _ (by decide), hv.x2, h2h],
    by rw [entry_gpr _ _ _ (by decide), hv.x2, h2h, show Layout.nodeSlots = 520 from rfl]
       have := Nat.mul_le_mul (show 2 ^ s p.a + 8 ≤ 520 by omega) hn32; omega,
    by rw [entry_gpr _ _ _ (by decide), hv.x5, h21, BitVec.toNat_ofNat]; omega,
    by rw [hx0, hvm, hv.v0, h25, BitVec.toNat_ofNat]; omega,
    by rw [hx0, hvm, hv.v1, h27, h25, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]; omega,
    by rw [hx0, hvm, hv.v2]; decide,
    by rw [hx0, hvm, hv.v3]; exact hKP⟩, by rw [List.nil_append]; exact Covers.right hc, hc⟩
  rw [hx0, hx4, hlog]
  refine ⟨rfl, rfl, hfit, ?_, hGd.sub_left hsub, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩
  show (AU + BitVec.ofNat 64 p.n).toNat + s p.a * p.n ≤ 2 ^ 64
  rw [hAUn, toNat_at (by omega)]; omega

/-! ## The root to the subtree roots -/

/-- The last block of `subtreeHeights`. -/
abbrev rcList (n a : Nat) : List Instr :=
  ([.lsr .x .x10 .x25 (s a)] : List Instr) ++ Impl.SlhDsa.AArch64.mulN n .x10 .x11 ++
    ([.add .x .x10 .x10 .x19] : List Instr) ++ Impl.SlhDsa.AArch64.copyWords .x10 Layout.oRoots .x19 Layout.oN (n / 8)

theorem ushr_ofNat {x : Nat} (hx : x < 2 ^ 64) (k : Nat) :
    BitVec.ofNat 64 x >>> k = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

/-- The subtree's root, node 0 at `oN`, to subtree root `U2 / 2^s`. -/
theorem rc_ok (hz : Sz p) {S : Addr} {U2 : Nat} {u : State} (h19 : u.gpr .x19 = S)
    (h25 : u.gpr .x25 = BitVec.ofNat 64 U2) (hU : U2 < 2 ^ 32) (hR : U2 / 2 ^ s p.a < 32)
    (hw : (⟨S, 65536⟩ : Region) ∈ u.wr) {Q : State → Prop}
    (k : ∀ u', Keep [.x10, .x11, .x14] u u' →
      bytesAt u'.mem (at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n)) p.n = bytesAt u.mem (at' S Layout.oN) p.n →
      Frame [⟨at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n), p.n⟩] u.mem u'.mem → Q u') :
    WP isa (.block (rcList p.n p.a)) u Q := by
  have hn32 := hz.n32
  have e8 : 8 * (p.n / 8) = p.n := by have := hz.n8; omega
  have eN : Layout.oN = 12480 := rfl
  have eR : Layout.oRoots = 29120 := rfl
  have hs9 := s_le9 p.a
  have hRn : U2 / 2 ^ s p.a * p.n + p.n ≤ 1024 := by
    have := Nat.mul_le_mul (show U2 / 2 ^ s p.a + 1 ≤ 32 by omega) hn32
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  rw [← List.append_nil (rcList p.n p.a)]
  simp only [rcList, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_lsr (by omega) fun t₁ u₁ => mulN_ok hz.nv (by decide) fun t₂ o₂ e₂ => wp_addr fun t₃ u₃ => ?_
  have k₃ : Keep [.x10, .x11] u t₃ := (((upK u₁).trans o₂.keep).trans (upK u₃)).mono (by simp)
  have hm₃ : t₃.mem = u.mem := by rw [u₃.mem, o₂.mem, u₁.mem]
  have g19 : t₃.gpr .x19 = S := by rw [k₃.get .x19, h19]
  have hx₃ : t₃.gpr .x10 = at' S (U2 / 2 ^ s p.a * p.n) := by
    rw [u₃.gpr, e₂, u₁.gpr, o₂.get .x19, u₁.other _ (by decide), h19, h25, ushr_ofNat (by omega),
      BitVec.ofNat_mul_ofNat, at', BitVec.add_comm]
  have hw₃ : (⟨S, 65536⟩ : Region) ∈ t₃.wr := by rw [k₃.wr]; exact hw
  have hdst : t₃.gpr .x10 + BitVec.ofNat 64 Layout.oRoots = at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n) := by
    rw [hx₃, at_add, Nat.add_comm]
  refine copyWords_ok ⟨by decide, by decide, ⟨by rw [eN] <;> omega, by rw [eN] <;> omega⟩,
      ⟨by rw [eR] <;> omega, by rw [eR] <;> omega⟩,
      by rw [g19, e8]; exact in_scr' hw₃ (by rw [eN] <;> omega),
      by rw [hdst, e8]; exact in_scr hw₃ (by rw [eR] <;> omega),
      by rw [hdst, g19, e8]; exact disj_scr S (by rw [eN, eR]; omega) (by rw [eR] <;> omega) (by rw [eN] <;> omega)⟩
    fun u' k' f' c' => WP.block_nil (k u' ((k₃.trans k').mono (by simp)) ?_ ?_)
  · rw [hdst, e8] at c'; rw [c', g19, hm₃]
  · rw [hdst, e8, hm₃] at f'; exact f'

/-! ## The heights of a subtree -/

/-- What a subtree's heights leave. -/
structure SubHP (p : Params) (S AU : Addr) (pk a16 sk : List Byte) (kp V4 U2 idx : Nat) (u u' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r
  sp : u'.sp = u.sp
  rd : u'.rd = u.rd
  wr : u'.wr = u.wr
  vcs : ∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64
  env : Env p u'.mem S pk a16
  root : bytesAt u'.mem (at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n)) p.n =
    node p sk pk a16 kp ((V4 + U2) / 2 ^ s p.a) (s p.a)
  auth : ∀ r < s p.a, bytesAt u'.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
    xorB (bytesAt u.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n)
      (if U2 / 2 ^ r ≤ sib idx r ∧ sib idx r < U2 / 2 ^ r + 2 ^ (s p.a - r) then
        node p sk pk a16 kp (V4 / 2 ^ r + sib idx r) r else toByte 0 p.n)
  frame : Frame (levelsChanges p S (at' S Layout.oN) (2 ^ s p.a) ++
    [⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩, ⟨at' S (Layout.oVar 3 0), 32⟩,
      ⟨at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n), p.n⟩]) u.mem u'.mem

theorem div_add_dvd {a b c : Nat} (h : c ∣ a) : (a + b) / c = a / c + b / c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  obtain ⟨d, rfl⟩ := h
  rw [Nat.mul_add_div hc, Nat.mul_div_cancel_left _ hc]

/-- A leaf, as the code computes it, is the specification's. -/
theorem leafv_node {pk a16 sk : List Byte} (h16 : a16.length = 16) {kp : Nat} (hkp : kp < 2 ^ 32) (x : Nat) :
    leafv p pk a16 sk kp x = node p sk pk a16 kp x 0 := by
  rw [node, forsNode_zero, X86_64.Fors.node_adrs h16, forsSkGen, X86_64.Fors.sk_adrs h16 kp hkp]
  rfl

theorem nodesAt_getD (m : Mem) (a : Addr) {c i : Nat} (hi : i < c) :
    (nodesAt p m a c).getD i [] = bytesAt m (a + BitVec.ofNat 64 (i * p.n)) p.n := by
  simp [nodesAt, List.getD_eq_getElem?_getD, hi]

theorem nodesAt_length (m : Mem) (a : Addr) (c : Nat) : (nodesAt p m a c).length = c := by
  simp [nodesAt]

/-- `subtreeHeights`: `levels` over the subtree's `2^s` leaves, its root to the
subtree roots. -/
theorem subH_ok (hz : Sz p) {t4name ln : String} {t4 : Prog isa}
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4).noFrames = true)
    {S SG AU : Addr} {L dA U2 V4 idx : Nat} {pk a16 sk : List Byte} {u : State}
    (h19 : u.gpr .x19 = S) (hKP : (u.gpr .x20).toNat < 2 ^ 32) (h21 : u.gpr .x21 = BitVec.ofNat 64 idx)
    (hidx : idx < 2 ^ 32) (h24 : u.gpr .x24 = AU) (h25 : u.gpr .x25 = BitVec.ofNat 64 U2)
    (h27 : u.gpr .x27 = BitVec.ofNat 64 V4) (hX : V4 + U2 < 2 ^ 32)
    (hw : (⟨S, 65536⟩ : Region) ∈ u.wr) (hwG : (⟨SG, L⟩ : Region) ∈ u.wr) (hAU : AU = SG + BitVec.ofNat 64 dA)
    (hdA : dA + p.n + s p.a * p.n ≤ L) (hGf : SG.toNat + L ≤ 2 ^ 64) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (hGd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩) (hs1 : 1 ≤ s p.a) (hE : Env p u.mem S pk a16)
    (hdv4 : 2 ^ s p.a ∣ V4) (hdv2 : 2 ^ s p.a ∣ U2) (hR : U2 / 2 ^ s p.a < 32)
    (hN : ∀ i < 2 ^ s p.a, bytesAt u.mem (at' S (Layout.oN + i * p.n)) p.n =
      leafv p pk a16 sk (u.gpr .x20).toNat (V4 + U2 + i)) :
    WP isa (Impl.SlhDsa.AArch64.Fors.subtreeHeights ⟨p.n, p.len⟩ p.a t4name ln t4) u
      (SubHP p S AU pk a16 sk (u.gpr .x20).toNat V4 U2 idx u) := by
  have hn32 := hz.n32
  have hs9 := s_le9 p.a
  have hP := pow_s_le p.a
  have eN : Layout.oN = 12480 := rfl
  have eR : Layout.oRoots = 29120 := rfl
  have eT : Layout.oSigTmp = 30144 := rfl
  have h16 : a16.length = 16 := env_a16 hE
  unfold Impl.SlhDsa.AArch64.Fors.subtreeHeights
  refine WP.seq (WP.mono (sbc_ok hz h19 hKP h21 hidx h24 h25 h27 hX hw hwG hAU hdA hGf hfit hGd hs1 hE) fun v hc => ?_)
  have hv := hc.sb
  refine WP.seq (WP.callV hL.1 hc.pre hc.c₁ hc.c₂ (fun s' h₁ h₂ h₃ _ h₅ _ h₇ hpost => ?_) hLf)
  have h2h : (BitVec.ofNat 64 (2 ^ s p.a)).toNat = 2 ^ s p.a := by rw [BitVec.toNat_ofNat]; omega
  have E0 : (v.callEntry.withRegions [] (sbW p.n p.a S AU)).gpr .x0 = S := by
    rw [entry_gpr _ _ _ (by decide), hv.x0]
  have E1 : (v.callEntry.withRegions [] (sbW p.n p.a S AU)).gpr .x1 = at' S Layout.oN := by
    rw [entry_gpr _ _ _ (by decide), hv.x1]
  have E2 : ((v.callEntry.withRegions [] (sbW p.n p.a S AU)).gpr .x2).toNat = 2 ^ s p.a := by
    rw [entry_gpr _ _ _ (by decide), hv.x2, h2h]
  have E3 : ((v.callEntry.withRegions [] (sbW p.n p.a S AU)).gpr .x3).toNat = 0 := by
    rw [entry_gpr _ _ _ (by decide), hv.x3]; rfl
  have E4 : (v.callEntry.withRegions [] (sbW p.n p.a S AU)).gpr .x4 = AU + BitVec.ofNat 64 p.n := by
    rw [entry_gpr _ _ _ (by decide), hv.x4, h24]
  have E5 : ((v.callEntry.withRegions [] (sbW p.n p.a S AU)).gpr .x5).toNat = idx := by
    rw [entry_gpr _ _ _ (by decide), hv.x5, h21, BitVec.toNat_ofNat]; omega
  have hlog : heightsOf (v.callEntry.withRegions [] (sbW p.n p.a S AU)) = s p.a := by
    simp only [heightsOf]; rw [E2, Nat.log2_two_pow]
  have hV0 : (varAt v.mem S 3 0).toNat = U2 := by rw [hv.v0, h25, BitVec.toNat_ofNat]; omega
  have hV1 : (varAt v.mem S 3 1).toNat = V4 + U2 := by
    rw [hv.v1, h27, h25, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]; omega
  have hV2 : (varAt v.mem S 3 2).toNat = FORS_TREE := by rw [hv.v2]; rfl
  have hV3 : (varAt v.mem S 3 3).toNat = (u.gpr .x20).toNat := by rw [hv.v3]
  simp only [levelsContract, E0, E1, E2, E3, E4, E5, hlog, State.withRegions_mem, State.callEntry_mem,
    hV0, hV1, hV2, hV3] at hpost
  obtain ⟨env₂, root₂, auth₂, fr₂⟩ := hpost pk a16 hc.env
  -- the registers
  have g : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = u.gpr r := fun r hr h30 => by
    rw [h₅ r hr h30, hv.keep.gpr r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
  have hw' : s'.wr = u.wr := by rw [h₂, hv.keep.wr]
  -- the leaves `levels` started from
  have hL0 : ∀ j < 2 ^ s p.a, (nodesAt p v.mem (at' S Layout.oN) (2 ^ s p.a)).getD j [] =
      node p sk pk a16 (u.gpr .x20).toNat ((V4 + U2) / 2 ^ 0 + j) 0 := fun j hj => by
    rw [nodesAt_getD _ _ hj, at_add, Nat.pow_zero, Nat.div_one, ← leafv_node h16 hKP, ← hN j hj]
    have : (j + 1) * p.n ≤ 512 * 32 := Nat.mul_le_mul (by omega) hn32
    rw [Nat.add_mul, Nat.one_mul] at this
    exact bytesAt_frame hv.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by rw [var3_eq, eN]; omega) (by rw [eN] <;> omega) (by rw [var3_eq]; omega)) (by omega)
  have hup := up_node p sk pk a16 (u.gpr .x20).toNat (L := nodesAt p v.mem (at' S Layout.oN) (2 ^ s p.a))
    (nodesAt_length _ _ _) (by rw [Nat.zero_add]; exact Nat.dvd_add hdv4 hdv2) hL0
  -- the signature is apart from what `levels` and the root copy change
  have hAUn : ∀ o, AU + BitVec.ofNat 64 o = at' SG (dA + o) := fun o => by
    rw [hAU, at', BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hsig : ∀ r < s p.a, Region.Disjoint ⟨AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n), p.n⟩
      ⟨S, Layout.oSigTmp⟩ := fun r hr => by
    have := Nat.mul_le_mul_right p.n (show r + 1 ≤ s p.a by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hAUn]
    exact hGd.sub_left (Offset.sub_base SG (by omega))
  refine rc_ok hz (by rw [g _ (by decide) (by decide), h19]) (by rw [g _ (by decide) (by decide), h25]) (by omega) hR
    (by rw [hw']; exact hw) fun w kw cw fw => ?_
  have hRn : U2 / 2 ^ s p.a * p.n + p.n ≤ 1024 := by
    have := Nat.mul_le_mul (show U2 / 2 ^ s p.a + 1 ≤ 32 by omega) hn32
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hslot : Region.Sub ⟨at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n), p.n⟩ ⟨S, Layout.oSigTmp⟩ :=
    Offset.sub_base S (by rw [eR, eT]; omega)
  have hvar : Region.Sub ⟨at' S (Layout.oVar 3 0), 32⟩ ⟨S, Layout.oSigTmp⟩ :=
    Offset.sub_base S (by rw [var3_eq, eT]; omega)
  refine ⟨fun r hr h30 => by rw [kw.gpr r (notin_of (keep_pres0 r hr)), g r hr h30], by rw [kw.sp, h₃, hv.keep.sp],
    by rw [kw.rd, h₁, hv.keep.rd], by rw [kw.wr, hw'], fun r hr => by rw [kw.vcs r hr, h₇ r hr, hv.keep.vcs r hr],
    env_keep hn32 env₂ fw fun r hr k hk => ?_, ?_, fun r hr => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨disj_scr S (by rw [laneA_eq, eR]; omega) (by rw [laneA_eq]; omega) (by rw [eR] <;> omega),
      disj_scr S (by rw [laneB_eq, eR]; omega) (by rw [laneB_eq]; omega) (by rw [eR] <;> omega)⟩
  · rw [cw, root₂]
    have e := (hup (s p.a) (Nat.le_refl _)).2 0 (by simp)
    rw [Nat.zero_add, Nat.add_zero] at e
    exact e
  · rw [bytesAt_frame fw (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact (hsig r hr).sub_right hslot) (by omega),
      auth₂ r hr, Nat.zero_add,
      bytesAt_frame hv.frame (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact (hsig r hr).sub_right hvar) (by omega)]
    congr 1
    obtain ⟨hlen, hget⟩ := hup r (by omega)
    have hdr : 2 ^ r ∣ V4 := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdv4
    exact pick_eq hlen (fun x => node p sk pk a16 (u.gpr .x20).toNat (V4 / 2 ^ r + x) r) fun j hj => by
      rw [Nat.zero_add] at hget
      rw [hget j hj, div_add_dvd hdr, Nat.add_assoc]
  · refine (hv.frame.mono fun x hx => ?_).trans ((fr₂.mono fun x hx => ?_).trans (fw.mono fun x hx => ?_))
    · simp only [List.mem_singleton] at hx; subst hx; simp
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · simp only [List.mem_singleton] at hx; subst hx; simp
    · simp only [List.mem_singleton] at hx; subst hx; simp

end VG.Proof.SlhDsa.AArch64.Fors
