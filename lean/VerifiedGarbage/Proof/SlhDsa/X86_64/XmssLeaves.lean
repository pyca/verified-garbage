module

-- separate module: the leaves' loop, a stage of `xmssTree`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsCT
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmss
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkDigits
public import VerifiedGarbage.Proof.SlhDsa.Lemmas
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkPath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT

/-!
# SLH-DSA (SHAKE) on x86-64: `xmssTree`, its prologue and its leaves

The trees `xmssTree` computes, as `levels` states them (`upNodes`, `pick`):
the XMSS tree (`xmss_node`, Algorithm 9) and its authentication path
(`xmss_sign`, Algorithm 10). Then the code: the prologue (`tpro_ok`), the
digits (`digits_ok`) and the loop of the leaves (`leaves_ok`), four at a
time by `wotsLeaves4`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.XmssTree

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs saveRegs restoreRegs)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add in_scr in_scr' at_add wp_cmpi)

variable {p : Params}

/-! ## The trees, as `levels` computes them -/

theorem length_treeAdrs {a16 : List Byte} (ha : a16.length = 16) : (treeAdrs a16).length = 32 := by
  simp [treeAdrs, ha, length_toByte]

/-- A cleared address has the key pair address 0. -/
theorem setKeyPairAddress_setTypeAndClear_zero {a : Adrs} (h : a.length = 32) (Y : Nat) :
    setKeyPairAddress (setTypeAndClear a Y) 0 = setTypeAndClear a Y := by
  have h1 := length_setTypeAndClear h Y
  apply ext_getD (by rw [length_setKeyPairAddress h1, h1])
  intro j hj
  rw [length_setKeyPairAddress h1] at hj
  rw [getD_setKeyPairAddress h1, getD_setTypeAndClear h, getD_toByte_zero]
  rcases (show j < 16 ∨ (16 ≤ j ∧ j < 20) ∨ (20 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 28) ∨ (28 ≤ j ∧ j < 32) ∨ 32 ≤ j
    by omega) with hr | hr | hr | hr | hr | hr <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

theorem nodeAdrs_tree {a16 : List Byte} (ha : a16.length = 16) (z j : Nat) :
    nodeAdrs a16 TREE 0 z j = setTreeIndex (setTreeHeight (setTypeAndClear (treeAdrs a16) TREE) z) j := by
  rw [nodeAdrs, setKeyPairAddress_setTypeAndClear_zero (length_treeAdrs ha)]

/-- The leaves of an XMSS tree. -/
abbrev leaf (p : Params) (skSeed pkSeed a16 : List Byte) (j : Nat) : List Byte :=
  xmssNode p skSeed j 0 pkSeed (treeAdrs a16)

theorem leaf_eq (skSeed pkSeed a16 : List Byte) (j : Nat) :
    wotsPkGen p skSeed pkSeed (wotsAdrs a16 j) = leaf p skSeed pkSeed a16 j := by
  rw [leaf, xmssNode_zero]; rfl

/-- The nodes `levels` computes `r` heights above the nodes of height `z` of
an XMSS tree: those of height `z + r`. -/
theorem upNodes_xmss {a16 : List Byte} (ha : a16.length = 16) (skSeed pkSeed : List Byte) :
    ∀ (r z k : Nat), upNodes p pkSeed a16 TREE 0 0 z
      ((List.range (2 ^ (k + r))).map fun j => xmssNode p skSeed j z pkSeed (treeAdrs a16)) r =
      (List.range (2 ^ k)).map fun j => xmssNode p skSeed j (z + r) pkSeed (treeAdrs a16)
  | 0, z, k => rfl
  | r + 1, z, k => by
    rw [upNodes, show z + (r + 1) = z + 1 + r by omega, ← upNodes_xmss ha skSeed pkSeed r (z + 1) k]
    refine congrArg (fun L => upNodes p pkSeed a16 TREE 0 0 (z + 1) L r) ?_
    rw [List.length_map, List.length_range, show k + (r + 1) = k + r + 1 by omega,
      show 2 ^ (k + r + 1) / 2 = 2 ^ (k + r) by rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]]
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    have h2 : 2 * j + 1 < 2 ^ (k + r + 1) := by rw [Nat.pow_succ]; omega
    rw [Nat.zero_div, Nat.zero_add, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_map, List.getElem?_range (by omega), List.getElem?_range h2,
      Option.map_some, Option.map_some, Option.getD_some, Option.getD_some, xmssNode_succ, nodeAdrs_tree ha]

/-- The node of the authentication path at height `r` that `levels` picks. -/
theorem pick_xmss {f : Nat → List Byte} {r idx : Nat} (hr : r < p.hp) (hidx : idx < 2 ^ p.hp) :
    pick p.n ((List.range (2 ^ (p.hp - r))).map f) (0 / 2 ^ (0 + r)) idx (0 + r) = f (idx / 2 ^ r ^^^ 1) := by
  have hq : idx / 2 ^ r < 2 ^ (p.hp - r) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel (by omega)]; exact hidx
  have hx : idx / 2 ^ r ^^^ 1 < 2 ^ (p.hp - r) :=
    Nat.xor_lt_two_pow hq (Nat.lt_of_lt_of_le (show 1 < 2 ^ 1 by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  simp only [pick, Nat.zero_div, Nat.zero_add, List.length_map, List.length_range, Nat.zero_le, true_and, hx,
    ↓reduceIte, Nat.sub_zero]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx, Option.map_some, Option.getD_some]

theorem xorB_zero {x : List Byte} {k : Nat} (h : x.length = k) : xorB (List.replicate k 0) x = x := by
  subst h
  induction x with
  | nil => rfl
  | cons a x ih => simp only [xorB, List.length_cons, List.replicate_succ, List.zipWith_cons_cons] at ih ⊢; rw [ih]; simp

/-! ## The prologue -/

/-- After `pro`. -/
structure TPro (s t : State) : Prop where
  bx : t.gpr .rbx = s.gpr .rdi
  r12 : t.gpr .r12 = s.gpr .rsi
  r13 : t.gpr .r13 = s.gpr .rdx
  r15 : t.gpr .r15 = s.gpr .rdi + BitVec.ofNat 64 Layout.oMsg
  sp : t.gpr .rsp = s.gpr .rsp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  saved : ∀ i < 6, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 1 i)) 64 = s.gpr (savedRegs.getD i .rbx)
  frame : Frame [⟨at' (s.gpr .rdi) (Layout.oSave 1 0), 48⟩] s.mem t.mem

theorem tpro_ok {s : State} (hw : (⟨s.gpr .rdi, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block Impl.SlhDsa.X86_64.Xmss.pro) s (TPro s) := by
  have hc : ∀ j < 6, Region.Contains ⟨at' (s.gpr .rdi) (Layout.oSave 1 0), 48⟩ (at' (s.gpr .rdi) (2528 + 8 * j)) 8 :=
    fun j hj => by
      rw [oSave1, show at' (s.gpr .rdi) (2528 + 8 * j) = at' (s.gpr .rdi) (2528 + 8 * 0) + BitVec.ofNat 64 (8 * j) by
        rw [at_add]]
      exact Offset.contains_base _ (by omega) (by omega)
  unfold Impl.SlhDsa.X86_64.Xmss.pro
  refine WP.block_append (WP.mono (Levels.wp_rangeMap (P := fun j t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ i < j, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 1 i)) 64 = s.gpr (savedRegs.getD i .rbx)) ∧
      Frame [⟨at' (s.gpr .rdi) (Layout.oSave 1 0), 48⟩] s.mem t.mem) 6
    ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩ fun j hj t ⟨g, r, w, sv, f⟩ => ?_) fun t ht => ?_)
  · refine wp_store (a := at' (s.gpr .rdi) (Layout.oSave 1 j)) (by rw [ea_at, g]) (by
      rw [w, oSave1]; exact in_scr hw (by omega)) fun t' g' m' r' w' => WP.block_nil ?_
    refine ⟨by rw [g', g], by rw [r', r], by rw [w', w], fun i hi => ?_, ?_⟩
    · rw [m']
      by_cases e : i = j
      · subst e; rw [Mem.readW_writeW_self64, g]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by rw [oSave1, oSave1]; omega) (by rw [oSave1]; omega)
          (by rw [oSave1]; omega)) (by decide), sv i (by omega)]
    · rw [m']
      exact f.writeW (List.mem_singleton_self _) _ (by rw [oSave1]; exact hc j (by omega))
  obtain ⟨g, r, w, sv, f⟩ := ht
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_mov fun t₄ u₄ => wp_addi fun t₅ u₅ => ?_
  refine WP.block_nil ?_
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, r], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, w],
    fun i hi => by rw [hm₅]; exact sv i hi, by rw [hm₅]; exact f⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, g]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g]
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g,
      sx_ofNat (by rw [show Layout.oMsg = 30496 from rfl]; omega)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g]

/-! ## Calls -/

/-- The regions of a call from a state with the stack pointer of `σ`, of
`stk` bytes of stack, on `scratch` and the part `O'` of `σ`'s buffer. -/
theorem regions_call {stack stk : Nat} {σ v : State} {S : Addr} {O O' : Region} (hR : Regions stack σ S [] O)
    (hsub : Region.Sub O' O) (hfit : O'.base.toNat + O'.len ≤ 2 ^ 64) (hsp : v.gpr .rsp = σ.gpr .rsp)
    (hst : stk + 8 ≤ stack) (hs : stack < 2 ^ 64) :
    Regions stk (v.callEntry.withRegions [] [⟨S, scratchLen⟩, O']) S [] O' := by
  have hret : retR (v.callEntry.withRegions [] [⟨S, scratchLen⟩, O']) = below (σ.gpr .rsp) 8 := by
    simp [retR, State.callEntry_rsp, hsp]
  have h8 : Region.Sub (below (σ.gpr .rsp) 8) (below (σ.gpr .rsp) stack) := below_sub (by omega) hs
  have hc : Region.Sub (below ((v.callEntry.withRegions [] [⟨S, scratchLen⟩, O']).gpr .rsp) stk)
      (below (σ.gpr .rsp) stack) := by
    simp only [State.withRegions_gpr, State.callEntry_rsp, hsp]
    exact fun x hx => below_sub (sp := σ.gpr .rsp) (a := stk + 8) hst hs x (below_callee _ _ x hx)
  refine ⟨rfl, rfl, hR.scr_fit, hfit, hR.out_scr.sub_left hsub, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, ?_, ?_, fun _ h => absurd h List.not_mem_nil, ?_, ?_,
    fun _ h => absurd h List.not_mem_nil⟩
  · rw [hret]; exact hR.stk_scr.sub_left h8
  · rw [hret]; exact (hR.stk_out.sub_left h8).sub_right hsub
  · exact hR.stk_scr.sub_left hc
  · exact (hR.stk_out.sub_left hc).sub_right hsub

/-- The memory on entry to a call: the return address below `rsp`. -/
theorem frame_callEntry (v : State) : Frame [below (v.gpr .rsp) 8] v.mem v.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-! ## The leaves -/

/-- The leaves' invariant after `j` groups of four, from the entry state `σ`. -/
structure LInv (p : Params) (stack : Nat) (σ : State) (S sig : Addr) (pk a sk M : List Byte) (j : Nat)
    (u : State) : Prop where
  bx : u.gpr .rbx = S
  r12 : u.gpr .r12 = σ.gpr .rsi
  r13 : u.gpr .r13 = sig
  r15 : u.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg
  sp : u.gpr .rsp = σ.gpr .rsp
  rd : u.rd = σ.rd
  wr : u.wr = σ.wr
  mx : u.mxcsr.extractLsb' 6 10 = σ.mxcsr.extractLsb' 6 10
  v0 : u.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 (4 * j)
  env : Env p u.mem S pk a
  skat : SkAt p u.mem S sk
  saved : ∀ i < 6, u.mem.readW (at' S (Layout.oSave 1 i)) 64 = σ.gpr (savedRegs.getD i .rbx)
  dig : ∀ i < p.len, digitAt u.mem S i = (wotsDigits p M).getD i 0
  nodes : ∀ k < 4 * j, bytesAt u.mem (at' S (Layout.oN + k * p.n)) p.n = leaf p sk pk a k
  wsig : (σ.gpr .rsi).toNat < 4 * j →
    bytesAt u.mem sig (p.len * p.n) = wotsSign p M sk pk (wotsAdrs a (σ.gpr .rsi).toNat)
  frame : Frame (changes p S ++ [⟨sig, p.xmssSigLen⟩, below (σ.gpr .rsp) stack]) σ.mem u.mem

/-- The parts of `scratch` a call of `wotsLeaves4` keeps. -/
theorem wc_disj (hn32 : p.n ≤ 32) {S sig sp : Addr} {stk kp o l : Nat} {X : Nat}
    (hsig : Region.Disjoint ⟨sig, X⟩ ⟨S, Layout.oSigTmp⟩) (hX : p.len * p.n ≤ X)
    (hstk : (below sp stk).Disjoint ⟨S, 2 ^ 16⟩) (hkp : (kp + 4) * p.n ≤ 32 * Layout.nodeSlots)
    (ho : (2528 ≤ o ∧ o + l ≤ 3296) ∨ (Layout.oDigits ≤ o ∧ o + l ≤ Layout.oSigTmp) ∨
      (Layout.oN ≤ o ∧ o + l ≤ Layout.oN + kp * p.n)) :
    ∀ r ∈ wotsChanges p S kp ++ [⟨sig, p.len * p.n⟩, below sp stk], Region.Disjoint ⟨at' S o, l⟩ r := by
  have eT : Layout.oSigTmp = 31648 := rfl
  have eN : Layout.oN = 12640 := rfl
  have eD : Layout.oDigits = 30368 := rfl
  have eS : Layout.nodeSlots = 520 := rfl
  rw [eS, Nat.add_mul] at hkp
  have hol : o + l ≤ Layout.oSigTmp := by omega
  intro r hr
  simp only [wotsChanges, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hr
  rcases hr with (((rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩) | rfl) | rfl | rfl
  · have h : Region.Disjoint ⟨at' S o, l⟩ ⟨S + BitVec.ofNat 64 0, 1600⟩ :=
      Levels.disj_scr S (o' := 0) (by omega) (by omega) (by omega)
    rwa [← Levels.scr0 S] at h
  · exact Levels.disj_scr S (by omega) (by omega) (by omega)
  · exact Levels.disj_scr S (by rw [show Layout.oVars = 2400 from rfl]; omega) (by omega)
      (by rw [show Layout.oVars = 2400 from rfl]; omega)
  · exact Levels.disj_scr S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega) (by omega)
      (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · exact Levels.disj_scr S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega) (by omega)
      (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)
  · exact Levels.disj_scr S (by omega) (by omega) (by omega)
  · exact ((hsig.sub_left (Region.sub_prefix hX)).sub_right (Offset.sub_base S hol)).symm
  · exact (hstk.sub_right (Offset.sub_base S (by omega))).symm

/-- The regions a call of `wotsLeaves4` changes are among `xmssTree`'s. -/
theorem wc_sub {S sig sp : Addr} {kp stk stack X : Nat} (hkp : (kp + 4) * p.n ≤ 32 * Layout.nodeSlots)
    (hX : p.len * p.n ≤ X) (hstk : stk ≤ stack) (hs : stack < 2 ^ 64) :
    ∀ r ∈ wotsChanges p S kp ++ [⟨sig, p.len * p.n⟩, below sp stk],
      ∃ R ∈ changes p S ++ [⟨sig, X⟩, below sp stack], Region.Sub r R := by
  intro r hr
  simp only [wotsChanges, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hr
  rcases hr with (((rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩) | rfl) | rfl | rfl
  · exact ⟨_, by simp [changes], fun _ h => h⟩
  · exact ⟨_, by simp [changes], fun _ h => h⟩
  · exact ⟨⟨at' S Layout.oVars, 768⟩, by simp [changes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, by simp⟩))), fun _ h => h⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, by simp⟩))), fun _ h => h⟩
  · rw [show Layout.nodeSlots = 520 from rfl, Nat.add_mul] at hkp
    exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp [changes],
      Offset.sub S (by omega) (by rw [show Layout.nodeSlots = 520 from rfl]; omega)⟩
  · exact ⟨_, by simp, Region.sub_prefix hX⟩
  · exact ⟨_, by simp, below_sub hstk hs⟩

/-- `wotsLeaves4`'s precondition at a call from `v`, for the key pairs from `4j`. -/
theorem wots_pre (hz : Wots4.Sz p) {stack stk : Nat} (hst : stk + 8 ≤ stack) (hs : stack < 2 ^ 63) {σ v : State}
    {S sig : Addr} {X : Nat} (hR : Regions stack σ S [] ⟨sig, X⟩) (hX : p.len * p.n ≤ X) {j : Nat}
    (hj : 4 * j + 4 ≤ 512) (h1 : v.gpr .rdi = S) (h2 : v.gpr .rsi = BitVec.ofNat 64 (4 * j))
    (h3 : (v.gpr .rdx).toNat < 2 ^ 32) (h4 : v.gpr .rcx = sig) (hsp : v.gpr .rsp = σ.gpr .rsp)
    (hwr : v.wr = σ.wr) {pk a : List Byte} (he : Env p v.mem S pk a)
    (hd : ∀ i < p.len, digitAt v.mem S i < 16) :
    (wots4Contract p stk).pre (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]) ∧
      Covers ([] ++ [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]) (v.rd ++ v.wr) ∧
      Covers [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩] v.wr := by
  have hn32 := hz.n32
  have hl := hz.len
  have eD : Layout.oDigits = 30368 := rfl
  have hg : ∀ r, r ≠ .rsp → (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]).gpr r = v.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  have h8 : (below (v.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [hsp]; exact hR.stk_scr.sub_left (below_sub (by omega) (by omega))
  have hcm := frame_callEntry v
  have h4j : (BitVec.ofNat 64 (4 * j)).toNat = 4 * j := by rw [BitVec.toNat_ofNat]; omega
  have hcov : Covers [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩] v.wr := Covers.of_sub fun r hr => by
    rw [hwr, hR.wr_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., 0, Levels.scr0 S, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 0, Levels.scr0 sig, by simpa using hX⟩
  refine ⟨⟨?_, ⟨pk, a, ?_⟩, ?_, ?_, ?_, fun i hi => ?_⟩, by rw [List.nil_append]; exact Covers.right hcov, hcov⟩
  · rw [hg _ (by decide), hg _ (by decide), h1, h4]
    exact regions_call hR (Region.sub_prefix hX) (by have := hR.out_fit; simp only at this ⊢; omega) hsp hst
      (by omega)
  · rw [hg _ (by decide), h1, State.withRegions_mem]
    exact Env.of_frame hn32 he (hcm.mono fun r hr => List.mem_append_right _ hr) h8
  · rw [hg _ (by decide), h2, h4j]; omega
  · rw [hg _ (by decide), h2, h4j, show Layout.nodeSlots = 520 from rfl]
    have := Nat.mul_le_mul hj hn32; omega
  · rw [hg _ (by decide)]; exact h3
  · rw [hg _ (by decide), h1, State.withRegions_mem]
    have := hd i hi
    simp only [digitAt] at this ⊢
    rw [Levels.callEntry_byte' v h8 (by omega)]; exact this

theorem wotsSign_eq (M skSeed pkSeed a16 : List Byte) (idx : Nat) :
    wotsSign p M skSeed pkSeed (wotsAdrs a16 idx) =
      (List.range p.len).flatMap fun i => wotsChainAt p skSeed pkSeed a16 idx i ((wotsDigits p M).getD i 0) := rfl

/-- A group of four leaves, from the invariant after `j` groups. -/
theorem leaf_step (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name wn : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hhp9 : p.hp ≤ 9)
    {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions stack σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .rsi).toNat < 2 ^ 32)
    {j : Nat} (hj : 4 * (j + 1) ≤ 2 ^ p.hp) {u : State} (hI : LInv p stack σ S sig pk a sk M j u) :
    WP isa (Impl.SlhDsa.X86_64.Xmss.leafBody (Wots4.L p) p.hp t4name wn T.code) u fun u' =>
      isa.eval .ne u' = some (decide (4 * (j + 1) ≠ 2 ^ p.hp)) ∧ LInv p stack σ S sig pk a sk M (j + 1) u' := by
  have hn32 := hz.n32
  have hl := hz.len
  have eT : Layout.oSigTmp = 31648 := rfl
  have eN : Layout.oN = 12640 := rfl
  have eD : Layout.oDigits = 30368 := rfl
  have eV : ∀ i, Layout.oVar 1 i = 2576 + 8 * i := fun _ => rfl
  have eSv : ∀ i, Layout.oSave 1 i = 2528 + 8 * i := fun _ => rfl
  have eK : Layout.oSkSeed = 3168 := rfl
  have h512 : 2 ^ p.hp ≤ 512 := by
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have hX : p.len * p.n ≤ p.xmssSigLen := by
    simp only [Params.xmssSigLen, Nat.add_mul]; omega
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ σ.wr := by rw [hR.wr_eq]; simp [scratchLen]
  have hstk : ∀ k ≤ stack, (below (σ.gpr .rsp) k).Disjoint ⟨S, 2 ^ 16⟩ := fun k hk =>
    hR.stk_scr.sub_left (below_sub hk (by omega))
  have hsigd : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, Layout.oSigTmp⟩ := hR.out_scr
  have hkp : (4 * j + 4) * p.n ≤ 32 * Layout.nodeSlots := by
    rw [show Layout.nodeSlots = 520 from rfl]; have := Nat.mul_le_mul (show 4 * j + 4 ≤ 512 by omega) hn32; omega
  have hkp' : (4 * j + 4) * p.n ≤ 16640 := by have := hkp; rw [show Layout.nodeSlots = 520 from rfl] at this; omega
  have hln : p.len * p.n ≤ 2144 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  unfold Impl.SlhDsa.X86_64.Xmss.leafBody
  refine WP.seq (WP.mono_mx rfl (Q := fun v => v.mxcsr = u.mxcsr → WP isa _ v _) (wp_mov fun u₁ e₁ =>
    wp_movm (a := at' S (Layout.oVar 1 0))
    (by rw [Impl.SlhDsa.X86_64.Xmss.var, ea_at, e₁.other _ (by decide), hI.bx])
    (by rw [e₁.rd, e₁.wr, hI.wr]; exact in_scr' hwS (by rw [eV]; omega)) fun u₂ e₂ =>
      wp_mov fun u₃ e₃ => wp_mov fun u₄ e₄ => WP.block_nil fun hmx₄ => ?_) fun _ h hm => h hm)
  -- the call's arguments
  have hm₄ : u₄.mem = u.mem := by rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  have hg₄ : ∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → u₄.gpr g = u.gpr g := fun g h₁ h₂ h₃ h₄ => by
    rw [e₄.other _ h₄, e₃.other _ h₃, e₂.other _ h₂, e₁.other _ h₁]
  have a1 : u₄.gpr .rdi = S := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, hI.bx]
  have a2 : u₄.gpr .rsi = BitVec.ofNat 64 (4 * j) := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, e₁.mem, hI.v0]
  have a3 : u₄.gpr .rdx = σ.gpr .rsi := by
    rw [e₄.other _ (by decide), e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), hI.r12]
  have a4 : u₄.gpr .rcx = sig := by
    rw [e₄.gpr, e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hI.r13]
  have asp : u₄.gpr .rsp = σ.gpr .rsp := by rw [hg₄ _ (by decide) (by decide) (by decide) (by decide), hI.sp]
  have awr : u₄.wr = σ.wr := by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr, hI.wr]
  have ard : u₄.rd = σ.rd := by rw [e₄.rd, e₃.rd, e₂.rd, e₁.rd, hI.rd]
  have hdig : ∀ i < p.len, digitAt u₄.mem S i < 16 := fun i hi => by
    rw [hm₄, hI.dig i hi]; exact wotsDigits_lt p hz.lgw hz.nv M i
  obtain ⟨hpre, hc, hw⟩ := wots_pre hz (stk := 8 + T.stack) (by omega) hs63 hR hX (by omega) a1 a2
    (by rw [a3]; exact hidx) a4 asp awr (by rw [hm₄]; exact hI.env) hdig
  -- the call
  refine WP.seq (Wots4.wots4call_ok hz T t4name wn hpre hc hw fun s' h₁ h₂ h₃ h₄ ⟨s₂, hm₂, _, hpost⟩ h₆ => ?_)
  generalize hE : u₄.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩] = E at hpost
  have hEg : ∀ r, r ≠ .rsp → E.gpr r = u₄.gpr r := fun r h => by
    rw [← hE, State.withRegions_gpr, State.callEntry_gpr _ h]
  have hEm : E.mem = u₄.callEntry.mem := by rw [← hE]; rfl
  have hEsp : E.gpr .rsp = σ.gpr .rsp - 8 := by rw [← hE, State.withRegions_gpr, State.callEntry_rsp, asp]
  have h8 : (below (u₄.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := by rw [asp]; exact hstk 8 (by omega)
  have hcb : ∀ o, o < 2 ^ 16 → E.mem (at' S o) = u.mem (at' S o) := fun o ho => by
    rw [hEm, Levels.callEntry_byte' u₄ h8 ho, hm₄]
  have hcm : Frame [below (σ.gpr .rsp) 8] u.mem E.mem := by rw [hEm, ← hm₄, ← asp]; exact frame_callEntry u₄
  have hcby : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → bytesAt E.mem (at' S o) l = bytesAt u.mem (at' S o) l :=
    fun {o l} h => bytesAt_frame hcm (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hstk 8 (by omega)).sub_right (Levels.sub_scr S h)).symm) (by omega)
  have hEnv : Env p E.mem S pk a := by
    rw [hEm]; exact Env.of_frame hn32 (by rw [hm₄]; exact hI.env)
      ((frame_callEntry u₄).mono fun r hr => List.mem_append_right _ hr) h8
  have hESk : SkAt p E.mem S sk := by
    have h0 := hI.skat
    unfold SkAt at h0 ⊢
    rw [← h0]
    exact hcby (by rw [eK]; omega)
  simp only [wots4Contract] at hpost
  rw [hEg _ (by decide), a1, hEg _ (by decide), a2, hEg _ (by decide), a3, hEg _ (by decide), a4, hEsp] at hpost
  obtain ⟨env₂, nodes₂, sigIn, sigOut, fr₂⟩ := hpost pk a sk hEnv hESk
  have h4j : (BitVec.ofNat 64 (4 * j)).toNat = 4 * j := by rw [BitVec.toNat_ofNat]; omega
  rw [h4j] at nodes₂ sigIn sigOut fr₂
  -- what the call changes, from `u`
  have hF : Frame (wotsChanges p S (4 * j) ++ [⟨sig, p.len * p.n⟩, below (σ.gpr .rsp) (T.stack + 16)]) u.mem s'.mem := by
    rw [← hm₂]
    refine Frame.trans (hcm.sub fun r hr => ?_) (fr₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (σ.gpr .rsp) (T.stack + 16), by simp, below_sub (by omega) (by omega)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by simp, fun _ h => h⟩
        · refine ⟨below (σ.gpr .rsp) (T.stack + 16), by simp, fun x hx => ?_⟩
          exact below_sub (sp := σ.gpr .rsp) (a := 8 + T.stack + 8) (by omega) (by omega) x (below_callee _ _ x hx)
  have hkeep : ∀ {o l : Nat}, ((2528 ≤ o ∧ o + l ≤ 3296) ∨ (Layout.oDigits ≤ o ∧ o + l ≤ Layout.oSigTmp) ∨
      (Layout.oN ≤ o ∧ o + l ≤ Layout.oN + 4 * j * p.n)) →
      ∀ r ∈ wotsChanges p S (4 * j) ++ [⟨sig, p.len * p.n⟩, below (σ.gpr .rsp) (T.stack + 16)],
        Region.Disjoint ⟨at' S o, l⟩ r := fun ho =>
    wc_disj hn32 hsigd hX (hstk _ (by omega)) hkp ho
  -- the tail: the next key pair, and ZF
  have hv0' : s'.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 (4 * j) := by
    rw [Thash4Avx.readW_frame hF (hkeep (.inl ⟨by rw [eV]; omega, by rw [eV]; omega⟩)), hI.v0]
  have hbx' : s'.gpr .rbx = S := by rw [h₃ _ (by simp [calleeSaved]), hg₄ _ (by decide) (by decide) (by decide) (by decide), hI.bx]
  have hwr' : (⟨S, 2 ^ 16⟩ : Region) ∈ s'.wr := by rw [h₂, awr]; exact hwS
  refine WP.mono_mx rfl (Q := fun v => v.mxcsr = s'.mxcsr → _) ?_ fun _ h hm => h hm
  refine wp_movm (a := at' S (Layout.oVar 1 0)) (by rw [Impl.SlhDsa.X86_64.Xmss.var, ea_at, hbx'])
    (in_scr' hwr' (by rw [eV]; omega)) fun t₁ f₁ => wp_addi fun t₂ f₂ => ?_
  have hea : t₂.ea (Impl.SlhDsa.X86_64.Xmss.var 0) = at' S (Layout.oVar 1 0) := by
    rw [Impl.SlhDsa.X86_64.Xmss.var, ea_at, f₂.other _ (by decide), f₁.other _ (by decide), hbx']
  refine wp_store hea (by rw [f₂.wr, f₁.wr]; exact in_scr hwr' (by rw [eV]; omega))
    fun t₃ g₃ m₃ r₃ w₃ => wp_cmpi fun t₄ g₄ m₄ r₄ w₄ z₄ => WP.block_nil fun hmx' => ?_
  have hrax : t₃.gpr .rax = BitVec.ofNat 64 (4 * (j + 1)) := by
    rw [show 4 * (j + 1) = 4 * j + 4 by omega, g₃, f₂.gpr, f₁.gpr, hv0', show BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 by decide,
      BitVec.ofNat_add_ofNat]
  have hm₄' : t₄.mem = s'.mem.writeW (at' S (Layout.oVar 1 0)) (BitVec.ofNat 64 (4 * (j + 1))) := by
    rw [m₄, m₃, ← g₃, hrax, f₂.mem, f₁.mem]
  have hfw : Frame [⟨at' S (Layout.oVar 1 0), 8⟩] s'.mem t₄.mem := by
    rw [hm₄']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hvar : ∀ {o l : Nat}, (o + l ≤ Layout.oVar 1 0 ∨ Layout.oVar 1 0 + 8 ≤ o) → o + l ≤ 2 ^ 16 →
      ∀ r ∈ [(⟨at' S (Layout.oVar 1 0), 8⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Levels.disj_scr S h₁ h₂ (by rw [eV]; omega)
  have h4n : 4 * j * p.n ≤ 16384 := by have := Nat.mul_le_mul (show 4 * j ≤ 512 by omega) hn32; omega
  have hb : ∀ {o l : Nat}, ((2528 ≤ o ∧ o + l ≤ 2576) ∨ (2584 ≤ o ∧ o + l ≤ 3296) ∨
      (Layout.oDigits ≤ o ∧ o + l ≤ Layout.oSigTmp) ∨ (Layout.oN ≤ o ∧ o + l ≤ Layout.oN + 4 * j * p.n)) →
      bytesAt t₄.mem (at' S o) l = bytesAt u.mem (at' S o) l := fun {o l} ho => by
    rw [bytesAt_frame hfw (hvar (by rw [eV]; omega) (by omega)) (by omega),
      bytesAt_frame hF (hkeep (by omega)) (by omega)]
  have hrw : ∀ {o : Nat}, ((2528 ≤ o ∧ o + 8 ≤ 2576) ∨ (2584 ≤ o ∧ o + 8 ≤ 3296)) →
      t₄.mem.readW (at' S o) 64 = u.mem.readW (at' S o) 64 := fun {o} ho => by
    rw [Thash4Avx.readW_frame hfw (hvar (by rw [eV]; omega) (by omega)),
      Thash4Avx.readW_frame hF (hkeep (by omega))]
  have hbyte : ∀ {o : Nat}, ((2528 ≤ o ∧ o + 1 ≤ 2576) ∨ (2584 ≤ o ∧ o + 1 ≤ 3296) ∨
      (Layout.oDigits ≤ o ∧ o + 1 ≤ Layout.oSigTmp)) → t₄.mem (at' S o) = u.mem (at' S o) := fun {o} ho =>
    (hfw _ fun r hr => hvar (by rw [eV]; omega) (by omega) r hr _ (Region.contains_self _ _)).trans
      (hF _ fun r hr => hkeep (by omega) r hr _ (Region.contains_self _ _))
  have hsig1 : ∀ r ∈ [(⟨at' S (Layout.oVar 1 0), 8⟩ : Region)], Region.Disjoint ⟨sig, p.len * p.n⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hsigd.sub_left (Region.sub_prefix hX)).sub_right (Offset.sub_base S (by rw [eV]; omega))
  have hcs : ∀ r ∈ calleeSaved, t₄.gpr r = u.gpr r := fun r hr => by
    have hne : r ≠ .rax := by intro h; subst h; simp [calleeSaved] at hr
    rw [g₄, g₃, f₂.other _ hne, f₁.other _ hne, h₃ r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide) (by decide)
  have hz : (BitVec.ofNat 64 (4 * (j + 1)) - BitVec.ofNat 64 (2 ^ p.hp) == 0) = decide (4 * (j + 1) = 2 ^ p.hp) := by
    by_cases h : 4 * (j + 1) = 2 ^ p.hp
    · rw [h]; simp
    · have hne : BitVec.ofNat 64 (4 * (j + 1)) ≠ BitVec.ofNat 64 (2 ^ p.hp) := fun e => h (by
        have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega)
      have hne' : BitVec.ofNat 64 (4 * (j + 1)) - BitVec.ofNat 64 (2 ^ p.hp) ≠ 0 := fun e => hne (by
        rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 (4 * (j + 1))) (BitVec.ofNat 64 (2 ^ p.hp)), e]; exact BitVec.zero_add _)
      rw [beq_eq_false_iff_ne.mpr hne']; simp [h]
  refine ⟨?_, ⟨by rw [hcs _ (by simp [calleeSaved]), hI.bx], by rw [hcs _ (by simp [calleeSaved]), hI.r12],
    by rw [hcs _ (by simp [calleeSaved]), hI.r13], by rw [hcs _ (by simp [calleeSaved]), hI.r15],
    by rw [hcs _ (by simp [calleeSaved]), hI.sp],
    by rw [r₄, r₃, f₂.rd, f₁.rd, h₁, ard], by rw [w₄, w₃, f₂.wr, f₁.wr, h₂, awr],
    by rw [hmx', h₆, hmx₄, hI.mx], by rw [hm₄', Mem.readW_writeW_self64], ?_, ?_,
    fun i hi => by rw [hrw (.inl ⟨by rw [eSv]; omega, by rw [eSv]; omega⟩)]; exact hI.saved i hi,
    fun i hi => by
      simp only [digitAt]; rw [hbyte (.inr (.inr ⟨by omega, by rw [eD]; omega⟩))]; exact hI.dig i hi,
    fun k hk => ?_, fun hk => ?_, ?_⟩⟩
  · show t₄.zf.map (!·) = _
    rw [z₄, hrax, sx_ofNat (by omega), hz]; simp
  · refine Env.of_frame hn32 (by rw [← hm₂]; exact env₂) (hfw.sub fun r hr => ?_) (hstk stack (Nat.le_refl _))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨at' S Layout.oVars, 768⟩, by simp [changes], Offset.sub S (by decide) (by decide)⟩
  · have h0 := hI.skat
    unfold SkAt at h0 ⊢
    rw [← h0]; exact hb (.inr (.inl ⟨by rw [eK]; omega, by rw [eK]; omega⟩))
  · by_cases hk' : k < 4 * j
    · rw [hb (.inr (.inr (.inr ⟨by omega, by
        have := Nat.mul_le_mul_right p.n (show k + 1 ≤ 4 * j by omega); rw [Nat.add_mul, Nat.one_mul] at this
        omega⟩)))]
      exact hI.nodes k hk'
    · obtain ⟨c, hc4, rfl⟩ : ∃ c, c < 4 ∧ k = 4 * j + c := ⟨k - 4 * j, by omega, by omega⟩
      have hk2 : (4 * j + c + 1) * p.n ≤ (4 * j + 4) * p.n := Nat.mul_le_mul_right _ (by omega)
      rw [bytesAt_frame hfw (hvar (by rw [eV, eN]; omega) (by rw [eN]; rw [Nat.add_mul, Nat.one_mul] at hk2; omega))
        (by omega), ← hm₂, nodes₂ c hc4, leaf_eq]
  · rw [bytesAt_frame hfw hsig1 (by omega)]
    by_cases hin : 4 * j ≤ (σ.gpr .rsi).toNat ∧ (σ.gpr .rsi).toNat < 4 * j + 4
    · rw [← hm₂, Wots4.sig_flat, wotsSign_eq]
      exact flatMap_range_congr fun i hi => by
        rw [sigIn hin i hi]; simp only [digitAt]; rw [hcb _ (by rw [eD]; omega)]; congr 1; exact hI.dig i hi
    · rw [← hm₂, sigOut hin, bytesAt_frame hcm (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hR.stk_out.sub_left (below_sub (by omega) (by omega))).symm.sub_left (Region.sub_prefix hX))
        (by omega)]
      exact hI.wsig (by omega)
  · refine hI.frame.trans ((hF.sub (wc_sub hkp hX (by omega) (by omega))).trans (hfw.sub fun r hr => ?_))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨at' S Layout.oVars, 768⟩, by simp [changes], Offset.sub S (by decide) (by decide)⟩

/-- The loop's invariant, `m` groups before the end. -/
def LI (p : Params) (stack : Nat) (σ : State) (S sig : Addr) (pk a sk M : List Byte) (m : Nat) (s : State) : Prop :=
  ∃ j, m = 2 ^ (p.hp - 2) - j ∧ j < 2 ^ (p.hp - 2) ∧ LInv p stack σ S sig pk a sk M j s

/-- A pass of the leaves' loop. -/
theorem leaves_step (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name wn : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9)
    {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions stack σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .rsi).toNat < 2 ^ 32) :
    ∀ m s, LI p stack σ S sig pk a sk M m s →
      WP isa (Impl.SlhDsa.X86_64.Xmss.leafBody (Wots4.L p) p.hp t4name wn T.code) s fun s' =>
        isa.eval .ne s' = some (decide (m ≠ 1)) ∧
        (decide (m ≠ 1) = false → LInv p stack σ S sig pk a sk M (2 ^ (p.hp - 2)) s') ∧
        (decide (m ≠ 1) = true → m - 1 < m ∧ LI p stack σ S sig pk a sk M (m - 1) s') := by
  have h4 : 2 ^ p.hp = 4 * 2 ^ (p.hp - 2) := by
    rw [show p.hp = p.hp - 2 + 2 by omega, Nat.pow_add, Nat.add_sub_cancel]; omega
  intro m s ⟨j, hm, hj, hI⟩
  refine WP.mono (leaf_step hz T t4name wn hst hs63 hhp9 hR hidx (by omega) hI) fun s' ⟨he, hI'⟩ =>
    ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · rw [he]; congr 1; subst hm; simp only [decide_eq_decide]; omega
  · have : j + 1 = 2 ^ (p.hp - 2) := by simp only [decide_eq_false_iff_not, Decidable.not_not] at hc; omega
    rw [← this]; exact hI'
  · simp only [decide_eq_true_eq] at hc
    exact ⟨by omega, j + 1, by omega, by omega, hI'⟩

/-- The leaves' loop: `2^h′ / 4` groups of four. -/
theorem leaves_ok (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name wn : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9)
    {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions stack σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .rsi).toNat < 2 ^ 32)
    {u : State} (h0 : LInv p stack σ S sig pk a sk M 0 u) :
    WP isa (.loop (Impl.SlhDsa.X86_64.Xmss.leafBody (Wots4.L p) p.hp t4name wn T.code) .ne) u
      (LInv p stack σ S sig pk a sk M (2 ^ (p.hp - 2))) :=
  Levels.wpLoop (fun m => decide (m ≠ 1)) (fun m => m - 1)
    (leaves_step hz T t4name wn hst hs63 hhp hhp9 hR hidx) (2 ^ (p.hp - 2))
    ⟨0, by omega, Nat.one_le_two_pow, h0⟩

theorem pro_digits_nm (L : Layout) :
    (Code.block (Impl.SlhDsa.X86_64.Xmss.pro ++ Impl.SlhDsa.X86_64.Xmss.digits L) : Prog isa).allInstrs
      (fun i => !loadsMxcsr i) = true := by
  simp [Code.allInstrs_eq, instrs, Impl.SlhDsa.X86_64.Xmss.pro, Impl.SlhDsa.X86_64.Xmss.digits,
    Impl.SlhDsa.X86_64.Xmss.digitByte, saveRegs, List.all_flatMap, loadsMxcsr]

/-- The prologue and the digits, from `xmssTree`'s precondition: the leaves'
invariant before the first group. -/
theorem entry_ok (hz : Wots4.Sz p) {stack : Nat} {σ : State} {S : Addr} (hS : σ.gpr .rdi = S)
    (hR : Regions stack σ S [] ⟨σ.gpr .rdx, p.xmssSigLen⟩) {pk a sk : List Byte} (hE : Env p σ.mem S pk a)
    (hsk : SkAt p σ.mem S sk) {Q : State → Prop}
    (k : ∀ u, LInv p stack σ S (σ.gpr .rdx) pk a sk (bytesAt σ.mem (at' S Layout.oMsg) p.n) 0 u → Q u) :
    WP isa (.block (Impl.SlhDsa.X86_64.Xmss.pro ++ Impl.SlhDsa.X86_64.Xmss.digits (Wots4.L p))) σ Q := by
  have hn32 := hz.n32
  have eD : Layout.oDigits = 30368 := rfl
  have eM : Layout.oMsg = 30496 := rfl
  have eV : ∀ i, Layout.oVar 1 i = 2576 + 8 * i := fun _ => rfl
  have eSv : ∀ i, Layout.oSave 1 i = 2528 + 8 * i := fun _ => rfl
  have eK : Layout.oSkSeed = 3168 := rfl
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ σ.wr := by rw [hR.wr_eq]; simp [scratchLen]
  refine WP.mono_mx (pro_digits_nm _) (Q := fun u => u.mxcsr = σ.mxcsr → Q u) ?_ fun _ h hm => h hm
  refine WP.block_append (WP.mono (tpro_ok (by rw [hS]; exact hwS)) fun t ht => ?_)
  have hsv := ht.saved
  have hf₁ := ht.frame
  rw [hS] at hsv hf₁
  rw [← List.append_nil (Impl.SlhDsa.X86_64.Xmss.digits _)]
  have hwt : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [ht.wr]; exact hwS
  refine digits_ok (Wots4.L p) hn32 (S := S) (by rw [ht.bx, hS]) (by rw [ht.r15, hS])
    (fun o ho => in_scr hwt ho) (fun o ho => in_scr hwt ho) (fun o ho => in_scr' hwt ho)
    fun u hm hg hrd hwr => WP.block_nil fun hmx => k u ?_
  -- the memory after the prologue and the digits
  have hf₂ := digits_frame p hn32 t.mem S (15 * 2 * p.n - dsum t.mem S p.n)
  rw [← hm] at hf₂
  have hd₁ : ∀ {o l : Nat}, (o + l ≤ 2528 ∨ 2576 ≤ o) → o + l ≤ 2 ^ 16 →
      ∀ r ∈ [(⟨at' S (Layout.oSave 1 0), 48⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Levels.disj_scr S (by rw [eSv]; omega) h₂ (by rw [eSv]; omega)
  have hd₂ : ∀ {o l : Nat}, (o + l ≤ 2576 ∨ (2592 ≤ o ∧ o + l ≤ Layout.oDigits) ∨ Layout.oDigits + 128 ≤ o) →
      o + l ≤ 2 ^ 16 → ∀ r ∈ [(⟨at' S Layout.oDigits, 128⟩ : Region), ⟨at' S (Layout.oVar 1 0), 16⟩],
        Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Levels.disj_scr S (by omega) h₂ (by rw [eD]; omega)
    · exact Levels.disj_scr S (by rw [eV]; omega) h₂ (by rw [eV]; omega)
  have hsub : ∀ r ∈ [(⟨at' S (Layout.oSave 1 0), 48⟩ : Region), ⟨at' S Layout.oDigits, 128⟩,
      ⟨at' S (Layout.oVar 1 0), 16⟩], ∃ R ∈ changes p S, Region.Sub r R := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨at' S Layout.oVars, 768⟩, by simp [changes], Offset.sub S (by decide) (by decide)⟩
    · exact ⟨_, by simp [changes], fun _ h => h⟩
    · exact ⟨⟨at' S Layout.oVars, 768⟩, by simp [changes], Offset.sub S (by decide) (by decide)⟩
  have hF₀ : Frame (changes p S) σ.mem u.mem :=
    (hf₁.sub fun r hr => hsub r (by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
      (hf₂.sub fun r hr => hsub r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  have hF : Frame (changes p S ++ [⟨σ.gpr .rdx, p.xmssSigLen⟩, below (σ.gpr .rsp) stack]) σ.mem u.mem :=
    hF₀.mono fun r hr => List.mem_append_left _ hr
  have hbt : ∀ {o l : Nat}, (o + l ≤ 2528 ∨ (2592 ≤ o ∧ o + l ≤ Layout.oDigits) ∨ Layout.oDigits + 128 ≤ o) →
      o + l ≤ 2 ^ 16 → bytesAt u.mem (at' S o) l = bytesAt σ.mem (at' S o) l := fun h₁ h₂ => by
    rw [bytesAt_frame hf₂ (hd₂ (by omega) h₂) (by omega), bytesAt_frame hf₁ (hd₁ (by omega) h₂) (by omega)]
  have hg' : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → r ≠ .r11 → u.gpr r = t.gpr r := hg
  refine ⟨by rw [hg' _ (by decide) (by decide) (by decide) (by decide), ht.bx, hS],
    by rw [hg' _ (by decide) (by decide) (by decide) (by decide), ht.r12],
    by rw [hg' _ (by decide) (by decide) (by decide) (by decide), ht.r13],
    by rw [hg' _ (by decide) (by decide) (by decide) (by decide), ht.r15, hS],
    by rw [hg' _ (by decide) (by decide) (by decide) (by decide), ht.sp], by rw [hrd, ht.rd], by rw [hwr, ht.wr],
    by rw [hmx], ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun k hk => absurd hk (by omega),
    fun hk => absurd hk (by omega), hF⟩
  · rw [hm]; simp only [csumMem]
    rw [Mem.readW_writeW_sep (Offset.sep _ (by simp only [eV]; omega) (by simp only [eV]; omega)
      (by simp only [eV]; omega)) (by decide),
      Mem.readW_writeW_self64]; rfl
  · exact Env.of_frame hn32 hE (hF₀.mono fun r hr => List.mem_append_left _ hr) hR.stk_scr
  · unfold SkAt at hsk ⊢; rw [← hsk]; exact hbt (.inr (.inl ⟨by rw [eK]; omega, by rw [eK, eD]; omega⟩)) (by omega)
  · rw [Thash4Avx.readW_frame hf₂ (hd₂ (by rw [eSv]; omega) (by rw [eSv]; omega))]; exact hsv i hi
  · simp only [digitAt]; rw [hm, digits_val p hz.lgw hz.nv t.mem S i hi]
    congr 2
    exact bytesAt_frame hf₁ (hd₁ (by rw [eM]; omega) (by rw [eM]; omega)) (by omega)

end VG.Proof.SlhDsa.X86_64.XmssTree
