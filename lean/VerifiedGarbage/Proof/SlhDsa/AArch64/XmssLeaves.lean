module

-- separate module: the leaves' loop, a stage of `xmssTree`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.XmssDigits
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Impl
public import VerifiedGarbage.Proof.SlhDsa.XmssSpec
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Xmss
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `xmssTree`, its prologue and its leaves

The callees `xmssTree` needs (`Callees`: `wotsLeaves4` and `levels`, with
their contracts and no frames); the prologue and the digits (`entry_ok`),
and the loop of the leaves (`leaves_ok`), four at a time by `wotsLeaves4`,
as on x86-64 (`Proof/SlhDsa/X86_64/XmssLeaves.lean`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Xmss

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.SlhDsa.X86_64.XmssTree (leaf leaf_eq)

variable {p : Params}

/-- What `xmssTree` needs of the functions it calls: their contracts, and no
frames (for `WP.callV`). -/
structure Callees (p : Params) (T : Thash4Impl p.n) (t4name : String) : Prop where
  wots : Verified AArch64.target (Impl.SlhDsa.AArch64.Wots.wotsLeaves4 ⟨p.n, p.len⟩ t4name T.code) (wots4Contract p)
  wotsNF : (Impl.SlhDsa.AArch64.Wots.wotsLeaves4 ⟨p.n, p.len⟩ t4name T.code).noFrames = true
  levels : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p)
  levelsNF : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true

/-! ## The prologue -/

/-- The slots of frame 1, and what they hold. -/
def slots1 : List (Reg × Nat) := [(.x19, 1152), (.x20, 1160), (.x21, 1168), (.x22, 1176), (.x30, 1184)]

theorem pro_eq : Impl.SlhDsa.AArch64.Xmss.pro =
    Spill.saveCode .x0 slots1 ++ ([.addImm .x .x19 .x0 0, .addImm .x .x20 .x1 0, .addImm .x .x21 .x2 0] : List Instr) := rfl

/-- The callee-saved registers `xmssTree` does not save, which its callees keep. -/
def kept : List Reg := [.x23, .x24, .x25, .x26, .x27, .x28]

/-- The slots of frame 1 are in `scratch`, apart from the rest. -/
theorem slots1_in : ∀ q ∈ slots1, 1152 ≤ q.2 ∧ q.2 + 8 ≤ 1192 := by decide

theorem slots1_ok : ∀ q ∈ slots1, q.2 % 8 = 0 ∧ q.2 < 32768 := by decide

/-- The registers `xmssTree` changes for good: what the calling convention
lets it, and its saved ones. -/
theorem saved_keep {σ : State} {S : Addr} {m : Mem} (h : Spill.Saved S σ.gpr slots1 m)
    {rs : List Region} {m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨at' S 1152, 40⟩ r) : Spill.Saved S σ.gpr slots1 m' :=
  h.frame hf fun q hq r hr => (hd r hr).sub_left (by
    have := slots1_in q hq
    exact Offset.sub S this.1 (by omega))

/-! ## The leaves -/

/-- The leaves' invariant after `j` groups of four, from the entry state `σ`. -/
structure LInv (p : Params) (σ : State) (S sig : Addr) (pk a sk M : List Byte) (j : Nat) (u : State) : Prop where
  x19 : u.gpr .x19 = S
  x20 : u.gpr .x20 = σ.gpr .x1
  x21 : u.gpr .x21 = sig
  x22 : u.gpr .x22 = BitVec.ofNat 64 (4 * j)
  kept : ∀ r ∈ kept, u.gpr r = σ.gpr r
  sp : u.sp = σ.sp
  rd : u.rd = σ.rd
  wr : u.wr = σ.wr
  vcs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64
  env : Env p u.mem S pk a
  skat : SkAt p u.mem S sk
  saved : Spill.Saved S σ.gpr slots1 u.mem
  dig : ∀ i < p.len, digitAt u.mem S i = (wotsDigits p M).getD i 0
  nodes : ∀ k < 4 * j, bytesAt u.mem (at' S (Layout.oN + k * p.n)) p.n = leaf p sk pk a k
  wsig : (σ.gpr .x1).toNat < 4 * j →
    bytesAt u.mem sig (p.len * p.n) = wotsSign p M sk pk (wotsAdrs a (σ.gpr .x1).toNat)
  frame : Frame (changes p S ++ [⟨sig, p.xmssSigLen⟩]) σ.mem u.mem

theorem xmssSigLen_eq : p.xmssSigLen = p.len * p.n + p.hp * p.n := by
  simp only [Params.xmssSigLen, Nat.add_mul]

/-- The parts of `scratch` a call of `wotsLeaves4` on the key pairs from `kp` keeps. -/
theorem wc_disj (hn32 : p.n ≤ 32) {S sig : Addr} {kp o l X : Nat}
    (hsig : Region.Disjoint ⟨sig, X⟩ ⟨S, Layout.oSigTmp⟩) (hX : p.len * p.n ≤ X)
    (hkp : (kp + 4) * p.n ≤ 32 * Layout.nodeSlots)
    (ho : (1152 ≤ o ∧ o + l ≤ Layout.oA) ∨ (Layout.oN ≤ o ∧ o + l ≤ Layout.oN + kp * p.n)) :
    ∀ r ∈ wotsChanges p S kp ++ [⟨sig, p.len * p.n⟩], Region.Disjoint ⟨at' S o, l⟩ r := by
  have eT : Layout.oSigTmp = 30144 := rfl
  have eN : Layout.oN = 12480 := rfl
  have eA : Layout.oA = 3136 := rfl
  have eS : Layout.nodeSlots = 520 := rfl
  rw [eS, Nat.add_mul] at hkp
  have hol : o + l ≤ Layout.oSigTmp := by omega
  intro r hr
  simp only [wotsChanges, laneTails, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hr
  rcases hr with (((rfl | rfl) | ⟨k, hk, rfl | rfl⟩) | rfl) | rfl
  · have h : Region.Disjoint ⟨at' S o, l⟩ ⟨at' S 0, workUsed⟩ :=
      disj_scr S (by simp only [workUsed]; omega) (by omega) (by simp only [workUsed]; omega)
    rwa [show at' S 0 = S from (scr0 S).symm] at h
  · exact disj_scr S (by simp only [Layout.oFrame, Layout.oVars, Layout.frameLen]; omega) (by omega)
      (by simp only [Layout.oFrame, Layout.oVars, Layout.frameLen]; omega)
  · exact disj_scr S (by rw [laneA_eq]; simp only [Layout.strideA]; omega) (by omega)
      (by rw [laneA_eq]; simp only [Layout.strideA]; omega)
  · exact disj_scr S (by rw [laneB_eq]; simp only [Layout.strideB]; omega) (by omega)
      (by rw [laneB_eq]; simp only [Layout.strideB]; omega)
  · exact disj_scr S (by omega) (by omega) (by omega)
  · exact ((hsig.sub_left (Region.sub_prefix hX)).sub_right (Offset.sub_base S hol)).symm

/-- The regions a call of `wotsLeaves4` changes are among `xmssTree`'s. -/
theorem wc_sub {S sig : Addr} {kp X : Nat} (hkp : (kp + 4) * p.n ≤ 32 * Layout.nodeSlots)
    (hX : p.len * p.n ≤ X) :
    ∀ r ∈ wotsChanges p S kp ++ [⟨sig, p.len * p.n⟩], ∃ R ∈ changes p S ++ [⟨sig, X⟩], Region.Sub r R := by
  intro r hr
  simp only [wotsChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (((rfl | rfl) | hr) | rfl) | rfl
  · exact ⟨_, by simp [changes], fun _ h => h⟩
  · exact ⟨⟨at' S Layout.oVars, 4 * Layout.frameLen⟩, by simp [changes],
      Offset.sub S (by simp [Layout.oFrame]) (by simp [Layout.oFrame, Layout.oVars, Layout.frameLen])⟩
  · exact ⟨r, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr)), fun _ h => h⟩
  · rw [show Layout.nodeSlots = 520 from rfl, Nat.add_mul] at hkp
    exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp [changes],
      Offset.sub S (by omega) (by rw [show Layout.nodeSlots = 520 from rfl]; omega)⟩
  · exact ⟨_, by simp, Region.sub_prefix hX⟩

/-- The regions of a call on `scratch` and the part `O'` of `σ`'s buffer. -/
theorem regions_call {σ v : State} {S : Addr} {O O' : Region} (hR : Regions σ S [] O)
    (hsub : Region.Sub O' O) (hfit : O'.base.toNat + O'.len ≤ 2 ^ 64) :
    Regions (v.callEntry.withRegions [] [⟨S, scratchLen⟩, O']) S [] O' :=
  ⟨rfl, rfl, hR.scr_fit, hfit, hR.out_scr.sub_left hsub, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩

theorem covers_call {v σ : State} {S : Addr} {O O' : Region} (hR : Regions σ S [] O) (hwr : v.wr = σ.wr)
    {d : Nat} (hO : O'.base = O.base + BitVec.ofNat 64 d) (hl : d + O'.len ≤ O.len) :
    Covers ([] ++ [⟨S, scratchLen⟩, O']) (v.rd ++ v.wr) ∧ Covers [⟨S, scratchLen⟩, O'] v.wr := by
  have hc : Covers [⟨S, scratchLen⟩, O'] v.wr := Covers.of_sub fun r hr => by
    rw [hwr, hR.wr_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, scr0 S, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, d, hO, hl⟩
  exact ⟨by rw [List.nil_append]; exact Covers.right hc, hc⟩

theorem callEntry_gpr' (v : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (v.callEntry.withRegions rd wr).gpr r = v.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- `wotsLeaves4`'s precondition at a call from `v`, for the key pairs from `4j`. -/
theorem wots_pre (hz : Sz p) {σ v : State} {S sig : Addr} {X : Nat} (hR : Regions σ S [] ⟨sig, X⟩)
    (hX : p.len * p.n ≤ X) {j : Nat} (hj : 4 * j + 4 ≤ 512) (h1 : v.gpr .x0 = S)
    (h2 : v.gpr .x1 = BitVec.ofNat 64 (4 * j)) (h3 : (v.gpr .x2).toNat < 2 ^ 32) (h4 : v.gpr .x3 = sig)
    (hwr : v.wr = σ.wr) {pk a : List Byte} (he : Env p v.mem S pk a)
    (hd : ∀ i < p.len, digitAt v.mem S i < 16) :
    (wots4Contract p).pre (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]) ∧
      Covers ([] ++ [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]) (v.rd ++ v.wr) ∧
      Covers [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩] v.wr := by
  have hn32 := hz.n32
  have h4j : (BitVec.ofNat 64 (4 * j)).toNat = 4 * j := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨⟨?_, ⟨pk, a, ?_⟩, ?_, ?_, ?_, fun i hi => ?_⟩, covers_call hR hwr (d := 0) (scr0 sig) (by simpa using hX)⟩
  · rw [callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide), h1, h4]
    exact regions_call hR (Region.sub_prefix hX) (by have := hR.out_fit; simp only at this ⊢; omega)
  · rw [callEntry_gpr' _ _ _ (by decide), h1, State.withRegions_mem, State.callEntry_mem]; exact he
  · rw [callEntry_gpr' _ _ _ (by decide), h2, h4j]; omega
  · rw [callEntry_gpr' _ _ _ (by decide), h2, h4j, show Layout.nodeSlots = 520 from rfl]
    have := Nat.mul_le_mul hj hn32; omega
  · rw [callEntry_gpr' _ _ _ (by decide)]; exact h3
  · rw [callEntry_gpr' _ _ _ (by decide), h1, State.withRegions_mem, State.callEntry_mem]; exact hd i hi

theorem wotsSign_eq (M skSeed pkSeed a16 : List Byte) (idx : Nat) :
    wotsSign p M skSeed pkSeed (wotsAdrs a16 idx) =
      (List.range p.len).flatMap fun i => wotsChainAt p skSeed pkSeed a16 idx i ((wotsDigits p M).getD i 0) := rfl

/-- The `len` chains of a WOTS⁺ signature, `n` bytes each. -/
theorem bytesAt_flat (m : Mem) (a : Addr) (n K : Nat) :
    bytesAt m a (K * n) = (List.range K).flatMap fun i => bytesAt m (a + BitVec.ofNat 64 (i * n)) n := by
  induction K with
  | zero => simp [bytesAt]
  | succ K ih =>
    rw [List.range_succ, List.flatMap_append, ← ih, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Nat.add_mul, Nat.one_mul]
    simp only [bytesAt, List.range_add, List.map_append, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The code of a pass of the leaves' loop. -/
abbrev leafCode (p : Params) (T : Thash4Impl p.n) (t4name wn : String) : Prog isa :=
  Impl.SlhDsa.AArch64.Xmss.leafBody ⟨p.n, p.len⟩ p.hp t4name wn T.code

/-- The arguments of a call of `wotsLeaves4`, after the moves. -/
structure Call1 (p : Params) (σ : State) (S sig : Addr) (j : Nat) (v : State) : Prop where
  x0 : v.gpr .x0 = S
  x1 : v.gpr .x1 = BitVec.ofNat 64 (4 * j)
  x2 : v.gpr .x2 = σ.gpr .x1
  x3 : v.gpr .x3 = sig
  sp : v.sp = σ.sp
  x19 : v.gpr .x19 = S
  x22 : v.gpr .x22 = BitVec.ofNat 64 (4 * j)
  pre : (wots4Contract p).pre (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩])
  c₁ : Covers ([] ++ [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]) (v.rd ++ v.wr)
  c₂ : Covers [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩] v.wr

/-- The moves before a call of `wotsLeaves4`. -/
theorem args_ok (hz : Sz p) (hhp9 : p.hp ≤ 9) {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    {j : Nat} (hj : 4 * (j + 1) ≤ 2 ^ p.hp) {u : State} (hI : LInv p σ S sig pk a sk M j u) :
    WP isa (.block [.addImm .x .x0 .x19 0, .addImm .x .x1 .x22 0, .addImm .x .x2 .x20 0, .addImm .x .x3 .x21 0]) u
      fun v => Call1 p σ S sig j v ∧ (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → v.gpr r = u.gpr r) ∧
        v.mem = u.mem ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.v = u.v := by
  have h512 : 2 ^ p.hp ≤ 512 :=
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have hX : p.len * p.n ≤ p.xmssSigLen := by rw [xmssSigLen_eq]; omega
  refine wp_mov fun u₁ e₁ => wp_mov fun u₂ e₂ => wp_mov fun u₃ e₃ => wp_mov fun u₄ e₄ => WP.block_nil ?_
  have hm₄ : u₄.mem = u.mem := by rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  have hg : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → u₄.gpr r = u.gpr r := fun r h0 h1 h2 h3 => by
    rw [e₄.other _ h3, e₃.other _ h2, e₂.other _ h1, e₁.other _ h0]
  have a1 : u₄.gpr .x0 = S := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, hI.x19]
  have a2 : u₄.gpr .x1 = BitVec.ofNat 64 (4 * j) := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, e₁.other _ (by decide), hI.x22]
  have a3 : u₄.gpr .x2 = σ.gpr .x1 := by
    rw [e₄.other _ (by decide), e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), hI.x20]
  have a4 : u₄.gpr .x3 = sig := by
    rw [e₄.gpr, e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hI.x21]
  have awr : u₄.wr = σ.wr := by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr, hI.wr]
  have hdig : ∀ i < p.len, digitAt u₄.mem S i < 16 := fun i hi => by
    rw [hm₄, hI.dig i hi]
    have := Proof.SlhDsa.wotsDigits_getD_lt (p := p) M i
    simp only [Params.w, hz.lgw] at this; exact this
  obtain ⟨hpre, hc, hw⟩ := wots_pre hz hR hX (by omega) a1 a2 (by rw [a3]; exact hidx) a4 awr
    (by rw [hm₄]; exact hI.env) hdig
  exact ⟨⟨a1, a2, a3, a4, by rw [e₄.sp, e₃.sp, e₂.sp, e₁.sp, hI.sp],
    by rw [hg _ (by decide) (by decide) (by decide) (by decide), hI.x19],
    by rw [hg _ (by decide) (by decide) (by decide) (by decide), hI.x22], hpre, hc, hw⟩, hg, hm₄,
    by rw [e₄.rd, e₃.rd, e₂.rd, e₁.rd], by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr],
    by rw [e₄.v, e₃.v, e₂.v, e₁.v]⟩

/-- `subImm` of a public counter, and the loop's condition after it. -/
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

/-- A group of four leaves, from the invariant after `j` groups. -/
theorem leaf_step (hz : Sz p) (T : Thash4Impl p.n) (t4name wn : String) (hC : Callees p T t4name)
    (hhp9 : p.hp ≤ 9) {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    {j : Nat} (hj : 4 * (j + 1) ≤ 2 ^ p.hp) {u : State} (hI : LInv p σ S sig pk a sk M j u) :
    WP isa (leafCode p T t4name wn) u fun u' =>
      isa.eval (.nonzero .x .x9) u' = some (decide (4 * (j + 1) ≠ 2 ^ p.hp)) ∧
        LInv p σ S sig pk a sk M (j + 1) u' := by
  have hn32 := hz.n32
  have eN : Layout.oN = 12480 := rfl
  have eK : Layout.oSkSeed = 1664 := rfl
  have eD : Layout.oDigits = 1856 := rfl
  have h512 : 2 ^ p.hp ≤ 512 :=
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have hX : p.len * p.n ≤ p.xmssSigLen := by rw [xmssSigLen_eq]; omega
  have hsigd : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, Layout.oSigTmp⟩ := hR.out_scr
  have hkp : (4 * j + 4) * p.n ≤ 32 * Layout.nodeSlots := by
    rw [show Layout.nodeSlots = 520 from rfl]; have := Nat.mul_le_mul (show 4 * j + 4 ≤ 512 by omega) hn32; omega
  have hln : p.len * p.n ≤ 2144 := by rw [hz.len]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  unfold leafCode Impl.SlhDsa.AArch64.Xmss.leafBody
  refine WP.seq (WP.mono (args_ok hz hhp9 hR hidx hj hI) fun v ⟨c1, hg, hmv, hrdv, hwrv, hvv⟩ => ?_)
  refine WP.seq (WP.callV hC.wots.1 c1.pre c1.c₁ c1.c₂ (fun s' h₁ h₂ h₃ _ h₅ _ h₇ hpost => ?_) hC.wotsNF)
  -- what the call did
  have e0 : (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]).gpr .x0 = S := by
    rw [callEntry_gpr' _ _ _ (by decide), c1.x0]
  have e1 : (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]).gpr .x1 = BitVec.ofNat 64 (4 * j) := by
    rw [callEntry_gpr' _ _ _ (by decide), c1.x1]
  have e2 : (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]).gpr .x2 = σ.gpr .x1 := by
    rw [callEntry_gpr' _ _ _ (by decide), c1.x2]
  have e3 : (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]).gpr .x3 = sig := by
    rw [callEntry_gpr' _ _ _ (by decide), c1.x3]
  simp only [wots4Contract, e0, e1, e2, e3, State.withRegions_mem, State.callEntry_mem, hmv] at hpost
  have h4j : (BitVec.ofNat 64 (4 * j)).toNat = 4 * j := by rw [BitVec.toNat_ofNat]; omega
  obtain ⟨env₂, nodes₂, sigIn, sigOut, fr₂⟩ := hpost pk a sk hI.env hI.skat
  rw [h4j] at nodes₂ sigIn sigOut fr₂
  have hkeep : ∀ {o l : Nat}, ((1152 ≤ o ∧ o + l ≤ Layout.oA) ∨ (Layout.oN ≤ o ∧ o + l ≤ Layout.oN + 4 * j * p.n)) →
      ∀ r ∈ wotsChanges p S (4 * j) ++ [⟨sig, p.len * p.n⟩], Region.Disjoint ⟨at' S o, l⟩ r := fun ho =>
    wc_disj hn32 hsigd hX hkp ho
  -- the tail: the next key pair, and the condition
  have hx22 : s'.gpr .x22 = BitVec.ofNat 64 (4 * j) := by rw [h₅ _ (by decide) (by decide), c1.x22]
  refine wp_addi (by decide) fun t₁ f₁ => wp_subi (by omega) fun t₂ f₂ => WP.block_nil ?_
  have h22 : t₂.gpr .x22 = BitVec.ofNat 64 (4 * (j + 1)) := by
    rw [f₂.other _ (by decide), f₁.gpr, hx22, ← BitVec.ofNat_add, Nat.mul_succ]
  have hm₂ : t₂.mem = s'.mem := by rw [f₂.mem, f₁.mem]
  have hcs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → t₂.gpr r = v.gpr r := fun r hr h30 h22' => by
    have h9 : r ≠ .x9 := by intro e; subst e; simp [preserved] at hr
    rw [f₂.other _ h9, f₁.other _ h22', h₅ r hr h30]
  have hkt : ∀ r ∈ kept, t₂.gpr r = σ.gpr r := fun r hr => by
    have hp : r ∈ preserved := by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [preserved]
    have h0 : r ≠ .x0 := by intro e; subst e; simp [kept] at hr
    have h1 : r ≠ .x1 := by intro e; subst e; simp [kept] at hr
    have h2 : r ≠ .x2 := by intro e; subst e; simp [kept] at hr
    have h3 : r ≠ .x3 := by intro e; subst e; simp [kept] at hr
    have h30 : r ≠ .x30 := by intro e; subst e; simp [kept] at hr
    have h22' : r ≠ .x22 := by intro e; subst e; simp [kept] at hr
    rw [hcs r hp h30 h22', hg r h0 h1 h2 h3, hI.kept r hr]
  refine ⟨?_, ⟨by rw [hcs _ (by simp [preserved]) (by decide) (by decide), c1.x19],
    by rw [hcs _ (by simp [preserved]) (by decide) (by decide), hg _ (by decide) (by decide) (by decide) (by decide),
      hI.x20],
    by rw [hcs _ (by simp [preserved]) (by decide) (by decide), hg _ (by decide) (by decide) (by decide) (by decide),
      hI.x21], h22, hkt,
    by rw [f₂.sp, f₁.sp, h₃, c1.sp], by rw [f₂.rd, f₁.rd, h₁, hrdv, hI.rd], by rw [f₂.wr, f₁.wr, h₂, hwrv, hI.wr],
    fun r hr => by rw [f₂.v, f₁.v, h₇ r hr, hvv, hI.vcs r hr], by rw [hm₂]; exact env₂, ?_, ?_,
    fun i hi => ?_, fun k hk => ?_, fun hk => ?_, ?_⟩⟩
  · show some (t₂.read .x .x9 != 0) = _
    rw [State.read, BitVec.setWidth_eq, f₂.gpr, f₁.gpr, hx22, ← BitVec.ofNat_add,
      nz_sub (by omega) (by omega), Nat.mul_succ]
  · have h0 := hI.skat
    unfold SkAt at h0 ⊢
    rw [← h0, hm₂, bytesAt_frame fr₂ (hkeep (.inl ⟨by rw [eK]; omega, by rw [eK]; simp only [Layout.oA]; omega⟩))
      (by omega)]
  · rw [hm₂]
    exact saved_keep hI.saved fr₂ fun r hr => by
      have := hkeep (o := 1152) (l := 40) (.inl ⟨by omega, by simp only [Layout.oA]; omega⟩) r hr
      exact this
  · simp only [digitAt]
    rw [hm₂, byte_frame fr₂ (hkeep (.inl ⟨by rw [eD]; omega, by rw [eD]; simp only [Layout.oA]; rw [hz.len] at hi; omega⟩))]
    exact hI.dig i hi
  · rw [hm₂]
    by_cases hk' : k < 4 * j
    · rw [bytesAt_frame fr₂ (hkeep (.inr ⟨by omega, by
        have := Nat.mul_le_mul_right p.n (show k + 1 ≤ 4 * j by omega); rw [Nat.add_mul, Nat.one_mul] at this
        omega⟩)) (by omega)]
      exact hI.nodes k hk'
    · obtain ⟨c, hc4, rfl⟩ : ∃ c, c < 4 ∧ k = 4 * j + c := ⟨k - 4 * j, by omega, by omega⟩
      rw [nodes₂ c hc4, leaf_eq]
  · rw [hm₂]
    by_cases hin : 4 * j ≤ (σ.gpr .x1).toNat ∧ (σ.gpr .x1).toNat < 4 * j + 4
    · rw [bytesAt_flat, wotsSign_eq]
      exact Proof.SlhDsa.flatMap_range_congr fun i hi => by rw [sigIn hin i hi, hI.dig i hi]
    · rw [sigOut hin]
      exact hI.wsig (by omega)
  · rw [hm₂]
    exact hI.frame.trans (fr₂.sub (wc_sub hkp hX))

/-- The loop's invariant, `m` groups before the end. -/
def LI (p : Params) (σ : State) (S sig : Addr) (pk a sk M : List Byte) (m : Nat) (s : State) : Prop :=
  ∃ j, m = 2 ^ (p.hp - 2) - j ∧ j < 2 ^ (p.hp - 2) ∧ LInv p σ S sig pk a sk M j s

theorem pow_hp (hhp : 2 ≤ p.hp) : 2 ^ p.hp = 4 * 2 ^ (p.hp - 2) := by
  rw [show p.hp = p.hp - 2 + 2 by omega, Nat.pow_add, Nat.add_sub_cancel]; omega

/-- A pass of the leaves' loop. -/
theorem leaves_step (hz : Sz p) (T : Thash4Impl p.n) (t4name wn : String) (hC : Callees p T t4name)
    (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9) {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) :
    ∀ m s, LI p σ S sig pk a sk M m s →
      WP isa (leafCode p T t4name wn) s fun s' =>
        isa.eval (.nonzero .x .x9) s' = some (decide (m ≠ 1)) ∧
        (decide (m ≠ 1) = false → LInv p σ S sig pk a sk M (2 ^ (p.hp - 2)) s') ∧
        (decide (m ≠ 1) = true → m - 1 < m ∧ LI p σ S sig pk a sk M (m - 1) s') := by
  have h4 := pow_hp hhp
  intro m s ⟨j, hm, hj, hI⟩
  refine WP.mono (leaf_step hz T t4name wn hC hhp9 hR hidx (by omega) hI) fun s' ⟨he, hI'⟩ =>
    ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · rw [he]; congr 1; subst hm; simp only [decide_eq_decide]; omega
  · have : j + 1 = 2 ^ (p.hp - 2) := by simp only [decide_eq_false_iff_not, Decidable.not_not] at hc; omega
    rw [← this]; exact hI'
  · simp only [decide_eq_true_eq] at hc
    exact ⟨by omega, j + 1, by omega, by omega, hI'⟩

/-- The leaves' loop: `2^h′ / 4` groups of four. -/
theorem leaves_ok (hz : Sz p) (T : Thash4Impl p.n) (t4name wn : String) (hC : Callees p T t4name)
    (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9) {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    {u : State} (h0 : LInv p σ S sig pk a sk M 0 u) :
    WP isa (.loop (leafCode p T t4name wn) (.nonzero .x .x9)) u (LInv p σ S sig pk a sk M (2 ^ (p.hp - 2))) :=
  wpLoop (fun m => decide (m ≠ 1)) (fun m => m - 1) (leaves_step hz T t4name wn hC hhp hhp9 hR hidx)
    (2 ^ (p.hp - 2)) ⟨0, by omega, Nat.one_le_two_pow, h0⟩

/-! ## The prologue and the digits -/

/-- The first block of `xmssTree`. -/
abbrev entryCode (p : Params) : List Instr :=
  Impl.SlhDsa.AArch64.Xmss.pro ++ Impl.SlhDsa.AArch64.Xmss.digits ⟨p.n, p.len⟩ ++ ([.movz .x .x22 0 0] : List Instr)

/-- The prologue and the digits, from `xmssTree`'s precondition: the leaves'
invariant before the first group. -/
theorem entry_ok (hz : Sz p) {σ : State} {S : Addr} (hS : σ.gpr .x0 = S)
    (hR : Regions σ S [] ⟨σ.gpr .x2, p.xmssSigLen⟩) {pk a sk : List Byte} (hE : Env p σ.mem S pk a)
    (hsk : SkAt p σ.mem S sk) :
    WP isa (.block (entryCode p)) σ
      (LInv p σ S (σ.gpr .x2) pk a sk (bytesAt σ.mem (at' S Layout.oMsg) p.n) 0) := by
  have hn32 := hz.n32
  have hl := hz.len
  have eD : Layout.oDigits = 1856 := rfl
  have eM : Layout.oMsg = 1984 := rfl
  have eK : Layout.oSkSeed = 1664 := rfl
  have hwS := regions_scr hR
  rw [entryCode, pro_eq, List.append_assoc, List.append_assoc]
  refine Spill.save_ok slots1_ok (fun q hq => by
    rw [hS]; have := slots1_in q hq; exact in_scr hwS (by omega)) ?_
  have hsv : Spill.Saved S σ.gpr slots1 (Spill.saveMem σ.mem (σ.gpr .x0) σ.gpr slots1) := by
    rw [← hS]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf₁ : Frame [⟨at' S 1152, 40⟩] σ.mem (Spill.saveMem σ.mem (σ.gpr .x0) σ.gpr slots1) := by
    rw [← hS]; exact Spill.saveMem_frame slots1_in (by decide) _ _ _
  generalize Spill.saveMem σ.mem (σ.gpr .x0) σ.gpr slots1 = m₁ at hsv hf₁
  refine wp_mov fun t₁ e₁ => wp_mov fun t₂ e₂ => wp_mov fun t₃ e₃ => ?_
  have h19 : t₃.gpr .x19 = S := by rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr]; exact hS
  have hm₃ : t₃.mem = m₁ := by rw [e₃.mem, e₂.mem, e₁.mem]
  have hw₃ : (⟨S, 65536⟩ : Region) ∈ t₃.wr := by rw [e₃.wr, e₂.wr, e₁.wr]; exact hwS
  have hg₃ : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → t₃.gpr r = σ.gpr r := fun r h19 h20 h21 => by
    rw [e₃.other _ h21, e₂.other _ h20, e₁.other _ h19]
  refine digits_ok hz h19 hw₃ fun t₄ hdig hfd hg₄ hsp₄ hrd₄ hwr₄ hv₄ => ?_
  refine wp_movz fun t₅ e₅ => WP.block_nil ?_
  rw [hm₃] at hdig hfd
  have hm₅ : t₅.mem = t₄.mem := e₅.mem
  have hg₅ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x22 → t₅.gpr r = t₃.gpr r :=
    fun r h9 h10 h11 h12 h13 h22 => by rw [e₅.other _ h22, hg₄ r h9 h10 h11 h12 h13]
  have hd₁ : ∀ {o l : Nat}, (o + l ≤ 1152 ∨ 1192 ≤ o) → o + l ≤ 65536 →
      ∀ r ∈ [(⟨at' S 1152, 40⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact disj_scr S h₁ h₂ (by omega)
  have hd₂ : ∀ {o l : Nat}, (o + l ≤ Layout.oDigits ∨ Layout.oDigits + p.len ≤ o) → o + l ≤ 65536 →
      ∀ r ∈ [(⟨at' S Layout.oDigits, p.len⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact disj_scr S h₁ h₂ (by rw [eD, hl]; omega)
  have hM : bytesAt m₁ (at' S Layout.oMsg) p.n = bytesAt σ.mem (at' S Layout.oMsg) p.n :=
    bytesAt_frame hf₁ (hd₁ (by rw [eM]; omega) (by rw [eM]; omega)) (by omega)
  rw [hM] at hdig
  have hsub : ∀ r ∈ [(⟨at' S 1152, 40⟩ : Region)] ++ [⟨at' S Layout.oDigits, p.len⟩],
      ∃ R ∈ changes p S ++ [⟨σ.gpr .x2, p.xmssSigLen⟩], Region.Sub r R := by
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨at' S Layout.oVars, 4 * Layout.frameLen⟩, by simp [changes],
        Offset.sub S (by simp [Layout.oVars]) (by simp [Layout.oVars, Layout.frameLen])⟩
    · exact ⟨⟨at' S Layout.oDigits, 128⟩, by simp [changes], Region.sub_prefix (by rw [hl]; omega)⟩
  have hF : Frame ([(⟨at' S 1152, 40⟩ : Region)] ++ [⟨at' S Layout.oDigits, p.len⟩]) σ.mem t₅.mem := by
    rw [hm₅]
    exact (hf₁.mono fun r hr => List.mem_append_left _ hr).trans (hfd.mono fun r hr => List.mem_append_right _ hr)
  have hkeep : ∀ {o l : Nat}, (1192 ≤ o ∧ o + l ≤ Layout.oDigits) ∨ (Layout.oDigits + p.len ≤ o ∧ o + l ≤ 65536) →
      ∀ r ∈ [(⟨at' S 1152, 40⟩ : Region)] ++ [⟨at' S Layout.oDigits, p.len⟩], Region.Disjoint ⟨at' S o, l⟩ r := by
    intro o l ho r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hd₁ (by omega) (by rw [eD] at ho; omega) r hr
    · exact hd₂ (by omega) (by rw [eD] at ho; omega) r hr
  refine ⟨by rw [hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h19],
    by rw [hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e₃.other _ (by decide),
      e₂.gpr, e₁.other _ (by decide)],
    by rw [hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e₃.gpr, e₂.other _ (by decide),
      e₁.other _ (by decide)],
    by rw [e₅.gpr]; rfl,
    fun r hr => ?_,
    by rw [e₅.sp, hsp₄, e₃.sp, e₂.sp, e₁.sp], by rw [e₅.rd, hrd₄, e₃.rd, e₂.rd, e₁.rd],
    by rw [e₅.wr, hwr₄, e₃.wr, e₂.wr, e₁.wr], fun r _ => by rw [e₅.v, hv₄, e₃.v, e₂.v, e₁.v],
    env_frame hn32 hE hF fun ho₁ ho₂ => hkeep (.inr ⟨by rw [eD, hl]; simp only [Layout.oA] at ho₁; omega,
      by simp only [Layout.oN] at ho₂; omega⟩), ?_, ?_, fun i hi => by simp only [digitAt]; rw [hm₅]; exact hdig i hi,
    fun k hk => absurd hk (by omega), fun hk => absurd hk (by omega), ?_⟩
  · simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (hg₃ _ (by decide) (by decide) (by decide))
  · unfold SkAt at hsk ⊢
    rw [← hsk]
    exact bytesAt_frame hF (hkeep (.inl ⟨by rw [eK]; omega, by rw [eK, eD]; omega⟩)) (by omega)
  · rw [hm₅]
    exact saved_keep hsv hfd fun r hr => hd₂ (by rw [eD]; omega) (by omega) r hr
  · exact hF.sub hsub

end VG.Proof.SlhDsa.AArch64.Xmss
