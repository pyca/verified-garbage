module

-- separate module: the two-run proofs of `forsSign`'s trees, rebuilt only when they change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsTop
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTSub
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`'s trees are constant time

The loop of subtrees (`subs_ct`), in two runs of the same tree `tt` with the
same signature `AU`: each run keeps its correctness invariant (`ST`, at the
same subtree `u`), which gives what a subtree needs (`ST.spre`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Fors (s)
open VG.Proof.SlhDsa.AArch64.TreeBase

variable {p : Params}

theorem ct_as_le32 (h : p.a ≤ 14) : 2 ^ (p.a - s p.a) ≤ 32 := by
  have : p.a - s p.a ≤ 5 := by simp only [s]; omega
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) this) (by decide)

/-- What a subtree needs, from the loop's invariant. -/
theorem ST.spre {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte} {t₀ : State}
    (C : SC p S SG AU L dA tt idx t₀) {u : Nat} {t : State} (hu : u < 2 ^ (p.a - s p.a))
    (hI : ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ u t) :
    SPre p S SG AU L dA (u * 2 ^ s p.a) (tt * 2 ^ p.a) idx pk a16 sk t₀.sp t := by
  have hz := C.hz
  have hn32 := hz.n32
  have hsa := s_le p.a
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel hsa]
  have hu1 : (u + 1) * 2 ^ s p.a ≤ 2 ^ p.a := by rw [← hUs]; exact Nat.mul_le_mul_right _ hu
  have htt := C.tt
  rw [Nat.add_mul, Nat.one_mul] at htt hu1
  have hn16 := hz.n16
  have hGf := C.Gf
  have hidx : idx < 2 ^ 32 := by
    have := C.idx; have := Nat.pow_le_pow_right (show 0 < 2 by decide) C.a14; omega
  have g : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → t.gpr r = t₀.gpr r := hI.cs
  have hsn : s p.a * p.n ≤ p.a * p.n := Nat.mul_le_mul_right _ hsa
  have hdA := C.dA
  rw [Nat.add_mul, Nat.one_mul] at hdA
  have hAUs : Region.Sub ⟨AU, p.n⟩ ⟨SG, L⟩ := by
    rw [C.AU]; exact Offset.sub_base SG (by omega)
  have hR : u * 2 ^ s p.a / 2 ^ s p.a < 32 := by
    rw [Nat.mul_div_cancel _ (Nat.two_pow_pos _)]; have := ct_as_le32 C.a14; omega
  refine ⟨⟨by rw [g .x19 (by decide) (by decide) (by decide) (by decide), C.x19],
    by rw [g .x20 (by decide) (by decide) (by decide) (by decide)]; exact C.kp,
    by rw [g .x21 (by decide) (by decide) (by decide) (by decide), C.x21], hidx,
    by rw [g .x24 (by decide) (by decide) (by decide) (by decide), C.x24], hI.x25,
    by rw [g .x27 (by decide) (by decide) (by decide) (by decide), C.x27], by omega,
    by rw [hI.wr]; exact C.w, by rw [hI.wr]; exact C.wG, C.AU, by omega, C.Gf, C.fit, C.Gd, hI.env, hI.sp, hR⟩,
    hI.skat, by omega,
    ⟨_, by rw [hI.wr]; exact C.wG, by rw [C.AU]; exact Offset.contains_base SG (by omega) (by omega)⟩,
    C.Gd.sub_left hAUs⟩

/-- `SPre` from the loop's invariant at the measure `m`. -/
theorem SI.spre {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte} {t₀ : State}
    (C : SC p S SG AU L dA tt idx t₀) {m : Nat} {t : State}
    (h : SI p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ m t) :
    SPre p S SG AU L dA ((2 ^ (p.a - s p.a) - m) * 2 ^ s p.a) (tt * 2 ^ p.a) idx pk a16 sk t₀.sp t := by
  obtain ⟨u, hu, hm, hI⟩ := h
  rw [show 2 ^ (p.a - s p.a) - m = u by omega]
  exact ST.spre C (by omega) hI

/-- The loop of subtrees, in two runs of the same tree with the same
signature and stack pointer. -/
theorem subs_ct (hA : As p) (T : Thash4Impl p.n) (t4name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true)
    {S SG AU : Addr} {L dA tt idx₁ idx₂ : Nat} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte} {t₁ t₂ : State}
    (C₁ : SC p S SG AU L dA tt idx₁ t₁) (C₂ : SC p S SG AU L dA tt idx₂ t₂) (hsp : t₁.sp = t₂.sp) (n : Nat) :
    RelCT isa (fun a b => SI p S AU pk₁ a₁ sk₁ (t₁.gpr .x20).toNat tt idx₁ t₁ n a ∧
        SI p S AU pk₂ a₂ sk₂ (t₂.gpr .x20).toNat tt idx₂ t₂ n b)
      (.loop (Impl.SlhDsa.AArch64.Fors.subtreeBody ⟨p.n, p.len⟩ p.a t4name ln T.code) (.nonzero .x .x9))
      fun a b => ST p S AU pk₁ a₁ sk₁ (t₁.gpr .x20).toNat tt idx₁ t₁ (2 ^ (p.a - s p.a)) a ∧
        ST p S AU pk₂ a₂ sk₂ (t₂.gpr .x20).toNat tt idx₂ t₂ (2 ^ (p.a - s p.a)) b :=
  relLoop (fun m => decide (m ≠ 1)) (fun m => m - 1)
    (fun m => RelCT.mono (sub_ct C₁.hz hA T t4name ln hL hLf (sp := t₁.sp))
      (fun a b ⟨ha, hb⟩ => ⟨SI.spre C₁ ha, by have := SI.spre C₂ hb; rw [← hsp] at this; exact this⟩)
      fun _ _ h => h)
    (sub_step T t4name ln hL hLf C₁) (sub_step T t4name ln hL hLf C₂) n

/-! ## The heights above the subtrees -/

/-- What `topHeights` needs: the tree `tt` from leaf `V4`, its signature `AU`
at `dA` in `⟨SG, L⟩`, the tree's index `idx`, `Env`, the stack pointer. -/
structure TPre (p : Params) (S SG AU : Addr) (L dA tt V4 idx : Nat) (pk a16 : List Byte) (sp : BitVec 64)
    (u : State) : Prop where
  x19 : u.gpr .x19 = S
  kp : (u.gpr .x20).toNat < 2 ^ 32
  x21 : u.gpr .x21 = BitVec.ofNat 64 idx
  idx : idx < 2 ^ 32
  x23 : u.gpr .x23 = BitVec.ofNat 64 tt
  x24 : u.gpr .x24 = AU
  x27 : u.gpr .x27 = BitVec.ofNat 64 V4
  V : V4 < 2 ^ 32
  scr : (⟨S, 65536⟩ : Region) ∈ u.wr
  wG : (⟨SG, L⟩ : Region) ∈ u.wr
  AU : AU = SG + BitVec.ofNat 64 dA
  dA : dA + (p.a + 1) * p.n ≤ L
  Gf : SG.toNat + L ≤ 2 ^ 64
  fit : S.toNat + 65536 ≤ 2 ^ 64
  Gd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩
  env : Env p u.mem S pk a16
  sp : u.sp = sp
  tk : (tt + 1) * p.n ≤ 1120

/-- What the root's copy needs. -/
abbrev RB (S : Addr) (tt : Nat) (sp : BitVec 64) (w : State) : Prop :=
  w.gpr .x19 = S ∧ w.gpr .x23 = BitVec.ofNat 64 tt ∧ w.sp = sp ∧ (⟨S, 65536⟩ : Region) ∈ w.wr

theorem tbc_pub {S AU : Addr} {pk₁ a₁ pk₂ a₂ : List Byte} {u₁ v₁ u₂ v₂ : State}
    (h₁ : TBC p S AU pk₁ a₁ u₁ v₁) (h₂ : TBC p S AU pk₂ a₂ u₂ v₂) (h24₁ : u₁.gpr .x24 = AU)
    (h24₂ : u₂.gpr .x24 = AU) (hsp : u₁.sp = u₂.sp) {W : List Region} :
    (levelsContract p).pub (v₁.callEntry.withRegions [] W) (v₂.callEntry.withRegions [] W) := by
  simp only [levelsContract]
  rw [Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide),
    Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide),
    Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide),
    Wots4.ce_gpr _ _ (by decide), State.withRegions_sp, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_sp, h₁.tb.x0, h₂.tb.x0, h₁.tb.x1, h₂.tb.x1, h₁.tb.x2, h₂.tb.x2, h₁.tb.x3, h₂.tb.x3,
    h₁.tb.x4, h₂.tb.x4, h24₁, h24₂, h₁.tb.keep.sp, h₂.tb.keep.sp, hsp]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {S SG AU : Addr} {L dA tt V4 idx : Nat} {pk a16 : List Byte} {sp : BitVec 64} {u : State}

theorem TPre.tbc (hz : Sz p) (hA : As p) (hsa : s p.a < p.a) (h : TPre p S SG AU L dA tt V4 idx pk a16 sp u) :
    WP isa (.block (tbList p.n p.a)) u (TBC p S AU pk a16 u) :=
  tbc_ok hz hA.facts.2.2.1 hsa h.x19 h.kp h.x21 h.idx h.x24 h.x27 h.V h.scr h.wG h.AU h.dA h.Gf h.fit h.Gd h.env

theorem TPre.rb (h : TPre p S SG AU L dA tt V4 idx pk a16 sp u) : RB S tt sp u := ⟨h.x19, h.x23, h.sp, h.scr⟩

theorem tbc_call {t4name ln : String} {t4 : Prog isa}
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4).noFrames = true) {v : State}
    (hu : TPre p S SG AU L dA tt V4 idx pk a16 sp u) (hv : TBC p S AU pk a16 u v) :
    WP isa (.call ln (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4)) v (RB S tt sp) :=
  WP.callV hL.1 hv.pre hv.c₁ hv.c₂ (fun s' _ h₂ h₃ _ h₅ _ _ _ =>
    ⟨by rw [h₅ .x19 (by decide) (by decide), hv.tb.keep.gpr .x19 (by decide), hu.x19],
      by rw [h₅ .x23 (by decide) (by decide), hv.tb.keep.gpr .x23 (by decide), hu.x23],
      by rw [h₃, hv.tb.keep.sp, hu.sp], by rw [h₂, hv.tb.keep.wr]; exact hu.scr⟩) hLf

end

/-- The heights above the subtrees and the root's copy, in two runs of the
same tree. -/
theorem top_ct (hz : Sz p) (hA : As p) {t4name ln : String} {t4 : Prog isa}
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4).noFrames = true)
    {S SG AU : Addr} {L dA tt V4 idx₁ idx₂ : Nat} {pk₁ a₁ pk₂ a₂ : List Byte} {sp : BitVec 64} :
    RelCT isa (fun a b => TPre p S SG AU L dA tt V4 idx₁ pk₁ a₁ sp a ∧ TPre p S SG AU L dA tt V4 idx₂ pk₂ a₂ sp b)
      (Impl.SlhDsa.AArch64.Fors.topHeights ⟨p.n, p.len⟩ p.a t4name ln t4) fun _ _ => True := by
  unfold Impl.SlhDsa.AArch64.Fors.topHeights
  have hrb : RelCT isa (fun a b => RB S tt sp a ∧ RB S tt sp b)
      (.block (([Impl.SlhDsa.AArch64.Thash4.mov .x10 .x23] : List Instr) ++
        Impl.SlhDsa.AArch64.mulN (⟨p.n, p.len⟩ : Layout).n .x10 .x11 ++ ([.add .x .x10 .x10 .x19] : List Instr) ++
        Impl.SlhDsa.AArch64.copyWords .x10 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).msgOff) .x19
          (Impl.SlhDsa.AArch64.Fors.rootOff p.a) ((⟨p.n, p.len⟩ : Layout).n / 8))) fun _ _ => True :=
    ct_rootB hz hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha.2.2.1, hb.2.2.1], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [ha.1, hb.1]
      · rw [ha.2.1, hb.2.1]⟩
  split
  · rename_i hsa
    refine relSeq (B₁ := RB S tt sp) (B₂ := RB S tt sp) ?_
      (fun u hu => WP.seq (WP.mono (hu.tbc hz hA hsa) fun v hv => tbc_call hL hLf hu hv))
      (fun u hu => WP.seq (WP.mono (hu.tbc hz hA hsa) fun v hv => tbc_call hL hLf hu hv)) hrb
    refine relSeq (c₁ := .block (tbList p.n p.a))
      (B₁ := fun v => ∃ u, TPre p S SG AU L dA tt V4 idx₁ pk₁ a₁ sp u ∧ TBC p S AU pk₁ a₁ u v)
      (B₂ := fun v => ∃ u, TPre p S SG AU L dA tt V4 idx₂ pk₂ a₂ sp u ∧ TBC p S AU pk₂ a₂ u v)
      (ct_top hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha.sp, hb.sp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [ha.x19, hb.x19]
        · rw [ha.x24, hb.x24]
        · rw [ha.x27, hb.x27]⟩)
      (fun u hu => WP.mono (hu.tbc hz hA hsa) fun v hv => ⟨u, hu, hv⟩)
      (fun u hu => WP.mono (hu.tbc hz hA hsa) fun v hv => ⟨u, hu, hv⟩) ?_
    exact RelCT.call hL.1 hL.2.1 [] (tbW p.n p.a S AU) fun v w ⟨⟨u, hu, hv⟩, ⟨u', hu', hw⟩⟩ =>
      ⟨hv.pre, hw.pre, tbc_pub hv hw hu.x24 hu'.x24 (by rw [hu.sp, hu'.sp]), hv.c₁, hv.c₂, hw.c₁, hw.c₂⟩
  · refine relSeq (B₁ := RB S tt sp) (B₂ := RB S tt sp)
      (ct_nil fun a b ⟨ha, hb⟩ => ⟨by rw [ha.sp, hb.sp], fun _ h => absurd h List.not_mem_nil⟩)
      (fun u hu => WP.block_nil hu.rb) (fun u hu => WP.block_nil hu.rb) hrb

/-- The heights above the subtrees keep the stack pointer. -/
theorem top_sp (hz : Sz p) (hA : As p) {t4name ln : String} {t4 : Prog isa}
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4).noFrames = true)
    {S SG AU : Addr} {L dA tt V4 idx : Nat} {pk a16 : List Byte} {sp : BitVec 64} {u : State}
    (hu : TPre p S SG AU L dA tt V4 idx pk a16 sp u) :
    WP isa (Impl.SlhDsa.AArch64.Fors.topHeights ⟨p.n, p.len⟩ p.a t4name ln t4) u fun w => w.sp = sp := by
  have hn32 := hz.n32
  have hR : Impl.SlhDsa.AArch64.Fors.rootOff p.a % 8 = 0 ∧ 4832 ≤ Impl.SlhDsa.AArch64.Fors.rootOff p.a ∧
      Impl.SlhDsa.AArch64.Fors.rootOff p.a + p.n ≤ 30144 := by
    simp only [Impl.SlhDsa.AArch64.Fors.rootOff]; split <;> simp only [Layout.oN, Layout.oRoots, Layout.nodeSlots] <;> omega
  have hrb : ∀ w, RB S tt sp w → WP isa (.block (rbList p.n (Impl.SlhDsa.AArch64.Fors.rootOff p.a))) w
      fun w' => w'.sp = sp := fun w hw =>
    rootB_ok hz hw.1 hw.2.1 hu.tk hR.1 hR.2.1 hR.2.2 hw.2.2.2 fun w' k _ _ => by rw [k.sp, hw.2.2.1]
  unfold Impl.SlhDsa.AArch64.Fors.topHeights
  split
  · rename_i hsa
    exact WP.seq (WP.seq (WP.mono (hu.tbc hz hA hsa) fun v hv => WP.mono (tbc_call hL hLf hu hv) fun w hw =>
      hrb w hw))
  · exact WP.seq (WP.block_nil (hrb u hu.rb))

/-- What `topHeights` needs, after the loop of subtrees. -/
theorem ST.tpre {S SG AU : Addr} {L dA tt idx : Nat} {pk a16 sk : List Byte} {t₀ : State}
    (C : SC p S SG AU L dA tt idx t₀) (h23 : t₀.gpr .x23 = BitVec.ofNat 64 tt) (htk : (tt + 1) * p.n ≤ 1120)
    {u : Nat} {t : State} (hI : ST p S AU pk a16 sk (t₀.gpr .x20).toNat tt idx t₀ u t) :
    TPre p S SG AU L dA tt (tt * 2 ^ p.a) idx pk a16 t₀.sp t := by
  have g : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → t.gpr r = t₀.gpr r := hI.cs
  have htt := C.tt
  rw [Nat.add_mul, Nat.one_mul] at htt
  have hidx : idx < 2 ^ 32 := by
    have := C.idx; have := Nat.pow_le_pow_right (show 0 < 2 by decide) C.a14; omega
  exact ⟨by rw [g .x19 (by decide) (by decide) (by decide) (by decide), C.x19],
    by rw [g .x20 (by decide) (by decide) (by decide) (by decide)]; exact C.kp,
    by rw [g .x21 (by decide) (by decide) (by decide) (by decide), C.x21], hidx,
    by rw [g .x23 (by decide) (by decide) (by decide) (by decide), h23],
    by rw [g .x24 (by decide) (by decide) (by decide) (by decide), C.x24],
    by rw [g .x27 (by decide) (by decide) (by decide) (by decide), C.x27], by omega,
    by rw [hI.wr]; exact C.w, by rw [hI.wr]; exact C.wG, C.AU, C.dA, C.Gf, C.fit, C.Gd, hI.env, hI.sp, htk⟩

end VG.Proof.SlhDsa.AArch64.Fors
