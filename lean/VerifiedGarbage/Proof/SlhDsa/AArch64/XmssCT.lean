module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.XmssMain
public import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsCT
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.AArch64.LevelsCT
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.XmssMain
public meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `xmssTree` is constant time, and `Verified`
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Xmss

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase

/-- The sizes of `h′`: those of the SHAKE parameter sets. -/
abbrev Hps (hp : Nat) : Prop := hp = 3 ∨ hp = 4 ∨ hp = 8 ∨ hp = 9

section
variable {P : State → State → Prop}

theorem ct_entry {n : Nat} (hn : n = 16 ∨ n = 24 ∨ n = 32)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x0], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Xmss.pro ++ Impl.SlhDsa.AArch64.Xmss.digits ⟨n, 2 * n + 3⟩ ++
      ([.movz .x .x22 0 0] : List Instr))) fun _ _ => True := by
  rcases hn with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

end

theorem ct_next {P : State → State → Prop} {hp : Nat} (hh : Hps hp) (hr : ∀ x y, P x y → x.sp = y.sp) :
    RelCT isa P (.block [.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 (2 ^ hp)]) fun _ _ => True := by
  rcases hh with rfl | rfl | rfl | rfl <;>
    exact taintR [] (fun x y h => ⟨hr x y h, fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide)

variable {p : Params}

theorem wots_pub {v₁ v₂ : State} {σ₁ σ₂ : State} {S sig : Addr} {j : Nat}
    (h₁ : Call1 p σ₁ S sig j v₁) (h₂ : Call1 p σ₂ S sig j v₂) (hsp : σ₁.sp = σ₂.sp) {W : List Region} :
    (wots4Contract p).pub (v₁.callEntry.withRegions [] W) (v₂.callEntry.withRegions [] W) := by
  simp only [wots4Contract]
  rw [callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide),
    callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide),
    State.withRegions_sp, State.withRegions_sp, State.callEntry_sp, State.callEntry_sp,
    h₁.x0, h₂.x0, h₁.x1, h₂.x1, h₁.x3, h₂.x3, h₁.sp, h₂.sp, hsp]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A pass of the leaves' loop, in two runs at the same point. -/
theorem body_ct (hz : Sz p) (T : Thash4Impl p.n) (t4name wn : String) (hC : Callees p T t4name) (hh : Hps p.hp)
    {σ₁ σ₂ : State} {S sig : Addr} {pk₁ a₁ sk₁ M₁ pk₂ a₂ sk₂ M₂ : List Byte}
    (hR₁ : Regions σ₁ S [] ⟨sig, p.xmssSigLen⟩) (hR₂ : Regions σ₂ S [] ⟨sig, p.xmssSigLen⟩)
    (hidx₁ : (σ₁.gpr .x1).toNat < 2 ^ 32) (hidx₂ : (σ₂.gpr .x1).toNat < 2 ^ 32)
    (hsp : σ₁.sp = σ₂.sp) (m : Nat) :
    RelCT isa (fun a b => LI p σ₁ S sig pk₁ a₁ sk₁ M₁ m a ∧ LI p σ₂ S sig pk₂ a₂ sk₂ M₂ m b)
      (leafCode p T t4name wn) fun _ _ => True := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  have h4 := pow_hp hhp
  by_cases hm : 1 ≤ m ∧ m ≤ 2 ^ (p.hp - 2)
  · have key : ∀ {σ : State} {pk a sk M : List Byte} {u : State}, LI p σ S sig pk a sk M m u →
        LInv p σ S sig pk a sk M (2 ^ (p.hp - 2) - m) u := by
      rintro σ pk a sk M u ⟨j, rfl, hj, h⟩; rwa [show 2 ^ (p.hp - 2) - (2 ^ (p.hp - 2) - j) = j by omega]
    have hj : 4 * (2 ^ (p.hp - 2) - m + 1) ≤ 2 ^ p.hp := by omega
    unfold leafCode Impl.SlhDsa.AArch64.Xmss.leafBody
    refine relSeq (B₁ := fun v => Call1 p σ₁ S sig _ v) (B₂ := fun v => Call1 p σ₂ S sig _ v)
      (taintR [] (fun x y ⟨hx, hy⟩ => ⟨by rw [(key hx).sp, (key hy).sp, hsp], fun _ h => absurd h List.not_mem_nil⟩)
        (by taint_decide))
      (fun x hx => WP.mono (args_ok hz hhp9 hR₁ hidx₁ hj (key hx)) fun _ h => h.1)
      (fun y hy => WP.mono (args_ok hz hhp9 hR₂ hidx₂ hj (key hy)) fun _ h => h.1) ?_
    refine relSeq (B₁ := fun w => w.sp = σ₁.sp) (B₂ := fun w => w.sp = σ₂.sp)
      (RelCT.call hC.wots.1 hC.wots.2.1 [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩] fun x y ⟨hx, hy⟩ =>
          ⟨hx.pre, hy.pre, wots_pub hx hy hsp, hx.c₁, hx.c₂, hy.c₁, hy.c₂⟩)
      (fun x hx => WP.callV hC.wots.1 hx.pre hx.c₁ hx.c₂ (fun s' _ _ h₃ _ _ _ _ _ => by rw [h₃, hx.sp]) hC.wotsNF)
      (fun y hy => WP.callV hC.wots.1 hy.pre hy.c₁ hy.c₂ (fun s' _ _ h₃ _ _ _ _ _ => by rw [h₃, hy.sp]) hC.wotsNF)
      (ct_next hh fun x y ⟨hx, hy⟩ => by rw [hx, hy, hsp])
  · exact RelCT.of_false fun x y ⟨⟨j, hj₁, hj₂, _⟩, _⟩ => hm ⟨by omega, by omega⟩

section
variable {P : State → State → Prop}

theorem ct_hb {n hp : Nat} (hn : n = 16 ∨ n = 24 ∨ n = 32) (hh : Hps hp)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19, .x21], x.gpr r = y.gpr r) :
    RelCT isa P (.block (hbList n (2 * n + 3) hp)) fun _ _ => True := by
  rcases hn with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_tail {n : Nat} (hn : n = 16 ∨ n = 24 ∨ n = 32)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.copyWords .x19 Layout.oMsg .x19 Layout.oN (n / 8) ++
      Impl.SlhDsa.AArch64.restoreRegs 1 Impl.SlhDsa.AArch64.Xmss.saved)) fun _ _ => True := by
  rcases hn with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

end

/-- What a call of `levels` needs, after the heights block. -/
structure Call2 (p : Params) (σ : State) (S AU : Addr) (v : State) : Prop where
  x0 : v.gpr .x0 = S
  x1 : v.gpr .x1 = at' S Layout.oN
  x2 : v.gpr .x2 = BitVec.ofNat 64 (2 ^ p.hp)
  x3 : v.gpr .x3 = 0
  x4 : v.gpr .x4 = AU
  sp : v.sp = σ.sp
  pre : (levelsContract p).pre (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩])
  c₁ : Covers ([] ++ [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]) (v.rd ++ v.wr)
  c₂ : Covers [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩] v.wr

theorem hb1_ok (hz : Sz p) (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9) {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    {u : State} (hI : LInv p σ S sig pk a sk M (2 ^ (p.hp - 2)) u) :
    WP isa (.block (hbCode p)) u (Call2 p σ S (sig + BitVec.ofNat 64 (p.len * p.n))) := by
  have hn32 := hz.n32
  have hSL := xmssSigLen_eq (p := p)
  have hsigd : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, Layout.oSigTmp⟩ := hR.out_scr
  refine hblock_ok hz hhp9 hI.x19 hI.x21 (by rw [hI.wr]; exact regions_scr hR) (by rw [hI.wr]; exact regions_out hR)
    hR.out_fit hsigd fun v hv => ?_
  have hvenv : Env p v.mem S pk a := env_frame hn32 hI.env hv.frame fun {o l} h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hsigd.sub_left (Offset.sub_base sig (by rw [hSL]))).sub_right
        (Offset.sub_base S (by rw [show Layout.oSigTmp = 30144 from rfl]; simp only [Layout.oN] at h₂; omega))).symm
    · exact disj_scr S (by rw [var_eq]; simp only [Layout.oA] at h₁; omega) (by simp only [Layout.oN] at h₂; omega)
        (by rw [var_eq]; omega)
  obtain ⟨hpre, hc, hw⟩ := levels_pre hz (by omega) hhp9 hR rfl hv (by rw [hv.x5, hI.x20]; exact hidx)
    (by rw [hv.keep.wr, hI.wr]) hvenv
  exact ⟨hv.x0, hv.x1, hv.x2, hv.x3, hv.x4, by rw [hv.keep.sp, hI.sp], hpre, hc, hw⟩

theorem levels_pub {v₁ v₂ : State} {σ₁ σ₂ : State} {S AU : Addr}
    (h₁ : Call2 p σ₁ S AU v₁) (h₂ : Call2 p σ₂ S AU v₂) (hsp : σ₁.sp = σ₂.sp) {W : List Region} :
    (levelsContract p).pub (v₁.callEntry.withRegions [] W) (v₂.callEntry.withRegions [] W) := by
  simp only [levelsContract]
  rw [callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide),
    callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide),
    callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide),
    callEntry_gpr' _ _ _ (by decide),
    State.withRegions_sp, State.withRegions_sp, State.callEntry_sp, State.callEntry_sp,
    h₁.x0, h₂.x0, h₁.x1, h₂.x1, h₁.x2, h₂.x2, h₁.x3, h₂.x3, h₁.x4, h₂.x4, h₁.sp, h₂.sp, hsp]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hbCode_eq (hz : Sz p) : hbCode p = hbList p.n (2 * p.n + 3) p.hp := by rw [← hz.len]

/-- The heights, in two runs. -/
theorem heights_ct (hz : Sz p) (T : Thash4Impl p.n) (t4name ln : String) (hC : Callees p T t4name) (hh : Hps p.hp)
    {σ₁ σ₂ : State} {S sig : Addr} {pk₁ a₁ sk₁ M₁ pk₂ a₂ sk₂ M₂ : List Byte}
    (hR₁ : Regions σ₁ S [] ⟨sig, p.xmssSigLen⟩) (hR₂ : Regions σ₂ S [] ⟨sig, p.xmssSigLen⟩)
    (hidx₁ : (σ₁.gpr .x1).toNat < 2 ^ 32) (hidx₂ : (σ₂.gpr .x1).toNat < 2 ^ 32) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (fun a b => LInv p σ₁ S sig pk₁ a₁ sk₁ M₁ (2 ^ (p.hp - 2)) a ∧
        LInv p σ₂ S sig pk₂ a₂ sk₂ M₂ (2 ^ (p.hp - 2)) b)
      (heightsCode p T t4name ln) fun _ _ => True := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  unfold heightsCode Impl.SlhDsa.AArch64.Xmss.heights
  refine relSeq (c₁ := .block (hbCode p)) (B₁ := Call2 p σ₁ S _) (B₂ := Call2 p σ₂ S _)
    (by
      rw [hbCode_eq hz]
      refine ct_hb hz.nv hh fun x y ⟨hx, hy⟩ => ⟨by rw [hx.sp, hy.sp, hsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hx.x19, hy.x19]
      · rw [hx.x21, hy.x21])
    (fun x hx => hb1_ok hz hhp hhp9 hR₁ hidx₁ hx)
    (fun y hy => hb1_ok hz hhp hhp9 hR₂ hidx₂ hy)
    (RelCT.call hC.levels.1 hC.levels.2.1 [] _ fun x y ⟨hx, hy⟩ =>
      ⟨hx.pre, hy.pre, levels_pub hx hy hsp, hx.c₁, hx.c₂, hy.c₁, hy.c₂⟩)

/-! ## Two runs of the whole function -/

theorem xmss_ct (hz : Sz p) (T : Thash4Impl p.n) (t4name wn ln : String) (hC : Callees p T t4name) (hh : Hps p.hp) :
    ConstantTime isa (xmssContract p).pre (xmssContract p).pub (xmssCode p T t4name wn ln) := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨hp1, hp2, hp3⟩ := hpub
  obtain ⟨hR₁, ⟨pk₁, a₁, hE₁⟩, hidx₁⟩ := h₁
  obtain ⟨hR₂, ⟨pk₂, a₂, hE₂⟩, hidx₂⟩ := h₂
  obtain ⟨S, eS⟩ : ∃ S, s₁.gpr .x0 = S := ⟨_, rfl⟩
  have eS₂ : s₂.gpr .x0 = S := by rw [← hp1, eS]
  rw [eS] at hR₁ hE₁
  rw [eS₂] at hR₂ hE₂
  have hR₂' : Regions s₂ S [] ⟨s₁.gpr .x2, p.xmssSigLen⟩ := by rw [hp2]; exact hR₂
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (xmssCode p T t4name wn ln) fun _ _ => True := by
    unfold xmssCode Impl.SlhDsa.AArch64.Xmss.xmssTree
    refine relSeq (by
        have h := ct_entry (P := fun a b => a = s₁ ∧ b = s₂) hz.nv fun x y ⟨hx, hy⟩ => ⟨by rw [hx, hy, hp3],
          fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [hx, hy, hp1]⟩
        rwa [← hz.len] at h)
      (fun x hx => by
        rw [hx]; exact WP.mono (entry_ok hz eS hR₁ hE₁ rfl) fun u hu => (⟨0, by omega, Nat.one_le_two_pow, hu⟩ :
          LI p s₁ S (s₁.gpr .x2) pk₁ a₁ _ _ (2 ^ (p.hp - 2)) u))
      (fun y hy => by
        rw [hy]; exact WP.mono (entry_ok hz eS₂ hR₂ hE₂ rfl) fun u hu => (⟨0, by omega, Nat.one_le_two_pow,
          by rw [← hp2] at hu; exact hu⟩ : LI p s₂ S (s₁.gpr .x2) pk₂ a₂ _ _ (2 ^ (p.hp - 2)) u)) ?_
    refine relSeq (RelCT.mono (relLoop (fun m => decide (m ≠ 1)) (fun m => m - 1)
        (body_ct hz T t4name wn hC hh hR₁ hR₂' hidx₁ hidx₂ hp3)
        (leaves_step hz T t4name wn hC hhp hhp9 hR₁ hidx₁)
        (leaves_step hz T t4name wn hC hhp hhp9 hR₂' hidx₂) (2 ^ (p.hp - 2))) (fun _ _ h => h)
          fun _ _ _ => trivial)
      (fun x hx => wpLoop _ _ (leaves_step hz T t4name wn hC hhp hhp9 hR₁ hidx₁) _ hx)
      (fun y hy => wpLoop _ _ (leaves_step hz T t4name wn hC hhp hhp9 hR₂' hidx₂) _ hy) ?_
    refine relSeq (heights_ct hz T t4name ln hC hh hR₁ hR₂' hidx₁ hidx₂ hp3)
      (fun x hx => heights_ok hz T t4name ln hC hhp hhp9 hR₁ hidx₁ hx)
      (fun y hy => heights_ok hz T t4name ln hC hhp hhp9 hR₂' hidx₂ hy)
      (ct_tail hz.nv fun x y ⟨hx, hy⟩ => ⟨by rw [hx.sp, hy.sp, hp3], fun r hr => ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr; rw [hx.x19, hy.x19]
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Frames, depth, and calls of `xmssTree` -/

theorem xmss_noFrames (T : Thash4Impl p.n) (t4name wn ln : String) (hC : Callees p T t4name) :
    (xmssCode p T t4name wn ln).noFrames = true := by
  simp only [xmssCode, Impl.SlhDsa.AArch64.Xmss.xmssTree, Impl.SlhDsa.AArch64.Xmss.leafBody,
    Impl.SlhDsa.AArch64.Xmss.heights, Code.noFrames, hC.wotsNF, hC.levelsNF, Bool.and_self]

theorem xmss_depth (L : Layout) (hp : Nat) (t4name wn ln : String) (t4 : Prog isa)
    (hW : (Impl.SlhDsa.AArch64.Wots.wotsLeaves4 L t4name t4).aarch64Depth = 0)
    (hL : (Impl.SlhDsa.AArch64.Tree.levels L t4name t4).aarch64Depth = 0) :
    (Impl.SlhDsa.AArch64.Xmss.xmssTree L hp t4name wn ln t4).aarch64Depth = 0 := by
  simp only [Impl.SlhDsa.AArch64.Xmss.xmssTree, Impl.SlhDsa.AArch64.Xmss.leafBody,
    Impl.SlhDsa.AArch64.Xmss.heights, Code.aarch64Depth, hW, hL, Nat.max_self]

/-- A call of `xmssTree`, given its precondition at the call's entry
(narrowed to the regions `rd` and `wr`). -/
theorem xmsscall_ok (hz : Sz p) (hh : Hps p.hp) (T : Thash4Impl p.n) (t4name wn ln xn : String)
    (hC : Callees p T t4name) {s : State} {rd wr : List Region}
    (hpre : (xmssContract p).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      (xmssContract p).post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call xn (xmssCode p T t4name wn ln)) s Q := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  exact WP.callV (xmss_correct hz T t4name wn ln hC hhp hhp9) hpre hc hw
    (fun s' h₁ h₂ h₃ h₄ h₅ _ h₇ h₈ => hQ s' h₁ h₂ h₃ h₄ h₅ h₇ h₈) (xmss_noFrames T t4name wn ln hC)

/-- What the cleanup of `xmssTree`'s callers needs of its code (`Scrub.sideAll`). -/
theorem xmss_side (hz : Sz p) (hh : Hps p.hp) (t4name wn ln : String) (t4 : Prog isa)
    (hW : Scrub.sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Wots.wotsLeaves4 ⟨p.n, p.len⟩ t4name t4) = true)
    (hL : Scrub.sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4) = true) :
    Scrub.sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Xmss.xmssTree ⟨p.n, p.len⟩ p.hp t4name wn ln t4) =
      true := by
  simp only [Impl.SlhDsa.AArch64.Xmss.xmssTree, Impl.SlhDsa.AArch64.Xmss.leafBody,
    Impl.SlhDsa.AArch64.Xmss.heights, Scrub.sideAll, hW, hL, Bool.and_true, Bool.true_and]
  have hl := hz.len
  generalize p.len = len at hl ⊢
  subst hl
  rcases hz.nv with e | e | e <;> rw [e] <;> rcases hh with h | h | h | h <;> rw [h] <;> decide

/-! ## A state satisfying the precondition -/

def xS : Addr := BitVec.ofNat 64 0x100000
def xSig : Addr := BitVec.ofNat 64 0x200000

/-- A state of the precondition: `scratch` and the signature apart, memory zero. -/
def xsat (p : Params) : State where
  gpr r := match r with
    | .x0 => xS | .x2 => xSig | _ => 0
  sp := 0
  mem := fun _ => 0
  rd := []
  wr := [⟨xS, scratchLen⟩, ⟨xSig, p.xmssSigLen⟩]

theorem bytes_zero (a : Addr) (n : Nat) : bytesAt (fun _ => 0) a n = List.replicate n 0 := by
  simp [bytesAt, List.map_const']

theorem xsat_pre (hz : Sz p) (hhp9 : p.hp ≤ 9) : (xmssContract p).pre (xsat p) := by
  have hn32 := hz.n32
  have hln : p.len * p.n ≤ 2144 := by rw [hz.len]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have hSL : p.xmssSigLen ≤ 2432 := by rw [xmssSigLen_eq]; have := Nat.mul_le_mul hhp9 hn32; omega
  have eS : xS.toNat = 0x100000 := rfl
  have eG : xSig.toNat = 0x200000 := rfl
  refine ⟨⟨rfl, rfl, by show xS.toNat + scratchLen ≤ 2 ^ 64; rw [eS]; decide,
    by show xSig.toNat + p.xmssSigLen ≤ 2 ^ 64; rw [eG]; omega, ?_,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0, fun k _ => bytes_zero _ _, fun k _ => bytes_zero _ _,
      fun k _ => bytes_zero _ _, fun k _ => bytes_zero _ _⟩, by show (0 : BitVec 64).toNat < 2 ^ 32; decide⟩
  exact (Offset.disjoint_of_le (r₁ := ⟨xS, Layout.oSigTmp⟩) (r₂ := ⟨xSig, p.xmssSigLen⟩)
    (by show xS.toNat + Layout.oSigTmp ≤ xSig.toNat; rw [eS, eG]; decide)
    (by show xSig.toNat + p.xmssSigLen ≤ 2 ^ 64; rw [eG]; omega)).symm

/-! ## `Verified` -/

/-- `xmssTree` for the SHAKE parameter sets, with any `thash4`. -/
theorem xmss_verified' (hz : Sz p) (hh : Hps p.hp) (T : Thash4Impl p.n) (t4name wn ln : String)
    (hC : Callees p T t4name) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Xmss.xmssTree ⟨p.n, p.len⟩ p.hp t4name wn ln T.code)
      (xmssContract p) := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  exact ⟨xmss_correct hz T t4name wn ln hC hhp hhp9, xmss_ct hz T t4name wn ln hC hh, ⟨xsat p, xsat_pre hz hhp9⟩⟩

/-- `Callees` from `levels`'s proof, `wotsLeaves4`'s being `wots4_verified`. -/
theorem callees_of (hz : Sz p) (T : Thash4Impl p.n) (t4name : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true) : Callees p T t4name :=
  ⟨Wots4.wots4_verified hz T t4name, Wots4.wots4_noFrames _ _ T.noFrames, hL, hLf⟩

/-- `xmssTree` for the SHAKE parameter sets, with any `thash4`, over its
callees' proofs. -/
theorem xmss_verified (hz : Sz p) (hh : Hps p.hp) (T : Thash4Impl p.n) (t4name wn ln : String) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Xmss.xmssTree ⟨p.n, p.len⟩ p.hp t4name wn ln T.code)
      (xmssContract p) :=
  xmss_verified' hz hh T t4name wn ln
    (callees_of hz T t4name (Levels.levels_verified hz T t4name) (Levels.levels_noFrames _ _ T.noFrames))

end VG.Proof.SlhDsa.AArch64.Xmss
