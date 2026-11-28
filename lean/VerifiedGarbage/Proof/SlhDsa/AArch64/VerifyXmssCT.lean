module

-- separate module: xmssPk's relational proofs and assembled theorems, which only verify's layer loop needs

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyXmssMain
public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyXmssCTBase
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTLeaf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `xmssPk` is constant time

Two runs of `xmssPk` from states of its precondition that agree on its
public data, which include the message at `oMsg` and so the digits, leak
the same trace (`xmssPk_ct`). Each run keeps the facts of its own
correctness, with the same digits `D`; the registers the taint analysis
needs public hold the same values in both, functions of the digits, of
`idx` and of the counters: so do the conditions of the branches and loops.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.XmssPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (relSeq relLoop wpLoop wp_subr wp_lsr)
open VG.Proof.MlKem.AArch64 (Only Keep)

variable {p : Params}

/-- Within a group's step `j`: what the step's pieces keep. -/
structure WS (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (D : List Nat) (g j : Nat) (u : State) :
    Prop where
  xk : XK p σ S sig pk a D u
  x22 : u.gpr .x22 = BitVec.ofNat 64 (4 * g)
  x23 : u.gpr .x23 = BitVec.ofNat 64 j

/-- The head of `restoreLane k`. -/
theorem rhead_ok (hz : Sz p) {σ t : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) {g k j : Nat} (hg : 4 * g < p.len) (hk : k < 4) (hj : j < 16)
    (hw : WS p σ S sig pk a D g j t) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.chainOf p k ++ ([.sub .x .x13 .x23 .x11, .lsr .x .x13 .x13 63] : List Instr))) t
      fun u => WS p σ S sig pk a D g j u ∧ u.gpr .x10 = BitVec.ofNat 64 (cOf p g k) ∧
        u.gpr .x13 = BitVec.ofNat 64 (if j < D.getD (cOf p g k) 0 then 1 else 0) := by
  have hl := hz.len
  have hn32 := hz.n32
  have hcl : cOf p g k < p.len := by simp only [cOf]; omega_using [hl, hn32]
  refine chainOf_ok hz hg hk hw.xk.x19 hw.x22 (by rw [hw.xk.wr]; exact TreeBase.regions_scr hR)
    fun t₁ o₁ c₁ d₁ => wp_subr fun t₂ u₂ => wp_lsr (sh := 63) (by decide) fun t₃ u₃ => MlKem.AArch64.wp_nil ?_
  have hd16 : digitAt t.mem S (cOf p g k) < 2 ^ 63 := by
    have := (t.mem (at' S (Layout.oDigits + cOf p g k))).isLt; simp only [digitAt]; omega_using [this]
  have K3 : Keep [.x10, .x13, .x14, .x15, .x11, .x13, .x13] t t₃ :=
    (o₁.keep.trans (upOnly u₂).keep).trans (upOnly u₃).keep
  refine ⟨⟨XK.step hz hw.xk (by decide) K3 (by rw [u₃.mem, u₂.mem, o₁.mem]; exact Frame.refl _ _)
    (fun r hr => absurd hr List.not_mem_nil), by rw [K3.get .x22, hw.x22], by rw [K3.get .x23, hw.x23]⟩,
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), c₁], ?_⟩
  rw [u₃.gpr, u₂.gpr, o₁.get .x23, hw.x23, d₁, lt_bit (by omega_using [hj]) hd16, hw.xk.dig _ hcl]

section
variable (hz : Sz p) {σ₁ σ₂ : State} {S sig : Addr} {pk₁ a₁ pk₂ a₂ : List Byte} {D : List Nat}
  (hR₁ : Regions σ₁ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hR₂ : Regions σ₂ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩)
  (hsp : σ₁.sp = σ₂.sp) (hx1 : σ₁.gpr .x1 = σ₂.gpr .x1)

include hsp hx1 in
theorem ag_xk {u v : State} (hu : XK p σ₁ S sig pk₁ a₁ D u) (hv : XK p σ₂ S sig pk₂ a₂ D v) :
    u.sp = v.sp ∧ u.gpr .x19 = v.gpr .x19 ∧ u.gpr .x20 = v.gpr .x20 ∧ u.gpr .x21 = v.gpr .x21 :=
  ⟨by rw [hu.sp, hv.sp, hsp], by rw [hu.x19, hv.x19], by rw [hu.x20, hv.x20, hx1], by rw [hu.x21, hv.x21]⟩

include hz hR₁ hR₂ hsp hx1 in
/-- `restoreLane k` in two runs. -/
theorem restoreLane_rel {g k j : Nat} (hg : 4 * g < p.len) (hk : k < 4) (hj : j < 16) :
    RelCT isa (fun a b => WS p σ₁ S sig pk₁ a₁ D g j a ∧ WS p σ₂ S sig pk₂ a₂ D g j b)
      (Impl.SlhDsa.AArch64.Verify.restoreLane p k) fun _ _ => True := by
  unfold Impl.SlhDsa.AArch64.Verify.restoreLane
  refine relSeq (ct_rhead hz hk fun x y ⟨hx, hy⟩ => ⟨(ag_xk hsp hx1 hx.xk hy.xk).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (ag_xk hsp hx1 hx.xk hy.xk).2.1
      · rw [hx.x22, hy.x22]
      · rw [hx.x23, hy.x23]⟩)
    (fun a h => rhead_ok hz hR₁ hg hk hj h) (fun b h => rhead_ok hz hR₂ hg hk hj h) ?_
  refine RelCT.ite (fun a b ⟨ha, hb⟩ => by rw [MlKem.AArch64.eval_zero, MlKem.AArch64.eval_zero, ha.2.2, hb.2.2])
    (ct_xnil fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨(ag_xk hsp hx1 hx.1.xk hy.1.xk).1, fun _ h => absurd h List.not_mem_nil⟩)
    (ct_rcopy hz hk fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨(ag_xk hsp hx1 hx.1.xk hy.1.xk).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (ag_xk hsp hx1 hx.1.xk hy.1.xk).2.1
      · rw [hx.2.1, hy.2.1]
      · exact (ag_xk hsp hx1 hx.1.xk hy.1.xk).2.2.2⟩)

end

/-! ## What each piece of a step keeps -/

section
variable (hz : Sz p) {σ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
  (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)

include hz hR in
theorem hfields_ws {g j : Nat} (hj : j < 16) {t : State} (hw : WS p σ S sig pk a D g j t) :
    WP isa (.block ((List.range 4).flatMap fun k => Impl.SlhDsa.AArch64.setFieldR .x19
      (Layout.laneA k + p.n + 28) .x23)) t (WS p σ S sig pk a D g j) := by
  have := hfields_ok hz hw.xk.x19 (by rw [hw.xk.wr]; exact TreeBase.regions_scr hR) (by omega) hw.x23 (is := [])
    (Q := WS p σ S sig pk a D g j) fun t' k f _ => WP.block_nil ⟨XK.step hz hw.xk (by decide) k f (hW_safe hz),
      by rw [k.get .x22, hw.x22], by rw [k.get .x23, hw.x23]⟩
  simp only [List.append_nil] at this
  exact this

include hz hR in
theorem thA_ws (T : Thash4Impl p.n) (name : String) {g j : Nat} {t : State} (hw : WS p σ S sig pk a D g j t) :
    WP isa (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA (2 * p.n + 32)) t
      (WS p σ S sig pk a D g j) := by
  have hfit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hR.scr_fit; simpa [scratchLen] using this
  exact thA_ok hz rfl T name hw.xk.x19 (by rw [hw.xk.wr]; exact TreeBase.regions_scr hR) hfit (.inl rfl)
    fun t' r' w' sp' g' v' _ f' => ⟨XK.call hz hw.xk r' w' sp' g' v' f' (t4ch_safe hz),
      by rw [g' _ (by decide) (by decide), hw.x22], by rw [g' _ (by decide) (by decide), hw.x23]⟩

include hz hR hidx in
theorem restoreLane_ws {g k j : Nat} (hg : 4 * g < p.len) (hk : k < 4) (hj : j < 16) {t : State}
    (hw : WS p σ S sig pk a D g j t) :
    WP isa (Impl.SlhDsa.AArch64.Verify.restoreLane p k) t (WS p σ S sig pk a D g j) := by
  have hn32 := hz.n32
  exact restoreLane_ok hz hg hk hj (hw.xk.laneIn hR hidx) hw.x22 hw.x23 fun t' k' f' _ =>
    ⟨XK.step hz hw.xk (by decide) k' f' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, _, rfl, .inr (.inr ⟨k, hk, .inl ⟨by omega, by simp only [Layout.strideA]; omega⟩⟩)⟩),
      by rw [k'.get .x22, hw.x22], by rw [k'.get .x23, hw.x23]⟩

end

section
variable (hz : Sz p) {σ₁ σ₂ : State} {S sig : Addr} {pk₁ a₁ pk₂ a₂ : List Byte} {D : List Nat}
  (hR₁ : Regions σ₁ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hR₂ : Regions σ₂ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩)
  (hidx₁ : (σ₁.gpr .x1).toNat < 2 ^ 32) (hidx₂ : (σ₂.gpr .x1).toNat < 2 ^ 32)
  (hsp : σ₁.sp = σ₂.sp) (hx1 : σ₁.gpr .x1 = σ₂.gpr .x1) (T : Thash4Impl p.n)
  {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)

include hz hR₁ hR₂ hidx₁ hidx₂ hsp hx1 ht in
/-- A step of a group in two runs. -/
theorem stepBody_rel {g j : Nat} (hg : 4 * g < p.len) (hj : j < 16) :
    RelCT isa (fun a b => WS p σ₁ S sig pk₁ a₁ D g j a ∧ WS p σ₂ S sig pk₂ a₂ D g j b)
      (Impl.SlhDsa.AArch64.Verify.stepBody p f) fun _ _ => True := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hfit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hR₁.scr_fit; simpa [scratchLen] using this
  have agW : ∀ x y, WS p σ₁ S sig pk₁ a₁ D g j x ∧ WS p σ₂ S sig pk₂ a₂ D g j y → x.sp = y.sp ∧
      x.gpr .x19 = y.gpr .x19 := fun x y ⟨hx, hy⟩ =>
    ⟨(ag_xk hsp hx1 hx.xk hy.xk).1, (ag_xk hsp hx1 hx.xk hy.xk).2.1⟩
  unfold Impl.SlhDsa.AArch64.Verify.stepBody
  rw [ht]
  refine relSeq (ct_hfields hz fun x y h => ⟨(agW x y h).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (agW x y h).2
      · rw [h.1.x23, h.2.x23]⟩)
    (fun a h => hfields_ws hz hR₁ hj h) (fun b h => hfields_ws hz hR₂ hj h) ?_
  refine relSeq (Fors.tcall_ct T f.t4name ⟨p.n, p.len⟩ rfl hn32 (fun h => ct_argsS hz h) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega)
      hfit (fun a h => ⟨h.xk.x19, by rw [h.xk.wr]; exact TreeBase.regions_scr hR₁⟩)
      (fun b h => ⟨h.xk.x19, by rw [h.xk.wr]; exact TreeBase.regions_scr hR₂⟩) fun a b ha hb => (agW a b ⟨ha, hb⟩).1)
    (fun a h => thA_ws hz hR₁ T f.t4name h) (fun b h => thA_ws hz hR₂ T f.t4name h) ?_
  refine relSeq (restoreLane_rel hz hR₁ hR₂ hsp hx1 hg (by decide) hj)
    (fun a h => restoreLane_ws hz hR₁ hidx₁ hg (by decide) hj h)
    (fun b h => restoreLane_ws hz hR₂ hidx₂ hg (by decide) hj h) ?_
  refine relSeq (restoreLane_rel hz hR₁ hR₂ hsp hx1 hg (by decide) hj)
    (fun a h => restoreLane_ws hz hR₁ hidx₁ hg (by decide) hj h)
    (fun b h => restoreLane_ws hz hR₂ hidx₂ hg (by decide) hj h) ?_
  refine relSeq (restoreLane_rel hz hR₁ hR₂ hsp hx1 hg (by decide) hj)
    (fun a h => restoreLane_ws hz hR₁ hidx₁ hg (by decide) hj h)
    (fun b h => restoreLane_ws hz hR₂ hidx₂ hg (by decide) hj h) ?_
  refine relSeq (restoreLane_rel hz hR₁ hR₂ hsp hx1 hg (by decide) hj)
    (fun a h => restoreLane_ws hz hR₁ hidx₁ hg (by decide) hj h)
    (fun b h => restoreLane_ws hz hR₂ hidx₂ hg (by decide) hj h) ?_
  exact ct_stail fun x y h => ⟨(agW x y h).1, fun _ h => absurd h List.not_mem_nil⟩

include hz hR₁ hR₂ hidx₁ hidx₂ hsp hx1 ht in
/-- A group in two runs. -/
theorem group_rel {g : Nat} (hg : 4 * g < p.len) :
    RelCT isa (fun a b => GI p σ₁ S sig pk₁ a₁ D g a ∧ GI p σ₂ S sig pk₂ a₂ D g b)
      (Impl.SlhDsa.AArch64.Verify.chainGroup p f) fun _ _ => True := by
  unfold Impl.SlhDsa.AArch64.Verify.chainGroup
  refine relSeq (B₁ := fun t₁ => ∃ t, GI p σ₁ S sig pk₁ a₁ D g t ∧ CLI p t S sig g 4 t₁)
    (B₂ := fun t₁ => ∃ t, GI p σ₂ S sig pk₂ a₂ D g t ∧ CLI p t S sig g 4 t₁)
    (ct_chainLanes hz fun x y ⟨hx, hy⟩ => ⟨(ag_xk hsp hx1 hx.xk hy.xk).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (ag_xk hsp hx1 hx.xk hy.xk).2.1
      · exact (ag_xk hsp hx1 hx.xk hy.xk).2.2.1
      · exact (ag_xk hsp hx1 hx.xk hy.xk).2.2.2
      · rw [hx.x22, hy.x22]⟩)
    (fun a h => by
      have := chainLanes_ok hz hg (h.xk.laneIn hR₁ hidx₁) h.x22 (is := [])
        (Q := fun t₁ => ∃ t, GI p σ₁ S sig pk₁ a₁ D g t ∧ CLI p t S sig g 4 t₁) fun t₁ c₁ => WP.block_nil ⟨a, h, c₁⟩
      simp only [List.append_nil] at this; exact this)
    (fun b h => by
      have := chainLanes_ok hz hg (h.xk.laneIn hR₂ hidx₂) h.x22 (is := [])
        (Q := fun t₁ => ∃ t, GI p σ₂ S sig pk₂ a₂ D g t ∧ CLI p t S sig g 4 t₁) fun t₁ c₁ => WP.block_nil ⟨b, h, c₁⟩
      simp only [List.append_nil] at this; exact this) ?_
  refine relSeq (B₁ := PM p σ₁ S sig pk₁ a₁ D g) (B₂ := PM p σ₂ S sig pk₂ a₂ D g)
    (ct_mid fun x y ⟨⟨t, ht₁, c⟩, ⟨t', ht₂, c'⟩⟩ => ⟨by rw [c.keep.sp, c'.keep.sp, ht₁.xk.sp, ht₂.xk.sp, hsp],
      fun _ h => absurd h List.not_mem_nil⟩)
    (fun a ⟨t, h, c⟩ => lanesMid_ok hz hR₁ hg h c) (fun b ⟨t, h, c⟩ => lanesMid_ok hz hR₂ hg h c) ?_
  refine relSeq (B₁ := fun u => ∃ t₃, PM p σ₁ S sig pk₁ a₁ D g t₃ ∧ SI p σ₁ t₃ S sig pk₁ a₁ D g (mnD p D g 4) 15 u)
    (B₂ := fun u => ∃ t₃, PM p σ₂ S sig pk₂ a₂ D g t₃ ∧ SI p σ₂ t₃ S sig pk₂ a₂ D g (mnD p D g 4) 15 u) ?_
    (fun a h => WP.mono (groupIte_ok hz T ht hR₁ hidx₁ hg h.h15 h.x9 h.si) fun u hu => ⟨a, h, hu⟩)
    (fun b h => WP.mono (groupIte_ok hz T ht hR₂ hidx₂ hg h.h15 h.x9 h.si) fun u hu => ⟨b, h, hu⟩)
    (ct_ends hz fun x y ⟨⟨_, _, hx⟩, ⟨_, _, hy⟩⟩ => ⟨(ag_xk hsp hx1 hx.xk hy.xk).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (ag_xk hsp hx1 hx.xk hy.xk).2.1
      · rw [hx.x22, hy.x22]⟩)
  refine RelCT.ite (fun a b ⟨ha, hb⟩ => by rw [MlKem.AArch64.eval_zero, MlKem.AArch64.eval_zero, ha.x9, hb.x9])
    (ct_xnil fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨(ag_xk hsp hx1 hx.si.xk hy.si.xk).1, fun _ h => absurd h List.not_mem_nil⟩) ?_
  refine RelCT.mono (P := fun a b => ∃ x y, (a = x ∧ PM p σ₁ S sig pk₁ a₁ D g x ∧ mnD p D g 4 ≠ 15) ∧
      (b = y ∧ PM p σ₂ S sig pk₂ a₂ D g y)) ?_ (fun a b ⟨⟨ha, hb⟩, he⟩ => ⟨a, b, ⟨rfl, ha, fun e => by
        rw [MlKem.AArch64.eval_zero, ha.x9, e, sub15_eq 15 (by decide)] at he; exact absurd he (by decide)⟩,
        ⟨rfl, hb⟩⟩) fun _ _ h => h
  refine RelCT.exists_ fun x => RelCT.exists_ fun y => ?_
  refine RelCT.mono (relLoop (I₁ := fun m u => 1 ≤ m ∧ m + mnD p D g 4 ≤ 15 ∧
        SI p σ₁ x S sig pk₁ a₁ D g (mnD p D g 4) (15 - m) u)
      (I₂ := fun m u => 1 ≤ m ∧ m + mnD p D g 4 ≤ 15 ∧ SI p σ₂ y S sig pk₂ a₂ D g (mnD p D g 4) (15 - m) u)
      (fun m => decide (m ≠ 1)) (· - 1) (fun m => ?_) (steps_step hz T ht hR₁ hidx₁ hg)
      (steps_step hz T ht hR₂ hidx₂ hg) (15 - mnD p D g 4))
    (fun a b ⟨⟨ea, ha, hne⟩, ⟨eb, hb⟩⟩ => by
      subst ea eb
      have := ha.h15
      refine ⟨⟨by omega, by omega, ?_⟩, ⟨by omega, by omega, ?_⟩⟩
      · rw [show 15 - (15 - mnD p D g 4) = mnD p D g 4 by omega]; exact ha.si
      · rw [show 15 - (15 - mnD p D g 4) = mnD p D g 4 by omega]; exact hb.si) fun _ _ _ => trivial
  by_cases hm : 1 ≤ m ∧ m + mnD p D g 4 ≤ 15
  · exact RelCT.mono (stepBody_rel hz hR₁ hR₂ hidx₁ hidx₂ hsp hx1 T ht hg (j := 15 - m) (by omega))
      (fun a b ⟨⟨_, _, ha⟩, ⟨_, _, hb⟩⟩ => ⟨⟨ha.xk, ha.x22, ha.x23⟩, ⟨hb.xk, hb.x22, hb.x23⟩⟩) fun _ _ h => h
  · exact RelCT.of_false fun a b ⟨⟨h1, h2, _⟩, _⟩ => hm ⟨h1, h2⟩

include hz hR₁ hR₂ hidx₁ hidx₂ hsp hx1 ht in
/-- The groups' loop in two runs. -/
theorem chains_rel (ha₁ : a₁.length = 16) (ha₂ : a₂.length = 16) (hD : ∀ i < p.len, D.getD i 0 < 16) :
    RelCT isa (fun a b => (1 ≤ nG p ∧ nG p ≤ nG p ∧ GI p σ₁ S sig pk₁ a₁ D (nG p - nG p) a) ∧
      (1 ≤ nG p ∧ nG p ≤ nG p ∧ GI p σ₂ S sig pk₂ a₂ D (nG p - nG p) b))
      (.loop (Impl.SlhDsa.AArch64.Verify.chainGroup p f) (.nonzero .x .x9)) fun _ _ => True :=
  RelCT.mono (relLoop (fun m => decide (m ≠ 1)) (· - 1) (fun m => by
      by_cases hm : 1 ≤ m ∧ m ≤ nG p
      · have hl := hz.len
        exact RelCT.mono (group_rel hz hR₁ hR₂ hidx₁ hidx₂ hsp hx1 T ht (g := nG p - m)
          (by simp only [nG]; omega)) (fun a b ⟨⟨_, _, ha⟩, ⟨_, _, hb⟩⟩ => ⟨ha, hb⟩) fun _ _ h => h
      · exact RelCT.of_false fun a b ⟨⟨h1, h2, _⟩, _⟩ => hm ⟨h1, h2⟩)
    (groups_step hz T ht hR₁ hidx₁ ha₁ hD) (groups_step hz T ht hR₂ hidx₂ ha₂ hD) (nG p))
    (fun _ _ h => h) fun _ _ _ => trivial

include hz hR₁ hR₂ hidx₁ hidx₂ hsp hx1 ht in
/-- The WOTS⁺ public key in two runs. -/
theorem wotsPk_rel :
    RelCT isa (fun a b => XK p σ₁ S sig pk₁ a₁ D a ∧ XK p σ₂ S sig pk₂ a₂ D b)
      (Impl.SlhDsa.AArch64.Verify.wotsPk p f) fun _ _ => True := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hL := hz.len
  have hln : p.len * p.n = 2 * p.n * p.n + 3 * p.n := by rw [hL, Nat.add_mul]
  have hnn : 2 * p.n * p.n + 3 * p.n ≤ 2 * 32 * 32 + 3 * 32 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn32) hn32; omega
  have hm8 : p.len * p.n % 8 = 0 := by rw [Nat.mul_mod, hn8, Nat.mul_zero, Nat.zero_mod]
  have hfit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hR₁.scr_fit; simpa [scratchLen] using this
  have fB : ∀ {σ : State} {pk a : List Byte}, Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩ →
      (σ.gpr .x1).toNat < 2 ^ 32 → ∀ t, XK p σ S sig pk a D t →
      WP isa (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + p.n + 16) 1 ++
        Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneB 0 + p.n + 20) .x20 ++
        Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + p.n + 24) 0 ++
        Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + p.n + 28) 0)) t (XK p σ S sig pk a D) :=
    fun hR hidx t h => by
      have := fieldsB_ok hz h.x19 (by rw [h.wr]; exact TreeBase.regions_scr hR) (by rw [h.x20]; exact hidx) (is := [])
        (Q := XK _ _ S sig _ _ D) fun t' k f _ => WP.block_nil (XK.step hz h (by decide) k f (bW_safe hz))
      simp only [List.append_nil] at this; exact this
  have tB : ∀ {σ : State} {pk a : List Byte}, Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩ → ∀ t,
      XK p σ S sig pk a D t → WP isa (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ f.t4name T.code Layout.oB
        Layout.strideB (p.n + 32 + p.len * p.n)) t (XK p σ S sig pk a D) :=
    fun hR t h => thB_ok hz T f.t4name h.x19 (by rw [h.wr]; exact TreeBase.regions_scr hR) hfit rfl
      fun t' r' w' sp' g' v' _ f' => XK.call hz h r' w' sp' g' v' f' (t4chB_safe hz)
  unfold Impl.SlhDsa.AArch64.Verify.wotsPk
  rw [ht]
  refine relSeq (ct_fieldsB hz fun x y ⟨hx, hy⟩ => ⟨(ag_xk hsp hx1 hx hy).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (ag_xk hsp hx1 hx hy).2.1
      · exact (ag_xk hsp hx1 hx hy).2.2.1⟩)
    (fB hR₁ hidx₁) (fB hR₂ hidx₂) ?_
  refine relSeq (Fors.tcall_ct T f.t4name ⟨p.n, p.len⟩ rfl hn32 (fun h => ct_argsW hz h) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by simp only [Layout.strideB]; omega) (by simp only [Layout.strideB]; omega)
      hfit (fun a h => ⟨h.x19, by rw [h.wr]; exact TreeBase.regions_scr hR₁⟩)
      (fun b h => ⟨h.x19, by rw [h.wr]; exact TreeBase.regions_scr hR₂⟩) fun a b ha hb => (ag_xk hsp hx1 ha hb).1)
    (tB hR₁) (tB hR₂) ?_
  exact ct_copyW hz fun x y ⟨hx, hy⟩ => ⟨(ag_xk hsp hx1 hx hy).1, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (ag_xk hsp hx1 hx hy).2.1⟩

include hz hR₁ hR₂ hidx₁ hidx₂ hsp hx1 ht in
/-- Height `z` of the path in two runs. -/
theorem pathBody_rel (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9) {node₁ node₂ : List Byte} {z : Nat}
    (hzh : z < p.hp) :
    RelCT isa (fun a b => PI p σ₁ S sig pk₁ a₁ D node₁ z a ∧ PI p σ₂ S sig pk₂ a₂ D node₂ z b)
      (Impl.SlhDsa.AArch64.Verify.pathBody p f) fun _ _ => True := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hfit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hR₁.scr_fit; simpa [scratchLen] using this
  have fA : ∀ {σ : State} {pk a : List Byte} {nd : List Byte}, Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩ →
      (σ.gpr .x1).toNat < 2 ^ 32 → ∀ u, P2 p σ S sig pk a D nd z u →
      WP isa (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA 0 + p.n + 16) 2 ++
        Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA 0 + p.n + 20) 0 ++
        [.addImm .x .x10 .x25 1] ++ Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA 0 + p.n + 24) .x10 ++
        [.lsr .x .x26 .x26 1] ++ Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA 0 + p.n + 28) .x26)) u
        (XK p σ S sig pk a D) :=
    fun hR hidx u h => by
      have := fieldsA_ok hz h.xk.x19 (by rw [h.xk.wr]; exact TreeBase.regions_scr hR) h.x25 (by omega) h.x26
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidx) (is := []) (Q := XK _ _ S sig _ _ D)
        fun t' k f _ _ => WP.block_nil (XK.step hz h.xk (by decide) k f (aF_safe hz))
      simp only [List.append_nil] at this; exact this
  have tP : ∀ {σ : State} {pk a : List Byte}, Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩ → ∀ t,
      XK p σ S sig pk a D t → WP isa (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ f.t4name T.code Layout.oA
        Layout.strideA (3 * p.n + 32)) t fun w => w.sp = σ.sp :=
    fun hR t h => WP.mono (Fors.tcall_wp T f.t4name ⟨p.n, p.len⟩ rfl hn32 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega) h.x19
      (by rw [h.wr]; exact TreeBase.regions_scr hR) hfit) fun w hw => by rw [hw.1, h.sp]
  unfold Impl.SlhDsa.AArch64.Verify.pathBody
  rw [ht]
  refine relSeq (ct_pb1 hz fun x y ⟨hx, hy⟩ => ⟨(ag_xk hsp hx1 hx.xk hy.xk).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (ag_xk hsp hx1 hx.xk hy.xk).2.2.2
      · rw [hx.x25, hy.x25]
      · rw [hx.x26, hy.x26, hx1]⟩)
    (fun a h => pathB1_ok hz hR₁ hidx₁ hzh h) (fun b h => pathB1_ok hz hR₂ hidx₂ hzh h) ?_
  refine relSeq (ct_pite hz fun x y ⟨hx, hy⟩ => ⟨(ag_xk hsp hx1 hx.xk hy.xk).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.x9, hy.x9, hx1]
      · rw [hx.x12, hy.x12]
      · exact (ag_xk hsp hx1 hx.xk hy.xk).2.1⟩)
    (fun a h => pathIte_ok hz hR₁ hidx₁ hzh h) (fun b h => pathIte_ok hz hR₂ hidx₂ hzh h) ?_
  refine relSeq (ct_pfields hz fun x y ⟨hx, hy⟩ => ⟨(ag_xk hsp hx1 hx.xk hy.xk).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (ag_xk hsp hx1 hx.xk hy.xk).2.1
      · rw [hx.x25, hy.x25]
      · rw [hx.x26, hy.x26, hx1]⟩)
    (fA hR₁ hidx₁) (fA hR₂ hidx₂) ?_
  refine relSeq (Fors.tcall_ct T f.t4name ⟨p.n, p.len⟩ rfl hn32 (fun h => ct_argsP hz h) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega)
      hfit (fun a h => ⟨h.x19, by rw [h.wr]; exact TreeBase.regions_scr hR₁⟩)
      (fun b h => ⟨h.x19, by rw [h.wr]; exact TreeBase.regions_scr hR₂⟩) fun a b ha hb => (ag_xk hsp hx1 ha hb).1)
    (tP hR₁) (tP hR₂) ?_
  exact ct_ptail hh fun x y ⟨hx, hy⟩ => ⟨by rw [hx, hy, hsp], fun _ h => absurd h List.not_mem_nil⟩

include hz hR₁ hR₂ hidx₁ hidx₂ hsp hx1 ht in
/-- The path's loop in two runs. -/
theorem path_rel (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9) {node₁ node₂ : List Byte} :
    RelCT isa (fun a b => (1 ≤ p.hp ∧ p.hp ≤ p.hp ∧ PI p σ₁ S sig pk₁ a₁ D node₁ (p.hp - p.hp) a) ∧
      (1 ≤ p.hp ∧ p.hp ≤ p.hp ∧ PI p σ₂ S sig pk₂ a₂ D node₂ (p.hp - p.hp) b))
      (.loop (Impl.SlhDsa.AArch64.Verify.pathBody p f) (.nonzero .x .x9)) fun _ _ => True := by
  have hh9 : p.hp ≤ 9 := by omega
  exact RelCT.mono (relLoop (fun m => decide (m ≠ 1)) (· - 1) (fun m => by
      by_cases hm : 1 ≤ m ∧ m ≤ p.hp
      · exact RelCT.mono (pathBody_rel hz hR₁ hR₂ hidx₁ hidx₂ hsp hx1 T ht hh (z := p.hp - m) (by omega))
          (fun a b ⟨⟨_, _, ha⟩, ⟨_, _, hb⟩⟩ => ⟨ha, hb⟩) fun _ _ h => h
      · exact RelCT.of_false fun a b ⟨⟨h1, h2, _⟩, _⟩ => hm ⟨h1, h2⟩)
    (path_step hz T ht hR₁ hidx₁ hh9) (path_step hz T ht hR₂ hidx₂ hh9) p.hp) (fun _ _ h => h) fun _ _ _ => trivial

end

/-- The first block of the path: height 0, `idx`. -/
theorem pinit_ok (hz : Sz p) {σ u : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hx : XK p σ S sig pk a D u) {node0 : List Byte}
    (hn : bytesAt u.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n = node0) :
    WP isa (.block [.movz .x .x25 0 0, Impl.SlhDsa.AArch64.Thash4.mov .x26 .x20]) u
      (PI p σ S sig pk a D node0 0) := by
  refine TreeBase.wp_movz fun u₃ v₃ => TreeBase.wp_mov fun u₄ v₄ => MlKem.AArch64.wp_nil ?_
  have K4 : Keep [.x25, .x26] u u₄ := (upOnly v₃).keep.trans (upOnly v₄).keep
  have m4 : u₄.mem = u.mem := by rw [v₄.mem, v₃.mem]
  exact ⟨XK.step hz hx (by decide) K4 (by rw [m4]; exact Frame.refl _ _) (fun r hr => absurd hr List.not_mem_nil),
    by rw [v₄.other _ (by decide), v₃.gpr]; rfl,
    by rw [v₄.gpr, v₃.other _ (by decide), hx.x20, Nat.pow_zero, Nat.div_one]; exact ofNat_of_toNat rfl,
    by rw [m4, hn, path]⟩

/-- Two runs of `xmssPk` from states of its precondition that agree on its public data leak the same trace. -/
theorem xmssPk_ct (hz : Sz p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9) (T : Thash4Impl p.n)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code) :
    ConstantTime isa (xmssPkContract p).pre (xmssPkContract p).pub (Impl.SlhDsa.AArch64.Verify.xmssPk p f) := by
  have hh9 : p.hp ≤ 9 := by omega
  have hh1 : 1 ≤ p.hp := by omega
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨hp0, hp1, hp2, hsp, -, hmsg⟩ := hpub
  obtain ⟨R₁, ⟨pk₁, a₁, E₁⟩, i₁⟩ := h₁
  obtain ⟨R₂, ⟨pk₂, a₂, E₂⟩, i₂⟩ := h₂
  obtain ⟨S, eS⟩ : ∃ S, s₁.gpr .x0 = S := ⟨_, rfl⟩
  have eS₂ : s₂.gpr .x0 = S := by rw [← hp0, eS]
  have hR₁ : Regions s₁ S [⟨s₁.gpr .x2, p.xmssSigLen⟩] ⟨S, 0⟩ := by rw [← eS]; exact R₁
  have hR₂ : Regions s₂ S [⟨s₂.gpr .x2, p.xmssSigLen⟩] ⟨S, 0⟩ := by rw [← eS₂]; exact R₂
  have hR₂' : Regions s₂ S [⟨s₁.gpr .x2, p.xmssSigLen⟩] ⟨S, 0⟩ := by rw [hp2]; exact hR₂
  rw [eS] at E₁ hmsg
  rw [eS₂] at E₂ hmsg
  have hidx₁ : (s₁.gpr .x1).toNat < 2 ^ 32 := Nat.lt_of_lt_of_le i₁ (Nat.pow_le_pow_right (by decide) (by omega))
  have hidx₂ : (s₂.gpr .x1).toNat < 2 ^ 32 := Nat.lt_of_lt_of_le i₂ (Nat.pow_le_pow_right (by decide) (by omega))
  have ha₁ := TreeBase.env_a16 E₁
  have ha₂ := TreeBase.env_a16 E₂
  obtain ⟨M, eM⟩ : ∃ M, bytesAt s₁.mem (at' S Layout.oMsg) p.n = M := ⟨_, rfl⟩
  have hD : ∀ i < p.len, (wotsDigits p M).getD i 0 < 16 := fun i _ => by
    have := wotsDigits_getD_lt (p := p) M i
    simp only [Params.w, hz.lgw] at this; exact this
  have hx1 : s₁.gpr .x1 = s₂.gpr .x1 := hp1
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.SlhDsa.AArch64.Verify.xmssPk p f) fun _ _ => True := by
    unfold Impl.SlhDsa.AArch64.Verify.xmssPk
    refine relSeq (B₁ := fun u => XK p s₁ S (s₁.gpr .x2) pk₁ a₁ (wotsDigits p M) u ∧ u.gpr .x22 = BitVec.ofNat 64 0)
      (B₂ := fun u => XK p s₂ S (s₁.gpr .x2) pk₂ a₂ (wotsDigits p M) u ∧ u.gpr .x22 = BitVec.ofNat 64 0)
      (ct_xentry hz fun x y ⟨hx, hy⟩ => ⟨by rw [hx, hy, hsp], fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx, hy, hp0]⟩)
      (fun x hx => by
        subst hx; exact WP.mono (entry_ok hz eS hR₁ E₁) fun u ⟨h, h22⟩ => ⟨by rw [eM] at h; exact h, h22⟩)
      (fun y hy => by
        subst hy
        exact WP.mono (entry_ok hz eS₂ hR₂ E₂) fun u ⟨h, h22⟩ => ⟨by rw [← hmsg, eM, ← hp2] at h; exact h, h22⟩) ?_
    refine relSeq (B₁ := fun u => XK p s₁ S (s₁.gpr .x2) pk₁ a₁ (wotsDigits p M) u ∧
        ∀ c < p.len, bytesAt u.mem (at' S (endAt p c)) p.n = chainEnd p s₁ (s₁.gpr .x2) pk₁ a₁ (wotsDigits p M) c)
      (B₂ := fun u => XK p s₂ S (s₁.gpr .x2) pk₂ a₂ (wotsDigits p M) u ∧
        ∀ c < p.len, bytesAt u.mem (at' S (endAt p c)) p.n = chainEnd p s₂ (s₁.gpr .x2) pk₂ a₂ (wotsDigits p M) c)
      (RelCT.mono (chains_rel hz hR₁ hR₂' hidx₁ hidx₂ hsp hx1 T ht ha₁ ha₂ hD) (fun a b ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩ =>
        have hl := hz.len
        ⟨⟨by simp only [nG]; omega, Nat.le_refl _, by rw [Nat.sub_self]; exact ⟨ha, ha', fun c hc => absurd hc (by omega)⟩⟩,
          ⟨by simp only [nG]; omega, Nat.le_refl _, by rw [Nat.sub_self]; exact ⟨hb, hb', fun c hc => absurd hc (by omega)⟩⟩⟩)
        fun _ _ h => h)
      (fun a ⟨h, h22⟩ => chains_ok hz T ht hR₁ hidx₁ ha₁ hD h h22)
      (fun b ⟨h, h22⟩ => chains_ok hz T ht hR₂' hidx₂ ha₂ hD h h22) ?_
    refine relSeq (B₁ := fun u => XK p s₁ S (s₁.gpr .x2) pk₁ a₁ (wotsDigits p M) u ∧
        bytesAt u.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n = shake256 (pk₁ ++ adrsOf a₁ 1 (s₁.gpr .x1).toNat 0 0 ++
          (List.range p.len).flatMap (chainEnd p s₁ (s₁.gpr .x2) pk₁ a₁ (wotsDigits p M))) p.n)
      (B₂ := fun u => XK p s₂ S (s₁.gpr .x2) pk₂ a₂ (wotsDigits p M) u ∧
        bytesAt u.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n = shake256 (pk₂ ++ adrsOf a₂ 1 (s₂.gpr .x1).toNat 0 0 ++
          (List.range p.len).flatMap (chainEnd p s₂ (s₁.gpr .x2) pk₂ a₂ (wotsDigits p M))) p.n)
      (RelCT.mono (wotsPk_rel hz hR₁ hR₂' hidx₁ hidx₂ hsp hx1 T ht) (fun a b ⟨ha, hb⟩ => ⟨ha.1, hb.1⟩) fun _ _ h => h)
      (fun a ⟨h, hE⟩ => wotsPk_ok hz T ht hR₁ hidx₁ h hE) (fun b ⟨h, hE⟩ => wotsPk_ok hz T ht hR₂' hidx₂ h hE) ?_
    refine relSeq (ct_pinit fun x y ⟨hx, hy⟩ => ⟨(ag_xk hsp hx1 hx.1 hy.1).1, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (ag_xk hsp hx1 hx.1 hy.1).2.2.1⟩)
      (fun a ⟨h, hn⟩ => pinit_ok hz h hn) (fun b ⟨h, hn⟩ => pinit_ok hz h hn) ?_
    refine relSeq (RelCT.mono (path_rel hz hR₁ hR₂' hidx₁ hidx₂ hsp hx1 T ht hh) (fun a b ⟨ha, hb⟩ =>
        ⟨⟨hh1, Nat.le_refl _, by rw [Nat.sub_self]; exact ha⟩, ⟨hh1, Nat.le_refl _, by rw [Nat.sub_self]; exact hb⟩⟩)
        fun _ _ h => h)
      (fun a h => path_ok hz T ht hR₁ hidx₁ hh1 hh9 h) (fun b h => path_ok hz T ht hR₂' hidx₂ hh1 hh9 h) ?_
    exact ct_xepi hz fun x y ⟨hx, hy⟩ => ⟨(ag_xk hsp hx1 hx.xk hy.xk).1, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (ag_xk hsp hx1 hx.xk hy.xk).2.1⟩
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified`, and calls of `xmssPk` -/

/-- The first part of `Verified`. -/
theorem xmssPk_correct (hz : Sz p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9) (T : Thash4Impl p.n)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code) :
    ∀ s, (xmssPkContract p).pre s → ∃ t s', Exec isa (Impl.SlhDsa.AArch64.Verify.xmssPk p f) s t s' ∧
      abiPreserved s s' ∧ (xmssPkContract p).post s s' := fun s h => by
  obtain ⟨t, s', e, abi, post⟩ := xmssPk_wp hz T ht (by omega) (by omega) h
  exact ⟨t, s', e, abi, post⟩

theorem xmssPk_noFrames (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) (h : f.t4.noFrames = true) :
    (Impl.SlhDsa.AArch64.Verify.xmssPk p f).noFrames = true := by
  simp only [Impl.SlhDsa.AArch64.Verify.xmssPk, Impl.SlhDsa.AArch64.Verify.chainGroup,
    Impl.SlhDsa.AArch64.Verify.stepBody, Impl.SlhDsa.AArch64.Verify.restoreLane, Impl.SlhDsa.AArch64.Verify.wotsPk,
    Impl.SlhDsa.AArch64.Verify.pathBody, Impl.SlhDsa.AArch64.thashCall, Code.noFrames, h, Bool.and_self]

theorem xmssPk_depth (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) (h : f.t4.aarch64Depth = 0) :
    (Impl.SlhDsa.AArch64.Verify.xmssPk p f).aarch64Depth = 0 := by
  simp only [Impl.SlhDsa.AArch64.Verify.xmssPk, Impl.SlhDsa.AArch64.Verify.chainGroup,
    Impl.SlhDsa.AArch64.Verify.stepBody, Impl.SlhDsa.AArch64.Verify.restoreLane, Impl.SlhDsa.AArch64.Verify.wotsPk,
    Impl.SlhDsa.AArch64.Verify.pathBody, Impl.SlhDsa.AArch64.thashCall, Code.aarch64Depth, h, Nat.max_self]

theorem bytes_zeroX (a : Addr) (n : Nat) : bytesAt (fun _ => 0) a n = List.replicate n 0 := by
  simp [bytesAt, List.map_const']

def xS : Addr := BitVec.ofNat 64 0x100000
def xSig : Addr := BitVec.ofNat 64 0x200000

/-- A state of the precondition: `scratch` and the signature apart, memory zero. -/
def xmssPkSat (p : Params) : State where
  gpr r := match r with
    | .x0 => xS | .x2 => xSig | _ => 0
  sp := 0
  mem := fun _ => 0
  rd := [⟨xSig, p.xmssSigLen⟩]
  wr := [⟨xS, scratchLen⟩, ⟨xS, 0⟩]

theorem xmssPkSat_pre (hz : Sz p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9) :
    (xmssPkContract p).pre (xmssPkSat p) := by
  have hSL : p.xmssSigLen ≤ 2432 := by
    rcases hz.nv with e | e | e <;> rcases hh with h | h | h | h <;>
      (simp only [Params.xmssSigLen, hz.len, e, h]; decide)
  have eS : xS.toNat = 0x100000 := rfl
  have eG : xSig.toNat = 0x200000 := rfl
  refine ⟨⟨rfl, rfl, by show xS.toNat + scratchLen ≤ 2 ^ 64; rw [eS]; decide,
    by show xS.toNat + 0 ≤ 2 ^ 64; rw [eS]; decide, fun x h _ => by simp [Region.Contains] at h,
    fun r hr => ?_, fun r hr => ?_⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0, fun k _ => bytes_zeroX _ _, fun k _ => bytes_zeroX _ _,
      fun k _ => bytes_zeroX _ _, fun k _ => bytes_zeroX _ _⟩, by
      show (0 : BitVec 64).toNat < 2 ^ p.hp; exact Nat.two_pow_pos _⟩
  · simp only [List.mem_singleton] at hr; subst hr
    show xSig.toNat + p.xmssSigLen ≤ 2 ^ 64; rw [eG]; omega
  · simp only [List.mem_singleton] at hr; subst hr
    exact (Offset.disjoint_of_le (r₁ := ⟨xS, scratchLen⟩) (r₂ := ⟨xSig, p.xmssSigLen⟩)
      (by show xS.toNat + scratchLen ≤ xSig.toNat; rw [eS, eG]; decide)
      (by show xSig.toNat + p.xmssSigLen ≤ 2 ^ 64; rw [eG]; omega)).symm

/-- `xmssPk` meets `xmssPkContract`, for the six SHAKE parameter sets and
every implementation of `thash4`. -/
theorem xmssPk_verified (hz : Sz p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9) (T : Thash4Impl p.n)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Verify.xmssPk p f) (xmssPkContract p) :=
  ⟨xmssPk_correct hz hh T ht, xmssPk_ct hz hh T ht, ⟨xmssPkSat p, xmssPkSat_pre hz hh⟩⟩

/-- A call of `xmssPk`, given its precondition at the call's entry (narrowed
to the regions `rd` and `wr`). -/
theorem xmssPkcall_ok (hz : Sz p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9) (T : Thash4Impl p.n)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code) (fn : String) {s : State} {rd wr : List Region}
    (hpre : (xmssPkContract p).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      (xmssPkContract p).post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call fn (Impl.SlhDsa.AArch64.Verify.xmssPk p f)) s Q :=
  WP.callV (xmssPk_correct hz hh T ht) hpre hc hw (fun s' h₁ h₂ h₃ h₄ h₅ _ h₇ h₈ => hQ s' h₁ h₂ h₃ h₄ h₅ h₇ h₈)
    (xmssPk_noFrames p f (by rw [ht]; exact T.noFrames))

end VG.Proof.SlhDsa.AArch64.XmssPk
