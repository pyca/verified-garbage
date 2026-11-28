module

-- separate module: the two-run proofs of `forsSign`'s subtrees, rebuilt only when they change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsSubH
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTLeaf
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`'s subtrees are constant time

The heights of a subtree (`subH_ct`), in two runs of the same subtree `U2`
of the same tree `V4`, with the same signature `AU` (`HPre`, what `sbc_ok`
needs): its first block by the taint analysis, the call of `levels` by its
contract (`RelCT.call`), whose public arguments `SB` gives the same in both
runs, the root's copy by the taint analysis.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Fors (s)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.MlKem.AArch64 (Keep)

variable {p : Params}

/-- What the heights of a subtree need: the subtree `U2` of the tree `V4`,
the signature `AU` at `dA` in the writable region `⟨SG, L⟩`, the tree's index
`idx`, `Env`, and the stack pointer `sp`. -/
structure HPre (p : Params) (S SG AU : Addr) (L dA U2 V4 idx : Nat) (pk a16 : List Byte) (sp : BitVec 64)
    (u : State) : Prop where
  x19 : u.gpr .x19 = S
  kp : (u.gpr .x20).toNat < 2 ^ 32
  x21 : u.gpr .x21 = BitVec.ofNat 64 idx
  idx : idx < 2 ^ 32
  x24 : u.gpr .x24 = AU
  x25 : u.gpr .x25 = BitVec.ofNat 64 U2
  x27 : u.gpr .x27 = BitVec.ofNat 64 V4
  X : V4 + U2 < 2 ^ 32
  scr : (⟨S, 65536⟩ : Region) ∈ u.wr
  wG : (⟨SG, L⟩ : Region) ∈ u.wr
  AU : AU = SG + BitVec.ofNat 64 dA
  dA : dA + p.n + s p.a * p.n ≤ L
  Gf : SG.toNat + L ≤ 2 ^ 64
  fit : S.toNat + 65536 ≤ 2 ^ 64
  Gd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩
  env : Env p u.mem S pk a16
  sp : u.sp = sp
  R : U2 / 2 ^ s p.a < 32

theorem HPre.sbc (hz : Sz p) (hA : As p) {S SG AU : Addr} {L dA U2 V4 idx : Nat} {pk a16 : List Byte}
    {sp : BitVec 64} {u : State} (h : HPre p S SG AU L dA U2 V4 idx pk a16 sp u) :
    WP isa (.block (sbList p.n p.a)) u (SBC p S AU pk a16 u) :=
  sbc_ok hz h.x19 h.kp h.x21 h.idx h.x24 h.x25 h.x27 h.X h.scr h.wG h.AU h.dA h.Gf h.fit h.Gd
    (by have := hA.facts.2.1; have := s_ge this; omega) h.env

/-- The public arguments of `levels`, the same in two runs. -/
theorem sbc_pub {S AU : Addr} {pk₁ a₁ pk₂ a₂ : List Byte} {u₁ v₁ u₂ v₂ : State}
    (h₁ : SBC p S AU pk₁ a₁ u₁ v₁) (h₂ : SBC p S AU pk₂ a₂ u₂ v₂) (h24₁ : u₁.gpr .x24 = AU)
    (h24₂ : u₂.gpr .x24 = AU) (hsp : u₁.sp = u₂.sp) {W : List Region} :
    (levelsContract p).pub (v₁.callEntry.withRegions [] W) (v₂.callEntry.withRegions [] W) := by
  simp only [levelsContract]
  rw [Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide),
    Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide),
    Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide),
    Wots4.ce_gpr _ _ (by decide), State.withRegions_sp, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_sp, h₁.sb.x0, h₂.sb.x0, h₁.sb.x1, h₂.sb.x1, h₁.sb.x2, h₂.sb.x2, h₁.sb.x3, h₂.sb.x3,
    h₁.sb.x4, h₂.sb.x4, h24₁, h24₂, h₁.sb.keep.sp, h₂.sb.keep.sp, hsp]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- After the call of `levels`: what the root's copy needs. -/
abbrev RC (S : Addr) (U2 : Nat) (sp : BitVec 64) (w : State) : Prop :=
  w.gpr .x19 = S ∧ w.gpr .x25 = BitVec.ofNat 64 U2 ∧ w.sp = sp ∧ (⟨S, 65536⟩ : Region) ∈ w.wr

theorem sbc_call {t4name ln : String} {t4 : Prog isa}
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4).noFrames = true)
    {S SG AU : Addr} {L dA U2 V4 idx : Nat} {pk a16 : List Byte} {sp : BitVec 64} {u v : State}
    (hu : HPre p S SG AU L dA U2 V4 idx pk a16 sp u) (hv : SBC p S AU pk a16 u v) :
    WP isa (.call ln (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4)) v (RC S U2 sp) :=
  WP.callV hL.1 hv.pre hv.c₁ hv.c₂ (fun s' _ h₂ h₃ _ h₅ _ _ _ =>
    ⟨by rw [h₅ .x19 (by decide) (by decide), hv.sb.keep.gpr .x19 (by decide), hu.x19],
      by rw [h₅ .x25 (by decide) (by decide), hv.sb.keep.gpr .x25 (by decide), hu.x25],
      by rw [h₃, hv.sb.keep.sp, hu.sp], by rw [h₂, hv.sb.keep.wr]; exact hu.scr⟩) hLf

/-- The heights of a subtree, in two runs of the same subtree. -/
theorem subH_ct (hz : Sz p) (hA : As p) {t4name ln : String} {t4 : Prog isa}
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4).noFrames = true)
    {S SG AU : Addr} {L dA U2 V4 idx₁ idx₂ : Nat} {pk₁ a₁ pk₂ a₂ : List Byte} {sp : BitVec 64} :
    RelCT isa (fun a b => HPre p S SG AU L dA U2 V4 idx₁ pk₁ a₁ sp a ∧ HPre p S SG AU L dA U2 V4 idx₂ pk₂ a₂ sp b)
      (Impl.SlhDsa.AArch64.Fors.subtreeHeights ⟨p.n, p.len⟩ p.a t4name ln t4) fun _ _ => True := by
  unfold Impl.SlhDsa.AArch64.Fors.subtreeHeights
  refine relSeq (c₁ := .block (sbList p.n p.a))
    (B₁ := fun v => ∃ u, HPre p S SG AU L dA U2 V4 idx₁ pk₁ a₁ sp u ∧ SBC p S AU pk₁ a₁ u v)
    (B₂ := fun v => ∃ u, HPre p S SG AU L dA U2 V4 idx₂ pk₂ a₂ sp u ∧ SBC p S AU pk₂ a₂ u v)
    (ct_sb hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha.sp, hb.sp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [ha.x19, hb.x19]
      · rw [ha.x24, hb.x24]
      · rw [ha.x25, hb.x25]
      · rw [ha.x27, hb.x27]⟩)
    (fun u hu => WP.mono (hu.sbc hz hA) fun v hv => ⟨u, hu, hv⟩)
    (fun u hu => WP.mono (hu.sbc hz hA) fun v hv => ⟨u, hu, hv⟩) ?_
  refine relSeq (B₁ := RC S U2 sp) (B₂ := RC S U2 sp)
    (RelCT.call hL.1 hL.2.1 [] (sbW p.n p.a S AU) fun v w ⟨⟨u, hu, hv⟩, ⟨u', hu', hw⟩⟩ =>
      ⟨hv.pre, hw.pre, sbc_pub hv hw hu.x24 hu'.x24 (by rw [hu.sp, hu'.sp]), hv.c₁, hv.c₂, hw.c₁, hw.c₂⟩)
    (fun v ⟨u, hu, hv⟩ => sbc_call hL hLf hu hv) (fun v ⟨u, hu, hv⟩ => sbc_call hL hLf hu hv)
    (ct_root hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha.2.2.1, hb.2.2.1], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [ha.1, hb.1]
      · rw [ha.2.1, hb.2.1]⟩)

/-- The heights of a subtree keep the stack pointer. -/
theorem subH_sp (hz : Sz p) (hA : As p) {t4name ln : String} {t4 : Prog isa}
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4).noFrames = true)
    {S SG AU : Addr} {L dA U2 V4 idx : Nat} {pk a16 : List Byte} {sp : BitVec 64} {u : State}
    (hu : HPre p S SG AU L dA U2 V4 idx pk a16 sp u) :
    WP isa (Impl.SlhDsa.AArch64.Fors.subtreeHeights ⟨p.n, p.len⟩ p.a t4name ln t4) u fun w => w.sp = sp := by
  unfold Impl.SlhDsa.AArch64.Fors.subtreeHeights
  refine WP.seq (WP.mono (hu.sbc hz hA) fun v hv => WP.seq (WP.mono (sbc_call hL hLf hu hv) fun w hw => ?_))
  exact rc_ok hz hw.1 hw.2.1 (by have := hu.X; omega) hu.R hw.2.2.2 fun u' k _ _ => by rw [k.sp, hw.2.2.1]

/-! ## A subtree -/

/-- What a subtree needs, at the entry of `subtreeBody`. -/
structure SPre (p : Params) (S SG AU : Addr) (L dA U2 V4 idx : Nat) (pk a16 sk : List Byte) (sp : BitVec 64)
    (u : State) : Prop where
  h : HPre p S SG AU L dA U2 V4 idx pk a16 sp u
  sk : SkAt p u.mem S sk
  XX : V4 + U2 + 2 ^ s p.a < 2 ^ 32
  out : InRegions u.wr AU p.n
  d : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩

/-- `x26 ← 0`. -/
theorem wp_j0 {u : State} : WP isa (.block [.movz .x .x26 0 0]) u fun t => Up u t .x26 0 :=
  wp_movz fun t e => WP.block_nil (by rw [show ((0 : BitVec 16).setWidth 64) = 0 from rfl] at e; exact e)

theorem s2_of (hA : As p) : 2 ≤ s p.a := by have := hA.facts.2.1; have := s_ge this; omega

/-- The loop of leaves' invariant, at its entry. -/
theorem li0 (hA : As p) {S AU : Addr} {V4 U2 idx : Nat} {pk a16 sk : List Byte} {t : State}
    (h26 : t.gpr .x26 = 0) (hE : Env p t.mem S pk a16) (hsk : SkAt p t.mem S sk) :
    LI p S AU pk a16 sk (t.gpr .x20).toNat V4 U2 idx t (2 ^ (s p.a - 2)) t := by
  have hs2 := s2_of hA
  have h4 : 2 ^ s p.a = 4 * 2 ^ (s p.a - 2) := by
    rw [show s p.a = s p.a - 2 + 2 by omega, Nat.pow_add, Nat.add_sub_cancel]; omega
  exact ⟨0, by omega, Nat.one_le_two_pow,
    ⟨fun _ _ _ _ => rfl, by rw [h26]; rfl, rfl, rfl, rfl, fun _ _ => rfl, hE, hsk,
      fun _ h => absurd h (Nat.not_lt_zero _), fun j _ => by rw [ite_eq_right (by omega)], Frame.refl _ _⟩⟩

section
variable {S SG AU : Addr} {L dA U2 V4 idx : Nat} {pk a16 sk : List Byte} {sp : BitVec 64} {u t : State}

/-- `SPre` after `x26 ← 0`. -/
abbrev SJ (p : Params) (S SG AU : Addr) (L dA U2 V4 idx : Nat) (pk a16 sk : List Byte) (sp : BitVec 64)
    (t : State) : Prop :=
  ∃ u, SPre p S SG AU L dA U2 V4 idx pk a16 sk sp u ∧ Up u t .x26 0

theorem SJ.leaves (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (name : String)
    (hp : SPre p S SG AU L dA U2 V4 idx pk a16 sk sp u) (hup : Up u t .x26 0) :
    WP isa (.loop (Impl.SlhDsa.AArch64.Fors.leafBody ⟨p.n, p.len⟩ p.a name T.code) (.nonzero .x .x9)) t
      (LS p S AU pk a16 sk (t.gpr .x20).toNat V4 U2 idx t (2 ^ s p.a)) :=
  leaves_ok hz T name (s2_of hA) (by rw [hup.other _ (by decide), hp.h.x19]) (by rw [hup.other _ (by decide)]; exact hp.h.kp)
    (by rw [hup.other _ (by decide), hp.h.x21]) hp.h.idx (by rw [hup.other _ (by decide), hp.h.x24])
    (by rw [hup.other _ (by decide), hp.h.x25]) hup.gpr (by rw [hup.other _ (by decide), hp.h.x27])
    (by rw [hup.wr]; exact hp.h.scr) hp.h.fit hp.XX (by rw [hup.wr]; exact hp.out) hp.d
    (by rw [hup.mem]; exact hp.h.env) (by rw [hup.mem]; exact hp.sk)

/-- After the loop of leaves: `HPre`. -/
theorem SJ.hpre (hp : SPre p S SG AU L dA U2 V4 idx pk a16 sk sp u) (hup : Up u t .x26 0) {w : State}
    (hw : LS p S AU pk a16 sk (t.gpr .x20).toNat V4 U2 idx t (2 ^ s p.a) w) :
    HPre p S SG AU L dA U2 V4 idx pk a16 sp w := by
  have g : ∀ r ∈ preserved, r ≠ .x26 → r ≠ .x30 → w.gpr r = u.gpr r := fun r hr h₁ h₂ => by
    rw [hw.cs r hr h₁ h₂, hup.other _ h₁]
  have hu := hp.h
  exact ⟨by rw [g .x19 (by decide) (by decide) (by decide), hu.x19],
    by rw [g .x20 (by decide) (by decide) (by decide)]; exact hu.kp,
    by rw [g .x21 (by decide) (by decide) (by decide), hu.x21], hu.idx,
    by rw [g .x24 (by decide) (by decide) (by decide), hu.x24],
    by rw [g .x25 (by decide) (by decide) (by decide), hu.x25],
    by rw [g .x27 (by decide) (by decide) (by decide), hu.x27], hu.X,
    by rw [hw.wr, hup.wr]; exact hu.scr, by rw [hw.wr, hup.wr]; exact hu.wG, hu.AU, hu.dA, hu.Gf, hu.fit, hu.Gd,
    hw.env, by rw [hw.sp, hup.sp, hu.sp], hu.R⟩

end

/-- Two runs from the same states. -/
theorem RelCT.pointwise {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ a b, P a b → RelCT isa (fun x y => x = a ∧ y = b) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- A subtree, in two runs of the same subtree of the same tree. -/
theorem sub_ct (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (t4name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true)
    {S SG AU : Addr} {L dA U2 V4 idx₁ idx₂ : Nat} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte} {sp : BitVec 64} :
    RelCT isa (fun a b => SPre p S SG AU L dA U2 V4 idx₁ pk₁ a₁ sk₁ sp a ∧
        SPre p S SG AU L dA U2 V4 idx₂ pk₂ a₂ sk₂ sp b)
      (Impl.SlhDsa.AArch64.Fors.subtreeBody ⟨p.n, p.len⟩ p.a t4name ln T.code) fun _ _ => True := by
  unfold Impl.SlhDsa.AArch64.Fors.subtreeBody
  refine relSeq (B₁ := SJ p S SG AU L dA U2 V4 idx₁ pk₁ a₁ sk₁ sp) (B₂ := SJ p S SG AU L dA U2 V4 idx₂ pk₂ a₂ sk₂ sp)
    (ct_j0 fun a b ⟨ha, hb⟩ => ⟨by rw [ha.h.sp, hb.h.sp], fun _ h => absurd h List.not_mem_nil⟩)
    (fun u hu => WP.mono wp_j0 fun t ht => ⟨u, hu, ht⟩) (fun u hu => WP.mono wp_j0 fun t ht => ⟨u, hu, ht⟩) ?_
  refine relSeq (B₁ := HPre p S SG AU L dA U2 V4 idx₁ pk₁ a₁ sp) (B₂ := HPre p S SG AU L dA U2 V4 idx₂ pk₂ a₂ sp)
    (RelCT.pointwise ?_)
    (fun t ⟨u, hu, hup⟩ => WP.mono (SJ.leaves hz hA T t4name hu hup) fun w hw => SJ.hpre hu hup hw)
    (fun t ⟨u, hu, hup⟩ => WP.mono (SJ.leaves hz hA T t4name hu hup) fun w hw => SJ.hpre hu hup hw) ?_
  · rintro a b ⟨⟨ua, h₁, ha⟩, ⟨ub, h₂, hb⟩⟩
    refine RelCT.mono (leaves_ct hz hA T t4name (pk₁ := pk₁) (a₁ := a₁) (sk₁ := sk₁) (pk₂ := pk₂) (a₂ := a₂)
      (sk₂ := sk₂) (t₁ := a) (t₂ := b)
      (by rw [ha.other _ (by decide), h₁.h.x19]) (by rw [ha.other _ (by decide)]; exact h₁.h.kp)
      (by rw [ha.other _ (by decide), h₁.h.x21]) h₁.h.idx (by rw [ha.other _ (by decide), h₁.h.x24])
      (by rw [ha.other _ (by decide), h₁.h.x25]) (by rw [ha.other _ (by decide), h₁.h.x27]) (by rw [ha.wr]; exact h₁.h.scr)
      (by rw [ha.wr]; exact h₁.out)
      (by rw [hb.other _ (by decide), h₂.h.x19]) (by rw [hb.other _ (by decide)]; exact h₂.h.kp)
      (by rw [hb.other _ (by decide), h₂.h.x21]) h₂.h.idx (by rw [hb.other _ (by decide), h₂.h.x24])
      (by rw [hb.other _ (by decide), h₂.h.x25]) (by rw [hb.other _ (by decide), h₂.h.x27]) (by rw [hb.wr]; exact h₂.h.scr)
      (by rw [hb.wr]; exact h₂.out)
      h₁.h.fit h₁.XX h₁.d (by rw [ha.sp, hb.sp, h₁.h.sp, h₂.h.sp]) (2 ^ (s p.a - 2)))
      (fun x y ⟨ex, ey⟩ => by
        subst ex ey
        exact ⟨li0 hA ha.gpr (by rw [ha.mem]; exact h₁.h.env) (by rw [ha.mem]; exact h₁.sk),
          li0 hA hb.gpr (by rw [hb.mem]; exact h₂.h.env) (by rw [hb.mem]; exact h₂.sk)⟩)
      fun _ _ _ => trivial
  refine relSeq (B₁ := fun w => w.sp = sp) (B₂ := fun w => w.sp = sp) (subH_ct hz hA hL hLf)
    (fun u hu => subH_sp hz hA hL hLf hu) (fun u hu => subH_sp hz hA hL hLf hu) (ct_nextSub hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha, hb], fun _ h => absurd h List.not_mem_nil⟩)

end VG.Proof.SlhDsa.AArch64.Fors
