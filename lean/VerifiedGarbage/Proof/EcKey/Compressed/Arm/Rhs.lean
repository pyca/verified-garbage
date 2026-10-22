module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Ecdsa.Arm.Stages
import VerifiedGarbage.Proof.Ecdh.Arm.Validate
public import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main

/-! # The curve polynomial used by coordinate recovery -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdh.Arm (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.Arm (rhsOps)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Ecdh.Arm

abbrev rhsSlots : List Nat := [QXM, AP, BP, W1, W2, W3]

def rhsTail : List FOp :=
  [.mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM,
    .add W3 W2 W1, .add W2 W3 BP]

theorem rhsOps_eq (c : Cfg) : rhsOps c =
    .mul (c.sl QXM) (c.sl E) (c.sl R2P) :: rhsTail.map (FOp.rename c.sl) := rfl

theorem rhsTail_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps rhsTail e W2 = e QXM * e QXM * e QXM + e AP * e QXM + e BP := by
  simp only [rhsTail, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W1, W2, W3, QXM, AP, BP, TT, SM, RM, XM, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem rhsTail_reads : readsOk rhsTail [QXM, AP, BP] = true := by decide
theorem rhsTail_slots : ∀ op ∈ rhsTail, ∀ x ∈ op.out :: op.ins, x ∈ rhsSlots := by decide
theorem rhsTail_out : ∀ op ∈ rhsTail, op.out ∈ [W1, W2, W3, TMP] := by decide

structure RhsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  rest : Rest Mont.callClob s s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.Arm.fprog c.SP (rhsOps c)) s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (VG.Impl.Weierstrass.Arm.Mont.mulCall c.SP
    (c.sl QXM) (c.sl E) (c.sl R2P))
    (VG.Impl.Weierstrass.Arm.fprog c.SP (rhsTail.map (FOp.rename c.sl)))) s _
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 hs hf (o := QXM) (a := E) (b := R2P)
    (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega)))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hM₁ := hM.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  have a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  have b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  have hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hW : WkOk c.MP' size c.wk (· ∈ rhsSlots.map c.sl) := by
    refine ⟨wk_le c h7 rfl, ?_, sl_below_wk c h7 (by decide), sl_below_wk c h7 (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have H : ∀ i ∈ rhsSlots, i < 45 := by decide
    exact sl_below_wk c h7 (H i hi)
  have I : Inv c.MP' base size c.C.p (· ∈ rhsSlots.map c.sl) ([QXM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base o c.n)) s₁ := by
    refine ⟨hs₁, hM₁, ?_, ?_, fun _ _ => rfl, hf.of_rest k₁.rest⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ [QXM, AP, BP], i ∈ rhsSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt₁
      · show sv c base s₁ AP < _
        rw [a₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega)
      · show sv c base s₁ BP < _
        rw [b₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega)
  refine WP.mono (fprog_ok hL hW hc.fp hpR _ I (fun op hop x hx => ?_)
    (readsOk_rename c.sl rhsTail_reads)) fun s₂ ⟨PK, I₂⟩ => ?_
  · obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (rhsTail_slots _ hop₀ _ hi)
  have hw : c.sl W2 ∈ validAfter (rhsTail.map (FOp.rename c.sl)) ([QXM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [rhsTail, FOp.rename, FOp.out]))
  have v₂ := I₂.val _ hw
  rw [congrFun (runOps_rename c.sl rhsTail _ fun _ _ _ h =>
    sl_inj c hc.n0 h) W2, rhsTail_run] at v₂
  have U₁ : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  have U₂ : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s₁.mem s₂.mem := PK.unch.mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_append_left _ (List.mem_map.mpr ⟨op₀.out, List.mem_cons_of_mem _ (rhsTail_out op₀ h₀), by
        rw [FOp.out_rename]; rfl⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
      · exact List.mem_append_right _ (by simp [MP'_n])
  refine ⟨PK.scr hs₁, I₂.mod, k₁.rest.trans PK.rest,
    PK.rest.rd.trans k₁.rest.rd, PK.rest.wr.trans k₁.rest.wr,
    (U₁.trans U₂).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw), I₂.lt _ hw, ?_⟩
  simpa only [sv, MP'_n, a₁, b₁, toM_cmont hc, v₁] using v₂

end VG.Proof.EcKey.Compressed.Arm
