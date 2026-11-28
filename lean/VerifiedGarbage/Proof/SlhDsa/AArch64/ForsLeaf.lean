module

-- separate module: four leaves of a FORS subtree, a stage of `forsSign`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsFront
public import VerifiedGarbage.Proof.SlhDsa.ForsSpec
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, its calls of `thash4` on the lanes `A`

A call of `thash4` on the lanes `A` of `scratch` (`acall_ok`), as `leafBody`
(`Impl/SlhDsa/AArch64/Fors.lean`) makes it twice: each lane's output is
SHAKE256 of its `2n + 32` bytes; only the outputs and `work` change.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)

variable {p : Params}

/-- What a call of `thash4` on the lanes `A` leaves. -/
structure ACall (p : Params) (S : Addr) (t t' : State) : Prop where
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r
  vcs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  out : ∀ j < 4, bytesAt t'.mem (at' S (Layout.laneA j + p.n + 32)) p.n =
    shake256 (bytesAt t.mem (at' S (Layout.laneA j)) (2 * p.n + 32)) p.n
  frame : Frame (Wots4.t4ch p.n S Layout.oA Layout.strideA) t.mem t'.mem

/-- A call of `thash4` on the lanes `A`, for messages of `2n + 32` bytes. -/
theorem acall_ok (hz : Sz p) (T : Thash4Impl p.n) (name : String) {S : Addr} {t : State} {Q : State → Prop}
    (h19 : t.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (K : ∀ t', ACall p S t t' → Q t') :
    WP isa (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA (2 * p.n + 32)) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  unfold Impl.SlhDsa.AArch64.thashCall
  refine WP.seq ?_
  rw [Wots4.thashArgs_eq ⟨p.n, p.len⟩ (o := Layout.oA) (by decide)]
  refine wp_addi (imm := Layout.oA) (by decide) fun t₂ e₂ => wp_movz fun t₃ e₃ => wp_movz fun t₄ e₄ =>
    wp_addi (imm := p.n + 32) (by omega) fun t₅ e₅ => wp_mov fun t₆ e₆ => WP.block_nil ?_
  have hm₆ : t₆.mem = t.mem := by rw [e₆.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem]
  have g0 : t₆.gpr .x0 = at' S Layout.oA := by
    rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, h19]
  refine Wots4.t4call_ok T name (s := t₆) (S := S) (o := Layout.oA) (st := Layout.strideA) (len := 2 * p.n + 32)
    (by rw [e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr]; exact hw) hfit (by decide) (by decide) g0
    (by rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.gpr, Wots4.movz_ofNat (by decide)])
    (by rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.gpr, Wots4.movz_ofNat (by omega)])
    (by rw [e₆.other _ (by decide), e₅.gpr, e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, h19, at_add,
        Nat.add_assoc])
    (by rw [e₆.gpr, e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), h19])
    (by omega) (by omega) (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega)
    fun t₇ r₇ w₇ sp₇ g₇ v₇ o₇ f₇ => K t₇ ⟨by rw [r₇, e₆.rd, e₅.rd, e₄.rd, e₃.rd, e₂.rd],
      by rw [w₇, e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr], by rw [sp₇, e₆.sp, e₅.sp, e₄.sp, e₃.sp, e₂.sp],
      fun r hr h30 => ?_, fun r hr => by rw [v₇ r hr, e₆.v, e₅.v, e₄.v, e₃.v, e₂.v], fun j hj => ?_,
      by rw [← hm₆]; exact f₇⟩
  · have hr' : r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    rw [g₇ r hr h30, e₆.other _ hr'.2.2.2.2, e₅.other _ hr'.2.2.2.1, e₄.other _ hr'.2.2.1, e₃.other _ hr'.2.1,
      e₂.other _ hr'.1]
  · have := o₇ j hj
    rw [hm₆, show Layout.oA + j * Layout.strideA = Layout.laneA j by simp only [Layout.laneA, Layout.strideA, Layout.oA]; omega] at this
    exact this

/-- The fields of lane `k` of the lanes `A` (`ty`, `kp`, 0, `x`). -/
abbrev lfld (ty kp x : Nat) : List Byte := toByte ty 4 ++ (toByte kp 4 ++ (toByte 0 4 ++ toByte x 4))

/-- What `leafAdrs ty k` and the copy of `SK.seed` leave in lane `k`. -/
structure LaneP (p : Params) (S : Addr) (t t' : State) (k ty x : Nat) : Prop where
  keep : Keep [.x9, .x11, .x14] t t'
  fld : bytesAt t'.mem (at' S (Layout.laneA k + p.n + 16)) 16 = lfld ty (t.gpr .x20).toNat x
  msg : bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n = bytesAt t.mem (at' S Layout.oSkSeed) p.n
  frame : Frame [⟨at' S (Layout.laneA k + p.n + 16), 16 + p.n⟩] t.mem t'.mem

theorem lane_ok (hz : Sz p) {S : Addr} {k ty x : Nat} {t : State} {is : List Instr} {Q : State → Prop}
    (hk : k < 4) (h19 : t.gpr .x19 = S) (hKP : (t.gpr .x20).toNat < 2 ^ 32)
    (h10 : t.gpr .x10 = BitVec.ofNat 64 (x - k)) (hkx : k ≤ x) (hx : x < 2 ^ 32)
    (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    (K : ∀ t', LaneP p S t t' k ty x → WP isa (.block is) t' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Fors.leafAdrs ⟨p.n, p.len⟩ ty k ++
      Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).msgOff) .x19 Layout.oSkSeed
        (p.n / 8) ++ is)) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hL := laneA_eq k
  have eK : Layout.oSkSeed = 1664 := rfl
  simp only [Impl.SlhDsa.AArch64.Fors.leafAdrs, Layout.adrsOff, Layout.msgOff, List.append_assoc]
  refine setField_ok (by decide) (by rw [hL]; omega) (by rw [h19]; exact in_scr hw (by rw [hL]; omega))
    fun t₁ f₁ => ?_
  have hb₁ : t₁.gpr .x19 = S := by rw [f₁.keep.get .x19, h19]
  refine setFieldR_ok (r := .x20) (by decide) (by rw [f₁.keep.get .x20]; exact hKP) (by rw [hL]; omega)
    (by rw [hb₁]; exact in_scr (by rw [f₁.keep.wr]; exact hw) (by rw [hL]; omega)) fun t₂ f₂ => ?_
  have hb₂ : t₂.gpr .x19 = S := by rw [f₂.keep.get .x19, hb₁]
  refine setField_ok (by decide) (by rw [hL]; omega)
    (by rw [hb₂]; exact in_scr (by rw [f₂.keep.wr, f₁.keep.wr]; exact hw) (by rw [hL]; omega)) fun t₃ f₃ => ?_
  have hb₃ : t₃.gpr .x19 = S := by rw [f₃.keep.get .x19, hb₂]
  rw [List.singleton_append]
  refine MlKem.AArch64.wp_addImm (by omega) fun t₄ o₄ e₄ => ?_
  have hx₄ : t₄.gpr .x11 = BitVec.ofNat 64 x := by
    rw [e₄, f₃.keep.get .x10, f₂.keep.get .x10, f₁.keep.get .x10, h10, ← BitVec.ofNat_add, Nat.sub_add_cancel hkx]
  have hb₄ : t₄.gpr .x19 = S := by rw [o₄.get .x19, hb₃]
  refine setFieldR_ok (r := .x11) (by decide) (by rw [hx₄, BitVec.toNat_ofNat]; omega) (by rw [hL]; omega)
    (by rw [hb₄]; exact in_scr (by rw [o₄.wr, f₃.keep.wr, f₂.keep.wr, f₁.keep.wr]; exact hw) (by rw [hL]; omega))
    fun t₅ f₅ => ?_
  have hb₅ : t₅.gpr .x19 = S := by rw [f₅.keep.get .x19, hb₄]
  have hw₅ : (⟨S, 65536⟩ : Region) ∈ t₅.wr := by rw [f₅.keep.wr, o₄.wr, f₃.keep.wr, f₂.keep.wr, f₁.keep.wr]; exact hw
  refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.laneA k + (p.n + 32)) (d₁ := Layout.oSkSeed)
    (w := p.n / 8) ⟨by decide, by decide, by rw [eK]; omega, by rw [hL]; omega,
      by rw [hb₅]; exact in_scr' hw₅ (by rw [eK]; omega), by rw [hb₅]; exact in_scr hw₅ (by rw [hL]; omega),
      by rw [hb₅]; exact disj_scr S (by rw [eK, hL]; omega) (by rw [hL]; omega) (by rw [eK]; omega)⟩
    fun t₆ k₆ f₆ c₆ => K t₆ ?_
  rw [hb₅, show 8 * (p.n / 8) = p.n by omega, show Layout.laneA k + (p.n + 32) = Layout.laneA k + p.n + 32 by omega]
    at f₆ c₆
  have e₁ := f₁.frame; have e₂ := f₂.frame; have e₃ := f₃.frame; have e₅ := f₅.frame
  have b₁ := f₁.bytes; have b₂ := f₂.bytes; have b₃ := f₃.bytes; have b₅ := f₅.bytes
  rw [h19] at e₁ b₁
  rw [hb₁] at e₂
  rw [hb₁, f₁.keep.get .x20] at b₂
  rw [hb₂] at e₃ b₃
  rw [hb₄] at e₅
  rw [hb₄, hx₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at b₅
  have hm₄ : t₄.mem = t₃.mem := o₄.mem
  -- what each write keeps
  have k1 : ∀ {m m' : Mem} {o l : Nat}, Frame [⟨at' S o, l⟩] m m' → ∀ q q', q + q' ≤ o ∨ o + l ≤ q →
      q + q' ≤ 65536 → o + l ≤ 65536 → bytesAt m' (at' S q) q' = bytesAt m (at' S q) q' := fun hf q q' h h₁ h₂ =>
    TreeBase.bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S h h₁ h₂) (by omega)
  refine ⟨((((f₁.keep.trans f₂.keep).trans f₃.keep).trans (o₄.keep.trans (f₅.keep.trans k₆))).mono (by simp)),
    ?_, ?_, ?_⟩
  · rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, bytesAt_cat, bytesAt_cat, bytesAt_cat]
    rw [k1 f₆ _ _ (by omega) (by rw [hL]; omega) (by rw [hL]; omega), k1 e₅ _ _ (by omega) (by rw [hL]; omega)
        (by rw [hL]; omega), hm₄, k1 e₃ _ _ (by omega) (by rw [hL]; omega) (by rw [hL]; omega),
      k1 e₂ _ _ (by omega) (by rw [hL]; omega) (by rw [hL]; omega), b₁,
      k1 f₆ _ _ (by omega) (by rw [hL]; omega) (by rw [hL]; omega), k1 e₅ _ _ (by omega) (by rw [hL]; omega)
        (by rw [hL]; omega), hm₄, k1 e₃ _ _ (by omega) (by rw [hL]; omega) (by rw [hL]; omega),
      show Layout.laneA k + p.n + 16 + 4 = Layout.laneA k + p.n + 20 by omega, b₂,
      k1 f₆ _ _ (by omega) (by rw [hL]; omega) (by rw [hL]; omega), k1 e₅ _ _ (by omega) (by rw [hL]; omega)
        (by rw [hL]; omega), hm₄,
      show Layout.laneA k + p.n + 20 + 4 = Layout.laneA k + p.n + 24 by omega, b₃,
      k1 f₆ _ _ (by omega) (by rw [hL]; omega) (by rw [hL]; omega),
      show Layout.laneA k + p.n + 24 + 4 = Layout.laneA k + p.n + 28 by omega, b₅]
  · rw [c₆, k1 e₅ _ _ (by rw [eK, hL]; omega) (by rw [eK]; omega) (by rw [hL]; omega), hm₄,
      k1 e₃ _ _ (by rw [eK, hL]; omega) (by rw [eK]; omega) (by rw [hL]; omega),
      k1 e₂ _ _ (by rw [eK, hL]; omega) (by rw [eK]; omega) (by rw [hL]; omega),
      k1 e₁ _ _ (by rw [eK, hL]; omega) (by rw [eK]; omega) (by rw [hL]; omega)]
  · have sub : ∀ o l, o + l ≤ 16 + p.n → ∀ r ∈ [(⟨at' S (Layout.laneA k + p.n + 16 + o), l⟩ : Region)],
        ∃ R ∈ [(⟨at' S (Layout.laneA k + p.n + 16), 16 + p.n⟩ : Region)], Region.Sub r R := fun o l ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩
    rw [show Layout.laneA k + p.n + 16 = Layout.laneA k + p.n + 16 + 0 from rfl] at e₁
    rw [show Layout.laneA k + p.n + 20 = Layout.laneA k + p.n + 16 + 4 by omega] at e₂
    rw [show Layout.laneA k + p.n + 24 = Layout.laneA k + p.n + 16 + 8 by omega] at e₃
    rw [show Layout.laneA k + p.n + 28 = Layout.laneA k + p.n + 16 + 12 by omega] at e₅
    rw [show Layout.laneA k + p.n + 32 = Layout.laneA k + p.n + 16 + 16 by omega] at f₆
    rw [← hm₄] at e₃
    exact ((((e₁.sub (sub 0 4 (by omega))).trans (e₂.sub (sub 4 4 (by omega)))).trans
      (e₃.sub (sub 8 4 (by omega)))).trans (e₅.sub (sub 12 4 (by omega)))).trans (f₆.sub (sub 16 p.n (by omega)))

end VG.Proof.SlhDsa.AArch64.Fors
