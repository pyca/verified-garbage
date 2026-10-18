module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMul
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
theorem prepare_ok (hc : CfgOk p521) (hC : Law p521.C) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed p521 base g s.mem) {P : Point p521.C}
    (hpx : sv p521 base s PX < p521.C.p) (hpy : sv p521 base s PY < p521.C.p)
    (hrep : Rep p521.C (tmv p521.C p521.n base s (p521.sl PX)) (tmv p521.C p521.n base s (p521.sl PY))
      (tmv p521.C p521.n base s (p521.sl ONEP)) P) :
    WP isa (.seq P521Joint.prep7 (PubNaf.prep (packedQ p521) (p521.sl V))) s fun t =>
      Scr t base size ∧ ModOkA p521.MP' size p521.C.p t.mem base ∧
      PubNaf.NafFixed (packedQ p521) p521.C base t P (sv p521 base s V) ∧
      (∀ x ∈ winRo (packedQ p521), tmv p521.C p521.n base t x = tmv p521.C p521.n base s x) ∧
      t.sp = s.sp ∧ Unch base prepRanges s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Fixed p521 base g t.mem ∧ tmv p521.C p521.n base t (packedQ p521).P.z = 1 ∧
      (∀j<577,t.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 (sv p521 base s U) j) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x, p521.mont x < p521.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  refine WP.mono (prep_ok hs) fun s₂ ⟨hs₂,_,ga,qa,k₂,U₂⟩=>?_
  have F₂ := F.unch h7 hn (show FixedOk p521 prepRanges from by unfold FixedOk; decide) U₂
  have e₂ : ∀ {i}, i < 45 → i ≠ TMP → sv p521 base s₂ i = sv p521 base s i := fun {i} hi hT =>
    U₂.wordsVal (by
      intro w hw
      have h := fields_apart i (List.mem_range.mpr hi) hT
      simp only [prepRanges,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact Or.inl h.1
      · exact Or.inl h.2) (by
        have h := sl_le p521 h7 hi; omega)
  have tv : ∀ {i}, i < 45 → i ≠ TMP → tmv p521.C p521.n base s₂ (p521.sl i) = tmv p521.C p521.n base s (p521.sl i) :=
    fun hi hT => by
      show toM _ _ (sv p521 base s₂ _) = toM _ _ (sv p521 base s _); rw [e₂ hi hT]
  have hlt : ∀ x ∈ winRo (packedQ p521), wordsVal s₂.mem base x p521.n < p521.C.p := by
    intro x hx
    simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₂.ap (hmont _)
    · exact lt_of_eq_of_lt F₂.bm (hmont _)
    · exact lt_of_eq_of_lt F₂.zero (by omega_arith)
    · exact lt_of_eq_of_lt (e₂ (i := PX) (by decide) (by decide)) hpx
    · exact lt_of_eq_of_lt (e₂ (i := PY) (by decide) (by decide)) hpy
    · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega_arith))
  have one : tmv p521.C p521.n base s₂ (p521.sl ONEP) = 1 := onep_tmv hc F₂
  have hp : Rep p521.C (tmv p521.C p521.n base s₂ (p521.sl PX)) (tmv p521.C p521.n base s₂ (p521.sl PY))
      (tmv p521.C p521.n base s₂ (p521.sl ONEP)) P := by
    rw [tv (by decide) (by decide), tv (by decide) (by decide), tv (by decide) (by decide)]; exact hrep
  have hj : InvJ p521.C (tmv p521.C p521.n base s₂ (p521.sl PX)) (tmv p521.C p521.n base s₂ (p521.sl PY))
      (tmv p521.C p521.n base s₂ (p521.sl ONEP)) P := by
    have hh := InvJ.of_rep hC hp
    simpa only [one, Lean.Grind.Semiring.mul_one] using hh
  have nf : PubNaf.NafFixed (packedQ p521) p521.C base s₂ P (sv p521 base s V) :=
    by
      refine ⟨hlt,F₂.zero,?_,fun i hi=>qa i hi⟩
      simpa only [packedQ,VG.Impl.Ecdsa.Verify.AArch64.Cfg.packedNafQ,
        VG.Impl.Ecdsa.AArch64.Cfg.winCfg,VG.Impl.Ecdsa.AArch64.Cfg.MP',VG.Impl.Ecdsa.AArch64.Cfg.pt] using hj
  refine ⟨hs₂, modP_of (c:=p521) hc F₂.mp, nf, ?_, k₂.sp, U₂,
    k₂.rd, k₂.wr, F₂, one, ga⟩
  intro x hx
  simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [tv (i := AP) (by decide) (by decide), tv (i := BM) (by decide) (by decide),
    tv (i := ZERO) (by decide) (by decide), tv (i := PX) (by decide) (by decide),
    tv (i := PY) (by decide) (by decide), tv (i := ONEP) (by decide) (by decide)]

end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
