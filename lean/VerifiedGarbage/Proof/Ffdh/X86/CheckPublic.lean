module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckDomain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ffdh_check_public` on i686: the checks

`body_ok`: for a valid domain, the status of `body` is 1 exactly when y is
a valid public value (`publicValid`): `1 < y < p − 1` (`rangeMask`), and
with q, `y^q mod p = 1` (`powP` and `eqStatus`). The body runs whatever the
domain, its powers modulo `safeM p`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckPublic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes argNum_comp)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len dlen : Nat}
  {args : Nat → BitVec 32}

/-- y, of `len` bytes at synthetic argument 8, with its length at 9. -/
structure YGeo (args : Nat → BitVec 32) (base : Addr) (bytes len : Nat) (rd wr : List Region) : Prop where
  e9 : args 9 = BitVec.ofNat 32 len
  fit : (args 8).toNat + len ≤ 2 ^ 32
  rd : InRegions (rd ++ wr) (byteAddr (args 8)) len
  apart : Region.Disjoint ⟨byteAddr (args 8), len⟩ ⟨base, bytes⟩

theorem YGeo.keep {rd wr : List Region} (Y : YGeo args base bytes len rd wr) {s t : State} {rs : List Reg}
    (e : s.rd = rd ∧ s.wr = wr) (K : Keeps rs s t) : YGeo args base bytes len t.rd t.wr := by
  rw [K.2.1, K.2.2, e.1, e.2]; exact Y

/-- y's value. -/
abbrev yv (m : Mem) (args : Nat → BitVec 32) (len : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 8)) len)

/-- Bytes apart from the working space and the 40 bytes below `sp`, after a stage. -/
theorem bytes_keep (h : In Ex base bytes len args s) {p : Addr} {n : Nat}
    (apart : Region.Disjoint ⟨p, n⟩ ⟨base, bytes⟩) (hn : n ≤ 2 ^ 64) {sp : BitVec 32}
    (hb40 : Region.Disjoint ⟨p, n⟩ (below sp 40)) {m m' : Mem} (F : Frame (frameR base sp (fR len)) m m') :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  have fit := fR_fit h
  have bl := h.bytes_lt
  refine frame_bytes F (fun r hr => ?_) hn
  rw [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨q, hq, rfl⟩
  · exact hb40
  · have := fit q hq
    exact apart.sub_right (Offset.sub_base _ (by omega))

/-- y into the wide slot 12. -/
theorem loadY_ok (h : In Ex base bytes len args s) (Y : YGeo args base bytes len s.rd s.wr) :
    WP isa (load (.slot .wide 12) (one .wide) 8 9) s fun u =>
      sv u.mem base len .wide 12 = yv s.mem args len ∧
      Outside base (lo len (.slot .wide 12)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have f := Y.fit
  have lb := len_le_bc len
  have lw := h.lower
  refine WP.mono (load_ok h (one_ok .wide) (slot_fit1 h (j := 12) (by decide)) (p := 8) (l := 9) (L := len)
    (by decide) (by decide) Y.e9 (by omega) (by rw [cb1]; exact lb) f Y.rd Y.apart)
    fun u ⟨V, O, K⟩ => ⟨by rw [cw1] at V; exact V, by rw [cb1] at O; exact O, K⟩

/-- What the status is for a valid domain: `publicValid`. -/
abbrev expected (len dlen : Nat) (m : Mem) (args : Nat → BitVec 32) : Nat :=
  if Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf len (domBytes m args dlen), yv m args len⟩ then 1 else 0

/-- The body up to its first branch. -/
abbrev pubFront : List (Prog isa) :=
  [Impl.Ffdh.X86.pSetup, load (.slot .wide 12) (one .wide) 8 9, Impl.Ffdh.X86.rangeMask 12,
    Impl.Ffdh.X86.testMask]

/-- The body with q: `y^q mod p = 1`. -/
abbrev pubQ : Prog isa :=
  .seq (load (.slot .wide 11) (one .wide) 6 7) (.seq (Impl.Ffdh.X86.powP 12 11) (Impl.Ffdh.X86.eqStatus 6 3))

theorem body_eq : Impl.Ffdh.X86.CheckPublic.body = Prog.chain pubFront (.ite .e (Impl.Ffdh.X86.ret 0)
    (.seq (.block Impl.Ffdh.X86.qTest) (.ite .e (Impl.Ffdh.X86.ret 1) pubQ))) := rfl

/-- p, one, `p − 1` and y into slots 9, 14, 15 and 12, and ZF telling whether y is out of range. -/
theorem front_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (Y : YGeo args base bytes len s.rd s.wr)
    (hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below (s.gpr .esp) 40)) :
    WP isa (Prog.chain pubFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      Gate u (¬ (yv s.mem args len < pm1 len (comp s.mem args len 0) ∧ 1 < yv s.mem args len)) ∧
      sv u.mem base len .wide 9 = comp s.mem args len 0 ∧ sv u.mem base len .wide 12 = yv s.mem args len := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have yf := Y.fit
  generalize hP : comp s.mem args len 0 = p
  generalize hY : yv s.mem args len = y
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [argNum_comp, hP] at V9 V15
  have S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  refine WP.seq (WP.mono (loadY_ok I₁ (Y.keep ⟨rfl, rfl⟩ K₁)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  rw [show yv u₁.mem args len = y by rw [yv, bytes_keep h Y.apart (by omega) hy40 F₁]; exact hY] at V₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot I₁ (by decide) O₂ K₂
  have k₂ := kept_slot I₁ (a := 12) O₂
  refine WP.seq (WP.mono (rangeMask_ok S₂.inp (a := 12) (by decide)) fun u₃ ⟨I₃, e₃, O₃, K₃⟩ => ?_)
  rw [V₂, k₂.slot_eq, k₂.slot_eq, V14, V15] at e₃
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.word S₂.inp (by decide) O₃ K₃
  have k₃ := kept_word S₂.inp (d := maskOff) (by decide) (by decide) O₃
  refine WP.seq (WP.mono (testMask_ok e₃) fun u₄ ⟨z₄, m₄, K₄⟩ => WP.block_nil ?_)
  have S₄ : Step Ex base bytes len args u₃ u₄ := Step.regs S₃.inp m₄ K₄
  refine ⟨((S₁.trans S₂).trans S₃).trans S₄, Gate.of_eval z₄ ?_, by rw [m₄, k₃.slot_eq, k₂.slot_eq, V9],
    by rw [m₄, k₃.slot_eq, V₂]⟩
  by_cases a : y < pm1 len p <;> by_cases b : 1 < y <;> simp [a, b]

/-- `vg_ffdh_check_public`'s body: a status, `expected` for a valid domain. -/
theorem body_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (Y : YGeo args base bytes len s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 40))
    (hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below (s.gpr .esp) 40)) :
    WP isa Impl.Ffdh.X86.CheckPublic.body s fun t => ∃ r, Res base len s r t ∧
      (Spec.Ffdh.domainValid len (domBytes s.mem args dlen) = true → r = expected len dlen s.mem args) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have h2 : 2 * len ≤ dlen := by omega
  have hp := comp_p s.mem args h2
  have iffP := VG.Proof.Ffdh.publicValid_eq (Spec.Ffdh.domainOf len (domBytes s.mem args dlen)) (yv s.mem args len)
  rw [← hp] at iffP
  rw [body_eq]
  refine WP.chain_split (front_ok h G Y hy40) fun u₄ ⟨S, Gt, V9, V12⟩ => ?_
  generalize hP : comp s.mem args len 0 = p at iffP hp Gt V9
  generalize hY : yv s.mem args len = y at iffP Gt V12
  /- A valid domain's p is an odd number above one. -/
  have pv : Spec.Ffdh.domainValid len (domBytes s.mem args dlen) = true → 1 < p ∧ p % 2 = 1 := by
    intro v
    have mv := VG.Proof.Ffdh.domainValid_mod v
    rw [← comp_p s.mem args h2, hP] at mv
    unfold Spec.Rsa.modulusValid at mv
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
    exact ⟨by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega, mv.1.1.1⟩
  refine WP.gate Gt (fun bad => WP.mono (ret_res (base := base) (len := len)) fun t R => ⟨0, S.res R, ?_⟩)
    (fun good => ?_)
  · intro v
    obtain ⟨gt, odd⟩ := pv v
    rw [pm1_of (by omega)] at bad
    have : ¬ (1 < y ∧ y < p - 1) := fun ⟨a, b⟩ => bad ⟨b, a⟩
    have nv : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf len (domBytes s.mem args dlen), y⟩ = false := by
      cases e : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf len (domBytes s.mem args dlen), y⟩
      · rfl
      · exact absurd (iffP.mp e).1 this
    simp only [expected, hY, nv, Bool.false_eq_true, ↓reduceIte]
  have good := Classical.not_not.mp good
  have range : Spec.Ffdh.domainValid len (domBytes s.mem args dlen) = true → 1 < y ∧ y < p - 1 := by
    intro v
    obtain ⟨gt, odd⟩ := pv v
    rw [pm1_of (by omega)] at good
    exact ⟨good.2, good.1⟩
  -- With y in range: is there a q?
  refine WP.seq (WP.mono (qTest_ok S.inp G.e3 G.e12 dl) fun u₅ ⟨z₅, m₅, K₅⟩ => ?_)
  have S₅ : Step Ex base bytes len args u₄ u₅ := Step.regs S.inp m₅ K₅
  have S' := S.trans S₅
  refine WP.ite _ z₅ (fun hb₅ => WP.mono (ret_res (base := base) (len := len)) fun t R => ⟨1, S'.res R, ?_⟩)
    (fun hb₅ => ?_)
  · intro v
    have e2 : dlen = 2 * len := by simpa using hb₅
    have nq : (Spec.Ffdh.domainOf len (domBytes s.mem args dlen)).q = none := by
      rw [domBytes, e2]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega)
    have vv : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf len (domBytes s.mem args dlen), y⟩ = true :=
      iffP.mpr ⟨range v, fun q hq => by rw [nq] at hq; cases hq⟩
    simp only [expected, hY, vv, ↓reduceIte]
  -- q, and `y^q mod p`.
  have e3 : dlen = 3 * len := by
    have : ¬ dlen = 2 * len := by simpa using hb₅
    omega
  subst e3
  have G₅ := G.keep ⟨rfl, rfl⟩ S'.keeps
  refine WP.seq (WP.mono (loadComp_ok S₅.inp G₅ (k := 2) (j := 11) (by decide) (by omega) (by decide))
    fun u₆ ⟨V₆, O₆, K₆⟩ => ?_)
  rw [comp_keep h G hb40 S'.frame (by omega)] at V₆
  have S₆ : Step Ex base bytes len args u₅ u₆ := Step.slot S₅.inp (by decide) O₆ K₆
  have k₆ := kept_slot S₅.inp (a := 11) O₆
  have nine₆ : sv u₆.mem base len .wide 9 = p := by rw [k₆.slot_eq, m₅, V9]
  have y₆ : sv u₆.mem base len .wide 12 = y := by rw [k₆.slot_eq, m₅, V12]
  refine WP.seq (WP.mono (powP_ok S₆.inp (P := safeM p) (b := 12) (e := 11) (by decide) (by decide) (by decide)
    (by decide) (by rw [nine₆])) fun u₇ ⟨C₇, Y₇, one₇, F₇, _, K₇⟩ => ?_)
  rw [y₆, V₆] at Y₇
  have S₇ : Step Ex base bytes len args u₆ u₇ := Step.ops S₆.inp F₇ K₇
  refine WP.mono (eqStatus_res C₇.inp (a := 6) (b := 3) (by decide) (by decide)) fun t R => ?_
  rw [Y₇, one₇] at R
  refine ⟨_, ((S'.trans S₆).trans S₇).res R, fun v => ?_⟩
  obtain ⟨gt, odd⟩ := pv v
  rw [safeM_of gt odd]
  have hq := comp_q (len := len) s.mem args
  have key : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf len (domBytes s.mem args (3 * len)), y⟩ = true ↔
      y ^ comp s.mem args len 2 % p = 1 := by
    rw [iffP]
    constructor
    · rintro ⟨_, hc⟩; exact hc _ hq
    · intro e; exact ⟨range v, fun q' hq' => by rw [hq] at hq'; cases hq'; exact e⟩
  by_cases c : y ^ comp s.mem args len 2 % p = 1
  · simp only [expected, hY, key.mpr c, c, ↓reduceIte]
  · have nv : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf len (domBytes s.mem args (3 * len)), y⟩ = false := by
      cases e : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf len (domBytes s.mem args (3 * len)), y⟩
      · rfl
      · exact absurd (key.mp e) c
    simp only [expected, hY, nv, c, Bool.false_eq_true, ↓reduceIte]

end VG.Proof.Ffdh.X86.CheckPublic
