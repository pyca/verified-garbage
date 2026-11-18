module

public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Parent
import VerifiedGarbage.Proof.Ffdh.WordPred
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Front

/-! ### `Ffdh.X86_64.CheckDomain.Scan`, which only this module used -/

section

/-! ### `Ffdh.X86_64.CheckDomain.Minus`, which only this module used -/

section

/-! # FFDH domain validation on x86-64: p minus one -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (zeroArr)

theorem minus_one {p : CdP} {s : State} (h : Parent p s) (ho : p.P % 2 = 1) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1) s
      (StepPost p s fun t => Parent p t ∧ wv t.mem p.B (slot p.w aX) p.w = p.P - 1 ∧
        (∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i))) := by
  have hk := h.base.k1
  have hk' := h.base.k2
  obtain ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  obtain hX := slot_le (w := p.w) (show aX < 8 by decide)
  obtain hX0 := hdr_lt_slot p.w aX (show 31 < 32 by decide)
  have hZ := h.good.2
  have hn := h.outer.scr.nowrap
  obtain arrFrame : ∀ {u v : State} (hu : Parent p u),
      Outside p.B (slot p.w aX) (8 * (p.w + 2)) u.mem v.mem → Keep mmRegs u v →
      Parent p v ∧ InScr p.B p.Z u.mem v.mem ∧
        (∀ i < 32, word v.mem p.B (8 * i) = word u.mem p.B (8 * i)) := by
    intro u v hu hf k
    obtain ff : Frm p.B [(slot p.w aX, 8 * (p.w + 2))] u.mem v.mem := Frm.of_outside hf (by simp)
    exact hu.array ff (fun r he => by
      rw [List.mem_singleton.mp he]; exact ⟨by omega, by omega_using [hX, hZ]⟩) k (k.gpr (by decide))
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1
  simp only [seqs]
  refine WP.seq (WP.mono (zeroArr_ok h.good.1 hZ (by omega_using [hk, ew]) (by omega_using [hk', ew]) (show aX < 8 by decide))
    fun u₁ ⟨_, ho₁, k₁⟩ => ?_)
  obtain ⟨h₁, hi₁, hh₁⟩ := arrFrame h ho₁ k₁
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx]
    (Q := fun u => u.gpr .rsi = p.dp ∧ u.gpr .rcx = BitVec.ofNat 64 p.k ∧
      u.gpr .rbx = off p.B (slot p.w aX) ∧ u.mem = u₁.mem)
    (by xrun [State.ea, hdr, h₁.outer.rdi, hdrOff, h₁.outer.ld (show sDom < 32 by decide),
      h₁.outer.ld (show sK < 32 by decide), h₁.outer.ld (show sArr aX < 32 by decide),
      h₁.base.hdr (sDom, p.dp) (by simp [CdP.headers]),
      h₁.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]), h₁.outer.harr aX (by decide)]) rfl)
    fun u₂ ⟨⟨hsi₂, hcx₂, hbx₂, hm₂⟩, k₂⟩ => ?_)
  obtain h₂ := h₁.keep hm₂ k₂ (k₂.gpr (by decide))
  obtain hsrc := h₂.base.dom.take p.k
  refine WP.seq (WP.mono (loadBE_ok h₂.outer.scr hsi₂ hcx₂ hbx₂ h.base.plen
    (by omega_using [hk]) (by omega_using [hk']) rfl (by omega_using [ew, hX, hZ])
    (fun i hi => hsrc.rd i (by rw [h.base.plen]; exact hi))
    (fun i hi => hsrc.val i _)
    (fun i hi => Or.inr (by have := hsrc.out i (by rw [h.base.plen]; exact hi); omega_using [ew, hX, hZ, this])))
    fun u₃ ⟨hP₃, ho₃, k₃⟩ => ?_)
  obtain k₃' : Keep mmRegs u₂ u₃ := k₃.mono (by decide)
  obtain ⟨h₃, hi₃, hh₃⟩ := arrFrame h₂ (ho₃.mono (Nat.le_refl _) (by omega_using [ew])) k₃'
  obtain hbx₃ : u₃.gpr .rbx = off p.B (slot p.w aX) := (k₃.gpr (by decide)).trans hbx₂
  refine WP.mono (WP.keep [.rax]
    (Q := fun t => t.mem = u₃.mem.writeW (off p.B (slot p.w aX)) (word u₃.mem p.B (slot p.w aX) - 1))
    (by xrun [State.ea, at0, hbx₃,
      show off p.B (slot p.w aX) + BitVec.ofInt 64 0 = off p.B (slot p.w aX) from by simp,
      h₃.outer.scr.ld (show slot p.w aX + 8 ≤ p.Z by omega_using [hX, hZ]),
      h₃.outer.scr.st (show slot p.w aX + 8 ≤ p.Z by omega_using [hX, hZ])]) rfl)
    fun t ⟨hm, k⟩ => ?_
  obtain hw := writeW_outside u₃.mem p.B (d := slot p.w aX) (word u₃.mem p.B (slot p.w aX) - 1) (by omega_using [hX, hZ, hn])
  rw [← hm] at hw
  obtain kk : Keep mmRegs u₃ t := k.mono (by decide)
  obtain ⟨ht, hit, hht⟩ := arrFrame h₃ (hw.mono (Nat.le_refl _) (by omega_using [])) kk
  obtain hi : InScr p.B p.Z s.mem t.mem := hi₁.trans (by rw [hm₂] at hi₃; exact hi₃.trans hit)
  obtain hh : ∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi => by
    rw [hht i hi, hh₃ i hi, hm₂, hh₁ i hi]
  refine ⟨⟨ht, ?_, hh⟩, hi, fun i hi => hh i (by omega_using [hi]),
    keep_trans (keep_trans (keep_trans (k₁.mono (by decide)) (k₂.mono (by decide)))
      (k₃'.mono (by decide))) (kk.mono (by decide))⟩
  rw [hm, wv_dec _ _ (by omega_using [hk, ew]) (by rw [hP₃]; exact ho) (by omega_using [hX, hZ, hn]), hP₃]

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end


/-! # FFDH domain validation on x86-64: significant bytes of q -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure Scanned (p : CdP) (s : State) : Prop where
  parent : Parent p s
  ep : word s.mem p.B (8 * sEp) = p.eqp
  el : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq

theorem scan_order {p : CdP} {s : State} (h : Parent p s) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (scan sQ)) s (StepPost p s (Scanned p)) := by
  obtain hl := h.base.qlen hq
  have hk := h.base.k1
  have hk' := h.base.k2
  obtain hn : p.qb ≠ [] := by intro he; simp [he] at hl; omega_using [hk, hl]
  refine WP.mono (scan_ok h.outer (show sQ < 32 by decide) h.q
    (by rw [hl]; exact h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) hn
    (by rw [hl]; omega_using [hk']) ((h.base.dom.drop (2 * p.k)).take p.k)) fun t ⟨hep, hel, _, hf, k⟩ => ?_
  have hZ := h.good.2
  obtain hE := hdr_lt_slot p.w 8 (show sEl < 32 by decide)
  obtain hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sEp sEl sFn at * <;> omega_using [hZ, hE])
  obtain hh : ∀ i < 32, i ≠ sEp → i ≠ sEl → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi h1 h2 => hf.word_eq (fun r he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [hi])
  obtain hb : Base p t := h.base.keep hi k (by
    intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide))
  obtain ho : Outer t p.B p.Z p.w := h.outer.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sEp sEl sFn at * <;> omega_using [hZ, hE]) k.2.2 (k.gpr (by decide))
  refine ⟨⟨⟨hb, ho, ?_, ?_⟩, hep, ?_⟩, hi, ?_, k.mono (by decide)⟩
  · rw [hh _ (by decide) (by decide) (by decide)]; exact h.g
  · rw [hh _ (by decide) (by decide) (by decide)]; exact h.q
  · simpa only [hl] using hel
  · intro i hi
    exact hh i (by omega_using [hi]) (by unfold sEp sFn; omega_using [hi]) (by unfold sEl sFn; omega_using [hi])

theorem scanned_minus {p : CdP} {s : State} (h : Scanned p s) (ho : p.P % 2 = 1) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1) s
      (StepPost p s fun t => Scanned p t ∧ wv t.mem p.B (slot p.w aX) p.w = p.P - 1) :=
  WP.mono (minus_one h.parent ho) fun t ⟨⟨hp, hv, hh⟩, hi, hs, k⟩ =>
    ⟨⟨⟨hp, (hh _ (by decide)).trans h.ep, (hh _ (by decide)).trans h.el⟩, hv⟩, hi, hs, k⟩

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end


/-! # FFDH domain validation on x86-64: q's reduction workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure QWork (p : CdP) (mi : BitVec 64) (s : State) : Prop where
  base : Base p s
  ctx : SubCtx s p.B p.Z (inner p.w) p.w p.wq mi
  xv : XVals s p.B (inner p.w) p.wq mi p.Q
  ep : word s.mem p.B (8 * sEp) = p.eqp
  el : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq
  g : word s.mem p.B (8 * sG) = off p.dp p.k
  q : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)
  x : wv s.mem p.B (slot p.w aX) p.w = p.P - 1

theorem setup_order {p : CdP} {s : State} (h : Scanned p s) (hq : p.dl = 3 * p.k)
    (ho : p.Q % 2 = 1) (hx : wv s.mem p.B (slot p.w aX) p.w = p.P - 1) :
    WP isa (seqs (wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl)) s
      (StepPost p s fun t => ∃ mi, QWork p mi t) := by
  have hb := h.parent.base
  have hO := h.parent.outer
  have hk := hb.k1
  have hk' := hb.k2
  obtain ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_arith
  obtain hl := hb.qlen hq
  obtain hne : p.qb ≠ [] := by intro he; simp [he] at hl; omega_arith
  obtain hld : p.ld < p.k := by have := lead_lt hne; change lead p.qb < p.k; omega_arith
  obtain hnl : p.eqb.length = p.nq := by simp only [CdP.eqb, List.length_drop, hl]
  obtain heq : Spec.Rsa.os2ip p.eqb = p.Q := os2ip_drop_lead p.qb
  obtain h2 : 2 ≤ p.wq := Nat.le_max_left _ _
  obtain hwq : p.wq ≤ p.w := by unfold CdP.wq CdP.nq wsWords; have := hO.w2; omega_arith
  have hZ := hb.hZ
  obtain hInner : slot p.w 8 ≤ inner p.w := Nat.le_refl _
  obtain h256 : 256 ≤ slot p.wq 8 := by unfold slot hdrBytes; omega_arith
  have hn := hO.scr.nowrap
  have hroom := hO.room
  obtain hX := slot_le (w := p.w) (show aX < 8 by decide)
  refine wp_seqs_append (a := wsSetup sEl ++ ([.block [enter]] : List (Prog isa))) (b := modSetup sEp sEl)
    (by simp [wsSetup]) (by simp [modSetup, VG.Impl.Rsa.X86_64.Crt.loadArr])
    (WP.mono (wsSetup_ok (sl := sEl) (len := p.nq) hO (by decide) (by decide) h.el
      (by unfold CdP.nq; omega_arith) (by unfold CdP.nq; omega_arith)) fun u ⟨hc, _, _, hf, k⟩ => ?_)
  change SubCtx u p.B p.Z (inner p.w) p.w p.wq _ at hc
  obtain hh : ∀ i < 32, i ≠ sWs → word u.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hne => hf.word_eq (fun r he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp only; unfold sWs sFn at *; omega_arith
      · simp only; have : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega_arith
        omega_arith) (by omega_arith)
  obtain hi : InScr p.B p.Z s.mem u.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simp only; unfold sWs sFn; omega_arith
    · simp only; have : 136 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
      omega_arith)
  obtain hbu : Base p u := hb.keep hi k (by
    intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact hh _ (by dsimp only; decide) (by dsimp only; decide))
  obtain hxu : wv u.mem p.B (slot p.w aX) p.w = p.P - 1 := by
    rw [hf.wv_eq (fun r he => ?_) (by omega_arith), hx]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Or.inr (hdr_lt_slot p.w aX (show sWs < 32 by decide))
    · exact Or.inl (by omega_arith)
  obtain hsrc : Src u p.B p.Z p.eqp p.eqb := ((hbu.dom.drop (2 * p.k)).take p.k).drop p.ld
  refine WP.mono (modSetup_ok hc h2 hwq hO.w28 (show sEp < 32 by decide) (show sEl < 32 by decide)
    ((hh _ (by decide) (by decide)).trans h.ep)
    (by rw [hnl]; exact (hh _ (by decide) (by decide)).trans h.el) hsrc
    (by rw [hnl]; unfold CdP.nq; omega_arith)
    (by rw [hnl]; exact Nat.le_max_right _ _) (by rw [heq]; exact ho)) fun t ⟨mi, hc', hv, ff, kk⟩ => ?_
  rw [heq] at hv
  obtain hr : ∀ r ∈ [(slot p.wq aN, 8 * (p.wq + 2)), (slot p.wq aOne, 8 * (p.wq + 2)), (8 * sMinv, 8)],
      r.1 + r.2 ≤ slot p.wq 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact slot_le (by decide)
    · exact slot_le (by decide)
    · exact hdr_lt_slot p.wq 8 (by decide)
  obtain hL : inner p.w + slot p.wq 8 ≤ p.Z := by have := hc.hi; omega_arith
  obtain ⟨hbt, hit, hht⟩ := hbu.child hc hL ff hr kk
  obtain hx' : wv t.mem p.B (slot p.w aX) p.w = p.P - 1 := by
    rw [ff.wv_below hr (by omega_arith) (by have := hc.hi; omega_arith)
      (by omega_arith), hxu]
  refine ⟨⟨mi, ⟨hbt, hc', hv, ?_, ?_, ?_, ?_, hx'⟩⟩, hi.trans hit, ?_, keep_trans k (kk.mono (by decide))⟩
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.ep
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.el
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.parent.g
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.parent.q
  · intro i hi
    rw [hht i (by omega_arith), hh i (by omega_arith) (by unfold sWs sFn; omega_arith)]

end VG.Proof.Ffdh.X86_64.CheckDomain
