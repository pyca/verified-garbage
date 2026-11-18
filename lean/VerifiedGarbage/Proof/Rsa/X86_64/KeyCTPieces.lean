module

import VerifiedGarbage.Proof.Rsa.X86_64.KeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
import VerifiedGarbage.Proof.Rsa.X86_64.KeyChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyPhases
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKeyCore
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCtx
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Impl.Rsa.X86_64.CheckKeyCore
meta import VerifiedGarbage.Impl.Rsa.X86_64.Keys
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCtx
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual

/-! ### `Rsa.X86_64.KeyCTDefs`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_check_key` on x86-64: constant time, the context

Two runs agree on the public data (`KPub`: the working space, `w`, the
private values' pointers and lengths) but not on the values. Between the
pieces of `main`, both are in the checks' context (`KK`), each for its own
entry state. A piece loads the bases it needs from the header (checked by
the taint analysis from `rdi`), then runs from the registers that
correctness pins (`hdr_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

/-- The public data of the checks. -/
structure KPub where
  B : Addr
  Z : Nat
  w : Nat
  pd : Addr
  pp : Addr
  pq : Addr
  pdp : Addr
  pdq : Addr
  pqi : Addr
  dl : Nat
  pl : Nat
  ql : Nat
  /-- `n`'s length and bytes, which the word-level checks' guard reads. -/
  k : Nat
  np : Addr
  nb : List Byte

/-- What the checks read of the entry state `s`: the private values'
pointers and lengths in the header, and their bytes. -/
structure KS (p : KPub) (s : State) : Prop where
  hD : word s.mem p.B (8 * sD) = p.pd
  hDl : word s.mem p.B (8 * sDlen) = BitVec.ofNat 64 p.dl
  hP : word s.mem p.B (8 * sP) = p.pp
  hPl : word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl
  hQ : word s.mem p.B (8 * sQ) = p.pq
  hQl : word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql
  hDP : word s.mem p.B (8 * sDP) = p.pdp
  hDQ : word s.mem p.B (8 * sDQ) = p.pdq
  hQI : word s.mem p.B (8 * sQI) = p.pqi
  srD : ∃ bs, Src s p.B p.Z p.pd bs ∧ bs.length = p.dl
  srP : ∃ bs, Src s p.B p.Z p.pp bs ∧ bs.length = p.pl
  srQ : ∃ bs, Src s p.B p.Z p.pq bs ∧ bs.length = p.ql
  srDP : ∃ bs, Src s p.B p.Z p.pdp bs ∧ bs.length = p.pl
  srDQ : ∃ bs, Src s p.B p.Z p.pdq bs ∧ bs.length = p.ql
  srQI : ∃ bs, Src s p.B p.Z p.pqi bs ∧ bs.length = p.pl
  dl1 : 1 ≤ p.dl
  dl2 : p.dl ≤ 8 * p.w
  pl1 : 1 ≤ p.pl
  pl2 : p.pl ≤ 8 * p.w
  ql1 : 1 ≤ p.ql
  ql2 : p.ql ≤ 8 * p.w
  word_w1 : 6 ≤ p.w
  word_w2 : p.w < 2 ^ 24
  word_room : slot p.w 8 + slot p.w 17 ≤ p.Z
  hS : word s.mem p.B (8 * Impl.Rsa.X86_64.Keys.sStride) = BitVec.ofNat 64 (8 * (p.w + 2))
  hK : word s.mem p.B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 p.k
  hN : word s.mem p.B (8 * Impl.Bignum.X86_64.Public.sN) = p.np
  srN : Src s p.B p.Z p.np p.nb
  nl : 0 < p.nb.length

/-- In the checks' context, from some entry state. -/
def KK (p : KPub) (t : State) : Prop := ∃ s minv N, KCtx s t p.B p.Z p.w minv N ∧ KS p s

theorem KK.goodW {p : KPub} {t : State} (h : KK p t) : GoodW ⟨p.B, p.Z, p.w⟩ t :=
  let ⟨_, minv, _, c, _⟩ := h; ⟨minv, c.good, c.hZ⟩

theorem KK.rdi {p : KPub} {t : State} (h : KK p t) : t.gpr .rdi = p.B :=
  let ⟨_, _, _, c, _⟩ := h; c.good.rdi

theorem pins_kk : Pins KK [.rdi] :=
  pins_of (fun p _ => p.B) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.rdi

theorem KK.hl {p : KPub} {t : State} (h : KK p t) : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.B (8 * i)) 8 := by
  obtain ⟨_, _, _, c, _⟩ := h
  have hn := c.good.scr.nowrap
  have hZ := c.hZ
  intro i hi
  exact c.good.scr.ld (by have := hdr_lt_slot p.w 8 hi; omega_using [hZ, this])

/-- `KK` with the same memory and `rdi`. -/
theorem KK.keep {p : KPub} {t t' : State} (h : KK p t) (hm : t'.mem = t.mem) (k : Keep mmRegs t t') : KK p t' := by
  obtain ⟨s, minv, N, c, hs⟩ := h
  exact ⟨s, minv, N, c.arr (js := []) (fun x _ => congrFun hm x) (fun _ h => absurd h List.not_mem_nil) List.not_mem_nil
    List.not_mem_nil k, hs⟩

/-- A list of registers and their values, as pins. -/
def RegsAre (vs : List (Reg × BitVec 64)) (t : State) : Prop := ∀ x ∈ vs, t.gpr x.1 = x.2

theorem regsAre_cons {r : Reg} {v : BitVec 64} {vs : List (Reg × BitVec 64)} {t : State} (h : t.gpr r = v)
    (hs : RegsAre vs t) : RegsAre ((r, v) :: vs) t := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h
  · exact hs x hx

theorem regsAre_nil {t : State} : RegsAre [] t := fun _ h => absurd h List.not_mem_nil

theorem pins_regs {α : Type} (vs : α → List (Reg × BitVec 64)) {rs : List Reg} (hrs : ∀ a, (vs a).map Prod.fst = rs) :
    Pins (fun a t => RegsAre (vs a) t) rs := by
  intro a s₁ s₂ h₁ h₂ r hr
  rw [← hrs a] at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  exact (h₁ x hx).trans (h₂ x hx).symm

/-- Header loads from `rdi`, then `body` from the registers they pin. -/
theorem hdr_ct {α : Type} {Φ : α → State → Prop} (hpin : Pins Φ [.rdi]) {L : List Instr} {body : Prog isa}
    {rs : List Reg} (vs : α → List (Reg × BitVec 64)) (hrs : ∀ a, (vs a).map Prod.fst = rs)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block L) hc₁).isSome = true)
    (hB : (taint.check (Taint.ofRegs rs) body hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block L) s (RegsAre (vs a))) :
    RelCT isa (Two Φ) (.seq (.block L) body) fun _ _ => True :=
  RelCT.seq (two_piece (Ψ := fun a t => RegsAre (vs a) t) [.rdi] hpin hT hw) (two_taint rs (pins_regs vs hrs) hB)

/-- A piece constant time from `KK` that keeps it. -/
theorem kk_ct {c : Prog isa} (hct : RelCT isa (Two KK) c fun _ _ => True) (hw : ∀ p s, KK p s → WP isa c s (KK p)) :
    RelCT isa (Two KK) c (Two KK) :=
  two_post hct hw

/-! ## Clearing an array -/

theorem zeroArrK_ok {p : KPub} {s : State} (h : KK p s) {j : Nat} (hj : j < 8) (hjN : j ≠ aN) (hj1 : j ≠ aOne) :
    WP isa (VG.Impl.Rsa.X86_64.Crt.zeroArr j) s fun t => KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.w := by
  obtain ⟨s₀, minv, N, c, hs⟩ := h
  have hn := c.good.scr.nowrap
  have hZ := c.hZ
  have := c.w1
  have := c.w2
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    c.good.scr.ld (by have := hdr_lt_slot p.w 8 hi; omega_using [hZ, this])
  unfold VG.Impl.Rsa.X86_64.Crt.zeroArr
  refine WP.seq (WP.mono (WP.keep [.r8, .r12] (Q := fun t => t.gpr .r8 = off p.B (slot p.w j) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, c.good.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega_using [hj]), hl sW (by decide),
      c.good.hdr.harr j hj, c.good.hdr.hw]) rfl) fun s₁ ⟨⟨h8, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (zeroAccLoop_ok (c.good.scr.congr k₁.2.2) h8 h12 (by omega_arith) (by omega_using [this])
    (Nat.le_trans (slot_le hj) hZ)) fun t ⟨_, ho, k⟩ => ⟨⟨s₀, minv, N, c.arr
      (Arrays.of_outside (List.mem_singleton_self j) (by rw [hm₁] at ho; exact ho) (Nat.le_refl _) (Nat.le_refl _))
      (by simpa using hj) (by simpa using Ne.symm hjN) (by simpa using Ne.symm hj1) ((k₁.trans k).mono (by decide)),
      hs⟩, (k.gpr (by decide)).trans h12⟩

theorem zeroArrK_ct {j : Nat} (hj : j < 8) (hjN : j ≠ aN) (hj1 : j ≠ aOne) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))])
      hc).isSome = true) :
    RelCT isa (Two KK) (VG.Impl.Rsa.X86_64.Crt.zeroArr j) (Two fun p t => KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.w) :=
  two_post (two_map (fun p : KPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun _ _ h => h.goodW) (zeroArr_ct hj hT))
    fun _ _ h => zeroArrK_ok h hj hjN hj1

end VG.Proof.Rsa.X86_64.Key

end

end

/-!
# `vg_rsa_check_key` on x86-64: constant time of the pieces

Each piece of the checks is constant time from `KK` and keeps it: its header
loads by the taint analysis from `rdi`, the rest from the registers they
pin (`hdr_ct`), and `KK` after it from its correctness lemma (`loadK`,
`ltK`, …).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

/-- The base of array `j`. -/
abbrev kb (p : KPub) (j : Nat) : BitVec 64 := off p.B (slot p.w j)

/-- What a piece's header loads read, from `KK`. -/
theorem KK.lds {p : KPub} {t : State} (h : KK p t) : t.gpr .rdi = p.B ∧
    (∀ i < 32, InRegions (t.rd ++ t.wr) (off p.B (8 * i)) 8) ∧
    word t.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧ (∀ j < 8, word t.mem p.B (8 * sArr j) = kb p j) := by
  obtain ⟨_, _, _, c, _⟩ := h
  exact ⟨c.good.rdi, (show KK p t from ⟨_, _, _, c, ‹_›⟩).hl, c.good.hdr.hw, c.good.hdr.harr⟩

/-! ## Loading a number -/

theorem loadNumK_ct {j sp sl : Nat} (hj : j < 8) (hjN : j ≠ aN) (hj1 : j ≠ aOne) (hsp : sp < 32) (hsl : sl < 32)
    (hsp' : sp ≠ sMask) (hsl' : sl ≠ sMask) (fp : KPub → Addr) (fl : KPub → Nat)
    (hf : ∀ p s, KS p s → word s.mem p.B (8 * sp) = fp p ∧ word s.mem p.B (8 * sl) = BitVec.ofNat 64 (fl p) ∧
      (∃ bs, Src s p.B p.Z (fp p) bs ∧ bs.length = fl p) ∧ 1 ≤ fl p ∧ fl p ≤ 8 * p.w)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hZ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))])
      hc₁).isSome = true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sp)), .mov .rcx (.mem (hdr sl)),
      .mov .rbx (.mem (hdr (sArr j)))]) hc₂).isSome = true) :
    RelCT isa (Two KK) (seqs (loadNum j sp sl)) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [loadNum, seqs]
    refine RelCT.seq ((zeroArrK_ct hj hjN hj1 hZ).mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.1) h)
      (hdr_ct pins_kk (rs := [.rsi, .rcx, .rbx]) (fun p => [(.rsi, fp p), (.rcx, BitVec.ofNat 64 (fl p)), (.rbx, kb p j)]) (fun _ => rfl) hT
        (by taint_decide) fun p s h => ?_)
    obtain ⟨hdi, hl, -, hb⟩ := h.lds
    obtain ⟨s₀, _, _, c, hs⟩ := h
    obtain ⟨hp, hpl, -⟩ := hf p s₀ hs
    rw [← c.hdr sp hsp hsp'] at hp
    rw [← c.hdr sl hsl hsl'] at hpl
    exact WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = fp p ∧ t.gpr .rcx = BitVec.ofNat 64 (fl p) ∧
        t.gpr .rbx = kb p j)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sp hsp, hl sl hsl, hl (sArr j) (by unfold sArr; omega_arith), hp, hpl,
        hb j hj]) rfl)
      fun t ⟨⟨a, b, c⟩, _⟩ => regsAre_cons a (regsAre_cons b (regsAre_cons c regsAre_nil))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, h1, h2⟩ := hf p s₀ hs
    rw [← hbl] at hl h1 h2
    exact WP.mono (loadK c hj hjN hj1 hsp hsl hsp' hsl' hp hl hsrc h1 h2) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

/-! ## Masks -/

theorem ltMaskK_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr a))),
      .mov .r10 (.mem (hdr (sArr b))), .mov32 .rbp (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two KK) (seqs (ltMask a b)) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [ltMask, seqs]
    refine hdr_ct pins_kk (rs := [.rdi, .r12, .rbx, .r10]) (fun p => [(.rdi, p.B), (.r12, BitVec.ofNat 64 p.w), (.rbx, kb p a), (.r10, kb p b)])
      (fun _ => rfl) hT (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = kb p a ∧ t.gpr .r10 = kb p b)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr a) (by unfold sArr; omega_arith),
        hl (sArr b) (by unfold sArr; omega_arith), hw, hb' a ha, hb' b hb]) rfl)
      fun t ⟨⟨x, y, z⟩, k⟩ => regsAre_cons ((k.gpr (by decide)).trans hdi)
        (regsAre_cons x (regsAre_cons y (regsAre_cons z regsAre_nil)))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (ltK c ha hb) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

theorem eqOneK_ct : RelCT isa (Two KK) (seqs eqOne) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [eqOne, seqs]
    refine hdr_ct pins_kk (rs := [.rdi, .r12, .rbx, .r10]) (fun p => [(.rdi, p.B), (.r12, BitVec.ofNat 64 p.w), (.rbx, kb p aR), (.r10, kb p aOne)])
      (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = kb p aR ∧ t.gpr .r10 = kb p aOne)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aR) (by decide),
        hl (sArr aOne) (by decide), hw, hb' aR (by decide), hb' aOne (by decide)]) rfl)
      fun t ⟨⟨x, y, z⟩, k⟩ => regsAre_cons ((k.gpr (by decide)).trans hdi)
        (regsAre_cons x (regsAre_cons y (regsAre_cons z regsAre_nil)))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (eqOneK c) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

theorem eqCheckK_ct : RelCT isa (Two KK) (seqs VG.Impl.Rsa.X86_64.Crt.eqCheck) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [VG.Impl.Rsa.X86_64.Crt.eqCheck, seqs]
    refine hdr_ct pins_kk (rs := [.rdi, .r12, .rbx, .r10]) (fun p => [(.rdi, p.B), (.r12, BitVec.ofNat 64 p.w), (.rbx, kb p aAcc), (.r10, kb p aN)])
      (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = kb p aAcc ∧ t.gpr .r10 = kb p aN)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aAcc) (by decide),
        hl (sArr aN) (by decide), hw, hb' aAcc (by decide), hb' aN (by decide)]) rfl)
      fun t ⟨⟨x, y, z⟩, k⟩ => regsAre_cons ((k.gpr (by decide)).trans hdi)
        (regsAre_cons x (regsAre_cons y (regsAre_cons z regsAre_nil)))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (eqCheckK c) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

theorem decMK_ct : RelCT isa (Two KK) (seqs decM) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [decM, seqs]
    refine hdr_ct pins_kk (rs := [.r12, .rbx]) (fun p => [(.r12, BitVec.ofNat 64 p.w), (.rbx, kb p aM)])
      (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rbx, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = kb p aM)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aM) (by decide), hw,
        hb' aM (by decide)]) rfl)
      fun t ⟨⟨x, y⟩, _⟩ => regsAre_cons x (regsAre_cons y regsAre_nil)
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (decK c) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

/-! ## Products -/

theorem mulEK_ct : RelCT isa (Two KK) (seqs mulE) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [mulE, seqs]
    refine RelCT.assoc (RelCT.seq (zeroArrK_ct (j := aAcc) (by decide) (by decide) (by decide) (by taint_decide))
      (hdr_ct (Φ := fun p t => KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.w)
        (pins_of (fun p _ => p.B) fun _ _ h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.1.rdi)
        (rs := [.r12, .r9, .r8]) (fun p => [(.r12, BitVec.ofNat 64 p.w), (.r9, kb p aX), (.r8, kb p aAcc)])
        (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_))
    obtain ⟨hdi, hl, -, hb'⟩ := h.1.lds
    have hl' : InRegions (s.rd ++ s.wr) (off p.B (8 * sEv)) 8 := hl sEv (by decide)
    exact WP.mono (WP.keep [.rcx, .r9, .r8] (Q := fun t => t.gpr .r9 = kb p aX ∧ t.gpr .r8 = kb p aAcc)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl', hl (sArr aX) (by decide), hl (sArr aAcc) (by decide),
        hb' aX (by decide), hb' aAcc (by decide)]) rfl)
      fun t ⟨⟨x, y⟩, k⟩ => regsAre_cons ((k.gpr (by decide)).trans h.2) (regsAre_cons x (regsAre_cons y regsAre_nil))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (mulEK c) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

theorem zeroAccsK_ok {p : KPub} {s : State} (h : KK p s) : WP isa (seqs VG.Impl.Rsa.X86_64.Crt.zeroAccs) s (KK p) := by
  obtain ⟨s₀, minv, N, c, hs⟩ := h
  have hn := c.good.scr.nowrap
  have := c.w2
  have sl := slot_eq p.w
  refine WP.mono (zeroAccs_ok c.good c.hZ (by omega_arith)) fun t ⟨_, ho, k⟩ => ⟨s₀, minv, N, c.arr (js := [aAcc, aTmp])
    (fun x hx => ho x (by
      have h1 := hx aAcc (by simp); have h2 := hx aTmp (by simp)
      rw [sl] at h1 h2; simp only [aAcc, aTmp] at h1 h2; rw [sl]; simp only [aAcc]; omega_arith))
    (by decide) (by decide) (by decide) k, hs⟩

theorem mulPQK_ct : RelCT isa (Two KK) (seqs mulPQ) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · unfold mulPQ
    refine RelCT.seqs_append (by simp [VG.Impl.Rsa.X86_64.Crt.zeroAccs]) (by simp)
      (RelCT.seq (two_post (two_map (fun p : KPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun _ _ h => h.goodW) zeroAccs_ct)
        fun _ _ h => zeroAccsK_ok h) ?_)
    simp only [seqs]
    refine hdr_ct pins_kk (rs := [.r11, .r10, .r9, .r12, .r8]) (fun p => [(.r11, kb p aX),
      (.r10, BitVec.ofNat 64 ((p.pl + 7) / 8)), (.r9, kb p aR), (.r12, BitVec.ofNat 64 ((p.ql + 7) / 8)),
      (.r8, kb p aAcc)]) (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, _, hb'⟩ := h.lds
    obtain ⟨s₀, minv, N, cx, hs⟩ := h
    have hpl : word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl := by
      rw [cx.hdr sPlen (by decide) (by decide)]; exact hs.hPl
    have hql : word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql := by
      rw [cx.hdr sQlen (by decide) (by decide)]; exact hs.hQl
    have := hs.pl2; have := hs.ql2; have := hs.word_w2
    exact WP.mono (WP.keep [.r11, .r10, .r9, .r12, .r8] (Q := fun t => t.gpr .r11 = kb p aX ∧
        t.gpr .r10 = BitVec.ofNat 64 ((p.pl + 7) / 8) ∧ t.gpr .r9 = kb p aR ∧
        t.gpr .r12 = BitVec.ofNat 64 ((p.ql + 7) / 8) ∧ t.gpr .r8 = kb p aAcc)
      (by
        xrun [State.ea, hdr, hdi, hdrOff, hl sPlen (by decide), hl sQlen (by decide), hl (sArr aX) (by decide),
          hl (sArr aR) (by decide), hl (sArr aAcc) (by decide), hpl, hql, hb' aX (by decide), hb' aR (by decide),
          hb' aAcc (by decide)]
        exact ⟨ceil8_bv (by omega_arith), ceil8_bv (by omega_arith)⟩) rfl)
      fun t ⟨⟨a, b, c, d, e⟩, _⟩ => regsAre_cons a (regsAre_cons b (regsAre_cons c (regsAre_cons d
        (regsAre_cons e regsAre_nil))))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (mulPQK c hs.hPl hs.hQl hs.pl1 hs.ql1 hs.pl2 hs.ql2) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

end VG.Proof.Rsa.X86_64.Key
