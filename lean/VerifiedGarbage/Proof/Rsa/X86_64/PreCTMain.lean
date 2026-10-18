module

public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.PreMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.PreMain
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_precompute` on x86-64: constant time of `main`

Two runs agree on `vg_rsa_check_key`'s public data (`MPub`) and on `pre`'s
pointer and length (`PPub`). Between the pieces of `main`, both are in the
checks' context with `pre`'s header slots (`PK`): the checks' pieces are
constant time from `KK` (`pk_lift`), and the new ones (the powers of 2, the
copies past the arrays and to `pre`) load the bases they need from the
header, then run from the registers that correctness pins.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey VG.Impl.Rsa.X86_64.PrivPre
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

/-- The public data of `main`: the checks', and `pre`'s pointer and length. -/
structure PPub where
  m : MPub
  op : Addr
  L : Nat

/-- What `main` reads of the context's entry state beyond `KS`: `pre`'s
pointer and length, and the bounds the copies need. -/
structure PS (q : PPub) (s : State) : Prop where
  hO : Bignum.word s.mem q.m.kp.B (8 * sE) = q.op
  hL : Bignum.word s.mem q.m.kp.B (8 * sElen) = BitVec.ofNat 64 q.L
  hLv : q.L = 2 * q.m.kp.w + Spec.Rsa.primeWords q.m.kp.pl + Spec.Rsa.primeWords q.m.kp.ql
  w8 : 8 ≤ q.m.kp.w
  w2 : q.m.kp.w < 2 ^ 28
  pl : q.m.kp.pl < 8 * q.m.kp.w
  ql : q.m.kp.ql < 8 * q.m.kp.w
  LZ : slot q.m.kp.w 8 + 8 * q.L ≤ q.m.kp.Z
  pw : ∀ i < q.L, InRegions s.wr (off q.op (8 * i)) 8
  ps : ∀ i < 8 * q.L, q.m.kp.Z ≤ ofs q.m.kp.B (q.op + BitVec.ofNat 64 i)

/-- In the checks' context, from some entry state, with `pre`'s slots and a
mask in `sMask`. -/
def PK (q : PPub) (t : State) : Prop :=
  ∃ s minv N b, KCtx s t q.m.kp.B q.m.kp.Z q.m.kp.w minv N ∧ KS q.m.kp s ∧ PS q s ∧
    Bignum.word t.mem q.m.kp.B (8 * sMask) = mask b

theorem PK.kk {q : PPub} {t : State} (h : PK q t) : KK q.m.kp t :=
  let ⟨s, minv, N, _, c, hs, _⟩ := h; ⟨s, minv, N, c, hs⟩

theorem PK.rdi {q : PPub} {t : State} (h : PK q t) : t.gpr .rdi = q.m.kp.B := h.kk.rdi

theorem pins_pk : Pins PK [.rdi] :=
  pins_of (fun q _ => q.m.kp.B) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.rdi

/-- A step that keeps the context, its entry state and a mask keeps `PK`. -/
theorem PK.step {q : PPub} {t : State} (h : PK q t) {c : Prog isa}
    (hc : ∀ s minv N b, KCtx s t q.m.kp.B q.m.kp.Z q.m.kp.w minv N → KS q.m.kp s → PS q s →
      Bignum.word t.mem q.m.kp.B (8 * sMask) = mask b → WP isa c t fun t' =>
        KCtx s t' q.m.kp.B q.m.kp.Z q.m.kp.w minv N ∧ ∃ b', Bignum.word t'.mem q.m.kp.B (8 * sMask) = mask b') :
    WP isa c t (PK q) := by
  obtain ⟨s, minv, N, b, c, hs, hp, hm⟩ := h
  exact WP.mono (hc s minv N b c hs hp hm) fun t' ⟨c', b', hm'⟩ => ⟨s, minv, N, b', c', hs, hp, hm'⟩

/-- A piece of the checks, constant time from `KK`, is from `PK`. -/
theorem pk_lift {c : Prog isa} (hct : RelCT isa (Two KK) c (Two KK)) (hok : ∀ q t, PK q t → WP isa c t (PK q)) :
    RelCT isa (Two PK) c (Two PK) :=
  two_post ((two_map (fun q : PPub => q.m.kp) (fun _ _ h => h.kk) hct).mono (fun _ _ h => h) fun _ _ _ => trivial)
    hok

theorem pk_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) (h₁ : RelCT isa (Two PK) (seqs a) (Two PK))
    (h₂ : RelCT isa (Two PK) (seqs b) (Two PK)) : RelCT isa (Two PK) (seqs (a ++ b)) (Two PK) :=
  RelCT.seqs_append ha hb (RelCT.seq h₁ h₂)

theorem mask_of_arrays {s t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (c : KCtx s t B Z w minv N) {js : List Nat} (ha : Arrays B w js t.mem t'.mem) {b : Bool}
    (hm : Bignum.word t.mem B (8 * sMask) = mask b) : ∃ b', Bignum.word t'.mem B (8 * sMask) = mask b' :=
  ⟨b, by rw [Arrays.mask_eq ha c.good.scr.nowrap c.hZ]; exact hm⟩

/-! ## The checks' pieces -/

theorem ld_DM : RelCT isa (Two KK) (seqs (loadNum aM sD sDlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pd) (·.dl)
    (fun _ _ h => ⟨h.hD, h.hDl, h.srD, h.dl1, h.dl2⟩) (by taint_decide) (by taint_decide)

/-- `loadNum j sp sl` keeps `PK`, for the pointer and length `KS` gives. -/
theorem loadPK {j sp sl : Nat} (hj : j < 8) (hjN : j ≠ aN) (hj1 : j ≠ aOne) (hsp : sp < 32) (hsl : sl < 32)
    (hsp' : sp ≠ sMask) (hsl' : sl ≠ sMask) (fp : KPub → Addr) (fl : KPub → Nat)
    (hf : ∀ p s, KS p s → Bignum.word s.mem p.B (8 * sp) = fp p ∧
      Bignum.word s.mem p.B (8 * sl) = BitVec.ofNat 64 (fl p) ∧
      (∃ bs, Src s p.B p.Z (fp p) bs ∧ bs.length = fl p) ∧ 1 ≤ fl p ∧ fl p ≤ 8 * p.w) :
    ∀ q t, PK q t → WP isa (seqs (loadNum j sp sl)) t (PK q) := fun _ _ h => h.step fun s _ _ _ c hs _ hm => by
  obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, h1, h2⟩ := hf _ s hs
  exact WP.mono (loadK c hj hjN hj1 hsp hsl hsp' hsl' hp (by rw [hbl]; exact hl) hsrc (by omega) (by omega))
    fun _ ⟨c', _, a⟩ => ⟨c', mask_of_arrays c a hm⟩

theorem pq_pk : RelCT isa (Two PK)
    (seqs (loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ VG.Impl.Rsa.X86_64.Crt.eqCheck)) (Two PK) :=
  pk_lift (kk_app (by simp [loadNum]) (by simp [VG.Impl.Rsa.X86_64.Crt.eqCheck]) (kk_app (by simp [loadNum])
      (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs]) (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PX ld_QR)
      mulXRK_ct) eqCheckK_ct)
    fun _ _ h => h.step fun _ _ _ _ c hs _ hm => by
      obtain ⟨bp, sp, lp⟩ := hs.srP
      obtain ⟨bq, sq, lq⟩ := hs.srQ
      have := hs.pl1
      have := hs.pl2
      have := hs.ql1
      have := hs.ql2
      exact WP.mono (pqN_ok c hm hs.hP (by rw [lp]; exact hs.hPl) hs.hQ (by rw [lq]; exact hs.hQl) sp sq
        (by omega) (by omega) (by omega) (by omega)) fun _ ⟨c', m'⟩ => ⟨c', _, m'⟩

theorem ldDM_pk : RelCT isa (Two PK) (seqs (loadNum aM sD sDlen)) (Two PK) :=
  pk_lift ld_DM (loadPK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (·.pd) (·.dl) fun _ _ h => ⟨h.hD, h.hDl, h.srD, h.dl1, h.dl2⟩)

theorem ldPM_pk : RelCT isa (Two PK) (seqs (loadNum aM sP sPlen)) (Two PK) :=
  pk_lift ld_PM (loadPK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (·.pp) (·.pl) fun _ _ h => ⟨h.hP, h.hPl, h.srP, h.pl1, h.pl2⟩)

theorem ldQM_pk : RelCT isa (Two PK) (seqs (loadNum aM sQ sQlen)) (Two PK) :=
  pk_lift ld_QM (loadPK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (·.pq) (·.ql) fun _ _ h => ⟨h.hQ, h.hQl, h.srQ, h.ql1, h.ql2⟩)

theorem reduceXR_pk : RelCT isa (Two PK) (seqs (reduce cntXR)) (Two PK) :=
  pk_lift reduceXRK_ct fun _ _ h => h.step fun _ _ _ _ c _ _ hm =>
    WP.mono (reduceXRK c) fun _ ⟨c', _, a⟩ => ⟨c', mask_of_arrays c a hm⟩

theorem reduceE_pk : RelCT isa (Two PK) (seqs (reduce cntE)) (Two PK) :=
  pk_lift reduceEK_ct fun _ _ h => h.step fun _ _ _ _ c _ _ hm =>
    WP.mono (reduceEK c) fun _ ⟨c', _, a⟩ => ⟨c', mask_of_arrays c a hm⟩

/-! ## The powers of 2 -/

/-- `setWord o .rcx` is constant time from pinned `rdi`, `r12` and `rcx`,
given the base it loads. -/
theorem setWord_ct {α : Type} {Φ : α → State → Prop} {o : Nat} (B r8v r12v rcxv : α → BitVec 64)
    (hr : ∀ a t, Φ a t → RegsAre [(.rdi, B a), (.r12, r12v a), (.rcx, rcxv a)] t)
    (hld : ∀ a t, Φ a t → WP isa (.block [.mov .r8 (.mem (hdr (sArr o)))]) t fun u => u.gpr .r8 = r8v a)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr o)))]) hc₁).isSome = true)
    (hB : (taint.check (Taint.ofRegs [.r8, .r12, .rcx])
      (.seq zeroAccLoop (.block [.store (ix .r8 .rcx) .rdx])) hc₂).isSome = true) :
    RelCT isa (Two Φ) (setWord o .rcx) fun _ _ => True := by
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := fun a t => RegsAre [(.r8, r8v a), (.r12, r12v a), (.rcx, rcxv a)] t) [.rdi]
    (pins_of (fun a _ => B a) fun a t h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hr a t h (.rdi, B a) (by simp)) hT fun a t h => ?_)
    (two_taint [.r8, .r12, .rcx] (pins_regsAre (fun a => [(.r8, r8v a), (.r12, r12v a), (.rcx, rcxv a)])
      (fun _ => rfl) fun _ _ h => h) hB)
  have h' := hr a t h
  exact WP.mono (WP.keep [.r8] (hld a t h) rfl) fun u ⟨h8, k⟩ => regsAre_cons h8
    (regsAre_cons ((k.gpr (by decide)).trans (h' (.r12, r12v a) (by simp)))
      (regsAre_cons ((k.gpr (by decide)).trans (h' (.rcx, rcxv a) (by simp))) regsAre_nil))

/-- A block that sets `rcx := i` and `r12 := w` from the header, then
`setWord o .rcx`, from `PK`. -/
theorem accRest_ct {X : List Instr} {o : Nat} (ho : o < 8) (iv : PPub → Nat)
    (hX : ∀ q t, PK q t → WP isa (.block X) t fun u => u.gpr .rcx = BitVec.ofNat 64 (iv q) ∧
      u.gpr .r12 = BitVec.ofNat 64 q.m.kp.w ∧ u.mem = t.mem ∧ Keep [.rcx, .rdx, .r12] t u)
    {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block X) hc₁).isSome = true)
    (hT' : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr o)))]) hc₂).isSome = true)
    (hB : (taint.check (Taint.ofRegs [.r8, .r12, .rcx])
      (.seq zeroAccLoop (.block [.store (ix .r8 .rcx) .rdx])) hc₃).isSome = true) :
    RelCT isa (Two PK) (.seq (.block X) (setWord o .rcx)) fun _ _ => True := by
  refine RelCT.seq (two_piece (Ψ := fun q t => RegsAre [(.rdi, q.m.kp.B), (.r12, BitVec.ofNat 64 q.m.kp.w),
      (.rcx, BitVec.ofNat 64 (iv q))] t ∧
      WP isa (.block [.mov .r8 (.mem (hdr (sArr o)))]) t fun u => u.gpr .r8 = kb q.m.kp o) [.rdi] pins_pk hT
    fun q t h => ?_)
    (setWord_ct (fun q => q.m.kp.B) (fun q => kb q.m.kp o) (fun q => BitVec.ofNat 64 q.m.kp.w)
      (fun q => BitVec.ofNat 64 (iv q)) (fun _ _ h => h.1) (fun _ _ h => h.2) hT' hB)
  obtain ⟨hdi, hl, -, hb⟩ := h.kk.lds
  refine WP.mono (hX q t h) fun u ⟨hcx, h12, hm, k⟩ => ⟨regsAre_cons ((k.gpr (by decide)).trans hdi)
    (regsAre_cons h12 (regsAre_cons hcx regsAre_nil)), ?_⟩
  exact WP.mono (WP.keep [.r8] (Q := fun v => v.gpr .r8 = kb q.m.kp o) (by
    xrun [State.ea, hdr, (k.gpr (by decide)).trans hdi, hdrOff,
      show InRegions (u.rd ++ u.wr) (off q.m.kp.B (8 * sArr o)) 8 by
        rw [k.2.1, k.2.2]; exact hl (sArr o) (by unfold sArr; omega), hm, hb o ho]) rfl) fun _ ⟨h8, _⟩ => h8

theorem zeroArrAcc_pk : RelCT isa (Two PK) (VG.Impl.Rsa.X86_64.Crt.zeroArr aAcc) (Two PK) :=
  two_post ((two_map (fun q : PPub => q.m.kp) (fun _ _ h => h.kk) (zeroArrK_ct (j := aAcc) (by decide) (by decide)
      (by decide) (by taint_decide))).mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun _ _ h => h.step fun _ _ _ _ c _ _ hm => by
      have := c.w2
      refine WP.mono (zeroArr_ok c.good c.hZ c.w1 (by omega) (j := aAcc) (by decide)) fun t' ⟨_, ho, k⟩ => ?_
      have a : Arrays _ _ [aAcc] _ t'.mem := Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _)
        (Nat.le_refl _)
      exact ⟨c.arr a (by decide) (by decide) (by decide) k, mask_of_arrays c a hm⟩

theorem accTop_pk : RelCT isa (Two PK) (seqs accTop) (Two PK) := by
  refine two_post ?_ fun _ _ h => h.step fun _ _ _ _ c _ hp hm => ?_
  · simp only [accTop, seqs]
    refine RelCT.seq zeroArrAcc_pk (accRest_ct (by decide) (fun q => q.m.kp.w - 2) (fun q t h => ?_)
      (by taint_decide) (by taint_decide) (by taint_decide))
    obtain ⟨hdi, hl, hw, -⟩ := h.kk.lds
    have hkw := h.kk.w
    obtain ⟨_, _, _, _, -, -, hp, -⟩ := h
    have := hp.w8
    exact WP.mono (WP.keep [.rcx, .rdx, .r12] (Q := fun u => u.gpr .rcx = BitVec.ofNat 64 (q.m.kp.w - 2) ∧
        u.gpr .r12 = BitVec.ofNat 64 q.m.kp.w ∧ u.mem = t.mem) (by
      xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hw]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show BitVec.toNat (2 : BitVec 64) = 2 from rfl]
      omega) rfl) fun _ ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  · have := hp.w8
    exact WP.mono (accTopK c (by omega)) fun _ ⟨c', _, a⟩ => ⟨c', mask_of_arrays c a hm⟩

/-- `accPrime sl`, for the length `fl q` in header slot `sl`. -/
theorem accPrime_pk {sl : Nat} (hsl : sl < 32) (hsl' : sl ≠ sMask) (fl : PPub → Nat)
    (hf : ∀ q s, KS q.m.kp s → PS q s → Bignum.word s.mem q.m.kp.B (8 * sl) = BitVec.ofNat 64 (fl q) ∧
      1 ≤ fl q ∧ fl q ≤ 8 * q.m.kp.w)
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (primeW sl ++ ([.mov .rcx (.reg .r12), .mov32 .rdx (.imm 1),
      .mov .r12 (.mem (hdr sW))] : List Instr))) hc₁).isSome = true) :
    RelCT isa (Two PK) (seqs (accPrime sl)) (Two PK) := by
  refine two_post ?_ fun q _ h => h.step fun s _ _ _ c hs hp hm => ?_
  · simp only [accPrime, seqs]
    refine accRest_ct (by decide) (fun q => Spec.Rsa.primeWords (fl q)) (fun q t h => ?_) hT (by taint_decide)
      (by taint_decide)
    obtain ⟨s, _, _, _, c, hs, hp, -⟩ := h
    obtain ⟨hsv, h1, h2⟩ := hf q s hs hp
    have := c.w2
    rw [WP.block_append_iff]
    refine WP.mono (primeW_ok c.good.rdi (c.ld hsl) (by rw [c.hdr sl hsl hsl']; exact hsv) h1 (by omega))
      fun u₁ ⟨h12₁, hm₁, k₁⟩ => ?_
    exact WP.mono (WP.keep [.rcx, .rdx, .r12] (Q := fun u =>
        u.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.primeWords (fl q)) ∧ u.gpr .r12 = BitVec.ofNat 64 q.m.kp.w ∧
        u.mem = t.mem) (by
      xrun [State.ea, hdr, (k₁.gpr (by decide)).trans c.good.rdi, hdrOff,
        show InRegions (u₁.rd ++ u₁.wr) (off q.m.kp.B (8 * sW)) 8 by rw [k₁.2.1, k₁.2.2]; exact c.ld (by decide),
        c.good.hdr.hw, h12₁, hm₁]) rfl)
      fun _ ⟨⟨a, b, d⟩, k⟩ => ⟨a, b, d, (k₁.trans k).mono (by decide)⟩
  · obtain ⟨hsv, h1, h2⟩ := hf q s hs hp
    have := hp.w8
    exact WP.mono (accPrimeK c hsl hsl' hsv h1 h2 (by omega)) fun _ ⟨c', _, a⟩ => ⟨c', mask_of_arrays c a hm⟩

/-! ## The copies -/

/-- `copyOut off j`, for the offset `e q` and count `c q` that `off` sets. -/
theorem copyOut_pk {offI : List Instr} {j : Nat} (hj : j < 8) (e c : PPub → Nat)
    (hoff : ∀ q s minv N, KS q.m.kp s → PS q s → OffOk s q.m.kp.B q.m.kp.Z q.m.kp.w minv N offI (e q) (c q))
    (hc : ∀ q s, PS q s → 1 ≤ c q ∧ c q ≤ q.m.kp.w + 2 ∧ slot q.m.kp.w 8 + 8 * (e q + c q) ≤ q.m.kp.Z)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (dBase ++ offI ++ ([.mov .rsi (.mem (hdr (sArr j)))] : List Instr))) hc₁).isSome = true)
    (hB : (taint.check (Taint.ofRegs [.rsi, .rbx, .r12]) Impl.Rsa.X86_64.copyWords hc₂).isSome = true) :
    RelCT isa (Two PK) (seqs (copyOut offI j)) (Two PK) := by
  refine two_post ?_ fun q t h => h.step fun s minv N b c' hs hp hm => ?_
  · show RelCT isa (Two PK) (.seq (.block _) Impl.Rsa.X86_64.copyWords) _
    refine hdr_ct pins_pk (rs := [.rsi, .rbx, .r12]) (fun q => [(.rsi, kb q.m.kp j),
      (.rbx, off q.m.kp.B (slot q.m.kp.w 8 + 8 * e q)), (.r12, BitVec.ofNat 64 (c q))]) (fun _ => rfl) hT hB
      fun q t h => ?_
    obtain ⟨s, minv, N, _, c, hs, hp, _⟩ := h
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (dBase_ok c.good c.hZ) fun u₁ ⟨hbx₁, h12₁, hm₁, k₁⟩ => ?_
    refine WP.mono (hoff q s minv N hs hp t c u₁ k₁ hm₁ hbx₁ h12₁) fun u₂ ⟨hbx₂, h12₂, hm₂, k₂⟩ => ?_
    have k12 := k₁.trans k₂
    have := c.w2
    refine WP.mono (WP.keep [.rsi] (Q := fun u => u.gpr .rsi = kb q.m.kp j) (by
      xrun [State.ea, hdr, (k12.gpr (by decide)).trans c.good.rdi, hdrOff,
        show InRegions (u₂.rd ++ u₂.wr) (off q.m.kp.B (8 * sArr j)) 8 by
          rw [k12.2.1, k12.2.2]; exact c.ld (by unfold sArr; omega), hm₂, hm₁, c.good.hdr.harr j hj]) rfl)
      fun u ⟨hsi, k⟩ => regsAre_cons hsi (regsAre_cons ((k.gpr (by decide)).trans hbx₂)
        (regsAre_cons ((k.gpr (by decide)).trans h12₂) regsAre_nil))
  · obtain ⟨h1, h2, h3⟩ := hc q s hp
    have hn := c'.good.scr.nowrap
    have := hdr_lt_slot q.m.kp.w 8 (show sMask < 32 by decide)
    exact WP.mono (copyOutK c' hj (hoff q s minv N hs hp t c') h1 h2 h3) fun t' ⟨c'', _, o⟩ =>
      ⟨c'', b, by rw [o.word (Or.inl (by omega)) (by omega)]; exact hm⟩

/-- `maskOut`: from `PK` to `rdi` at the working space. -/
theorem maskOut_ct : RelCT isa (Two PK) (seqs maskOut) (Two fun (q : PPub) t => t.gpr .rdi = q.m.kp.B) := by
  refine two_post ?_ fun q _ h => ?_
  · show RelCT isa (Two PK) (.seq (.block _) maskWords) _
    refine hdr_ct pins_pk (rs := [.rsi, .rbx, .r12]) (fun q => [(.rsi, off q.m.kp.B (slot q.m.kp.w 8)),
      (.rbx, q.op), (.r12, BitVec.ofNat 64 q.L)]) (fun _ => rfl) (by taint_decide) (by taint_decide)
      fun q t h => ?_
    obtain ⟨s, minv, N, b, c, hs, hp, hm⟩ := h
    rw [WP.block_append_iff]
    refine WP.mono (dBase_ok c.good c.hZ) fun u₁ ⟨hbx₁, h12₁, hm₁, k₁⟩ => ?_
    have hdi₁ : u₁.gpr .rdi = q.m.kp.B := (k₁.gpr (by decide)).trans c.good.rdi
    have hl₁ : ∀ i < 32, InRegions (u₁.rd ++ u₁.wr) (off q.m.kp.B (8 * i)) 8 := fun i hi => by
      rw [k₁.2.1, k₁.2.2]; exact c.ld hi
    exact WP.mono (WP.keep [.rsi, .rbx, .r12, .rbp] (Q := fun u => u.gpr .rsi = off q.m.kp.B (slot q.m.kp.w 8) ∧
        u.gpr .rbx = q.op ∧ u.gpr .r12 = BitVec.ofNat 64 q.L) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, hl₁ sE (by decide), hl₁ sElen (by decide), hl₁ sMask (by decide), hbx₁,
        hm₁, c.hdr sE (by decide) (by decide), hp.hO, c.hdr sElen (by decide) (by decide), hp.hL]) rfl)
      fun u ⟨⟨a, b', d⟩, _⟩ => regsAre_cons a (regsAre_cons b' (regsAre_cons d regsAre_nil))
  · obtain ⟨s, minv, N, b, c, hs, hp, hm⟩ := h
    have := c.w2
    have hLv := hp.hLv
    have : Spec.Rsa.primeWords q.m.kp.pl ≤ q.m.kp.w := by
      have := hp.pl; unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; have := hp.w8; omega
    have : Spec.Rsa.primeWords q.m.kp.ql ≤ q.m.kp.w := by
      have := hp.ql; unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; have := hp.w8; omega
    exact WP.mono (maskOutK c hp.hO hp.hL (by have := hp.w8; omega) (by omega) hp.LZ hm
      (fun i hi => by rw [c.wr]; exact hp.pw i hi) hp.ps) fun _ ⟨_, _, k⟩ => (k.gpr (by decide)).trans c.good.rdi

/-! ## `main` -/

/-- `main`'s hypotheses, with the public data `q`. -/
def P0 (q : PPub) (s : State) : Prop :=
  M0 q.m s ∧ Bignum.word s.mem q.m.kp.B (8 * sE) = q.op ∧
    Bignum.word s.mem q.m.kp.B (8 * sElen) = BitVec.ofNat 64 q.L ∧
    q.L = 2 * q.m.kp.w + Spec.Rsa.primeWords q.m.kp.pl + Spec.Rsa.primeWords q.m.kp.ql ∧
    8 ≤ q.m.kp.w ∧ q.m.kp.w < 2 ^ 28 ∧ q.m.kp.pl < 8 * q.m.kp.w ∧ q.m.kp.ql < 8 * q.m.kp.w ∧
    slot q.m.kp.w 8 + 8 * q.L ≤ q.m.kp.Z ∧ (∀ i < q.L, InRegions s.wr (off q.op (8 * i)) 8) ∧
    ∀ i < 8 * q.L, q.m.kp.Z ≤ ofs q.m.kp.B (q.op + BitVec.ofNat 64 i)

/-- The setup leaves `PK`. -/
theorem setup_pk (q : PPub) (s : State) (h : P0 q s) :
    WP isa (seqs [.block VG.Impl.Rsa.X86_64.head, loadBE, .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)],
      setWord aOne .rcx, .block maskInit]) s (PK q) := by
  obtain ⟨⟨nb, db, pb, qb, dpb, dqb, qib, ev, hp, hw', hdl, hpl, hql⟩, hO, hL, hLv, w8, w2, hpl', hql', hLZ, hpw,
    hps⟩ := h
  have := hp.dl2
  have := hp.pl2
  have := hp.ql2
  refine WP.mono (setupK_ok hp) fun t₀ ⟨minv, h₀, m₀, hw, in₀, rd₀, wr₀, k₀⟩ => ?_
  have sr : ∀ {p : Addr} {bs : List Byte}, Src s q.m.kp.B q.m.kp.Z p bs → Src t₀ q.m.kp.B q.m.kp.Z p bs :=
    fun h => h.congr in₀ rd₀ wr₀
  refine ⟨t₀, minv, _, true, by rw [hw']; exact h₀,
    { hD := by rw [hw sD (by decide) (by decide)]; exact hp.hD
      hDl := by rw [hw sDlen (by decide) (by decide), hp.hDl, hdl]
      hP := by rw [hw sP (by decide) (by decide)]; exact hp.hP
      hPl := by rw [hw sPlen (by decide) (by decide), hp.hPl, hpl]
      hQ := by rw [hw sQ (by decide) (by decide)]; exact hp.hQ
      hQl := by rw [hw sQlen (by decide) (by decide), hp.hQl, hql]
      hDP := by rw [hw sDP (by decide) (by decide)]; exact hp.hDP
      hDQ := by rw [hw sDQ (by decide) (by decide)]; exact hp.hDQ
      hQI := by rw [hw sQI (by decide) (by decide)]; exact hp.hQI
      srD := ⟨db, sr hp.srD, hdl⟩
      srP := ⟨pb, sr hp.srP, hpl⟩
      srQ := ⟨qb, sr hp.srQ, hql⟩
      srDP := ⟨dpb, sr hp.srDP, hp.dpl.trans hpl⟩
      srDQ := ⟨dqb, sr hp.srDQ, hp.dql.trans hql⟩
      srQI := ⟨qib, sr hp.srQI, hp.qil.trans hpl⟩
      dl1 := hdl ▸ hp.dl1
      dl2 := by omega
      pl1 := hpl ▸ hp.pl1
      pl2 := by omega
      ql1 := hql ▸ hp.ql1
      ql2 := by omega },
    { hO := by rw [hw sE (by decide) (by decide)]; exact hO
      hL := by rw [hw sElen (by decide) (by decide)]; exact hL
      hLv := hLv
      w8 := w8
      w2 := w2
      pl := hpl'
      ql := hql'
      LZ := hLZ
      pw := fun i hi => by rw [wr₀]; exact hpw i hi
      ps := hps }, m₀⟩

theorem primeWords_le {l w : Nat} (h : l < 8 * w) (hw : 2 ≤ w) : Spec.Rsa.primeWords l ≤ w := by
  unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega

theorem two_le_primeWords (l : Nat) : 2 ≤ Spec.Rsa.primeWords l := by
  unfold Spec.Rsa.primeWords; omega

/-- `main` is constant time from `P0`. -/
theorem preMain_ct : RelCT isa (Two P0) Impl.Rsa.X86_64.PrivPre.main fun _ _ => True := by
  rw [preMain_eq]
  refine RelCT.seqs_append (by simp) (by simp [loadNum]) (RelCT.seq (two_post ((two_map (fun q : PPub => q.m)
    (fun _ _ h => h.1) setupK_ct).mono (fun _ _ h => h) fun _ _ _ => trivial) setup_pk) ?_)
  refine RelCT.seqs_append (by simp [loadNum]) (by simp [copyOut]) (RelCT.seq pq_pk ?_)
  refine RelCT.seqs_append (by simp [copyOut]) (by simp [loadNum]) (RelCT.seq (copyOut_pk (j := aN) (by decide)
    (fun _ => 0) (fun q => q.m.kp.w) (fun _ _ _ _ _ _ => offNil)
    (fun q _ hp => ⟨by have := hp.w8; omega, by omega, by have := hp.LZ; have := hp.hLv; omega⟩)
    (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [loadNum]) (by simp [loadNum]) (RelCT.seq
    (pk_app (by simp [loadNum, accTop, reduce]) (by simp [copyOut])
      (pk_app (by simp [loadNum, accTop]) (by simp [reduce])
        (pk_app (by simp [loadNum]) (by simp [accTop]) ldDM_pk accTop_pk) reduceXR_pk)
      (copyOut_pk (j := aR) (by decide) (fun q => q.m.kp.w) (fun q => q.m.kp.w) (fun _ _ _ _ _ _ => offSkip)
        (fun q _ hp => ⟨by have := hp.w8; omega, by omega, by have := hp.LZ; have := hp.hLv; omega⟩)
        (by taint_decide) (by taint_decide))) ?_)
  refine RelCT.seqs_append (by simp [loadNum]) (by simp [loadNum]) (RelCT.seq
    (pk_app (by simp [loadNum, accPrime, reduce]) (by simp [copyOut])
      (pk_app (by simp [loadNum, accPrime]) (by simp [reduce])
        (pk_app (by simp [loadNum]) (by simp [accPrime]) ldPM_pk
          (accPrime_pk (by decide) (by decide) (fun q => q.m.kp.pl) (fun _ _ hs _ => ⟨hs.hPl, hs.pl1, hs.pl2⟩)
            (by taint_decide))) reduceE_pk)
      (copyOut_pk (j := aR) (by decide) (fun q => 2 * q.m.kp.w) (fun q => Spec.Rsa.primeWords q.m.kp.pl)
        (fun q s _ _ hs hp => offPrime hs.hPl hs.pl1 (by have := hp.pl; have := hp.w2; omega))
        (fun q _ hp => ⟨by have := two_le_primeWords q.m.kp.pl; omega,
          by have := primeWords_le hp.pl (by have := hp.w8; omega); omega,
          by have := hp.LZ; have := hp.hLv; omega⟩)
        (by taint_decide) (by taint_decide))) ?_)
  refine RelCT.seqs_append (by simp [loadNum]) (by simp [maskOut]) (RelCT.seq
    (pk_app (by simp [loadNum, accPrime, reduce]) (by simp [copyOut])
      (pk_app (by simp [loadNum, accPrime]) (by simp [reduce])
        (pk_app (by simp [loadNum]) (by simp [accPrime]) ldQM_pk
          (accPrime_pk (by decide) (by decide) (fun q => q.m.kp.ql) (fun _ _ hs _ => ⟨hs.hQl, hs.ql1, hs.ql2⟩)
            (by taint_decide))) reduceE_pk)
      (copyOut_pk (j := aR) (by decide) (fun q => 2 * q.m.kp.w + Spec.Rsa.primeWords q.m.kp.pl)
        (fun q => Spec.Rsa.primeWords q.m.kp.ql)
        (fun q s _ _ hs hp => offPrime2 hs.hPl hs.hQl hs.pl1 (by have := hp.pl; have := hp.w2; omega) hs.ql1
          (by have := hp.ql; have := hp.w2; omega))
        (fun q _ hp => ⟨by have := two_le_primeWords q.m.kp.ql; omega,
          by have := primeWords_le hp.ql (by have := hp.w8; omega); omega,
          by have := hp.LZ; have := hp.hLv; omega⟩)
        (by taint_decide) (by taint_decide))) ?_)
  exact RelCT.seqs_append (by simp [maskOut]) (by simp) (RelCT.seq maskOut_ct
    (two_taint [.rdi] (pins_of (fun (q : PPub) _ => q.m.kp.B) fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)))

end VG.Proof.Rsa.X86_64.Key
