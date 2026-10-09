import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Branch
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Ws
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode

/-!
# RSA with AVX512_IFMA on x86-64, any size: the computation

`main` runs `vg_rsa_private_crt`'s
front, then the IFMA branch of the first layout whose sizes the key has
(`branch`, `sizes`), the CRT one if none, and its finish (`main_ok`); `code`
writes `privateCrt` of its inputs (`code_correct`).
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.CrtIfma (Lay lay2048 lay3072 lay4096 sizes ifma)
open VG.Proof.Bignum.X86_64 (ofNat_eq_iff mx_ffff CrtReady.of_regs)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- `(len + 7) / 8 = v`, for the workspace of a prime of `len` bytes. -/
theorem sz_iff {n v : Nat} (hn : n < 2 ^ 60) (hv : v < 2 ^ 31) :
    ((BitVec.ofNat 64 n + 7) >>> 3 ^^^ BitVec.ofNat 64 v = 0#64) ↔ (n + 7) / 8 = v := by
  have h7 : ((BitVec.ofNat 64 n + 7) >>> 3).toNat = (n + 7) / 8 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      show (7 : BitVec 64).toNat = 7 from rfl, Nat.mod_eq_of_lt (a := n) (by omega),
      Nat.mod_eq_of_lt (a := n + 7) (by omega)]
  rw [BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj, h7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v) (by omega)]

/-- `sizes l`: ZF exactly if `n` has `2 W` words and `p` and `q` `W`. -/
theorem sizes_ok (hl : LayOk l) {t : State} {B : Addr} {Z w pl ql : Nat} {minv : BitVec 64}
    (hg : VG.Proof.Bignum.X86_64.Good t B Z w minv) (hpl : word t.mem B (8 * sPlen) = BitVec.ofNat 64 pl)
    (hql : word t.mem B (8 * sQlen) = BitVec.ofNat 64 ql) (hZ : 8 * 32 ≤ Z) (hw : w < 2 ^ 64)
    (hpl' : pl < 2 ^ 60) (hql' : ql < 2 ^ 60) :
    WP isa (.block (sizes l)) t fun t' =>
      t'.zf = some (decide (w = 2 * l.W ∧ (pl + 7) / 8 = l.W ∧ (ql + 7) / 8 = l.W)) ∧ t'.mem = t.mem ∧
        Keep [.rax, .rdx] t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hl' : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide
  have sxW := VG.Proof.Bignum.X86_64.AmmSym.se_ofNat (show l.W < 2 ^ 31 by omega)
  have sx2W := VG.Proof.Bignum.X86_64.AmmSym.se_ofNat (show 2 * l.W < 2 ^ 31 by omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' =>
    t'.zf = some (decide (w = 2 * l.W ∧ (pl + 7) / 8 = l.W ∧ (ql + 7) / 8 = l.W)) ∧ t'.mem = t.mem) (by
      xrun [sizes, State.ea, hdr, hg.rdi, hdrOff, hl' sW (by decide), hl' sPlen (by decide),
        hl' sQlen (by decide), hg.hdr.hw, hpl, hql, sxW, sx2W]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show (0 : BitVec 64) = 0#64 from rfl,
        BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff,
        ofNat_eq_iff hw (by omega), sx7, sz_iff hpl' (by omega), sz_iff hql' (by omega), and_assoc]) rfl)
    fun t' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

/-- The IFMA area fits in the working space the contract asks for. -/
theorem ifmaZ_of (hl : LayOk l) {Z k pl : Nat} (hzk : 128 * k ≤ Z) (hw : (k + 7) / 8 = 2 * l.W)
    (hp : wsWords pl = l.W) : offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W + 2 * l.D + 8 ≤ Z := by
  rcases hl with rfl | rfl | rfl <;>
    simp only [VG.Impl.Rsa.X86_64.CrtIfma.lay2048, VG.Impl.Rsa.X86_64.CrtIfma.lay3072,
      VG.Impl.Rsa.X86_64.CrtIfma.lay4096] at hw hp ⊢ <;>
    unfold offQ slot wsWords hdrBytes tabBytes at * <;>
    simp only [VG.Impl.Rsa.X86_64.CrtIfma.Lay.D, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oFin,
      VG.Impl.Rsa.X86_64.CrtIfma.Lay.oV, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oK1, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oE,
      VG.Impl.Rsa.X86_64.CrtIfma.Lay.oTab, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oS, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oX,
      VG.Impl.Rsa.X86_64.CrtIfma.Lay.oY, VG.Impl.Rsa.X86_64.CrtIfma.Lay.NB,
      VG.Impl.Rsa.X86_64.CrtIfma.Lay.E] at * <;> omega

/-- What `main` leaves after the front, for a valid modulus. -/
abbrev MainQ (s : State) (B : Addr) (Z k pl ql : Nat) (minv mp mq : BitVec 64) (nb xb pb qb qib dpb dqb : List Byte)
    (t : State) : Prop :=
  PDone s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) ∧ t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem sizes_mx (hl : LayOk l) : ((.block (sizes l)) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- The key's sizes are those of the layout `l`. -/
abbrev SizesOf (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (w pl ql : Nat) : Prop :=
  w = 2 * l.W ∧ (pl + 7) / 8 = l.W ∧ (ql + 7) / 8 = l.W

/-- At most one layout has given sizes. -/
theorem sizesOf_eq {l l' : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (hl : LayOk l) (hl' : LayOk l') {w pl ql : Nat}
    (h : SizesOf l w pl ql) (h' : SizesOf l' w pl ql) : l = l' := by
  have e := h.1.symm.trans h'.1
  rcases hl with rfl | rfl | rfl <;> rcases hl' with rfl | rfl | rfl <;> first | rfl | exact absurd e (by decide)

/-- `sizes l` after the checks: ZF says whether the key has `l`'s sizes. -/
theorem sizesR_ok (hl : LayOk l) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {N C P Q : Nat} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk) :
    WP isa (.block (sizes l)) t₀ fun t₁ => t₁.zf = some (decide (SizesOf l ((k + 7) / 8) pl ql)) ∧
      CrtReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk ∧ t₁.mxcsr = t₀.mxcsr := by
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hZq := h.z
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  exact WP.mono_mx (sizes_mx hl) (sizes_ok hl (pl := pl) (ql := ql) hr.good
    (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hPl) (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hQl)
    (by unfold offQ at hZq; omega) (by omega) (by omega) (by omega))
    fun t₁ ⟨zf, me, k₁⟩ mx₁ => ⟨zf, hr.of_regs me k₁, mx₁⟩

/-- `anySizes`: ZF says whether the key has the sizes of one of the layouts. -/
theorem anySizes_ok {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {N C P Q : Nat} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk) :
    WP isa CrtIfma.anySizes t₀ fun t₁ => t₁.zf = some (decide (SizesOf lay2048 ((k + 7) / 8) pl ql ∨
        SizesOf lay3072 ((k + 7) / 8) pl ql ∨ SizesOf lay4096 ((k + 7) / 8) pl ql)) ∧
      CrtReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk ∧ t₁.mxcsr = t₀.mxcsr := by
  unfold CrtIfma.anySizes
  refine WP.seq (WP.mono (sizesR_ok (Or.inl rfl) h hr) fun t₁ ⟨z₁, r₁, x₁⟩ => ?_)
  refine WP.ite _ z₁ (fun hb => WP.block_nil
    ⟨by rw [z₁, hb, decide_eq_true (Or.inl (of_decide_eq_true hb))], r₁, x₁⟩) (fun hb => ?_)
  simp only [decide_eq_false_iff_not] at hb
  refine WP.seq (WP.mono (sizesR_ok (Or.inr (Or.inl rfl)) h r₁) fun t₂ ⟨z₂, r₂, x₂⟩ => ?_)
  refine WP.ite _ z₂ (fun hb' => WP.block_nil
    ⟨by rw [z₂, hb', decide_eq_true (Or.inr (Or.inl (of_decide_eq_true hb')))], r₂, x₂.trans x₁⟩) (fun hb' => ?_)
  simp only [decide_eq_false_iff_not] at hb'
  refine WP.mono (sizesR_ok (Or.inr (Or.inr rfl)) h r₂) fun t₃ ⟨z₃, r₃, x₃⟩ => ⟨?_, r₃, x₃.trans (x₂.trans x₁)⟩
  rw [z₃]
  congr 1
  exact decide_eq_decide.mpr ⟨fun h => .inr (.inr h), fun h => h.resolve_left hb |>.resolve_left hb'⟩

/-- `APost` after an instruction that changes only `rax`, `rdx` and the flags. -/
theorem APost.of_regs {s t t' : State} {B : Addr} {Z w op oq wp : Nat} {minv mp mq : BitVec 64} {N P Q C : Nat}
    (h : APost s t B Z w op oq wp minv mp mq N P Q C) (hm : t'.mem = t.mem) (k : Keep [.rax, .rdx] t t') :
    APost s t' B Z w op oq wp minv mp mq N P Q C := by
  obtain ⟨hg, hN, hp, hq, hf, hk, hw⟩ := h
  have hx : ∀ {X : Nat} {o wx : Nat} {mx : BitVec 64}, XVals t B o wx mx X → XVals t' B o wx mx X :=
    fun hx => by rw [show t' = { t' with mem := t.mem } by rw [← hm]]; exact ⟨hx.n, hx.inv, hx.one⟩
  have hpr : ∀ {o wx : Nat} {mx : BitVec 64} {X : Nat}, PrimeRdy t B o wx mx N X C → PrimeRdy t' B o wx mx N X C :=
    fun hp => ⟨hm ▸ hp.ws, hx hp.x, hm ▸ hp.ylt, hm ▸ hp.yv, hm ▸ hp.clt, hm ▸ hp.cv⟩
  refine ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, ?_, hpr hp, hpr hq, hm ▸ hf,
    (hk.trans k).mono (by decide), hm ▸ hw⟩
  rw [show t' = { t' with mem := t.mem } by rw [← hm]]
  exact ⟨hN.n, hN.inv, hN.r2, hN.r2lt, hN.one⟩

/-- `sizes l'` after `pre`: ZF says whether the key has `l'`'s sizes. -/
theorem sizesA_ok (hl' : LayOk l) {s t₀ s₁ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {N C P Q : Nat} {Mk : Bool} {wp : Nat} {N' P' Q' C' : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk)
    (hA : APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) wp minv mp mq N' P' Q' C') :
    WP isa (.block (sizes l)) s₁ fun s₂ => s₂.zf = some (decide (SizesOf l ((k + 7) / 8) pl ql)) ∧
      APost t₀ s₂ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) wp minv mp mq N' P' Q' C' ∧
      s₂.mxcsr = s₁.mxcsr := by
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hZq := h.z
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hns := preRanges_nsafe (w := (k + 7) / 8) (wp := wp) (wq := wp) (op := offP ((k + 7) / 8))
    (oq := offQ ((k + 7) / 8) pl) (le_refl _) (by unfold offQ; omega)
  have hpw : word s₁.mem B (8 * sPlen) = BitVec.ofNat 64 pl := by
    rw [nsafe_word hA.2.2.2.2.1 hns (by decide) (by decide) (by decide), hr.hfix _ (by decide) (by decide)]
    exact h.hPl
  have hqw : word s₁.mem B (8 * sQlen) = BitVec.ofNat 64 ql := by
    rw [nsafe_word hA.2.2.2.2.1 hns (by decide) (by decide) (by decide), hr.hfix _ (by decide) (by decide)]
    exact h.hQl
  exact WP.mono_mx (sizes_mx hl') (sizes_ok hl' (pl := pl) (ql := ql) hA.1 hpw hqw
    (by unfold offQ at hZq; omega) (by omega) (by omega) (by omega))
    fun s₂ ⟨zf, me, k₂⟩ mx₂ => ⟨zf, APost.of_regs hA me k₂, mx₂⟩

/-- `ifmaAny` after `pre`, for the layout `l` of the key's sizes: `ifma l`. -/
theorem ifmaAny_ok (hl : LayOk l) {s t₀ s₁ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hs : SizesOf l ((k + 7) / 8) pl ql)
    (hA : APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
      (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
      (Spec.Rsa.os2ip xb)) :
    WP isa CrtIfma.ifmaAny s₁ fun t =>
      IDone l s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
      t.mxcsr = s₁.mxcsr &&& 0xFFFF := by
  obtain ⟨hW1, -⟩ := W_bounds hl
  have hw := hs.1
  have hp : wsWords pl = l.W := by unfold wsWords; omega
  have hq : wsWords ql = l.W := by unfold wsWords; omega
  -- The vector code of the layout `l'` that the tests choose, which is `l`.
  have last : ∀ {l' : VG.Impl.Rsa.X86_64.CrtIfma.Lay} {s₂ : State}, LayOk l' → l = l' →
      APost t₀ s₂ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
        (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
        (Spec.Rsa.os2ip xb) → s₂.mxcsr = s₁.mxcsr →
      WP isa (seqs (ifma l')) s₂ fun t =>
        IDone l s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
          (offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
          (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
        t.mxcsr = s₁.mxcsr &&& 0xFFFF := by
    intro l' s₂ _ e a₂ x₂
    subst e
    exact WP.mono (branchA2_ok hl h hv hr hMk hw hp hq (ifmaZ_of hl h.zk hw hp) a₂) fun t ⟨hd, mx⟩ =>
      ⟨hd, by rw [mx, x₂]⟩
  unfold CrtIfma.ifmaAny
  refine WP.seq (WP.mono (sizesA_ok (l := lay2048) (Or.inl rfl) h hr hA) fun s₂ ⟨z₂, a₂, x₂⟩ => ?_)
  refine WP.ite _ z₂ (fun hb => last (Or.inl rfl) (sizesOf_eq hl (Or.inl rfl) hs (of_decide_eq_true hb)) a₂ x₂)
    (fun hb => ?_)
  refine WP.seq (WP.mono (sizesA_ok (l := lay3072) (Or.inr (Or.inl rfl)) h hr a₂) fun s₃ ⟨z₃, a₃, x₃⟩ => ?_)
  refine WP.ite _ z₃ (fun hb' => last (Or.inr (Or.inl rfl))
    (sizesOf_eq hl (Or.inr (Or.inl rfl)) hs (of_decide_eq_true hb')) a₃ (x₃.trans x₂)) (fun hb' => ?_)
  refine last (Or.inr (Or.inr rfl)) ?_ a₃ (x₃.trans x₂)
  rcases hl with rfl | rfl | rfl
  · exact absurd hs (of_decide_eq_false hb)
  · exact absurd hs (of_decide_eq_false hb')
  · rfl

/-- The IFMA computation, for the layout `l` of the key's sizes: `pre`,
`ifmaAny` and `post`. -/
theorem ifmaPart_ok (hl : LayOk l) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)))
    (mx₀ : t₀.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10)
    (hs : SizesOf l ((k + 7) / 8) pl ql)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfma.pre M.mm ++ ([CrtIfma.ifmaAny] : List (Prog isa)) ++ CrtIfma.post M.mm)) t₀
      (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb) := by
  obtain ⟨hW1, -⟩ := W_bounds hl
  have hw := hs.1
  have hp : wsWords pl = l.W := by unfold wsWords; omega
  have hq : wsWords ql = l.W := by unfold wsWords; omega
  rw [List.append_assoc]
  exact wp_seqs_append (by simp [CrtIfma.pre, CrtIfma.prep]) (by simp)
    (WP.mono (branchA1_ok hl M h hv hr rfl hw hp hq hpre) fun s₁ ⟨hA, mx₁⟩ =>
      wp_seqs_append (by simp) (by simp [CrtIfma.post])
        (WP.mono (ifmaAny_ok hl h hv hr rfl hs hA) fun t ⟨hd, mxa⟩ =>
          WP.mono (branchB_ok hl M h hv hd rfl hw hp hq hpost) fun t' ⟨hd', mxb⟩ =>
            ⟨hd', by rw [mxb, mxa, mx_ffff, mx₁, mx₀]⟩))

theorem main_eq (mul : Nat → Nat → Nat → Prog isa) : CrtIfma.main mul =
    seqs ((nSetup mul ++ primesSetup ++ checks) ++
      (([.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.pre mul ++ ([CrtIfma.ifmaAny] : List (Prog isa)) ++
        CrtIfma.post mul)) (seqs (qPhase mul ++ pPhase mul)))] : List (Prog isa)) ++ finish)) := by
  simp only [CrtIfma.main, List.append_assoc]

/-- `main`, for a valid modulus: `privateCrt`'s result as `vg_rsa_private_crt`
leaves it, and MXCSR's control bits. -/
theorem main_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hfront : (seqs (nSetup M.mm ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm ++ pPhase M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (CrtIfma.main M.mm) s fun t => (∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb)) ∧
      t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  rw [main_eq]
  refine wp_seqs_append (by simp [nSetup]) (by simp) (WP.mono_mx hfront (front_ok M h hv)
    fun t₀ ⟨minv, mp, mq, hr⟩ mx₀ => ?_)
  refine wp_seqs_append (by simp) (by simp [finish]) ?_
  have hcrtB : ∀ t₁, CrtReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) →
      t₁.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 →
      WP isa (seqs (qPhase M.mm ++ pPhase M.mm)) t₁ (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb) :=
    fun t₁ hr₁ mx₁ => WP.mono_mx hcrt (wp_seqs_append (by simp [qPhase]) (by simp [pPhase])
      (WP.mono (qPart_ok M h hv hr₁ rfl) fun _ hq => pPart_ok M h hv hq rfl)) fun t hp' mxc =>
        ⟨hp', by rw [mxc, mx₁]⟩
  have hdisp : WP isa (.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.pre M.mm ++ ([CrtIfma.ifmaAny] : List (Prog isa)) ++
      CrtIfma.post M.mm)) (seqs (qPhase M.mm ++ pPhase M.mm)))) t₀
      (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb) := by
    refine WP.seq (WP.mono (anySizes_ok h hr) fun t₁ ⟨z₁, r₁, x₁⟩ => ?_)
    refine WP.ite _ z₁ (fun hb => ?_) (fun _ => hcrtB t₁ r₁ (by rw [x₁, mx₀]))
    have mx₁ : t₁.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [x₁, mx₀]
    rcases of_decide_eq_true hb with hs | hs | hs
    · exact ifmaPart_ok (Or.inl rfl) M h hv r₁ mx₁ hs hpre hpost
    · exact ifmaPart_ok (Or.inr (Or.inl rfl)) M h hv r₁ mx₁ hs hpre hpost
    · exact ifmaPart_ok (Or.inr (Or.inr rfl)) M h hv r₁ mx₁ hs hpre hpost
  refine WP.mono hdisp fun t₂ ⟨hp, mx₂⟩ => ?_
  refine WP.mono_mx (by decide +kernel) (finPart_ok h hv hp rfl) fun t ht mxf => ⟨⟨_, ht, ?_⟩, by rw [mxf, mx₂]⟩
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- `vg_rsa_private_crt_ifma` with Montgomery multiplication `M`, given that
the parts of its code outside the vector code never load MXCSR (which the
registration file evaluates). -/
theorem code_correct (M : Mont)
    (hfront : (seqs (nSetup M.mm ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm ++ pPhase M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtContract.pre s) :
    ∃ t s', Exec isa (CrtIfma.code M.mm) s t s' ∧ abiPreserved s s' ∧ crtContract.post s s' := by
  have c := crtCtx_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (CrtIfma.code M.mm) s fun s' => (gprPreserved s s' ∧ crtContract.post s s') ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 by
    obtain ⟨t, s', he, ⟨hg, hp⟩, hmx⟩ := hwp
    exact ⟨t, s', he, ⟨hg.1, hg.2, hmx⟩, hp⟩
  unfold CrtIfma.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (c := .block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] :
    List Instr))) (by decide +kernel) (crtHead_ok c) fun t₁ h₁ mx₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono_mx (by decide +kernel) (invalid_ok h₁.rdx h₁.rcx hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ mx₂ => ?_
  have hpre' := crtPre_of c h₁ hm₂ k₂
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    exact WP.mono_mx (by decide +kernel) (fail_ok hpre'.scr hpre'.rdi (by omega)
      (by omega) (by omega) hpre'.hO hpre'.hK hpre'.out hpre'.outSep)
      fun t hp mx => ⟨crtCode_fin c h₁ hm₂ k₂ hp (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩,
        by rw [mx, mx₂, mx₁]⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    exact WP.mono (main_ok M hpre' hv hfront hpre hpost hcrt) fun t ⟨⟨Mk, hp, hiff⟩, mx⟩ =>
      ⟨crtCode_fin c h₁ hm₂ k₂ hp (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide),
        by rw [mx, mx₂, mx₁]⟩

end VG.Proof.Bignum.X86_64.Ifma
