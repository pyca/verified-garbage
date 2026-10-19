module

public import VerifiedGarbage.Proof.Bignum.X86_64.PdCode
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.PdRanges
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math

/-!
# `vg_rsa_public_precomputed` on x86-64: constant time but for `pre` and `e`

Every piece's addresses and branches depend only on the pointers, the
lengths, `pre` and `e`: `X := input R` (`pdMm_ct`), the exponentiation
(`pdExp_ct`), the last multiplication (`pdFinal_ct`), and what the whole
function's proof (`FoldedCTCode.lean`) needs of the entry and the load.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-! ## `rest` -/

/-- The public data of `rest`: the working space, `k`, the pointers, `e`
and the values `N` and `R` in the arrays. -/
structure DPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  ep : Addr
  ip : Addr
  len : Nat
  eb : List Byte
  N : Nat
  R : Nat

/-- What the computation starts from (`PdPre`). -/
def DRel (p : DPub) (s : State) : Prop :=
  ∃ xb, PdPre s p.B p.Z p.k p.op p.ep p.ip p.len p.eb xb p.N p.R

/-- From `σ`, at `rest`'s start, to `t`: what changed, and the mask. -/
def DG (p : DPub) (xb : List Byte) (σ t : State) : Prop :=
  PdPre σ p.B p.Z p.k p.op p.ep p.ip p.len p.eb xb p.N p.R ∧ Frm p.B (pdAll ((p.k + 7) / 8)) σ.mem t.mem ∧
    Keep mmRegs σ t ∧ word t.mem p.B (8 * sMask) = mask (decide (Spec.Rsa.os2ip xb < p.N))

theorem PdPre.mem {s t : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte}
    {N R : Nat} (h : PdPre s B Z k op ep ip L eb xb N R) (hm : t.mem = s.mem) {regs : List Reg} (kp : Keep regs s t)
    (hr : .rdi ∉ regs) : PdPre t B Z k op ep ip L eb xb N R :=
  { scr := h.scr.congr kp.2.2, rdi := (kp.gpr hr).trans h.rdi, z := h.z, k1 := h.k1, k2 := h.k2,
    hO := hm ▸ h.hO, hK := hm ▸ h.hK, hE := hm ▸ h.hE, hL := hm ▸ h.hL, hIn := hm ▸ h.hIn, hW := hm ▸ h.hW,
    hb := hm ▸ h.hb, n := hm ▸ h.n, r := hm ▸ h.r, odd := h.odd, n1 := h.n1, big := h.big, rlt := h.rlt,
    x := h.x.congrK (by rw [hm]; exact InScr.refl _ _ _) kp, e := h.e.congrK (by rw [hm]; exact InScr.refl _ _ _) kp,
    xl := h.xl, el := h.el, L1 := h.L1, L2 := h.L2, out := fun j hj => by rw [kp.2.2]; exact h.out j hj,
    outSep := h.outSep,
    inSpan := by rw [kp.2.1, kp.2.2]; exact h.inSpan,
    outSpan := by rw [kp.2.2]; exact h.outSpan, eodd := h.eodd, e3 := h.e3 }

theorem DG.step {p : DPub} {xb : List Byte} {σ t t' : State} (h : DG p xb σ t)
    (hf : Frm p.B (pdAll ((p.k + 7) / 8)) t.mem t'.mem) (k : Keep mmRegs t t')
    (hm : word t'.mem p.B (8 * sMask) = word t.mem p.B (8 * sMask)) : DG p xb σ t' :=
  ⟨h.1, h.2.1.trans hf, (h.2.2.1.trans k).mono (by decide), hm.trans h.2.2.2⟩

theorem DG.fixed {p : DPub} {xb : List Byte} {σ t : State} (h : DG p xb σ t) : Fixed p.B σ.mem t.mem :=
  Fixed.of_frm h.2.1 (pdAll_fixed _)

theorem DG.inScr {p : DPub} {xb : List Byte} {σ t : State} (h : DG p xb σ t) : InScr p.B p.Z σ.mem t.mem :=
  InScr.of_frm h.2.1 fun r hr => (pdAll_le _ r hr).trans h.1.z

/-- After the input's registers. -/
def DIn (p : DPub) (s : State) : Prop :=
  DRel p s ∧ s.gpr .rsi = p.ip ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = off p.B (slot ((p.k + 7) / 8) aX)

/-- After the setup, for `-m⁻¹ = q.2`. -/
def DA (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ SetupOut t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 q.1.N (Spec.Rsa.os2ip xb) ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aR2) ((q.1.k + 7) / 8) = q.1.R

/-- `rest`'s public data with `-m⁻¹`. -/
abbrev DPub.L (q : DPub × BitVec 64) : Lay := ⟨q.1.B, q.1.Z, ((q.1.k + 7) / 8), q.2⟩

/-- After `X := input R`. -/
def DB (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ Good t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 ∧ wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aN) ((q.1.k + 7) / 8) = q.1.N ∧
    ((word t.mem q.1.B (slot ((q.1.k + 7) / 8) aN)).toNat * q.2.toNat + 1) % 2 ^ 64 = 0 ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aXm) ((q.1.k + 7) / 8) < q.1.N ∧ wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aOne) ((q.1.k + 7) / 8) = 1

theorem arrays_pdAll {B : Addr} {w : Nat} {m m' : Mem} (h : Arrays B w [aAcc, aTmp, aXm] m m') :
    Frm B (pdAll w) m m' :=
  Frm.of_arrays h (by simp [pdAll, pExpRanges, pBitRanges, bitRanges])

/-- After the setup, without the registers it leaves: what the
exponentiation needs. -/
def DAw (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ Good t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aN) ((q.1.k + 7) / 8) = q.1.N ∧
    ((word t.mem q.1.B (slot ((q.1.k + 7) / 8) aN)).toNat * q.2.toNat + 1) % 2 ^ 64 = 0 ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aX) ((q.1.k + 7) / 8) = Spec.Rsa.os2ip xb ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aOne) ((q.1.k + 7) / 8) = 1 ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aR2) ((q.1.k + 7) / 8) = q.1.R

theorem DA.weak {q : DPub × BitVec 64} {t : State} (h : DA q t) : DAw q t :=
  let ⟨xb, σ, g, so, hR⟩ := h
  ⟨xb, σ, g, so.good, so.n, so.inv, so.x, so.one, hR⟩

/-- `DAw` through code that writes registers only. -/
theorem DAw.regs {q : DPub × BitVec 64} {s t : State} (h : DAw q s) (hm : t.mem = s.mem) {rs : List Reg}
    (k : Keep rs s t) (hrs : ∀ r ∈ rs, r ∈ mmRegs) : DAw q t := by
  obtain ⟨xb, σ, g, hg, hn, hinv, hx, hone, hR⟩ := h
  exact ⟨xb, σ, g.step (by rw [hm]; exact Frm.refl _ _ _) (k.mono hrs) (by rw [hm]),
    ⟨hg.scr.congr k.2.2, (k.gpr (fun h => by have := hrs _ h; simp [mmRegs] at this)).trans hg.rdi,
      by rw [hm]; exact hg.hdr⟩, by rw [hm]; exact hn, by rw [hm]; exact hinv, by rw [hm]; exact hx,
    by rw [hm]; exact hone, by rw [hm]; exact hR⟩

/-- `X := input R` leaks the same in runs with the same public data. -/
theorem pdMm_ctw : RelCT isa (Two DAw) (M.mm aXm aX aR2) (Two DB) := by
  refine two_post (two_map DPub.L (fun _ _ ⟨_, σ, g, hg, _⟩ => ⟨hg, g.1.z⟩)
    (M.ctL (by unfold MmUse; decide))) ?_
  rintro q t ⟨xb, σ, g, hg₀, hN₀, hinv₀, -, hone₀, hR⟩
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hn : q.1.B.toNat + slot ((q.1.k + 7) / 8) 8 ≤ 2 ^ 64 := by have := g.1.scr.nowrap; have := g.1.z; omega_arith
  refine WP.mono (mmN_ok M (o := aXm) (a := aX) (b := aR2) hg₀ g.1.z (by omega_arith)
    (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hN₀ hinv₀ (by rw [hR]; exact g.1.rlt)) fun t' ⟨hg, hn', hinv, hlt, _, ha, k⟩ =>
    ⟨xb, σ, g.step (arrays_pdAll ha) k (ha.hslot (by decide)), hg, hn', hinv, hlt, ?_⟩
  rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hone₀

/-- `X := input R` leaks the same in runs with the same public data. -/
theorem pdMm_ct : RelCT isa (Two DA) (M.mm aXm aX aR2) (Two DB) :=
  two_map id (fun _ _ h => h.weak) pdMm_ctw

/-- The exponentiation's public data. -/
def DPub.E (q : DPub × BitVec 64) : EPub := ⟨DPub.L q, q.1.N, q.1.ep, q.1.len, q.1.eb⟩

theorem db_pre {q : DPub × BitVec 64} {t : State} (h : DB q t) : PExpPre (DPub.E q) t := by
  obtain ⟨xb, σ, g, hg, hn, hinv, hlt, -⟩ := h
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hL2 := g.1.L2
  have hR := VG.Proof.Bignum.coprime_pow2 g.1.odd (64 * ((q.1.k + 7) / 8))
  obtain ⟨x, hx⟩ := exists_mont hR g.1.n1 (wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aXm) ((q.1.k + 7) / 8))
  have he := g.1.e.congrK g.inScr g.2.2.1
  exact ⟨_, x, ⟨hg, hn, hinv, rfl⟩, ⟨g.1.z, show 2 ≤ ((q.1.k + 7) / 8) by omega_arith,
    show ((q.1.k + 7) / 8) < 2 ^ 31 by omega_arith, hR, hlt, hx⟩,
    (g.fixed sE (by decide)).trans g.1.hE, (g.fixed sElen (by decide)).trans g.1.hL, g.1.L1,
    src_esrc he g.1.el (show q.1.len < 2 ^ 31 by omega_arith)⟩

/-- After the exponentiation, by `e - 1`. -/
def DC (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ X x, DG q.1 xb σ t ∧ ExpCtx t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 q.1.N X ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aY) ((q.1.k + 7) / 8) < q.1.N ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aY) ((q.1.k + 7) / 8) % q.1.N =
      x ^ Spec.Rsa.os2ip (evenLast q.1.eb) * 2 ^ (64 * ((q.1.k + 7) / 8)) % q.1.N

theorem pExpRanges_pdAll (w : Nat) : ∀ r ∈ pExpRanges w, r ∈ pdAll w :=
  fun _ hr => List.mem_append_right _ hr

/-- The exponentiation leaks the same in runs that agree on `e`. -/
theorem pdExp_ct : RelCT isa (Two DB) (Precomputed.expLoop M.mm) (Two DC) := by
  refine two_post ((two_map DPub.E (fun _ _ h => db_pre h) pExpLoop_ct).mono (fun _ _ h => h)
    fun _ _ _ => trivial) ?_
  rintro q t h
  obtain ⟨X, x, hc, hf, he, hlen, hL1, hsrc⟩ := db_pre h
  obtain ⟨xb, σ, g, -⟩ := h
  refine WP.mono (pExpLoop_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 he hlen hsrc.1 hL1
    hsrc.2.1 hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2) fun t' ⟨hc', hy, f₀, k⟩ => ?_
  have f : Frm q.1.B (pExpRanges ((q.1.k + 7) / 8)) t.mem t'.mem := f₀
  have hE : Spec.Rsa.os2ip (evenLast q.1.eb) ≠ 0 := by
    have := os2ip_evenLast g.1.eodd; have := g.1.e3; omega_arith
  rcases hy with ⟨h0, -⟩ | ⟨-, -, Y, hY, hYN, hYc⟩
  · exact absurd h0 hE
  exact ⟨xb, σ, X, x, g.step (f.mono (pExpRanges_pdAll _)) k
      (f.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (by unfold sMask sFn; omega_arith)), hc', by rw [← hY] at hYN; exact hYN, by rw [← hY] at hYc; exact hYc⟩

/-- After the last multiplication. -/
def DD (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ Good t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2

/-- The last multiplication, by the input, leaks the same in runs with the
same public data (`hfinal`, which `MmUse` does not list). -/
theorem pdFinal_ct (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) fun _ _ => True) :
    RelCT isa (Two DC) (M.mm aY aX aY) (Two DD) := by
  refine two_post (two_map DPub.L (fun _ _ ⟨_, _, _, _, g, hc, _⟩ => ⟨hc.good, g.1.z⟩) hfinal) ?_
  rintro q t ⟨xb, σ, X, x, g, hc, hYN, hYc⟩
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hR := VG.Proof.Bignum.coprime_pow2 g.1.odd (64 * ((q.1.k + 7) / 8))
  refine WP.mono (FoldedPublic.final_factor_ok M (x := x) (e := Spec.Rsa.os2ip (evenLast q.1.eb)) hc.good g.1.z (by omega_arith) (by omega_arith) hc.n hc.inv hR rfl
    hYN hYc) fun t' ⟨hg, _, ha, k⟩ => ?_
  have f : Frm q.1.B (finRanges ((q.1.k + 7) / 8)) t.mem t'.mem := Frm.of_arrays ha (by simp [finRanges])
  exact ⟨xb, σ, g.step (f.mono (by simp [finRanges, pdAll, pExpRanges, pBitRanges, bitRanges])) k
      (f.word_eq (fun r hr => by
        have := hdr_lt_slot ((q.1.k + 7) / 8) aAcc (show sMask < 32 by decide)
        have := hdr_lt_slot ((q.1.k + 7) / 8) aTmp (show sMask < 32 by decide)
        have := hdr_lt_slot ((q.1.k + 7) / 8) aY (show sMask < 32 by decide)
        simp only [finRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> omega_arith) (by unfold sMask sFn; omega_arith)), hg⟩

/-! ## The load and the checks -/

/-- The public data of `vg_rsa_public_precomputed`: `rest`'s, `pre` and the
stack pointer. -/
structure CPubD where
  d : DPub
  pp : Addr
  rsp : Addr

/-- What the load keeps. -/
def LH (p : CPubD) (t : State) : Prop :=
  Scr t p.d.B p.d.Z ∧ t.gpr .rdi = p.d.B ∧ slot ((p.d.k + 7) / 8) 8 ≤ p.d.Z ∧ 64 ≤ p.d.k ∧ p.d.k ≤ 1024 ∧
    word t.mem p.d.B (8 * sK) = BitVec.ofNat 64 p.d.k ∧ word t.mem p.d.B (8 * sN) = p.pp ∧
    (∀ i < 2 * ((p.d.k + 7) / 8), InRegions (t.rd ++ t.wr) (off p.pp (8 * i)) 8) ∧
    (∀ j < 16 * ((p.d.k + 7) / 8), p.d.Z ≤ ofs p.d.B (p.pp + BitVec.ofNat 64 j))

theorem LH.congr {p : CPubD} {s t : State} (h : LH p s) {rs : List (Nat × Nat)} (hf : Frm p.d.B rs s.mem t.mem)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : LH p t := by
  obtain ⟨hs, hdi, hZ, hk1, hk2, hK, hN, hpr, hps⟩ := h
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hZ, hk1, hk2, (hfx sK (by decide)).trans hK,
    (hfx sN (by decide)).trans hN, fun i hi => by rw [k.2.1, k.2.2]; exact hpr i hi, hps⟩

theorem pins_LH : Pins LH [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- `LH` with the header's `w` and bases. -/
def LW (p : CPubD) (t : State) : Prop :=
  LH p t ∧ word t.mem p.d.B (8 * sW) = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
    (∀ j < 8, word t.mem p.d.B (8 * sArr j) = off p.d.B (slot ((p.d.k + 7) / 8) j))

/-- A copy of `w` words from `pre + 8 c` into array `j`. -/
theorem ldCopy_ok {p : CPubD} {t : State} (h : LW p t) {c j : Nat} (hc : c ≤ (p.d.k + 7) / 8) (hj : j < 8)
    (hsi : t.gpr .rsi = off p.pp (8 * c)) (hbx : t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) j))
    (h12 : t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) :
    WP isa copyWords t fun t' => LW p t' ∧ Keep [.rax, .r14] t t' := by
  have h₀ : LH p t := h.1
  obtain ⟨⟨hs, hdi, hZ, hk1, hk2, hK, hN, hpr, hps⟩, hW, hb⟩ := h
  have hn := hs.nowrap
  have hsl := slot_le (w := (p.d.k + 7) / 8) hj
  have hge := hdr_lt_slot ((p.d.k + 7) / 8) j (show 31 < 32 by decide)
  have hA : ∀ i < 8, 8 * sArr i + 8 ≤ slot ((p.d.k + 7) / 8) j := fun i hi => by unfold sArr; omega_arith
  refine WP.mono (copyWords_ok (S := p.pp) (eS := 8 * c) hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => by rw [show 8 * c + 8 * i = 8 * (c + i) by omega_arith]; exact hpr _ (by omega_arith))
    (fun i hi => hs.st (by omega_arith))
    (fun i hi b hb => Or.inr (by
      have := hps (8 * c + 8 * i + b) (by omega_arith)
      rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; omega_arith))) fun t' ⟨_, _, ho, k⟩ => ?_
  refine ⟨⟨h₀.congr (Frm.of_outside ho (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; left; omega_arith) k (by decide),
    by rw [ho.word (by unfold sW; omega_arith) (by unfold sW; omega_arith)]; exact hW,
    fun i hi => by rw [ho.word (d := 8 * sArr i) (Or.inl (hA i hi)) (by unfold sArr; omega_arith)]; exact hb i hi⟩, k⟩

/-! ## The whole function -/

/-- A state the contract allows, with the public data `p`. -/
def CR (p : CPubD) (s : State) : Prop :=
  pdContract.pre s ∧ s.gpr .rsp = p.rsp ∧ stackArg s 2 = p.d.B ∧ (stackArg s 3).toNat * 8 = p.d.Z ∧
    (s.gpr .rsi).toNat = p.d.k ∧ s.gpr .rdi = p.d.op ∧ s.gpr .rdx = p.pp ∧ s.gpr .r8 = p.d.ep ∧
    stackArg s 0 = p.d.ip ∧ (s.gpr .r9).toNat = p.d.len ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = p.d.eb ∧
    wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8) = p.d.N ∧
    wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8) = p.d.R ∧
    Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.d.eb) = true

/-- What `entry` leaves (`pdEntry_ok`). -/
def PdEnt (s t : State) : Prop :=
  t.gpr .rdi = stackArg s 2 ∧
    word t.mem (stackArg s 2) (8 * 0) = s.gpr .rbx ∧ word t.mem (stackArg s 2) (8 * 1) = s.gpr .rbp ∧
    word t.mem (stackArg s 2) (8 * 2) = s.gpr .r12 ∧ word t.mem (stackArg s 2) (8 * 3) = s.gpr .r13 ∧
    word t.mem (stackArg s 2) (8 * 4) = s.gpr .r14 ∧ word t.mem (stackArg s 2) (8 * 5) = s.gpr .r15 ∧
    word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi ∧ word t.mem (stackArg s 2) (8 * sN) = s.gpr .rdx ∧
    word t.mem (stackArg s 2) (8 * sK) = s.gpr .rsi ∧ word t.mem (stackArg s 2) (8 * sE) = s.gpr .r8 ∧
    word t.mem (stackArg s 2) (8 * sElen) = s.gpr .r9 ∧ word t.mem (stackArg s 2) (8 * sIn) = stackArg s 0 ∧
    Outside (stackArg s 2) 0 (8 * 22) s.mem t.mem ∧ Keep [.r11, .rax, .rdi] s t

theorem pdEntry_split : Precomputed.entry =
    ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++ Precomputed.entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def CE1 (p : CPubD) (t : State) : Prop :=
  ∃ s, CR p s ∧ t.gpr .r11 = p.d.B ∧ t.gpr .rsp = p.rsp ∧ WP isa (.block (Precomputed.entry.drop 1)) t (PdEnt s)

/-- After `entry`. -/
def CE2 (p : CPubD) (t : State) : Prop := ∃ s, CR p s ∧ PdEnt s t

/-- After the load and the checks (`pdLoadWith_ok`). -/
def CL (p : CPubD) (t : State) : Prop :=
  ∃ s t₁, CR p s ∧ PdEnt s t₁ ∧
    wv t.mem p.d.B (slot ((p.d.k + 7) / 8) aN) ((p.d.k + 7) / 8) = p.d.N ∧
    wv t.mem p.d.B (slot ((p.d.k + 7) / 8) aR2) ((p.d.k + 7) / 8) = p.d.R ∧
    word t.mem p.d.B (8 * sW) = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
    (∀ j < 8, word t.mem p.d.B (8 * sArr j) = off p.d.B (slot ((p.d.k + 7) / 8) j)) ∧
    t.zf = some (!(chkv ((p.d.k + 7) / 8) p.d.N p.d.R)) ∧
    Frm p.d.B (pdLoadRanges ((p.d.k + 7) / 8)) t₁.mem t.mem ∧ Keep mmRegs t₁ t

theorem ce2_lh {p : CPubD} {t : State} (h : CE2 p t) : LH p t := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, -, hpp, -⟩, hdi, -, -, -, -, -, -, -, hN, hK, -, -, -, -, k⟩ := h
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  subst hB hZ hk hpp
  exact ⟨c.hs.congr k.2.2, hdi, by dsimp only; unfold slot hdrBytes; omega_arith, c.hk1, c.hk2, by rw [hK, ofNat_toNat64], hN,
    fun i hi => by rw [k.2.1, k.2.2]; exact c.hpr i hi, c.hps⟩

/-- What `fail` needs after the load. -/
theorem cl_fail {p : CPubD} {t : State} (h : CL p t) :
    Scr t p.d.B p.d.Z ∧ t.gpr .rdi = p.d.B ∧ 8 * 32 ≤ p.d.Z ∧ 64 ≤ p.d.k ∧ p.d.k ≤ 1024 ∧
      word t.mem p.d.B (8 * sOut) = p.d.op ∧ word t.mem p.d.B (8 * sK) = BitVec.ofNat 64 p.d.k := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, t₁, ⟨hpre, -, hB, hZ, hk, hop, -⟩, ⟨hdi, -, -, -, -, -, -, hO, -, hK, -, -, -, -, k₁⟩, -, -, -, -, -,
    f, k⟩ := h
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  subst hB hZ hk hop
  have x := Fixed.of_frm f (pdLoadRanges_fixed _)
  exact ⟨c.hs.congr (k₁.trans k).2.2, (k.gpr (by decide)).trans hdi, by dsimp only; omega_arith, c.hk1, c.hk2,
    (x sOut (by decide)).trans hO, by rw [x sK (by decide), hK, ofNat_toNat64]⟩

/-- `rest`'s hypotheses after the load, for values that pass the checks. -/
theorem cl_rest {p : CPubD} {t : State} (h : CL p t) (he : isa.eval .e t = some false) : DRel p.d t := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, t₁, ⟨hpre, -, hB, hZ, hk, hop, hpp, hep, hip, hlen, heb, hNv, hRv, hev⟩,
    ⟨hdi, -, -, -, -, -, -, hO, -, hK, hE, hL, hIn, ho₁, k₁⟩, hN, hR, hW, hb, hz, f, k₂⟩ := h
  have c := pdCtx_of hpre
  have := c.hk1
  subst hB hZ hk hop hpp hep hip hlen heb hNv hRv
  have hchk : chkv (((s.gpr .rsi).toNat + 7) / 8)
      (wv t.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8))
      (wv t.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8)) = true := by
    rw [hN, hR]; simp only [eval, hz, Option.some.injEq] at he; simpa using he
  rw [← chk_eq (by omega_arith)] at hchk
  obtain ⟨hodd, hN1, hRN⟩ := checks_facts (by omega_arith) hchk
  have hp := pdPre_of c hdi hO hK hE hL hIn ho₁ k₁ hW hb f k₂ hodd hN1 (checks_big (by omega_arith) hchk) hRN hev
  rw [hN, hR] at hp
  exact ⟨_, hp⟩

/-- The public data of a state. -/
def cpubOfD (s : State) : CPubD :=
  ⟨⟨stackArg s 2, (stackArg s 3).toNat * 8, (s.gpr .rsi).toNat, s.gpr .rdi, s.gpr .r8, stackArg s 0,
    (s.gpr .r9).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat,
    wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8),
    wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8)⟩,
    s.gpr .rdx, s.gpr .rsp⟩

end VG.Proof.Bignum.X86_64
