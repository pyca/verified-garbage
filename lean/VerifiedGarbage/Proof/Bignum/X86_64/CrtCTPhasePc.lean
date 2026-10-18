module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTUnitPc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTUnitPc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtBackPc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtBackPc
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: constant time of the primes' phases

`q`'s and `p`'s phases with `pre` (`qPhasePc_ct`, `pPhasePc_ct`): their
starts by `unitPc_ct`, the rest as without `pre` (`qRest_ct`, `pRest_ct`).
Their public data are those of the phases, `pre`'s pointer and length, the
stack pointer and, for `q`, where `p`'s workspace is.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## `q`'s phase -/

/-- The public data of `q`'s phase with `pre`: also `p`'s workspace, which
`offQ` reads. -/
structure QPubPc where
  ph : PhasePub
  P : Addr
  W : Nat
  rsp : Addr
  op : Nat
  wp : Nat

/-- `p`'s workspace's header, as `offQ` reads it. -/
def PHdr (p : UPubPc) (s : State) : Prop :=
  word s.mem p.u.B (8 * sWsP) = off p.u.B p.D.op ∧ word s.mem (off p.u.B p.D.op) (8 * sW) = BitVec.ofNat 64 p.D.wp ∧
    slot p.u.w 8 ≤ p.D.op ∧ p.D.op + 8 * 32 ≤ p.u.o ∧ p.D.B = p.u.B ∧ p.D.w = p.u.w ∧
    p.d = 2 * p.u.w + p.D.wp ∧ p.u.B.toNat + p.u.o ≤ 2 ^ 64

/-- `qPhasePc_ok`'s hypotheses. -/
def QPrePc (p : QPubPc) (s : State) : Prop :=
  QPre p.ph s ∧ PreAt p.ph.B p.ph.Z p.P p.W p.rsp s ∧ 2 * p.ph.w + p.wp + p.ph.wx ≤ p.W ∧
    word s.mem p.ph.B (8 * sWsP) = off p.ph.B p.op ∧ word s.mem (off p.ph.B p.op) (8 * sW) = BitVec.ofNat 64 p.wp ∧
    slot p.ph.w 8 ≤ p.op ∧ p.op + 8 * 32 ≤ p.ph.o

/-- `qPhase M.mm E.code true` is constant time. -/
def QPhasePcCT (M : Mont) (E : CrtExpL M) : Prop :=
  RelCT isa (Two QPrePc) (seqs (qPhase M.mm E.code true)) fun _ _ => True

namespace CrtCTPhasePc

open CrtCTQ CrtCTUnitPc

/-- The start's public data. -/
def uq (p : QPubPc) : UPubPc :=
  ⟨up p.ph, p.P, p.W, 2 * p.ph.w + p.wp, p.rsp, ⟨p.ph.B, p.ph.w, p.op, p.wp⟩⟩

theorem pHdr_frm {p : UPubPc} {s t : State} (h : PHdr p s) (hf : Frm p.u.B (gRanges p.u.w) s.mem t.mem) :
    PHdr p t := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hz := h5.2.2.2
  have ht : ∀ d, slot p.u.w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word t.mem p.u.B d = word s.mem p.u.B d := fun d hd hd' =>
    hf.word_eq (fun r hr => Or.inr (by have := gRanges_le p.u.w r hr; omega)) hd'
  have h8 := hdr_lt_slot p.u.w 8 (show sWsP < 32 by decide)
  refine ⟨?_, ?_, h3, h4, h5⟩
  · rw [(hf.mono (rs' := gRanges p.u.w ++ [xRange (slot p.u.w 8) 0]) fun _ hr => List.mem_append_left _ hr).gx_hdr
      (Nat.le_refl _) (by decide) (by decide) (by decide)]
    exact h1
  · rw [word_off, ht _ (by omega) (by unfold sW; omega), ← word_off]; exact h2

theorem pHdr_qx {sl : Nat} {p : UPubPc} {t : State} (h1 : U1 sl p.u t) (h : PHdr p t) :
    OffQF p.lp p.D t ∧ p.lp.d = 2 * p.D.w + p.D.wp := by
  obtain ⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1⟩ := h1
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, -⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have hX8 : 256 ≤ slot p.u.wx 8 := by unfold slot hdrBytes; omega
  have h8 := hdr_lt_slot p.u.w 8 (show 31 < 32 by decide)
  refine ⟨⟨⟨?_, hws.link.trans a5.symm, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, show p.d = _ by rw [a6]; exact a7⟩
  · show InRegions (t.rd ++ t.wr) (off (off p.u.B p.u.o) (8 * sLink)) 8
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega)
  · rw [a5]; exact hs.ld (by unfold sW; omega)
  · rw [a5, a6]; exact hg.hdr.hw
  · rw [a5]; exact hs.ld (by unfold sWsP sFn; omega)
  · rw [a5]; exact a1
  · rw [a5, off_off]; exact hs.ld (by unfold sW; omega)
  · rw [a5]; exact a2

theorem uPrePc_q {p : QPubPc} {s : State} (h : QPrePc p s) : UPrePc sWsQ PHdr (uq p) s := by
  obtain ⟨hq, hpa, hW, h1, h2, h3, h4⟩ := h
  have hn := (let ⟨_, _, _, _, hg, _⟩ := hq; hg.scr.nowrap)
  have hhi := (let ⟨_, _, _, _, _, _, _, _, hhi, _⟩ := hq; hhi)
  exact ⟨uPre hq, hpa, by simp only [uq, up]; omega, h1, h2, h3, h4, rfl, rfl, rfl, by simp only [uq, up]; omega⟩

/-- `q`'s start with `pre`, as `unitWith_q1` needs it. -/
theorem unitPc_q1 (M : Mont) {p : QPubPc} {s : State} (h : QPrePc p s) :
    WP isa (seqs (Crt.gPow M.mm sWsQ ++ ([.block [.mov .rdi (.mem (hdr sWsQ))]] : List (Prog isa)) ++
      Crt.loadPre Public.aY Crt.offQ ++ ([.block [leave]] : List (Prog isa)))) s (Q1 p.ph) := by
  obtain ⟨hq, ⟨hpre, -⟩, hW, h1, h2, h3, h4⟩ := h
  refine unitWith_q1 hq fun mx' X' hws' hX' hX1' hXodd' => ?_
  obtain ⟨mx, X, _, eb, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hodd, hN1, -⟩ := hq
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot p.ph.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.ph.wx 8 := by unfold slot hdrBytes; omega
  have hl : ∀ d, d + 8 ≤ p.ph.Z → ∀ {t : State}, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (off p.ph.B d) 8 := fun d hd t hrd hwr => by rw [hrd, hwr]; exact hg.scr.ld hd
  refine WP.mono (unitPhasePc_ok M hg hw hw28 hlo hhi hwx2 hwx (by decide) (by decide) (by decide) hslv hws' hN
    hodd hN1 hX' hX1' hpre (d := 2 * p.ph.w + p.wp) (by omega) fun t hdi hrd hwr hlk hf => ?_) fun _ h => ⟨_, h⟩
  have hpk : word t.mem (off p.ph.B p.op) (8 * sW) = BitVec.ofNat 64 p.wp := by
    rw [word_off, hf.word_eq (fun r hr' => by
      rcases List.mem_append.mp hr' with hr' | hr'
      · exact .inr (by have := gRanges_le p.ph.w r hr'; omega)
      · rw [List.mem_singleton.mp hr']; exact .inl (by simp only [xRange]; unfold sW; omega))
      (by unfold sW at *; omega), ← word_off]
    exact h2
  exact offQ_ok hdi (by rw [hrd, hwr, off_off]; exact hg.scr.ld (by unfold sLink sFn; omega)) hlk
    (hl _ (by unfold sW; omega) hrd hwr)
    (by rw [hf.gx_hdr hlo (by decide) (by decide) (by decide)]; exact hg.hdr.hw)
    (hl _ (by unfold sWsP sFn; omega) hrd hwr)
    (by rw [hf.gx_hdr hlo (by decide) (by decide) (by decide)]; exact h1)
    (by rw [hrd, hwr, off_off]; exact hg.scr.ld (by unfold sW; omega)) hpk

end CrtCTPhasePc

open CrtCTQ CrtCTUnitPc CrtCTPhasePc in
/-- `q`'s phase with `pre` is constant time. -/
theorem qPhasePc_ct (M : Mont) (E : CrtExpL M) (hG : GPowCT M sWsQ) (hP : PowCT M E sWsQ sDq sQlen) :
    QPhasePcCT M E := by
  unfold QPhasePcCT
  rw [qPhase_pc]
  refine RelCT.seqs_append (by simp [Crt.gPow]) (by simp) (RelCT.seq (two_post (Ψ := fun p => Q1 p.ph)
    (two_map uq (fun _ _ h => uPrePc_q h) (unitPc_ct M (QX := fun a s => OffQF a.lp a.D s ∧ a.lp.d = 2 * a.D.w + a.D.wp)
      hG (by taint_decide)
      (fun _ _ _ h hf _ _ => pHdr_frm h hf)
      (fun _ _ h1 h => pHdr_qx h1 h)
      (fun _ _ _ h hm hrd hwr => ⟨h.1.congr hm hrd hwr, h.2⟩)
      (offQ_ct UPubPc.lp UPubPc.D (fun _ _ h => h.1) fun _ _ h => h.2)))
    fun _ _ h => unitPc_q1 M h) (two_map QPubPc.ph (fun _ _ h => h) (qRest_ct M E hP)))

/-! ## `p`'s phase -/

/-- The public data of `p`'s phase with `pre`. -/
structure PPubPc where
  pp : PPhasePub
  P : Addr
  W : Nat
  rsp : Addr

/-- `pPhasePc_ok`'s hypotheses. -/
def PPrePc (p : PPubPc) (s : State) : Prop :=
  PPre p.pp s ∧ PreAt p.pp.ph.B p.pp.ph.Z p.P p.W p.rsp s ∧ 2 * p.pp.ph.w + p.pp.ph.wx ≤ p.W

/-- `pPhase M.mm E.code true` is constant time. -/
def PPhasePcCT (M : Mont) (E : CrtExpL M) : Prop :=
  RelCT isa (Two PPrePc) (seqs (pPhase M.mm E.code true)) fun _ _ => True

/-- The bases `offP` reads are `n`'s. -/
def NBase (p : UPubPc) (_ : State) : Prop := p.D.B = p.u.B ∧ p.D.w = p.u.w ∧ p.d = 2 * p.u.w

/-- Before `pPhase` with `pre`. -/
def PO0Pc (M : Mont) (E : CrtExpL M) (p : PPubPc) (s : State) : Prop :=
  UPrePc sWsP NBase ⟨p.pp.u, p.P, p.W, 2 * p.pp.ph.w, p.rsp, ⟨p.pp.ph.B, p.pp.ph.w, 0, 0⟩⟩ s ∧
    WP isa (seqs (Crt.gPow M.mm sWsP ++ ([.block [.mov .rdi (.mem (hdr sWsP))]] : List (Prog isa)) ++
      Crt.loadPre Public.aY Crt.offP ++ ([.block [leave]] : List (Prog isa)))) s (PO1 M E p.pp)

namespace CrtCTPhasePc

open CrtCTQ CrtCTUnitPc

theorem nBase_px {sl : Nat} {p : UPubPc} {t : State} (h1 : U1 sl p.u t) (h : NBase p t) :
    OffPF p.lp p.D t ∧ p.lp.d = 2 * p.D.w := by
  obtain ⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1⟩ := h1
  obtain ⟨a5, a6, a7⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have hX8 : 256 ≤ slot p.u.wx 8 := by unfold slot hdrBytes; omega
  have h8 := hdr_lt_slot p.u.w 8 (show 31 < 32 by decide)
  refine ⟨⟨?_, hws.link.trans a5.symm, ?_, ?_⟩, show p.d = _ by rw [a6]; exact a7⟩
  · show InRegions (t.rd ++ t.wr) (off (off p.u.B p.u.o) (8 * sLink)) 8
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega)
  · rw [a5]; exact hs.ld (by unfold sW; omega)
  · rw [a5, a6]; exact hg.hdr.hw

theorem o0Pc_of (M : Mont) (E : CrtExpL M) {p : PPubPc} {s : State} (h : PPrePc p s) : PO0Pc M E p s := by
  obtain ⟨hp, hpa, hW⟩ := h
  refine ⟨⟨(o0_of M E hp).1, hpa, by omega, rfl, rfl, rfl⟩, o0With_of M E hp fun mx' X' hws' hX' hX1' hXodd' => ?_⟩
  obtain ⟨⟨⟨B, Z, w, minv, N, o, wx, ep, len⟩, oq, wq, qp⟩, P, W, rsp⟩ := p
  dsimp only [PPre] at hp hpa hW hws' hX' ⊢
  obtain ⟨mx, mq, X, C, eb, qib, c, hg, hw, hw28, hlo, hhi, hqhi, hwx2, hwx, -, -, hslv, hws, -, -, hN, hodd, hN1,
    -⟩ := hp
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hhi' : o + slot wx 8 + wsTab wx ≤ Z := by omega
  refine WP.mono (unitPhasePc_ok M hg hw hw28 hlo hhi' hwx2 hwx (sl := sWsP) (by decide) (by decide) (by decide)
    hslv hws' hN hodd hN1 hX' hX1' hpa.1 (d := 2 * w) (by omega) fun t hdi hrd hwr hlk hf => ?_) fun _ h => ⟨_, h⟩
  exact offP_ok hdi (by rw [hrd, hwr, off_off]; exact hg.scr.ld (by unfold sLink sFn; omega)) hlk
    (by rw [hrd, hwr]; exact hg.scr.ld (by unfold sW; omega))
    (by rw [hf.gx_hdr hlo (by decide) (by decide) (by decide)]; exact hg.hdr.hw)

end CrtCTPhasePc

open CrtCTQ CrtCTUnitPc CrtCTPhasePc in
/-- `p`'s phase with `pre` is constant time, given its pieces' claims. -/
theorem pPhasePc_ct (M : Mont) (E : CrtExpL M) (hG : GPowCT M sWsP) (hP : PowCT M E sWsP sDp sPlen)
    (hRX : RedcCT M Public.aX) (hL : LoadCT aChunk sQinv sPlen) : PPhasePcCT M E := by
  unfold PPhasePcCT
  refine two_map id (fun _ _ h => o0Pc_of M E h) ?_
  rw [pPhase_pc]
  exact ct_steps (by simp [Crt.gPow]) (by simp [mqSteps])
    (fun p : PPubPc => (⟨p.pp.u, p.P, p.W, 2 * p.pp.ph.w, p.rsp, ⟨p.pp.ph.B, p.pp.ph.w, 0, 0⟩⟩ : UPubPc))
    (fun _ _ h => h.1) (fun _ _ h => h.2)
    (unitPc_ct M (QX := fun a s => OffPF a.lp a.D s ∧ a.lp.d = 2 * a.D.w) hG (by taint_decide)
      (fun _ _ _ h _ _ _ => h) (fun _ _ h1 h => nBase_px h1 h) (fun _ _ _ h hm hrd hwr => ⟨h.1.congr hm hrd hwr, h.2⟩)
      (offP_ct UPubPc.lp UPubPc.D (fun _ _ h => h.1) fun _ _ h => h.2))
    (two_map PPubPc.pp (fun _ _ h => h) (pRest_ct M E hP hRX hL))

end VG.Proof.Bignum.X86_64
