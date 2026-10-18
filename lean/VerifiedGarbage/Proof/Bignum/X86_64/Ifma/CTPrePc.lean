module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTPre
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTPre
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PrePc
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PrePc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPhasePc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPhasePc
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64: constant time of `pre` with the precomputed values

`prep` with `pre` is its start as without it (`prepHead_ct`), then `loadPre`
(`loadPre_ct`): `prepPc_ct`. `pre` with `pre` is `prep` for each prime
(`prePc_ct`), its offsets read as in the primes' phases (`offQ_ct`,
`offP_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64 CrtCTQ CrtCTUnitPc CrtCTPhasePc

/-! ## `prep` -/

/-- `prepPc_ok`'s hypotheses, and `E`, what the offset's code needs. -/
def PrepPrePc (sl : Nat) (E : UPubPc → State → Prop) (p : UPubPc) (s : State) : Prop :=
  PrepPre sl p.u s ∧ PreAt p.u.B p.u.Z p.P p.W p.rsp s ∧ p.d + p.u.wx ≤ p.W ∧ E p s

/-- `prep` with `pre` is constant time, given that the offset's code `po`
is. -/
theorem prepPc_ct (M : Mont) (sl : Nat) {po : List Instr} {E QX : UPubPc → State → Prop}
    (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true)
    (hX : ∀ p s t (mx : BitVec 64), E p s → SubCtx t p.u.B p.u.Z p.u.o p.u.w p.u.wx mx →
      Frm p.u.B [xRange p.u.o p.u.wx] s.mem t.mem → QX p t)
    (hQ : ∀ a s t, QX a s → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → QX a t)
    (hpo : RelCT isa (Two fun a s => LpA Public.aY a.lp s ∧ QX a s) (.block po) (Two (LpB Public.aY))) :
    RelCT isa (Two (PrepPrePc sl E)) (seqs (CrtIfma.prep M.mm sl true po)) fun _ _ => True := by
  rw [show CrtIfma.prep M.mm sl true po = prepHead M.mm sl ++ (Crt.loadPre Public.aY po ++
      ([.block [leave]] : List (Prog isa))) by simp only [CrtIfma.prep, prepHead, ↓reduceIte, List.append_assoc]]
  refine RelCT.seqs_app (by simp [prepHead]) (by simp [Crt.loadPre])
    (RelCT.seq (two_post (Ψ := fun (a : UPubPc) t => LpPre Public.aY a.lp t ∧ QX a t)
      ((two_map (fun a : UPubPc => a.u) (fun _ _ h => prep_chain M h.1) (prepHead_ct M sl hR2 hXm hT)).mono
        (fun _ _ h => h) fun _ _ _ => trivial) fun a s h => ?_)
      (loadPre_ct UPubPc.lp (by taint_decide) (by taint_decide) (fun a s t h hm k => hQ a s t h hm k.2.1 k.2.2)
        hpo))
  obtain ⟨⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX', hX1⟩, ⟨hpre, hsp⟩, hdW, he⟩ := h
  have hn := hg.scr.nowrap
  have hX8 : 256 ≤ slot a.u.wx 8 := by unfold slot hdrBytes; omega
  rw [show prepHead M.mm sl = ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc M.mm Public.aR2 ++
      copyArr Public.aY aXc ++ redc M.mm Public.aXm ++ ([M.mm aT Public.aY aXc] : List (Prog isa)) ++
      copyArr aXc aT by simp only [prepHead, List.append_assoc]]
  refine WP.mono (prepHead_frame M hg hw28 hlo hhi hwx2 hwx hsl hslv hws hX' hX1) fun t ⟨hc, k, f⟩ => ?_
  have i : InScr a.u.B a.u.Z s.mem t.mem := InScr.of_frm f fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  exact ⟨lpPre_sub hc (hpre.congrK i k (by decide)) hdW ((k.gpr (by decide)).trans hsp) hwx2 (by omega),
    hX a s t mx he hc f⟩

/-! ## `pre` -/

/-- The public data of `pre` with `pre`. -/
structure PrePubPc where
  pp : PrePub
  P : Addr
  W : Nat
  rsp : Addr

/-- `q`'s `prep`'s public data. -/
abbrev PrePubPc.uq (p : PrePubPc) : UPubPc :=
  ⟨p.pp.uq, p.P, p.W, 2 * p.pp.w + p.pp.wp, p.rsp, ⟨p.pp.B, p.pp.w, p.pp.op, p.pp.wp⟩⟩

/-- `p`'s `prep`'s public data. -/
abbrev PrePubPc.up (p : PrePubPc) : UPubPc :=
  ⟨p.pp.up, p.P, p.W, 2 * p.pp.w, p.rsp, ⟨p.pp.B, p.pp.w, 0, 0⟩⟩

/-- `prePc_ok`'s hypotheses. -/
def PrePrePc (p : PrePubPc) (s : State) : Prop :=
  PrePre p.pp s ∧ PreAt p.pp.B p.pp.Z p.P p.W p.rsp s ∧ 2 * p.pp.w + p.pp.wp + p.pp.wp ≤ p.W

/-- Before `pre` with `pre`. -/
def PR0Pc (M : Mont) (p : PrePubPc) (s : State) : Prop :=
  PrepPrePc sWsQ PHdr p.uq s ∧ WP isa (seqs (CrtIfma.prep M.mm sWsQ true Crt.offQ)) s (PrepPrePc sWsP NBase p.up)

/-- `prePc_ok`'s hypotheses give `PR0Pc`, as `prePc_ok` runs the pieces. -/
theorem prePc_chain (M : Mont) {p : PrePubPc} {s : State} (h : PrePrePc p s) : PR0Pc M p s := by
  have h0 := (pre_chain M h.1).1
  obtain ⟨⟨B, Z, w, minv, N, op, oq, wp⟩, P, W, rsp⟩ := p
  obtain ⟨hp, ha, hW⟩ := h
  dsimp only [PrePre] at hp ha hW h0 ⊢
  obtain ⟨mp, mq, Pn, Q, hg, hw28, hlo, hpq, hoq, hwp2, hw2, hsp, hsq, hwsp, hwsq, hN, hP,
    hP1, hPodd, hQ, hQ1, hQodd⟩ := hp
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega
  have ho64 : oq < 2 ^ 64 := by omega
  have hl : ∀ d, d + 8 ≤ Z → InRegions (s.rd ++ s.wr) (off B d) 8 := fun d hd => hs.ld hd
  have hQd : ∀ r ∈ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega)
  refine ⟨⟨h0, ha, show 2 * w + wp + wp ≤ W by omega, hsp, hwsp.hdr.hw, hlo, show op + 8 * 32 ≤ oq by omega,
    rfl, rfl, rfl, show B.toNat + oq ≤ 2 ^ 64 by omega⟩, ?_⟩
  refine WP.mono (prepPc_ok (C := 0) M hg hw28 (by omega) hoq hwp2 hw2 (by decide) hsq hwsq hN False.elim hQ hQ1
    hQodd ha.1 (d := 2 * w + wp) (by omega) fun t hdi hrd hwr hlk hf => ?_)
    fun s₁ ⟨hg₁, _, _, _, _, _, _, fQ, kQ, _⟩ => ?_
  · have hb : ∀ d, d + 8 ≤ oq → word t.mem B d = word s.mem B d := fun d hd => hf.x_below hd ho64
    exact offQ_ok hdi (by rw [hrd, hwr, off_off]; exact hl _ (by unfold sLink sFn; omega)) hlk
      (by rw [hrd, hwr]; exact hl _ (by unfold sW; omega)) (by rw [hb _ (by unfold sW; omega)]; exact hg.hdr.hw)
      (by rw [hrd, hwr]; exact hl _ (by unfold sWsP sFn; omega))
      (by rw [hb _ (by unfold sWsP sFn; omega)]; exact hsp)
      (by rw [hrd, hwr, off_off]; exact hl _ (by unfold sW; omega))
      (by rw [word_off, hb _ (by unfold sW; omega), ← word_off]; exact hwsp.hdr.hw)
  have hb : ∀ d, d + 8 ≤ oq → word s₁.mem B d = word s.mem B d := fun d hd => fQ.x_below hd ho64
  have i₁ : InScr B Z s.mem s₁.mem := InScr.of_frm fQ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  dsimp only [PrepPrePc, PrepPre, PrePubPc.up, PrePub.up]
  exact ⟨⟨mp, Pn, hg₁, hw28, hlo, by omega, hwp2, by omega, by decide,
    by rw [hb _ (by unfold sWsP sFn; omega)]; exact hsp,
    hwsp.of_disj fQ (fun r hr => by rcases hQd r hr with h | h <;> omega) (by omega),
    hP.of_disj fQ hQd (by omega), hP1⟩, PreAt.congrK ha i₁ kQ (by decide), show 2 * w + wp ≤ W by omega, rfl, rfl,
    rfl⟩

/-- `q`'s offset's bases, in its workspace. -/
theorem pHdr_qxf {p : UPubPc} {s t : State} {mx : BitVec 64} (h : PHdr p s)
    (hc : SubCtx t p.u.B p.u.Z p.u.o p.u.w p.u.wx mx) (hf : Frm p.u.B [xRange p.u.o p.u.wx] s.mem t.mem) :
    OffQF p.lp p.D t ∧ p.lp.d = 2 * p.D.w + p.D.wp := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  have hs := hc.scr
  have hn := hs.nowrap
  have hlo := hc.lo
  have hhi := hc.hi
  have hX8 : 256 ≤ slot p.u.wx 8 := by unfold slot hdrBytes; omega
  have ho64 : p.u.o < 2 ^ 64 := by omega
  have hb : ∀ d, d + 8 ≤ p.u.o → word t.mem p.u.B d = word s.mem p.u.B d := fun d hd => hf.x_below hd ho64
  refine ⟨⟨⟨?_, hc.link.trans a5.symm, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, show p.d = _ by rw [a6]; exact a7⟩
  · show InRegions (t.rd ++ t.wr) (off (off p.u.B p.u.o) (8 * sLink)) 8
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega)
  · rw [a5]; exact hs.ld (by have := hdr_lt_slot p.u.w 8 (show sW < 32 by decide); omega)
  · rw [a5, a6]; exact hc.nw
  · rw [a5]; exact hs.ld (by have := hdr_lt_slot p.u.w 8 (show sWsP < 32 by decide); omega)
  · rw [a5, hb _ (by have := hdr_lt_slot p.u.w 8 (show sWsP < 32 by decide); omega)]; exact a1
  · rw [a5, off_off]; exact hs.ld (by unfold sW; omega)
  · rw [a5, word_off, hb _ (by unfold sW; omega), ← word_off]; exact a2

/-- `p`'s offset's bases, in its workspace. -/
theorem nBase_pxf {p : UPubPc} {t : State} {mx : BitVec 64} (h : NBase p t)
    (hc : SubCtx t p.u.B p.u.Z p.u.o p.u.w p.u.wx mx) : OffPF p.lp p.D t ∧ p.lp.d = 2 * p.D.w := by
  obtain ⟨a5, a6, a7⟩ := h
  have hs := hc.scr
  have hlo := hc.lo
  have hhi := hc.hi
  have hX8 : 256 ≤ slot p.u.wx 8 := by unfold slot hdrBytes; omega
  refine ⟨⟨?_, hc.link.trans a5.symm, ?_, ?_⟩, show p.d = _ by rw [a6]; exact a7⟩
  · show InRegions (t.rd ++ t.wr) (off (off p.u.B p.u.o) (8 * sLink)) 8
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega)
  · rw [a5]; exact hs.ld (by have := hdr_lt_slot p.u.w 8 (show sW < 32 by decide); omega)
  · rw [a5, a6]; exact hc.nw

/-- `pre` with `pre` is constant time. -/
theorem prePc_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm) :
    RelCT isa (Two PrePrePc) (seqs (CrtIfma.pre M.mm true)) fun _ _ => True := by
  refine two_map id (fun _ _ h => prePc_chain M h) ?_
  rw [pre_pc]
  refine ct_steps (by simp [CrtIfma.prep]) (by simp [CrtIfma.prep]) PrePubPc.uq (fun _ _ h => h.1)
    (fun _ _ h => h.2) (prepPc_ct M sWsQ (QX := fun a s => OffQF a.lp a.D s ∧ a.lp.d = 2 * a.D.w + a.D.wp) hR2 hXm
      (by taint_decide) (fun _ _ _ _ h hc hf => pHdr_qxf h hc hf) (fun _ _ _ h hm hrd hwr => ⟨h.1.congr hm hrd hwr, h.2⟩)
      (offQ_ct UPubPc.lp UPubPc.D (fun _ _ h => h.1) fun _ _ h => h.2)) ?_
  exact ct_last PrePubPc.up (fun _ _ h => h) (prepPc_ct M sWsP (QX := fun a s => OffPF a.lp a.D s ∧ a.lp.d = 2 * a.D.w)
    hR2 hXm (by taint_decide) (fun _ _ _ _ h hc _ => nBase_pxf h hc) (fun _ _ _ h hm hrd hwr => ⟨h.1.congr hm hrd hwr, h.2⟩)
    (offP_ct UPubPc.lp UPubPc.D (fun _ _ h => h.1) fun _ _ h => h.2))

end VG.Proof.Bignum.X86_64
