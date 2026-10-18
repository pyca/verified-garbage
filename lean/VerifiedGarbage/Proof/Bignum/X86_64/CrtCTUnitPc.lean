module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTOff
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTOff
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrontPc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrontPc
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: constant time of a prime's start

The start of a prime's phase with `pre` (`unitPc_ct`): `G` as before, then
the prime's `Y` from word `d` of `pre`, at the offset `po` computes. Its
public data are those of `unit_ct`, `pre`'s pointer and length, the offset,
the stack pointer, and the bases `po` reads (`UPubPc`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of a prime's start with `pre`. -/
structure UPubPc where
  u : UPub
  P : Addr
  W : Nat
  d : Nat
  rsp : Addr
  D : OffD

/-- `loadPre`'s public data, in the prime's workspace. -/
def UPubPc.lp (p : UPubPc) : LPub := ⟨off p.u.B p.u.o, slot p.u.wx 8, p.u.wx, p.P, p.d, p.rsp⟩

/-- `pre` at `P` (`W` words) and the stack pointer. -/
def PreAt (B : Addr) (Z : Nat) (P : Addr) (W : Nat) (rsp : Addr) (s : State) : Prop :=
  PreSrc s B Z P W ∧ s.gpr .rsp = rsp

theorem PreAt.congrK {B : Addr} {Z : Nat} {P : Addr} {W : Nat} {rsp : Addr} {s t : State} {rs : List Reg}
    (h : PreAt B Z P W rsp s) (hi : InScr B Z s.mem t.mem) (k : Keep rs s t) (hsp : Reg.rsp ∉ rs) :
    PreAt B Z P W rsp t :=
  ⟨h.1.congrK hi k hsp, (k.1 _ hsp).trans h.2⟩

/-- `unitPhasePc_ok`'s hypotheses, and `E`, what the offset's code needs. -/
def UPrePc (sl : Nat) (E : UPubPc → State → Prop) (p : UPubPc) (s : State) : Prop :=
  UPre sl p.u s ∧ PreAt p.u.B p.u.Z p.P p.W p.rsp s ∧ p.d + p.u.wx ≤ p.W ∧ E p s

/-- `loadPre`'s hypotheses in a prime's workspace, from `pre` outside the
working space. -/
theorem lpPre_sub {t : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {P : Addr} {W d : Nat} {rsp : Addr}
    (hc : SubCtx t B Z o w wx mx) (hp : PreSrc t B Z P W) (hdW : d + wx ≤ W) (hsp : t.gpr .rsp = rsp)
    (hwx2 : 2 ≤ wx) (hwx : wx < 2 ^ 31) :
    LpPre Public.aY ⟨off B o, slot wx 8, wx, P, d, rsp⟩ t := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hY := slot_le (w := wx) (show Public.aY < 8 by decide)
  -- A byte outside the working space is past the prime's arrays.
  have hfar : ∀ x : Addr, Z ≤ ofs B x → slot wx Public.aY + 8 * (wx + 2) ≤ ofs (off B o) x := fun x hx => by
    rcases ofs_rebase B x (o := o) (by omega) with ⟨_, e⟩ | ⟨h, _⟩
    · rw [e]; omega
    · omega
  refine ⟨⟨mx, hc.good, Nat.le_refl _, show 1 ≤ wx by omega, hwx, by decide, fun i hi => ?_, fun i hi b hb => ?_⟩,
    hsp, hp.arg, hp.val⟩
  · have hi' : i < wx := hi
    show InRegions (t.rd ++ t.wr) (off P (8 * d + 8 * i)) 8
    rw [show 8 * d + 8 * i = 8 * (d + i) by omega]; exact hp.rd _ (by omega)
  · have hi' : i < wx := hi
    show _ ∨ slot wx Public.aY + 8 * (wx + 2) ≤ ofs (off B o) (off P (8 * d + 8 * i) + _)
    refine .inr (hfar _ ?_)
    have := hp.out (d + i) (by omega) b hb
    rwa [show 8 * (d + i) = 8 * d + 8 * i by omega] at this

namespace CrtCTUnitPc

open CrtCTQ

/-- After `gPow`. -/
def U1Pc (sl : Nat) (E : UPubPc → State → Prop) (p : UPubPc) (t : State) : Prop :=
  U1 sl p.u t ∧ PreAt p.u.B p.u.Z p.P p.W p.rsp t ∧ p.d + p.u.wx ≤ p.W ∧ E p t

theorem gPow_u1pc (M : Mont) {sl : Nat} {E : UPubPc → State → Prop}
    (hE : ∀ p s t, E p s → Frm p.u.B (gRanges p.u.w) s.mem t.mem → t.rd = s.rd → t.wr = s.wr → E p t)
    {p : UPubPc} {s : State} (h : UPrePc sl E p s) :
    WP isa (seqs (Crt.gPow M.mm sl)) s (U1Pc sl E p) := by
  obtain ⟨hu, ⟨hpre, hsp⟩, hdW, he⟩ := h
  obtain ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, hsl, hsl1, hsl2, hslv, hws, hN, hodd, hN1, hX, hX1, -⟩ := hu
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.u.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.u.wx 8 := by unfold slot hdrBytes; omega
  have hoL : p.u.o + slot p.u.wx 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (gPow_ok M (ok := False) hg (by omega) (by omega) (by omega) hN.n hN.inv hodd hN1 False.elim
    hN.r2lt hN.one hsl hslv hws.hdr.hw ((hs.sub (o := p.u.o) (n := slot p.u.wx 8) (by omega) (by omega)).ld
      (d := 8 * sW) (by unfold sW; omega)) (by omega) hwx) fun s₁ ⟨hg₁, _, _, f₁, k₁⟩ => ?_
  have f₁' : Frm p.u.B (gRanges p.u.w) s.mem s₁.mem := f₁
  have fx : Frm p.u.B (gRanges p.u.w ++ [xRange p.u.o p.u.wx]) s.mem s₁.mem :=
    Frm.mono f₁' fun r hr => List.mem_append_left _ hr
  exact ⟨⟨mx, X, hg₁, hw28, hlo, hhi, hwx2, hwx, hsl, by rw [Frm.gx_hdr fx hlo hsl hsl1 hsl2]; exact hslv,
    WsAt.of_g hws f₁' hlo (by omega), hX.of_below f₁' (fun r hr => (gRanges_le _ r hr).trans hlo) hoL, hX1⟩,
    ⟨hpre.congrK (InScr.of_frm f₁' fun r hr => (gRanges_le _ r hr).trans (by omega)) k₁ (by decide),
      (k₁.gpr (by decide)).trans hsp⟩, hdW, hE _ _ _ he f₁' k₁.2.1 k₁.2.2⟩

/-- Entering the prime's workspace: `loadPre`'s hypotheses. -/
theorem enter_lp {sl : Nat} {E QX : UPubPc → State → Prop} (hX : ∀ p t, U1 sl p.u t → E p t → QX p t)
    (hQ : ∀ a s t, QX a s → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → QX a t)
    {p : UPubPc} {s : State} (h : U1Pc sl E p s) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s fun t => LpPre Public.aY p.lp t ∧ QX p t := by
  have hq := hX p s h.1 h.2.2.2
  obtain ⟨⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1⟩, ⟨hpre, hsp⟩, hdW, -⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.u.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.u.B p.u.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  have hc : SubCtx t p.u.B p.u.Z p.u.o p.u.w p.u.wx mx := SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr)
    (by rw [hm]; exact hws) hdi hlo (hi_of_wsTab hhi)
  exact ⟨lpPre_sub hc (hpre.congrK (by rw [hm]; exact InScr.refl _ _ _) k (by decide)) hdW
    ((k.gpr (by decide)).trans hsp) hwx2 (by omega), hQ p s t hq hm k.2.1 k.2.2⟩

end CrtCTUnitPc

open CrtCTQ CrtCTUnitPc in
/-- The start of a prime's phase with `pre` is constant time, given that the
offset's code `po` is. -/
theorem unitPc_ct (M : Mont) {sl : Nat} {po : List Instr} {E QX : UPubPc → State → Prop} (hG : GPowCT M sl)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true)
    (hE : ∀ p s t, E p s → Frm p.u.B (gRanges p.u.w) s.mem t.mem → t.rd = s.rd → t.wr = s.wr → E p t)
    (hX : ∀ p t, U1 sl p.u t → E p t → QX p t)
    (hQ : ∀ a s t, QX a s → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → QX a t)
    (hpo : RelCT isa (Two fun a s => LpA Public.aY a.lp s ∧ QX a s) (.block po) (Two (LpB Public.aY))) :
    RelCT isa (Two (UPrePc sl E)) (seqs (Crt.gPow M.mm sl ++ ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++
      Crt.loadPre Public.aY po ++ ([.block [leave]] : List (Prog isa)))) fun _ _ => True := by
  rw [List.append_assoc, List.append_assoc]
  refine RelCT.seqs_append (by simp [Crt.gPow]) (by simp) (RelCT.seq (two_post (Ψ := U1Pc sl E)
    (two_map (fun p : UPubPc => gp p.u) (fun _ _ h => gPre h.1) hG) fun _ _ h => gPow_u1pc M hE h) ?_)
  refine RelCT.seqs_append (a := [.block [.mov .rdi (.mem (hdr sl))]]) (by simp) (by simp [Crt.loadPre])
    (RelCT.seq (two_piece (Ψ := fun (p : UPubPc) t => LpPre Public.aY p.lp t ∧ QX p t) [.rdi]
      (pinsRdi (fun p : UPubPc => p.u.B) fun _ _ ⟨⟨_, _, hg, _⟩, _⟩ => hg.rdi) hT fun _ _ h => enter_lp hX hQ h) ?_)
  exact loadPre_ct UPubPc.lp (by taint_decide) (by taint_decide) (fun a s t h hm k => hQ a s t h hm k.2.1 k.2.2) hpo

end VG.Proof.Bignum.X86_64
