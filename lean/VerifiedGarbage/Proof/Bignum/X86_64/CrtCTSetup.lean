module

import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.CrtKey
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.CrtKey
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import Mathlib.Tactic.TermCongr
import Mathlib.Tactic.TermCongr
import Mathlib.Tactic.Set
meta import Mathlib.Data.Int.ModEq
meta import Mathlib.Tactic.Set
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Bignum.X86_64.CrtCTQ`, which the modules that import this one used -/

section

/-!
# RSA with the CRT on x86-64: constant time of `q`'s phase

The start of a prime's phase (`unit_ct`, `unitPhase_ok`), its power
(`pow_ct`, `powPhase_ok`) and `q`'s phase (`qPhase_ct`, `qPhase_ok`), from
the claims about their parts (`GPowCT`, `RedcCT`, `ExpCT`). Between the
parts, each state predicate fixes the public data and keeps of the secrets
only what the next part's claim and the correctness of the parts after it
need.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

namespace CrtCTQ

/-- `Φ a` fixes `rdi`. -/
theorem pinsRdi {α : Type} {Φ : α → State → Prop} (f : α → Addr) (h : ∀ a s, Φ a s → s.gpr .rdi = f a) :
    Pins Φ [.rdi] :=
  pins_of (fun a _ => f a) fun a s hs r hr => by rw [List.mem_singleton.mp hr]; exact h a s hs

/-! ## The start of a prime's phase -/

/-- `gPow`'s public data. -/
def gp (p : UPub) : GPub := ⟨p.B, p.Z, p.w, p.minv, p.N, off p.B p.o, p.wx⟩

/-- The prime's workspace. -/
def xp (p : UPub) : XPub := ⟨p.B, p.Z, p.o, p.w, p.wx⟩

theorem gPre {sl : Nat} {p : UPub} {s : State} (h : UPre sl p s) : GPre sl (gp p) s := by
  obtain ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, hsl, -, -, hslv, hws, hN, hodd, hN1, -⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega_arith
  dsimp only [GPre, gp]
  exact ⟨hg, by omega_arith, by omega_arith, by omega_arith, hN.n, hN.inv, hodd, hN1, hN.r2, hN.one, hsl, hslv, hws.hdr.hw,
    (hs.sub (o := p.o) (n := slot p.wx 8) (by omega_arith) (by omega_arith)).ld (d := 8 * sW) (by unfold sW; omega_arith), by omega_arith, hwx⟩

/-- After `gPow`. -/
def U1 (sl : Nat) (p : UPub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), Good t p.B p.Z p.w p.minv ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧ word t.mem p.B (8 * sl) = off p.B p.o ∧
    WsAt t.mem p.B p.o p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X

theorem gPow_u1 (M : Mont) {sl : Nat} {p : UPub} {s : State} (h : UPre sl p s) :
    WP isa (seqs (Crt.gPow M.mm sl)) s (U1 sl p) := by
  obtain ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, hsl, hsl1, hsl2, hslv, hws, hN, hodd, hN1, hX, hX1, -⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega_arith
  have hoL : p.o + slot p.wx 8 ≤ 2 ^ 64 := by omega_arith
  refine WP.mono (gPow_ok M hg (by omega_arith) (by omega_arith) (by omega_arith) hN.n hN.inv hodd hN1 hN.r2 hN.one hsl hslv
    hws.hdr.hw ((hs.sub (o := p.o) (n := slot p.wx 8) (by omega_arith) (by omega_arith)).ld (d := 8 * sW) (by unfold sW; omega_arith))
    (by omega_arith) hwx) fun s₁ ⟨hg₁, _, _, f₁, _⟩ => ?_
  have f₁' : Frm p.B (gRanges p.w) s.mem s₁.mem := f₁
  have fx : Frm p.B (gRanges p.w ++ [xRange p.o p.wx]) s.mem s₁.mem :=
    Frm.mono f₁' fun r hr => List.mem_append_left _ hr
  exact ⟨mx, X, hg₁, hw28, hlo, hhi, hwx2, hwx, hsl, by rw [Frm.gx_hdr fx hlo hsl hsl1 hsl2]; exact hslv,
    WsAt.of_g hws f₁' hlo (by omega_arith), hX.of_below f₁' (fun r hr => (gRanges_le _ r hr).trans hlo) hoL, hX1⟩

theorem blk_rpre {sl : Nat} {p : UPub} {s : State} (h : U1 sl p s) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (RPre Public.aY (xp p)) := by
  obtain ⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.B p.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega_arith), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ⟨mx, X, SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr)
      (by rw [hm]; exact hws) hdi hlo (hi_of_wsTab hhi), ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv,
      by rw [hm]; exact hX.one⟩, hwx2, hwx, (by omega_arith : p.w < 2 ^ 30), hX1, by decide⟩

/-- A prime's workspace, its base in `rdi`, and its size. -/
def XG (p : XPub) (t : State) : Prop :=
  ∃ minv : BitVec 64, Good t (off p.B p.o) (slot p.wx 8) p.wx minv ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

/-- `Y := X_c` in a prime's workspace, and back to the modulus'. -/
theorem copyLeave_ct :
    RelCT isa (Two XG) (seqs (copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa))))
      fun _ _ => True := by
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) (RelCT.seq (two_post
    (Ψ := fun p t => t.gpr .rdi = off p.B p.o)
    (two_map (fun p : XPub => (⟨off p.B p.o, slot p.wx 8, p.wx⟩ : Ws))
      (fun _ _ ⟨minv, hg, _⟩ => ⟨minv, hg, Nat.le_refl _⟩)
      (copyArr_ct (by decide) (by decide) (by taint_decide)))
    fun p s ⟨_, hg, hwx2, hwx⟩ => WP.mono (copyArr_ok hg (Nat.le_refl _) (by omega_arith) (by omega_arith)
      (o := Public.aY) (a := aXc) (by decide) (by decide) (by decide))
      fun t ⟨_, _, k⟩ => (k.gpr (by decide)).trans hg.rdi) ?_)
  exact two_taint [.rdi] (pinsRdi (fun p : XPub => off p.B p.o) fun _ _ h => h) (by taint_decide)

/-- `redc`, `Y := X_c` and back to the modulus'. -/
theorem redcCopy_ct (M : Mont) (hR : RedcCT M Public.aY) :
    RelCT isa (Two (RPre Public.aY))
      (seqs (redc M.mm Public.aY ++ (copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa)))))
      fun _ _ => True :=
  RelCT.seqs_append (by simp [redc]) (by simp [copyArr]) (RelCT.seq (two_post (Ψ := XG) hR
    fun _ _ ⟨minv, _, hc, hX, hwx2, hwx, hw30, hX1, hj⟩ =>
      WP.mono (redc_ok M hc hX hwx2 hwx hw30 hX1 hj) fun _ ⟨hc', _⟩ => ⟨minv, hc'.good, hwx2, by omega_arith⟩)
    copyLeave_ct)

end CrtCTQ

open CrtCTQ in
/-- The start of a prime's phase is constant time. -/
theorem unit_ct (M : Mont) {sl : Nat} (hG : GPowCT M sl) (hR : RedcCT M Public.aY)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    UnitCT M sl := by
  unfold UnitCT
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp [Crt.gPow]) (by simp) (RelCT.seq (two_post (Ψ := U1 sl)
    (two_map gp (fun _ _ h => gPre h) hG) fun _ _ h => gPow_u1 M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq (two_piece
    (Ψ := fun p => RPre Public.aY (xp p)) [.rdi]
    (pinsRdi (fun p : UPub => p.B) fun _ _ ⟨_, _, hg, _⟩ => hg.rdi) hT fun _ _ h => blk_rpre h) ?_)
  exact two_map xp (fun _ _ h => h) (redcCopy_ct M hR)

namespace CrtCTQ

/-- After entering the prime's workspace. -/
def P1 (sd slen : Nat) (p : BPub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat) (eb : List Byte), SubCtx t p.x.B p.x.Z p.x.o p.x.w p.x.wx mx ∧
    p.x.o + slot p.x.wx 8 + wsTab p.x.wx ≤ p.x.Z ∧ XVals t p.x.B p.x.o p.x.wx mx X ∧ 2 ≤ p.x.wx ∧ p.x.wx ≤ p.x.w ∧ p.x.w < 2 ^ 28 ∧ 1 < X ∧ X % 2 = 1 ∧
    wv t.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx < X ∧ sd < 32 ∧ slen < 32 ∧
    word t.mem p.x.B (8 * sd) = p.ptr ∧ word t.mem p.x.B (8 * slen) = BitVec.ofNat 64 eb.length ∧
    eb.length = p.len ∧ 1 ≤ eb.length ∧ eb.length ≤ 1024 ∧ Src t p.x.B p.x.Z p.ptr eb

theorem blk_p1 {sl sd slen : Nat} {p : BPub} {s : State} (h : PwPre sl sd slen p s) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (P1 sd slen p) := by
  obtain ⟨_, mx, _, X, _, eb, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1, hXodd, -, hyl, -, hsd, hsln,
    hep, hel, hlen, hL1, hL2, he⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.x.B p.x.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega_arith), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ⟨mx, X, eb, SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr)
      (by rw [hm]; exact hws) hdi hlo (hi_of_wsTab hhi), hhi, ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv,
      by rw [hm]; exact hX.one⟩, hwx2, hwx, hw28, hX1, hXodd, by rw [hm]; exact hyl, hsd, hsln,
      by rw [hm]; exact hep, by rw [hm]; exact hel, hlen, hL1, hL2,
      he.congrK (by rw [hm]; exact InScr.refl _ _ _) k⟩

theorem redc_ePre (M : Mont) {sd slen : Nat} {p : BPub} {s : State} (h : P1 sd slen p s) :
    WP isa (seqs (redc M.mm Public.aY)) s (EPre sd slen p) := by
  obtain ⟨mx, X, eb, hc, hT, hX, hwx2, hwx, hw28, hX1, hXodd, hyl, hsd, hsln, hep, hel, hlen, hL1, hL2, he⟩ := h
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hhi := hc.hi
  have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.x.wx 8 := by unfold slot hdrBytes; omega_arith
  have ho64 : p.x.o < 2 ^ 64 := by omega_arith
  have hoL : p.x.o + slot p.x.wx 8 ≤ 2 ^ 64 := by omega_arith
  refine WP.mono (redc_ok M hc hX hwx2 hwx (by omega_arith) hX1 (j := Public.aY) (by decide))
    fun t ⟨hc₂, hX₂, hlt₂, _, f₂, k₂⟩ => ?_
  have fx₂ : Frm p.x.B [xRange p.x.o p.x.wx] s.mem t.mem :=
    f₂.to_x (redcRanges_ok _) hoL (List.mem_singleton_self _)
  have hY₂ : wv t.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx =
      wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx := by
    have rY := redcRanges_arr p.x.wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := p.x.wx) (show Public.aY < 8 by decide)
    have := hc.good.scr.nowrap
    exact f₂.wv_eq (fun r hr => by have := rY r hr; omega_arith) (by omega_arith)
  have hR : Nat.Coprime (2 ^ (64 * p.x.wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  obtain ⟨x, hx⟩ := VG.Proof.Bignum.exists_mont hR (by omega_arith)
    (wv t.mem (off p.x.B p.x.o) (slot p.x.wx aXc) p.x.wx)
  obtain ⟨y, hy⟩ := VG.Proof.Bignum.exists_mont hR (by omega_arith)
    (wv t.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx)
  exact ⟨mx, X, x, y, eb, hc₂, hwx2, hwx, by omega_arith, hX₂.n, hX₂.inv, hXodd, hlt₂, hx,
    by rw [hY₂]; exact hyl, hy,
    hsd, hsln, by rw [fx₂.x_below (by omega_arith) ho64]; exact hep, by rw [fx₂.x_below (by omega_arith) ho64]; exact hel,
    hlen, hL1, hL2, he.congrK (InScr.of_frm fx₂ fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_arith) k₂⟩

end CrtCTQ

open CrtCTQ in
/-- The power in a prime's phase is constant time. -/
theorem pow_ct (M : Mont) (E : CrtExpL M) {sl sd slen : Nat} (hR : RedcCT M Public.aY) (hE : ExpCTL E sd slen)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    PowCT M E sl sd slen := by
  unfold PowCT
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq (two_piece (Ψ := P1 sd slen) [.rdi]
    (pinsRdi (fun p : BPub => p.x.B) fun _ _ ⟨_, _, _, _, _, _, hg, _⟩ => hg.rdi) hT
    fun _ _ h => blk_p1 h) ?_)
  exact RelCT.seqs_append (by simp [redc]) (E.ne _ _) (RelCT.seq (two_post (Ψ := EPre5 sd slen)
    (two_map BPub.x (fun _ _ ⟨mx, X, _, hc, _, hX, hwx2, hwx, hw28, hX1, _⟩ =>
      ⟨mx, X, hc, hX, hwx2, hwx, by omega_arith, hX1, by decide⟩) hR)
      fun _ _ h => WP.mono (redc_ePre M h) fun _ h' => ⟨h', let ⟨_, _, _, _, hT, _⟩ := h; hT⟩) hE)

namespace CrtCTQ

/-- The start of `q`'s phase's public data. -/
def up (p : PhasePub) : UPub := ⟨p.B, p.Z, p.w, p.minv, p.N, p.o, p.wx⟩

/-- The power's public data. -/
def sp (p : PhasePub) : BPub := ⟨⟨p.B, p.Z, p.o, p.w, p.wx⟩, p.ep, p.len⟩

theorem uPre {p : PhasePub} {s : State} (h : QPre p s) : UPre sWsQ (up p) s := by
  obtain ⟨mx, X, _, _, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hodd, hN1, -, hX, hX1, hXodd, -⟩ := h
  exact ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, by decide, by decide, by decide, hslv, hws, hN, hodd, hN1,
    hX, hX1, hXodd⟩

/-- After the start of `q`'s phase. -/
def Q1 (p : PhasePub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat) (eb : List Byte), Good t p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    slot p.w 8 ≤ p.o ∧ p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧
    word t.mem p.B (8 * sWsQ) = off p.B p.o ∧ WsAt t.mem p.B p.o p.wx mx ∧ NVals t p.B p.w p.minv p.N ∧
    wv t.mem p.B (slot p.w Public.aY) p.w < p.N ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧
    wv t.mem (off p.B p.o) (slot p.wx Public.aY) p.wx < X ∧ word t.mem p.B (8 * sDq) = p.ep ∧
    word t.mem p.B (8 * sQlen) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src t p.B p.Z p.ep eb

theorem unit_q1 (M : Mont) {p : PhasePub} {s : State} (h : QPre p s) :
    WP isa (seqs (unitSteps M.mm sWsQ)) s (Q1 p) := by
  obtain ⟨mx, X, _, eb, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hodd, hN1, -, hX, hX1, hXodd, hep,
    hel, hlen, hL1, hL2, he⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hz : p.B.toNat + slot p.w 8 ≤ 2 ^ 64 := by omega_arith
  refine WP.mono (unitPhase_ok M hg hw hw28 hlo hhi hwx2 hwx (by decide) (by decide) (by decide) hslv hws hN
    hodd hN1 hX hX1 hXodd) fun t ⟨hg₁, hws₁, hX₁, hlt₁, _, hlq₁, _, _, f₁, k₁⟩ => ?_
  have hX8 : 8 * 17 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega_arith
  exact ⟨mx, X, eb, hg₁, hw, hw28, hlo, hhi, hwx2, hwx,
    by rw [Frm.gx_hdr f₁ hlo (by decide) (by decide) (by decide)]; exact hslv, hws₁,
    hN.of_frm f₁ hlo hz (by omega_arith), hlt₁, hX₁, hX1, hXodd, hlq₁,
    by rw [Frm.gx_hdr f₁ hlo (by decide) (by decide) (by decide)]; exact hep,
    by rw [Frm.gx_hdr f₁ hlo (by decide) (by decide) (by decide)]; exact hel, hlen, hL1, hL2,
    he.congrK (InScr.of_frm f₁ fun r hr => (gxRanges_le hlo r hr).trans hhi) k₁⟩

theorem mm_pwPre (M : Mont) {p : PhasePub} {s : State} (h : Q1 p s) :
    WP isa (M.mm Public.aY Public.aXm Public.aY) s (PwPre sWsQ sDq sQlen (sp p)) := by
  obtain ⟨mx, X, eb, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hlt, hX, hX1, hXodd, hyl, hep, hel, hlen,
    hL1, hL2, he⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega_arith
  have hoL : p.o + slot p.wx 8 ≤ 2 ^ 64 := by omega_arith
  refine WP.mono (mmY_ok M hg (by omega_arith) (by omega_arith) (by omega_arith) (a := Public.aXm) (by decide) (by decide)
    (by decide) hN hlt) fun t ⟨hg₂, _, _, f₂, k₂⟩ => ?_
  have f₂' : Frm p.B (gRanges p.w ++ [xRange p.o p.wx]) s.mem t.mem :=
    Frm.mono f₂ fun r hr => List.mem_append_left _ hr
  have hY₂ : wv t.mem (off p.B p.o) (slot p.wx Public.aY) p.wx =
      wv s.mem (off p.B p.o) (slot p.wx Public.aY) p.wx := by
    have := slot_le (w := p.wx) (show Public.aY < 8 by decide)
    rw [wv_off, wv_off]
    exact f₂.wv_eq (fun r hr => Or.inr (by have := gRanges_le p.w r hr; omega_arith)) (by omega_arith)
  -- `N := 1` makes the facts about the modulus trivial: the power's time does not depend on them.
  dsimp only [PwPre, sp]
  refine ⟨p.minv, mx, 1, X, 0, eb, hg₂, hw28, hlo, hhi, hwx2, hwx, by decide,
    by rw [Frm.gx_hdr f₂' hlo (by decide) (by decide) (by decide)]; exact hslv, WsAt.of_g hws f₂ hlo (by omega_arith),
    hX.of_below f₂ (fun r hr => (gRanges_le _ r hr).trans hlo) hoL, hX1, hXodd, by simp only [Nat.mod_one],
    by rw [hY₂]; exact hyl, fun hd => absurd (Nat.le_of_dvd Nat.one_pos hd) (by omega_arith), by decide, by decide,
    by rw [Frm.gx_hdr f₂' hlo (by decide) (by decide) (by decide)]; exact hep,
    by rw [Frm.gx_hdr f₂' hlo (by decide) (by decide) (by decide)]; exact hel, hlen, hL1, hL2,
    he.congrK (InScr.of_frm f₂' fun r hr => (gxRanges_le hlo r hr).trans hhi) k₂⟩

/-- After the power: in the prime's workspace. -/
def Q3 (p : PhasePub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 28

theorem pow_q3 (M : Mont) (E : CrtExpL M) {p : PhasePub} {s : State} (h : PwPre sWsQ sDq sQlen (sp p) s) :
    WP isa (seqs (powSteps M.mm E.code sWsQ sDq sQlen)) s (Q3 p) := by
  obtain ⟨_, mx, _, X, _, eb, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1, hXodd, hnY, hyl, hyc, hsd,
    hsln, hep, hel, _, hL1, hL2, he⟩ := h
  exact WP.mono (powPhase_ok M E hg hw28 hlo hhi hwx2 hwx hsl hslv hws hX hX1 hXodd hnY hyl hyc hsd hsln hep hel
    hL1 hL2 he) fun _ ⟨hc, hX', _⟩ => ⟨mx, X, hc, hX', hX1, hwx2, (by omega_arith : (sp p).x.wx < 2 ^ 28)⟩

/-- Back to `Y`'s value, and to the modulus' workspace. -/
theorem mmLeave_ct (M : Mont) :
    RelCT isa (Two Q3) (seqs [M.mm Public.aY Public.aY Public.aOne, .block [leave]]) fun _ _ => True := by
  show RelCT isa _ (.seq _ _) _
  refine RelCT.seq (two_post (Ψ := fun p t => t.gpr .rdi = off p.B p.o)
    (two_map (fun p : PhasePub => (⟨off p.B p.o, slot p.wx 8, p.wx⟩ : Ws))
      (fun _ _ ⟨mx, _, hc, _⟩ => ⟨mx, hc.good, Nat.le_refl _⟩) (M.ct (by unfold MmUse; decide)))
    fun _ _ ⟨_, _, hc, hX, hX1, hwx2, hwx⟩ => WP.mono (M.mm_ok hc.good (Nat.le_refl _) hwx2 (by omega_arith)
      (o := Public.aY) (a := Public.aY) (b := Public.aOne) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hX.inv (by rw [hX.one, hX.n]; exact hX1))
      fun _ h => h.1.rdi) ?_
  exact two_taint [.rdi] (pinsRdi (fun p : PhasePub => off p.B p.o) fun _ _ h => h) (by taint_decide)

end CrtCTQ

open CrtCTQ in
/-- `q`'s phase is constant time. -/
theorem qPhase_ct (M : Mont) (E : CrtExpL M) (hU : UnitCT M sWsQ) (hP : PowCT M E sWsQ sDq sQlen) : QPhaseCT M E := by
  unfold QPhaseCT
  rw [qPhase_eq]
  refine RelCT.seqs_append (by simp [unitSteps, Crt.gPow]) (by simp) (RelCT.seq (two_post (Ψ := Q1)
    (two_map up (fun _ _ h => uPre h) hU) fun _ _ h => unit_q1 M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [powSteps]) (RelCT.seq (two_post
    (Ψ := fun p => PwPre sWsQ sDq sQlen (sp p))
    (two_map (fun p : PhasePub => (⟨p.B, p.Z, p.w⟩ : Ws))
      (fun _ _ ⟨_, _, _, hg, _, _, hlo, hhi, _⟩ =>
        ⟨_, hg, by dsimp only; omega_arith⟩)
      (M.ct (by unfold MmUse; decide))) fun _ _ h => mm_pwPre M h) ?_)
  exact RelCT.seqs_append (by simp [powSteps]) (by simp) (RelCT.seq (two_post (Ψ := Q3)
    (two_map sp (fun _ _ h => h) hP) fun _ _ h => pow_q3 M E h) (mmLeave_ct M))

end VG.Proof.Bignum.X86_64

end

end

/-! ### `Bignum.X86_64.CrtCTSetupChk`, which only this module used -/

section

/-! ### `Bignum.X86_64.CrtCTSetupFix`, which only this module used -/

section

/-!
# RSA with the CRT on x86-64: constant time of a prime's fixes

`primeFix` in a prime's workspace (`primeFix_ct`): the mask's load reads
`n`'s header through the workspace's link, pinned by correctness; the
masking loop, the low word's fix, `-X⁻¹` and the number 1 then run from
registers that correctness pins (the array's base and `w_X`). What each
piece keeps and changes (`pf1_ok` to `pf4_ok`) gives `primeFix_frm`, what
`primeFix` changes whatever the mask and the prime.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `minv` changes only its registers, whatever `rbx`. -/
theorem minv_keep (s : State) :
    WP isa (.block minv) s fun t => Keep [.rax, .rcx, .rdx, .rsi, .r15] s t ∧ t.mem = s.mem :=
  WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi, .r15] (Q := fun t => t.mem = s.mem) (by unfold minv newton; simp only [List.cons_append, List.nil_append]; xrun) rfl)
    fun _ ⟨h, k⟩ => ⟨k, h⟩

/-! ## The pieces' correctness -/

theorem pf1_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) :
    WP isa (.block fixMask) s fun t => SubCtx t B Z o w wx minv ∧ word t.mem (off B o) (8 * sMaskX) = mask c ∧
      Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem ∧ Keep [.rax] s t := by
  have h8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  refine WP.mono (fixMask_ok hc hM) fun t ⟨hm, k⟩ => ?_
  have o₁ := writeW_outside s.mem (off B o) (d := 8 * sMaskX) (mask c) (by decide)
  rw [← hm] at o₁
  have f₁ : Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem := Frm.of_outside o₁ (by simp)
  exact ⟨hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sMaskX sFn; omega_arith) k.2.2
    (k.gpr (by decide)), by rw [hm]; exact word_writeW_self _ _ _ _, f₁, k⟩

/-- `maskArr_ok`, with the registers it leaves. -/
theorem maskArr_regs {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : j < 8) {c : Bool}
    (hm : word s.mem B (8 * sMaskX) = mask c) :
    WP isa (seqs (maskArr j)) s fun t => Outside B (slot w j) (8 * w) s.mem t.mem ∧
      t.gpr .rbx = off B (slot w j) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have sj := (slot_le (w := w) hj).trans hZ
  unfold maskArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w j) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sMaskX (by decide),
      hl (sArr j) (by unfold sArr; omega_arith), hl sW (by decide), hm, hg.hdr.harr j hj,
      hg.hdr.hw]) rfl) fun s₁ ⟨⟨h15, h12, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      MaskInv s₁ B Z (slot w j) c 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_arith) hw' (MaskInv s₁ B Z (slot w j) c) h0
    (fun i _ hi t hI => maskStep_ok hbx h15 h12 (by omega_arith) (by omega_arith) hi hI)) fun t hI => ?_
  have ho := hI.out
  rw [hm₁] at ho
  exact ⟨ho, (hI.keep.gpr (by decide)).trans hbx, (hI.keep.gpr (by decide)).trans h12,
    (k₁.trans hI.keep).mono (by decide)⟩

theorem pf2_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31)
    (hm : word s.mem (off B o) (8 * sMaskX) = mask c) :
    WP isa (seqs (maskArr Public.aN)) s fun t => SubCtx t B Z o w wx minv ∧
      t.gpr .rbx = off (off B o) (slot wx Public.aN) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  refine WP.mono (maskArr_regs hc.good (Nat.le_refl _) hw hw' (by decide) hm) fun t ⟨ho, hbx, h12, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) k.2.2 (k.gpr (by decide)),
    hbx, h12, f, k⟩

/-- A prime's workspace context after a store of its `-X⁻¹`. -/
theorem SubCtx.setMinv {s t : State} {B : Addr} {Z o w wx : Nat} {minv v : BitVec 64}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem.writeW (off (off B o) (8 * sMinv)) v)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) : SubCtx t B Z o w wx v := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hlo := h.lo
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h8x := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hh : ∀ k < 32, k ≠ sMinv → word t.mem (off B o) (8 * k) = word s.mem (off B o) (8 * k) := fun k hk hne => by
    rw [hm]; exact hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hne)
  have hb : ∀ k < 32, word t.mem B (8 * k) = word s.mem B (8 * k) := fun k hk => by
    rw [hm, off_off]
    exact (writeW_outside s.mem B (d := o + 8 * sMinv) v (by unfold sMinv; omega_arith)).word
      (Or.inl (by unfold sMinv; omega_arith)) (by omega_arith)
  exact ⟨h.scr.congr hwr, hdi.trans h.rdi, ⟨(hh _ (by decide) (by decide)).trans h.hdr.hw,
    by rw [hm]; exact word_writeW_self _ _ _ _,
    fun j hj => (hh _ (by unfold sArr; omega_arith) (by unfold sArr sMinv; omega_arith)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide) (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega_arith)).trans (h.narr j hj), hlo, hi⟩

theorem pf3_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w wx mi) (hbx : s.gpr .rbx = off (off B o) (slot wx Public.aN))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 wx) :
    WP isa (.block (fixLow ++ VG.Impl.Bignum.X86_64.minv ++ fixTail)) s fun t =>
      SubCtx t B Z o w wx (word t.mem (off B o) (8 * sMinv)) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hn := hg.scr.nowrap
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hd : slot wx Public.aN + 8 ≤ slot wx 8 := by omega_arith
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbx] (c := .block fixLow) (Q := fun t =>
      ∃ v : BitVec 64, t.mem = s.mem.writeW (off (off B o) (slot wx Public.aN)) v) (by
    unfold fixLow
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hg.scr.ld hd,
      hg.scr.st hd]
    exact ⟨_, rfl⟩) rfl) fun s₁ ⟨⟨v, hm₁⟩, k₁⟩ => ?_
  have o₁ := writeW_outside s.mem (off B o) (d := slot wx Public.aN) v (by omega_arith)
  rw [← hm₁] at o₁
  have f₁ : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem s₁.mem :=
    Frm.of_outside (o₁.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hc₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) k₁.2.2
    (k₁.gpr (by decide))
  refine WP.mono (minv_keep s₁) fun s₂ ⟨k₂, hm₂⟩ => ?_
  have hc₂ := hc₁.mem hm₂ k₂ (by decide)
  have hs₂ := hc₂.good.scr
  refine WP.mono (WP.keep [.rdx, .rcx] (c := .block fixTail) (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 0 ∧
      t.mem = s₂.mem.writeW (off (off B o) (8 * sMinv)) (s₂.gpr .r15)) (by
    unfold fixTail
    xrun [State.ea, hdr, hc₂.rdi, hdrOff, hs₂.st (d := 8 * sMinv) (by unfold sMinv; omega_arith)]) rfl)
    fun t ⟨⟨hcx, hm₃⟩, k₃⟩ => ?_
  have o₃ := writeW_outside s₂.mem (off B o) (d := 8 * sMinv) (s₂.gpr .r15) (by decide)
  rw [← hm₃] at o₃
  have f₃ : Frm (off B o) [(8 * sMinv, 8)] s₂.mem t.mem := Frm.of_outside o₃ (by simp)
  have K := (k₁.trans k₂).trans k₃
  refine ⟨hc₂.setMinv (by rw [hm₃, word_writeW_self]) k₃.2.2 (k₃.gpr (by decide)), ?_, hcx, ?_,
    K.mono (by decide)⟩
  · exact ((k₂.trans k₃).gpr (by decide)).trans ((k₁.gpr (by decide)).trans h12)
  · rw [hm₂] at f₃
    exact (f₁.append f₃).mono fun r hr => by simpa using hr

theorem pf4_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31) (h12 : s.gpr .r12 = BitVec.ofNat 64 wx)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 0) :
    WP isa (setWord Public.aOne .rcx) s fun t => SubCtx t B Z o w wx minv ∧
      Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem ∧ Keep [.rax, .r8, .r14] s t := by
  have h0 := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aOne < 8 by decide)
  refine WP.mono (setWord_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) h12 hw hw' (o := Public.aOne) (by decide)
    (ri := .rcx) (by decide) (i := 0) (by omega_arith) hcx) fun t ⟨_, ho, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) k.2.2 (k.gpr (by decide)),
    f, k⟩

/-- What `primeFix` changes, whatever the mask and the prime. -/
def pfRanges (wx : Nat) : List (Nat × Nat) :=
  [(8 * sMaskX, 8), (slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8), (slot wx Public.aOne, 8 * (wx + 2))]

theorem primeFix_frm {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) (hw : 1 ≤ wx)
    (hw' : wx < 2 ^ 31) :
    WP isa (seqs primeFix) s fun t => ∃ minv', SubCtx t B Z o w wx minv' ∧
      Frm (off B o) (pfRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  rw [primeFix_eq]
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [maskArr]) ?_
  refine WP.mono (pf1_ok hc hM) fun s₁ ⟨hc₁, hm₁, f₁, k₁⟩ => ?_
  refine wp_seqs_append (by simp [maskArr]) (by simp) ?_
  refine WP.mono (pf2_ok hc₁ hw hw' hm₁) fun s₂ ⟨hc₂, hbx₂, h12₂, f₂, k₂⟩ => ?_
  simp only [seqs]
  refine WP.seq (WP.mono (pf3_ok hc₂ hbx₂ h12₂) fun s₃ ⟨hc₃, h12₃, hcx₃, f₃, k₃⟩ => ?_)
  refine WP.mono (pf4_ok hc₃ hw hw' h12₃ hcx₃) fun t ⟨hc₄, f₄, k₄⟩ => ⟨_, hc₄, ?_,
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  exact (((f₁.append f₂).append f₃).append f₄).mono fun r hr => by
    simp only [pfRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp [h]

/-! ## Constant time -/

/-- `primeFix`'s hypotheses: a prime's workspace (some `-X⁻¹`), and the
modulus' mask (some value). -/
def PF (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    word s.mem p.B (8 * Public.sMask) = mask c ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the mask's load. -/
def PF1 (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    word s.mem (off p.B p.o) (8 * sMaskX) = mask c ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the masking. -/
def PF2 (p : XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    s.gpr .rbx = off (off p.B p.o) (slot p.wx Public.aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧ 2 ≤ p.wx ∧
    p.wx < 2 ^ 31

/-- After `-X⁻¹`. -/
def PF3 (p : XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .rcx = BitVec.ofNat 64 0

/-- `setWord`'s registers. -/
def PF4 (p : XPub) (s : State) : Prop :=
  s.gpr .r8 = off (off p.B p.o) (slot p.wx Public.aOne) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .rcx = BitVec.ofNat 64 0

theorem fixMask_ct : RelCT isa (Two PF) (.block fixMask) fun _ _ => True := by
  unfold fixMask
  refine RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun p t => PF p t ∧ t.gpr .rax = p.B) [.rdi]
      (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, _, hc, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hc.rdi) (by taint_decide) ?_)
    (two_taint [.rdi, .rax] (pins_of (fun (p : XPub) r => if r = .rdi then off p.B p.o else p.B)
      fun p s ⟨⟨_, _, hc, _⟩, hax⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.rdi
        · exact hax) (by taint_decide)))
  rintro p s ⟨minv, c, hc, hM, h1, h2⟩
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hl₁ : InRegions (s.rd ++ s.wr) (off (off p.B p.o) (8 * sLink)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot p.wx 8 (show sLink < 32 by decide); omega_arith)
  exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.B ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl₁, hc.link]) rfl)
    fun t ⟨⟨hax, hm⟩, k⟩ => ⟨⟨minv, c, hc.mem hm k (by decide), hm ▸ hM, h1, h2⟩, hax⟩

/-- `primeFix` is constant time. -/
theorem primeFix_ct : RelCT isa (Two PF) (seqs primeFix) fun _ _ => True := by
  rw [primeFix_eq]
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [maskArr]) (RelCT.seq (two_post (Ψ := PF1) fixMask_ct
    fun p s ⟨minv, c, hc, hM, h1, h2⟩ => WP.mono (pf1_ok hc hM) fun t ⟨hc', hm, _⟩ =>
      ⟨minv, c, hc', hm, h1, h2⟩) ?_)
  refine RelCT.seqs_append (by simp [maskArr]) (by simp) (RelCT.seq (two_post (Ψ := PF2)
    (two_map (fun p : XPub => (⟨off p.B p.o, slot p.wx 8, p.wx⟩ : Ws))
      (fun p s ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) (maskArr_ct (by decide) (by taint_decide)))
    fun p s ⟨minv, c, hc, hm, h1, h2⟩ => WP.mono (pf2_ok hc (by omega_arith) h2 hm) fun t ⟨hc', hbx, h12, _⟩ =>
      ⟨minv, hc', hbx, h12, h1, h2⟩) ?_)
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := PF3) [.rdi, .rbx]
    (pins_of (fun (p : XPub) r => if r = .rdi then off p.B p.o else off (off p.B p.o) (slot p.wx Public.aN))
      fun p s ⟨_, hc, hbx, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.rdi
        · exact hbx) (by taint_decide)
    fun p s ⟨_, hc, hbx, h12, _⟩ => WP.mono (pf3_ok hc hbx h12) fun t ⟨hc', h12', hcx, _⟩ =>
      ⟨_, hc', h12', hcx⟩) ?_
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := PF4) [.rdi]
    (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, hc, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.rdi) (by taint_decide) ?_)
    (two_taint [.r8, .r12, .rcx] (pins_of (fun (p : XPub) r => if r = .r8 then
      off (off p.B p.o) (slot p.wx Public.aOne) else if r = .r12 then BitVec.ofNat 64 p.wx else BitVec.ofNat 64 0)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  rintro p s ⟨_, hc, h12, hcx⟩
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hl₁ : InRegions (s.rd ++ s.wr) (off (off p.B p.o) (8 * sArr Public.aOne)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot p.wx 8 (show sArr Public.aOne < 32 by decide); omega_arith)
  exact WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off (off p.B p.o) (slot p.wx Public.aOne))
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl₁, hc.hdr.harr Public.aOne (by decide)]) rfl)
    fun t ⟨h8, k⟩ => ⟨h8, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩

end VG.Proof.Bignum.X86_64

end

end

/-!
# RSA with the CRT on x86-64: constant time of the checks' pieces

Between the pieces of `checks`, what they read from the headers (`CK`: the
modulus' header, the primes' workspaces' bases, links, sizes and arrays, and
a mask in `sMask`) is kept by their frames. Each piece is constant time from
`CK` and `rdi` (`pq_ct`, `eq_ct`, `qinv_ct`, `fixP_ct`, …).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- What the checks keep. -/
def CK (p : ChecksPub) (t : State) : Prop :=
  Scr t p.B p.Z ∧ Hdr t.mem p.B p.w p.minv ∧ word t.mem p.B (8 * sWsP) = off p.B p.op ∧
    word t.mem p.B (8 * sWsQ) = off p.B p.oq ∧ WsF t.mem p.B p.op p.wp ∧ WsF t.mem p.B p.oq p.wq ∧
    (∃ c, word t.mem p.B (8 * Public.sMask) = mask c) ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot p.wp 8 + wsTab p.wp ≤ p.oq ∧ p.oq + slot p.wq 8 + wsTab p.wq ≤ p.Z ∧ 2 ≤ p.wp ∧
    p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w

/-- `CK` with `rdi` at `f p`. -/
def CKr (f : ChecksPub → Addr) (p : ChecksPub) (t : State) : Prop := CK p t ∧ t.gpr .rdi = f p

theorem pins_ckr (f : ChecksPub → Addr) : Pins (CKr f) [.rdi] :=
  pins_of (fun p _ => f p) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2

theorem CK.bounds {p : ChecksPub} {t : State} (h : CK p t) :
    p.B.toNat + p.Z ≤ 2 ^ 64 ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.op ∧
      p.op + slot p.wp 8 + wsTab p.wp ≤ p.oq ∧ p.oq + slot p.wq 8 + wsTab p.wq ≤ p.Z ∧ 2 ≤ p.wp ∧
      p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w :=
  let ⟨hs, _, _, _, _, _, _, b⟩ := h; ⟨hs.nowrap, b⟩

/-- A change above the modulus' header, keeping the primes' workspaces. -/
theorem CK.frm {p : ChecksPub} {t t' : State} (h : CK p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, 256 ≤ r.1) (hP : WsF t'.mem p.B p.op p.wp) (hQ : WsF t'.mem p.B p.oq p.wq) {regs : List Reg}
    (k : Keep regs t t') : CK p t' := by
  obtain ⟨hs, hH, hWP, hWQ, -, -, ⟨c, hM⟩, b⟩ := h
  have hn := hs.nowrap
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  have hw : ∀ i < 32, word t'.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_arith)) (by omega_arith)
  exact ⟨hs.congr k.2.2, ⟨(hw _ (by decide)).trans hH.hw, (hw _ (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega_arith)).trans (hH.harr j hj)⟩, (hw _ (by decide)).trans hWP,
    (hw _ (by decide)).trans hWQ, hP, hQ, ⟨c, (hw _ (by decide)).trans hM⟩, b⟩

theorem CK.mem {p : ChecksPub} {t t' : State} (h : CK p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : CK p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (hm ▸ h.2.2.2.2.1) (hm ▸ h.2.2.2.2.2.1) k

/-- A change in the accumulators. -/
theorem CK.acc {p : ChecksPub} {t t' : State} (h : CK p t)
    (ho : Outside p.B (slot p.w Public.aAcc) (8 * (2 * p.w + 2)) t.mem t'.mem) {regs : List Reg}
    (k : Keep regs t t') : CK p t' := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have hA := accs_le p.w
  have := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h0 := hdr_lt_slot p.w Public.aAcc (show 31 < 32 by decide)
  have f := Frm.of_outside (rs := [(slot p.w Public.aAcc, 8 * (2 * p.w + 2))]) ho (by simp)
  have hr : ∀ r ∈ [(slot p.w Public.aAcc, 8 * (2 * p.w + 2))], r.1 + r.2 ≤ p.op := fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_arith
  exact h.frm f (fun r hr' => by rw [List.mem_singleton.mp hr']; simp only; omega_arith)
    (h.2.2.2.2.1.frm f (fun r hr' => Or.inr (hr r hr')) (by omega_arith))
    (h.2.2.2.2.2.1.frm f (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith)) k

/-- A change of the mask. -/
theorem CK.newMask {p : ChecksPub} {t t' : State} (h : CK p t) (ho : Outside p.B (8 * Public.sMask) 8 t.mem t'.mem)
    (hM : ∃ c, word t'.mem p.B (8 * Public.sMask) = mask c) {regs : List Reg} (k : Keep regs t t') : CK p t' := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  have := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have f := Frm.of_outside (rs := [(8 * Public.sMask, 8)]) ho (by simp)
  have hr : ∀ r ∈ [(8 * Public.sMask, 8)], r.1 + r.2 ≤ p.op := fun r hr => by
    rw [List.mem_singleton.mp hr]; unfold Public.sMask sFn; simp only; omega_arith
  obtain ⟨hs, hH, hWP, hWQ, hP, hQ, -, b⟩ := h
  have hw : ∀ i < 32, i ≠ Public.sMask → word t'.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi hne =>
    ho.word (by unfold Public.sMask sFn at hne ⊢; omega_arith) (by omega_arith)
  exact ⟨hs.congr k.2.2, ⟨(hw _ (by decide) (by decide)).trans hH.hw, (hw _ (by decide) (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega_arith) (by unfold sArr Public.sMask sFn; omega_arith)).trans (hH.harr j hj)⟩,
    (hw _ (by decide) (by decide)).trans hWP, (hw _ (by decide) (by decide)).trans hWQ,
    hP.frm f (fun r hr' => Or.inr (hr r hr')) (by omega_arith),
    hQ.frm f (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith), hM, b⟩

theorem ChecksPre.ck {p : ChecksPub} {s : State} (h : ChecksPre p s) : CKr (·.B) p s := by
  obtain ⟨mp, mq, P, Q, QI, m0, hg, a1, a2, b1, b2, b3, c1, c2, c3, c4, hsP, hsQ, hwsP, hwsQ, -, hM, -⟩ := h
  exact ⟨⟨hg.scr, hg.hdr, hsP, hsQ, ⟨hwsP.link, hwsP.hdr.hw, hwsP.hdr.harr⟩, ⟨hwsQ.link, hwsQ.hdr.hw, hwsQ.hdr.harr⟩,
    ⟨m0, hM⟩, a1, a2, b1, b2, b3, c1, c2, c3, c4⟩, hg.rdi⟩

theorem CK.good {p : ChecksPub} {t : State} (h : CK p t) (hdi : t.gpr .rdi = p.B) : Good t p.B p.Z p.w p.minv :=
  ⟨h.1, hdi, h.2.1⟩

theorem CK.slotZ {p : ChecksPub} {t : State} (h : CK p t) : slot p.w 8 ≤ p.Z := by
  obtain ⟨-, -, h28, hlo, hop, hoq, -⟩ := h.bounds; omega_arith

/-- Into a workspace from the modulus' (`enterP`, `enterQ`), or back (`leave`). -/
theorem CK.move {p : ChecksPub} {s : State} (h : CK p s) {X : Addr} {i : Nat} {A' : Addr}
    (hdi : s.gpr .rdi = X) (hl : InRegions (s.rd ++ s.wr) (off X (8 * i)) 8) (hw : word s.mem X (8 * i) = A') :
    WP isa (.block [.mov .rdi (.mem (hdr i))]) s (CKr (fun _ => A') p) :=
  WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = A' ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl, hw]) rfl) fun t ⟨⟨hdi', hm⟩, k⟩ => ⟨h.mem hm k, hdi'⟩

theorem CK.ldB {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 :=
  h.1.ld (by have := h.slotZ; have := hdr_lt_slot p.w 8 hi; omega_arith)

theorem CK.ldP {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off (off p.B p.op) (8 * i)) 8 := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 := hdr_lt_slot p.wp 8 hi
  exact (h.1.sub (o := p.op) (n := slot p.wp 8) (by omega_arith) (by omega_arith)).ld (by omega_arith)

/-- `p`'s workspace. -/
abbrev ckP (p : ChecksPub) : Addr := off p.B p.op
/-- `q`'s workspace. -/
abbrev ckQ (p : ChecksPub) : Addr := off p.B p.oq

theorem enterP_ck {p : ChecksPub} {s : State} (h : CKr (·.B) p s) : WP isa (.block [enterP]) s (CKr ckP p) :=
  h.1.move (X := p.B) (i := sWsP) h.2 (h.1.ldB (by decide)) h.1.2.2.1

theorem enterQ_ck {p : ChecksPub} {s : State} (h : CKr (·.B) p s) : WP isa (.block [enterQ]) s (CKr ckQ p) :=
  h.1.move (X := p.B) (i := sWsQ) h.2 (h.1.ldB (by decide)) h.1.2.2.2.1

theorem leaveP_ck {p : ChecksPub} {s : State} (h : CKr ckP p s) : WP isa (.block [leave]) s (CKr (·.B) p) :=
  h.1.move (X := ckP p) (i := sLink) h.2 (h.1.ldP (by decide)) h.1.2.2.2.2.1.1

/-! ## `p q` -/

theorem CKr.rows {p : ChecksPub} {s : State} (h : CKr (·.B) p s) :
    RowsPre Public.aN ⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ s := by
  obtain ⟨⟨hs, hH, hWP, hWQ, hP, hQ, -, -, -, hlo, hop, hoq, -⟩, hdi⟩ := h
  exact ⟨hs, hdi, hH.harr _ (by decide), hWP, hWQ, hP.2.1, hQ.2.1, (hP.2.2 _ (by decide)).trans (off_off _ _ _),
    (hQ.2.2 _ (by decide)).trans (off_off _ _ _), by decide, hlo, by dsimp only; omega_arith, by dsimp only; omega_arith⟩

theorem pq_ct : RelCT isa (Two (CKr (·.B))) (seqs pqProduct) (Two (CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · rw [pqProduct_eq]
    refine RelCT.seqs_append (by simp [zeroAccs]) (by simp) (RelCT.seq (two_post (Ψ := CKr (·.B))
      (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun p s h => ⟨p.minv, h.1.good h.2, h.1.slotZ⟩)
        zeroAccs_ct) fun p s h => ?_) ?_)
    · obtain ⟨hn, -, h28, -⟩ := h.1.bounds
      exact WP.mono (zeroAccs_ok (h.1.good h.2) h.1.slotZ (by omega_arith)) fun t ⟨_, ho, k⟩ =>
        ⟨h.1.acc ho k, (k.gpr (by decide)).trans h.2⟩
    · exact two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ : RowsPub))
        (fun p s h => h.rows) (rows_ct (by taint_decide))
  · obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, a3, a4⟩ := h.1.bounds
    have hR := h.rows
    exact WP.mono (pqProduct_ok (h.1.good h.2) (by omega_arith) hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2.1
      hR.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.2.1 hlo hop hoq (show 1 ≤ p.wp by omega_arith) a2 (show 1 ≤ p.wq by omega_arith) a4)
      fun t ⟨_, ho, k⟩ => ⟨h.1.acc ho k, (k.gpr (by decide)).trans h.2⟩

/-! ## `p q = n` -/

/-- `eqCheck`'s registers. -/
def EQ1 (p : ChecksPub) (t : State) : Prop :=
  t.gpr .rdi = p.B ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rbx = off p.B (slot p.w Public.aAcc) ∧
    t.gpr .r10 = off p.B (slot p.w Public.aN)

theorem eq_ct : RelCT isa (Two (CKr (·.B))) (seqs eqCheck) (Two (CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · unfold eqCheck
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := EQ1) [.rdi] (pins_ckr _) (by taint_decide) fun p s h => ?_)
      (two_taint [.rdi, .r12, .rbx, .r10] (pins_of (fun (p : ChecksPub) r => if r = .rdi then p.B else
        if r = .r12 then BitVec.ofNat 64 p.w else if r = .rbx then off p.B (slot p.w Public.aAcc) else
        off p.B (slot p.w Public.aN)) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2) (by taint_decide))
    obtain ⟨hk, hdi⟩ := h
    have hH := hk.2.1
    exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = off p.B (slot p.w Public.aAcc) ∧ t.gpr .r10 = off p.B (slot p.w Public.aN))
      (by xrun [State.ea, hdr, hdi, hdrOff, hk.ldB (i := sW) (by decide), hk.ldB (i := sArr Public.aAcc) (by decide),
        hk.ldB (i := sArr Public.aN) (by decide), hH.hw, hH.harr Public.aAcc (by decide),
        hH.harr Public.aN (by decide)]) rfl)
      fun t ⟨h', k⟩ => ⟨(k.gpr (by decide)).trans hdi, h'⟩
  · obtain ⟨hn, a1, a2, -⟩ := h.1.bounds
    obtain ⟨c, hM⟩ := h.1.2.2.2.2.2.2.1
    exact WP.mono (eqCheck_ok (h.1.good h.2) h.1.slotZ (by omega_arith) (by omega_arith)) fun t ⟨hM', ho, k⟩ =>
      ⟨h.1.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr (by decide)).trans h.2⟩

/-! ## `qInv < p` -/

/-- `qinvCheck`'s registers. -/
def QI1 (p : ChecksPub) (t : State) : Prop :=
  CKr ckP p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.wp ∧ t.gpr .rbx = off (ckP p) (slot p.wp aChunk) ∧
    t.gpr .r10 = off (ckP p) (slot p.wp Public.aN) ∧ t.gpr .rbp = mask false

theorem qinv_ct : RelCT isa (Two (CKr ckP)) (seqs qinvCheck) (Two (CKr ckP)) := by
  refine two_post ?_ fun p s h => ?_
  · unfold qinvCheck
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := QI1) [.rdi] (pins_ckr _) (by taint_decide) fun p s h => ?_)
      (RelCT.seq (two_post (Ψ := CKr ckP) (two_taint [.r12, .rbx, .r10] (pins_of (fun (p : ChecksPub) r =>
        if r = .r12 then BitVec.ofNat 64 p.wp else if r = .rbx then off (ckP p) (slot p.wp aChunk) else
        off (ckP p) (slot p.wp Public.aN)) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2.1) (by taint_decide)) fun p s h => ?_)
      (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr)) (RelCT.seq
        (two_piece (Ψ := fun p t => t.gpr .rax = p.B) [.rdi] (pins_ckr _) (by taint_decide) fun p s h => ?_)
        (two_taint [.rax] (pins_of (fun p _ => p.B) fun p s h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)))))
    · obtain ⟨hk, hdi⟩ := h
      have hF := hk.2.2.2.2.1
      exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.wp ∧
          t.gpr .rbx = off (ckP p) (slot p.wp aChunk) ∧ t.gpr .r10 = off (ckP p) (slot p.wp Public.aN) ∧
          t.gpr .rbp = mask false ∧ t.mem = s.mem)
        (by xrun [State.ea, hdr, hdi, hdrOff, hk.ldP (i := sW) (by decide), hk.ldP (i := sArr aChunk) (by decide),
          hk.ldP (i := sArr Public.aN) (by decide), hF.2.1, hF.2.2 aChunk (by decide),
          hF.2.2 Public.aN (by decide)]) rfl)
        fun t ⟨⟨a, b, c, d, hm⟩, k⟩ => ⟨⟨hk.mem hm k, (k.gpr (by decide)).trans hdi⟩, a, b, c, d⟩
    · obtain ⟨⟨hk, hdi⟩, h12, hbx, h10, hbp⟩ := h
      obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
      have := slot_le (w := p.wp) (show aChunk < 8 by decide)
      have := slot_le (w := p.wp) (show Public.aN < 8 by decide)
      exact WP.mono (cmpLoop_ok (hk.1.sub (o := p.op) (n := slot p.wp 8) (by omega_arith)
        (by unfold slot hdrBytes; omega_arith)) hbx h10 h12 hbp (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
        fun t ⟨_, hm, k⟩ => ⟨hk.mem hm k, (k.gpr (by decide)).trans hdi⟩
    · obtain ⟨hk, hdi⟩ := h
      exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.B)
        (by xrun [State.ea, hdr, hdi, hdrOff, hk.ldP (i := sLink) (by decide), hk.2.2.2.2.1.1]) rfl)
        fun t h => h.1
  · obtain ⟨hk, hdi⟩ := h
    obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
    obtain ⟨c, hM⟩ := hk.2.2.2.2.2.2.1
    have hF := hk.2.2.2.2.1
    exact WP.mono (qinvCheck_ok hk.1 hdi (hdr_any hF.2.1 hF.2.2) (by omega_arith)
      (by unfold Public.sMask sFn; unfold slot hdrBytes at hlo; omega_arith) (by omega_arith) (by omega_arith) hF.1)
      fun t ⟨hM', ho, k⟩ => ⟨hk.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr (by decide)).trans hdi⟩

/-! ## The fixes -/

theorem pfRanges_le (wx : Nat) : ∀ r ∈ pfRanges wx, 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  have := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have := slot_le (w := wx) (show Public.aN < 8 by decide)
  have := slot_le (w := wx) (show Public.aOne < 8 by decide)
  intro r hr
  simp only [pfRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega_arith

theorem CK.sub {p : ChecksPub} {s : State} {o wx : Nat} (hk : CK p s) (hdi : s.gpr .rdi = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ p.Z) :
    ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z o p.w wx minv ∧ word s.mem p.B (8 * Public.sMask) = mask c := by
  obtain ⟨hs, hH, -, -, -, -, ⟨c, hM⟩, -⟩ := hk
  exact ⟨_, c, ⟨hs, hdi, hdr_any hF.2.1 hF.2.2, hF.1, hH.hw, hH.harr, hlo, hi_of_wsTab hhi⟩, hM⟩

theorem CK.pf {p : ChecksPub} {s : State} {o wx : Nat} (hk : CK p s) (hdi : s.gpr .rdi = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ p.Z) (h2 : 2 ≤ wx) (hwx : wx ≤ p.w) :
    PF ⟨p.B, p.Z, o, p.w, wx⟩ s := by
  have := hk.bounds
  obtain ⟨m, c, hc, hM⟩ := hk.sub hdi hF hlo hhi
  exact ⟨m, c, hc, hM, h2, by simp only; omega_arith⟩

theorem fixP_ct : RelCT isa (Two (CKr ckP)) (seqs primeFix) (Two (CKr ckP)) := by
  refine two_post (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.op, p.w, p.wp⟩ : XPub)) (fun p s ⟨hk, hdi⟩ => by
    obtain ⟨-, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
    exact hk.pf hdi hk.2.2.2.2.1 hlo (by omega_arith) a1 a2) primeFix_ct) fun p s ⟨hk, hdi⟩ => ?_
  obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
  obtain ⟨_, c, hc, hM⟩ := hk.sub hdi hk.2.2.2.2.1 hlo (by omega_arith)
  have h8 := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h8w := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hr := pfRanges_le p.wp
  refine WP.mono (primeFix_frm hc hM (by omega_arith) (by omega_arith)) fun t ⟨_, hc', f, k⟩ => ?_
  have f' := f.rebase (by omega_arith) fun r hr' => by have := hr r hr'; omega_arith
  have hr' : ∀ r ∈ shiftRanges p.op (pfRanges p.wp), p.op + 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ p.op + slot p.wp 8 :=
    fun r hr'' => by
      obtain ⟨r₀, h₀, rfl⟩ := List.mem_map.mp hr''
      have := hr r₀ h₀; simp only; omega_arith
  exact ⟨hk.frm f' (fun r h => by have := hr' r h; omega_arith) ⟨hc'.link, hc'.hdr.hw, hc'.hdr.harr⟩
    (hk.2.2.2.2.2.1.frm f' (fun r h => Or.inr (by have := hr' r h; omega_arith)) (by omega_arith)) k, hc'.rdi⟩

theorem fixQ_ct : RelCT isa (Two (CKr ckQ)) (seqs primeFix) (Two (CKr ckQ)) := by
  refine two_post (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.oq, p.w, p.wq⟩ : XPub)) (fun p s ⟨hk, hdi⟩ => by
    obtain ⟨-, -, h28, hlo, hop, hoq, -, -, a3, a4⟩ := hk.bounds
    exact hk.pf hdi hk.2.2.2.2.2.1 (by omega_arith) hoq a3 a4) primeFix_ct) fun p s ⟨hk, hdi⟩ => ?_
  obtain ⟨hn, -, h28, hlo, hop, hoq, -, -, a3, a4⟩ := hk.bounds
  obtain ⟨_, c, hc, hM⟩ := hk.sub hdi hk.2.2.2.2.2.1 (by omega_arith) hoq
  have h8 := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h8w := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hr := pfRanges_le p.wq
  refine WP.mono (primeFix_frm hc hM (by omega_arith) (by omega_arith)) fun t ⟨_, hc', f, k⟩ => ?_
  have f' := f.rebase (by omega_arith) fun r hr' => by have := hr r hr'; omega_arith
  have hr' : ∀ r ∈ shiftRanges p.oq (pfRanges p.wq), p.oq + 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ p.oq + slot p.wq 8 :=
    fun r hr'' => by
      obtain ⟨r₀, h₀, rfl⟩ := List.mem_map.mp hr''
      have := hr r₀ h₀; simp only; omega_arith
  exact ⟨hk.frm f' (fun r h => by have := hr' r h; omega_arith)
    (hk.2.2.2.2.1.frm f' (fun r h => Or.inl (by have := hr' r h; omega_arith)) (by omega_arith))
    ⟨hc'.link, hc'.hdr.hw, hc'.hdr.harr⟩ k, hc'.rdi⟩

end VG.Proof.Bignum.X86_64

end

end

/-!
# RSA with the CRT on x86-64: constant time of the setup and the checks

The claims of `CrtCTDefs.lean` for the primes' setup: the loads
(`loadArr_ct_pN`, `loadArr_ct_pI`, `loadArr_ct_qN`, in `CrtCTSetupLoad.lean`),
`primesSetup` (`setup_ct`, in `CrtCTSetupWs.lean`), and `checks`
(`checks_ct`) and `checksP` (`checksP_ct`), from their pieces
(`CrtCTSetupChk.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem leaveEnterQ_ck : RelCT isa (Two (CKr ckP)) (.block [leave, enterQ]) (Two (CKr ckQ)) :=
  RelCT.block_append (l₁ := ([leave] : List Instr))
    (RelCT.seq (two_piece (Ψ := CKr (·.B)) [.rdi] (pins_ckr _) (by taint_decide) fun p s h => leaveP_ck h)
      (two_piece [.rdi] (pins_ckr _) (by taint_decide) fun p s h => enterQ_ck h))

theorem checks_ct : ChecksCT := by
  unfold ChecksCT checks
  simp only [List.append_assoc]
  refine two_map id (fun _ _ h => h.ck) ?_
  refine RelCT.seqs_append (by simp [pqProduct, zeroAccs]) (by simp [eqCheck]) (RelCT.seq pq_ct ?_)
  refine RelCT.seqs_append (by simp [eqCheck]) (by simp) (RelCT.seq eq_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [qinvCheck]) (RelCT.seq (two_piece [.rdi] (pins_ckr _)
    (by taint_decide) fun p s h => enterP_ck h) ?_)
  refine RelCT.seqs_append (by simp [qinvCheck]) (by simp [primeFix]) (RelCT.seq qinv_ct ?_)
  refine RelCT.seqs_append (by simp [primeFix]) (by simp) (RelCT.seq fixP_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [primeFix]) (RelCT.seq leaveEnterQ_ck ?_)
  refine RelCT.seqs_append (by simp [primeFix]) (by simp) (RelCT.seq fixQ_ct ?_)
  exact two_taint [.rdi] (pins_ckr _) (by taint_decide)

/-- The checks but `p q = n`'s. -/
theorem checksP_ct : ChecksPCT := by
  unfold ChecksPCT checksP
  simp only [List.append_assoc]
  refine two_map id (fun _ _ h => h.ck) ?_
  refine RelCT.seqs_append (by simp) (by simp [qinvCheck]) (RelCT.seq (two_piece [.rdi] (pins_ckr _)
    (by taint_decide) fun p s h => enterP_ck h) ?_)
  refine RelCT.seqs_append (by simp [qinvCheck]) (by simp [primeFix]) (RelCT.seq qinv_ct ?_)
  refine RelCT.seqs_append (by simp [primeFix]) (by simp) (RelCT.seq fixP_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [primeFix]) (RelCT.seq leaveEnterQ_ck ?_)
  refine RelCT.seqs_append (by simp [primeFix]) (by simp) (RelCT.seq fixQ_ct ?_)
  exact two_taint [.rdi] (pins_ckr _) (by taint_decide)

end VG.Proof.Bignum.X86_64
