module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.R2
public import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.R2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_precompute` on x86-64: `R_X² mod X` is constant time

`double` and `doubles` leak the same in runs with the same workspace and
count, whatever their moduli and `-m⁻¹` (`double_ctW`, `doubles_ctW`), and
so does `r2X` (`r2X_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (r2X count r2At)

/-- `DblHeadL`, which does not read `-m⁻¹`, for a workspace. -/
def DblHeadW (mo acc tmp o : Nat) (L : Ws) (t : State) : Prop := DblHeadL mo acc tmp o ⟨L.B, L.Z, L.w, 0⟩ t

/-- `double` leaks the same in runs with the same workspace. -/
theorem double_ctW {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodW) (double mo acc tmp o) fun _ _ => True :=
  RelCT.seq (two_piece (Ψ := DblHeadW mo acc tmp o) _ pins_goodW h fun L _ ⟨minv, hg⟩ =>
      dblHead_ok (L := ⟨L.B, L.Z, L.w, minv⟩) hg hmo hacc htmp ho)
    (two_taint _ (fun L => pins_dblHead mo acc tmp o ⟨L.B, L.Z, L.w, 0⟩) (by taint_decide))

/-- The public data of `doubles` in a workspace whose `-m⁻¹` is secret. -/
structure DblPubW where
  L : Ws
  c : Nat

/-- What `doubles` keeps, after `j` doublings. -/
def DblsAtW (mo acc tmp o sl : Nat) (p : DblPubW) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (O N : Nat) (minv : BitVec 64), DblsInv σ p.L.B p.L.Z p.L.w minv mo acc tmp o sl p.c O N j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ p.c < 2 ^ 31 ∧ 0 < N

theorem dblsAtW_good {mo acc tmp o sl : Nat} {p : DblPubW} {j : Nat} {t : State}
    (h : DblsAtW mo acc tmp o sl p j t) : GoodW p.L t :=
  let ⟨_, _, _, minv, hI, hZ, _⟩ := h; ⟨minv, ⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩

/-- `doubles` leaks the same in runs with the same workspace and count. -/
theorem doubles_ctW {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.rdi]) (.block [.store (hdr sl) .rcx]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.rdi]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two fun (p : DblPubW) s => ∃ minv, GoodL ⟨p.L.B, p.L.Z, p.L.w, minv⟩ s ∧ 2 ≤ p.L.w ∧
      p.L.w < 2 ^ 31 ∧ 1 ≤ p.c ∧ p.c < 2 ^ 31 ∧ s.gpr .rcx = BitVec.ofNat 64 p.c ∧
      wv s.mem p.L.B (slot p.L.w o) p.L.w < wv s.mem p.L.B (slot p.L.w mo) p.L.w)
      (doubles mo acc tmp o sl) fun _ _ => True := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ DblsAtW mo acc tmp o sl p 0 s) _
    (fun p s₁ s₂ ⟨m₁, h₁, _⟩ ⟨m₂, h₂, _⟩ => pins_goodW ⟨p.L.B, p.L.Z, p.L.w⟩ s₁ s₂ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩) h' ?_) ?_
  · rintro p s ⟨minv, hg, hw, hw', hc1, hc', hcx, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.1.scr hg.1.rdi hg.1.hdr hg.2 hmo ho hsl hsl' hcx hO)
      fun t hI => ⟨by omega, s, _, _, minv, hI, hg.2, hw, hw', hc', Nat.lt_of_le_of_lt (Nat.zero_le _) hO⟩
  refine RelCT.mono (two_loop (Φ := DblsAtW mo acc tmp o sl) (Ψ := fun _ _ => True) (fun p => p.c) ?_ ?_)
    (fun _ _ h => h) fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : DblPubW × Nat) s => GoodW q.1.L s)
      (two_map (·.1.L) (fun _ _ h => dblsAtW_good h.2) (double_ctW hmo hacc htmp ho h)) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_goodW q.1.L s₁ s₂ h₁ h₂) h'')
    rintro ⟨p, j⟩ s ⟨hj, σ, O, N, minv, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨minv, ⟨hI.scr.congr k.2.2, (k.gpr (by decide)).trans hI.rdi, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨σ, O, N, minv, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, O, N, minv, hI', hZ, hw, hw', hc', hN0⟩, fun _ => trivial⟩

/-- The public data of `r2X` and `r2At`: the working space, `n`'s words,
and the prime's workspace's offset and words. -/
structure RXPub where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  wx : Nat

/-- The prime's workspace. -/
abbrev RXPub.ws (p : RXPub) : Ws := ⟨off p.B p.o, slot p.wx 8, p.wx⟩

/-- In the prime's workspace, before `r2X`. -/
def RXPre (p : RXPub) (s : State) : Prop :=
  ∃ mx X, SubCtx s p.B p.Z p.o p.w p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 20

/-- After `r2X`'s copy of 1. -/
def RXOne (p : RXPub) (s : State) : Prop :=
  ∃ mx X, SubCtx s p.B p.Z p.o p.w p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 20 ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx = 1

theorem pins_rx {Φ : RXPub → State → Prop} (h : ∀ p s, Φ p s → s.gpr .rdi = off p.B p.o) : Pins Φ [.rdi] :=
  pins_of (fun p _ => off p.B p.o) fun p s hs r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h p s hs

/-- `r2X` leaks the same in runs with the same workspaces. -/
theorem r2X_ct : RelCT isa (Two RXPre) (seqs r2X) fun _ _ => True := by
  unfold r2X
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) (RelCT.seq (R := Two RXOne) ?_ ?_)
  · refine two_post (two_map RXPub.ws (fun p s ⟨mx, _, hc, _⟩ => ⟨mx, hc.good, Nat.le_refl _⟩)
      (copyArr_ct (o := aY) (a := aOne) (by decide) (by decide) (by taint_decide))) ?_
    rintro p s ⟨mx, X, hc, hv, hX1, hwx2, hwx⟩
    have hz : (off p.B p.o).toNat + slot p.wx 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega
    have hr := r2Ranges_ok p.wx
    exact WP.mono (copyArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) (o := aY) (a := aOne) (by decide)
      (by decide) (by decide)) fun s₁ ⟨hv₁, ho₁, k₁⟩ =>
      ⟨mx, X, hc.of_frm ((Frm.of_outside ho₁ (List.mem_singleton_self _)).widen fun r h => by
          rw [List.mem_singleton.mp h]; exact ⟨_, List.mem_cons_self, Nat.le_refl _, by simp only; omega⟩) hr
          k₁.2.2 (k₁.gpr (by decide)),
        hv.of_outside ho₁ (by decide) (by decide) (by decide) (by omega) hz, hX1, hwx2, hwx, by rw [hv₁, hv.one]⟩
  · refine RelCT.seq (two_piece (Ψ := fun (p : RXPub) t => ∃ minv, GoodL ⟨p.ws.B, p.ws.Z, p.ws.w, minv⟩ t ∧
        2 ≤ p.ws.w ∧ p.ws.w < 2 ^ 31 ∧ 1 ≤ 128 * p.wx ∧ 128 * p.wx < 2 ^ 31 ∧
        t.gpr .rcx = BitVec.ofNat 64 (128 * p.wx) ∧
        wv t.mem p.ws.B (slot p.ws.w aY) p.ws.w < wv t.mem p.ws.B (slot p.ws.w aN) p.ws.w) _
      (pins_rx fun p s ⟨_, _, hc, _⟩ => hc.rdi) (by taint_decide) ?_)
      (two_map (fun p => (⟨p.ws, 128 * p.wx⟩ : DblPubW)) (fun _ _ h => h)
        (doubles_ctW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (sl := sRem) (by decide) (by decide) (by taint_decide)
          (by taint_decide) (by taint_decide)))
    rintro p s ⟨mx, X, hc, hv, hX1, hwx2, hwx, hy⟩
    have hg := hc.good
    have hl : InRegions (s.rd ++ s.wr) (off (off p.B p.o) (8 * sW)) 8 := hg.scr.ld (by unfold sW slot hdrBytes; omega)
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (128 * p.wx) ∧ t.mem = s.mem)
      (by xrun [count, State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.hw, shl7_w (show 128 * p.wx < 2 ^ 64 by omega)]) rfl)
      fun t ⟨⟨hcx, hm⟩, k⟩ => ⟨mx, ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩,
        Nat.le_refl _⟩, hwx2, show p.wx < 2 ^ 31 by omega, by omega, by omega, hcx, by rw [hm, hy, hv.n]; exact hX1⟩

/-- In `n`'s workspace, before `r2At sl`. -/
def RAPre (sl : Nat) (p : RXPub) (s : State) : Prop :=
  ∃ minv mx X, Good s p.B p.Z p.w minv ∧ slot p.w 8 ≤ p.o ∧ p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z ∧
    word s.mem p.B (8 * sl) = off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 20 ∧ sl < 32

/-- `r2At sl` leaks the same in runs with the same workspaces, given that
the taint analysis checks its load of the prime's workspace. -/
theorem r2At_ct {sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two (RAPre sl)) (seqs (r2At sl)) fun _ _ => True := by
  unfold r2At
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two RXPre) (two_piece _
    (pins_of (fun p _ => p.B) fun p s ⟨_, _, _, hg, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.rdi) hT ?_) ?_)
  · rintro p s ⟨minv, mx, X, hg, hlo, hhi, hslv, hws, hX, hX1, hwx2, hwx, hsl⟩
    have hs := hg.scr
    refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.B p.o ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by have := hdr_lt_slot p.w 8 (show sl < 32 from hsl); omega), hslv]) rfl)
      fun t ⟨⟨hdi, hm⟩, k⟩ => ⟨mx, X, SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr) (by rw [hm]; exact hws)
        hdi hlo (hi_of_wsTab hhi), ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv, by rw [hm]; exact hX.one⟩,
        hX1, hwx2, hwx⟩
  refine RelCT.seqs_append (by simp [r2X, copyArr]) (by simp) (RelCT.seq (two_post (Ψ := fun (p : RXPub) t =>
    t.gpr .rdi = off p.B p.o) r2X_ct fun p s ⟨mx, X, hc, hv, hX1, hwx2, hwx⟩ =>
      WP.mono (r2X_ok hc hv hX1 hwx2 hwx) fun _ h => h.1.rdi) ?_)
  exact two_taint [.rdi] (pins_of (fun p _ => off p.B p.o) fun p s h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)

end VG.Proof.Bignum.X86_64.PrivPre
