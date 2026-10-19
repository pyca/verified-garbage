module

public import VerifiedGarbage.Proof.Dsa.X86_64.JointWindows
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointWindows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Dsa.Joint
meta import VerifiedGarbage.Proof.Dsa.Joint
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Spec.Dsa

/-! # Joint exponentiation and conversion out of Montgomery representation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def JointWinI (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (n xc g y a b v z : Nat),
    JointWinInv t₀ (off p.B p.o) p.wx minv n xc g y a b v z j s ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) n ∧ v < 256 ∧ z < 256

theorem jointWindow_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 4 ∧ JointWinI q.1 q.2 s) (Joint.window Sq.mm M.mm)
      fun _ _ => True := by
  unfold Joint.window seqs
  have sq : RelCT isa (Two fun (q : XPub × Nat) s => WinQ q.1 s Sq.bd) Sq.mm
      (Two fun (q : XPub × Nat) s => WinQ q.1 s Sq.bd) :=
    two_post (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ h => h.goodW) Sq.ct)
      fun _ _ h => winSqS_q Sq h
  -- Two squarings.
  have sq0 : RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 4 ∧ JointWinI q.1 q.2 s) Sq.mm
      (Two fun (q : XPub × Nat) s => WinQ q.1 s Sq.bd) :=
    two_post (two_map (fun q : XPub × Nat => q.1.ws)
      (fun _ _ ⟨_, _, _, _, _, _, _, _, _, _, _, hI, _⟩ => ⟨_, hI.ctx.good, Nat.le_refl _⟩)
      Sq.ct) fun q s ⟨hj, t₀, minv, n, xc, g, y, a, b, v, z, hI, hw, hw', hR, hv, hz⟩ => by
        have hp : (256 * v + z) * 4 ^ q.2 < 2 ^ 56 := by
          have : 4 ^ q.2 ≤ 4 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
          have := Nat.mul_le_mul_left (256 * v + z) this
          omega
        have tab : CTab s.mem (off q.1.B q.1.o) q.1.wx n False 0 :=
          ⟨hI.tab.tab, hI.tab.lt, fun h _ _ => False.elim h⟩
        have hnR : n ≤ 2 ^ (64 * q.1.wx) := by rw [← hI.ctx.n]; exact Nat.le_of_lt (wv_lt _ _ _ _)
        exact winSqS_q Sq ⟨minv, n, xc, _, hI.ctx, tab, Nat.lt_of_lt_of_le hI.ylt (Sq.le hnR), hI.bytes, hp, hw, hw', hR⟩
  -- The window, and `sV` up.
  have mid : RelCT isa (Two fun (q : XPub × Nat) s => WinQ q.1 s Sq.bd)
      (.block Joint.windowIndex)
      (Two fun (q : XPub × Nat) s => WinS q.1 s Sq.bd) := by
    refine two_piece [.rdi] (pins_rdi (fun q : XPub × Nat => off q.1.B q.1.o) fun _ _ h => h.rdi) (by unfold Joint.windowIndex; taint_decide)
      fun q s h => ?_
    obtain ⟨minv, X, Xc, V, hc, htab, hY, hV, hV', hw, hw', hR⟩ := h
    have hn := hc.scrT.nowrap
    refine WP.mono (joint_mid_ok hc hV (by omega_arith)) fun t ⟨hm, k⟩ => ?_
    have o1 := writeW_outside s.mem (off q.1.B q.1.o) (d := 8 * Crt.sV) (BitVec.ofNat 64 (4 * V)) (by decide)
    have o2 := writeW_outside (s.mem.writeW (off (off q.1.B q.1.o) (8 * Crt.sV)) (BitVec.ofNat 64 (4 * V)))
      (off q.1.B q.1.o) (d := 8 * Crt.sNib) (BitVec.ofNat 64 ((4 * (V / 16384 % 4) + V / 64 % 4))) (by decide)
    rw [← hm] at o2
    have f : Frm (off q.1.B q.1.o) (crtWinRanges q.1.wx) s.mem t.mem :=
      (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
    have hc' := hc.of_win f k.2.2 (k.gpr (by decide))
    have hY0 := slot_le (w := q.1.wx) (show Public.aY < 8 by decide)
    have hYe : wv t.mem (off q.1.B q.1.o) (slot q.1.wx Public.aY) q.1.wx =
        wv s.mem (off q.1.B q.1.o) (slot q.1.wx Public.aY) q.1.wx := by
      rw [o2.wv (by have := hdr_lt_slot q.1.wx Public.aY (show Crt.sNib < 32 by decide); omega_arith) (by omega_arith),
        o1.wv (by have := hdr_lt_slot q.1.wx Public.aY (show Crt.sV < 32 by decide); omega_arith) (by omega_arith)]
    exact ⟨⟨minv, X, Xc, (4 * (V / 16384 % 4) + V / 64 % 4), hc', hw, hw', (VG.Proof.Dsa.joint_index (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))).1, by
        rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
          hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact htab.tab,
        by rw [hm, word_writeW_self]⟩,
      minv, X, Xc, hc', htab.of_win f hn, hYe ▸ hY, hR⟩
  refine RelCT.seq sq0 (RelCT.seq sq (RelCT.seq mid ?_))
  refine RelCT.seq (two_post (Ψ := fun (q : XPub × Nat) s => WinT q.1 s)
    (two_map (fun q : XPub × Nat => q.1) (fun _ _ h => h.1) tabSel_ct) fun q s h => ?_) ?_
  · obtain ⟨⟨minv, X, Xc, v, hc, hw, hw', hv, ht, hN⟩, minv', X', Xc', hc₂, htab, -, -⟩ := h
    refine WP.mono (tabSel_ok hc hw hw' hv ht hN) fun t ⟨hc', hT, _, _⟩ => ⟨minv, X, Xc, hc', ?_, hw, hw'⟩
    have hX : X' = X := hc₂.n.symm.trans hc.n
    rw [hT, ← hX]; exact htab.lt _ hv
  refine RelCT.seq (two_post (Ψ := fun (q : XPub × Nat) t => t.gpr .rdi = off q.1.B q.1.o)
    (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ ⟨minv, _, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
      (M.ct (o := Public.aY) (a := Public.aY) (b := Crt.aT) (by unfold MmUse; decide)))
    fun q s ⟨minv, X, Xc, hc, hT, hw, hw'⟩ => ?_) ?_
  · exact WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Crt.aT) hc.good (Nat.le_refl _) hw (by omega_arith)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hT)) fun t ⟨hg, _⟩ => hg.rdi
  exact rdi_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => h) (by taint_decide)

theorem jointWindows_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two fun p s => 0 < 4 ∧ JointWinI p 0 s) (.loop (Joint.window Sq.mm M.mm) .ne)
      (Two fun p s => JointWinI p 4 s) :=
  two_loop (Φ := JointWinI) (fun _ => 4) (jointWindow_ct M Sq)
    fun _ _ _ hj ⟨t₀, minv, n, xc, g, y, a, b, v, z, hI, hw, hw', hR, hv, hz⟩ =>
      WP.mono (jointWinStep_ok M Sq hw hw' hR hv hz hj hI) fun _ ⟨hflag, hI'⟩ =>
        ⟨eval_ne_count hj hflag, fun _ => ⟨t₀, minv, n, xc, g, y, a, b, v, z, hI', hw, hw', hR, hv, hz⟩,
          fun h => h ▸ ⟨t₀, minv, n, xc, g, y, a, b, v, z, hI', hw, hw', hR, hv, hz⟩⟩

end VG.Proof.Dsa.X86_64
