module

public import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreCode
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain
public import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreCTR2
import VerifiedGarbage.Proof.Bignum.PrimeR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreCTR2
meta import VerifiedGarbage.Proof.Bignum.PrimeR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid

/-!
# `vg_rsa_private_precompute` on AArch64: constant time

A prime's `phase` (`phase_ct`): between its parts, each state predicate
fixes the public data (the working space, the prime's workspace and length,
`pre` and the cursor) and keeps of the secrets only what the parts after it
need.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.PrivPre

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.PrivPre
open VG.Impl.Rsa.AArch64.Crt (copyArr addMod leave)
open VG.Impl.Rsa.AArch64 (invalid)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Bignum.AArch64 (eval_nz_count)

/-- A phase's public data: the working space, the prime's workspace (its
offset `o` and words `wx`), `n`'s slot `sl` of its base, `pre` and the
cursor. -/
structure PhPub where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  wx : Nat
  sl : Nat
  op : Addr
  cur : Nat

abbrev PhPub.ws (p : PhPub) : Ws := ⟨off p.B p.o, slot p.wx 8, p.wx⟩

/-- `phase_ok`'s hypotheses. -/
def PhRel (p : PhPub) (t : State) : Prop :=
  ∃ (minv mx : BitVec 64) (X : Nat) (M : Bool), Good t p.B p.Z p.w minv ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 24 ∧ p.sl < 32 ∧
    word t.mem p.B (8 * p.sl) = off p.B p.o ∧ WsAt t.mem p.B p.o p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X ∧
    word t.mem p.B (8 * Public.sMask) = mask M ∧ word t.mem p.B (8 * Crt.sD) = off p.op p.cur ∧
    p.cur + 8 * p.wx ≤ 2 ^ 64 ∧ (∀ i < p.wx, InRegions t.wr (off p.op (p.cur + 8 * i)) 8) ∧
    (∀ x, ofs p.B x < p.Z → ofs p.op x < p.cur ∨ p.cur + 8 * p.wx ≤ ofs p.op x) ∧
    p.wx ≤ p.w ∧ p.w < 2 ^ 24 ∧
    (M = true → X % 2 = 1 ∧ wv t.mem p.B (slot p.w Public.aR2) p.w % X = 2 ^ (128 * p.w) % X)

/-- In the prime's workspace: what the parts after the entry need. -/
def PA (p : PhPub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 24 ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 24 ∧ p.o + slot p.wx 8 ≤ 2 ^ 64 ∧
    word t.mem p.B (8 * Crt.sD) = off p.op p.cur ∧ 8 * Crt.sD + 8 ≤ p.o ∧ 8 * Public.sMask + 8 ≤ p.o ∧
    p.cur + 8 * p.wx ≤ 2 ^ 64 ∧ (∀ i < p.wx, InRegions t.wr (off p.op (p.cur + 8 * i)) 8) ∧
    (∀ x, ofs p.B x < p.Z → ofs p.op x < p.cur ∨ p.cur + 8 * p.wx ≤ ofs p.op x)

theorem phEnter_ok {p : PhPub} {s : State} (h : PhRel p s) : WP isa (.block [ldh .x0 p.sl]) s (PA p) := by
  obtain ⟨minv, mx, X, M, hg, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1, -, hcur, hcb, hwr, hsep, hww, hw24, -⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega_arith
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = off p.B p.o ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc hsl, hs.ld (d := 8 * p.sl) (by omega_arith), hslv]) rfl rfl rfl)
    fun t ⟨⟨h0, hm⟩, k⟩ => ⟨mx, X, SubCtx.mk' (hs.congr k.wr) (by rw [hm]; exact hg.hdr) (by rw [hm]; exact hws) h0
      hlo (by have := tabBytes_le_wsTab p.wx; omega_arith),
      ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv, by rw [hm]; exact hX.one⟩, hX1, hwx2, hwx, hww, hw24, by omega_arith,
      by rw [hm]; exact hcur, by unfold Crt.sD sFn; omega_arith, by unfold Public.sMask sFn; omega_arith, hcb,
      by rw [k.wr]; exact hwr, hsep⟩

/-- After `r2X`: the prime's workspace, the cursor, and `pre`. -/
def PL (p : PhPub) (t : State) : Prop :=
  ∃ mx : BitVec 64, SubCtx t p.B p.Z p.o p.w p.wx mx ∧ word t.mem p.B (8 * Crt.sD) = off p.op p.cur ∧
    8 * Crt.sD + 8 ≤ p.o ∧ 8 * Public.sMask + 8 ≤ p.o ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 24 ∧ p.o + slot p.wx 8 ≤ 2 ^ 64 ∧
    p.cur + 8 * p.wx ≤ 2 ^ 64 ∧ (∀ i < p.wx, InRegions t.wr (off p.op (p.cur + 8 * i)) 8) ∧
    (∀ x, ofs p.B x < p.Z → ofs p.op x < p.cur ∨ p.cur + 8 * p.wx ≤ ofs p.op x)

/-- `r2X`, from the prime's workspace: the cursor and `pre` are kept. -/
theorem ph_r2_ct (M : Mont) : RelCT isa (Two PA) (seqs (r2X M.mm)) (Two PL) := by
  refine two_post (two_map (fun p : PhPub => (⟨p.B, p.Z, p.o, p.w, p.wx⟩ : XPub))
    (fun p s ⟨mx, X, hc, hX, hX1, hwx2, hwx, hww, hw24, _⟩ => ⟨mx, X, hc, hX, hwx2, hww, show p.w < 2 ^ 30 by omega_using [hw24], hX1, by decide⟩)
    (r2X_ct M)) fun p s h => ?_
  obtain ⟨mx, X, hc, hX, hX1, hwx2, hwx, hww, hw24, hoL, hcur, hsD, hsM, hcb, hwr, hsep⟩ := h
  refine WP.mono (r2X_ok M hc hX hwx2 hww (by omega_using [hw24]) hX1 (P := False) (fun h => h.elim))
    fun t ⟨hc', _, _, f, k⟩ => ⟨mx, hc', ?_, hsD, hsM, hwx2, hwx, hoL, hcb, by rw [k.wr]; exact hwr, hsep⟩
  have h8 := hdr_lt_slot p.wx 8 (show 0 < 32 by decide)
  rw [(f.to_x (r2Ranges_ok p.wx) hoL (List.mem_singleton_self _)).x_below hsD (by omega_using [hoL, h8])]
  exact hcur

/-- After the loads: the copy's source, destination and count. -/
def PM (p : PhPub) (t : State) : Prop :=
  PL p t ∧ t.gpr .x17 = off p.op p.cur ∧ t.gpr .x12 = BitVec.ofNat 64 p.wx ∧
    t.gpr .x16 = off p.B (p.o + slot p.wx Public.aY)

theorem ph_load_ct : RelCT isa (Two PL)
    (.block [ldh .x5 sLink, Impl.Rsa.AArch64.Crt.ldw .x17 .x5 Crt.sD, Impl.Rsa.AArch64.Crt.ldw .x15 .x5 Public.sMask,
      ldh .x12 sW, ldh .x16 (sArr Public.aY)]) (Two PM) := by
  refine RelCT.block_append (l₁ := [ldh .x5 sLink]) (RelCT.seq (two_piece (Ψ := fun p t => PL p t ∧ t.gpr .x5 = p.B)
    [.x0] (pins_x0B (Φ := PL) (fun p : PhPub => off p.B p.o) fun _ _ ⟨_, hc, _⟩ => hc.x0) (by taint_decide) ?_) ?_)
  · rintro p s ⟨mx, hc, hrest⟩
    refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B ∧ t.mem = s.mem)
      (by brun [hc.x0, hdr_enc (show sLink < 32 by decide), hc.ld' (show sLink < 32 by decide), hc.link'])
      rfl rfl rfl) fun t ⟨⟨h5, hm⟩, k⟩ => ⟨?_, h5⟩
    obtain ⟨hcur, rest⟩ := hrest
    refine ⟨mx, ⟨hc.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hc.x0, by rw [hm]; exact hc.hdr,
      by rw [hm]; exact hc.link, by rw [hm]; exact hc.nw, by rw [hm]; exact hc.narr, hc.lo, hc.hi⟩,
      by rw [hm]; exact hcur, ?_⟩
    obtain ⟨a, b, c, d, e, f, hwr, hsep⟩ := rest
    exact ⟨a, b, c, d, e, f, by rw [k.wr]; exact hwr, hsep⟩
  · refine two_piece [.x0, .x5] (pins_of (fun (p : PhPub) r => if r = .x0 then off p.B p.o else p.B)
      fun p s ⟨⟨_, hc, _⟩, h5⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.x0
        · exact h5) (by taint_decide) ?_
    rintro p s ⟨⟨mx, hc, hcur, hsD, hsM, hrest⟩, h5⟩
    refine WP.mono (WP.keep [.x12, .x15, .x16, .x17] (Q := fun t => t.gpr .x17 = off p.op p.cur ∧
        t.gpr .x12 = BitVec.ofNat 64 p.wx ∧ t.gpr .x16 = off p.B (p.o + slot p.wx Public.aY) ∧ t.mem = s.mem)
      (by brun [Impl.Rsa.AArch64.Crt.ldw, hc.x0, h5, hdr_enc (show Crt.sD < 32 by decide),
        hdr_enc (show Public.sMask < 32 by decide), hdr_enc (show sW < 32 by decide),
        hdr_enc (sArr_lt (show Public.aY < 8 by decide)), hc.ldn (show Crt.sD < 32 by decide),
        hc.ldn (show Public.sMask < 32 by decide), hc.ld' (show sW < 32 by decide),
        hc.ld' (sArr_lt (show Public.aY < 8 by decide)), hc.hw', hc.harr' (show Public.aY < 8 by decide), hcur])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h17, h12, h16, hm⟩, k⟩ => ⟨?_, h17, h12, h16⟩
    obtain ⟨a, b, c, d, hwr, hsep⟩ := hrest
    exact ⟨mx, ⟨hc.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hc.x0, by rw [hm]; exact hc.hdr,
      by rw [hm]; exact hc.link, by rw [hm]; exact hc.nw, by rw [hm]; exact hc.narr, hc.lo, hc.hi⟩,
      by rw [hm]; exact hcur, hsD, hsM, a, b, c, d, by rw [k.wr]; exact hwr, hsep⟩

/-- After the copy: the prime's base, and its link readable. -/
def PS (p : PhPub) (t : State) : Prop :=
  t.gpr .x0 = off p.B p.o ∧ word t.mem p.B (p.o + 8 * sLink) = p.B ∧
    InRegions (t.rd ++ t.wr) (off p.B (p.o + 8 * sLink)) 8

theorem ph_copyOut_ct : RelCT isa (Two PM)
    (.seq maskCopy (.block [ldh .x5 sLink, Impl.Rsa.AArch64.Crt.stw .x17 .x5 Crt.sD, leave])) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := PS) (two_taint [.x12, .x16, .x17] (pins_of (fun (p : PhPub) r =>
      if r = .x12 then BitVec.ofNat 64 p.wx else if r = .x16 then off p.B (p.o + slot p.wx Public.aY)
      else off p.op p.cur) fun p s ⟨_, h17, h12, h16⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h12
        · exact h16
        · exact h17) (by taint_decide)) ?_) ?_
  · rintro p s ⟨⟨mx, hc, -, -, -, hwx2, hwx, hoL, hcb, hwr, hsep⟩, h17, h12, h16⟩
    have hn := hc.scr.nowrap
    have hY := slot_le (w := p.wx) (show Public.aY < 8 by decide)
    have hhi := hc.hi
    have hsepC : ∀ j < p.wx, ∀ b < 8, ofs p.op (off p.B (p.o + slot p.wx Public.aY + 8 * j) + BitVec.ofNat 64 b) < p.cur ∨
        p.cur + 8 * p.wx ≤ ofs p.op (off p.B (p.o + slot p.wx Public.aY + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb =>
      hsep _ (by rw [ofs_off p.B (d := p.o + slot p.wx Public.aY + 8 * j) (i := b) (by omega_arith)]; omega_arith)
    refine WP.mono (maskCopy_ok (S := p.B) (D := p.op) (eS := p.o + slot p.wx Public.aY) (eD := p.cur) (w := p.wx)
      h16 h17 h12 (by omega_using [hwx2]) (by omega_arith) hcb (fun j hj => hc.scr.ld (by omega_arith)) hwr hsepC)
      fun t ⟨_, ho, _, _, k⟩ => ⟨(k.gpr .x0 (by decide)).trans hc.x0, ?_, by rw [k.rd, k.wr]; exact hc.ld' (by decide)⟩
    have h8 := hdr_lt_slot p.wx 8 (show sLink < 32 by decide)
    rw [word_of_pre ho hsep (by omega_arith) hn]
    exact hc.link'
  · refine RelCT.block_append (l₁ := [ldh .x5 sLink]) (l₂ := [Impl.Rsa.AArch64.Crt.stw .x17 .x5 Crt.sD, leave])
      (RelCT.seq (two_piece (Ψ := fun p t => t.gpr .x0 = off p.B p.o ∧ t.gpr .x5 = p.B) [.x0]
      (pins_x0B (Φ := PS) (fun p : PhPub => off p.B p.o) fun _ _ h => h.1) (by taint_decide) ?_)
      (two_taint [.x0, .x5] (pins_of (fun (p : PhPub) r => if r = .x0 then off p.B p.o else p.B)
        fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2) (by taint_decide)))
    rintro p s ⟨h0, hl, hr⟩
    exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B)
      (by brun [h0, hdr_enc (show sLink < 32 by decide), off_off, hr, hl]) rfl rfl rfl)
      fun t ⟨h5, k⟩ => ⟨(k.gpr .x0 (by decide)).trans h0, h5⟩

/-- A prime's `phase` is constant time, given that the taint analysis checks
its entry (`by taint_decide` for a given `sl`). -/
theorem phase_ct_of (M : Mont) {sl : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x0 sl]) hc).isSome = true) :
    RelCT isa (Two fun p s => p.sl = sl ∧ PhRel p s) (seqs (phase M.mm sl)) fun _ _ => True := by
  show RelCT isa _ (seqs ([.block [ldh .x0 sl]] ++ (r2X M.mm ++
    [.block [ldh .x5 sLink, Impl.Rsa.AArch64.Crt.ldw .x17 .x5 Crt.sD, Impl.Rsa.AArch64.Crt.ldw .x15 .x5 Public.sMask,
        ldh .x12 sW, ldh .x16 (sArr Public.aY)], maskCopy,
      .block [ldh .x5 sLink, Impl.Rsa.AArch64.Crt.stw .x17 .x5 Crt.sD, leave]]))) _
  refine RelCT.seqs_append (by simp) (by simp [r2X, Impl.Rsa.AArch64.Crt.redc]) (RelCT.seq (two_piece (Ψ := PA) [.x0]
    (pins_x0B (fun p : PhPub => p.B) fun _ _ ⟨_, _, _, _, _, hg, _⟩ => hg.x0) hT
    fun p s ⟨hsl, h⟩ => hsl ▸ phEnter_ok h) ?_)
  refine RelCT.seqs_append (by simp [r2X, Impl.Rsa.AArch64.Crt.redc]) (by simp) (RelCT.seq (ph_r2_ct M) ?_)
  simp only [seqs]
  exact RelCT.seq ph_load_ct ph_copyOut_ct

theorem phaseP_ct (M : Mont) :
    RelCT isa (Two fun p s => p.sl = sWsP ∧ PhRel p s) (seqs (phase M.mm sWsP)) fun _ _ => True :=
  phase_ct_of M (by taint_decide)

theorem phaseQ_ct (M : Mont) :
    RelCT isa (Two fun p s => p.sl = sWsQ ∧ PhRel p s) (seqs (phase M.mm sWsQ)) fun _ _ => True :=
  phase_ct_of M (by taint_decide)

/-! ## The checks, with `pre` -/

/-- `main`'s public data, and `pre`'s words. -/
structure PPub where
  m : CrtPub
  L : Nat

/-- What `pre` is: writable, apart from the working space, of `L` words. -/
def PreF (q : PPub) (σ : State) : Prop :=
  (∀ i < q.L, InRegions σ.wr (off q.m.op (8 * i)) 8) ∧ 8 * q.L ≤ 2 ^ 64 ∧
    (∀ x, ofs q.m.B x < q.m.Z → 8 * q.L ≤ ofs q.m.op x) ∧
    q.L = 2 * q.m.w + wsWords q.m.pl + wsWords q.m.ql

/-- A `Stage`, with `pre`. -/
def PStage (R : StageRel) (q : PPub) (t : State) : Prop :=
  ∃ (σ : State) (xb pb qb dpb dqb qib : List Byte),
    CrtPre σ q.m.B q.m.Z q.m.k q.m.op q.m.np q.m.ip q.m.pp q.m.qp q.m.dpp q.m.dqp q.m.qip q.m.pl q.m.ql q.m.nb
      xb pb qb dpb dqb qib ∧
    Spec.Rsa.modulusValid q.m.N q.m.k = true ∧ R q.m σ xb pb qb dpb dqb qib t ∧ PreF q σ

theorem pstage_step {R R' : StageRel} {c : Prog isa} (hct : RelCT isa (Two (Stage R)) c fun _ _ => True)
    (hw : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      WP isa c t (R' p σ xb pb qb dpb dqb qib)) :
    RelCT isa (Two (PStage R)) c (Two (PStage R')) :=
  two_post (two_map PPub.m (fun _ _ ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr, _⟩ =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩) hct)
    fun q t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr, hf⟩ =>
      WP.mono (hw q.m σ xb pb qb dpb dqb qib t h hv hr) fun _ h' => ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, h', hf⟩

/-- `n`'s setup, the primes' and the checks are constant time. -/
theorem front_ct (M : Mont) :
    RelCT isa (Two (PStage R0)) (seqs (Impl.Rsa.AArch64.Crt.nSetup M.mm ++ Impl.Rsa.AArch64.Crt.primesSetup ++
      Impl.Rsa.AArch64.Crt.checks)) (Two (PStage R3)) := by
  refine RelCT.seqs_append (by simp [Impl.Rsa.AArch64.Crt.nSetup]) checks_okG.ne
    (RelCT.seq (R := Two (PStage R2)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [Impl.Rsa.AArch64.Crt.nSetup]) (by simp [Impl.Rsa.AArch64.Crt.primesSetup])
      (RelCT.seq (R := Two (PStage R1)) ?_ ?_)
    · exact pstage_step (nSetup_ct M) fun p σ xb _ _ _ _ _ t h hv ht => by
        subst ht; exact WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ => ⟨minv, hr⟩
    · exact pstage_step (two_map id (fun _ _ h => stage_true h)
          ((setupS_ct _ setup_ct).mono (fun _ _ h => h) fun _ _ _ => trivial))
        fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, hr⟩ => WP.mono (setupPart_ok h hr) fun _ h' => ⟨minv, h'⟩
  · exact pstage_step (two_map id (fun _ _ h => stage_true h)
        ((checksS_ct checks_ct checks_okG).mono (fun _ _ h => h) fun _ _ _ => trivial))
      fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (checksPart_ok h hv hr checks_okG trivial)
        fun _ ⟨mp', mq', h'⟩ => ⟨minv, mp', mq', h'⟩

/-! ## `n`'s values -/

/-- What `outN` starts from: `outN_ok`'s hypotheses, `n`'s workspace public. -/
structure OPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Addr

def OF (p : OPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (N : Nat) (M : Bool), Good t p.B p.Z p.w minv ∧ slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    NVals t p.B p.w minv N ∧ word t.mem p.B (8 * Public.sMask) = mask M ∧ word t.mem p.B (8 * Public.sOut) = p.op ∧
    (∀ i < 2 * p.w, InRegions t.wr (off p.op (8 * i)) 8) ∧ (∀ x, ofs p.B x < p.Z → 16 * p.w ≤ ofs p.op x)

/-- Between `outN`'s copies: `n`'s workspace, its header readable, and the
copy's count and destination. -/
def OM (p : OPub) (t : State) : Prop :=
  ∃ minv : BitVec 64, Good t p.B p.Z p.w minv ∧ slot p.w 8 ≤ p.Z ∧ t.gpr .x12 = BitVec.ofNat 64 p.w ∧
    t.gpr .x17 = off p.op (8 * p.w)

theorem outN_ct : RelCT isa (Two OF) (seqs outN) fun _ _ => True := by
  simp only [outN, seqs]
  -- The loads, and the first copy.
  refine RelCT.seq (two_piece (Ψ := fun p t => OF p t ∧ t.gpr .x12 = BitVec.ofNat 64 p.w ∧
      t.gpr .x16 = off p.B (slot p.w Public.aN) ∧ t.gpr .x17 = p.op ∧ t.gpr .x0 = p.B) [.x0]
    (pins_x0B (fun p : OPub => p.B) fun _ _ ⟨_, _, _, hg, _⟩ => hg.x0) (by taint_decide) ?_) ?_
  · rintro p s ⟨minv, N, M, hg, hZ, hw, hw', hN, hmk, hO, hwr, hsep⟩
    refine WP.mono (WP.keep [.x12, .x15, .x16, .x17] (Q := fun u => u.gpr .x12 = BitVec.ofNat 64 p.w ∧
        u.gpr .x16 = off p.B (slot p.w Public.aN) ∧ u.gpr .x17 = p.op ∧ u.mem = s.mem)
      (by brun [hg.x0, hdr_enc (show Public.sMask < 32 by decide), hdr_enc (show sW < 32 by decide),
        hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hdr_enc (show Public.sOut < 32 by decide),
        hg.ld hZ (show Public.sMask < 32 by decide), hg.ld hZ (show sW < 32 by decide),
        hg.ld hZ (sArr_lt (show Public.aN < 8 by decide)), hg.ld hZ (show Public.sOut < 32 by decide),
        hmk, hg.hdr.hw, hg.hdr.harr Public.aN (by decide), hO])
      (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨h12, h16, h17, hm⟩, k⟩ => ⟨?_, h12, h16, h17,
        (k.gpr .x0 (by decide)).trans hg.x0⟩
    exact ⟨minv, N, M, ⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, by rw [hm]; exact hg.hdr⟩, hZ, hw,
      hw', nvals_of_words hN fun d _ _ => by rw [hm], by rw [hm]; exact hmk,
      by rw [hm]; exact hO, by rw [k.wr]; exact hwr, hsep⟩
  -- A copy: `w` words from `x16` to `x17`, and-ed with the mask.
  have pin3 : ∀ {Φ : OPub → State → Prop} (f : OPub → Addr) (g : OPub → Addr),
      (∀ p t, Φ p t → t.gpr .x12 = BitVec.ofNat 64 p.w ∧ t.gpr .x16 = f p ∧ t.gpr .x17 = g p) →
      Pins Φ [.x12, .x16, .x17] := fun f g h =>
    pins_of (fun p r => if r = .x12 then BitVec.ofNat 64 p.w else if r = .x16 then f p else g p)
      fun p s hs r hr => by
        obtain ⟨a, b, c⟩ := h p s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact a
        · exact b
        · exact c
  -- `n`'s words.
  refine RelCT.seq (two_post (Ψ := fun p t => (∃ minv, Good t p.B p.Z p.w minv) ∧ slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧
      p.w < 2 ^ 28 ∧ t.gpr .x12 = BitVec.ofNat 64 p.w ∧ t.gpr .x17 = off p.op (8 * p.w) ∧
      (∀ i < 2 * p.w, InRegions t.wr (off p.op (8 * i)) 8) ∧ (∀ x, ofs p.B x < p.Z → 16 * p.w ≤ ofs p.op x))
    (two_taint _ (pin3 (fun p => off p.B (slot p.w Public.aN)) (fun p => p.op) fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩)
      (by taint_decide)) ?_) ?_
  · rintro p s ⟨⟨minv, N, M, hg, hZ, hw, hw', hN, hmk, hO, hwr, hsep⟩, h12, h16, h17, h0⟩
    have hn := hg.scr.nowrap
    have hsN := slot_le (w := p.w) (show Public.aN < 8 by decide)
    have h17' : s.gpr .x17 = off p.op 0 := by rw [h17]; simp [off]
    have hsep0 : ∀ x, ofs p.B x < p.Z → ofs p.op x < 0 ∨ 0 + 8 * p.w ≤ ofs p.op x := fun x hx =>
      Or.inr (by have := hsep x hx; omega_using [this])
    have hsC : ∀ j < p.w, ∀ b < 8, ofs p.op (off p.B (slot p.w Public.aN + 8 * j) + BitVec.ofNat 64 b) < 0 ∨
        0 + 8 * p.w ≤ ofs p.op (off p.B (slot p.w Public.aN + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb => by
      apply hsep0
      rw [ofs_off p.B (d := slot p.w Public.aN + 8 * j) (i := b) (by omega_arith)]
      omega_arith
    refine WP.mono (maskCopy_ok (S := p.B) (D := p.op) (eS := slot p.w Public.aN) (eD := 0) (w := p.w)
      h16 h17' h12 (by omega_using [hw]) (by omega_arith) (by omega_arith) (fun j hj => hg.scr.ld (by omega_arith))
      (fun i hi => by rw [Nat.zero_add]; exact hwr i (by omega_using [hi])) hsC) fun t ⟨_, ho, _, ht17, k⟩ => ?_
    have hh : ∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi =>
      word_of_pre ho hsep0 (by have := hdr_lt_slot p.w 8 hi; omega_using [hZ, this]) hn
    exact ⟨⟨minv, hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0,
      ⟨(hh _ (by decide)).trans hg.hdr.hw, (hh _ (by decide)).trans hg.hdr.hminv,
        fun j hj => (hh _ (by unfold sArr; omega_using [hj])).trans (hg.hdr.harr j hj)⟩⟩, hZ, hw, hw',
      by rw [k.gpr .x12 (by decide), h12], by rw [ht17, Nat.zero_add], by rw [k.wr]; exact hwr, hsep⟩
  refine RelCT.seq (two_piece (Ψ := fun p t => t.gpr .x12 = BitVec.ofNat 64 p.w ∧
      t.gpr .x16 = off p.B (slot p.w Public.aR2) ∧ t.gpr .x17 = off p.op (8 * p.w) ∧ (∃ minv, Good t p.B p.Z p.w minv) ∧
      slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2 ^ 28 ∧ (∀ i < 2 * p.w, InRegions t.wr (off p.op (8 * i)) 8) ∧
      (∀ x, ofs p.B x < p.Z → 16 * p.w ≤ ofs p.op x)) [.x0]
    (pins_x0B (fun p : OPub => p.B) fun _ _ ⟨⟨_, hg⟩, _⟩ => hg.x0) (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨minv, hg⟩, hZ, hw, hw', h12, h17, hwr, hsep⟩
    refine WP.mono (WP.keep [.x16] (Q := fun u => u.gpr .x16 = off p.B (slot p.w Public.aR2) ∧ u.mem = s.mem)
      (by brun [hg.x0, hdr_enc (sArr_lt (show Public.aR2 < 8 by decide)), hg.ld hZ (sArr_lt (show Public.aR2 < 8 by decide)),
        hg.hdr.harr Public.aR2 (by decide)]) (by decide) (by decide) (by decide +kernel))
      fun u ⟨⟨h16, hm⟩, k⟩ => ⟨by rw [k.gpr .x12 (by decide), h12], h16, by rw [k.gpr .x17 (by decide), h17],
        ⟨minv, hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, by rw [hm]; exact hg.hdr⟩, hZ, hw, hw',
        by rw [k.wr]; exact hwr, hsep⟩
  -- `R² mod n`.
  refine RelCT.seq (two_post (Ψ := fun p t => t.gpr .x0 = p.B)
    (two_taint _ (pin3 (fun p => off p.B (slot p.w Public.aR2)) (fun p => off p.op (8 * p.w))
      fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) (by taint_decide)) ?_)
    (two_taint [.x0] (pins_x0B (fun p : OPub => p.B) fun _ _ h => h) (by taint_decide))
  rintro p s ⟨h12, h16, h17, ⟨minv, hg⟩, hZ, hw, hw', hwr, hsep⟩
  have hsR := slot_le (w := p.w) (show Public.aR2 < 8 by decide)
  exact WP.mono (maskCopy_ok (S := p.B) (D := p.op) (eS := slot p.w Public.aR2) (eD := 8 * p.w) (w := p.w)
    h16 h17 h12 (by omega_using [hw]) (by omega_arith) (by have := hg.scr.nowrap; omega_arith)
    (fun j hj => hg.scr.ld (by omega_arith))
    (fun i hi => by rw [show 8 * p.w + 8 * i = 8 * (p.w + i) by omega_using []]; exact hwr _ (by omega_using [hi]))
    (fun j hj b hb => Or.inr (by
      have hb' : ofs p.B (off p.B (slot p.w Public.aR2 + 8 * j) + BitVec.ofNat 64 b) < p.Z := by
        have := hg.scr.nowrap
        rw [ofs_off p.B (d := slot p.w Public.aR2 + 8 * j) (i := b) (by omega_arith)]
        omega_arith
      have := hsep _ hb'
      omega_using [this]))) fun t ⟨_, _, _, _, k⟩ => (k.gpr .x0 (by decide)).trans hg.x0

/-! ## The primes -/

abbrev PPub.pP (q : PPub) : PhPub :=
  ⟨q.m.B, q.m.Z, q.m.w, offP q.m.w, wsWords q.m.pl, sWsP, q.m.op, 16 * q.m.w⟩
abbrev PPub.pQ (q : PPub) : PhPub :=
  ⟨q.m.B, q.m.Z, q.m.w, offQ q.m.w q.m.pl, wsWords q.m.ql, sWsQ, q.m.op, 16 * q.m.w + 8 * wsWords q.m.pl⟩
abbrev PPub.oP (q : PPub) : OPub := ⟨q.m.B, q.m.Z, q.m.w, q.m.op⟩

/-- The layout's facts, all public. -/
def Lay (q : PPub) : Prop :=
  8 ≤ q.m.w ∧ q.m.w < 2 ^ 24 ∧ offQ q.m.w q.m.pl + slot (wsWords q.m.ql) 8 + wsTab (wsWords q.m.ql) ≤ q.m.Z ∧
    wsWords q.m.pl ≤ q.m.w ∧ wsWords q.m.ql ≤ q.m.w ∧ 8 * q.L ≤ 2 ^ 64 ∧
    (∀ x, ofs q.m.B x < q.m.Z → 8 * q.L ≤ ofs q.m.op x) ∧ q.L = 2 * q.m.w + wsWords q.m.pl + wsWords q.m.ql ∧
    q.m.B.toNat + q.m.Z ≤ 2 ^ 64

/-- After `p`'s phase: what `q`'s and `outN` need. -/
def QF (q : PPub) (t : State) : Prop :=
  ∃ (minv mq : BitVec 64) (X N : Nat) (M : Bool), Good t q.m.B q.m.Z q.m.w minv ∧
    word t.mem q.m.B (8 * sWsQ) = off q.m.B (offQ q.m.w q.m.pl) ∧ WsAt t.mem q.m.B (offQ q.m.w q.m.pl) (wsWords q.m.ql) mq ∧
    XVals t q.m.B (offQ q.m.w q.m.pl) (wsWords q.m.ql) mq X ∧ 1 < X ∧
    word t.mem q.m.B (8 * Public.sMask) = mask M ∧ NVals t q.m.B q.m.w minv N ∧
    word t.mem q.m.B (8 * Public.sOut) = q.m.op ∧ (∀ i < q.L, InRegions t.wr (off q.m.op (8 * i)) 8) ∧
    (M = true → X % 2 = 1 ∧ X ∣ N) ∧ Lay q

/-- The cursor, from what the checks leave. -/
theorem cursor_ok {q : PPub} {t : State} (h : PStage R3 q t) :
    WP isa (.block setCursor) t fun t₁ => PhRel q.pP t₁ ∧ QF q t₁ := by
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, hp, hv, ⟨minv, mp, mq, hr⟩, hwrσ, hL, hsep, hLe⟩ := h
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hz := hp.z
  have hpl2 := hp.pl2
  have hql2 := hp.ql2
  have hg := hr.good
  have hs := hg.scr
  have hn := hs.nowrap
  have hO : word t.mem q.m.B (8 * Public.sOut) = q.m.op := (hr.hfix _ (by decide) (by decide)).trans hp.hO
  have hwr : ∀ i < q.L, InRegions t.wr (off q.m.op (8 * i)) 8 := fun i hi => by rw [hr.keep.wr]; exact hwrσ i hi
  have hz : offQ q.m.w q.m.pl + slot (wsWords q.m.ql) 8 + wsTab (wsWords q.m.ql) ≤ q.m.Z := hz
  have hwk : q.m.w = (q.m.k + 7) / 8 := rfl
  have hw8 : 8 ≤ q.m.w := by omega_using [hk1, hwk]
  have hw24 : q.m.w < 2 ^ 24 := by omega_using [hk2, hwk]
  have hpw : wsWords q.m.pl ≤ q.m.w := wsWords_le (by omega_using [hpl2, hwk]) (by omega_using [hw8])
  have hqw : wsWords q.m.ql ≤ q.m.w := wsWords_le (by omega_using [hql2, hwk]) (by omega_using [hw8])
  -- The primes are more than 1 under the mask.
  obtain ⟨hNo, hN1, -⟩ := valid_facts hv hk1
  have hN256 : 256 ^ (q.m.k - 1) ≤ q.m.N := by
    have := hv; simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
  have hpq : q.m.mask xb pb qb qib = true → Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = q.m.N := fun h' => by
    simp only [CrtPub.mask, keyMask, Bool.and_eq_true, decide_eq_true_eq] at h'; exact h'.1.2
  have hP1 : q.m.mask xb pb qb qib = true → 1 < Spec.Rsa.os2ip pb := fun h' =>
    factor_gt_one (hpq h') hN256 (by have := os2ip_lt qb; rwa [hp.qbl] at this) hql2
  have hQ1 : q.m.mask xb pb qb qib = true → 1 < Spec.Rsa.os2ip qb := fun h' =>
    factor_gt_one (by rw [Nat.mul_comm]; exact hpq h') hN256 (by have := os2ip_lt pb; rwa [hp.pbl] at this) hpl2
  generalize hM : q.m.mask xb pb qb qib = M at *
  have hsD : 8 * Crt.sD + 8 ≤ slot q.m.w 8 := hdr_lt_slot q.m.w 8 (show Crt.sD < 32 by decide)
  have hp2 : 2 ≤ wsWords q.m.pl := by unfold wsWords; omega_using []
  have hq2 : 2 ≤ wsWords q.m.ql := by unfold wsWords; omega_using []
  have hZ8 : slot q.m.w 8 ≤ q.m.Z := by unfold offQ at hz; omega_using [hz]
  have eQ : offQ q.m.w q.m.pl = offP q.m.w + slot (wsWords q.m.pl) 8 + wsTab (wsWords q.m.pl) := rfl
  have hP8 : 256 ≤ slot (wsWords q.m.pl) 8 := by unfold slot hdrBytes; omega_using []
  have hPZ : offP q.m.w + slot (wsWords q.m.pl) 8 + wsTab (wsWords q.m.pl) + slot (wsWords q.m.ql) 8 +
      wsTab (wsWords q.m.ql) ≤ q.m.Z := by rw [← eQ]; exact hz
  have hoP : offP q.m.w = slot q.m.w 8 := rfl
  have hQ8 : 256 ≤ slot (wsWords q.m.ql) 8 := by unfold slot hdrBytes; omega_using []
  have hQlo : slot q.m.w 8 ≤ offQ q.m.w q.m.pl := by omega_using [eQ, hoP]
  refine WP.mono (WP.keep [.x4, .x17] (Q := fun u =>
      u.mem = t.mem.writeW (off q.m.B (8 * Crt.sD)) (off q.m.op (16 * q.m.w)))
    (by brun [setCursor, hg.x0, hdr_enc (show Public.sOut < 32 by decide), hdr_enc (show sW < 32 by decide),
      hdr_enc (show Crt.sD < 32 by decide), hg.ld hZ8 (show Public.sOut < 32 by decide),
      hg.ld hZ8 (show sW < 32 by decide), hs.st (d := 8 * Crt.sD) (by omega_using [hsD, hZ8]), hO, hg.hdr.hw,
      shl_ofNat (show q.m.w * 2 ^ 4 < 2 ^ 64 by omega_using [hw24]), show q.m.w * 2 ^ 4 = 16 * q.m.w by omega_using [], off])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have oT₁ : Outside q.m.B (8 * Crt.sD) 8 t.mem t₁.mem := by
    rw [hm₁]; exact writeW_outside _ _ _ (by unfold Crt.sD sFn; omega_using [])
  have hw₁ : ∀ d, 8 * Crt.sD + 8 ≤ d → d + 8 ≤ 2 ^ 64 → word t₁.mem q.m.B d = word t.mem q.m.B d :=
    fun d hd hd' => oT₁.word (Or.inr hd) hd'
  have hg₁ : Good t₁ q.m.B q.m.Z q.m.w minv := ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0, by
    rw [hm₁]; exact Hdr.store hg.hdr (by decide) (by decide) _⟩
  have hhd : ∀ i < 31, word t₁.mem q.m.B (8 * i) = word t.mem q.m.B (8 * i) := fun i hi => by
    rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by omega_using [hi]) (by unfold Crt.sD sFn; omega_using [hi])]
  have hN₁ : NVals t₁ q.m.B q.m.w minv q.m.N := nvals_of_words hr.nv fun d hd hd' =>
    hw₁ _ (by unfold Crt.sD sFn; omega_using [hd']) (by omega_arith)
  dsimp only [PPub.pP, PhRel]
  refine ⟨⟨minv, mp, if M then Spec.Rsa.os2ip pb else 3, M, hg₁, by omega_using [hoP], by rw [← eQ]; omega_using [hz], hp2, by omega_using [hw24, hpw],
    by decide, (hhd _ (by decide)).trans hr.wsP,
    hr.pws.of_words fun i hi => by rw [word_off, word_off, hw₁ _ (by omega_arith) (by omega_arith)],
    xvals_of_words hr.pxv fun d hd hd' => hw₁ _ (by omega_arith) (by omega_arith), if3_gt hP1,
    (hhd _ (by decide)).trans hr.msk, by rw [hm₁, word_writeW_self], by omega_using [hw24, hpw],
    fun i hi => by rw [k₁.wr, show 16 * q.m.w + 8 * i = 8 * (2 * q.m.w + i) by omega_using []]; exact hwr _ (by omega_using [hLe, hi]),
    fun x hx => Or.inr (by have := hsep x hx; omega_using [hL, hLe, hk1, hk2, hpl2, hql2, hwk, hw8, hw24, hpw, hqw, hp2, hq2, this]), hpw, hw24, fun hm => by
      simp only [hm, ite_true]
      exact ⟨odd_of_dvd hNo ⟨_, (hpq hm).symm⟩, r2_of_dvd ⟨_, (hpq hm).symm⟩ hN₁.r2⟩⟩,
    ⟨minv, mq, if M then Spec.Rsa.os2ip qb else 3, q.m.N, M, hg₁, (hhd _ (by decide)).trans hr.wsQ,
    hr.qws.of_words fun i hi => by rw [word_off, word_off, hw₁ _ (by omega_using [hsD, hQlo]) (by omega_using [hn, hz, hQ8, hi])],
    xvals_of_words hr.qxv fun d hd hd' => hw₁ _ (by omega_using [hsD, hQlo]) (by omega_arith), if3_gt hQ1,
    (hhd _ (by decide)).trans hr.msk, hN₁, (hhd _ (by decide)).trans hO,
    fun i hi => by rw [k₁.wr]; exact hwr i hi,
    fun hm => by
      simp only [hm, ite_true]
      have hd : Spec.Rsa.os2ip qb ∣ q.m.N := ⟨Spec.Rsa.os2ip pb, by rw [Nat.mul_comm]; exact (hpq hm).symm⟩
      exact ⟨odd_of_dvd hNo hd, hd⟩,
    hw8, hw24, hz, hpw, hqw, hL, hsep, hLe, hn⟩⟩

/-- `p`'s phase: what `q`'s and `outN` need. -/
theorem phP_ok (MM : Mont) {q : PPub} {t₁ : State} (h : PhRel q.pP t₁ ∧ QF q t₁) :
    WP isa (seqs (phase MM.mm sWsP)) t₁ fun t₂ => PhRel q.pQ t₂ ∧ OF q.oP t₂ := by
  obtain ⟨hP, minv, mq, X, N, M, hg₁, hslQ, hwsQ, hxQ, hX1, hmk₁, hN₁, hO₁, hwr₁, hQd, hw8, hw24, hz, hpw, hqw, hL,
    hsep, hLe, hn⟩ := h
  obtain ⟨_, _, _, _, hgP, hloP, hhiP, hp2, hwp24, hslP, hslvP, hwsP, hxP, hXP, hmkP, hcurP, hcbP, hwrP, hsepP,
    hwwP, hw24P, hPrP⟩ := hP
  have hq2 : 2 ≤ wsWords q.m.ql := by unfold wsWords; omega_using []
  have hsD : 8 * Crt.sD + 8 ≤ slot q.m.w 8 := hdr_lt_slot q.m.w 8 (show Crt.sD < 32 by decide)
  have eQ : offQ q.m.w q.m.pl = offP q.m.w + slot (wsWords q.m.pl) 8 + wsTab (wsWords q.m.pl) := rfl
  have hoP : offP q.m.w = slot q.m.w 8 := rfl
  have hQ8 : 256 ≤ slot (wsWords q.m.ql) 8 := by unfold slot hdrBytes; omega_using []
  have hQlo : slot q.m.w 8 ≤ offQ q.m.w q.m.pl := by rw [eQ]; omega_using [hoP]
  have hP8 : 256 ≤ slot (wsWords q.m.pl) 8 := by unfold slot hdrBytes; omega_using []
  have hS8 : 256 ≤ slot q.m.w 8 := by unfold slot hdrBytes; omega_using []
  refine WP.mono (phase_ok MM (sl := sWsP) hgP hloP hhiP hp2 hwp24 hwwP hw24P hslP hslvP hPrP hwsP hxP hXP hmkP hcurP
    hcbP hwrP hsepP)
    fun t₂ ⟨hg₂, _, _, _, hc₂, f₂, k₂⟩ => ?_
  have hsep₂ : ∀ x, ofs q.m.B x < q.m.Z → ofs q.m.op x < 16 * q.m.w ∨
      16 * q.m.w + 8 * wsWords q.m.pl ≤ ofs q.m.op x := fun x hx => Or.inr (by have := hsep x hx; omega_using [hLe, this])
  have hrs₂ : ∀ d, d + 8 ≤ q.m.Z → (d + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ d) →
      (d + 8 ≤ offP q.m.w + 8 * 17 ∨ offQ q.m.w q.m.pl ≤ d) → word t₂.mem q.m.B d = word t₁.mem q.m.B d :=
    fun d hd h1 h2 => pfrm_word f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [xRange]; rw [eQ] at h2; omega_using [hP8, h2]
      · exact h1) hd hn hsep₂
  have hZ8 : slot q.m.w 8 ≤ q.m.Z := by unfold offQ at hz; omega_using [hz]
  have hhd : ∀ i < 31, word t₂.mem q.m.B (8 * i) = word t₁.mem q.m.B (8 * i) := fun i hi =>
    hrs₂ _ (by omega_using [hz, hQ8, hi]) (Or.inl (by unfold Crt.sD sFn; omega_using [hi])) (Or.inl (by omega_using [hoP, hS8, hi]))
  have hg₂' : Good t₂ q.m.B q.m.Z q.m.w minv :=
    ⟨hg₂.scr, hg₂.x0, ⟨(hhd _ (by decide)).trans hg₁.hdr.hw, (hhd _ (by decide)).trans hg₁.hdr.hminv,
      fun j hj => (hhd _ (by unfold sArr; omega_using [hj])).trans (hg₁.hdr.harr j hj)⟩⟩
  have hN₂ : NVals t₂ q.m.B q.m.w minv N :=
    nvals_of_words hN₁ fun d hd hd' => hrs₂ d (by omega_using [hZ8, hd]) (Or.inr (by unfold Crt.sD sFn; omega_using [hd'])) (Or.inl (by omega_using [hoP, hd]))
  dsimp only [PPub.pQ, PPub.oP, PhRel, OF]
  refine ⟨⟨minv, mq, X, M, hg₂', hQlo, hz, hq2, by omega_using [hw24, hqw], by decide, (hhd _ (by decide)).trans hslQ,
    hwsQ.of_words fun i hi => by rw [word_off, word_off, hrs₂ _ (by omega_using [hz, hQ8, hi]) (Or.inr (by omega_using [hsD, hQlo])) (Or.inr (by omega_using []))],
    xvals_of_words hxQ fun d hd hd' => hrs₂ _ (by omega_using [hz, hd]) (Or.inr (by omega_using [hsD, hQlo])) (Or.inr (by omega_using [])), hX1,
    (hhd _ (by decide)).trans hmk₁, hc₂, by omega_using [hw24, hpw, hqw],
    fun i hi => by
      rw [k₂.wr, show 16 * q.m.w + 8 * wsWords q.m.pl + 8 * i = 8 * (2 * q.m.w + wsWords q.m.pl + i) by omega_using []]
      exact hwr₁ _ (by omega_using [hLe, hi]),
    fun x hx => Or.inr (by have := hsep x hx; omega_using [hLe, this]), hqw, hw24,
    fun hm => ⟨(hQd hm).1, r2_of_dvd (hQd hm).2 hN₂.r2⟩⟩,
    ⟨minv, N, M, hg₂', hZ8, by omega_using [hw8], by omega_using [hw24], hN₂,
      (hhd _ (by decide)).trans hmk₁, (hhd _ (by decide)).trans hO₁, fun i hi => by rw [k₂.wr]; exact hwr₁ i (by omega_using [hLe, hi]),
      fun x hx => by have := hsep x hx; omega_using [hLe, this]⟩⟩

/-- `q`'s phase keeps what `outN` needs. -/
theorem phQ_ok (MM : Mont) {q : PPub} {t₂ : State} (h : PhRel q.pQ t₂ ∧ OF q.oP t₂) :
    WP isa (seqs (phase MM.mm sWsQ)) t₂ (OF q.oP) := by
  obtain ⟨hP, minv, N, M, hg₂, hZ8, hw2, hw28, hN₂, hmk₂, hO₂, hwr₂, hsep₂⟩ := h
  obtain ⟨_, _, _, _, hgQ, hloQ, hhiQ, hq2, hwq24, hslQ, hslvQ, hwsQ, hxQ, hXQ, hmkQ, hcurQ, hcbQ, hwrQ, hsepQ,
    hwwQ, hw24Q, hPrQ⟩ := hP
  have hn := hg₂.scr.nowrap
  have hS8 : 256 ≤ slot q.m.w 8 := by unfold slot hdrBytes; omega_using []
  have hQ8 : 256 ≤ slot (wsWords q.m.ql) 8 := by unfold slot hdrBytes; omega_using []
  have hlo : slot q.m.w 8 ≤ offQ q.m.w q.m.pl := hloQ
  have hZ : slot q.m.w 8 ≤ q.m.Z := hZ8
  refine WP.mono (phase_ok MM (sl := sWsQ) hgQ hloQ hhiQ hq2 hwq24 hwwQ hw24Q hslQ hslvQ hPrQ hwsQ hxQ hXQ hmkQ hcurQ
    hcbQ hwrQ hsepQ)
    fun t₃ ⟨hg₃, _, _, _, _, f₃, k₃⟩ => ?_
  have hrs : ∀ d, d + 8 ≤ slot q.m.w 8 → (d + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ d) →
      word t₃.mem q.m.B d = word t₂.mem q.m.B d := fun d hd h1 => pfrm_word f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [xRange]; omega_using [hlo, hd]
    · exact h1) (show d + 8 ≤ q.m.Z by omega_using [hZ, hd]) hn hsepQ
  have hhd : ∀ i < 31, word t₃.mem q.m.B (8 * i) = word t₂.mem q.m.B (8 * i) := fun i hi =>
    hrs _ (by omega_using [hS8, hi]) (Or.inl (by unfold Crt.sD sFn; omega_using [hi]))
  exact ⟨minv, N, M, ⟨hg₃.scr, hg₃.x0, ⟨(hhd _ (by decide)).trans hg₂.hdr.hw, (hhd _ (by decide)).trans hg₂.hdr.hminv,
      fun j hj => (hhd _ (by unfold sArr; omega_using [hj])).trans (hg₂.hdr.harr j hj)⟩⟩, hZ8, hw2, hw28,
    nvals_of_words hN₂ fun d hd hd' => hrs d hd (Or.inr (by unfold Crt.sD sFn; omega_using [hd'])),
    (hhd _ (by decide)).trans hmk₂, (hhd _ (by decide)).trans hO₂, fun i hi => by rw [k₃.wr]; exact hwr₂ i hi,
    hsep₂⟩

/-- `primes` and `outN` are constant time, from what the checks leave. -/
theorem tail_ct (M : Mont) : RelCT isa (Two (PStage R3)) (seqs (primes M.mm ++ outN)) fun _ _ => True := by
  simp only [primes, List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [phase]) (RelCT.seq (two_piece
    (Ψ := fun q t => PhRel q.pP t ∧ QF q t) [.x0]
    (pins_x0B (fun q : PPub => q.m.B) fun _ _ ⟨_, _, _, _, _, _, _, _, _, ⟨_, _, _, hr⟩, _⟩ => hr.good.x0)
    (by taint_decide) fun _ _ h => cursor_ok h) ?_)
  refine RelCT.seqs_append (by simp [phase]) (by simp [phase]) (RelCT.seq (two_post
    (two_map PPub.pP (fun _ _ h => ⟨rfl, h.1⟩) (phaseP_ct M)) fun _ _ h => phP_ok M h) ?_)
  refine RelCT.seqs_append (by simp [phase]) (by simp [outN]) (RelCT.seq (two_post
    (two_map PPub.pQ (fun _ _ h => ⟨rfl, h.1⟩) (phaseQ_ct M)) fun _ _ h => phQ_ok M h) ?_)
  exact two_map PPub.oP (fun _ _ h => h) outN_ct

/-! ## The whole function -/

/-- The public data of `vg_rsa_private_precompute`: `main`'s, with `pre`'s
words, and the stack pointer. -/
structure CPub where
  q : PPub
  sp : Addr

/-- A state the contract allows, with the public data `c`. -/
def PPRel (c : CPub) (s : State) : Prop :=
  ppA.pre s ∧ s.sp = c.sp ∧ ppB s = c.q.m.B ∧ ppZ s = c.q.m.Z ∧ (s.gpr .x3).toNat = c.q.m.k ∧
    s.gpr .x0 = c.q.m.op ∧ s.gpr .x0 = c.q.m.ip ∧ s.gpr .x0 = c.q.m.qip ∧ (s.gpr .x1).toNat = c.q.L ∧
    s.gpr .x2 = c.q.m.np ∧ s.gpr .x4 = c.q.m.pp ∧ s.gpr .x4 = c.q.m.dpp ∧ s.gpr .x6 = c.q.m.qp ∧
    s.gpr .x6 = c.q.m.dqp ∧ (s.gpr .x5).toNat = c.q.m.pl ∧ (s.gpr .x7).toNat = c.q.m.ql ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = c.q.m.nb

/-- After `head`, from a state the contract allows. -/
def E4 (c : CPub) (t : State) : Prop := ∃ s, PPRel c s ∧ HeadP s t

theorem e4_x9 {c : CPub} {t : State} (h : E4 c t) :
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid c.q.m.N c.q.m.k).toNat := by
  obtain ⟨s, ⟨-, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, -, hnb⟩, hh⟩ := h
  rw [hh.x9, hnb, hk]

theorem e4_pstage {c : CPub} {t : State} (h : E4 c t) (hv : Spec.Rsa.modulusValid c.q.m.N c.q.m.k = true) :
    PStage R0 c.q t := by
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, hop, hip, hqip, hL, hnp, hpp, hdpp, hqp, hdqp, hpl, hql, hnb⟩, hh⟩ := h
  have cx := ppCtx_of hpre
  have hcp := hh.crt
  have e1 : c.q.m.ip = c.q.m.op := hip.symm.trans hop
  have e2 : c.q.m.qip = c.q.m.op := hqip.symm.trans hop
  have e3 : c.q.m.dpp = c.q.m.pp := hdpp.symm.trans hpp
  have e4 : c.q.m.dqp = c.q.m.qp := hdqp.symm.trans hqp
  rw [hnb, hB, hZ, hk, hop, hnp, hpp, hqp, hpl, hql] at hcp
  refine ⟨t, _, _, _, _, _, _, by rw [e1, e2, e3, e4]; exact hcp, hv, rfl, fun i hi => ?_, ?_, fun x hx => ?_, ?_⟩
  · rw [hh.keep.wr, ← hop]; exact cx.hpw i (by rw [hL]; exact hi)
  · rw [← hL]; have := cx.hpL; omega_using [this]
  · rw [← hL, ← hop, Nat.mul_comm]; rw [← hB, ← hZ] at hx; exact cx.hps x hx
  · rw [← hL, cx.hpre]; simp only [ppW, ppWP, ppWQ, CrtPub.w, hk, hpl, hql]

/-- `entry` but its first instruction. -/
abbrev entry1 : List Instr := entry.drop 1

/-- `mov x0, x8` and the modulus' check. -/
abbrev invBlk : List Instr := [mov .x0 .x8] ++ invalid

theorem head_eq : VG.Impl.Rsa.AArch64.PrivPre.head =
    .seq (.block (([.ldrSp .x8 0] : List Instr) ++ entry1)) (.seq zeroPre (.block invBlk)) := rfl

/-- After `entry`'s first instruction. -/
def E1 (c : CPub) (t : State) : Prop :=
  ∃ s, PPRel c s ∧ t.gpr .x8 = c.q.m.B ∧ Keep [.x8] s t ∧
    WP isa (.block entry1) t fun u => WP isa (.seq zeroPre (.block invBlk)) u (HeadP s)

/-- After `entry`. -/
def E2 (c : CPub) (t : State) : Prop :=
  ∃ s, PPRel c s ∧ t.gpr .x1 = BitVec.ofNat 64 c.q.L ∧ t.gpr .x10 = c.q.m.op ∧ t.gpr .x8 = c.q.m.B ∧
    t.gpr .x2 = c.q.m.np ∧ t.gpr .x3 = BitVec.ofNat 64 c.q.m.k ∧ WP isa (.seq zeroPre (.block invBlk)) t (HeadP s)

/-- After `pre := 0`. -/
def E3 (c : CPub) (t : State) : Prop :=
  ∃ s, PPRel c s ∧ t.gpr .x8 = c.q.m.B ∧ t.gpr .x2 = c.q.m.np ∧ t.gpr .x3 = BitVec.ofNat 64 c.q.m.k ∧
    WP isa (.block invBlk) t (HeadP s)

theorem head_ct : RelCT isa (Two PPRel) VG.Impl.Rsa.AArch64.PrivPre.head (Two E4) := by
  rw [head_eq]
  refine RelCT.seq (R := Two E2) (RelCT.block_append (RelCT.seq (R := Two E1) ?_ ?_)) ?_
  · -- `ldr x8, [sp]`.
    refine two_piece [] (fun _ _ _ _ _ r hr => absurd hr (List.not_mem_nil)) (by taint_decide) fun c s hs => ?_
    have cx := ppCtx_of hs.1
    have hh : WP isa (.block ([.ldrSp .x8 0] ++ entry1)) s fun u =>
        WP isa (.seq zeroPre (.block invBlk)) u (HeadP s) := by
      have := ppHead_ok cx; rw [head_eq, WP.seq_iff] at this; exact this
    have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = ppB s := rfl
    have hB'' : s.mem.readW s.sp 64 = ppB s := by simpa using hB'
    have ha0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := cx.ha
    have ho : 0 % 8 = 0 ∧ 0 < 32768 := ⟨rfl, by decide⟩
    refine WP.mono (wp_and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = ppB s)
      (by brun [exec_ldrSp ho ha0, hB', hB'']) (by decide) (by decide) (by decide +kernel)))
      fun t ⟨hw, h8, k⟩ => ⟨s, hs, h8.trans hs.2.2.1, k, hw⟩
  · -- The rest of `entry`.
    refine two_piece [.x8] (pins_of (fun (c : CPub) _ => c.q.m.B) fun c s ⟨_, _, h8, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h8) (by taint_decide) fun c t ⟨s, hs, h8, k, hw⟩ => ?_
    have cx := ppCtx_of hs.1
    have hst : ∀ i < 32, InRegions t.wr (off c.q.m.B (8 * i)) 8 := fun i hi => by
      rw [k.wr, ← hs.2.2.1]; exact cx.hs.st (by have := cx.hZ; omega_using [hi, this])
    refine WP.mono (wp_and hw (WP.keep [.x9, .x10] (Q := fun u => u.gpr .x10 = t.gpr .x0) (by
      brun [entry1, entry, List.drop_succ_cons, List.drop_zero, Impl.Rsa.AArch64.Crt.stw, h8, hdr_enc (show Public.sOut < 32 by decide),
        hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hdr_enc (show Public.sIn < 32 by decide), hdr_enc (show sP < 32 by decide),
        hdr_enc (show sPlen < 32 by decide), hdr_enc (show sQ < 32 by decide), hdr_enc (show sQlen < 32 by decide),
        hdr_enc (show sDp < 32 by decide), hdr_enc (show sDq < 32 by decide), hdr_enc (show sQinv < 32 by decide),
        hst Public.sOut (by decide), hst Public.sN (by decide), hst Public.sK (by decide),
        hst Public.sIn (by decide), hst sP (by decide), hst sPlen (by decide), hst sQ (by decide),
        hst sQlen (by decide), hst sDp (by decide), hst sDq (by decide), hst sQinv (by decide)])
      (by decide) (by decide) (by decide +kernel))) fun u ⟨hw', h10, k'⟩ => ?_
    have kk := k.trans k'
    have hs' := hs
    obtain ⟨-, -, -, -, hk, hop, -, -, hL, hnp, -⟩ := hs'
    exact ⟨s, hs, by rw [kk.gpr .x1 (by decide), ← hL, ofNat_toNat64], by rw [h10, k.gpr .x0 (by decide), hop],
      by rw [k'.gpr .x8 (by decide), h8], by rw [kk.gpr .x2 (by decide), hnp],
      by rw [kk.gpr .x3 (by decide), ← hk, ofNat_toNat64], hw'⟩
  · have z_ct : RelCT isa (Two E2) zeroPre (Two E3) :=
      two_piece [.x1, .x10] (pins_of (Φ := E2) (fun (c : CPub) r =>
        if r = .x1 then BitVec.ofNat 64 c.q.L else c.q.m.op) fun c s ⟨_, _, h1, h10, _⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h1
          · exact h10) (by taint_decide) fun c t ⟨s, hs, h1, h10, h8, h2, h3, hw⟩ => by
        rw [WP.seq_iff] at hw
        exact WP.mono (WP.keep [.x1, .x10] hw (by decide) (by decide) (by decide +kernel)) fun u ⟨hw', k⟩ =>
          ⟨s, hs, by rw [k.gpr .x8 (by decide), h8], by rw [k.gpr .x2 (by decide), h2],
            by rw [k.gpr .x3 (by decide), h3], hw'⟩
    have i_ct : RelCT isa (Two E3) (.block invBlk) (Two E4) :=
      two_piece [.x8, .x2, .x3] (pins_of (Φ := E3) (fun (c : CPub) r =>
        if r = .x8 then c.q.m.B else if r = .x2 then c.q.m.np else BitVec.ofNat 64 c.q.m.k)
        fun c s ⟨_, _, h8, h2, h3, _⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h8
          · exact h2
          · exact h3) (by taint_decide) fun c t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun u h => ⟨s, hs, h⟩
    exact RelCT.seq z_ct i_ct

/-- `vg_rsa_private_precompute` leaks the same in runs that agree on the
public data. -/
theorem ppCode_ct (M : Mont) : RelCT isa (Two PPRel) (code M.mm) fun _ _ => True := by
  unfold code
  refine RelCT.seq head_ct (two_ite (fun c s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, e4_x9 h₁, e4_x9 h₂]) ?_ ?_)
  · exact two_taint [] (fun _ _ _ _ _ r hr => absurd hr (List.not_mem_nil)) (by taint_decide)
  · simp only [main]
    rw [show Impl.Rsa.AArch64.Crt.nSetup M.mm ++ Impl.Rsa.AArch64.Crt.primesSetup ++ Impl.Rsa.AArch64.Crt.checks ++
        primes M.mm ++ outN = (Impl.Rsa.AArch64.Crt.nSetup M.mm ++ Impl.Rsa.AArch64.Crt.primesSetup ++
        Impl.Rsa.AArch64.Crt.checks) ++ (primes M.mm ++ outN) by simp only [List.append_assoc]]
    refine RelCT.seqs_append (by simp [Impl.Rsa.AArch64.Crt.nSetup]) (by simp [primes]) (RelCT.seq ?_ (tail_ct M))
    refine two_map CPub.q (fun c t ⟨h, he⟩ => e4_pstage h ?_) (front_ct M)
    change isa.eval (.zero .x .x9) t = some false at he
    rw [eval_zero, e4_x9 h] at he
    revert he
    cases Spec.Rsa.modulusValid c.q.m.N c.q.m.k <;> decide

/-- The public data of a state. -/
def ppPubOf (s : State) : CPub :=
  ⟨⟨⟨ppB s, ppZ s, (s.gpr .x3).toNat, s.gpr .x0, s.gpr .x2, s.gpr .x0, s.gpr .x4, s.gpr .x6, s.gpr .x4, s.gpr .x6,
    s.gpr .x0, (s.gpr .x5).toNat, (s.gpr .x7).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat⟩,
    (s.gpr .x1).toNat⟩, s.sp⟩

/-- `vg_rsa_private_precompute` is constant time. -/
theorem ppCode_constantTime (M : Mont) : ConstantTime isa ppA.pre ppA.pub (code M.mm) := by
  refine RelCT.constantTime ((ppCode_ct M).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨ppPubOf s₁, ?_, ?_, hp.2.1⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, hsp, a0, a1, hn⟩ := hp
    have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, hsp.symm, a0.symm, by simp only [ppZ, ppPubOf]; rw [← a1], by rw [r .x3 (by decide)]; rfl,
      r .x0 (by decide), r .x0 (by decide), r .x0 (by decide), by rw [r .x1 (by decide)]; rfl, r .x2 (by decide),
      r .x4 (by decide), r .x4 (by decide), r .x6 (by decide), r .x6 (by decide), by rw [r .x5 (by decide)]; rfl,
      by rw [r .x7 (by decide)]; rfl, hn.symm⟩

end VG.Proof.Bignum.AArch64.PrivPre
