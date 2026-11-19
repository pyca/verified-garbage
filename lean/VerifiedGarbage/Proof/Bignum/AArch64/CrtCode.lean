module

public import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
public import VerifiedGarbage.Impl.Rsa.AArch64.Crt
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCallees
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.AArch64.CrtMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
public import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.CrtKey
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRows
meta import VerifiedGarbage.Proof.Bignum.CrtKey
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFix
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import Mathlib.Algebra.GroupWithZero.Nat
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import Mathlib.Algebra.GroupWithZero.Nat
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs

/-! ### `Bignum.AArch64.CrtCTNSetup`, which the modules that import this one used -/

section

/-! ### `Bignum.AArch64.CrtCTSetup`, which the modules that import this one used -/

section

/-! ### `Bignum.AArch64.CrtCTSetupWs`, which this module and modules that import it used -/

section

/-!
# RSA with the CRT on AArch64: constant time of the primes' setup

`wsNew` computes the prime's size without branching (a `csel`), so the
taint analysis checks it from its bases. `primesSetup` (`setup_ct`) runs in
the modulus' workspace, then in the primes'; between its pieces, what the
next one reads from the headers (`SSt`, the primes' links, sizes and bases
`WsF`) is kept by the frames of the pieces before it.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The setup's states -/

/-- What the setup keeps: the modulus' working space and header, its
arguments, and the byte strings. -/
def SSt (p : SetupPub) (t : State) : Prop :=
  ∃ pb qb ib : List Byte, Scr t p.B p.Z ∧ Hdr t.mem p.B p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ p.w p.pl + slot (wsWords p.ql) 8 + wsTab (wsWords p.ql) ≤ p.Z ∧
    word t.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl ∧ word t.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql ∧
    word t.mem p.B (8 * sP) = p.pp ∧ word t.mem p.B (8 * sQ) = p.qp ∧ word t.mem p.B (8 * sQinv) = p.ip ∧
    Src t p.B p.Z p.pp pb ∧ Src t p.B p.Z p.qp qb ∧ Src t p.B p.Z p.ip ib ∧ pb.length = p.pl ∧
    qb.length = p.ql ∧ ib.length = p.pl ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w

theorem SSt.frm {p : SetupPub} {t t' : State} (h : SSt p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, 8 * 29 ≤ r.1 ∧ r.1 + r.2 ≤ p.Z) {regs : List Reg} (k : Keep regs t t') : SSt p t' := by
  obtain ⟨pb, qb, ib, hs, hH, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩ := h
  have hn := hs.nowrap
  have h8 : 256 ≤ offQ p.w p.pl := by unfold offQ slot hdrBytes; omega_arith
  have hw : ∀ i < 29, word t'.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_arith)) (by omega_arith)
  have hi := InScr.of_frm hf fun r hr' => (hr r hr').2
  exact ⟨pb, qb, ib, hs.congr k.wr, ⟨(hw _ (by decide)).trans hH.hw, (hw _ (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega_arith)).trans (hH.harr j hj)⟩, a1, a2, hZ, (hw _ (by decide)).trans b1,
    (hw _ (by decide)).trans b2, (hw _ (by decide)).trans b3, (hw _ (by decide)).trans b4,
    (hw _ (by decide)).trans b5, c1.congrK hi k, c2.congrK hi k, c3.congrK hi k, d⟩

theorem SSt.mem {p : SetupPub} {t t' : State} (h : SSt p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : SSt p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k

theorem SSt.scr {p : SetupPub} {t : State} (h : SSt p t) : Scr t p.B p.Z :=
  let ⟨_, _, _, hs, _⟩ := h; hs

theorem SSt.bounds {p : SetupPub} {t : State} (h : SSt p t) :
    8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ offQ p.w p.pl + slot (wsWords p.ql) 8 + wsTab (wsWords p.ql) ≤ p.Z ∧ 1 ≤ p.pl ∧
      p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w :=
  let ⟨_, _, _, _, _, a1, a2, hZ, _, _, _, _, _, _, _, _, _, _, _, d1, d2, d3, d4⟩ := h
  ⟨a1, a2, hZ, d1, d2, d3, d4⟩

/-- A prime's workspace at `off B o`: its link, size and bases. -/
def WsF (m : Mem) (B : Addr) (o wx : Nat) : Prop :=
  word m (off B o) (8 * sLink) = B ∧ word m (off B o) (8 * sW) = BitVec.ofNat 64 wx ∧
    ∀ j < 8, word m (off B o) (8 * sArr j) = off (off B o) (slot wx j)

theorem WsF.frm {m m' : Mem} {B : Addr} {o wx : Nat} (h : WsF m B o wx) {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, o + 8 * 17 ≤ r.1 ∨ r.1 + r.2 ≤ o) (ho : o + 8 * 17 ≤ 2 ^ 64) : WsF m' B o wx := by
  have hw : ∀ i < 17, word m' (off B o) (8 * i) = word m (off B o) (8 * i) := fun i hi => by
    rw [word_off, word_off]
    exact hf.word_eq (fun r hr' => by have := hr r hr'; omega_arith) (by omega_arith)
  exact ⟨(hw _ (by decide)).trans h.1, (hw _ (by decide)).trans h.2.1,
    fun j hj => (hw _ (by unfold sArr; omega_arith)).trans (h.2.2 j hj)⟩

/-- After `p`'s workspace. -/
def SA (p : SetupPub) (t : State) : Prop :=
  SSt p t ∧ word t.mem p.B (8 * sWsP) = off p.B (offP p.w) ∧ WsF t.mem p.B (offP p.w) (wsWords p.pl)

/-- After `q`'s workspace. -/
def SB (p : SetupPub) (t : State) : Prop :=
  SA p t ∧ word t.mem p.B (8 * sWsQ) = off p.B (offQ p.w p.pl) ∧ WsF t.mem p.B (offQ p.w p.pl) (wsWords p.ql)

theorem SB.frm {p : SetupPub} {t t' : State} (h : SB p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, offP p.w + 8 * 17 ≤ r.1 ∧ (r.1 + r.2 ≤ offQ p.w p.pl ∨ offQ p.w p.pl + 8 * 17 ≤ r.1) ∧
      r.1 + r.2 ≤ p.Z) {regs : List Reg} (k : Keep regs t t') : SB p t' := by
  obtain ⟨⟨hS, hP, hFP⟩, hQ, hFQ⟩ := h
  have hn := hS.scr.nowrap
  obtain ⟨a1, -, hZ, -, -, -, -⟩ := hS.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  have hPQ : offP p.w + 256 ≤ offQ p.w p.pl := by unfold offP offQ slot hdrBytes; omega_arith
  have hP0 : offP p.w = slot p.w 8 := rfl
  have hQZ : offQ p.w p.pl + 256 ≤ p.Z := by unfold slot hdrBytes at hZ; omega_arith
  refine ⟨⟨hS.frm hf (fun r hr' => by have := hr r hr'; omega_arith) k, ?_, hFP.frm hf (fun r hr' => by
    have := hr r hr'; omega_arith) (by omega_arith)⟩, ?_, hFQ.frm hf (fun r hr' => by have := hr r hr'; omega_arith) (by omega_arith)⟩
  · rw [hf.word_eq (fun r hr' => by have := hr r hr'; unfold sWsP sFn; omega_arith) (by unfold sWsP sFn; omega_arith)]
    exact hP
  · rw [hf.word_eq (fun r hr' => by have := hr r hr'; unfold sWsQ sFn; omega_arith) (by unfold sWsQ sFn; omega_arith)]
    exact hQ

theorem SA.frm' {p : SetupPub} {t t' : State} (h : SA p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : SA p t' :=
  ⟨h.1.mem hm k, hm ▸ h.2.1, hm ▸ h.2.2⟩

theorem SB.mem {p : SetupPub} {t t' : State} (h : SB p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : SB p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k

theorem SB.scr {p : SetupPub} {t : State} (h : SB p t) : Scr t p.B p.Z := h.1.1.scr

theorem SB.bounds {p : SetupPub} {t : State} (h : SB p t) :
    8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ offQ p.w p.pl + slot (wsWords p.ql) 8 + wsTab (wsWords p.ql) ≤ p.Z ∧ 1 ≤ p.pl ∧
      p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w := h.1.1.bounds

/-- `SB` with `x0` at `f p`. -/
def SBr (f : SetupPub → Addr) (p : SetupPub) (t : State) : Prop := SB p t ∧ t.gpr .x0 = f p

theorem pins_sbr (f : SetupPub → Addr) : Pins (SBr f) [.x0] :=
  pins_of (fun p _ => f p) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2

theorem SetupPre.sst {p : SetupPub} {s : State} (h : SetupPre p s) : SSt p s ∧ s.gpr .x0 = p.B :=
  let ⟨pb, qb, ib, hg, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩ := h
  ⟨⟨pb, qb, ib, hg.scr, hg.hdr, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩, hg.x0⟩

/-! ## The workspaces -/

/-- Before `p`'s workspace: its base in `x4`. -/
def SS1 (p : SetupPub) (t : State) : Prop := SSt p t ∧ t.gpr .x0 = p.B ∧ t.gpr .x4 = off p.B (offP p.w)

/-- Before `q`'s workspace: its base in `x4`. -/
def SS3 (p : SetupPub) (t : State) : Prop := SA p t ∧ t.gpr .x0 = p.B ∧ t.gpr .x4 = off p.B (offQ p.w p.pl)

theorem pins_ws {Φ : SetupPub → State → Prop} (f : SetupPub → Addr)
    (h : ∀ p s, Φ p s → s.gpr .x0 = p.B ∧ s.gpr .x4 = f p) : Pins Φ [.x0, .x4] :=
  pins_of (fun p r => if r = .x0 then p.B else f p) fun p s hs r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (h p s hs).1
    · exact (h p s hs).2

theorem stage1_ok {p : SetupPub} {s : State} (h : SetupPre p s) :
    WP isa (.block (([mov .x5 .x0] : List Instr) ++ wsEnd)) s (SS1 p) := by
  obtain ⟨hS, h0⟩ := h.sst
  have hS' := hS
  obtain ⟨_, _, _, hs, hH, a1, a2, hZ, -⟩ := hS'
  have : slot p.w 8 ≤ offQ p.w p.pl := by unfold offQ; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B ∧ t.mem = s.mem) (by brun [h0])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h5₁, hm₁⟩, k₁⟩ => ?_
  exact WP.mono (wsEnd_ok (wx := p.w) (hs.congr k₁.wr) h5₁ (by rw [hm₁]; exact hH.hw) (by omega_arith)
    (by rw [hm₁]; exact hH.harr _ (by decide)) (by omega_arith)) fun t ⟨⟨h4, _, hm₂⟩, k₂⟩ =>
    ⟨hS.mem (hm₂.trans hm₁) (k₁.trans k₂), (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans h0), h4⟩

theorem wsP_ok {p : SetupPub} {s : State} (h : SS1 p s) :
    WP isa (.block (wsNew sWsP sPlen)) s fun t => SA p t ∧ t.gpr .x0 = p.B := by
  obtain ⟨hS, h0, h4⟩ := h
  have hS' := hS
  obtain ⟨_, _, _, hs, -, a1, a2, hZ, hpl, -, -, -, -, -, -, -, -, -, -, d1, d2, -, -⟩ := hS'
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega_arith
  unfold offQ at hZ
  exact WP.mono (wsNew_ok (o := offP p.w) (len := p.pl) hs h0 h4 (by decide) (by decide) (by decide) hpl
    (by omega_arith) (by unfold offP; omega_arith) (by unfold offP; omega_arith))
    fun t ⟨hWs, hl, hw, ha, h0', f, k⟩ => ⟨⟨hS.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsP, sFn, offP] <;> omega_arith) k, hWs, hl, hw, ha⟩, h0'⟩

/-- `q`'s workspace's base: `p`'s, in `x5`. -/
def SS2 (p : SetupPub) (t : State) : Prop :=
  SA p t ∧ t.gpr .x0 = p.B ∧ t.gpr .x5 = off p.B (offP p.w)

theorem stage2_ok {p : SetupPub} {s : State} (h : SA p s ∧ s.gpr .x0 = p.B) :
    WP isa (.block [ldh .x5 sWsP]) s (SS2 p) := by
  obtain ⟨hA, h0⟩ := h
  have hs := hA.1.scr
  have hWsP := hA.2.1
  have := hA.1.bounds
  have hn := hs.nowrap
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  unfold offQ at this
  exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = off p.B (offP p.w) ∧ t.mem = s.mem)
    (by brun [h0, hdr_enc (show sWsP < 32 by decide), hs.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega_arith), hWsP])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h5, hm⟩, k⟩ => ⟨hA.frm' hm k, (k.gpr .x0 (by decide)).trans h0, h5⟩

theorem stage3_ok {p : SetupPub} {s : State} (h : SS2 p s) : WP isa (.block wsEndT) s (SS3 p) := by
  obtain ⟨hA, h0, h5⟩ := h
  have hA' := hA
  obtain ⟨⟨_, _, _, hs, -, a1, -, hZ, -⟩, -, -, hw, ha⟩ := hA'
  have hn := hs.nowrap
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega_arith
  have hwp : wsWords p.pl < 2 ^ 30 := by have := hA.1.bounds; unfold wsWords; omega_arith
  unfold offQ at hZ
  refine WP.mono (wsEndT_ok (wx := wsWords p.pl) (hs.sub (o := offP p.w)
    (n := slot (wsWords p.pl) 8) (by unfold offP; omega_arith) (by omega_arith)) h5 hw hwp
    (ha _ (by decide)) (Nat.le_refl _)) fun t ⟨⟨h4, hm⟩, k⟩ => ?_
  rw [off_off] at h4
  exact ⟨hA.frm' hm k, (k.gpr .x0 (by decide)).trans h0, by
    rw [h4]; exact congrArg (off p.B) (by unfold offQ offP; omega_arith)⟩

theorem wsQ_ok {p : SetupPub} {s : State} (h : SS3 p s) :
    WP isa (.block (wsNew sWsQ sQlen)) s (SBr (·.B) p) := by
  obtain ⟨hA, h0, h4⟩ := h
  have hA' := hA
  obtain ⟨⟨_, _, _, hs, -, a1, a2, hZ, -, hql, -, -, -, -, -, -, -, -, -, d1, d2, d3, d4⟩, hWsP, hF⟩ := hA'
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega_arith
  have hn := hs.nowrap
  unfold offQ at hZ
  refine WP.mono (wsNew_ok (o := offQ p.w p.pl) (len := p.ql) hs h0 h4 (by decide) (by decide) (by decide) hql
    (by omega_arith) (by unfold offQ; omega_arith) (by unfold offQ; omega_arith))
    fun t ⟨hWs, hl, hw, ha, h0', f, k⟩ => ⟨⟨⟨hA.1.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsQ, sFn, offQ] <;> omega_arith) k, ?_, hF.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsQ, sFn, offQ, offP] <;> omega_arith) (by unfold offP; omega_arith)⟩,
      hWs, hl, hw, ha⟩, h0'⟩
  rw [f.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sWsQ, sWsP, sFn, offQ] <;> omega_arith) (by unfold sWsP sFn; omega_arith)]
  exact hWsP

/-- Into a workspace from the modulus' (`enterP`, `enterQ`), or back (`leave`). -/
theorem SB.move {p : SetupPub} {s : State} (h : SB p s) {X : Addr} {i : Nat} {f : SetupPub → Addr}
    (h0 : s.gpr .x0 = X) (hi : i < 32) (hl : InRegions (s.rd ++ s.wr) (off X (8 * i)) 8)
    (hw : word s.mem X (8 * i) = f p) :
    WP isa (.block [ldh .x0 i]) s (SBr f p) :=
  WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = f p ∧ t.mem = s.mem)
    (by brun [h0, hdr_enc hi, hl, hw]) rfl rfl rfl) fun t ⟨⟨h0', hm⟩, k⟩ => ⟨h.mem hm k, h0'⟩

/-- A prime's workspace context from `SB`. -/
theorem SB.sub {p : SetupPub} {s : State} (h : SB p s) {o wx : Nat} (h0 : s.gpr .x0 = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ p.Z) :
    SubCtx s p.B p.Z o p.w wx (word s.mem (off p.B o) (8 * sMinv)) :=
  let ⟨⟨⟨_, _, _, hs, hH, _⟩, _⟩, _⟩ := h
  ⟨hs, h0, hdr_any hF.2.1 hF.2.2, hF.1, hH.hw, hH.harr, hlo, hi_of_wsTab hhi⟩

/-- A load into a prime's workspace keeps `SB`. -/
theorem SB.load {p : SetupPub} {s : State} {o wx j sp sl len : Nat} {ptr : Addr} (h : SB p s)
    (hL : LPre j sp sl ⟨⟨p.B, p.Z, o, p.w, wx⟩, ptr, len⟩ s)
    (hr : offP p.w + 8 * 17 ≤ o + 256 ∧ (o + slot wx 8 ≤ offQ p.w p.pl ∨ offQ p.w p.pl + 8 * 17 ≤ o + 256)) :
    WP isa (seqs (loadArr j sp sl)) s fun t => SB p t ∧ t.gpr .x0 = off p.B o := by
  simp only [LPre] at hL
  obtain ⟨minv, bs, hc, hw2, hwx, hw30, hj, hsp, hsl, hp, hl, hbl, hsrc, hk1, hk', hkw⟩ := hL
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hc.scr.nowrap
  have hi : o + slot wx 8 + tabBytes wx ≤ p.Z := hc.hi
  have h8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  exact WP.mono (primeLoad_ok hc hw2 hwx hw30 hj hsp hsl hp hl hsrc hk1 hk' hkw) fun t ⟨hc', _, ho, k⟩ =>
    ⟨h.frm (Frm.of_load ho hj (by omega_arith) (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only; omega_arith) k, hc'.x0⟩

/-- `LPre` from `SB`, in the workspace at `off B o` (`x0`). -/
theorem SB.lpre {p : SetupPub} {s : State} (h : SB p s) {o wx j sp sl len : Nat} {ptr : Addr} {bs : List Byte}
    (h0 : s.gpr .x0 = off p.B o) (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o)
    (hhi : o + slot wx 8 + wsTab wx ≤ p.Z) (hw2 : 2 ≤ wx) (hwx : wx ≤ p.w) (hj : j < 8) (hsp : sp < 32)
    (hsl : sl < 32) (hp : word s.mem p.B (8 * sp) = ptr) (hl : word s.mem p.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hbl : bs.length = len) (hsrc : Src s p.B p.Z ptr bs) (hk1 : 1 ≤ bs.length) (hk' : bs.length < 2 ^ 31)
    (hkw : (bs.length + 7) / 8 ≤ wx) : LPre j sp sl ⟨⟨p.B, p.Z, o, p.w, wx⟩, ptr, len⟩ s :=
  ⟨_, bs, h.sub h0 hF hlo hhi, hw2, hwx, by have := h.bounds; show p.w < 2 ^ 30; omega_arith, hj, hsp, hsl, hp, hl,
    hbl, hsrc, hk1, hk', hkw⟩

theorem lpreP {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    LPre Public.aN sP sPlen ⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.pp, p.pl⟩ s ∧
      LPre aChunk sQinv sPlen ⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.ip, p.pl⟩ s := by
  obtain ⟨hB, h0⟩ := h
  have hB' := hB
  obtain ⟨⟨⟨pb, qb, ib, hs, -, a1, a2, hZ, hpl, -, hpp, -, hip, c1, -, c3, l1, -, l3, d1, d2, -, -⟩, -, hF⟩, -⟩ := hB'
  unfold offQ at hZ
  have hw := wsWords_le d2 (by omega_arith)
  exact ⟨hB.lpre h0 hF (Nat.le_refl _) (by unfold offP; omega_arith) (by unfold wsWords; omega_arith) hw (by decide)
    (by decide) (by decide) hpp (by rw [l1]; exact hpl) l1 c1 (by omega_arith) (by omega_arith) (by unfold wsWords; omega_arith),
    hB.lpre h0 hF (Nat.le_refl _) (by unfold offP; omega_arith) (by unfold wsWords; omega_arith) hw (by decide)
    (by decide) (by decide) hip (by rw [l3]; exact hpl) l3 c3 (by omega_arith) (by omega_arith) (by unfold wsWords; omega_arith)⟩

theorem lpreQ {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offQ p.w p.pl)) p s) :
    LPre Public.aN sQ sQlen ⟨⟨p.B, p.Z, offQ p.w p.pl, p.w, wsWords p.ql⟩, p.qp, p.ql⟩ s := by
  obtain ⟨hB, h0⟩ := h
  have hB' := hB
  obtain ⟨⟨⟨pb, qb, ib, hs, -, a1, a2, hZ, -, hql, -, hqp, -, -, c2, -, -, l2, -, -, -, d3, d4⟩, -, -⟩, -, hF⟩ := hB'
  exact hB.lpre h0 hF (by unfold offQ; omega_arith) hZ (by unfold wsWords; omega_arith) (wsWords_le d4 (by omega_arith))
    (by decide) (by decide) (by decide) hqp (by rw [l2]; exact hql) l2 c2 (by omega_arith) (by omega_arith)
    (by unfold wsWords; omega_arith)

theorem enterP_ok {p : SetupPub} {s : State} (h : SBr (·.B) p s) :
    WP isa (.block [enterP]) s (SBr (fun p => off p.B (offP p.w)) p) := by
  obtain ⟨h, h0⟩ := h
  have := h.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  exact h.move (X := p.B) (i := sWsP) h0 (by decide) (h.scr.ld (by unfold sWsP sFn offQ at *; omega_arith)) h.1.2.1

theorem leaveP_ok {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    WP isa (.block [leave]) s (SBr (·.B) p) := by
  obtain ⟨h, h0⟩ := h
  have hF := h.1.2.2
  have := h.bounds
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega_arith
  exact h.move (X := off p.B (offP p.w)) (i := sLink) h0 (by decide) ((h.scr.sub (o := offP p.w)
    (n := slot (wsWords p.pl) 8) (by unfold offQ offP at *; omega_arith) (by omega_arith)).ld (by unfold sLink sFn; omega_arith)) hF.1

theorem enterQ_ok {p : SetupPub} {s : State} (h : SBr (·.B) p s) :
    WP isa (.block [enterQ]) s (SBr (fun p => off p.B (offQ p.w p.pl)) p) := by
  obtain ⟨h, h0⟩ := h
  have := h.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  exact h.move (X := p.B) (i := sWsQ) h0 (by decide) (h.scr.ld (by unfold sWsQ sFn offQ at *; omega_arith)) h.2.1

theorem loadP1_ok {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    WP isa (seqs (loadArr Public.aN sP sPlen)) s (SBr (fun p => off p.B (offP p.w)) p) :=
  SB.load (o := offP p.w) (wx := wsWords p.pl) h.1 (lpreP h).1
    ⟨by omega_arith, Or.inl (by unfold offQ offP; omega_arith)⟩

theorem loadP2_ok {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    WP isa (seqs (loadArr aChunk sQinv sPlen)) s (SBr (fun p => off p.B (offP p.w)) p) :=
  SB.load (o := offP p.w) (wx := wsWords p.pl) h.1 (lpreP h).2
    ⟨by omega_arith, Or.inl (by unfold offQ offP; omega_arith)⟩

theorem loadQ_ok {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offQ p.w p.pl)) p s) :
    WP isa (seqs (loadArr Public.aN sQ sQlen)) s (SBr (fun p => off p.B (offQ p.w p.pl)) p) :=
  SB.load (o := offQ p.w p.pl) (wx := wsWords p.ql) h.1 (lpreQ h) ⟨by unfold offQ offP; omega_arith, Or.inr (by omega_arith)⟩

theorem leaveEnterQ_ct : RelCT isa (Two (SBr fun p => off p.B (offP p.w))) (.block [leave, enterQ])
    (Two (SBr fun p => off p.B (offQ p.w p.pl))) :=
  RelCT.block_append (l₁ := ([leave] : List Instr))
    (RelCT.seq (two_piece (Ψ := SBr (·.B)) [.x0] (pins_sbr _) (by taint_decide) fun p s h => leaveP_ok h)
      (two_piece [.x0] (pins_sbr _) (by taint_decide) fun p s h => enterQ_ok h))

theorem primesSetup_eq : primesSetup = ([.block (([mov .x5 .x0] : List Instr) ++ wsEnd)] : List (Prog isa)) ++
    (([.block (wsNew sWsP sPlen)] : List (Prog isa)) ++ (([.block (([ldh .x5 sWsP] : List Instr) ++ wsEndT)] : List (Prog isa)) ++
    (([.block (wsNew sWsQ sQlen)] : List (Prog isa)) ++ (([.block [enterP]] : List (Prog isa)) ++ (loadArr Public.aN sP sPlen ++
    (loadArr aChunk sQinv sPlen ++ (([.block [leave, enterQ]] : List (Prog isa)) ++ (loadArr Public.aN sQ sQlen ++
    ([.block [leave]] : List (Prog isa)))))))))) := rfl

theorem setup_ct : SetupCT := by
  unfold SetupCT
  rw [primesSetup_eq]
  -- `p`'s workspace.
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (two_piece (Ψ := SS1) [.x0]
    (pins_of (fun p _ => p.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sst.2) (by taint_decide)
    fun p s h => stage1_ok h) ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (two_piece
    (Ψ := fun p t => SA p t ∧ t.gpr .x0 = p.B) [.x0, .x4]
    (pins_ws (fun p => off p.B (offP p.w)) fun p s h => ⟨h.2.1, h.2.2⟩) (by taint_decide)
    fun p s h => wsP_ok h) ?_)
  -- `q`'s workspace.
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (RelCT.block_append
    (l₁ := ([ldh .x5 sWsP] : List Instr)) (l₂ := wsEndT) (RelCT.seq (two_piece (Ψ := SS2) [.x0]
    (pins_of (fun p _ => p.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide)
    fun p s h => stage2_ok h) (two_piece (Ψ := SS3) [.x5]
    (pins_of (fun p _ => off p.B (offP p.w)) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2) (by taint_decide)
    fun p s h => stage3_ok h))) ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (two_piece (Ψ := SBr (·.B)) [.x0, .x4]
    (pins_ws (fun p => off p.B (offQ p.w p.pl)) fun p s h => ⟨h.2.1, h.2.2⟩) (by taint_decide)
    fun p s h => wsQ_ok h) ?_)
  -- Into `p`'s workspace: `p` and `qInv`.
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (two_piece
    (Ψ := SBr fun p => off p.B (offP p.w)) [.x0] (pins_sbr _) (by taint_decide) fun p s h => enterP_ok h) ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (two_post
    (Ψ := SBr fun p => off p.B (offP p.w)) (two_map
    (fun p : SetupPub => (⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.pp, p.pl⟩ : BPub)) (fun p s h => (lpreP h).1)
    loadArr_ct_pN) fun p s h => loadP1_ok h) ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (two_post
    (Ψ := SBr fun p => off p.B (offP p.w)) (two_map
    (fun p : SetupPub => (⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.ip, p.pl⟩ : BPub)) (fun p s h => (lpreP h).2)
    loadArr_ct_pI) fun p s h => loadP2_ok h) ?_)
  -- Into `q`'s workspace: `q`.
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq leaveEnterQ_ct ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (two_post
    (Ψ := SBr fun p => off p.B (offQ p.w p.pl)) (two_map
    (fun p : SetupPub => (⟨⟨p.B, p.Z, offQ p.w p.pl, p.w, wsWords p.ql⟩, p.qp, p.ql⟩ : BPub))
    (fun p s h => lpreQ h) loadArr_ct_qN)
    fun p s h => loadQ_ok h) ?_)
  exact two_taint [.x0] (pins_sbr _) (by taint_decide)

end VG.Proof.Bignum.AArch64

end

end

/-! ### `Bignum.AArch64.CrtCTSetupChk`, which only this module used -/

section

/-! ### `Bignum.AArch64.CrtCTSetupFix`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: constant time of a prime's fixes

`primeFix` in a prime's workspace (`primeFix_ct`): the mask's load reads
`n`'s header through the workspace's link, pinned by correctness; the
masking loop runs from the array's base and `w_X`, the low word's fix from
the array's base, and `-X⁻¹` and the number 1 from `x0`. What each piece
keeps and changes (`pf1_ok` to `pf4_ok`) gives `primeFix_frm`, what
`primeFix` changes whatever the mask and the prime.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `minv` changes only its registers, whatever `x3`. -/
theorem minv_keep (s : State) :
    WP isa (.block VG.Impl.Bignum.AArch64.minv) s fun t => Keep [.x4, .x5, .x6, .x15] s t ∧ t.mem = s.mem :=
  WP.mono (WP.keep [.x4, .x5, .x6, .x15] (Q := fun t => t.mem = s.mem)
    (by brun [VG.Impl.Bignum.AArch64.minv, newton]) (by decide) (by decide) (by decide +kernel))
    fun _ ⟨h, k⟩ => ⟨k, h⟩

/-- The low word's fix: its base, then the fix. -/
def fixA : List Instr :=
  [movi .x4 3, .logic .and .x .x5 .x15 .x4, .logic .eor .x .x5 .x5 .x4, ldh .x16 (sArr Public.aN)]

def fixB : List Instr := [ld .x3 .x16, .logic .orr .x .x3 .x3 .x5, st .x3 .x16]

theorem fixLow_eq : fixLow = fixA ++ fixB := rfl

/-! ## The pieces' correctness -/

theorem pf1_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) :
    WP isa (.block fixMask) s fun t => SubCtx t B Z o w wx minv ∧ word t.mem (off B o) (8 * sMaskX) = mask c ∧
      Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem ∧ Keep [.x5] s t := by
  have h8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  refine WP.mono (fixMask_ok hc hM) fun t ⟨hm, k⟩ => ?_
  have o₁ := writeW_outside s.mem (off B o) (d := 8 * sMaskX) (mask c) (by decide)
  rw [← hm] at o₁
  have f₁ : Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem := Frm.of_outside o₁ (by simp)
  exact ⟨hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sMaskX sFn; omega_arith) k.wr
    (k.gpr .x0 (by decide)), by rw [hm]; exact word_writeW_self _ _ _ _, f₁, k⟩

theorem pf2_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31)
    (hm : word s.mem (off B o) (8 * sMaskX) = mask c) :
    WP isa (seqs (maskArr Public.aN)) s fun t => SubCtx t B Z o w wx minv ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  refine WP.mono (maskArr_ok hc.good (Nat.le_refl _) hw hw' (by decide) hm) fun t ⟨_, _, ho, _, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) k.wr
    (k.gpr .x0 (by decide)), f, k⟩

theorem pfA_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv) :
    WP isa (.block fixA) s fun t => t.gpr .x16 = off B (o + slot wx Public.aN) ∧ t.mem = s.mem ∧
      Keep [.x4, .x5, .x16] s t :=
  WP.mono (WP.keep [.x4, .x5, .x16] (Q := fun t => t.gpr .x16 = off B (o + slot wx Public.aN) ∧ t.mem = s.mem)
    (by brun [fixA, hc.x0, hdr_enc (sArr_lt (show Public.aN < 8 by decide)),
      hc.ld' (sArr_lt (show Public.aN < 8 by decide)), hc.harr' (show Public.aN < 8 by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16, hm⟩, k⟩ => ⟨h16, hm, k⟩

/-- A prime's workspace context after a store of its `-X⁻¹`. -/
theorem SubCtx.setMinv {s t : State} {B : Addr} {Z o w wx : Nat} {minv v : BitVec 64}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem.writeW (off (off B o) (8 * sMinv)) v)
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) : SubCtx t B Z o w wx v := by
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
  exact ⟨h.scr.congr hwr, h0.trans h.x0, ⟨(hh _ (by decide) (by decide)).trans h.hdr.hw,
    by rw [hm]; exact word_writeW_self _ _ _ _,
    fun j hj => (hh _ (by unfold sArr; omega_arith) (by unfold sArr sMinv; omega_arith)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide) (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega_arith)).trans (h.narr j hj), hlo, hi⟩

theorem pf3_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w wx mi) (h16 : s.gpr .x16 = off B (o + slot wx Public.aN)) :
    WP isa (.block (fixB ++ VG.Impl.Bignum.AArch64.minv ++ fixTail)) s fun t =>
      SubCtx t B Z o w wx (word t.mem (off B o) (8 * sMinv)) ∧ t.gpr .x12 = BitVec.ofNat 64 wx ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hd : o + slot wx Public.aN + 8 ≤ Z := by omega_arith
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (c := .block fixB) (Q := fun t =>
      ∃ v : BitVec 64, t.mem = s.mem.writeW (off B (o + slot wx Public.aN)) v) (by
    brun [fixB, h16, hc.scr.ld hd, hc.scr.st hd]; exact ⟨_, rfl⟩) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨v, hm₁⟩, k₁⟩ => ?_
  rw [← off_off] at hm₁
  have o₁ := writeW_outside s.mem (off B o) (d := slot wx Public.aN) v (by omega_arith)
  rw [← hm₁] at o₁
  have f₁ : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem s₁.mem :=
    Frm.of_outside (o₁.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hc₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) k₁.wr
    (k₁.gpr .x0 (by decide))
  refine WP.mono (minv_keep s₁) fun s₂ ⟨k₂, hm₂⟩ => ?_
  have hc₂ := hc₁.mem hm₂ k₂ (by decide)
  have hs₂ := hc₂.good.scr
  have hW : ∀ v : BitVec 64, word (s₂.mem.writeW (off B (o + 8 * sMinv)) v) B (o + 8 * sW) =
      BitVec.ofNat 64 wx := fun v => by
    rw [← off_off, ← word_off, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hc₂.hdr.hw
  refine WP.mono (WP.keep [.x9, .x12, .x13] (c := .block fixTail) (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 wx ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧ t.mem = s₂.mem.writeW (off (off B o) (8 * sMinv)) (s₂.gpr .x15)) (by
    rw [off_off]
    brun [fixTail, hc₂.x0, hdr_enc (show sMinv < 32 by decide), hdr_enc (show sW < 32 by decide),
      hc₂.st' (show sMinv < 32 by decide), hc₂.ld' (show sW < 32 by decide), hW])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h12, h13, hm₃⟩, k₃⟩ => ?_
  have o₃ := writeW_outside s₂.mem (off B o) (d := 8 * sMinv) (s₂.gpr .x15) (by decide)
  rw [← hm₃] at o₃
  have f₃ : Frm (off B o) [(8 * sMinv, 8)] s₂.mem t.mem := Frm.of_outside o₃ (by simp)
  have K := (k₁.trans k₂).trans k₃
  refine ⟨hc₂.setMinv (by rw [hm₃, word_writeW_self]) k₃.wr (k₃.gpr .x0 (by decide)), h12, h13, ?_,
    K.mono (by decide)⟩
  rw [hm₂] at f₃
  exact (f₁.append f₃).mono fun r hr => by simpa using hr

theorem pf4_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31) (h12 : s.gpr .x12 = BitVec.ofNat 64 wx)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 0) :
    WP isa (setWord Public.aOne) s fun t => SubCtx t B Z o w wx minv ∧
      Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem ∧ Keep [.x7, .x8, .x14, .x16] s t := by
  have h0 := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aOne < 8 by decide)
  refine WP.mono (setWord_ok hc.good.scr hc.x0 hc.hdr (Nat.le_refl _) h12 hw' (o := Public.aOne) (by decide)
    (i := 0) (by omega_arith) h13) fun t ⟨_, ho, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) k.wr
    (k.gpr .x0 (by decide)), f, k⟩

/-- What `primeFix` changes, whatever the mask and the prime. -/
def pfRanges (wx : Nat) : List (Nat × Nat) :=
  [(8 * sMaskX, 8), (slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8), (slot wx Public.aOne, 8 * (wx + 2))]

theorem primeFix_eq' : primeFix = ([.block fixMask] : List (Prog isa)) ++ (maskArr Public.aN ++
    ([.block (fixA ++ (fixB ++ VG.Impl.Bignum.AArch64.minv ++ fixTail)), setWord Public.aOne] : List (Prog isa))) := by
  rw [primeFix_eq, fixLow_eq]; simp only [List.append_assoc]

theorem primeFix_frm {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) (hw : 1 ≤ wx)
    (hw' : wx < 2 ^ 31) :
    WP isa (seqs primeFix) s fun t => ∃ minv', SubCtx t B Z o w wx minv' ∧
      Frm (off B o) (pfRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  rw [primeFix_eq']
  refine wp_seqs_append (by simp) (by simp [maskArr]) ?_
  refine WP.mono (pf1_ok hc hM) fun s₁ ⟨hc₁, hm₁, f₁, k₁⟩ => ?_
  refine wp_seqs_append (by simp [maskArr]) (by simp) ?_
  refine WP.mono (pf2_ok hc₁ hw hw' hm₁) fun s₂ ⟨hc₂, f₂, k₂⟩ => ?_
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pfA_ok hc₂) fun s₃ ⟨h16, hm₃, k₃⟩ => ?_
  have hc₃ := hc₂.mem hm₃ k₃ (by decide)
  refine WP.mono (pf3_ok hc₃ h16) fun s₄ ⟨hc₄, h12₄, h13₄, f₄, k₄⟩ => ?_
  refine WP.mono (pf4_ok hc₄ hw hw' h12₄ h13₄) fun t ⟨hc₅, f₅, k₅⟩ => ⟨_, hc₅, ?_,
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  rw [hm₃] at f₄
  exact (((f₁.append f₂).append f₄).append f₅).mono fun r hr => by
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
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the low word's base. -/
def PFA (p : XPub) (s : State) : Prop := PF2 p s ∧ s.gpr .x16 = off p.B (p.o + slot p.wx Public.aN)

/-- After `-X⁻¹`. -/
def PF3 (p : XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧ s.gpr .x12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .x13 = BitVec.ofNat 64 0

/-- `setWord`'s registers. -/
def PF4 (p : XPub) (s : State) : Prop :=
  s.gpr .x8 = off p.B (p.o + slot p.wx Public.aOne) ∧ s.gpr .x12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .x13 = BitVec.ofNat 64 0

theorem fixMask_ct : RelCT isa (Two PF) (.block fixMask) fun _ _ => True := by
  unfold fixMask
  refine RelCT.block_append (l₁ := ([ldh .x5 sLink] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun p t => PF p t ∧ t.gpr .x5 = p.B) [.x0]
      (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, _, hc, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hc.x0) (by taint_decide) ?_)
    (two_taint [.x0, .x5] (pins_of (fun (p : XPub) r => if r = .x0 then off p.B p.o else p.B)
      fun p s ⟨⟨_, _, hc, _⟩, h5⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.x0
        · exact h5) (by taint_decide)))
  rintro p s ⟨minv, c, hc, hM, h1, h2⟩
  exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B ∧ t.mem = s.mem)
    (by brun [hc.x0, hdr_enc (show sLink < 32 by decide), hc.ld' (show sLink < 32 by decide), hc.link'])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h5, hm⟩, k⟩ => ⟨⟨minv, c, hc.mem hm k (by decide), hm ▸ hM, h1, h2⟩, h5⟩

/-- `primeFix` is constant time. -/
theorem primeFix_ct : RelCT isa (Two PF) (seqs primeFix) fun _ _ => True := by
  rw [primeFix_eq']
  refine RelCT.seqs_append (by simp) (by simp [maskArr]) (RelCT.seq (two_post (Ψ := PF1) fixMask_ct
    fun p s ⟨minv, c, hc, hM, h1, h2⟩ => WP.mono (pf1_ok hc hM) fun t ⟨hc', hm, _⟩ =>
      ⟨minv, c, hc', hm, h1, h2⟩) ?_)
  refine RelCT.seqs_append (by simp [maskArr]) (by simp) (RelCT.seq (two_post (Ψ := PF2)
    (two_map (fun p : XPub => (⟨off p.B p.o, slot p.wx 8, p.wx⟩ : Ws))
      (fun p s ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) (maskArr_ct (by decide) (by taint_decide)))
    fun p s ⟨minv, c, hc, hm, h1, h2⟩ => WP.mono (pf2_ok hc (by omega_arith) h2 hm) fun t ⟨hc', _⟩ =>
      ⟨minv, hc', h1, h2⟩) ?_)
  simp only [seqs]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_piece (Ψ := PFA) [.x0]
    (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, hc, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.x0) (by taint_decide)
    fun p s h => by
      obtain ⟨minv, hc, h1, h2⟩ := h
      exact WP.mono (pfA_ok hc) fun t ⟨h16, hm, k⟩ => ⟨⟨minv, hc.mem hm k (by decide), h1, h2⟩, h16⟩)
    (two_piece (Ψ := PF3) [.x0, .x16]
      (pins_of (fun (p : XPub) r => if r = .x0 then off p.B p.o else off p.B (p.o + slot p.wx Public.aN))
        fun p s ⟨⟨_, hc, _⟩, h16⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hc.x0
          · exact h16) (by taint_decide)
      fun p s ⟨⟨_, hc, _⟩, h16⟩ => WP.mono (pf3_ok hc h16) fun t ⟨hc', h12', h13, _⟩ =>
        ⟨_, hc', h12', h13⟩))) ?_
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := PF4) [.x0]
    (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, hc, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.x0) (by taint_decide) ?_)
    (two_taint [.x8, .x12, .x13] (pins_of (fun (p : XPub) r => if r = .x8 then
      off p.B (p.o + slot p.wx Public.aOne) else if r = .x12 then BitVec.ofNat 64 p.wx else BitVec.ofNat 64 0)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  rintro p s ⟨_, hc, h12, h13⟩
  exact WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off p.B (p.o + slot p.wx Public.aOne))
    (by brun [hc.x0, hdr_enc (sArr_lt (show Public.aOne < 8 by decide)),
      hc.ld' (sArr_lt (show Public.aOne < 8 by decide)), hc.harr' (show Public.aOne < 8 by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨h8, k⟩ => ⟨h8, (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13⟩

end VG.Proof.Bignum.AArch64

end

end

/-!
# RSA with the CRT on AArch64: constant time of the checks' pieces

Between the pieces of `checks`, what they read from the headers (`CK`: the
modulus' header, the primes' workspaces' bases, links, sizes and arrays, and
a mask in `sMask`) is kept by their frames. Each piece is constant time from
`CK` and `x0` (`pq_ct`, `eq_ct`, `qinv_ct`, `fixP_ct`, …).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- What the checks keep. -/
def CK (p : ChecksPub) (t : State) : Prop :=
  Scr t p.B p.Z ∧ Hdr t.mem p.B p.w p.minv ∧ word t.mem p.B (8 * sWsP) = off p.B p.op ∧
    word t.mem p.B (8 * sWsQ) = off p.B p.oq ∧ WsF t.mem p.B p.op p.wp ∧ WsF t.mem p.B p.oq p.wq ∧
    (∃ c, word t.mem p.B (8 * Public.sMask) = mask c) ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot p.wp 8 + wsTab p.wp ≤ p.oq ∧ p.oq + slot p.wq 8 + wsTab p.wq ≤ p.Z ∧ 2 ≤ p.wp ∧
    p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w

/-- `CK` with `x0` at `f p`. -/
def CKr (f : ChecksPub → Addr) (p : ChecksPub) (t : State) : Prop := CK p t ∧ t.gpr .x0 = f p

theorem pins_ckr (f : ChecksPub → Addr) : Pins (CKr f) [.x0] :=
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
  exact ⟨hs.congr k.wr, ⟨(hw _ (by decide)).trans hH.hw, (hw _ (by decide)).trans hH.hminv,
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
  exact ⟨hs.congr k.wr, ⟨(hw _ (by decide) (by decide)).trans hH.hw, (hw _ (by decide) (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega_arith) (by unfold sArr Public.sMask sFn; omega_arith)).trans (hH.harr j hj)⟩,
    (hw _ (by decide) (by decide)).trans hWP, (hw _ (by decide) (by decide)).trans hWQ,
    hP.frm f (fun r hr' => Or.inr (hr r hr')) (by omega_arith),
    hQ.frm f (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith), hM, b⟩

theorem ChecksPre.ck {p : ChecksPub} {s : State} (h : ChecksPre p s) : CKr (·.B) p s := by
  obtain ⟨mp, mq, P, Q, QI, m0, hg, a1, a2, b1, b2, b3, c1, c2, c3, c4, hsP, hsQ, hwsP, hwsQ, -, hM, -⟩ := h
  exact ⟨⟨hg.scr, hg.hdr, hsP, hsQ, ⟨hwsP.link, hwsP.hdr.hw, hwsP.hdr.harr⟩, ⟨hwsQ.link, hwsQ.hdr.hw, hwsQ.hdr.harr⟩,
    ⟨m0, hM⟩, a1, a2, b1, b2, b3, c1, c2, c3, c4⟩, hg.x0⟩

theorem CK.good {p : ChecksPub} {t : State} (h : CK p t) (hdi : t.gpr .x0 = p.B) : Good t p.B p.Z p.w p.minv :=
  ⟨h.1, hdi, h.2.1⟩

theorem CK.slotZ {p : ChecksPub} {t : State} (h : CK p t) : slot p.w 8 ≤ p.Z := by
  obtain ⟨-, -, h28, hlo, hop, hoq, -⟩ := h.bounds; omega_arith

/-- Into a workspace from the modulus' (`enterP`, `enterQ`), or back (`leave`). -/
theorem CK.move {p : ChecksPub} {s : State} (h : CK p s) {X : Addr} {i : Nat} {A' : Addr}
    (hdi : s.gpr .x0 = X) (hi : i < 32) (hl : InRegions (s.rd ++ s.wr) (off X (8 * i)) 8)
    (hw : word s.mem X (8 * i) = A') :
    WP isa (.block [ldh .x0 i]) s (CKr (fun _ => A') p) :=
  WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = A' ∧ t.mem = s.mem)
    (by brun [hdi, hdr_enc hi, hl, hw]) rfl rfl rfl) fun t ⟨⟨hdi', hm⟩, k⟩ => ⟨h.mem hm k, hdi'⟩

theorem CK.ldB {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 :=
  h.1.ld (by have := h.slotZ; have := hdr_lt_slot p.w 8 hi; omega_arith)

theorem CK.ldP {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off (off p.B p.op) (8 * i)) 8 := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 := hdr_lt_slot p.wp 8 hi
  exact (h.1.sub (o := p.op) (n := slot p.wp 8) (by omega_arith) (by omega_arith)).ld (by omega_arith)

theorem CK.ldP' {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off p.B (p.op + 8 * i)) 8 := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 := hdr_lt_slot p.wp 8 hi
  exact h.1.ld (by omega_arith)

/-- `p`'s workspace. -/
abbrev ckP (p : ChecksPub) : Addr := off p.B p.op
/-- `q`'s workspace. -/
abbrev ckQ (p : ChecksPub) : Addr := off p.B p.oq

theorem enterP_ck {p : ChecksPub} {s : State} (h : CKr (·.B) p s) : WP isa (.block [enterP]) s (CKr ckP p) :=
  h.1.move (X := p.B) (i := sWsP) h.2 (by decide) (h.1.ldB (by decide)) h.1.2.2.1

theorem enterQ_ck {p : ChecksPub} {s : State} (h : CKr (·.B) p s) : WP isa (.block [enterQ]) s (CKr ckQ p) :=
  h.1.move (X := p.B) (i := sWsQ) h.2 (by decide) (h.1.ldB (by decide)) h.1.2.2.2.1

theorem leaveP_ck {p : ChecksPub} {s : State} (h : CKr ckP p s) : WP isa (.block [leave]) s (CKr (·.B) p) :=
  h.1.move (X := ckP p) (i := sLink) h.2 (by decide) (h.1.ldP (by decide)) h.1.2.2.2.2.1.1

/-! ## `p q` -/

theorem CKr.rows {p : ChecksPub} {s : State} (h : CKr (·.B) p s) :
    RowsPre Public.aN ⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ s := by
  obtain ⟨⟨hs, hH, hWP, hWQ, hP, hQ, -, -, -, hlo, hop, hoq, -⟩, hdi⟩ := h
  exact ⟨hs, hdi, hH.harr _ (by decide), hWP, hWQ, by rw [← word_off]; exact hP.2.1,
    by rw [← word_off]; exact hQ.2.1, by rw [← word_off, hP.2.2 _ (by decide), off_off],
    by rw [← word_off, hQ.2.2 _ (by decide), off_off], by decide, hlo, by dsimp only; omega_arith, by dsimp only; omega_arith⟩

theorem pq_ct : RelCT isa (Two (CKr (·.B))) (seqs pqProduct) (Two (CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · rw [pqProduct_eq]
    refine RelCT.seqs_append (by simp [zeroAccs]) (by simp) (RelCT.seq (two_post (Ψ := CKr (·.B))
      (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun p s h => ⟨p.minv, h.1.good h.2, h.1.slotZ⟩)
        zeroAccs_ct) fun p s h => ?_) ?_)
    · obtain ⟨hn, -, h28, -⟩ := h.1.bounds
      exact WP.mono (zeroAccs_ok (h.1.good h.2) h.1.slotZ (by omega_arith)) fun t ⟨_, ho, k⟩ =>
        ⟨h.1.acc ho k, (k.gpr .x0 (by decide)).trans h.2⟩
    · exact two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ : RowsPub))
        (fun p s h => h.rows) (rows_ct (by taint_decide))
  · obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, a3, a4⟩ := h.1.bounds
    have hR := h.rows
    exact WP.mono (pqProduct_ok (h.1.good h.2) (by omega_arith) hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2.1
      hR.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.2.1 hlo hop hoq (show 1 ≤ p.wp by omega_arith) a2 (show 1 ≤ p.wq by omega_arith) a4)
      fun t ⟨_, ho, k⟩ => ⟨h.1.acc ho k, (k.gpr .x0 (by decide)).trans h.2⟩

/-! ## `p q = n` -/

/-- `eqCheck`'s registers. -/
def EQ1 (p : ChecksPub) (t : State) : Prop :=
  t.gpr .x0 = p.B ∧ t.gpr .x12 = BitVec.ofNat 64 p.w ∧ t.gpr .x14 = BitVec.ofNat 64 p.w ∧
    t.gpr .x16 = off p.B (slot p.w Public.aAcc) ∧ t.gpr .x17 = off p.B (slot p.w Public.aN)

theorem eq_ct : RelCT isa (Two (CKr (·.B))) (seqs eqCheck) (Two (CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · unfold eqCheck
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := EQ1) [.x0] (pins_ckr _) (by taint_decide) fun p s h => ?_)
      (two_taint [.x0, .x12, .x14, .x16, .x17] (pins_of (fun (p : ChecksPub) r => if r = .x0 then p.B else
        if r = .x12 then BitVec.ofNat 64 p.w else if r = .x14 then BitVec.ofNat 64 p.w else
        if r = .x16 then off p.B (slot p.w Public.aAcc) else off p.B (slot p.w Public.aN)) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2.1
          · exact h.2.2.2.2) (by taint_decide))
    obtain ⟨hk, hdi⟩ := h
    have hH := hk.2.1
    exact WP.mono (WP.keep [.x9, .x12, .x14, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 p.w ∧
        t.gpr .x14 = BitVec.ofNat 64 p.w ∧ t.gpr .x16 = off p.B (slot p.w Public.aAcc) ∧
        t.gpr .x17 = off p.B (slot p.w Public.aN))
      (by brun [hdi, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show Public.aAcc < 8 by decide)),
        hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hk.ldB (i := sW) (by decide),
        hk.ldB (i := sArr Public.aAcc) (by decide), hk.ldB (i := sArr Public.aN) (by decide), hH.hw,
        hH.harr Public.aAcc (by decide), hH.harr Public.aN (by decide)]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨h', k⟩ => ⟨(k.gpr .x0 (by decide)).trans hdi, h'⟩
  · obtain ⟨hn, a1, a2, -⟩ := h.1.bounds
    obtain ⟨c, hM⟩ := h.1.2.2.2.2.2.2.1
    exact WP.mono (eqCheck_ok (h.1.good h.2) h.1.slotZ (by omega_arith) (by omega_arith)) fun t ⟨hM', ho, k⟩ =>
      ⟨h.1.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr .x0 (by decide)).trans h.2⟩

/-! ## `qInv < p` -/

/-- `qinvCheck`'s registers. -/
def QI1 (p : ChecksPub) (t : State) : Prop :=
  CKr ckP p t ∧ t.gpr .x12 = BitVec.ofNat 64 p.wp ∧ t.gpr .x14 = BitVec.ofNat 64 p.wp ∧
    t.gpr .x16 = off p.B (p.op + slot p.wp aChunk) ∧ t.gpr .x17 = off p.B (p.op + slot p.wp Public.aN) ∧
    t.c = true

theorem qinvCheck_eq : qinvCheck = [
    .block [ldh .x12 sW, ldh .x16 (sArr aChunk), ldh .x17 (sArr Public.aN), movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7],
    cmpLoop,
    .block ((borrowMask ++ [ldh .x5 sLink]) ++ ([ldw .x3 .x5 Public.sMask, .logic .and .x .x15 .x15 .x3,
      stw .x15 .x5 Public.sMask] : List Instr))] := rfl

theorem qinv_ct : RelCT isa (Two (CKr ckP)) (seqs qinvCheck) (Two (CKr ckP)) := by
  refine two_post ?_ fun p s h => ?_
  · rw [qinvCheck_eq]
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := QI1) [.x0] (pins_ckr _) (by taint_decide) fun p s h => ?_)
      (RelCT.seq (two_post (Ψ := CKr ckP) (two_taint [.x12, .x14, .x16, .x17] (pins_of (fun (p : ChecksPub) r =>
        if r = .x12 then BitVec.ofNat 64 p.wp else if r = .x14 then BitVec.ofNat 64 p.wp else
        if r = .x16 then off p.B (p.op + slot p.wp aChunk) else off p.B (p.op + slot p.wp Public.aN))
        fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2.1
          · exact h.2.2.2.2.1) (by taint_decide)) fun p s h => ?_)
      (RelCT.block_append (RelCT.seq
        (two_piece (Ψ := fun p t => t.gpr .x5 = p.B) [.x0] (pins_ckr _) (by taint_decide) fun p s h => ?_)
        (two_taint [.x5] (pins_of (fun p _ => p.B) fun p s h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)))))
    · obtain ⟨hk, hdi⟩ := h
      have hF := hk.2.2.2.2.1
      have h0 : s.gpr .x0 = off p.B p.op := hdi
      have hw : word s.mem p.B (p.op + 8 * sW) = BitVec.ofNat 64 p.wp := by rw [← word_off]; exact hF.2.1
      have ha : ∀ j < 8, word s.mem p.B (p.op + 8 * sArr j) = off p.B (p.op + slot p.wp j) := fun j hj => by
        rw [← word_off, hF.2.2 j hj, off_off]
      exact WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 p.wp ∧
          t.gpr .x14 = BitVec.ofNat 64 p.wp ∧ t.gpr .x16 = off p.B (p.op + slot p.wp aChunk) ∧
          t.gpr .x17 = off p.B (p.op + slot p.wp Public.aN) ∧ t.c = true ∧ t.mem = s.mem)
        (by brun [h0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aChunk < 8 by decide)),
          hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hk.ldP' (i := sW) (by decide),
          hk.ldP' (i := sArr aChunk) (by decide), hk.ldP' (i := sArr Public.aN) (by decide), hw,
          ha aChunk (by decide), ha Public.aN (by decide)])
        (by decide) (by decide) (by decide +kernel))
        fun t ⟨⟨a, b, c, d, e, hm⟩, k⟩ => ⟨⟨hk.mem hm k, (k.gpr .x0 (by decide)).trans hdi⟩, a, b, c, d, e⟩
    · obtain ⟨⟨hk, hdi⟩, h12, h14, h16, h17, hc⟩ := h
      obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
      have := slot_le (w := p.wp) (show aChunk < 8 by decide)
      have := slot_le (w := p.wp) (show Public.aN < 8 by decide)
      exact WP.mono (cmpLoop_ok hk.1 h16 h17 h14 hc (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
        fun t ⟨_, hm, k⟩ => ⟨hk.mem hm k, (k.gpr .x0 (by decide)).trans hdi⟩
    · obtain ⟨hk, hdi⟩ := h
      have h0 : s.gpr .x0 = off p.B p.op := hdi
      have hL : word s.mem p.B (p.op + 8 * sLink) = p.B := by rw [← word_off]; exact hk.2.2.2.2.1.1
      exact WP.mono (WP.keep [.x4, .x5, .x15] (Q := fun t => t.gpr .x5 = p.B)
        (by brun [borrowMask, h0, hdr_enc (show sLink < 32 by decide), hk.ldP' (i := sLink) (by decide), hL])
        (by decide) (by decide) (by decide +kernel))
        fun t h => h.1
  · obtain ⟨hk, hdi⟩ := h
    obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
    obtain ⟨c, hM⟩ := hk.2.2.2.2.2.2.1
    have hF := hk.2.2.2.2.1
    exact WP.mono (qinvCheck_ok hk.1 hdi (hdr_any hF.2.1 hF.2.2) (by omega_arith)
      (by unfold Public.sMask sFn; unfold slot hdrBytes at hlo; omega_arith) (by omega_arith) (by omega_arith) hF.1)
      fun t ⟨hM', ho, k⟩ => ⟨hk.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr .x0 (by decide)).trans hdi⟩

/-! ## The fixes -/

theorem pfRanges_le (wx : Nat) : ∀ r ∈ pfRanges wx, 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  have := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have := slot_le (w := wx) (show Public.aN < 8 by decide)
  have := slot_le (w := wx) (show Public.aOne < 8 by decide)
  intro r hr
  simp only [pfRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega_arith

theorem CK.sub {p : ChecksPub} {s : State} {o wx : Nat} (hk : CK p s) (hdi : s.gpr .x0 = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ p.Z) :
    ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z o p.w wx minv ∧ word s.mem p.B (8 * Public.sMask) = mask c := by
  obtain ⟨hs, hH, -, -, -, -, ⟨c, hM⟩, -⟩ := hk
  exact ⟨_, c, ⟨hs, hdi, hdr_any hF.2.1 hF.2.2, hF.1, hH.hw, hH.harr, hlo, hi_of_wsTab hhi⟩, hM⟩

theorem CK.pf {p : ChecksPub} {s : State} {o wx : Nat} (hk : CK p s) (hdi : s.gpr .x0 = off p.B o)
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
    (hk.2.2.2.2.2.1.frm f' (fun r h => Or.inr (by have := hr' r h; omega_arith)) (by omega_arith)) k, hc'.x0⟩

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
    ⟨hc'.link, hc'.hdr.hw, hc'.hdr.harr⟩ k, hc'.x0⟩

end VG.Proof.Bignum.AArch64

end

end

/-!
# RSA with the CRT on AArch64: constant time of the setup and the checks

The claims of `CrtCTDefs.lean` for the primes' setup: the loads
(`loadArr_ct_pN`, `loadArr_ct_pI`, `loadArr_ct_qN`, in `CrtCTSetupLoad.lean`),
`primesSetup` (`setup_ct`, in `CrtCTSetupWs.lean`), and `checks`
(`checks_ct`) and `checksGiven` (`checksGiven_ct`), from their pieces
(`CrtCTSetupChk.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem leaveEnterQ_ck : RelCT isa (Two (CKr ckP)) (.block [leave, enterQ]) (Two (CKr ckQ)) :=
  RelCT.block_append (l₁ := ([leave] : List Instr))
    (RelCT.seq (two_piece (Ψ := CKr (·.B)) [.x0] (pins_ckr _) (by taint_decide) fun p s h => leaveP_ck h)
      (two_piece [.x0] (pins_ckr _) (by taint_decide) fun p s h => enterQ_ck h))

/-- `checksGiven`, from the checks' state. -/
theorem checksGiven_ck : RelCT isa (Two (CKr (·.B))) (seqs checksGiven) fun _ _ => True := by
  unfold checksGiven
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (two_piece [.x0] (pins_ckr _)
    (by taint_decide) fun p s h => enterP_ck h) ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq qinv_ct ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq fixP_ct ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq leaveEnterQ_ck ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq fixQ_ct ?_)
  exact two_taint [.x0] (pins_ckr _) (by taint_decide)

theorem checksGiven_ct : ChecksCTOf checksGiven := two_map id (fun _ _ h => h.ck) checksGiven_ck

theorem checks_ct : ChecksCT := by
  unfold ChecksCT ChecksCTOf checks
  simp only [List.append_assoc]
  refine two_map id (fun _ _ h => h.ck) ?_
  refine RelCT.seqs_append (by decide) (by simp [checksGiven]) (RelCT.seq pq_ct ?_)
  exact RelCT.seqs_append (by decide) (by simp [checksGiven]) (RelCT.seq eq_ct checksGiven_ck)

end VG.Proof.Bignum.AArch64

end

end

/-!
# RSA with the CRT on AArch64: `n`'s setup in constant time

`nSetup` is `pcLoad`, `nInput`, `r2StepsPub` and `c R mod n` (`nSetup_ct`),
each constant time for its correctness lemma's hypotheses, which the one
before it gives, as `nPart_ok` runs them; `-n⁻¹` is the same in both runs,
as `n` is.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- After `pcLoad`: `nInput_ok`'s hypotheses and what `r2_ok` needs. -/
def NS1 (p : CrtPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (xb : List Byte), Good t p.B p.Z p.w minv ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word t.mem p.B (8 * Public.sK) = BitVec.ofNat 64 p.k ∧ word t.mem p.B (8 * Public.sIn) = p.ip ∧
    Src t p.B p.Z p.ip xb ∧ xb.length = p.k ∧ wv t.mem p.B (slot p.w Public.aN) p.w = p.N ∧
    ((word t.mem p.B (slot p.w Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧ p.N % 2 = 1 ∧
    2 ^ (64 * (p.w - 1)) ≤ p.N

/-- After `nInput`: `r2_ok`'s hypotheses, for some `-n⁻¹`. -/
def NS2 (p : CrtPub) (t : State) : Prop := ∃ minv : BitVec 64, R2Pre ⟨⟨p.B, p.Z, p.w, minv⟩, p.N⟩ t

theorem stage0_pcl {p : CrtPub} {s : State} (h : Stage R0 p s) : PcL ⟨p.B, p.Z, p.k, p.op, p.np, p.nb⟩ s := by
  obtain ⟨σ, xb, _, _, _, _, _, h, hv, rfl⟩ := h
  have hZq := h.z
  exact ⟨h.scr, h.x0, show slot ((p.k + 7) / 8) 8 ≤ p.Z by unfold offQ at hZq; omega_arith, h.k1, h.k2, h.hK, h.hN,
    h.n, h.nl, hv⟩

theorem ns1_ok {p : CrtPub} {s : State} (h : Stage R0 p s) : WP isa (seqs pcLoad) s (NS1 p) := by
  obtain ⟨σ, xb, _, _, _, _, _, h, hv, rfl⟩ := h
  obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ at hZq; omega_arith
  have hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ slot ((p.k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ p.Z :=
    fun h' r hr => Nat.le_trans (h' r hr) hZ
  refine WP.mono (pcLoad_ok h.scr h.x0 hZ (by omega_arith) (by omega_arith) h.hK h.hN h.n h.nl hodd)
    fun t₁ ⟨minv, hg₁, hn₁, hi₁, f₁, k₁⟩ => ?_
  have f₁' : Frm p.B (setupRanges p.w) s.mem t₁.mem := f₁.mono (by simp [pcLoadRanges, setupRanges, loadRanges])
  have hh₁ := HFix.of_frm f₁' (keepsHdr_setupRanges _)
  exact ⟨minv, xb, hg₁, hZ, hk1, hk2, by rw [hh₁ _ (by decide) (by decide)]; exact h.hK,
    by rw [hh₁ _ (by decide) (by decide)]; exact h.hIn, h.x.congrK (InScr.of_frm f₁' (hZs (setupRanges_le _))) k₁,
    h.xl, hn₁, hi₁, hodd, hlo⟩

theorem ns2_ok {p : CrtPub} {s : State} (h : NS1 p s) : WP isa (seqs nInput) s (NS2 p) := by
  obtain ⟨minv, xb, hg, hZ, hk1, hk2, hK, hIn, hx, hxl, hn, hi, hodd, hlo⟩ := h
  unfold NS2 R2Pre GoodL
  simp only [CrtPub.w] at *
  have hnw := hg.scr.nowrap
  refine WP.mono (nInput_ok hg hZ hk1 hk2 hK hIn hx hxl hn) fun t ⟨hg₂, _, _, _, f₂, _⟩ => ?_
  have hN₂ : wv t.mem p.B (slot ((p.k + 7) / 8) Public.aN) ((p.k + 7) / 8) = p.N := by
    rw [f₂.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := slot_le (w := (p.k + 7) / 8) (show Public.aN < 8 by decide)
      have := slot_sep (w := (p.k + 7) / 8) (show Public.aN ≠ Public.aX by decide)
      have := slot_sep (w := (p.k + 7) / 8) (show Public.aN ≠ Public.aOne by decide)
      have := hdr_lt_slot ((p.k + 7) / 8) Public.aN (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl <;> simp only [Public.sMask, sFn] <;> omega_arith)
      (by have := slot_le (w := (p.k + 7) / 8) (show Public.aN < 8 by decide); omega_arith)]; exact hn
  have hI₂ : ((word t.mem p.B (slot ((p.k + 7) / 8) Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := slot_le (w := (p.k + 7) / 8) (show Public.aN < 8 by decide)
      have := slot_sep (w := (p.k + 7) / 8) (show Public.aN ≠ Public.aX by decide)
      have := slot_sep (w := (p.k + 7) / 8) (show Public.aN ≠ Public.aOne by decide)
      have := hdr_lt_slot ((p.k + 7) / 8) Public.aN (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl <;> simp only [Public.sMask, sFn] <;> omega_arith)
      (by have := slot_le (w := (p.k + 7) / 8) (show Public.aN < 8 by decide); omega_arith)]; exact hi
  exact ⟨minv, ⟨hg₂, hZ⟩, by omega_arith, by omega_arith, hN₂, hI₂, hodd, hlo⟩

/-- `-n⁻¹` is the same in runs that agree on `n`. -/
theorem r2_minv {B : Addr} {Z w : Nat} {N : Nat} {m₁ m₂ : BitVec 64} {s₁ s₂ : State}
    (h₁ : R2Pre ⟨⟨B, Z, w, m₁⟩, N⟩ s₁) (h₂ : R2Pre ⟨⟨B, Z, w, m₂⟩, N⟩ s₂) : m₁ = m₂ := by
  obtain ⟨-, hw, -, n₁, i₁, hodd, -⟩ := h₁
  obtain ⟨-, -, -, n₂, i₂, -, -⟩ := h₂
  have e : ∀ {t : State}, wv t.mem B (slot w Public.aN) w = N →
      (word t.mem B (slot w Public.aN)).toNat = N % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ (show 1 ≤ w by simp only at hw; omega_arith), h]
  rw [e n₁] at i₁
  rw [e n₂] at i₂
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) i₁ i₂

/-- `nHead` leaks the same in runs that agree on the public data. -/
theorem nHead_ct (M : Mont) :
    RelCT isa (Two (Stage R0)) (seqs (nHead M.mm)) (Two fun (p : CrtPub) t => GoodW ⟨p.B, p.Z, p.w⟩ t) := by
  rw [nHead_eq]
  refine RelCT.seqs_append (by simp [pcLoad, pcLoadWith]) (by simp [nInput]) (RelCT.seq (R := Two NS1) (two_post
    (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.k, p.op, p.np, p.nb⟩ : PcPub)) (fun _ _ h => stage0_pcl h) pcLoad_ct)
    fun _ _ h => ns1_ok h) ?_)
  refine RelCT.seqs_append (by simp [nInput]) (by simp [r2StepsPub]) (RelCT.seq (R := Two NS2) (two_post
    (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.k, p.ip⟩ : NIPub))
      (fun _ _ ⟨minv, xb, hg, hZ, hk1, hk2, hK, hIn, hx, hxl, _⟩ => ⟨minv, xb, hg, hZ, hk1, hk2, hK, hIn, hx, hxl⟩)
      nInput_ct) fun _ _ h => ns2_ok h) ?_)
  refine two_post
    ((r2Pub_ct M).mono (fun _ _ h => two_bind (fun (p : CrtPub) s₁ s₂ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩ => by
      obtain rfl := r2_minv h₁ h₂
      exact ⟨_, h₁, h₂⟩) h) fun _ _ h => h)
    fun p s hh => ?_
  obtain ⟨minv, ⟨hg, hZ⟩, hw, hw30, hn, hinv, hodd, hlo⟩ := hh
  exact WP.mono (r2Pub_ok M hg hZ hw hw30 hn hinv hodd hlo) fun t ⟨hg', _⟩ => ⟨minv, hg', hZ⟩

/-- `n`'s setup leaks the same in runs that agree on the public data. -/
theorem nSetup_ct (M : Mont) : RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) fun _ _ => True := by
  rw [show nSetup M.mm = nHead M.mm ++ [M.mm Public.aXm Public.aX Public.aR2] from rfl]
  refine RelCT.seqs_append (by simp [nHead]) (by simp) (RelCT.seq (nHead_ct M) ?_)
  simp only [seqs]
  exact two_map (fun p : CrtPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun _ _ h => h) (M.ct (by unfold MmUse; decide))

end VG.Proof.Bignum.AArch64

end

end

/-! ### `Bignum.AArch64.CrtEntry`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: the entry

`entry` stores the arguments (the pointers and lengths among them that
`main` reads, some from the stack) in the header of the working space, and
leaves its base in `x0` (`crtEntry_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem crtEntry_eq : entry = ([.ldrSp .x8 64, stw .x0 .x8 Public.sOut, stw .x2 .x8 Public.sN,
    stw .x3 .x8 Public.sK, stw .x4 .x8 Public.sIn, stw .x6 .x8 sP, stw .x7 .x8 sPlen] : List Instr) ++
    (hdrPairs [(0, sQ), (1, sQlen), (2, sDp), (4, sDq), (6, sQinv)] ++ ([mov .x0 .x8] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def crtEntryMemA (m : Mem) (B : Addr) (vo vn vk vi vp vpl : BitVec 64) : Mem :=
  (((((m.writeW (off B (8 * Public.sOut)) vo).writeW (off B (8 * Public.sN)) vn).writeW
    (off B (8 * Public.sK)) vk).writeW (off B (8 * Public.sIn)) vi).writeW (off B (8 * sP)) vp).writeW
    (off B (8 * sPlen)) vpl

/-- The header after the entry's stores. -/
def crtEntryMem (m : Mem) (B : Addr) (vo vn vk vi vp vpl vq vql vdp vdq vqi : BitVec 64) : Mem :=
  (((((crtEntryMemA m B vo vn vk vi vp vpl).writeW (off B (8 * sQ)) vq).writeW
    (off B (8 * sQlen)) vql).writeW (off B (8 * sDp)) vdp).writeW (off B (8 * sDq)) vdq).writeW
    (off B (8 * sQinv)) vqi

theorem crtEntryMemA_outside (m : Mem) (B : Addr) (vo vn vk vi vp vpl : BitVec 64) :
    Outside B 0 (8 * 32) m (crtEntryMemA m B vo vn vk vi vp vpl) := by
  unfold crtEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem crtEntryMem_facts (m : Mem) (B : Addr) (vo vn vk vi vp vpl vq vql vdp vdq vqi : BitVec 64) :
    let m' := crtEntryMem m B vo vn vk vi vp vpl vq vql vdp vdq vqi
    word m' B (8 * Public.sOut) = vo ∧ word m' B (8 * Public.sN) = vn ∧ word m' B (8 * Public.sK) = vk ∧
    word m' B (8 * Public.sIn) = vi ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sPlen) = vpl ∧
    word m' B (8 * sQ) = vq ∧ word m' B (8 * sQlen) = vql ∧ word m' B (8 * sDp) = vdp ∧
    word m' B (8 * sDq) = vdq ∧ word m' B (8 * sQinv) = vqi ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' crtEntryMem crtEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 8) in `x0`. -/
theorem crtEntry_ok {s : State} {B : Addr} (hB : stackArg s 8 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 10, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * Public.sOut) = s.gpr .x0 ∧ word t.mem B (8 * Public.sN) = s.gpr .x2 ∧
      word t.mem B (8 * Public.sK) = s.gpr .x3 ∧ word t.mem B (8 * Public.sIn) = s.gpr .x4 ∧
      word t.mem B (8 * sP) = s.gpr .x6 ∧ word t.mem B (8 * sPlen) = s.gpr .x7 ∧
      word t.mem B (8 * sQ) = stackArg s 0 ∧ word t.mem B (8 * sQlen) = stackArg s 1 ∧
      word t.mem B (8 * sDp) = stackArg s 2 ∧ word t.mem B (8 * sDq) = stackArg s 4 ∧
      word t.mem B (8 * sQinv) = stackArg s 6 ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.x0, .x8, .x9] s t := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = B := hB
  have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := ha 8 (by decide)
  have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
  rw [crtEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧
      t.mem = crtEntryMemA s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6) (s.gpr .x7)) ?_
      (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_
  · brun [stw, exec_ldrSp ho ha8, hB', hdr_enc (show Public.sOut < 32 by decide),
      hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
      hdr_enc (show Public.sIn < 32 by decide), hdr_enc (show sP < 32 by decide),
      hdr_enc (show sPlen < 32 by decide), hw Public.sOut (by decide), hw Public.sN (by decide),
      hw Public.sK (by decide), hw Public.sIn (by decide), hw sP (by decide), hw sPlen (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hdrPairs_ok _ t₁ ?_ h8 k₁.sp k₁.rd k₁.wr
    (by rw [hm₁]; exact crtEntryMemA_outside _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h8₂ : t₂.gpr .x8 = B := (k₂.gpr .x8 (by decide)).trans h8
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = t₂.mem) (by brun [h8₂])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = crtEntryMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6)
      (s.gpr .x7) (stackArg s 0) (stackArg s 1) (stackArg s 2) (stackArg s 4) (stackArg s 6) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho'⟩ :=
    crtEntryMem_facts s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6) (s.gpr .x7)
      (stackArg s 0) (stackArg s 1) (stackArg s 2) (stackArg s 4) (stackArg s 6)
  exact ⟨h0, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho', ((k₁.trans k₂).trans k₃).mono (by decide)⟩

end VG.Proof.Bignum.AArch64

end

end


/-!
# RSA with the CRT on AArch64: correctness

`code`, from a state its contract allows, writes `privateCrt` of its inputs,
against `crtA` (`Proof/Rsa/AArch64/PrivCallees.lean`),
which states the shared contract's precondition on the registers and the
stack.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Rsa.AArch64 (crtA)

/-! ## The precondition, as `main` uses it -/

theorem stackArgAddr_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.zero_add]

theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.zero_add]

/-- What `code` uses of its contract's precondition, for the working space
`B` (stack argument 8) of `Z` bytes, `n`'s length `k` and the primes'
lengths (`x7` and stack argument 1). -/
structure CrtCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .x3).toNat
  hk2 : (s.gpr .x3).toNat ≤ 1024
  hpl1 : 1 ≤ (s.gpr .x7).toNat
  hpl2 : (s.gpr .x7).toNat < (s.gpr .x3).toNat
  hql1 : 1 ≤ (stackArg s 1).toNat
  hql2 : (stackArg s 1).toNat < (s.gpr .x3).toNat
  hZ : 128 * (s.gpr .x3).toNat + 256 ≤ (stackArg s 9).toNat * 8
  hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8)
  ha : ∀ j < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 10, ∀ m', Outside (stackArg s 8) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  hnb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x2)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  hxb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x4)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x3).toNat)
  hpb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x6)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
  hqb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  hdpb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 2)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat)
  hdqb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 4)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
  hqib : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 6)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat)
  hout : ∀ j < (s.gpr .x3).toNat, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .x3).toNat,
    (stackArg s 9).toNat * 8 ≤ ofs (stackArg s 8) (s.gpr .x0 + BitVec.ofNat 64 j)

theorem crtCtx_of {s : State} (h : crtA.pre s) : CrtCtx s := by
  simp only [crtA] at h
  sig_split h
  rename_i hsp hrd hwr dOn dOi dOp dOq dOdp dOdq dOqi dOs dOa dns dis dps dqs ddps ddqs dqis dsa wO
    wN wI wP wQ wDp wDq wQi wS hk hol hil hpl1 hpl2 hql1 hql2 hdpl hqil hdql
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 80⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hpl1, hpl2, hql1, hql2, by omega_arith, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 80) (by omega_arith) (by omega_arith))
      rw [← stackArgAddr_add s j b] at this; omega_arith)),
    src_of_region (by rw [hrd]; simp) (by omega_arith) dns,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega_arith) (by rw [← hil]; exact dis),
    src_of_region (by rw [hrd]; simp) (by omega_arith) dps,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dqs,
    src_of_region (by rw [hrd, ← hdpl]; simp) (by omega_arith) (by rw [← hdpl]; exact ddps),
    src_of_region (by rw [hrd, ← hdql]; simp) (by omega_arith) (by rw [← hdql]; exact ddqs),
    src_of_region (by rw [hrd, ← hqil]; simp) (by omega_arith) (by rw [← hqil]; exact dqis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self, contains_byte _ (by omega_arith) (by omega_arith)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega_arith) (by omega_arith))⟩

/-- After `entry`, from `s`. -/
structure CrtHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 8) ((stackArg s 9).toNat * 8)
  x0 : t.gpr .x0 = stackArg s 8
  hO : word t.mem (stackArg s 8) (8 * Public.sOut) = s.gpr .x0
  hN : word t.mem (stackArg s 8) (8 * Public.sN) = s.gpr .x2
  hK : word t.mem (stackArg s 8) (8 * Public.sK) = BitVec.ofNat 64 (s.gpr .x3).toNat
  hIn : word t.mem (stackArg s 8) (8 * Public.sIn) = s.gpr .x4
  hP : word t.mem (stackArg s 8) (8 * sP) = s.gpr .x6
  hPl : word t.mem (stackArg s 8) (8 * sPlen) = BitVec.ofNat 64 (s.gpr .x7).toNat
  hQ : word t.mem (stackArg s 8) (8 * sQ) = stackArg s 0
  hQl : word t.mem (stackArg s 8) (8 * sQlen) = BitVec.ofNat 64 (stackArg s 1).toNat
  hDp : word t.mem (stackArg s 8) (8 * sDp) = stackArg s 2
  hDq : word t.mem (stackArg s 8) (8 * sDq) = stackArg s 4
  hQi : word t.mem (stackArg s 8) (8 * sQinv) = stackArg s 6
  inScr : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem
  keep : Keep [.x0, .x8, .x9] s t

/-- `entry`. -/
theorem crtHead_ok {s : State} (c : CrtCtx s) : WP isa (.block entry) s (CrtHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 8) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  refine WP.mono (crtEntry_ok rfl hw c.ha c.hsep) fun t ⟨h0, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq,
    hQi, ho, k⟩ => ?_
  exact ⟨c.hs.congr k.wr, h0, hO, hN, by rw [hK, ofNat_toNat64], hI, hP, by rw [hPl, ofNat_toNat64], hQ,
    by rw [hQl, ofNat_toNat64], hDp, hDq, hQi, InScr.of_outside ho (by omega_arith), k⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem crtPre_of {s t₁ t : State} (c : CrtCtx s) (h : CrtHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t) :
    CrtPre t (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x3).toNat (s.gpr .x0) (s.gpr .x2)
      (s.gpr .x4) (s.gpr .x6) (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 6)
      (s.gpr .x7).toNat (stackArg s 1).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat) := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  have h0 : t.gpr .x0 = stackArg s 8 := (k.gpr .x0 (by decide)).trans h.x0
  have hz : offQ (((s.gpr .x3).toNat + 7) / 8) (s.gpr .x7).toNat + slot (wsWords (stackArg s 1).toNat) 8 +
      wsTab (wsWords (stackArg s 1).toNat) ≤ (stackArg s 9).toNat * 8 :=
    crt_room hk1 hpl2 hql2 hZ
  exact
    { scr := h.scr.congr k.wr, x0 := h0, z := hz, zk := (by omega_arith), k1 := hk1, k2 := hk2, hO := (by rw [hm]; exact h.hO),
      hN := (by rw [hm]; exact h.hN), hK := (by rw [hm]; exact h.hK), hIn := (by rw [hm]; exact h.hIn),
      hP := (by rw [hm]; exact h.hP), hPl := (by rw [hm]; exact h.hPl), hQ := (by rw [hm]; exact h.hQ),
      hQl := (by rw [hm]; exact h.hQl), hDp := (by rw [hm]; exact h.hDp), hDq := (by rw [hm]; exact h.hDq),
      hQi := (by rw [hm]; exact h.hQi), n := c.hnb.congrK hi kk, x := c.hxb.congrK hi kk,
      p := c.hpb.congrK hi kk, q := c.hqb.congrK hi kk, dp := c.hdpb.congrK hi kk, dq := c.hdqb.congrK hi kk,
      qi := c.hqib.congrK hi kk, nl := bytesAt_length _ _ _, xl := bytesAt_length _ _ _,
      pbl := bytesAt_length _ _ _, qbl := bytesAt_length _ _ _, dpl := bytesAt_length _ _ _,
      dql := bytesAt_length _ _ _, qil := bytesAt_length _ _ _, pl1 := c.hpl1, pl2 := hpl2, ql1 := c.hql1,
      ql2 := hql2, out := (fun j hj => by rw [kk.wr]; exact c.hout j hj), outSep := c.houts }

/-- `fail`: zeros to `out`, and 0 returned. -/
theorem crtFail_ok {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib) :
    WP isa Precomputed.fail s fun t => MainPost s t B Z k op 0 false := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have h8 : 8 * 32 ≤ Z := by
    have := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
    have := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
    unfold offQ at hZq; omega_arith
  refine WP.mono (pdFail_ok h.scr h.x0 h8 (by omega_arith) (by omega_arith) h.hO h.hK h.out)
    fun t ⟨hb, hx, hfr, k⟩ => ⟨by rw [i2osp_zero']; exact hb, hx, fun x _ hx' => hfr x hx', k⟩

/-- What `code` leaves, from what `fail` or `main` leaves. -/
theorem crtCode_fin {s t₁ t₂ t : State} (h : CrtHeadPost s t₁)
    (k : Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t₂) {r : Nat} {cb : Bool}
    (hp : MainPost t₂ t (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x3).toNat (s.gpr .x0) r cb)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = true →
      (cb = true ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x3).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) *
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)) ∧
      r = if cb then crtResult (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x3).toNat)) else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = false → cb = false ∧ r = 0) :
    abiPreserved s t ∧ crtA.post s t :=
  ⟨abiPreserved_of_keep (((h.keep.trans k).trans hp.keep).mono (by decide)),
    crtWritten_of (bytesAt_length _ _ _) hp.bytes hp.x0 hc hf⟩

end VG.Proof.Bignum.AArch64
