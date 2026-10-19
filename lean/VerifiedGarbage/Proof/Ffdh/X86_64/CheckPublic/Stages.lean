module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Contract
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Context
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-!
# `vg_ffdh_check_public` on X86_64: the stages of a run

Every input of `vg_ffdh_check_public` is public (`CpP`). Between the pieces
of `CheckPublic.code` whose timing the constant-time proof checks, a run from
a state with the public data `p` (`CR p`) satisfies a stage of `p`
(`E1`, `CE`, `C1` … `C8`), by the pieces' correctness. Each stage fixes what
the next piece's addresses, loop counts and branches depend on.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh
open VG.Proof.MlKem.X86_64
open VG.Spec.Ffdh

/-- The public data: the working space, the lengths, the pointers, the
domain, y and the stack pointer. -/
structure CpP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  yp : Addr
  dom : List Byte
  yb : List Byte
  sp : Addr

namespace CpP

abbrev w (p : CpP) : Nat := (p.k + 7) / 8

/-- p. -/
abbrev P (p : CpP) : Nat := Spec.Rsa.os2ip (p.dom.take p.k)

/-- q's octets, for a domain with q. -/
abbrev qb (p : CpP) : List Byte := (p.dom.drop (2 * p.k)).take p.k

/-- y. -/
abbrev Y (p : CpP) : Nat := Spec.Rsa.os2ip p.yb

/-- Whether p is a valid modulus. -/
abbrev mv (p : CpP) : Bool := Spec.Rsa.modulusValid p.P p.k

/-- The front's public data. -/
abbrev d (p : CpP) : DPub := ⟨p.B, p.Z, p.k, p.dp⟩

/-- The inner workspace. -/
abbrev ws (p : CpP) : Ws := ⟨off p.B (inner p.w), slot p.w 8, p.w⟩

/-- The header slots the code reads after the entry. -/
abbrev hd (p : CpP) : List (Nat × BitVec 64) :=
  [(sDom, p.dp), (sDomLen, BitVec.ofNat 64 p.dl), (sK, BitVec.ofNat 64 p.k), (sY, p.yp)]

/-- And after `domHead`. -/
abbrev hdQ (p : CpP) : List (Nat × BitVec 64) := p.hd ++ [(sQ, p.dp + BitVec.ofNat 64 (2 * p.k))]

end CpP

/-- A state the contract allows, with the public data `p`. -/
def CR (p : CpP) (s : State) : Prop :=
  cpPre s ∧ s.gpr .rsp = p.sp ∧ s.gpr .r9 = p.B ∧ (scrLen s).toNat * 8 = p.Z ∧ (s.gpr .rdx).toNat = p.k ∧
    (s.gpr .rsi).toNat = p.dl ∧ s.gpr .rdi = p.dp ∧ s.gpr .rcx = p.yp ∧ cpDom s = p.dom ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat = p.yb

/-- What a run keeps of its start: the inputs, outside the working space,
and the permissions. -/
def Fx (p : CpP) (t : State) : Prop :=
  ∃ s, CR p s ∧ InScr p.B p.Z s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem Fx.step {p : CpP} {t u : State} (h : Fx p t) (hi : InScr p.B p.Z t.mem u.mem) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) : Fx p u :=
  let ⟨s, hs, i, r, w⟩ := h
  ⟨s, hs, i.trans hi, hrd.trans r, hwr.trans w⟩

theorem Fx.keep {p : CpP} {t u : State} (h : Fx p t) (hi : InScr p.B p.Z t.mem u.mem) {rs : List Reg}
    (k : Keep rs t u) : Fx p u := h.step hi k.2.1 k.2.2

/-- What `Fx` gives. -/
structure FxCtx (p : CpP) (t : State) : Prop where
  scr : Scr t p.B p.Z
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  dl : p.dl = 2 * p.k ∨ p.dl = 3 * p.k
  hZ : 128 * p.k + 256 ≤ p.Z
  dom : Src t p.B p.Z p.dp p.dom
  doml : p.dom.length = p.dl
  y : Src t p.B p.Z p.yp p.yb
  yl : p.yb.length = p.k

theorem Fx.ctx {p : CpP} {t : State} (h : Fx p t) : FxCtx p t := by
  obtain ⟨B, Z, k, dl, dp, yp, dom, yb, sp⟩ := p
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, hdl, hdp, hyp, hdom, hyb⟩, hi, hrd, hwr⟩ := h
  have c := cpCtx_of hpre
  have hy := c.y
  rw [c.yl] at hy hyb
  subst hB hZ hk hdl hdp hyp hdom hyb
  exact ⟨c.hs.congr hwr, c.k1, c.k2, c.dl, c.hZ, c.dom.congr hi hrd hwr, bytesAt_length _ _ _, hy.congr hi hrd hwr,
    bytesAt_length _ _ _⟩

/-! ## The entry and the check of p -/

/-- After the entry. -/
def E1 (p : CpP) (t : State) : Prop := Fx p t ∧ t.gpr .rdi = p.B ∧ Slots t.mem p.B p.hd

/-- The entry's registers. -/
def entryRegs (p : CpP) (r : Reg) : BitVec 64 :=
  if r = .rdi then p.dp else if r = .rsi then BitVec.ofNat 64 p.dl else if r = .rdx then BitVec.ofNat 64 p.k else
    if r = .rcx then p.yp else p.B

theorem cr_regs (p : CpP) (s : State) (h : CR p s) : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9], s.gpr r = entryRegs p r := by
  obtain ⟨-, -, hB, -, hk, hdl, hdp, hyp, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [entryRegs, reduceCtorEq, ↓reduceIte]
  · exact hdp
  · rw [← hdl, ofNat_toNat64]
  · rw [← hk, ofNat_toNat64]
  · exact hyp
  · exact hB

theorem cr_e1 (p : CpP) (s : State) (h : CR p s) : WP isa (.block CheckPublic.entry) s (E1 p) := by
  have c := cpCtx_of h.1
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have h' := h
  obtain ⟨-, -, hB, hZ', hk, hdl, hdp, hyp, -⟩ := h'
  have hw : ∀ i < 20, InRegions s.wr (off (s.gpr .r9) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  refine WP.mono (cpEntry_ok rfl hw) fun t ⟨h0, _, slots, ho, k⟩ => ?_
  have hD := slots (sDom, s.gpr .rdi) (by simp)
  have hL := slots (sDomLen, s.gpr .rsi) (by simp)
  have hK := slots (sK, s.gpr .rdx) (by simp)
  have hY := slots (sY, s.gpr .rcx) (by simp)
  rw [hB] at h0 hD hL hK hY ho
  rw [hZ'] at hn hZ
  refine ⟨⟨s, h, InScr.of_outside ho (by rw [← hZ']; omega), k.2.1, k.2.2⟩, h0, ?_⟩
  intro q hq
  simp only [CpP.hd, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact hD.trans hdp
  · rw [hL, ← hdl, ofNat_toNat64]
  · rw [hK, ← hk, ofNat_toNat64]
  · exact hY.trans hyp

theorem e1_dhp (p : CpP) (t : State) (h : E1 p t) : DHP p.d t := by
  obtain ⟨hx, h0, hs⟩ := h
  have c := hx.ctx
  have := c.hZ
  exact ⟨c.scr, h0, show 256 ≤ p.Z by omega, hs (sDom, p.dp) (by simp), hs (sK, BitVec.ofNat 64 p.k) (by simp)⟩

/-- After `domHead`. -/
def CE (p : CpP) (t : State) : Prop :=
  Fx p t ∧ t.gpr .rdi = p.B ∧ Slots t.mem p.B p.hdQ ∧ t.zf = some p.mv

theorem e1_ce (p : CpP) (t : State) (h : E1 p t) : WP isa (.block domHead) t (CE p) := by
  obtain ⟨hx, h0, hs⟩ := h
  have c := hx.ctx
  have hn := c.scr.nowrap
  have hZ := c.hZ
  have hl : (p.dom.take p.k).length = p.k := by rw [List.length_take, c.doml]; rcases c.dl with h | h <;> omega
  refine WP.mono (domHead_ok c.scr h0 (by omega) c.k1 c.k2 (hs (sDom, p.dp) (by simp)) (hs (sK, BitVec.ofNat 64 p.k) (by simp)) (c.dom.take p.k) hl)
    fun u ⟨h9, _, hQ, f, h0', k⟩ => ⟨hx.keep (InScr.of_frm f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sG, sQ, sFn] <;> omega) k, h0', ?_, h9⟩
  have hs' : Slots u.mem p.B p.hd := hs.frm f (fun q hq r hr => by
      simp only [CpP.hd, List.mem_cons, List.not_mem_nil, or_false] at hq hr
      rcases hq with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl <;>
        simp only [sG, sQ, sDom, sDomLen, sK, sY, sFn] <;> omega)
    (fun q hq => by
      simp only [CpP.hd, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [sDom, sDomLen, sK, sY, sFn] <;> omega)
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hs' q hq
  · rw [List.mem_singleton.mp hq]; exact hQ

theorem ce_eval {p : CpP} {t : State} (h : CE p t) :
    isa.eval .ne t = some (!p.mv) := by
  simp [eval, h.2.2.2]

theorem ce_valid {p : CpP} {t : State} (h : CE p t) (he : isa.eval .ne t = some false) : p.mv = true := by
  rw [ce_eval h] at he
  cases hv : p.mv
  · rw [hv] at he; simp at he
  · rfl

theorem ce_setupP (p : CpP) (t : State) (h : CE p t) (he : isa.eval .ne t = some false) :
    SetupP p.d t := by
  have hv := ce_valid h he
  obtain ⟨hx, h0, hs, -⟩ := h
  have c := hx.ctx
  have hl : (p.dom.take p.k).length = p.k := by rw [List.length_take, c.doml]; rcases c.dl with h | h <;> omega
  obtain ⟨hodd, -⟩ := valid_facts hv c.k1
  exact ⟨p.dom.take p.k, c.scr, h0, c.k1, c.k2, c.hZ, hs (sDom, p.dp) (by simp), hs (sK, BitVec.ofNat 64 p.k) (by simp), c.dom.take p.k, hl, hodd⟩

/-! ## The workspaces, y and its range -/

/-- In the inner workspace for p. -/
def C1 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ SubCtx t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ ∧ p.mv = true

theorem ce_c1 (p : CpP) (t : State) (h : CE p t) (he : isa.eval .ne t = some false) :
    WP isa (seqs (([.block head] : List (Prog isa)) ++ pSetup)) t (C1 p) := by
  have hv := ce_valid h he
  obtain ⟨hx, h0, hs, -⟩ := h
  have c := hx.ctx
  have hn := c.scr.nowrap
  have hZ := c.hZ
  have hroom := room_k c.k1 hZ
  have hl : (p.dom.take p.k).length = p.k := by rw [List.length_take, c.doml]; rcases c.dl with h | h <;> omega
  obtain ⟨hodd, -⟩ := valid_facts hv c.k1
  refine WP.mono (setup_ok c.scr h0 c.k1 c.k2 hZ (hs (sDom, p.dp) (by simp)) (hs (sK, BitVec.ofNat 64 p.k) (by simp)) (c.dom.take p.k) hl hodd)
    fun u ⟨mi, hc, hX, hWs, f, k⟩ => ⟨mi, hx.keep (InScr.of_frm f fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      unfold inner slot hdrBytes tabBytes at hroom
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [sW, sArr, sWs, sFn, inner, slot, hdrBytes] <;> omega_arith) k,
      hc, hX, hWs, fun q hq => ?_, hv⟩
  rw [f.word_eq (fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl | rfl <;>
          simp only [sW, sArr, sWs, sDom, sDomLen, sK, sY, sQ, sFn, inner, slot, hdrBytes] <;> omega_arith)
    (by unfold inner slot hdrBytes tabBytes at hroom
        simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp only [sDom, sDomLen, sK, sY, sQ, sFn] <;> omega_arith)]
  exact hs q hq

theorem hdQ_lt (p : CpP) : ∀ q ∈ p.hdQ, q.1 < 32 := by
  intro q hq
  simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [sDom, sDomLen, sK, sY, sQ, sFn]

/-- In the inner workspace for p, with what the outer one keeps. -/
def In (p : CpP) (mi : BitVec 64) (t : State) : Prop :=
  Fx p t ∧ SubCtx t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ

theorem In.step {p : CpP} {mi : BitVec 64} {t u : State} (h : In p mi t) {rs : List (Nat × Nat)}
    (hf : Frm (off p.B (inner p.w)) rs t.mem u.mem) (hr : ∀ r ∈ rs, StepR p.w r) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) (h0 : u.gpr .rdi = t.gpr .rdi) : In p mi u := by
  obtain ⟨hx, hc, hv, hWs, hs⟩ := h
  have c := hx.ctx
  have hroom := room_k c.k1 c.hZ
  rw [show (p.k + 7) / 8 = p.w from rfl] at hroom
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have hGn := hc.good.scr.nowrap
  have hc' := hc.of_frm hf (fun r hr' => ⟨(hr r hr').1, (hr r hr').2.1⟩) hwr h0
  obtain ⟨hb, hi⟩ := child_frm hc (by unfold inner at hroom ⊢; omega) hf (fun r hr' => by
    have := (hr r hr').2.1; omega)
  exact ⟨hx.step hi hrd hwr, hc', hv.of_frmA hGn (by omega) hf (fun r hr' => (hr r hr').2.2),
    by rw [hb _ (by decide)]; exact hWs, fun q hq => by rw [hb _ (hdQ_lt p q hq)]; exact hs q hq⟩

theorem In.keep {p : CpP} {mi : BitVec 64} {t u : State} (h : In p mi t) (hm : u.mem = t.mem) {rs : List Reg}
    (k : Keep rs t u) (h0 : .rdi ∉ rs) : In p mi u :=
  h.step (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (fun _ h => absurd h List.not_mem_nil) k.2.1 k.2.2
    (k.gpr h0)

theorem c1_in {p : CpP} {t : State} (h : C1 p t) : ∃ mi, In p mi t ∧ p.mv = true :=
  let ⟨mi, hx, hc, hv, hWs, hs, hm⟩ := h
  ⟨mi, ⟨hx, hc, hv, hWs, hs⟩, hm⟩

/-- y's load. -/
abbrev CpP.yl (p : CpP) : BPub := ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, p.yp, p.k⟩

theorem c1_lpre (p : CpP) (t : State) (h : C1 p t) : LPre aXm sY sK p.yl t := by
  obtain ⟨mi, ⟨hx, hc, -, -, hs⟩, -⟩ := c1_in h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have := c.k2
  have := c.yl
  exact ⟨mi, p.yb, hc, show 2 ≤ p.w by omega, Nat.le_refl _, show p.w < 2 ^ 30 by omega, by decide, by decide,
    by decide, hs (sY, p.yp) (by simp), by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp), c.yl, c.y,
    by omega, by omega, show (p.yb.length + 7) / 8 ≤ p.w by rw [c.yl]⟩

/-- With y in `aXm`. -/
def C2 (p : CpP) (t : State) : Prop :=
  ∃ mi, In p mi t ∧ p.mv = true ∧ wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.Y

theorem c1_c2 (p : CpP) (t : State) (h : C1 p t) : WP isa (seqs (Crt.loadArr aXm sY sK)) t (C2 p) := by
  obtain ⟨mi, hI, hm⟩ := c1_in h
  have hI' := hI
  obtain ⟨hx, hc, -, -, hs⟩ := hI'
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have := c.k2
  have := c.yl
  refine WP.mono (primeLoad_ok hc (show 2 ≤ p.w by omega) (Nat.le_refl _) (show p.w < 2 ^ 30 by omega)
    (show aXm < 8 by decide) (show sY < 32 by decide) (show sK < 32 by decide) (hs (sY, p.yp) (by simp))
    (by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp)) c.y (by omega) (by omega)
    (show (p.yb.length + 7) / 8 ≤ p.w by rw [c.yl])) fun u ⟨_, hy, ho, k⟩ =>
    ⟨mi, hI.step (rs := [(slot p.w aXm, 8 * (p.w + 2))]) (Frm.of_outside ho (by simp)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact stepR_arr _ (by decide) (by decide) (by decide)) k.2.1 k.2.2
      (k.gpr (by decide)), hm, hy⟩

theorem c2_goodW1 (p : CpP) (t : State) (h : C2 p t) : GoodW1 p.ws t := by
  obtain ⟨mi, ⟨hx, hc, -⟩, -⟩ := h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have := c.k2
  exact ⟨⟨mi, hc.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega, show p.w < 2 ^ 31 by omega⟩

/-- Whether `1 < y < p − 1`, as the code compares. -/
abbrev CpP.rg (p : CpP) : Prop := 1 < p.Y ∧ 2 * (p.Y / 2) + 1 < p.P

/-- After the range check. -/
def C3 (p : CpP) (t : State) : Prop := ∃ mi, In p mi t ∧ p.mv = true ∧ t.zf = some (!decide p.rg)

theorem c2_c3 (p : CpP) (t : State) (h : C2 p t) : WP isa (seqs (rangeTest aXm)) t (C3 p) := by
  obtain ⟨mi, hI, hm, hy⟩ := h
  have hI' := hI
  obtain ⟨hx, hc, hv, -⟩ := hI'
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have := c.k2
  refine WP.mono (rangeTest_ok hc.good (Nat.le_refl _) (show 1 ≤ p.w by omega) (show p.w < 2 ^ 31 by omega)
    (show aXm < 8 by decide) (by decide) hv.one) fun u ⟨h9, hz, _, f, k⟩ => ⟨mi, hI.step f (fun r hr => ?_) k.2.1 k.2.2
      (k.gpr (by decide)), hm, by rw [hz, hy, hv.n]⟩
  have := slot_le (w := p.w) (show aTmp < 8 by decide)
  have := hdr_lt_slot p.w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot p.w 8 (show sF < 32 by decide)
  have := hdr_lt_slot p.w aN (show sF < 32 by decide)
  have := hdr_lt_slot p.w aOne (show sF < 32 by decide)
  have s1 := slot_sep (w := p.w) (show aTmp ≠ aN by decide)
  have s2 := slot_sep (w := p.w) (show aTmp ≠ aOne by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [sF, sFn] at * <;> omega

theorem c3_eval {p : CpP} {t : State} (h : C3 p t) : isa.eval .e t = some (!decide p.rg) := by
  obtain ⟨_, _, _, h9⟩ := h
  simp [eval, h9]

/-! ## Back to the outer workspace -/

/-- After `leave` and the test of the domain's length. -/
def C4 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ SubMem t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ ∧ p.mv = true ∧ t.gpr .rdi = p.B ∧
    t.zf = some (decide (p.dl = 2 * p.k))

theorem c3_leave (p : CpP) (t : State) (h : C3 p t) : WP isa (.block [leave]) t fun u => u.gpr .rdi = p.B := by
  obtain ⟨mi, ⟨-, hc, -⟩, -⟩ := h
  exact WP.mono (leave_ok hc) fun u ⟨h0, _, _⟩ => h0

theorem c3_c4 (p : CpP) (t : State) (h : C3 p t) : WP isa (.block (leave :: qTest)) t (C4 p) := by
  obtain ⟨mi, ⟨hx, hc, hv, hWs, hs⟩, hm, -⟩ := h
  have c := hx.ctx
  refine WP.mono (leaveQ_ok hc (hs (sDomLen, BitVec.ofNat 64 p.dl) (by simp)) (hs (sK, BitVec.ofNat 64 p.k) (by simp))
    (by rcases c.dl with h | h <;> omega)
    (by have := c.k2; rcases c.dl with h | h <;> omega)) fun u ⟨h0, _, h3, hmu, k⟩ =>
    ⟨mi, hx.keep (by rw [hmu]; exact InScr.refl _ _ _) k, hc.toMem.congr hmu k.2.2,
      ⟨by rw [hmu]; exact hv.n, by rw [hmu]; exact hv.inv, by rw [hmu]; exact hv.one⟩, by rw [hmu]; exact hWs,
      by rw [hmu]; exact hs, hm, h0, h3⟩

theorem c4_eval {p : CpP} {t : State} (h : C4 p t) :
    isa.eval .e t = some (decide (p.dl = 2 * p.k)) := by
  obtain ⟨_, _, _, _, _, _, _, _, h3⟩ := h
  simp [eval, h3]

theorem c4_q {p : CpP} {t : State} (h : C4 p t) (he : isa.eval .e t = some false) : p.dl = 3 * p.k := by
  have c := h.choose_spec.1.ctx
  rw [c4_eval h] at he
  have := c.k2
  rcases c.dl with hd | hd
  · simp [hd] at he
  · exact hd

/-! ## q's first nonzero octet -/

/-- q's octets and their pointer. -/
abbrev CpP.qs (p : CpP) : ScanPub := ⟨p.B, p.Z, p.w, p.dp + BitVec.ofNat 64 (2 * p.k), p.qb⟩

theorem qb_length {p : CpP} {t : State} (c : FxCtx p t) (hq : p.dl = 3 * p.k) : p.qb.length = p.k := by
  simp only [CpP.qb, List.length_take, List.length_drop, c.doml, hq]; omega

theorem c4_scan (p : CpP) (t : State) (h : C4 p t) (he : isa.eval .e t = some false) :
    ScanPre sQ p.qs t := by
  have hq := c4_q h he
  obtain ⟨mi, hx, hc, -, -, hs, -, h0, -⟩ := h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have := c.k2
  have hroom := room_k c.k1 c.hZ
  rw [show (p.k + 7) / 8 = p.w from rfl] at hroom
  have hl := qb_length c hq
  show Outer t p.B p.Z p.w ∧ word t.mem p.B (8 * sQ) = p.dp + BitVec.ofNat 64 (2 * p.k) ∧
    word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.qb.length ∧ p.qb ≠ [] ∧ p.qb.length < 2 ^ 32 ∧
    Src t p.B p.Z (p.dp + BitVec.ofNat 64 (2 * p.k)) p.qb ∧ sQ < 32
  refine ⟨Outer.of_mem hc h0 hroom (by omega) (by omega), hs (sQ, p.dp + BitVec.ofNat 64 (2 * p.k)) (by simp),
    by rw [hl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp), fun he' => by rw [he'] at hl; simp at hl; omega,
    by omega, (c.dom.drop (2 * p.k)).take p.k, by decide⟩

/-- After the scan. -/
def C5 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ SubMem t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ ∧ p.mv = true ∧ t.gpr .rdi = p.B ∧
    p.dl = 3 * p.k ∧ word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead p.qb)

theorem c4_c5 (p : CpP) (t : State) (h : C4 p t) (he : isa.eval .e t = some false) :
    WP isa (seqs (scan sQ)) t (C5 p) := by
  have hq := c4_q h he
  have hS := c4_scan p t h he
  obtain ⟨mi, hx, hc, hv, hWs, hs, hm, h0, -⟩ := h
  have c := hx.ctx
  have hl := qb_length c hq
  have hS' : Outer t p.B p.Z p.w ∧ word t.mem p.B (8 * sQ) = p.dp + BitVec.ofNat 64 (2 * p.k) ∧
      word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.qb.length ∧ p.qb ≠ [] ∧ p.qb.length < 2 ^ 32 ∧
      Src t p.B p.Z (p.dp + BitVec.ofNat 64 (2 * p.k)) p.qb ∧ sQ < 32 := hS
  obtain ⟨hO, hp, hk, hne, hlt, hsrc, -⟩ := hS'
  refine WP.mono (scan_ok hO (show sQ < 32 by decide) hp hk hne hlt hsrc) fun u ⟨hEp, hEl, _, f, k⟩ => ?_
  have hr : ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [sEp, sEl, sFn] <;> omega
  have hroom := room_k c.k1 c.hZ
  have i : InScr p.B p.Z t.mem u.mem := InScr.of_frm f fun r hr' => by
    have := (hr r hr').2; unfold inner slot hdrBytes at hroom; omega
  have hw : ∀ q ∈ p.hdQ ++ [(sWs, off p.B (inner p.w))], word u.mem p.B (8 * q.1) = word t.mem p.B (8 * q.1) := by
    intro q hq
    have hq32 : q.1 < 32 := by
      rcases List.mem_append.mp hq with hq | hq
      · exact hdQ_lt p q hq
      · rw [List.mem_singleton.mp hq]; show sWs < 32; decide
    refine f.word_eq (fun r hr' => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hr' with rfl | rfl <;>
      simp only [sDom, sDomLen, sK, sY, sQ, sWs, sEp, sEl, sFn] <;> omega
  refine ⟨mi, hx.keep i k, hc.of_parent f hr k.2.2, hv.of_parent hc f (fun r hr' => (hr r hr').2),
    by rw [hw (sWs, off p.B (inner p.w)) (by simp)]; exact hWs, fun q hq => by rw [hw q (List.mem_append_left _ hq)]; exact hs q hq,
    hm, (k.gpr (by decide)).trans h0, hq, hEp, by rw [hEl, hl]⟩

/-! ## `R² mod p`, `y^q mod p` -/

/-- Back in the inner workspace. -/
def C6 (p : CpP) (t : State) : Prop :=
  ∃ mi, In p mi t ∧ p.mv = true ∧ p.dl = 3 * p.k ∧
    word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead p.qb)

theorem c5_x0 {p : CpP} {t : State} (h : C5 p t) : t.gpr .rdi = p.B := h.choose_spec.2.2.2.2.2.2.1

theorem c5_c6 (p : CpP) (t : State) (h : C5 p t) : WP isa (.block [enter]) t (C6 p) := by
  obtain ⟨mi, hx, hc, hv, hWs, hs, hm, h0, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have := c.k2
  have hroom := room_k c.k1 c.hZ
  rw [show (p.k + 7) / 8 = p.w from rfl] at hroom
  refine WP.mono (enter_ok (Outer.of_mem hc h0 hroom (by omega) (by omega)) hWs) fun u ⟨h0', hmu, k⟩ =>
    ⟨mi, ⟨hx.keep (by rw [hmu]; exact InScr.refl _ _ _) k, (hc.congr hmu k.2.2).ctx h0',
      ⟨by rw [hmu]; exact hv.n, by rw [hmu]; exact hv.inv, by rw [hmu]; exact hv.one⟩, by rw [hmu]; exact hWs,
      by rw [hmu]; exact hs⟩, hm, hq, by rw [hmu]; exact hEp, by rw [hmu]; exact hEl⟩

/-- `r2_ok`'s hypotheses, for the run's `-p⁻¹`. -/
theorem c6_r2 {p : CpP} {t : State} {mi : BitVec 64} (hI : In p mi t) (hm : p.mv = true)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 p.w) (h10 : t.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)) :
    R2Pre ⟨⟨off p.B (inner p.w), slot p.w 8, p.w, mi⟩, p.P⟩ t := by
  obtain ⟨hx, hc, hv, -⟩ := hI
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have := c.k2
  obtain ⟨hodd, -, hlo⟩ := valid_facts hm c.k1
  exact ⟨⟨hc.good, Nat.le_refl _⟩, show 2 ≤ p.w by omega, show p.w < 2 ^ 30 by omega, hv.n, hv.inv, h12, h10, hodd, hlo⟩

/-- After `R² mod p`. -/
def C7 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ ModCtx t p.B p.Z (inner p.w) p.w mi p.P ∧ Slots t.mem p.B p.hdQ ∧ p.dl = 3 * p.k ∧
    word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead p.qb)

theorem c6_c7 (M : Mont) (R : R2Impl M) (p : CpP) (t : State) (h : C6 p t) : WP isa (.seq (.block r2Head) R.code) t (C7 p) := by
  obtain ⟨mi, ⟨hx, hc, hv, -, hs⟩, hm, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have hroom := room_k c.k1 c.hZ
  refine WP.mono (r2_ctx M R hc hv hm c.k1 c.k2 c.hZ) fun u ⟨hM, f, k⟩ => ?_
  obtain ⟨hb, hi⟩ := child_frm hc (by unfold inner at hroom ⊢; omega) f (fun r hr => by
    have := r2Ranges_le p.w r hr; unfold tabBytes; omega)
  exact ⟨mi, hx.keep hi k, hM, fun q hq => by rw [hb _ (hdQ_lt p q hq)]; exact hs q hq, hq,
    by rw [hb _ (by decide)]; exact hEp, by rw [hb _ (by decide)]; exact hEl⟩

/-- `pow`'s public data. -/
abbrev CpP.pw (p : CpP) : PowPub :=
  ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, p.yp, p.yb.length, off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb),
    (p.qb.drop (lead p.qb)).length⟩

theorem c7_ps0 (p : CpP) (t : State) (h : C7 p t) : PS0 sY sK sEp sEl p.pw t := by
  obtain ⟨mi, hx, hM, hs, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have hl := qb_length c hq
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have := c.k2
  have hne : p.qb ≠ [] := fun he => by rw [he] at hl; simp at hl; omega
  have hlead := lead_lt hne
  have := c.yl
  have hsq : Src t p.B p.Z (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb)) (p.qb.drop (lead p.qb)) :=
    ((c.dom.drop (2 * p.k)).take p.k).drop (lead p.qb)
  exact ps0_of hM (by decide) (by decide) (by decide) (by decide) (hs (sY, p.yp) (by simp))
    (by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp)) c.y (by omega) (by rw [c.yl]) hEp
    (by rw [hEl, List.length_drop, hl]) hsq (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)

/-- After `pow`: the inner workspace. -/
def C8 (p : CpP) (t : State) : Prop := GoodW1 p.ws t

theorem c7_c8 (M : Mont) (E : CrtExpL M) (p : CpP) (t : State) (h : C7 p t) :
    WP isa (seqs (pow M.mm E.code sY sK sEp sEl)) t (C8 p) := by
  have h0 := c7_ps0 p t h
  obtain ⟨mi, hx, hM, hs, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have hl := qb_length c hq
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have := c.k1
  have := c.k2
  have hne : p.qb ≠ [] := fun he => by rw [he] at hl; simp at hl; omega
  have hlead := lead_lt hne
  have := c.yl
  have hsq : Src t p.B p.Z (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb)) (p.qb.drop (lead p.qb)) :=
    ((c.dom.drop (2 * p.k)).take p.k).drop (lead p.qb)
  exact WP.mono (pow_ok M E hM (by decide) (by decide) (by decide) (by decide) (hs (sY, p.yp) (by simp))
    (by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp)) c.y (by omega) (by rw [c.yl]) hEp
    (by rw [hEl, List.length_drop, hl]) hsq (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega))
    fun u ⟨hM', _⟩ => ⟨⟨mi, hM'.sub.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega, show p.w < 2 ^ 31 by omega⟩

end VG.Proof.Ffdh.X86_64.CheckPublic
