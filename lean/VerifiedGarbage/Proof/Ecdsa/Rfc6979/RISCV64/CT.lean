module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Correct
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on RISC-V: constant time, up to the number of candidates

Two runs from states whose public data agree (`PubEq`: the pointers, the
stack pointer, the number of candidates RFC 6979 tries, which the contract
lets leak, and the addresses of the table's functions) are related piece by
piece. The code between the calls is checked by the taint analysis
(`Checks`, which the kernel evaluates once for each curve: the code is the
same for every hash function), from the registers that hold pointers, `D`
and `B` and the length of `T`, which agree in both runs; the calls through
the table, of HMAC's `init` and `finalize` (`hi_rel`, `hf_rel`) and of the
streaming `update` (`upd_rel`), reach the same function in both runs
(`tcall_rel`), and are related by their contracts, as the call of the
signature with a given `k` (`core_rel`), with the arguments each run's
correctness gives. Each run's correctness then says what the registers hold
after a piece (`RelCT.wp`), so that they agree again. The loops' branches
agree: the candidate's after `j` `V`s in both runs, and the candidates' as
in both runs it goes on after candidate `i` iff `i` is before the candidate
it stops at (`go_iff`, `exitAt`); the frame's `alloc` and `free` leak nothing
(`rel_alloc`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (eval_nonzero wp_li wp_ld Upd)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Hmac.Stream.RISCV64 (updK)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)

/-- A piece of code the taint analysis accepts with the registers `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true

/-- The registers that hold the pointers, `D` and `B`. -/
abbrev ptrRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s6, .s7, .s8]

/-- The taint checks of `update`'s arguments for the parts of a message. -/
def UpdCks : Len → List Part → Prop
  | _, [] => True
  | cnt, p :: ps => Ck ptrRegs (.block (Cfg.updArgs cnt p)) ∧ UpdCks (cnt.1 || p.2.2.1, cnt.2 + p.2.2.2) ps

/-- The parts of the messages of steps d and f, of `V = HMAC_K(V)` and of step h.3. -/
abbrev fullParts (c : Cfg) : List Part := [(.s1, fV, (true, 1)), (.s3, 0, (false, c.Q)), (.s1, c.fHo, (false, c.Q))]
abbrev vParts : List Part := [(.s1, fV, (true, 0))]
abbrev rParts : List Part := [(.s1, fV, (true, 1))]

/-- The taint checks of the pieces of the function between the calls. -/
structure Checks (c : Cfg) : Prop where
  pro : Ck [.a0, .a1, .a2, .a4, .a5] (.block Cfg.prologue)
  px : Ck ptrRegs c.prepX
  ph : Ck ptrRegs c.prepH
  kv : Ck ptrRegs (.block Cfg.initKV)
  sep0 : Ck ptrRegs (.block (Cfg.sep 0))
  sep1 : Ck ptrRegs (.block (Cfg.sep 1))
  ia : Ck ptrRegs (.block Cfg.initArgs)
  uF : UpdCks (false, 0) (fullParts c)
  uV : UpdCks (false, 0) vParts
  uR : UpdCks (false, 0) rParts
  tc0 : Ck ptrRegs (.block [.load .d .t1 .s6 (8 * 0)])
  tc1 : Ck ptrRegs (.block [.load .d .t1 .s6 (8 * 1)])
  tc2 : Ck ptrRegs (.block [.load .d .t1 .s6 (8 * 2)])
  fF : Ck ptrRegs (.block (Cfg.finArgs (total (fullParts c)) fK))
  fVc : Ck ptrRegs (.block (Cfg.finArgs (total vParts) fV))
  fR : Ck ptrRegs (.block (Cfg.finArgs (total rParts) fK))
  cnt : Ck [] (.block c.initCnt)
  ti : Ck [] (.block Cfg.tInit)
  ka : Ck (.s9 :: ptrRegs) (.block Cfg.keepArgs)
  cl : Ck [.a4, .a5, .a6] (Impl.Words.RISCV64.copyLoop .t1 .a4 .a5 .a6)
  ts : Ck (.s9 :: ptrRegs) (.block c.tStep)
  ca : Ck ptrRegs (.block c.coreArgs)
  go : Ck [.s5] (.block Cfg.goOn)
  ag : Ck [] (.block Cfg.again)
  st : Ck [] (.block Cfg.stop)
  fin : Ck [.s1] (.block (Cfg.wipe ++ Cfg.restore))

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (P : Rfc) (s₀ s₀' : State) : Prop where
  a0 : s₀.gpr .a0 = s₀'.gpr .a0
  a1 : s₀.gpr .a1 = s₀'.gpr .a1
  a2 : s₀.gpr .a2 = s₀'.gpr .a2
  a4 : s₀.gpr .a4 = s₀'.gpr .a4
  a5 : s₀.gpr .a5 = s₀'.gpr .a5
  sp : s₀.sp = s₀'.sp
  lk : (result P.I s₀.mem (dk s₀) (dg s₀)).2 = (result P.I s₀'.mem (dk s₀') (dg s₀')).2
  sy : ∀ cn ∈ P.kit.K, s₀.syms cn.1 = s₀'.syms cn.1
  sn : ∀ n ∈ [P.w.hiN, P.H.updN, P.w.hfN], s₀.syms n = s₀'.syms n

variable {P : Rfc}

section
variable {s₀ s₀' : State} (hq : PubEq P s₀ s₀')
include hq

theorem PubEq.sA (o : Nat) : sA s₀' o = sA s₀ o := by simp only [RISCV64.sA, hq.sp]
theorem PubEq.cA (o : Nat) : cA s₀' o = cA s₀ o := by simp only [RISCV64.cA, scr, hq.a4]
theorem PubEq.pA (p : Part) : pA s₀' p = pA s₀ p := by
  obtain ⟨r, o, n⟩ := p
  simp only [RISCV64.pA]
  congr 1
  cases r <;> simp only [regV, dk, hq.sp, hq.a1]

/-- The pointer registers agree in two runs that keep `KR`. -/
theorem ag_kr {s s' : State} (h : KR P s₀ s) (h' : KR P s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ ptrRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.s0, h'.s0, scr, scr, hq.a4]
  · rw [h.s1, h'.s1, hq.sp]
  · rw [h.s2, h'.s2, out, out, hq.a0]
  · rw [h.s3, h'.s3, dk, dk, hq.a1]
  · rw [h.s4, h'.s4, dg, dg, hq.a2]
  · rw [h.s6, h'.s6, tab, tab, hq.a5]
  · rw [h.s7, h'.s7]
  · rw [h.s8, h'.s8]

end

/-- Code the taint analysis accepts from the registers `rs`, in two runs
whose single-run facts `G₁` and `G₂` agree on them. -/
theorem rel_agree {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa} {rs : List Reg}
    (hag : ∀ s s', P₁ s → P₂ s' → s.sp = s'.sp ∧ ∀ r ∈ rs, s.gpr r = s'.gpr r) (hc : Ck rs c)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' := by
  obtain ⟨_, hc⟩ := hc
  refine ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => ?_) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨e, g⟩ := hag s s' h.1 h.2
  exact ⟨e, fun r hr => g r (Taint.mem_ofRegs.mp hr)⟩

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun _ _ => True)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Code that keeps `KR`, accepted by the taint analysis from pointer registers. -/
theorem rel_kr {s₀ s₀' : State} (hq : PubEq P s₀ s₀') {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hk₁ : ∀ s, P₁ s → KR P s₀ s) (hk₂ : ∀ s, P₂ s → KR P s₀' s) (hc : Ck ptrRegs c)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' :=
  rel_agree (fun s s' h h' => ag_kr hq (hk₁ s h) (hk₂ s' h')) hc hw hw'

/-- Two runs of an empty block. -/
theorem rel_nil {Q : State → State → Prop} : RelCT isa Q (.block []) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  rw [← e₁.2, ← e₂.2]; exact ⟨rfl, trivial⟩

/-! ## The calls through the table -/

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀')
include hp hp' hq

/-- The table's function `j`, among `ts`, which reaches `n` in both runs, at
the same address: two runs of the call of `n` from the states the load of its
address leaves. -/
theorem tcall_rel {Φ₁ Φ₂ : State → Prop} {j : Nat} (hj : j < 3) {ts : List (String × Prog isa)} {n : String}
    {c : Prog isa} (hk : ∀ t, Φ₁ t → KR P s₀ t ∧ t.syms = s₀.syms)
    (hk' : ∀ t, Φ₂ t → KR P s₀' t ∧ t.syms = s₀'.syms)
    (hf : ts.find? (fun q => s₀.syms q.1 == s₀.syms n) = some (n, c))
    (hf' : ts.find? (fun q => s₀'.syms q.1 == s₀'.syms n) = some (n, c))
    (hw : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * j)) 64 = s₀.syms n)
    (hw' : s₀'.mem.readW (tab s₀' + BitVec.ofNat 64 (8 * j)) 64 = s₀'.syms n)
    (hsn : s₀.syms n = s₀'.syms n) (hcl : Ck ptrRegs (.block [.load .d .t1 .s6 (8 * j)]))
    (hcall : RelCT isa (fun u u' => (∃ t, Φ₁ t ∧ Upd t u .t1 (s₀.syms n) ∧ u.syms = t.syms) ∧
      (∃ t', Φ₂ t' ∧ Upd t' u' .t1 (s₀'.syms n) ∧ u'.syms = t'.syms)) (.call n c) fun _ _ => True) :
    RelCT isa (fun t t' => Φ₁ t ∧ Φ₂ t') (tcall j ts) fun _ _ => True := by
  have ld : ∀ {σ : State} (hσ : Pre P σ) {t : State}, KR P σ t →
      σ.mem.readW (tab σ + BitVec.ofNat 64 (8 * j)) 64 = σ.syms n →
      WP isa (.block [.load .d .t1 .s6 (8 * j)]) t fun u => Upd t u .t1 (σ.syms n) ∧ u.syms = t.syms :=
    fun {σ} hσ t h hv => by
      have hin : InRegions (t.rd ++ t.wr) (tab σ + BitVec.ofNat 64 (8 * j)) 8 :=
        ⟨tabR σ, List.mem_append_left _ (by rw [h.rd, hσ.rd]; simp),
          Offset.contains_base _ (by omega) (by have := hσ.nt; omega)⟩
      have hal : (tab σ + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hσ.ta; have := hσ.nt; omega
      refine VG.RISCV64.WP.of_syms (wp_ld (by omega) (by rw [h.s6]) hal hin fun u v => WP.block_nil fun sy => ?_)
      rw [h.tabW hσ (by omega), hv] at v
      exact ⟨v, sy⟩
  unfold tcall
  refine (rel_agree (P₁ := Φ₁) (P₂ := Φ₂) (G₁ := fun u => ∃ t, Φ₁ t ∧ Upd t u .t1 (s₀.syms n) ∧ u.syms = t.syms)
    (G₂ := fun u => ∃ t, Φ₂ t ∧ Upd t u .t1 (s₀'.syms n) ∧ u.syms = t.syms)
    (fun s s' h h' => ag_kr hq (hk s h).1 (hk' s' h').1) hcl
    (fun s h => WP.mono (ld hp (hk s h).1 hw) fun u ⟨v, y⟩ => ⟨s, h, v, y⟩)
    (fun s h => WP.mono (ld hp' (hk' s h).1 hw') fun u ⟨v, y⟩ => ⟨s, h, v, y⟩)).seq ?_
  cases ts with
  | nil => exact RelCT.of_false fun _ _ _ => by simp at hf
  | cons q ts =>
    refine RelCT.icalls_of_call hcall ?_
    rintro u u' ⟨⟨t, h, v, y⟩, ⟨t', h', v', y'⟩⟩
    refine ⟨s₀.syms n, by show some (u.gpr .t1) = _; rw [v.gpr], by show some (u'.gpr .t1) = _; rw [v'.gpr, hsn],
      ?_, ?_, rfl⟩
    · show (q :: ts).find? (fun q => u.syms q.1 == s₀.syms n) = _
      rw [y, (hk t h).2]; exact hf
    · show (q :: ts).find? (fun q => u'.syms q.1 == s₀.syms n) = _
      rw [y', (hk' t' h').2, hsn]; exact hf'

end

/-- Two runs of a call of the streaming `update` with the same arguments. -/
theorem upd_rel {Q : State → State → Prop} {st dat : Addr} {len : Nat}
    (h : ∀ s s', Q s s' → UpdArgs P s st dat len ∧ UpdArgs P s' st dat len ∧ s.sp = s'.sp ∧
      s.gpr .a1 = s'.gpr .a1) :
    RelCT isa Q (.call P.H.updN P.H.updC) fun _ _ => True := by
  refine RelCT.call P.hH.upd P.w.t.l.ct.upd [⟨dat, len⟩] [⟨st, P.H.S⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e1⟩ := h s s' hp
  have pre : ∀ {s : State}, UpdArgs P s st dat len →
      (updK P.H.S P.H.F P.hH.SH.Repr).pre (s.callEntry.withRegions [⟨dat, len⟩] [⟨st, P.H.S⟩]) :=
    fun {s} a => by
    have c0 : s.callEntry.gpr .a0 = s.gpr .a0 := State.callEntry_gpr _ (by decide)
    have c2 : s.callEntry.gpr .a2 = s.gpr .a2 := State.callEntry_gpr _ (by decide)
    have c3 : s.callEntry.gpr .a3 = s.gpr .a3 := State.callEntry_gpr _ (by decide)
    simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, c0, c2, c3, a.a0, a.a2, a.a3]
    exact ⟨trivial, trivial, a.d, a.al, a.sp, a.b_s, a.b_d⟩
  refine ⟨pre a, pre a', ?_, a.hc, a.hw, a'.hc, a'.hw⟩
  simp only [updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide),
    a.a0, a'.a0, a.a2, a'.a2]
  simp only [true_and]
  exact ⟨e1, BitVec.eq_of_toNat_eq (a.a3.trans a'.a3.symm), e⟩

/-! ## One HMAC, in two runs -/

theorem HI.upd {s₀ s t t₀ : State} (h : HI P s₀ s t) {v : BitVec 64} (u : Upd t t₀ .t1 v) : HI P s₀ s t₀ :=
  ⟨h.1.upd (by decide) u, by rw [u.other _ (by decide)]; exact h.2.1, by rw [u.other _ (by decide)]; exact h.2.2.1,
    by rw [u.other _ (by decide)]; exact h.2.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.2⟩

theorem HFA.upd {s₀ s t t₀ : State} {msg : List Byte} {dst : Nat} (h : HFA P s₀ s msg dst t) {v : BitVec 64}
    (u : Upd t t₀ .t1 v) : HFA P s₀ s msg dst t₀ :=
  ⟨⟨h.1.1.upd (by decide) u, by rw [u.mem]; exact h.1.2.1, by rw [u.mem]; exact h.1.2.2⟩,
    by rw [u.other _ (by decide)]; exact h.2.1, by rw [u.other _ (by decide)]; exact h.2.2.1,
    by rw [u.other _ (by decide)]; exact h.2.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.2⟩

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq

/-- With the states' symbols. -/
abbrev Sy (s₀ : State) (F : State → Prop) (t : State) : Prop := F t ∧ t.syms = s₀.syms

omit hp hp' hq in
theorem wp_sy {σ s : State} {c : Prog isa} {Q : State → Prop} (h : WP isa c s Q) (hs : s.syms = σ.syms) :
    WP isa c s (Sy σ Q) :=
  VG.RISCV64.WP.mono_syms h fun _ q y => ⟨q, y.trans hs⟩

omit hp hp' hq in
theorem sy_of {σ : State} {F : State → Prop} {c : Prog isa} {Q : State → Prop}
    (h : ∀ s, F s → s.syms = σ.syms → WP isa c s Q) : ∀ s, Sy σ F s → WP isa c s (Sy σ Q) :=
  fun s hs => wp_sy (h s hs.1 hs.2) hs.2

/-- The parts absorbed, in two runs. -/
theorem upds_rel {σ σ' : State} (hc1 : Ck ptrRegs (.block [.load .d .t1 .s6 (8 * 1)])) :
    ∀ (ps : List Part) (cnt : Len) {pre pre' : List Byte},
    lval P cnt = pre.length → lval P cnt = pre'.length → OneD cnt ps → (∀ p ∈ ps, PartOk P p) →
    cnt.2 + (ps.map (·.2.2.2)).sum < 2048 → UpdCks cnt ps →
    RelCT isa (fun t t' => Sy s₀ (HU P s₀ σ pre) t ∧ Sy s₀' (HU P s₀' σ' pre') t') (P.c.upds cnt ps)
      fun t t' => Sy s₀ (HU P s₀ σ (pre ++ msgOf P σ.mem s₀ ps)) t ∧
        Sy s₀' (HU P s₀' σ' (pre' ++ msgOf P σ'.mem s₀' ps)) t'
  | [], cnt, pre, pre', _, _, _, _, _, _ => by
    simp only [msgOf, List.append_nil]
    exact (rel_nil.wp (F₁ := Sy s₀ (HU P s₀ σ pre)) (F₂ := Sy s₀' (HU P s₀' σ' pre')) fun s s' h =>
      ⟨WP.block_nil h.1, WP.block_nil h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  | p :: ps, cnt, pre, pre', hl, hl', ho, hps, hb, ⟨cu, cs⟩ => by
    have hpo : PartOk P p := hps p (by simp)
    simp only [List.map_cons, List.sum_cons] at hb
    unfold Cfg.upds
    have r₁ := rel_kr hq (P₁ := Sy s₀ (HU P s₀ σ pre)) (P₂ := Sy s₀' (HU P s₀' σ' pre'))
      (G₁ := Sy s₀ (HUA P s₀ σ pre p)) (G₂ := Sy s₀' (HUA P s₀' σ' pre' p))
      (fun _ h => h.1.1.kr) (fun _ h => h.1.1.kr) cu
      (sy_of fun s h _ => updArgs_ok h hl hpo.reg (by omega) hpo.off (by omega))
      (sy_of fun s h _ => updArgs_ok h hl' hpo.reg (by omega) hpo.off (by omega))
    have r₂ : RelCT isa (fun t t' => Sy s₀ (HUA P s₀ σ pre p) t ∧ Sy s₀' (HUA P s₀' σ' pre' p) t')
        (tcall 1 P.c.f.upd) fun t t' => Sy s₀ (HU P s₀ σ (pre ++ bytesAt σ.mem (pA s₀ p) (plen P p))) t ∧
          Sy s₀' (HU P s₀' σ' (pre' ++ bytesAt σ'.mem (pA s₀' p) (plen P p))) t' :=
      rel_wp (tcall_rel hp hp' hq (j := 1) (by decide) (fun _ h => ⟨h.1.1.1.kr, h.2⟩) (fun _ h => ⟨h.1.1.1.kr, h.2⟩)
        hp.tok.u hp'.tok.u (by rw [Nat.mul_one]; exact hp.tmem.2.1) (by rw [Nat.mul_one]; exact hp'.tmem.2.1)
        (hq.sn _ (by simp)) hc1
        (upd_rel fun u u' ⟨⟨t, h, v, _⟩, ⟨t', h', v', _⟩⟩ => by
          have a := upd_args hp (h.1.upd v) hpo
          have a' := upd_args hp' (h'.1.upd v') hpo
          rw [hq.cA, hq.pA] at a'
          refine ⟨a, a', by rw [(h.1.upd v).1.1.kr.sp, (h'.1.upd v').1.1.kr.sp, hq.sp], ?_⟩
          rw [(h.1.upd v).2.2.1, (h'.1.upd v').2.2.1, ← hl, ← hl']))
        (sy_of fun s h hs => updc_ok hp h hpo hs) (sy_of fun s h hs => updc_ok hp' h hpo hs)
    have e₁ : lval P (cnt.1 || p.2.2.1, cnt.2 + p.2.2.2) = (pre ++ bytesAt σ.mem (pA s₀ p) (plen P p)).length := by
      rw [lval_add P ho.1, List.length_append, bytesAt_length, hl]
    have e₂ : lval P (cnt.1 || p.2.2.1, cnt.2 + p.2.2.2) = (pre' ++ bytesAt σ'.mem (pA s₀' p) (plen P p)).length := by
      rw [lval_add P ho.1, List.length_append, bytesAt_length, hl']
    have r₃ := upds_rel (σ := σ) (σ' := σ') hc1 ps (cnt.1 || p.2.2.1, cnt.2 + p.2.2.2) e₁ e₂ ho.2 (fun q hq' => hps q (by simp [hq']))
      (by omega) cs
    refine ((r₁.seq r₂).seq r₃).mono (fun _ _ h => h) fun t t' h => ?_
    simp only [msgOf, List.append_assoc] at h ⊢
    exact h

include hc in
/-- `HMAC_K(parts)` to `dst`, in two runs from `σ` and `σ'`. -/
theorem hmac_rel {σ σ' : State} (k : KR P s₀ σ) (k' : KR P s₀' σ') (y : σ.syms = s₀.syms)
    (y' : σ'.syms = s₀'.syms) {ps : List Part} (hps : ∀ p ∈ ps, PartOk P p) (hone : OneD (false, 0) ps)
    (htot : lval P (total ps) = tlen P ps) (hb : (total ps).2 < 2048) (hb' : (ps.map (·.2.2.2)).sum < 2048)
    (htl : tlen P ps < 2048) {dst : Nat} (hdst : 96 ≤ dst ∧ dst + P.H.D ≤ frB) (cu : UpdCks (false, 0) ps)
    (cf : Ck ptrRegs (.block (Cfg.finArgs (total ps) dst))) :
    RelCT isa (fun t t' => t = σ ∧ t' = σ') (P.c.hmac ps dst)
      fun t t' => HD P s₀ σ (msgOf P σ.mem s₀ ps) dst t ∧ HD P s₀' σ' (msgOf P σ'.mem s₀' ps) dst t' := by
  have hfr : frB = 512 := rfl
  unfold Cfg.hmac
  have r₁ := rel_kr hq (P₁ := (· = σ)) (P₂ := (· = σ')) (G₁ := Sy s₀ (HI P s₀ σ)) (G₂ := Sy s₀' (HI P s₀' σ'))
    (fun _ h => by subst h; exact k) (fun _ h => by subst h; exact k') hc.ia
    (fun s h => by subst h; exact wp_sy (initArgs_ok k) y) (fun s h => by subst h; exact wp_sy (initArgs_ok k') y')
  have r₂ : RelCT isa (fun t t' => Sy s₀ (HI P s₀ σ) t ∧ Sy s₀' (HI P s₀' σ') t') (tcall 0 P.c.f.init)
      fun t t' => Sy s₀ (HK P s₀ σ) t ∧ Sy s₀' (HK P s₀' σ') t' :=
    rel_wp (tcall_rel hp hp' hq (j := 0) (by decide) (fun _ h => ⟨h.1.1.kr, h.2⟩) (fun _ h => ⟨h.1.1.kr, h.2⟩)
      hp.tok.i hp'.tok.i (by rw [Nat.mul_zero, BitVec.add_zero]; exact hp.tmem.1)
      (by rw [Nat.mul_zero, BitVec.add_zero]; exact hp'.tmem.1) (hq.sn _ (by simp)) hc.tc0
      (hi_rel fun u u' ⟨⟨t, h, v, _⟩, ⟨t', h', v', _⟩⟩ => by
        have a' := hi_args hp' (h'.1.upd v')
        rw [hq.cA, hq.cA, hq.sA] at a'
        exact ⟨hi_args hp (h.1.upd v), a', by rw [(h.1.upd v).1.kr.sp, (h'.1.upd v').1.kr.sp, hq.sp]⟩))
      (sy_of fun s h hs => initT_ok hp h hs) (sy_of fun s h hs => initT_ok hp' h hs)
  have r₃ := upds_rel hp hp' hq (σ := σ) (σ' := σ') hc.tc1 ps (false, 0) (pre := []) (pre' := []) (by simp [lval])
    (by simp [lval]) hone hps (by simpa using hb') cu
  have hl := msgOf_length P σ.mem s₀ ps
  have hl' := msgOf_length P σ'.mem s₀' ps
  have r₄ := rel_kr hq (P₁ := Sy s₀ (HU P s₀ σ (msgOf P σ.mem s₀ ps)))
    (P₂ := Sy s₀' (HU P s₀' σ' (msgOf P σ'.mem s₀' ps)))
    (G₁ := Sy s₀ (HFA P s₀ σ (msgOf P σ.mem s₀ ps) dst)) (G₂ := Sy s₀' (HFA P s₀' σ' (msgOf P σ'.mem s₀' ps) dst))
    (fun _ h => h.1.1.kr) (fun _ h => h.1.1.kr) cf
    (sy_of fun s h _ => finArgs_ok h (len := total ps) (by rw [htot, hl]) hb dst (by omega))
    (sy_of fun s h _ => finArgs_ok h (len := total ps) (by rw [htot, hl']) hb dst (by omega))
  have hz := (sizes P).B
  have hm : P.H.B + (msgOf P σ.mem s₀ ps).length < 2 ^ 63 := by rw [hl]; rcases hz with h' | h' <;> rw [h'] <;> omega
  have hm' : P.H.B + (msgOf P σ'.mem s₀' ps).length < 2 ^ 63 := by
    rw [hl']; rcases hz with h' | h' <;> rw [h'] <;> omega
  have r₅ : RelCT isa (fun t t' => Sy s₀ (HFA P s₀ σ (msgOf P σ.mem s₀ ps) dst) t ∧
        Sy s₀' (HFA P s₀' σ' (msgOf P σ'.mem s₀' ps) dst) t') (tcall 2 P.c.f.fin)
      fun t t' => HD P s₀ σ (msgOf P σ.mem s₀ ps) dst t ∧ HD P s₀' σ' (msgOf P σ'.mem s₀' ps) dst t' :=
    rel_wp (tcall_rel hp hp' hq (j := 2) (by decide) (fun _ h => ⟨h.1.1.1.kr, h.2⟩) (fun _ h => ⟨h.1.1.1.kr, h.2⟩)
      hp.tok.f hp'.tok.f hp.tmem.2.2 hp'.tmem.2.2 (hq.sn _ (by simp)) hc.tc2
      (hf_rel fun u u' ⟨⟨t, h, v, _⟩, ⟨t', h', v', _⟩⟩ => by
        have a' := hf_args hp' hdst (h'.1.upd v')
        rw [hq.cA, hq.cA, hq.sA] at a'
        exact ⟨hf_args hp hdst (h.1.upd v), a', by rw [(h.1.upd v).1.1.kr.sp, (h'.1.upd v').1.1.kr.sp, hq.sp],
          by rw [(h.1.upd v).2.2.2.1, (h'.1.upd v').2.2.2.1, hl, hl']⟩))
      (fun s h => finT_ok hp hdst hm h.1 h.2) (fun s h => finT_ok hp' hdst hm' h.1 h.2)
  refine (r₁.seq (r₂.seq ((r₃.mono (fun t t' h => ⟨⟨h.1.1.hu, h.1.2⟩, ⟨h.2.1.hu, h.2.2⟩⟩) fun _ _ h => ?_).seq
    (r₄.seq r₅)))).mono (fun _ _ h => h) fun _ _ h => h
  simpa using h

end

/-! ## Pieces that keep `KR` -/

/-- Two runs that keep `KR`, naming the symbols as at the start. -/
abbrev KK (P : Rfc) (s₀ s₀' : State) (t t' : State) : Prop := Sy s₀ (KR P s₀) t ∧ Sy s₀' (KR P s₀') t'

/-- The separator, keeping `KR`. -/
theorem sep_kr {s₀ : State} (hp : Pre P s₀) {s : State} (h : KR P s₀ s) {b : Nat} (hb : b < 256) :
    WP isa (.block (Cfg.sep b)) s (KR P s₀) := by
  have hz := sizes P
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  unfold Cfg.sep
  refine VG.RISCV64.Steps.wp_add fun s₁ u₁ => wp_li (imm := b) (by omega) fun s₂ u₂ => ?_
  have a₂ : s₂.gpr .t0 + BitVec.ofNat 64 fV = sA s₀ (fV + P.H.D) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.s1, h.s7]
    show s₀.sp + _ + _ = s₀.sp + _
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
  refine VG.RISCV64.Steps.wp_sb (by decide) a₂ (by
      rw [u₂.wr, u₁.wr]; exact in_fr hp h.wr (by simp only [fV]; omega)) fun s₃ m₃ => WP.block_nil ?_
  have k₂ : KR P s₀ s₂ := (h.upd (by decide) u₁).upd (by decide) u₂
  have F : Frame [sR s₀ (fV + P.H.D) 1] s₂.mem s₃.mem := by
    rw [m₃.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact k₂.keep m₃.rd m₃.wr m₃.sp (fun r _ => by rw [m₃.gpr]) F
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by simp only [fV]; omega)) (by decide) (by simp only [fV]; omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, part_sub (by simp only [fV]; omega)⟩)

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq hc

theorem hmac_kk {ps : List Part} (hps : ∀ p ∈ ps, PartOk P p) (hone : OneD (false, 0) ps)
    (htot : lval P (total ps) = tlen P ps) (hb : (total ps).2 < 2048) (hb' : (ps.map (·.2.2.2)).sum < 2048)
    (htl : tlen P ps < 2048) {dst : Nat} (hdst : 96 ≤ dst ∧ dst + P.H.D ≤ frB) (cu : UpdCks (false, 0) ps)
    (cf : Ck ptrRegs (.block (Cfg.finArgs (total ps) dst))) :
    RelCT isa (KK P s₀ s₀') (P.c.hmac ps dst) (KK P s₀ s₀') := by
  have ht : RelCT isa (KK P s₀ s₀') (P.c.hmac ps dst) fun _ _ => True :=
    fun s₁ s₂ t₁ t₂ s₁' s₂' h e₁ e₂ =>
      ⟨(hmac_rel hp hp' hq hc h.1.1 h.2.1 h.1.2 h.2.2 hps hone htot hb hb' htl hdst cu cf _ _ _ _ _ _ ⟨rfl, rfl⟩
        e₁ e₂).1, trivial⟩
  exact (rel_wp (P₁ := Sy s₀ (KR P s₀)) (P₂ := Sy s₀' (KR P s₀')) ht
    (sy_of fun s h hs => WP.mono (hmac_ok hp h hs hps hone htot hb hb' htl hdst) fun _ h => h.1)
    (sy_of fun s h hs => WP.mono (hmac_ok hp' h hs hps hone htot hb hb' htl hdst) fun _ h => h.1)).mono
    (fun _ _ h => h) fun _ _ h => h

theorem hmacV_kk : RelCT isa (KK P s₀ s₀') P.c.hmacV (KK P s₀ s₀') := by
  have hz := sizes P
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  exact hmac_kk hp hp' hq hc (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact ⟨.inl ⟨rfl, by simp only [fV]; omega, by simp only [fV, plen, lval]; simp; omega⟩, by decide⟩)
    (by simp [OneD]) (by simp [total, tlen, lval, plen]) (by decide) (by decide)
    (by simp only [tlen, plen, lval]; simp; omega) ⟨by decide, by simp only [fV]; omega⟩ hc.uV hc.fVc

omit hc in
theorem sep_kk {b : Nat} (hb : b < 256) (cs : Ck ptrRegs (.block (Cfg.sep b))) :
    RelCT isa (KK P s₀ s₀') (.block (Cfg.sep b)) (KK P s₀ s₀') :=
  (rel_kr hq (fun _ h => h.1) (fun _ h => h.1) cs (sy_of fun _ h _ => sep_kr hp h hb)
    (sy_of fun _ h _ => sep_kr hp' h hb)).mono (fun _ _ h => h) fun _ _ h => h

theorem rekeyFull_kk {b : Nat} (hb : b < 256) (cs : Ck ptrRegs (.block (Cfg.sep b))) :
    RelCT isa (KK P s₀ s₀') (P.c.rekeyFull b) (KK P s₀ s₀') := by
  have hz := sizes P
  obtain ⟨hQ1, hQ2, hcQ, -⟩ := hz.Q
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  have hfo : P.c.fHo + P.Q ≤ frB ∧ 96 ≤ P.c.fHo := by
    rcases fHo_cases P with e | e <;> rw [e] <;> simp only [fX, fH] <;> omega
  unfold Cfg.rekeyFull
  refine (sep_kk hp hp' hq hb cs).seq ((hmac_kk hp hp' hq hc (fun p hp' => ?_) (by simp [OneD])
    (by simp [total, tlen, lval, plen]; omega) (by simp [total]; omega) (by simp; omega)
    (by simp only [tlen, plen, lval]; simp; omega) ⟨by decide, by simp only [fK]; omega⟩ hc.uF
    hc.fF).seq (hmacV_kk hp hp' hq hc))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl
  · exact ⟨.inl ⟨rfl, by simp only [fV]; omega, by simp only [fV, plen, lval]; simp; omega⟩, by decide⟩
  · exact ⟨.inr ⟨rfl, rfl, by simp [plen, lval, hcQ]⟩, by show P.c.Q < 2048; omega⟩
  · exact ⟨.inl ⟨rfl, hfo.2, by simp [plen, lval, hcQ]; omega⟩, by show P.c.Q < 2048; omega⟩

theorem rekey_kk : RelCT isa (KK P s₀ s₀') P.c.rekey (KK P s₀ s₀') := by
  have hz := sizes P
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  unfold Cfg.rekey
  refine (sep_kk hp hp' hq (b := 0) (by decide) hc.sep0).seq ((hmac_kk hp hp' hq hc (fun p hp' => ?_)
    (by simp [OneD]) (by simp [total, tlen, lval, plen]) (by decide) (by decide)
    (by simp only [tlen, plen, lval]; simp; omega) ⟨by decide, by simp only [fK]; omega⟩ hc.uR hc.fR).seq
    (hmacV_kk hp hp' hq hc))
  simp only [List.mem_singleton] at hp'; subst hp'
  exact ⟨.inl ⟨rfl, by simp only [fV]; omega, by simp only [fV, plen, lval]; simp; omega⟩, by decide⟩

/-- Two runs of the candidate. -/
theorem cand_rel {K V₀ K' V₀' : List Byte} :
    RelCT isa (fun t t' => (KVH P s₀ K V₀ t ∧ t.syms = s₀.syms) ∧ KVH P s₀' K' V₀' t' ∧ t'.syms = s₀'.syms)
      P.c.cand fun _ _ => True := by
  obtain ⟨hN1, -, -⟩ := nV_facts P
  unfold Cfg.cand
  have r₀ := rel_agree (P₁ := fun t => KVH P s₀ K V₀ t ∧ t.syms = s₀.syms)
    (P₂ := fun t => KVH P s₀' K' V₀' t ∧ t.syms = s₀'.syms)
    (G₁ := fun t => ∃ c, CI P s₀ K V₀ c 0 t) (G₂ := fun t => ∃ c, CI P s₀' K' V₀' c 0 t) (rs := [])
    (fun _ _ h h' => ⟨by rw [h.1.kr.sp, h'.1.kr.sp, hq.sp], fun _ h => absurd h (by simp)⟩) hc.ti
    (fun t h => VG.RISCV64.WP.of_syms (wp_li (imm := 0) (by decide) fun t₁ u₁ => WP.block_nil fun y₁ =>
      ⟨t.gpr .s5, ⟨h.1.kr.upd (by decide) u₁, by rw [u₁.mem]; exact h.1.k, by rw [u₁.mem]; exact h.1.v,
        by rw [u₁.mem]; exact h.1.h, by rw [u₁.mem]; exact h.1.x⟩, by rw [u₁.gpr, Nat.zero_mul],
        by simp [bytesAt, Spec.Ecdsa.Rfc6979.genT], u₁.other _ (by decide), y₁.trans h.2⟩))
    (fun t h => VG.RISCV64.WP.of_syms (wp_li (imm := 0) (by decide) fun t₁ u₁ => WP.block_nil fun y₁ =>
      ⟨t.gpr .s5, ⟨h.1.kr.upd (by decide) u₁, by rw [u₁.mem]; exact h.1.k, by rw [u₁.mem]; exact h.1.v,
        by rw [u₁.mem]; exact h.1.h, by rw [u₁.mem]; exact h.1.x⟩, by rw [u₁.gpr, Nat.zero_mul],
        by simp [bytesAt, Spec.Ecdsa.Rfc6979.genT], u₁.other _ (by decide), y₁.trans h.2⟩))
  refine r₀.seq ((RelCT.loop (Q := fun _ _ => True)
    (fun n t t' => ∃ j c c', n = P.nV - j ∧ j < P.nV ∧ CI P s₀ K V₀ c j t ∧ CI P s₀' K' V₀' c' j t')
    (fun n => RelCT.exists_ fun j => RelCT.exists_ fun c => RelCT.exists_ fun c' => ?_) P.nV).mono
    (fun _ _ ⟨⟨c, h⟩, ⟨c', h'⟩⟩ => ⟨0, c, c', rfl, hN1, h, h'⟩) fun _ _ h => h)
  by_cases hn : n = P.nV - j
  · subst hn
    by_cases hj : j < P.nV
    · have r₁ := rel_wp (P₁ := CI P s₀ K V₀ c j) (P₂ := CI P s₀' K' V₀' c' j)
        ((hmacV_kk hp hp' hq hc).mono (fun _ _ h => ⟨⟨h.1.kvh.kr, h.1.sy⟩, ⟨h.2.kvh.kr, h.2.sy⟩⟩)
          fun _ _ _ => trivial) (fun _ h => cs1_ok hp hj h) (fun _ h => cs1_ok hp' hj h)
      have r₂ := rel_agree (P₁ := CA P s₀ K V₀ c j) (P₂ := CA P s₀' K' V₀' c' j) (rs := .s9 :: ptrRegs)
        (G₁ := CB P s₀ K V₀ c j) (G₂ := CB P s₀' K' V₀' c' j)
        (fun s s' h h' => by
          obtain ⟨e, g⟩ := ag_kr hq h.kvh.kr h'.kvh.kr
          refine ⟨e, fun r hr => ?_⟩
          rcases List.mem_cons.mp hr with rfl | hr
          · rw [h.s9, h'.s9]
          · exact g r hr) hc.ka (fun _ h => cs2_ok hj h) (fun _ h => cs2_ok hj h)
      have r₃ := rel_agree (P₁ := CB P s₀ K V₀ c j) (P₂ := CB P s₀' K' V₀' c' j) (rs := [.a4, .a5, .a6])
        (G₁ := CC P s₀ K V₀ c j) (G₂ := CC P s₀' K' V₀' c' j)
        (fun s s' h h' => by
          refine ⟨by rw [h.ca.kvh.kr.sp, h'.ca.kvh.kr.sp, hq.sp], fun r hr => ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [h.a4, h'.a4, hq.sA]
          · rw [h.a5, h'.a5, hq.sA]
          · rw [h.a6, h'.a6]) hc.cl (fun _ h => cs3_ok hp hj h) (fun _ h => cs3_ok hp' hj h)
      have r₄ := rel_agree (P₁ := CC P s₀ K V₀ c j) (P₂ := CC P s₀' K' V₀' c' j) (rs := .s9 :: ptrRegs)
        (G₁ := fun x => CI P s₀ K V₀ c (j + 1) x ∧ isa.eval (.nonzero .t6) x = some (decide (j + 1 < P.nV)))
        (G₂ := fun x => CI P s₀' K' V₀' c' (j + 1) x ∧ isa.eval (.nonzero .t6) x = some (decide (j + 1 < P.nV)))
        (fun s s' h h' => by
          obtain ⟨e, g⟩ := ag_kr hq h.kvh.kr h'.kvh.kr
          refine ⟨e, fun r hr => ?_⟩
          rcases List.mem_cons.mp hr with rfl | hr
          · rw [h.s9, h'.s9]
          · exact g r hr) hc.ts (fun _ h => cs4_ok hj h) (fun _ h => cs4_ok hj h)
      refine ((r₁.seq (r₂.seq (r₃.seq r₄))).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun u u' ⟨⟨hu, e⟩, ⟨hu', e'⟩⟩ =>
        ⟨by rw [e, e'], fun _ => trivial, fun ht => ?_⟩)
      have hg : j + 1 < P.nV := by
        rw [e] at ht
        by_contra h'
        rw [decide_eq_false h'] at ht
        cases ht
      exact ⟨P.nV - (j + 1), by omega, j + 1, c, c', rfl, hg, hu, hu'⟩
    · exact RelCT.of_false fun _ _ h => hj h.2.1
  · exact RelCT.of_false fun _ _ h => hn h.1

end

/-! ## Where the loop stops -/

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : Rfc) (s₀ : State) : Nat :=
  if (result P.I s₀.mem (dk s₀) (dg s₀)).2 = 0 then P.c.tries - 1 else (result P.I s₀.mem (dk s₀) (dg s₀)).2 - 1

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {s₀ : State} {i : Nat} (hi : i < P.c.tries) (hf : ∀ j < i, sigI P s₀ j = none) :
    (sigI P s₀ i = none ∧ i + 1 < P.c.tries) ↔ i < exitAt P s₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P s₀ ∧ xOf P s₀ < P.kit.E.curve.n
  · simp only [hv, and_self, ite_true]
    rw [VG.Proof.Ecdsa.Rfc6979.searchB_shift (b := P.nV) (nV_eq P) i P.c.tries (by omega) hf,
      show P.c.tries - i = (P.c.tries - 1 - i) + 1 by omega]
    cases hs : sigI P s₀ i with
    | some rs =>
      rw [VG.Proof.Ecdsa.Rfc6979.searchB_ok (b := P.nV) (nV_eq P) hs]
      simp
    | none =>
      rw [VG.Proof.Ecdsa.Rfc6979.searchB_fail (b := P.nV) (nV_eq P) hs]
      by_cases h7 : i + 1 < P.c.tries
      · have := VG.Proof.Ecdsa.Rfc6979.searchB_pos (C := P.kit.E.curve) (H := P.hH.SH.H) (hlen := P.H.D)
          (d := xOf P s₀) (e := eOf P s₀) (n := P.c.tries - 2 - i)
          (K := (VG.Proof.Ecdsa.Rfc6979.stepB P.hH.SH.H P.nV
            (VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H P.nV (kv0 P s₀).1 (kv0 P s₀).2 i).1
            (VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H P.nV (kv0 P s₀).1 (kv0 P s₀).2 i).2).1)
          (V := (VG.Proof.Ecdsa.Rfc6979.stepB P.hH.SH.H P.nV
            (VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H P.nV (kv0 P s₀).1 (kv0 P s₀).2 i).1
            (VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H P.nV (kv0 P s₀).1 (kv0 P s₀).2 i).2).2) (b := P.nV) (nV_eq P)
        rw [show P.c.tries - 1 - i = P.c.tries - 2 - i + 1 by omega]
        simp only [true_and, h7]
        rw [true_iff]
        split <;> omega
      · rw [show P.c.tries - 1 - i = 0 by omega]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega) (by omega)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P s₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega

theorem PubEq.exitAt {s₀ s₀' : State} (hq : PubEq P s₀ s₀') :
    RISCV64.exitAt P s₀ = RISCV64.exitAt P s₀' := by
  unfold RISCV64.exitAt; rw [hq.lk]

/-! ## One candidate, in two runs -/

/-- `V` after candidate `i`. -/
abbrev vC (P : Rfc) (s₀ : State) (i : Nat) : List Byte :=
  (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H (kvI P s₀ i).1 P.nV (kvI P s₀ i).2).2

/-- After the candidate: `K`, `V`, `T`, the candidates left, and that the
earlier candidates failed. -/
structure T0 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  kvh : KVH P s₀ (kvI P s₀ i).1 (vC P s₀ i) t
  T : bytesAt t.mem (sA s₀ fT) (P.nV * P.H.D) = candI P s₀ i
  cnt : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)
  lt : i < P.c.tries
  fails : ∀ j < i, sigI P s₀ j = none
  sy : t.syms = s₀.syms

/-- After `core`'s arguments. -/
def T2 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop :=
  T0 P s₀ i t ∧ CoreArgsG P.Q P.kit.G P.kit.K t (out s₀) (dk s₀) (sA s₀ P.c.fDg) (sA s₀ fT) (scr s₀)

/-- After `core`. -/
structure T3 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  kvh : KVH P s₀ (kvI P s₀ i).1 (vC P s₀ i) t
  cnt : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)
  lt : i < P.c.tries
  fails : ∀ j < i, sigI P s₀ j = none
  sy : t.syms = s₀.syms
  res : ResultIs P s₀ (sigI P s₀ i) t

/-- After `goOn`. -/
def T4 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop :=
  KVH P s₀ (kvI P s₀ i).1 (vC P s₀ i) t ∧ i < P.c.tries ∧ (∀ j < i, sigI P s₀ j = none) ∧
    t.syms = s₀.syms ∧ isa.eval (.nonzero .t6) t = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries))

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem t0_ok {i : Nat} {t : State} (h : LoopInv P s₀ i t) : WP isa P.c.cand t (T0 P s₀ i) :=
  WP.mono (cand_ok hp h.kvh h.sy) fun _ ⟨k, T, c, y⟩ => ⟨k, T, by rw [c, h.cnt], h.lt, h.fails, y⟩

theorem t2_ok {i : Nat} {t : State} (h : T0 P s₀ i t) : WP isa (.block P.c.coreArgs) t (T2 P s₀ i) :=
  VG.RISCV64.WP.mono_syms (coreArgs_ok hp h.kvh h.sy) fun _ ⟨k, pr, mm, a⟩ y =>
    ⟨⟨k, by rw [mm]; exact h.T, by rw [pr _ (by decide), h.cnt], h.lt, h.fails, y.trans h.sy⟩, a⟩

theorem t3_ok {i : Nat} {t : State} (h : T2 P s₀ i t) : WP isa (.call P.c.coreN P.c.coreC) t (T3 P s₀ i) :=
  VG.RISCV64.WP.mono_syms (coreCall_ok hp h.1.kvh (sg_eq hp h.1.kvh.kr h.1.kvh.x h.1.T) h.2)
    fun _ ⟨k, pr, r⟩ y => ⟨k, by rw [pr _ (by decide), h.1.cnt], h.1.lt, h.1.fails, y.trans h.1.sy, r⟩

omit hp in
theorem t4_ok {i : Nat} {t : State} (h : T3 P s₀ i t) : WP isa (.block Cfg.goOn) t (T4 P s₀ i) :=
  VG.RISCV64.WP.mono_syms (goOn_ok h.kvh h.lt h.cnt h.res) fun _ ⟨k, _, _, e⟩ y =>
    ⟨k, h.lt, h.fails, y.trans h.sy, e⟩

end

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq hc

/-- Two runs of a candidate. -/
theorem tryOne_rel {i : Nat} :
    RelCT isa (fun t t' => LoopInv P s₀ i t ∧ LoopInv P s₀' i t') P.c.tryOne fun _ _ => True := by
  unfold Cfg.tryOne
  have r₁ := rel_wp (P₁ := LoopInv P s₀ i) (P₂ := LoopInv P s₀' i) (G₁ := T0 P s₀ i) (G₂ := T0 P s₀' i)
    ((cand_rel hp hp' hq hc).mono (fun _ _ h => ⟨⟨h.1.kvh, h.1.sy⟩, ⟨h.2.kvh, h.2.sy⟩⟩) fun _ _ _ => trivial)
    (fun _ h => t0_ok hp h) (fun _ h => t0_ok hp' h)
  have r₂ := rel_kr hq (P₁ := T0 P s₀ i) (P₂ := T0 P s₀' i) (G₁ := T2 P s₀ i) (G₂ := T2 P s₀' i)
    (fun _ h => h.kvh.kr) (fun _ h => h.kvh.kr) hc.ca (fun _ h => t2_ok hp h) (fun _ h => t2_ok hp' h)
  have r₃ : RelCT isa (fun t t' => T2 P s₀ i t ∧ T2 P s₀' i t') (.call P.c.coreN P.c.coreC)
      fun t t' => T3 P s₀ i t ∧ T3 P s₀' i t' := by
    refine rel_wp ?_ (fun _ h => t3_ok hp h) (fun _ h => t3_ok hp' h)
    rw [P.hcC]
    refine P.kit.core_rel (f := s₀.syms) fun t t' ⟨h, h'⟩ => ⟨h.2, ?_, by rw [h.1.kvh.kr.sp, h'.1.kvh.kr.sp, hq.sp],
      fun cn hcn => ⟨by rw [h.1.sy], by rw [h'.1.sy]; exact (hq.sy cn hcn).symm⟩⟩
    have a := h'.2
    rwa [hq.sA, hq.sA, show out s₀' = out s₀ from hq.a0.symm, show dk s₀' = dk s₀ from hq.a1.symm,
      show scr s₀' = scr s₀ from hq.a4.symm] at a
  have r₄ := rel_agree (P₁ := T3 P s₀ i) (P₂ := T3 P s₀' i) (G₁ := T4 P s₀ i) (G₂ := T4 P s₀' i) (rs := [.s5])
    (fun t t' h h' => ⟨by rw [h.kvh.kr.sp, h'.kvh.kr.sp, hq.sp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.cnt, h'.cnt]⟩) hc.go
    (fun _ h => t4_ok h) (fun _ h => t4_ok h)
  have r₅ : RelCT isa (fun t t' => T4 P s₀ i t ∧ T4 P s₀' i t')
      (.ite (.nonzero .t6) (.seq P.c.rekey (.block Cfg.again)) (.block Cfg.stop)) fun _ _ => True := by
    refine RelCT.ite (fun t t' ⟨h, h'⟩ => ?_) ?_ ?_
    · rw [h.2.2.2.2, h'.2.2.2.2]
      congr 1
      exact decide_eq_decide.mpr ((go_iff h.2.1 h.2.2.1).trans (by rw [hq.exitAt]) |>.trans
        (go_iff h'.2.1 h'.2.2.1).symm)
    · obtain ⟨_, ha⟩ := hc.ag
      refine ((rekey_kk hp hp' hq hc).mono (fun _ _ h => ⟨⟨h.1.1.1.kr, h.1.1.2.2.2.1⟩,
        ⟨h.1.2.1.kr, h.1.2.2.2.2.1⟩⟩) fun _ _ h => h).seq
        ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun t t' h => ⟨by rw [h.1.1.sp, h.2.1.sp, hq.sp], fun r hr => by
          simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩) ha))
    · obtain ⟨_, hs⟩ := hc.st
      exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun t t' h => ⟨by
        rw [h.1.1.1.kr.sp, h.1.2.1.kr.sp, hq.sp], fun r hr => by
          simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩) hs
  exact r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))

/-- Two runs of the loop. -/
theorem loop_rel :
    RelCT isa (fun t t' => LoopInv P s₀ 0 t ∧ LoopInv P s₀' 0 t') (.loop P.c.tryOne (.nonzero .t6))
      fun t t' => (∃ i, Exit P s₀ i t) ∧ ∃ i, Exit P s₀' i t' := by
  refine (RelCT.loop (Q := fun t t' => (∃ i, Exit P s₀ i t) ∧ ∃ i, Exit P s₀' i t')
    (fun n t t' => ∃ i, n = P.c.tries - i ∧ LoopInv P s₀ i t ∧ LoopInv P s₀' i t')
    (fun n => RelCT.exists_ fun i => ?_) P.c.tries).mono (fun t t' h => ⟨0, rfl, h⟩) fun _ _ h => h
  by_cases hn : n = P.c.tries - i
  · subst hn
    refine ((tryOne_rel hp hp' hq hc).wp
      (F₁ := fun u => (i < P.c.tries ∧ ∀ j < i, sigI P s₀ j = none) ∧ _)
      (F₂ := fun u => (i < P.c.tries ∧ ∀ j < i, sigI P s₀' j = none) ∧ _)
      fun t t' h => ⟨WP.mono (tryOne_ok hp h.1) fun u x => ⟨⟨h.1.lt, h.1.fails⟩, x⟩,
        WP.mono (tryOne_ok hp' h.2) fun u x => ⟨⟨h.2.lt, h.2.fails⟩, x⟩⟩).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩)
      fun u u' ⟨_, ⟨⟨hi, hf⟩, e, on, off⟩, ⟨⟨hi', hf'⟩, e', on', off'⟩⟩ => ?_
    have hg : (sigI P s₀ i = none ∧ i + 1 < P.c.tries) ↔ (sigI P s₀' i = none ∧ i + 1 < P.c.tries) :=
      (go_iff hi hf).trans (by rw [hq.exitAt]) |>.trans (go_iff hi' hf').symm
    refine ⟨by rw [e, e', decide_eq_decide.mpr hg], fun hz => ?_, fun hz => ?_⟩
    · have hn : ¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) := by
        intro h'; rw [e, decide_eq_true h'] at hz; cases hz
      exact ⟨⟨i, off hn⟩, i, off' (fun h' => hn (hg.mpr h'))⟩
    · have hy : sigI P s₀ i = none ∧ i + 1 < P.c.tries := by
        by_contra h'; rw [e, decide_eq_false h'] at hz; cases hz
      exact ⟨P.c.tries - (i + 1), by omega, i + 1, rfl, on hy, on' (hg.mp hy)⟩
  · exact RelCT.of_false fun _ _ h => hn h.1

end

/-! ## The whole function -/

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- Steps d–g, in the form `kv0` gives. -/
theorem stagesDG_ok {s : State} (h : KVH P s₀ (List.replicate P.H.D 0) (List.replicate P.H.D 1) s)
    (hsy : s.syms = s₀.syms) :
    WP isa (.seq (P.c.rekeyFull 0) (P.c.rekeyFull 1)) s (KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2) := by
  refine WP.seq (VG.RISCV64.WP.mono_syms (rekeyFull_ok hp h hsy (b := 0) (by decide)) fun s₄ h₄ y₄ => ?_)
  refine WP.mono (rekeyFull_ok hp h₄ (y₄.trans hsy) (b := 1) (by decide)) fun s₅ h₅ => ?_
  have e := kv0_eq P s₀
  rw [e]
  exact h₅

omit hp in
/-- The candidates left: `LoopInv` before the first. -/
theorem initCnt_ok {s : State} (h : KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2 s) (hsy : s.syms = s₀.syms) :
    WP isa (.block P.c.initCnt) s (LoopInv P s₀ 0) := by
  unfold Cfg.initCnt
  refine VG.RISCV64.WP.of_syms (wp_li (imm := P.c.tries) P.hT' fun s₆ u₆ => WP.block_nil fun y₆ => ?_)
  refine ⟨P.hT, ⟨h.kr.upd (by decide) u₆, ?_, ?_, ?_, ?_⟩, by rw [u₆.gpr, Nat.sub_zero],
    fun j hj => absurd hj (by omega), y₆.trans hsy⟩
  · rw [u₆.mem]; exact h.k
  · rw [u₆.mem]; exact h.v
  · rw [u₆.mem]; exact h.h
  · rw [u₆.mem]; exact h.x

end

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq hc

/-- Two runs of the frame's body. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') P.c.main fun _ _ => True := by
  unfold Cfg.main
  have rp := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀')
    (G₁ := Sy s₀ (KR P s₀)) (G₂ := Sy s₀' (KR P s₀'))
    (rs := [.a0, .a1, .a2, .a4, .a5]) (fun s s' h h' => by
      subst h h'
      refine ⟨hq.sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hq.a0, hq.a1, hq.a2, hq.a4, hq.a5]) hc.pro
    (fun s h => by subst h; exact wp_sy (prologue_ok hp) rfl) (fun s h => by subst h; exact wp_sy (prologue_ok hp') rfl)
  have rx := rel_kr hq (P₁ := Sy s₀ (KR P s₀)) (P₂ := Sy s₀' (KR P s₀'))
    (G₁ := Sy s₀ fun t => KR P s₀ t ∧ xOfM P s₀ t.mem = xSpec P s₀)
    (G₂ := Sy s₀' fun t => KR P s₀' t ∧ xOfM P s₀' t.mem = xSpec P s₀')
    (fun _ h => h.1) (fun _ h => h.1) hc.px
    (sy_of fun s h _ => WP.mono (prepX_ok hp h) fun _ h => ⟨h.1, h.2.1⟩)
    (sy_of fun s h _ => WP.mono (prepX_ok hp' h) fun _ h => ⟨h.1, h.2.1⟩)
  have rh := rel_kr hq (P₁ := Sy s₀ fun t => KR P s₀ t ∧ xOfM P s₀ t.mem = xSpec P s₀)
    (P₂ := Sy s₀' fun t => KR P s₀' t ∧ xOfM P s₀' t.mem = xSpec P s₀')
    (G₁ := Sy s₀ fun t => KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀ ∧ xOfM P s₀ t.mem = xSpec P s₀)
    (G₂ := Sy s₀' fun t => KR P s₀' t ∧ hOf P s₀' t.mem = hSpec P s₀' ∧ xOfM P s₀' t.mem = xSpec P s₀')
    (fun _ h => h.1.1) (fun _ h => h.1.1) hc.ph
    (sy_of fun s h _ => WP.mono (prepH_ok hp h.1 h.2) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (sy_of fun s h _ => WP.mono (prepH_ok hp' h.1 h.2) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  have rk := rel_kr hq (P₁ := Sy s₀ fun t => KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀ ∧ xOfM P s₀ t.mem = xSpec P s₀)
    (P₂ := Sy s₀' fun t => KR P s₀' t ∧ hOf P s₀' t.mem = hSpec P s₀' ∧ xOfM P s₀' t.mem = xSpec P s₀')
    (G₁ := Sy s₀ (KVH P s₀ (List.replicate P.H.D 0) (List.replicate P.H.D 1)))
    (G₂ := Sy s₀' (KVH P s₀' (List.replicate P.H.D 0) (List.replicate P.H.D 1)))
    (fun _ h => h.1.1) (fun _ h => h.1.1) hc.kv
    (sy_of fun s h _ => initKV_ok hp h.1 h.2.1 h.2.2) (sy_of fun s h _ => initKV_ok hp' h.1 h.2.1 h.2.2)
  have rd : RelCT isa (fun t t' => Sy s₀ (KVH P s₀ (List.replicate P.H.D 0) (List.replicate P.H.D 1)) t ∧
        Sy s₀' (KVH P s₀' (List.replicate P.H.D 0) (List.replicate P.H.D 1)) t')
      (.seq (P.c.rekeyFull 0) (P.c.rekeyFull 1))
      fun t t' => Sy s₀ (KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2) t ∧ Sy s₀' (KVH P s₀' (kv0 P s₀').1 (kv0 P s₀').2) t' :=
    rel_wp (((rekeyFull_kk hp hp' hq hc (b := 0) (by decide) hc.sep0).seq
        (rekeyFull_kk hp hp' hq hc (b := 1) (by decide) hc.sep1)).mono
        (fun _ _ h => ⟨⟨h.1.1.kr, h.1.2⟩, ⟨h.2.1.kr, h.2.2⟩⟩) fun _ _ _ => trivial)
      (sy_of fun s h hs => stagesDG_ok hp h hs) (sy_of fun s h hs => stagesDG_ok hp' h hs)
  have rc := rel_agree (P₁ := Sy s₀ (KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2))
    (P₂ := Sy s₀' (KVH P s₀' (kv0 P s₀').1 (kv0 P s₀').2)) (G₁ := LoopInv P s₀ 0) (G₂ := LoopInv P s₀' 0)
    (rs := []) (fun s s' h h' => ⟨by rw [h.1.kr.sp, h'.1.kr.sp, hq.sp], fun _ h => absurd h (by simp)⟩) hc.cnt
    (fun s h => initCnt_ok h.1 h.2) (fun s h => initCnt_ok h.1 h.2)
  have rl := loop_rel hp hp' hq hc
  obtain ⟨_, hf⟩ := hc.fin
  have re : RelCT isa (fun t t' => (∃ i, Exit P s₀ i t) ∧ ∃ i, Exit P s₀' i t') (.block (Cfg.wipe ++ Cfg.restore))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.s1]) (fun t t' ⟨⟨i, x⟩, ⟨i', x'⟩⟩ => ⟨by rw [x.kr.sp, x'.kr.sp, hq.sp],
      fun r hr => by
        rw [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr
        rw [x.kr.s1, x'.kr.s1, hq.sp]⟩) hf
  exact rp.seq (rx.seq (rh.seq (rk.seq (RelCT.assoc (rd.seq (rc.seq (rl.seq re)))))))

end

/-! ## The frame -/

/-- Two runs of a frame allocating `n` bytes, which leaks nothing itself. -/
theorem rel_alloc {n : Nat} {body : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (fun a b => ∃ s₁ s₂, Q s₁ s₂ ∧ a = allocd n s₁ ∧ b = allocd n s₂) body fun _ _ => True) :
    RelCT isa Q (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hpush : ∀ {s a : State}, isa.push (.alloc n) s = some a → a = allocd n s := by
    intro s a h'
    simp only [isa, push] at h'
    split at h' <;> cases h'
    rfl
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea := hpush p₁
      have eb := hpush p₂
      subst ea eb
      obtain ⟨rfl, -⟩ := h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

/-- The function is constant time but for the number of candidates, given
the taint checks of its pieces, for runs whose public data name the
table's functions' addresses (`ns`). -/
theorem ct (hc : Checks P.c) {ns : List String} (hns : ∀ n ∈ [P.w.hiN, P.H.updN, P.w.hfN], n ∈ ns) :
    ConstantTime isa (rfcRC P.kit.K P.I P.w P.c.f ns P.N).pre (rfcRC P.kit.K P.I P.w P.c.f ns P.N).pub P.c.sign := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc h; have hp' := pre_alloc h'
  obtain ⟨⟨qsp, q0, q1, q2, q4, q5, qlk, qn⟩, qsy⟩ := hpub
  have hq : PubEq P (allocd frB e) (allocd frB e') :=
    ⟨q0, q1, q2, q4, q5, by simp only [allocd, qsp], qlk, qsy, fun n hn => qn n (hns n hn)⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q P.c.sign fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold Cfg.sign
  refine rel_alloc ((main_rel hp hp' hq hc).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end VG.Proof.Ecdsa.Rfc6979.RISCV64
