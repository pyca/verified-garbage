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

end VG.Proof.Ecdsa.Rfc6979.RISCV64
