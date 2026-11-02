module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Correct
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on RISC-V: constant time, up to the number of candidates

As for PBKDF2 (`Proof/Pbkdf2/Whole/RISCV64/CT.lean`): two runs from states
whose public data agree (`PubEq`: the pointers, the stack pointer and the
number of candidates RFC 6979 tries, which the contract lets leak) are
related piece by piece. The code between the calls of HMAC's `init` and
`finalize` and of the signature with a given `k`, the calls of the
streaming `update` and of the order's addition included, is checked by the
taint analysis (`Checks`, which the kernel evaluates for each hash
function), from the registers that hold pointers; the calls whose callees
restore the callee-saved registers from memory are related by their
contracts (`hi_rel`, `hf_rel`, `core_rel`), with the arguments each run's
correctness gives. Each run's correctness then says what the registers hold
after a piece (`RelCT.wp`), so that they agree again. The loop's branch
agrees, since in both runs it goes on after candidate `i` iff `i` is before
the candidate it stops at (`go_iff`, `exitAt`); the frame's `alloc` and
`free` leak nothing (`rel_alloc`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (eval_nonzero wp_li)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open Spec.Sha256 (bytesAt)

/-- A piece of code the taint analysis accepts with the registers `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true

/-- The taint checks of `update`'s arguments for the parts of a message. -/
def UpdCks (c : Cfg) : Nat → List Part → Prop
  | _, [] => True
  | cnt, p :: ps => Ck [.s0, .s1, .s3] (.block (c.updArgs cnt p)) ∧ UpdCks c (cnt + p.2.2) ps

/-- The parts of the messages of steps d and f, of `V = HMAC_K(V)` and of step h.3. -/
abbrev fullParts (c : Cfg) : List Part := [(.s1, fV, c.H.D + 1), (.s3, 0, c.Q), (.s1, fH, c.Q)]
abbrev vParts (c : Cfg) : List Part := [(.s1, fV, c.H.D)]
abbrev rParts (c : Cfg) : List Part := [(.s1, fV, c.H.D + 1)]

/-- The taint checks of the pieces of the function between the calls of
HMAC's `init` and `finalize` and of the signature. -/
structure Checks (c : Cfg) : Prop where
  pro : Ck [.a0, .a1, .a2, .a3] (.block Cfg.prologue)
  red : Ck [.s0, .s1, .s4] c.reduce
  kv : Ck [.s1] (.block c.initKV)
  sep0 : Ck [.s1] (.block (c.sep 0))
  sep1 : Ck [.s1] (.block (c.sep 1))
  ia : Ck [.s0, .s1] (.block c.initArgs)
  uF : UpdCks c 0 (fullParts c)
  uV : UpdCks c 0 (vParts c)
  uR : UpdCks c 0 (rParts c)
  upd : Ck [.a0, .a1, .a2, .a3] c.H.callUpd
  fF : Ck [.s0, .s1] (.block (c.finArgs (total (fullParts c)) fK))
  fVc : Ck [.s0, .s1] (.block (c.finArgs (total (vParts c)) fV))
  fR : Ck [.s0, .s1] (.block (c.finArgs (total (rParts c)) fK))
  cnt : Ck [] (.block c.initCnt)
  ca : Ck [.s0, .s1, .s2, .s3, .s4] (.block Cfg.coreArgs)
  go : Ck [.s5] (.block Cfg.goOn)
  ag : Ck [] (.block Cfg.again)
  st : Ck [] (.block Cfg.stop)
  fin : Ck [.s1] (.block (c.wipe ++ Cfg.restore))

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (P : Rfc) (s₀ s₀' : State) : Prop where
  a0 : s₀.gpr .a0 = s₀'.gpr .a0
  a1 : s₀.gpr .a1 = s₀'.gpr .a1
  a2 : s₀.gpr .a2 = s₀'.gpr .a2
  a3 : s₀.gpr .a3 = s₀'.gpr .a3
  sp : s₀.sp = s₀'.sp
  lk : (result P.I s₀.mem (dk s₀) (dg s₀)).2 = (result P.I s₀'.mem (dk s₀') (dg s₀')).2
  sy : ∀ cn ∈ P.kit.K, s₀.syms cn.1 = s₀'.syms cn.1

variable {P : Rfc}

section
variable {s₀ s₀' : State} (hq : PubEq P s₀ s₀')
include hq

theorem PubEq.sA (o : Nat) : sA s₀' o = sA s₀ o := by simp only [RISCV64.sA, hq.sp]
theorem PubEq.cA (o : Nat) : cA s₀' o = cA s₀ o := by simp only [RISCV64.cA, scr, hq.a3]
theorem PubEq.pA (p : Part) : pA s₀' p = pA s₀ p := by
  obtain ⟨r, o, n⟩ := p
  simp only [RISCV64.pA]
  congr 1
  cases r <;> simp only [regV, dk, hq.sp, hq.a1]

/-- The pointer registers agree in two runs that keep `KR`. -/
theorem ag_kr {s s' : State} (h : KR P s₀ s) (h' : KR P s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ [Reg.s0, .s1, .s2, .s3, .s4], s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.s0, h'.s0, scr, scr, hq.a3]
  · rw [h.s1, h'.s1, hq.sp]
  · rw [h.s2, h'.s2, out, out, hq.a0]
  · rw [h.s3, h'.s3, dk, dk, hq.a1]
  · rw [h.s4, h'.s4, dg, dg, hq.a2]

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
    {rs : List Reg} (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3, .s4])
    (hk₁ : ∀ s, P₁ s → KR P s₀ s) (hk₂ : ∀ s, P₂ s → KR P s₀' s) (hc : Ck rs c)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' :=
  rel_agree (fun s s' h h' => by
    obtain ⟨e, g⟩ := ag_kr hq (hk₁ s h) (hk₂ s' h')
    exact ⟨e, fun r hr => g r (hrs r hr)⟩) hc hw hw'

/-- Two runs of an empty block. -/
theorem rel_nil {Q : State → State → Prop} : RelCT isa Q (.block []) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  rw [← e₁.2, ← e₂.2]; exact ⟨rfl, trivial⟩

/-! ## One HMAC -/

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq

/-- The parts absorbed, in two runs. -/
theorem upds_rel {σ σ' : State} : ∀ (ps : List Part) (cnt : Nat) {pre pre' : List Byte},
    pre.length = cnt → pre'.length = cnt → (∀ p ∈ ps, PartOk P p) → P.c.H.B + cnt + total ps < 2048 →
    UpdCks P.c cnt ps → Ck [.a0, .a1, .a2, .a3] P.c.H.callUpd →
    RelCT isa (fun t t' => HU P s₀ σ pre t ∧ HU P s₀' σ' pre' t') (P.c.upds cnt ps)
      fun t t' => HU P s₀ σ (pre ++ msgOf σ.mem s₀ ps) t ∧ HU P s₀' σ' (pre' ++ msgOf σ'.mem s₀' ps) t'
  | [], cnt, pre, pre', _, _, _, _, _, _ => by
    simp only [msgOf, List.append_nil]
    exact (rel_nil.wp (F₁ := HU P s₀ σ pre) (F₂ := HU P s₀' σ' pre') fun s s' h =>
      ⟨WP.block_nil h.1, WP.block_nil h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  | p :: ps, cnt, pre, pre', hl, hl', hps, hb, ⟨cu, cs⟩, cup => by
    have hpo : PartOk P p := hps p (by simp)
    have hlp : p.2.2 ≤ total (p :: ps) := by simp only [total]; omega
    subst hl
    unfold Cfg.upds
    have r₁ := rel_kr hq (P₁ := HU P s₀ σ pre) (P₂ := HU P s₀' σ' pre')
      (G₁ := HUA P s₀ σ pre p) (G₂ := HUA P s₀' σ' pre' p) (by decide)
      (fun _ h => h.1.kr) (fun _ h => h.1.kr) cu
      (fun s h => updArgs_ok h hpo.reg (by omega) hpo.off (by omega))
      (fun s h => by rw [← hl']; exact updArgs_ok h hpo.reg (by omega) hpo.off (by omega))
    have r₂ := rel_agree (P₁ := HUA P s₀ σ pre p) (P₂ := HUA P s₀' σ' pre' p)
      (fun s s' h h' => by
        refine ⟨by rw [h.1.1.kr.sp, h'.1.1.kr.sp, hq.sp], fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.2.1, h'.2.1, hq.cA]
        · rw [h.2.2.1, h'.2.2.1, hl']
        · rw [h.2.2.2.1, h'.2.2.2.1, hq.pA]
        · rw [h.2.2.2.2, h'.2.2.2.2]) cup
      (fun s h => updc_ok hp h hpo) (fun s h => updc_ok hp' h hpo)
    have e₁ : pre.length + p.2.2 = (pre ++ bytesAt σ.mem (pA s₀ p) p.2.2).length := by
      rw [List.length_append, VG.Proof.Hmac.Common.bytesAt_length]
    have r₃ := upds_rel (σ := σ) (σ' := σ') ps (pre.length + p.2.2) (pre := pre ++ bytesAt σ.mem (pA s₀ p) p.2.2)
      (pre' := pre' ++ bytesAt σ'.mem (pA s₀' p) p.2.2) e₁.symm
      (by rw [List.length_append, VG.Proof.Hmac.Common.bytesAt_length, hl'])
      (fun q hq' => hps q (by simp [hq'])) (by simp only [total] at hb; omega) cs cup
    refine ((r₁.seq r₂).seq r₃).mono (fun _ _ h => h) fun t t' h => ?_
    simp only [msgOf, List.append_assoc] at h ⊢
    exact h

/-- `HMAC_K(parts)` to `dst`, in two runs from `σ` and `σ'`. -/
theorem hmac_rel {σ σ' : State} (k : KR P s₀ σ) (k' : KR P s₀' σ') {ps : List Part}
    (hps : ∀ p ∈ ps, PartOk P p) (hb : P.c.H.B + total ps < 2048) {dst : Nat}
    (hdst : 64 ≤ dst ∧ dst + P.c.H.D ≤ P.c.frB) (cu : UpdCks P.c 0 ps)
    (cf : Ck [.s0, .s1] (.block (P.c.finArgs (total ps) dst))) (cia : Ck [.s0, .s1] (.block P.c.initArgs))
    (cup : Ck [.a0, .a1, .a2, .a3] P.c.H.callUpd) :
    RelCT isa (fun t t' => t = σ ∧ t' = σ') (P.c.hmac ps dst)
      fun t t' => HD P s₀ σ (msgOf σ.mem s₀ ps) dst t ∧ HD P s₀' σ' (msgOf σ'.mem s₀' ps) dst t' := by
  unfold Cfg.hmac
  have r₁ := rel_kr hq (P₁ := (· = σ)) (P₂ := (· = σ')) (G₁ := HI P s₀ σ) (G₂ := HI P s₀' σ')
    (by decide)
    (fun _ h => by subst h; exact k) (fun _ h => by subst h; exact k') cia
    (fun s h => by subst h; exact initArgs_ok k) (fun s h => by subst h; exact initArgs_ok k')
  have r₂ : RelCT isa (fun t t' => HI P s₀ σ t ∧ HI P s₀' σ' t') (.call P.c.hiN P.c.H.init)
      fun t t' => HK P s₀ σ t ∧ HK P s₀' σ' t' :=
    rel_wp (hi_rel fun t t' ⟨h, h'⟩ => by
        have a' := hi_args hp' h'
        rw [hq.cA, hq.cA, hq.sA] at a'
        exact ⟨hi_args hp h, a', by rw [h.1.kr.sp, h'.1.kr.sp, hq.sp]⟩)
      (fun s h => init_ok hp h) (fun s h => init_ok hp' h)
  have r₃ := upds_rel hp hp' hq (σ := σ) (σ' := σ') ps 0 (pre := []) (pre' := []) rfl rfl hps (by omega) cu cup
  have hl := msgOf_length σ.mem s₀ ps
  have hl' := msgOf_length σ'.mem s₀' ps
  have r₄ := rel_kr hq (P₁ := HU P s₀ σ (msgOf σ.mem s₀ ps)) (P₂ := HU P s₀' σ' (msgOf σ'.mem s₀' ps))
    (G₁ := HFA P s₀ σ (msgOf σ.mem s₀ ps) dst) (G₂ := HFA P s₀' σ' (msgOf σ'.mem s₀' ps) dst)
    (by decide)
    (fun _ h => h.1.kr) (fun _ h => h.1.kr) cf
    (fun s h => by rw [← hl]; exact finArgs_ok h dst (by omega) (by have := (sizes P).Q; omega))
    (fun s h => by rw [← hl']; exact finArgs_ok h dst (by omega) (by have := (sizes P).Q; omega))
  have r₅ : RelCT isa (fun t t' => HFA P s₀ σ (msgOf σ.mem s₀ ps) dst t ∧ HFA P s₀' σ' (msgOf σ'.mem s₀' ps) dst t')
      (.call P.c.hfN P.c.H.finalize)
      fun t t' => HD P s₀ σ (msgOf σ.mem s₀ ps) dst t ∧ HD P s₀' σ' (msgOf σ'.mem s₀' ps) dst t' :=
    rel_wp (hf_rel fun t t' ⟨h, h'⟩ => by
        have a' := hf_args hp' hdst h'
        rw [hq.cA, hq.cA, hq.sA] at a'
        exact ⟨hf_args hp hdst h, a', by rw [h.1.1.kr.sp, h'.1.1.kr.sp, hq.sp],
          by rw [h.2.2.2.1, h'.2.2.2.1, hl, hl']⟩)
      (fun s h => fin_ok hp hdst (by omega) h) (fun s h => fin_ok hp' hdst (by omega) h)
  refine (r₁.seq (r₂.seq ((r₃.mono (fun t t' h => ⟨h.1.hu, h.2.hu⟩) fun _ _ h => ?_).seq
    (r₄.seq r₅)))).mono (fun _ _ h => h) fun _ _ h => h
  simpa using h

end

/-! ## Pieces that keep `KR` -/

/-- Two runs that keep `KR`. -/
abbrev KK (P : Rfc) (s₀ s₀' : State) (t t' : State) : Prop := KR P s₀ t ∧ KR P s₀' t'

theorem initKV_kr {s₀ : State} (hp : Pre P s₀) {s : State} (h : KR P s₀ s) :
    WP isa (.block P.c.initKV) s (KR P s₀) := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.initKV
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hp h (doff := fK) (bs := List.replicate P.c.H.D 0) (fun i hi => by
      simp only [List.length_replicate] at hi; simp [List.getD_eq_getElem?_getD, hi])
    (by simp only [fK, List.length_replicate]; have := (sizes P).Q; omega)) fun t₁ h₁ => ?_
  exact WP.mono (store_ok hp h₁.1 (doff := fV) (bs := List.replicate P.c.H.D 1) (fun i hi => by
      simp only [List.length_replicate] at hi; simp [List.getD_eq_getElem?_getD, hi])
    (by simp only [fV, List.length_replicate]; have := (sizes P).Q; omega)) fun t₂ h₂ => h₂.1

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq hc

theorem hmac_kk {ps : List Part} (hps : ∀ p ∈ ps, PartOk P p) (hb : P.c.H.B + total ps < 2048) {dst : Nat}
    (hdst : 64 ≤ dst ∧ dst + P.c.H.D ≤ P.c.frB) (cu : UpdCks P.c 0 ps)
    (cf : Ck [.s0, .s1] (.block (P.c.finArgs (total ps) dst))) :
    RelCT isa (KK P s₀ s₀') (P.c.hmac ps dst) (KK P s₀ s₀') := by
  have ht : RelCT isa (KK P s₀ s₀') (P.c.hmac ps dst) fun _ _ => True :=
    fun s₁ s₂ t₁ t₂ s₁' s₂' h e₁ e₂ =>
      ⟨(hmac_rel hp hp' hq h.1 h.2 hps hb hdst cu cf hc.ia hc.upd _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, trivial⟩
  exact (rel_wp (P₁ := KR P s₀) (P₂ := KR P s₀') ht (fun s h => WP.mono (hmac_ok hp h hps hb hdst) fun _ h => h.1)
    fun s h => WP.mono (hmac_ok hp' h hps hb hdst) fun _ h => h.1).mono (fun _ _ h => h) fun _ _ h => h

theorem hmacV_kk : RelCT isa (KK P s₀ s₀') P.c.hmacV (KK P s₀ s₀') := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  exact hmac_kk hp hp' hq hc (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact .inl ⟨rfl, by simp only [fV]; omega, by simp only [fV]; have := (sizes P).Q; omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega) ⟨by decide, by simp only [fV]; have := (sizes P).Q; omega⟩
    hc.uV hc.fVc

omit hc in
theorem sep_kk {b : Nat} (hb : b < 256) (cs : Ck [.s1] (.block (P.c.sep b))) :
    RelCT isa (KK P s₀ s₀') (.block (P.c.sep b)) (KK P s₀ s₀') := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  have hw : ∀ {σ : State} (hσ : Pre P σ) {s : State}, KR P σ s → WP isa (.block (P.c.sep b)) s (KR P σ) :=
    fun hσ s h => WP.mono (store_ok hσ h (doff := fV + P.c.H.D) (bs := [b]) (fun i hi => by
      simp only [List.length_singleton] at hi; obtain rfl : i = 0 := by omega
      simpa using hb) (by simp only [fV, List.length_singleton]; have := (sizes P).Q; omega)) fun _ h => h.1
  exact (rel_kr hq (by decide) (fun _ h => h) (fun _ h => h) cs (fun s h => hw hp h) fun s h => hw hp' h).mono
    (fun _ _ h => h) fun _ _ h => h

theorem rekeyFull_kk {b : Nat} (hb : b < 256) (cs : Ck [.s1] (.block (P.c.sep b))) :
    RelCT isa (KK P s₀ s₀') (P.c.rekeyFull b) (KK P s₀ s₀') := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.rekeyFull
  refine (sep_kk hp hp' hq hb cs).seq ((hmac_kk hp hp' hq hc (fun p hp' => ?_) ?_ ⟨by decide, ?_⟩ hc.uF
    hc.fF).seq (hmacV_kk hp hp' hq hc))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · exact .inl ⟨rfl, by simp only [fV]; omega, by simp only [fV]; have := (sizes P).Q; omega⟩
    · exact .inr ⟨rfl, rfl, Nat.le_of_eq (sizes P).Q.2.2.1⟩
    · exact .inl ⟨rfl, by simp only [fH]; omega, by simp only [fH]; have := (sizes P).Q; omega⟩
  · simp only [total]; have := (sizes P).Q; rcases hz.B with h' | h' <;> omega
  · simp only [fK]; have := (sizes P).Q; omega

theorem rekey_kk : RelCT isa (KK P s₀ s₀') P.c.rekey (KK P s₀ s₀') := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.rekey
  refine (sep_kk hp hp' hq (b := 0) (by decide) hc.sep0).seq ((hmac_kk hp hp' hq hc (fun p hp' => ?_) ?_
    ⟨by decide, ?_⟩ hc.uR hc.fR).seq (hmacV_kk hp hp' hq hc))
  · simp only [List.mem_singleton] at hp'; subst hp'
    exact .inl ⟨rfl, by simp only [fV]; omega, by simp only [fV]; have := (sizes P).Q; omega⟩
  · simp only [total]; rcases hz.B with h' | h' <;> omega
  · simp only [fK]; have := (sizes P).Q; omega

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
    rw [VG.Proof.Ecdsa.Rfc6979.search_shift (blocks_one P) i P.c.tries (by omega) hf,
      show P.c.tries - i = (P.c.tries - 1 - i) + 1 by omega]
    cases hs : sigI P s₀ i with
    | some rs =>
      rw [VG.Proof.Ecdsa.Rfc6979.search_ok (blocks_one P) hs]
      simp
    | none =>
      rw [VG.Proof.Ecdsa.Rfc6979.search_fail (blocks_one P) hs]
      by_cases h7 : i + 1 < P.c.tries
      · have := VG.Proof.Ecdsa.Rfc6979.search_pos (C := P.kit.E.curve) (H := P.hH.SH.H) (hlen := P.c.H.D)
          (d := xOf P s₀) (e := eOf P s₀) (n := P.c.tries - 2 - i)
          (K := (VG.Proof.Ecdsa.Rfc6979.step P.hH.SH.H
            (VG.Proof.Ecdsa.Rfc6979.kvAt P.hH.SH.H (kv0 P s₀).1 (kv0 P s₀).2 i).1
            (VG.Proof.Ecdsa.Rfc6979.kvAt P.hH.SH.H (kv0 P s₀).1 (kv0 P s₀).2 i).2).1)
          (V := (VG.Proof.Ecdsa.Rfc6979.step P.hH.SH.H
            (VG.Proof.Ecdsa.Rfc6979.kvAt P.hH.SH.H (kv0 P s₀).1 (kv0 P s₀).2 i).1
            (VG.Proof.Ecdsa.Rfc6979.kvAt P.hH.SH.H (kv0 P s₀).1 (kv0 P s₀).2 i).2).2) (blocks_one P)
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

/-- What every piece of a candidate needs: `K`, the candidate `V` and the
candidates left, and that the earlier candidates failed. -/
structure T1 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  kvh : KVH P s₀ (kvI P s₀ i).1 (candI P s₀ i) t
  cnt : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)
  lt : i < P.c.tries
  fails : ∀ j < i, sigI P s₀ j = none
  sy : t.syms = s₀.syms

/-- After `core`'s arguments. -/
def T2 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop :=
  T1 P s₀ i t ∧ CoreArgs (8 * P.kit.nw) P.kit.K t (out s₀) (dk s₀) (dg s₀) (sA s₀ fV) (scr s₀)

/-- After `core`. -/
def T3 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop :=
  T1 P s₀ i t ∧ ResultIs P s₀ (sigI P s₀ i) t

/-- After `goOn`. -/
def T4 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop :=
  KVH P s₀ (kvI P s₀ i).1 (candI P s₀ i) t ∧ i < P.c.tries ∧ (∀ j < i, sigI P s₀ j = none) ∧
    isa.eval (.nonzero .t6) t = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries))

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem t1_ok {i : Nat} {t : State} (h : LoopInv P s₀ i t) : WP isa P.c.hmacV t (T1 P s₀ i) :=
  VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (hmacV_ok hp h.kvh) fun _ ⟨k, pr⟩ y =>
    ⟨k, by rw [pr _ (by decide), h.cnt], h.lt, h.fails, y.trans h.sy⟩

theorem t2_ok {i : Nat} {t : State} (h : T1 P s₀ i t) : WP isa (.block Cfg.coreArgs) t (T2 P s₀ i) :=
  VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (coreArgs_ok hp h.kvh h.sy) fun _ ⟨k, pr, a⟩ y =>
    ⟨⟨k, by rw [pr _ (by decide), h.cnt], h.lt, h.fails, y.trans h.sy⟩, a⟩

theorem t3_ok {i : Nat} {t : State} (h : T2 P s₀ i t) : WP isa (.call P.c.coreN P.c.coreC) t (T3 P s₀ i) :=
  VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (coreCall_ok hp h.1.kvh (i := i) rfl h.2) fun _ ⟨k, pr, r⟩ y =>
    ⟨⟨k, by rw [pr _ (by decide), h.1.cnt], h.1.lt, h.1.fails, y.trans h.1.sy⟩, r⟩

omit hp in
theorem t4_ok {i : Nat} {t : State} (h : T3 P s₀ i t) : WP isa (.block Cfg.goOn) t (T4 P s₀ i) :=
  WP.mono (goOn_ok h.1.kvh h.1.lt h.1.cnt h.2) fun _ ⟨k, _, _, e⟩ => ⟨k, h.1.lt, h.1.fails, e⟩

end

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq hc

/-- Two runs of a candidate. -/
theorem tryOne_rel {i : Nat} :
    RelCT isa (fun t t' => LoopInv P s₀ i t ∧ LoopInv P s₀' i t') P.c.tryOne fun _ _ => True := by
  unfold Cfg.tryOne
  have r₁ := rel_wp (P₁ := LoopInv P s₀ i) (P₂ := LoopInv P s₀' i) (G₁ := T1 P s₀ i) (G₂ := T1 P s₀' i)
    ((hmacV_kk hp hp' hq hc).mono (fun _ _ h => ⟨h.1.kvh.kr, h.2.kvh.kr⟩) fun _ _ _ => trivial)
    (fun _ h => t1_ok hp h) (fun _ h => t1_ok hp' h)
  have r₂ := rel_kr hq (P₁ := T1 P s₀ i) (P₂ := T1 P s₀' i) (G₁ := T2 P s₀ i) (G₂ := T2 P s₀' i) (by decide)
    (fun _ h => h.kvh.kr) (fun _ h => h.kvh.kr) hc.ca (fun _ h => t2_ok hp h) (fun _ h => t2_ok hp' h)
  have r₃ : RelCT isa (fun t t' => T2 P s₀ i t ∧ T2 P s₀' i t') (.call P.c.coreN P.c.coreC)
      fun t t' => T3 P s₀ i t ∧ T3 P s₀' i t' := by
    refine rel_wp ?_ (fun _ h => t3_ok hp h) (fun _ h => t3_ok hp' h)
    rw [P.hcC]
    refine P.kit.core_rel (f := s₀.syms) fun t t' ⟨h, h'⟩ => ⟨h.2, ?_, by rw [h.1.kvh.kr.sp, h'.1.kvh.kr.sp, hq.sp],
      fun cn hcn => ⟨by rw [h.1.sy], by rw [h'.1.sy]; exact (hq.sy cn hcn).symm⟩⟩
    have a := h'.2
    rwa [hq.sA, show out s₀' = out s₀ from hq.a0.symm, show dk s₀' = dk s₀ from hq.a1.symm,
      show dg s₀' = dg s₀ from hq.a2.symm, show scr s₀' = scr s₀ from hq.a3.symm] at a
  have r₄ := rel_agree (P₁ := T3 P s₀ i) (P₂ := T3 P s₀' i) (G₁ := T4 P s₀ i) (G₂ := T4 P s₀' i) (rs := [.s5])
    (fun t t' h h' => ⟨by rw [h.1.kvh.kr.sp, h'.1.kvh.kr.sp, hq.sp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.cnt, h'.1.cnt]⟩) hc.go
    (fun _ h => t4_ok h) (fun _ h => t4_ok h)
  have r₅ : RelCT isa (fun t t' => T4 P s₀ i t ∧ T4 P s₀' i t')
      (.ite (.nonzero .t6) (.seq P.c.rekey (.block Cfg.again)) (.block Cfg.stop)) fun _ _ => True := by
    refine RelCT.ite (fun t t' ⟨h, h'⟩ => ?_) ?_ ?_
    · rw [h.2.2.2, h'.2.2.2]
      congr 1
      exact decide_eq_decide.mpr ((go_iff h.2.1 h.2.2.1).trans (by rw [hq.exitAt]) |>.trans
        (go_iff h'.2.1 h'.2.2.1).symm)
    · obtain ⟨_, ha⟩ := hc.ag
      refine ((rekey_kk hp hp' hq hc).mono (fun _ _ h => ⟨h.1.1.1.kr, h.1.2.1.kr⟩) fun _ _ h => h).seq
        ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun t t' h => ⟨by rw [h.1.sp, h.2.sp, hq.sp], fun r hr => by
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

/-- What follows code from a state naming the symbols as `s₀` does names them so too. -/
theorem wp_sy {s₀ s : State} {c : Prog isa} {Q : State → Prop} (h : WP isa c s Q) (hs : s.syms = s₀.syms) :
    WP isa c s fun t => Q t ∧ t.syms = s₀.syms :=
  VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms h fun _ q y => ⟨q, y.trans hs⟩

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem reduceKR_ok {s : State} (h : KR P s₀ s) :
    WP isa P.c.reduce s fun t => KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀ :=
  WP.mono (reduce_ok hp h) fun _ h => ⟨h.1, h.2.1⟩

omit hp in
/-- The candidates left: `LoopInv` before the first. -/
theorem initCnt_ok {s : State}
    (h : KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2 s) (hsy : s.syms = s₀.syms) :
    WP isa (.block P.c.initCnt) s (LoopInv P s₀ 0) := by
  unfold Cfg.initCnt
  refine VG.Proof.Ecdsa.RISCV64.Comb.WP.of_syms (wp_li (imm := P.c.tries) P.hT' fun s₆ u₆ =>
    WP.block_nil fun y₆ => ?_)
  refine ⟨P.hT, ⟨h.kr.upd (by decide) u₆, ?_, ?_, ?_⟩, by rw [u₆.gpr, Nat.sub_zero], fun j hj => absurd hj (by omega),
    y₆.trans hsy⟩
  · rw [u₆.mem]; exact h.k
  · rw [u₆.mem]; exact h.v
  · rw [u₆.mem]; exact h.h

/-- Steps d–g, in the form `kv0` gives. -/
theorem stagesDG_ok {s : State} (h : KVH P s₀ (List.replicate P.c.H.D 0) (List.replicate P.c.H.D 1) s) :
    WP isa (.seq (P.c.rekeyFull 0) (P.c.rekeyFull 1)) s (KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2) := by
  refine WP.seq (WP.mono (rekeyFull_ok hp h (b := 0) (by decide)) fun s₄ h₄ => ?_)
  refine WP.mono (rekeyFull_ok hp h₄ (b := 1) (by decide)) fun s₅ h₅ => ?_
  have e := kv0_eq P s₀
  rw [e]
  exact h₅

end

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq hc

/-- Two runs of the frame's body. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') P.c.main fun _ _ => True := by
  unfold Cfg.main
  have rp := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀')
    (G₁ := fun t => KR P s₀ t ∧ t.syms = s₀.syms) (G₂ := fun t => KR P s₀' t ∧ t.syms = s₀'.syms)
    (rs := [.a0, .a1, .a2, .a3]) (fun s s' h h' => by
      subst h h'
      refine ⟨hq.sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.a0, hq.a1, hq.a2, hq.a3]) hc.pro
    (fun s h => by subst h; exact wp_sy (prologue_ok hp) rfl) (fun s h => by subst h; exact wp_sy (prologue_ok hp') rfl)
  have rr := rel_kr hq (P₁ := fun t => KR P s₀ t ∧ t.syms = s₀.syms) (P₂ := fun t => KR P s₀' t ∧ t.syms = s₀'.syms)
    (G₁ := fun t => (KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀) ∧ t.syms = s₀.syms)
    (G₂ := fun t => (KR P s₀' t ∧ hOf P s₀' t.mem = hSpec P s₀') ∧ t.syms = s₀'.syms)
    (by decide) (fun _ h => h.1) (fun _ h => h.1) hc.red
    (fun s h => wp_sy (reduceKR_ok hp h.1) h.2) (fun s h => wp_sy (reduceKR_ok hp' h.1) h.2)
  have rk := rel_kr hq (P₁ := fun t => (KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀) ∧ t.syms = s₀.syms)
    (P₂ := fun t => (KR P s₀' t ∧ hOf P s₀' t.mem = hSpec P s₀') ∧ t.syms = s₀'.syms)
    (G₁ := fun t => KVH P s₀ (List.replicate P.c.H.D 0) (List.replicate P.c.H.D 1) t ∧ t.syms = s₀.syms)
    (G₂ := fun t => KVH P s₀' (List.replicate P.c.H.D 0) (List.replicate P.c.H.D 1) t ∧ t.syms = s₀'.syms)
    (by decide) (fun _ h => h.1.1) (fun _ h => h.1.1) hc.kv
    (fun s h => wp_sy (initKV_ok hp h.1.1 h.1.2) h.2) (fun s h => wp_sy (initKV_ok hp' h.1.1 h.1.2) h.2)
  have rd : RelCT isa (fun t t' =>
        (KVH P s₀ (List.replicate P.c.H.D 0) (List.replicate P.c.H.D 1) t ∧ t.syms = s₀.syms) ∧
        (KVH P s₀' (List.replicate P.c.H.D 0) (List.replicate P.c.H.D 1) t' ∧ t'.syms = s₀'.syms))
      (.seq (P.c.rekeyFull 0) (P.c.rekeyFull 1))
      fun t t' => (KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2 t ∧ t.syms = s₀.syms) ∧
        (KVH P s₀' (kv0 P s₀').1 (kv0 P s₀').2 t' ∧ t'.syms = s₀'.syms) :=
    rel_wp (((rekeyFull_kk hp hp' hq hc (b := 0) (by decide) hc.sep0).seq
        (rekeyFull_kk hp hp' hq hc (b := 1) (by decide) hc.sep1)).mono (fun _ _ h => ⟨h.1.1.kr, h.2.1.kr⟩)
        fun _ _ _ => trivial)
      (fun s h => wp_sy (stagesDG_ok hp h.1) h.2) (fun s h => wp_sy (stagesDG_ok hp' h.1) h.2)
  have rc := rel_kr hq (P₁ := fun t => KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2 t ∧ t.syms = s₀.syms)
    (P₂ := fun t => KVH P s₀' (kv0 P s₀').1 (kv0 P s₀').2 t ∧ t.syms = s₀'.syms)
    (rs := []) (by decide) (fun _ h => h.1.kr) (fun _ h => h.1.kr) hc.cnt
    (fun s h => initCnt_ok h.1 h.2) (fun s h => initCnt_ok h.1 h.2)
  have rl := loop_rel hp hp' hq hc
  obtain ⟨_, hf⟩ := hc.fin
  have re : RelCT isa (fun t t' => (∃ i, Exit P s₀ i t) ∧ ∃ i, Exit P s₀' i t') (.block (P.c.wipe ++ Cfg.restore))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.s1]) (fun t t' ⟨⟨i, x⟩, ⟨i', x'⟩⟩ => ⟨by rw [x.kr.sp, x'.kr.sp, hq.sp],
      fun r hr => by
        rw [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr
        rw [x.kr.s1, x'.kr.s1, hq.sp]⟩) hf
  exact rp.seq (rr.seq (rk.seq (RelCT.assoc (rd.seq (rc.seq (rl.seq re))))))

end

/-! ## The frame, and `Verified` -/

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
the taint checks of its pieces. -/
theorem ct (hc : Checks P.c) :
    ConstantTime isa (rfcRC P.kit.K P.I P.N).pre (rfcRC P.kit.K P.I P.N).pub P.c.sign := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc h; have hp' := pre_alloc h'
  obtain ⟨⟨qsp, q0, q1, q2, q3, qlk⟩, qsy⟩ := hpub
  have hq : PubEq P (allocd P.c.frB e) (allocd P.c.frB e') := ⟨q0, q1, q2, q3, by simp only [allocd, qsp], qlk, qsy⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q P.c.sign fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold Cfg.sign
  refine rel_alloc ((main_rel hp hp' hq hc).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

/-- `rfcRC` with tables implies the shared contract with them
(`abi.withConsts`), from `rfcR`'s implying it without, given a state
satisfying it. -/
theorem rfcRC_implies {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {I : Spec.Ecdsa.Rfc6979.Instance} {N : Nat}
    (h : (rfcR I N).Implies (I.signContract RISCV64.abi N))
    (hs : ∃ s, (I.signContract (RISCV64.abi.withConsts (c₀ :: cs)) N).pre s) :
    (rfcRC (c₀ :: cs) I N).Implies (I.signContract (RISCV64.abi.withConsts (c₀ :: cs)) N) :=
  { pre := fun _ hp => ⟨h.pre _ (pre_consts.mp hp).1, (pre_consts.mp hp).2⟩
    post := fun s s' hp hq => post_consts.mpr (h.post (stripConsts _ s) s' (pre_consts.mp hp).1 hq)
    pub := fun s₁ s₂ h₁ h₂ hq => ⟨h.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hq).1, (pub_consts.mp hq).2⟩
    sat := hs }

theorem stripConsts_nil (s : State) : stripConsts [] s = s := by
  cases s; simp [stripConsts, State.withRegions]

theorem constsOk_nil (st : Nat) (s : State) : ConstsOk [] st s :=
  ⟨by simp [constRegs, Abi.constRegions], fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- `rfcRC` without tables implies what `rfcR` does. -/
theorem rfcR0_implies {I : Spec.Ecdsa.Rfc6979.Instance} {N : Nat} {C : Contract isa}
    (h : (rfcR I N).Implies C) : (rfcRC [] I N).Implies C :=
  { pre := fun s hp => ⟨by rw [stripConsts_nil]; exact h.pre s hp, constsOk_nil _ _⟩
    post := fun s s' hp hq => h.post s s' hp hq
    pub := fun s₁ s₂ h₁ h₂ hq => ⟨h.pub s₁ s₂ h₁ h₂ hq, fun _ h => absurd h List.not_mem_nil⟩
    sat := h.sat }

/-- `Verified`, for an instance whose shared contract `C` implies `rfcRC`. -/
theorem sign_verified (hc : Checks P.c) {N : Nat} (hN : P.N = N) {C : Contract isa}
    (himp : (rfcRC P.kit.K P.I N).Implies C) : Verified RISCV64.target P.c.sign C := by
  subst hN
  exact Verified.of_correct (fun s h => by
    obtain ⟨t, s', he, h₁, h₂⟩ := correct h
    exact ⟨t, s', he, h₁, h₂⟩) (ct hc) himp

end VG.Proof.Ecdsa.Rfc6979.RISCV64
