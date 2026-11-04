module

-- separate module: it needs only `Hmac`, so it builds in parallel with the proof of correctness

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Hmac
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on RISC-V: two runs of an HMAC through the table

Two runs from states whose public data agree (`PubEq`: the pointers, the
table, the stack pointer, the addresses of the hash function's streaming
functions and the number of candidates RFC 6979 tries, which the contract
lets leak) are related piece by piece. A block of `addi` and `li` accesses
no memory and leaks nothing (`rel_noaddr`); the padded key's blocks and the
load of a table's word are checked by the taint analysis (`Ck`), from the
registers that hold pointers; an indirect call of the table's function
reaches the same function at the same address in both runs (`tcall_rel`),
whose call is related by its contract and its constant time (`HashCT`,
`RelCT.callEx`) with the arguments each run's correctness gives. Each
piece keeps `KR` and the entry's addresses of statics in both runs (`KK`),
so that HMAC's do (`hmac_kk`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd wp_addi wp_li wp_ld)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initK updK finK)
open Spec.Sha256 (bytesAt)

/-- A piece of code the taint analysis accepts with the registers `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (P : Rfc) (s₀ s₀' : State) : Prop where
  a0 : s₀.gpr .a0 = s₀'.gpr .a0
  a1 : s₀.gpr .a1 = s₀'.gpr .a1
  a2 : s₀.gpr .a2 = s₀'.gpr .a2
  a4 : s₀.gpr .a4 = s₀'.gpr .a4
  a5 : s₀.gpr .a5 = s₀'.gpr .a5
  sp : s₀.sp = s₀'.sp
  fi : s₀.syms P.H.initN = s₀'.syms P.H.initN
  fu : s₀.syms P.H.updN = s₀'.syms P.H.updN
  ff : s₀.syms P.H.finN = s₀'.syms P.H.finN
  lk : (result P.I s₀.mem (dk s₀) (dg s₀)).2 = (result P.I s₀'.mem (dk s₀') (dg s₀')).2
  sy : ∀ cn ∈ P.kit.K, s₀.syms cn.1 = s₀'.syms cn.1

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
  cases r <;> simp only [regV, dk, scr, hq.sp, hq.a1, hq.a4]

/-- The pointer registers agree in two runs that keep `KR`. -/
theorem ag_kr {s s' : State} (h : KR P s₀ s) (h' : KR P s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s6], s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.s0, h'.s0, scr, scr, hq.a4]
  · rw [h.s1, h'.s1, hq.sp]
  · rw [h.s2, h'.s2, out, out, hq.a0]
  · rw [h.s3, h'.s3, dk, dk, hq.a1]
  · rw [h.s4, h'.s4, dg, dg, hq.a2]
  · rw [h.s6, h'.s6, tab, tab, hq.a5]

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
    {rs : List Reg} (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s6])
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

/-- A block of instructions that access no memory leaks nothing. -/
theorem execBlock_noaddr : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    (∀ i ∈ is, ∀ s, isa.addrs i s = []) → execBlock isa is s = some (s', t) → t = []
  | [], s, s', t, _, h => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | i :: is, s, s', t, ha, h => by
    simp only [execBlock] at h
    split at h
    · cases h
    · obtain ⟨⟨s₂, t₂⟩, h₂, e⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at e
      rw [← e.2, show addrs i s = [] from ha i (by simp) s, execBlock_noaddr (fun j hj => ha j (by simp [hj])) h₂]
      rfl

theorem rel_noaddr {Q : State → State → Prop} {is : List Instr} (ha : ∀ i ∈ is, ∀ s, isa.addrs i s = []) :
    RelCT isa Q (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  rw [execBlock_noaddr ha e₁, execBlock_noaddr ha e₂]; exact ⟨rfl, trivial⟩

/-- Two runs of a block of `addi` and `li`, each described by `WP`. -/
theorem rel_args {P₁ P₂ G₁ G₂ : State → Prop} {is : List Instr} (ha : ∀ i ∈ is, ∀ s, isa.addrs i s = [])
    (hw : ∀ s, P₁ s → WP isa (.block is) s G₁) (hw' : ∀ s, P₂ s → WP isa (.block is) s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') (.block is) fun s s' => G₁ s ∧ G₂ s' :=
  rel_wp (rel_noaddr ha) hw hw'

/-! ## The table's calls, in two runs -/

/-- `KR`, with the entry's addresses of statics. -/
abbrev KS (P : Rfc) (s₀ t : State) : Prop := KR P s₀ t ∧ t.syms = s₀.syms

/-- Two runs that keep `KS`. -/
abbrev KK (P : Rfc) (s₀ s₀' : State) (t t' : State) : Prop := KS P s₀ t ∧ KS P s₀' t'

/-- The load of the table's word `k`, in one run. -/
theorem tword_ok {σ : State} (hσ : Pre P σ) {t : State} (hk : KR P σ t) {k : Nat} (hk3 : k < 3) {n : String}
    (hw : σ.mem.readW (tab σ + BitVec.ofNat 64 (8 * k)) 64 = σ.syms n) :
    WP isa (.block (tword k)) t fun u => Upd t u .t1 (σ.syms n) ∧ u.syms = t.syms := by
  unfold tword
  have hin : InRegions (t.rd ++ t.wr) (tab σ + BitVec.ofNat 64 (8 * k)) 8 :=
    ⟨tabR σ, List.mem_append_left _ (by rw [hk.rd, hσ.rd]; simp),
      Offset.contains_base _ (by omega) (by have := hσ.bn; omega)⟩
  refine WP.of_syms (wp_ld (a := tab σ + BitVec.ofNat 64 (8 * k)) (by omega)
    (by rw [hk.s6]) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := hσ.ba; have := hσ.bn; omega) hin fun u up => WP.block_nil fun sy => ⟨?_, sy⟩)
  rwa [tabWord hσ hk (by omega), hw] at up

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀')
include hp hp' hq

/-- An indirect call of the table's function `k`, in two runs from states
`R₁` and `R₂`, which reaches `n` in both, given its call's two runs. -/
theorem tcall_rel {k : Nat} (hk3 : k < 3) {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    {R₁ R₂ : State → Prop} (hr₁ : ∀ t, R₁ t → KS P s₀ t) (hr₂ : ∀ t, R₂ t → KS P s₀' t)
    (hf₁ : ts.find? (fun q => s₀.syms q.1 == s₀.syms n) = some (n, c))
    (hf₂ : ts.find? (fun q => s₀'.syms q.1 == s₀'.syms n) = some (n, c))
    (hw₁ : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * k)) 64 = s₀.syms n)
    (hw₂ : s₀'.mem.readW (tab s₀' + BitVec.ofNat 64 (8 * k)) 64 = s₀'.syms n)
    (he : s₀.syms n = s₀'.syms n) (ck : Ck [.s6] (.block (tword k)))
    (hcall : RelCT isa (fun u u' => (∃ t, R₁ t ∧ Upd t u .t1 (s₀.syms n)) ∧
      (∃ t', R₂ t' ∧ Upd t' u' .t1 (s₀'.syms n))) (.call n c) fun _ _ => True) :
    RelCT isa (fun t t' => R₁ t ∧ R₂ t') (tcall k ts) fun _ _ => True := by
  unfold tcall
  have r₁ := rel_agree (P₁ := R₁) (P₂ := R₂) (rs := [.s6])
    (G₁ := fun u => (∃ t, R₁ t ∧ Upd t u .t1 (s₀.syms n)) ∧ u.syms = s₀.syms)
    (G₂ := fun u => (∃ t, R₂ t ∧ Upd t u .t1 (s₀'.syms n)) ∧ u.syms = s₀'.syms)
    (fun s s' h h' => by
      obtain ⟨e, g⟩ := ag_kr hq (hr₁ s h).1 (hr₂ s' h').1
      exact ⟨e, fun r hr => g r (by simp only [List.mem_singleton] at hr; subst hr; simp)⟩) ck
    (fun s h => WP.mono (tword_ok hp (hr₁ s h).1 hk3 hw₁) fun u ⟨up, sy⟩ =>
      ⟨⟨s, h, up⟩, sy.trans (hr₁ s h).2⟩)
    (fun s h => WP.mono (tword_ok hp' (hr₂ s h).1 hk3 hw₂) fun u ⟨up, sy⟩ =>
      ⟨⟨s, h, up⟩, sy.trans (hr₂ s h).2⟩)
  refine r₁.seq ?_
  cases ts with
  | nil => simp at hf₁
  | cons q ts =>
    refine RelCT.icalls_of_call (hcall.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) ?_
    rintro u u' ⟨⟨⟨t, _, up⟩, sy⟩, ⟨⟨t', _, up'⟩, sy'⟩⟩
    refine ⟨s₀.syms n, by show some (u.gpr .t1) = _; rw [up.gpr],
      by show some (u'.gpr .t1) = _; rw [up'.gpr, he], ?_, ?_, rfl⟩
    · show (q :: ts).find? (fun p => u.syms p.1 == s₀.syms n) = _
      rw [sy]; exact hf₁
    · show (q :: ts).find? (fun p => u'.syms p.1 == s₀.syms n) = _
      rw [sy', he]; exact hf₂

end

/-! ## The streaming calls' arguments, at the call -/

section
variable {σ : State} (hσ : Pre P σ)
include hσ

/-- `init`'s precondition and regions, from `u`, in `KR`, with the state at
`scratch + o` in `a0`. -/
theorem initK_pre {u : State} (hk : KR P σ u) {o : Nat} (ho : o + P.H.S ≤ 384) (g0 : u.gpr .a0 = cA σ o) :
    (initK P.H.S P.hH.SH.Repr).pre (u.callEntry.withRegions [] [cR σ o P.H.S]) ∧
      Covers ([] ++ [cR σ o P.H.S]) (u.rd ++ u.wr) ∧ Covers [cR σ o P.H.S] u.wr := by
  have c0 : u.callEntry.gpr .a0 = cA σ o := (State.callEntry_gpr _ (by decide)).trans g0
  refine ⟨?_, VG.Covers.of_sub fun r hr => ?_, VG.Covers.of_sub fun r hr => ?_⟩
  · simp only [initK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0]
    exact ⟨trivial, trivial⟩
  · simp only [List.nil_append, List.mem_singleton] at hr; subst hr
    exact cov_scr hσ hk (by have := (sizes P).S192; omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact covW_scr hσ hk (by have := (sizes P).S192; omega)

/-- `update`'s, with the state at `scratch + o` in `a0` and the data's `len`
bytes at `off(base)` in `a2` and `a3`. -/
theorem updK_pre {u : State} (hk : KR P σ u) {o : Nat} (ho : o + P.H.S ≤ 384) {base : Reg} {off len : Nat}
    (hd : DatOk P base off len) (g0 : u.gpr .a0 = cA σ o) (g2 : u.gpr .a2 = pA σ (base, off, len))
    (g3 : (u.gpr .a3).toNat = len) :
    (updK P.H.S P.H.F P.hH.SH.Repr).pre (u.callEntry.withRegions [⟨pA σ (base, off, len), len⟩] [cR σ o P.H.S]) ∧
      Covers ([⟨pA σ (base, off, len), len⟩] ++ [cR σ o P.H.S]) (u.rd ++ u.wr) ∧ Covers [cR σ o P.H.S] u.wr := by
  have hX := (sizes P).X
  have hS := (sizes P).S192
  have c0 : u.callEntry.gpr .a0 = cA σ o := (State.callEntry_gpr _ (by decide)).trans g0
  have c2 : u.callEntry.gpr .a2 = pA σ (base, off, len) := (State.callEntry_gpr _ (by decide)).trans g2
  have c3 : (u.callEntry.gpr .a3).toNat = len := by rw [State.callEntry_gpr _ (by decide), g3]
  refine ⟨?_, VG.Covers.of_sub fun r hr => ?_, VG.Covers.of_sub fun r hr => ?_⟩
  · simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c2, c3]
    exact ⟨trivial, trivial, hd.st hσ ho, by rw [hk.sp]; exact hσ.al, by rw [hk.sp]; have := hσ.spX; omega,
      below_st hσ hk hX.1 (st_sub (by omega)), hd.below hσ hk hX.1⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.cov hσ hk
    · exact cov_scr hσ hk (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact covW_scr hσ hk (by omega)

/-- `finalize`'s, with the state at `scratch + o` in `a0` and the digest to
`off(base)` in `a2`. -/
theorem finK_pre {u : State} (hk : KR P σ u) {o : Nat} (ho : o + P.H.S ≤ 384) {base : Reg} {off : Nat}
    (hd : OutOk P base off) (g0 : u.gpr .a0 = cA σ o) (g2 : u.gpr .a2 = pA σ (base, off, P.c.D)) :
    (finK P.H.S P.H.F P.H.D P.hH.SH.Repr P.hH.SH.H.hash).pre
        (u.callEntry.withRegions [] [cR σ o P.H.S, ⟨pA σ (base, off, P.c.D), P.H.D⟩]) ∧
      Covers ([] ++ [cR σ o P.H.S, ⟨pA σ (base, off, P.c.D), P.H.D⟩]) (u.rd ++ u.wr) ∧
      Covers [cR σ o P.H.S, ⟨pA σ (base, off, P.c.D), P.H.D⟩] u.wr := by
  have hz := sizes P
  have hX := hz.X
  have hS := hz.S192
  have hzH := hz.H
  have hzQ := hz.Q
  obtain ⟨hD1, hD2⟩ := hz.D
  have hDH : P.H.D = P.c.D := hz.DB.1
  rw [hDH]
  have hW : Region.Sub ⟨pA σ (base, off, P.c.D), P.c.D⟩ (stR σ) ∨
      ((∃ o' n, (⟨pA σ (base, off, P.c.D), P.c.D⟩ : Region) = sR σ o' n ∧ 64 ≤ o' ∧ o' + n ≤ P.c.frB)) := by
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, h₁, h₂⟩
    · exact .inl (st_sub (o := sTmp) (n := P.c.D) (by simp only [sTmp]; omega))
    · exact .inr ⟨off, P.c.D, rfl, h₁, h₂⟩
  have hcovO : ∃ r' ∈ u.wr, ∃ o', pA σ (base, off, P.c.D) = r'.base + BitVec.ofNat 64 o' ∧ o' + P.c.D ≤ r'.len := by
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, h₁, h₂⟩
    · exact covW_scr hσ hk (o := sTmp) (n := P.c.D) (by simp only [sTmp]; omega)
    · exact covW_fr hσ hk h₂
  have hdO : Region.Disjoint (cR σ o P.H.S) ⟨pA σ (base, off, P.c.D), P.c.D⟩ := by
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, h₁, h₂⟩
    · exact scr_disj hσ (.inl (by simp only [sTmp]; omega)) (by omega) (by simp only [sTmp]; omega)
    · exact (fr_st hσ h₂ (st_sub (by omega))).symm
  have hbS : (below u.sp P.H.F).Disjoint ⟨pA σ (base, off, P.c.D), P.c.D⟩ := by
    rcases hW with h' | ⟨o', n, e, h₁, h₂⟩
    · exact below_st hσ hk hX.1 h'
    · rw [e]; exact below_fr hσ hk hX.1 h₂
  have c0 : u.callEntry.gpr .a0 = cA σ o := (State.callEntry_gpr _ (by decide)).trans g0
  have c2 : u.callEntry.gpr .a2 = pA σ (base, off, P.c.D) := (State.callEntry_gpr _ (by decide)).trans g2
  refine ⟨?_, VG.Covers.of_sub fun r hr => ?_, VG.Covers.of_sub fun r hr => ?_⟩
  · simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c2]
    exact ⟨trivial, trivial, hdO, by rw [hk.sp]; exact hσ.al, by rw [hk.sp]; have := hσ.spX; omega,
      below_st hσ hk hX.1 (st_sub (by omega)), hbS⟩
  · simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_scr hσ hk (by omega)
    · obtain ⟨r', hr', o', h₁, h₂⟩ := hcovO
      exact ⟨r', List.mem_append_right _ hr', o', by rw [h₁], h₂⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact covW_scr hσ hk (by omega)
    · exact hcovO

end

/-! ## The streaming calls, in two runs -/

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀')
include hp hp' hq

/-- `init`'s arguments set. -/
abbrev IA (P : Rfc) (s₀ : State) (o : Nat) (t : State) : Prop := KS P s₀ t ∧ t.gpr .a0 = cA s₀ o

/-- `update`'s. -/
abbrev UA (P : Rfc) (s₀ : State) (o cnt : Nat) (base : Reg) (off len : Nat) (t : State) : Prop :=
  KS P s₀ t ∧ t.gpr .a0 = cA s₀ o ∧ t.gpr .a1 = BitVec.ofNat 64 cnt ∧ t.gpr .a2 = pA s₀ (base, off, len) ∧
    (t.gpr .a3).toNat = len

/-- `finalize`'s. -/
abbrev FA (P : Rfc) (s₀ : State) (o cnt : Nat) (base : Reg) (off : Nat) (t : State) : Prop :=
  KS P s₀ t ∧ t.gpr .a0 = cA s₀ o ∧ t.gpr .a1 = BitVec.ofNat 64 cnt ∧ t.gpr .a2 = pA s₀ (base, off, P.c.D)

theorem initT_rel {o : Nat} (ho : o + P.H.S ≤ 384) (ck : Ck [.s6] (.block (tword 0))) :
    RelCT isa (fun t t' => IA P s₀ o t ∧ IA P s₀' o t') (tcall 0 P.c.f.init) fun _ _ => True := by
  refine tcall_rel hp hp' hq (by decide) (fun _ h => h.1) (fun _ h => h.1) hp.bo.i hp'.bo.i
    (by rw [Nat.mul_zero, BitVec.add_zero]; exact hp.bm.1) (by rw [Nat.mul_zero, BitVec.add_zero]; exact hp'.bm.1)
    hq.fi ck ?_
  refine RelCT.callEx P.hH.init P.w.l.ct.init fun u u' ⟨⟨t, ⟨⟨k, _⟩, g0⟩, up⟩, ⟨t', ⟨⟨k', _⟩, g0'⟩, up'⟩⟩ => ?_
  have k₁ := k.upd (by decide) up
  have k₁' := k'.upd (by decide) up'
  obtain ⟨p₁, c₁, w₁⟩ := initK_pre hp k₁ ho (by rw [up.other _ (by decide), g0])
  obtain ⟨p₂, c₂, w₂⟩ := initK_pre hp' k₁' ho (by rw [up'.other _ (by decide), g0'])
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂⟩
  simp only [initK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide)]
  exact ⟨by rw [up.other _ (by decide), up'.other _ (by decide), g0, g0', hq.cA],
    by rw [k₁.sp, k₁'.sp, hq.sp]⟩

theorem updT_rel {o cnt : Nat} (ho : o + P.H.S ≤ 384) {base : Reg} {off len : Nat} (hd : DatOk P base off len)
    (ck : Ck [.s6] (.block (tword 1))) :
    RelCT isa (fun t t' => UA P s₀ o cnt base off len t ∧ UA P s₀' o cnt base off len t') (tcall 1 P.c.f.upd)
      fun _ _ => True := by
  refine tcall_rel hp hp' hq (by decide) (fun _ h => h.1) (fun _ h => h.1) hp.bo.u hp'.bo.u hp.bm.2.1 hp'.bm.2.1
    hq.fu ck ?_
  refine RelCT.callEx P.hH.upd P.w.l.ct.upd
    fun u u' ⟨⟨t, ⟨⟨k, _⟩, g0, g1, g2, g3⟩, up⟩, ⟨t', ⟨⟨k', _⟩, g0', g1', g2', g3'⟩, up'⟩⟩ => ?_
  have k₁ := k.upd (by decide) up
  have k₁' := k'.upd (by decide) up'
  obtain ⟨p₁, c₁, w₁⟩ := updK_pre hp k₁ ho hd (by rw [up.other _ (by decide), g0])
    (by rw [up.other _ (by decide), g2]) (by rw [up.other _ (by decide), g3])
  obtain ⟨p₂, c₂, w₂⟩ := updK_pre hp' k₁' ho hd (by rw [up'.other _ (by decide), g0'])
    (by rw [up'.other _ (by decide), g2']) (by rw [up'.other _ (by decide), g3'])
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂⟩
  simp only [updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide),
    up.other _ (show Reg.a0 ≠ .t1 by decide), up'.other _ (show Reg.a0 ≠ .t1 by decide),
    up.other _ (show Reg.a1 ≠ .t1 by decide), up'.other _ (show Reg.a1 ≠ .t1 by decide),
    up.other _ (show Reg.a2 ≠ .t1 by decide), up'.other _ (show Reg.a2 ≠ .t1 by decide),
    up.other _ (show Reg.a3 ≠ .t1 by decide), up'.other _ (show Reg.a3 ≠ .t1 by decide)]
  exact ⟨by rw [g0, g0', hq.cA], by rw [g1, g1'], by rw [g2, g2', hq.pA],
    BitVec.eq_of_toNat_eq (g3.trans g3'.symm), by rw [k₁.sp, k₁'.sp, hq.sp]⟩

theorem finT_rel {o cnt : Nat} (ho : o + P.H.S ≤ 384) {base : Reg} {off : Nat} (hd : OutOk P base off)
    (ck : Ck [.s6] (.block (tword 2))) :
    RelCT isa (fun t t' => FA P s₀ o cnt base off t ∧ FA P s₀' o cnt base off t') (tcall 2 P.c.f.fin)
      fun _ _ => True := by
  refine tcall_rel hp hp' hq (by decide) (fun _ h => h.1) (fun _ h => h.1) hp.bo.f hp'.bo.f hp.bm.2.2 hp'.bm.2.2
    hq.ff ck ?_
  refine RelCT.callEx P.hH.fin P.w.l.ct.fin
    fun u u' ⟨⟨t, ⟨⟨k, _⟩, g0, g1, g2⟩, up⟩, ⟨t', ⟨⟨k', _⟩, g0', g1', g2'⟩, up'⟩⟩ => ?_
  have k₁ := k.upd (by decide) up
  have k₁' := k'.upd (by decide) up'
  obtain ⟨p₁, c₁, w₁⟩ := finK_pre hp k₁ ho hd (by rw [up.other _ (by decide), g0]) (by rw [up.other _ (by decide), g2])
  obtain ⟨p₂, c₂, w₂⟩ := finK_pre hp' k₁' ho hd (by rw [up'.other _ (by decide), g0'])
    (by rw [up'.other _ (by decide), g2'])
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂⟩
  simp only [finK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide),
    up.other _ (show Reg.a0 ≠ .t1 by decide), up'.other _ (show Reg.a0 ≠ .t1 by decide),
    up.other _ (show Reg.a1 ≠ .t1 by decide), up'.other _ (show Reg.a1 ≠ .t1 by decide),
    up.other _ (show Reg.a2 ≠ .t1 by decide), up'.other _ (show Reg.a2 ≠ .t1 by decide)]
  exact ⟨by rw [g0, g0', hq.cA], by rw [g1, g1'], by rw [g2, g2', hq.pA], by rw [k₁.sp, k₁'.sp, hq.sp]⟩

end

end VG.Proof.Ecdsa.Rfc6979.RISCV64
