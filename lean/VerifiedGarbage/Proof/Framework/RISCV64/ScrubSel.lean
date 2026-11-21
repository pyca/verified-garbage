module

public import VerifiedGarbage.Proof.Framework.RISCV64.ResidueTaintSound
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Clearing only the stack the residue analysis finds secret (64-bit RISC-V)

`Impl.Scrub.RISCV64.scrubSel rb fs c` is `c`, then the clearing of `scrubAll` with frames that
zero only the doublewords of their runs (`fs`). Its run after `c` leaves the registers as
`scrubAll`'s does and the memory as it was but within the frames (`tailSel_run`), so it is
verified against `c`'s contract (`Verified.scrubSel`), with `scrubAll`'s proof. It returns
without secret residue when the residue analysis (`rtaint`) of the whole of it, from where
the contract starts it, ends in `RTaint.done` (`RTaint.noResidue_of_verified`): that analysis
sees the clearing's stores, and that they leave no byte of the window secret.

`verifiedScrubbedSel` (`ScrubProved.lean`) states it of a registration's code, as
`verifiedScrubbedAll` does of `scrubAll`.
-/

@[expose] public section

namespace VG.RISCV64.Scrub

open VG.Impl.Scrub.RISCV64

/-! ## The clearing's run -/

/-- The trace of `storesRuns rs` from `t1 = q`. -/
def runsTr (q : Addr) : List (Nat × Nat) → List Leak
  | [] => []
  | (k, n) :: rs => storesTr q k n ++ runsTr q rs

/-- The memory `storesRuns rs` leaves from `t1 = q`. -/
def zeroRuns (q : Addr) : List (Nat × Nat) → Mem → Mem
  | [], m => m
  | (k, n) :: rs, m => zeroRuns q rs (zeroOn q (8 * k) (8 * (k + n)) m)

theorem storesRuns_run (q : Addr) (b : Nat) (hq : q.toNat % 8 = 0) (hb : b ≤ 2048)
    (hqb : q.toNat + b ≤ 2 ^ 64) :
    ∀ (rs : List (Nat × Nat)) (u : State), (∀ p ∈ rs, 8 * (p.1 + p.2) ≤ b) → u.gpr .t0 = 0 →
      u.gpr .t1 = q → ⟨q, b⟩ ∈ u.wr →
      execBlock isa (storesRuns rs) u = some ({ u with mem := zeroRuns q rs u.mem }, runsTr q rs)
  | [], u, _, _, _, _ => by
    simp only [storesRuns, execBlock, zeroRuns, runsTr]
  | (k, n) :: rs, u, h, h0, h1, hw => by
    simp only [storesRuns]
    rw [execBlock_append, stores_run q b hq hb hqb n k u (h _ List.mem_cons_self) h0 h1 hw,
      Option.bind_some,
      storesRuns_run q b hq hb hqb rs { u with mem := zeroOn q (8 * k) (8 * (k + n)) u.mem }
        (fun p hp => h p (List.mem_cons_of_mem _ hp)) h0 h1 hw]
    rfl

theorem zeroRuns_out (q : Addr) {b : Nat} : ∀ (rs : List (Nat × Nat)) (m : Mem) (x : Addr),
    (∀ p ∈ rs, 8 * (p.1 + p.2) ≤ b) → ¬ (x - q).toNat < b → zeroRuns q rs m x = m x
  | [], _, _, _, _ => rfl
  | (k, n) :: rs, m, x, h, hx => by
    simp only [zeroRuns]
    rw [zeroRuns_out q rs _ x (fun p hp => h p (List.mem_cons_of_mem _ hp)) hx]
    have := h _ List.mem_cons_self
    simp only [zeroOn]
    split
    · next hc => exfalso; simp only at this; omega_using [hc, hx, this]
    · rfl

/-- The trace of `wipeSel fs` from `sp = p`. -/
def wipeSelTr : List (Nat × List (Nat × Nat)) → Addr → List Leak
  | [], _ => []
  | (b, rs) :: bs, p => runsTr (p - BitVec.ofNat 64 b) rs ++ wipeSelTr bs (p - BitVec.ofNat 64 b)

/-- The frames of `fs`: each of a size `alloc` takes, and its runs within it. -/
def FramesOk (fs : List (Nat × List (Nat × Nat))) : Prop :=
  ∀ f ∈ fs, 0 < f.1 ∧ f.1 ≤ 2048 ∧ f.1 % 16 = 0 ∧ ∀ p ∈ f.2, 8 * (p.1 + p.2) ≤ f.1

/-- The bytes of the frames of `fs`. -/
def sizeOf (fs : List (Nat × List (Nat × Nat))) : Nat := (fs.map (·.1)).sum

/-- `wipeSel fs` leaves the memory as it was outside its frames' `sizeOf fs` bytes below
`sp`, and changes no register but `t1`. -/
theorem wipeSel_run : ∀ (fs : List (Nat × List (Nat × Nat))) (u : State), FramesOk fs →
    sizeOf fs ≤ u.sp.toNat → u.sp.toNat % 16 = 0 → u.gpr .t0 = 0 →
    ∃ g m U, (∀ r, r ≠ .t1 → g r = u.gpr r) ∧
      (∀ x, ¬ (x - (u.sp - BitVec.ofNat 64 (sizeOf fs))).toNat < sizeOf fs → m x = u.mem x) ∧
      Exec isa (wipeSel fs) u (wipeSelTr fs u.sp) { u with gpr := g, mem := m, unknowns := U }
  | [], u, _, _, _, _ => by
    refine ⟨u.gpr, u.mem, u.unknowns, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    simp only [wipeSel, wipeSelTr]
    exact .block rfl
  | (b, rs) :: bs, u, hv, hs, h16, h0 => by
    obtain ⟨hb0, hb, hb16, hrs⟩ := hv _ List.mem_cons_self
    have hbs : FramesOk bs := fun f h => hv f (List.mem_cons_of_mem _ h)
    simp only [sizeOf, List.map_cons, List.sum_cons] at hs
    have hS : sizeOf bs = (bs.map (·.1)).sum := rfl
    have hp := u.sp.isLt
    have hq : (u.sp - BitVec.ofNat 64 b).toNat = u.sp.toNat - b := toNat_sub_ofNat _ _ (by omega_using [hs])
    have hpush : isa.push (.alloc b) u =
        some { u with sp := u.sp - BitVec.ofNat 64 b, wr := ⟨u.sp - BitVec.ofNat 64 b, b⟩ :: u.wr } := by
      have h1 : b ≤ 4064 := by omega_using [hb]
      have h2 : b ≤ u.sp.toNat := by omega_using [hs]
      simp only [isa, push, hb0, h1, hb16, h2, and_self, ite_true]
    generalize hs₁ : ({ u with sp := u.sp - BitVec.ofNat 64 b, wr := ⟨u.sp - BitVec.ofNat 64 b, b⟩ :: u.wr } :
      State) = s₁ at hpush
    have hs₁sp : s₁.sp = u.sp - BitVec.ofNat 64 b := by rw [← hs₁]
    have hs₁wr : s₁.wr = ⟨u.sp - BitVec.ofNat 64 b, b⟩ :: u.wr := by rw [← hs₁]
    have hs₁g : s₁.gpr = u.gpr := by rw [← hs₁]
    have hs₁m : s₁.mem = u.mem := by rw [← hs₁]
    have hst := storesRuns_run (u.sp - BitVec.ofNat 64 b) b (by omega_using [hq, h16, hb16, hs]) hb
      (by omega_using [hq, hs, hp]) rs (s₁.write .t1 (s₁.sp + BitVec.ofNat 64 0)) hrs
      (by rw [RegUpd.gpr_write_of_ne _ _ (by decide), hs₁g, h0])
      (by rw [RegUpd.gpr_write_self, hs₁sp]; simp)
      (by rw [RegUpd.wr_write, hs₁wr]; exact List.mem_cons_self)
    have hblk : execBlock isa (.addSp .t1 0 :: storesRuns rs) s₁ =
        some ({ s₁.write .t1 (s₁.sp + BitVec.ofNat 64 0) with
          mem := zeroRuns (u.sp - BitVec.ofNat 64 b) rs s₁.mem },
          runsTr (u.sp - BitVec.ofNat 64 b) rs) := by
      simp only [execBlock, isa, exec_addSp (show 0 < 2048 by decide), hst, Option.map_some, addrs,
        List.map_nil, List.nil_append, RegUpd.mem_write]
    generalize hs₂ : ({ s₁.write .t1 (s₁.sp + BitVec.ofNat 64 0) with
      mem := zeroRuns (u.sp - BitVec.ofNat 64 b) rs s₁.mem } : State) = s₂ at hblk
    have hs₂sp : s₂.sp = u.sp - BitVec.ofNat 64 b := by rw [← hs₂]; exact hs₁sp
    have hs₂g0 : s₂.gpr .t0 = 0 := by rw [← hs₂]; simp [State.write, hs₁g, h0]
    have hs₂m : s₂.mem = zeroRuns (u.sp - BitVec.ofNat 64 b) rs u.mem := by rw [← hs₂, hs₁m]
    obtain ⟨g, m, U, hg, hm, he⟩ := wipeSel_run bs s₂ hbs (by rw [hs₂sp, hq]; omega_using [hs, hS])
      (by rw [hs₂sp, hq]; omega_using [h16, hb16, hs]) hs₂g0
    generalize hs₃ : ({ s₂ with gpr := g, mem := m, unknowns := U } : State) = s₃ at he
    have hpop : isa.pop (.free b) s₁ s₃ = some { s₃ with
        sp := s₃.sp + BitVec.ofNat 64 b, wr := s₃.wr.tail,
        mem := lose s₃.mem s₃.sp b s₃.unknowns, unknowns := fun n => s₃.unknowns (n + b / 4) } := by
      have h1 : b ≤ 4064 := by omega_using [hb]
      have hw : s₃.wr = s₁.wr := by rw [← hs₃, ← hs₂]; rfl
      have hsp : s₃.sp = s₁.sp := by rw [← hs₃]; exact hs₂sp.trans hs₁sp.symm
      simp only [isa, pop, hb0, h1, hb16, hsp, hw, hs₁wr, hs₁sp, List.head?_cons, and_self, ite_true]
    have ef := Exec.frame (M := isa) (i := Instr.alloc b) (j := Instr.free b) hpush (.seq (.block hblk) he) hpop
    have hs₃sp : s₃.sp = u.sp - BitVec.ofNat 64 b := by rw [← hs₃]; exact hs₂sp
    refine ⟨g, lose m (u.sp - BitVec.ofNat 64 b) b U, fun n => U (n + b / 4), fun r hr => ?_, fun x hx => ?_, ?_⟩
    · rw [hg r hr, ← hs₂]
      exact (RegUpd.gpr_write_of_ne _ _ hr).trans (by rw [hs₁g])
    · have hx' : ¬ (x - (u.sp - BitVec.ofNat 64 (b + sizeOf bs))).toNat < b + sizeOf bs := hx
      have e1 : u.sp - BitVec.ofNat 64 b - BitVec.ofNat 64 (sizeOf bs) =
          u.sp - BitVec.ofNat 64 (b + sizeOf bs) := by
        rw [BitVec.ofNat_add]; bv_omega
      have e2 : u.sp - BitVec.ofNat 64 b = u.sp - BitVec.ofNat 64 (b + sizeOf bs) +
          BitVec.ofNat 64 (sizeOf bs) := by
        rw [BitVec.ofNat_add]; bv_omega
      have ho := off_lt x (u.sp - BitVec.ofNat 64 (b + sizeOf bs)) (sizeOf bs) b
        (by omega_using [hs, hp, hS])
      have hin : ¬ (x - (u.sp - BitVec.ofNat 64 b)).toNat < b := by
        rw [e2]; intro h; exact hx' (by have := ho.mp h; omega_using [this])
      have hout : ¬ (x - (s₂.sp - BitVec.ofNat 64 (sizeOf bs))).toNat < sizeOf bs := by
        rw [hs₂sp, e1]; exact fun h => hx' (by omega_using [h])
      simp only [lose, hin, ite_false]
      rw [hm x hout, hs₂m, zeroRuns_out _ rs u.mem x hrs hin]
    · have et : (List.map Leak.addr (isa.addrs (.alloc b) u) ++
          (runsTr (u.sp - BitVec.ofNat 64 b) rs ++ wipeSelTr bs s₂.sp) ++
          List.map Leak.addr (isa.addrs (.free b) s₃)) = wipeSelTr ((b, rs) :: bs) u.sp := by
        simp only [addrs, List.map_nil, List.nil_append, List.append_nil, wipeSelTr, hs₂sp]
      rw [et] at ef
      have es : ({ s₃ with
          sp := s₃.sp + BitVec.ofNat 64 b, wr := s₃.wr.tail,
          mem := lose s₃.mem s₃.sp b s₃.unknowns, unknowns := fun n => s₃.unknowns (n + b / 4) } : State) =
          { u with gpr := g, mem := lose m (u.sp - BitVec.ofNat 64 b) b U, unknowns := fun n => U (n + b / 4) } := by
        subst hs₃ hs₂ hs₁
        cases u
        simp only [State.write, List.tail_cons, BitVec.sub_add_cancel]
      rw [es] at ef
      exact ef

/-- The trace of `scrubTailSel rb fs` from `sp = p`: a function of `p`. -/
def tailSelTr (fs : List (Nat × List (Nat × Nat))) (p : Addr) : List Leak := [] ++ (wipeSelTr fs p ++ [])

/-- The clearing's run: it leaves the registers as `scrubAll`'s does (`finG`), and the memory
as it was outside its frames. -/
theorem tailSel_run {rb : Nat} (hrb : rb ≤ 64) {fs : List (Nat × List (Nat × Nat))} (hv : FramesOk fs)
    (u : State) (hs : sizeOf fs ≤ u.sp.toNat) (h16 : u.sp.toNat % 16 = 0) :
    ∃ m U, (∀ x, ¬ (x - (u.sp - BitVec.ofNat 64 (sizeOf fs))).toNat < sizeOf fs → m x = u.mem x) ∧
      Exec isa (scrubTailSel rb fs) u (tailSelTr fs u.sp)
        { u with gpr := finG rb u.gpr, mem := m, unknowns := U } := by
  have h₀ : execBlock isa [zeroR .t0] u =
      some ({ u with gpr := fun r => if r ∈ [Reg.t0] then 0 else u.gpr r }, []) := zeroRs_run [.t0] u
  generalize hu₁ : ({ u with gpr := fun r => if r ∈ [Reg.t0] then 0 else u.gpr r } : State) = u₁ at h₀
  have hsp : u₁.sp = u.sp := by rw [← hu₁]
  have hmem : u₁.mem = u.mem := by rw [← hu₁]
  have hg₁ : ∀ r, r ≠ .t0 → u₁.gpr r = u.gpr r := fun r hr => by rw [← hu₁]; simp [hr]
  obtain ⟨g, m, U, hg, hm, hw⟩ := wipeSel_run fs u₁ hv (hsp ▸ hs) (hsp ▸ h16) (by rw [← hu₁]; simp)
  have hc := execBlock_append (M := isa) (retFix rb) (scratchRegs.map zeroR)
    { u₁ with gpr := g, mem := m, unknowns := U }
  rw [retFix_run hrb, Option.bind_some, zeroRs_run] at hc
  have e := Exec.seq (.block h₀) (.seq hw (.block hc))
  have eg : (fun r => if r ∈ scratchRegs then 0 else
      (fun r => if r = Reg.a0 then fixA rb (g .a0) else g r) r) = finG rb u.gpr := by
    funext r
    simp only [finG]
    by_cases h : r ∈ scratchRegs
    · simp [h]
    · have h0 : r ≠ .t0 := fun e => h (e ▸ by decide)
      have h1 : r ≠ .t1 := fun e => h (e ▸ by decide)
      simp only [h, ite_false, hg r h1, hg₁ r h0, hg .a0 (by decide), hg₁ .a0 (by decide)]
  have et : ([] ++ (wipeSelTr fs u₁.sp ++ ([] ++ []))) = tailSelTr fs u.sp := by
    simp only [hsp, tailSelTr, List.nil_append]
  refine ⟨m, U, fun x hx => by rw [hm x (by rw [hsp]; exact hx), hmem], ?_⟩
  simp only at e
  rw [eg, et] at e
  subst hu₁
  exact e

/-! ## Verified -/

section

variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- A byte in the `S` bytes below `sp` is in the `stack` bytes below it, for `S ≤ stack`. -/
theorem below_le {sp x : Addr} {S stack : Nat} (hS : S ≤ stack) (hst : stack ≤ sp.toNat)
    (h : (x - (sp - BitVec.ofNat 64 S)).toNat < S) : (x - (sp - BitVec.ofNat 64 stack)).toNat < stack := by
  have hp := sp.isLt
  have e : x - (sp - BitVec.ofNat 64 stack) = (x - (sp - BitVec.ofNat 64 S)) + BitVec.ofNat 64 (stack - S) := by
    rw [← BitVec.ofNat_sub_ofNat_of_le (w := 64) stack S (by omega_using [hS, hst, hp]) hS]; bv_omega
  rw [e, toNat_add_of_lt _ _ (by omega_using [h, hS, hst, hp])]
  omega_using [h, hS]

/-- The window of `stack` bytes below the stack pointer is apart from every region. -/
theorem regions_out (hA : ScrubAbi A) {s : State} (h : (sig.contract A pre post wa stack leak).pre s) :
    ∀ g ∈ s.rd ++ s.wr, ∀ x, g.Contains x 1 → ¬ (x - (s.sp - BitVec.ofNat 64 stack)).toNat < stack := by
  intro g hg x hx hb
  by_cases h0 : stack = 0
  · subst h0; omega_using [hb]
  · exact (contract_pre_scrub hA h).2.2 g hg h0 x ((below_contains_iff _ _ _).mpr hb) hx

/-- `c` followed by `scrubSel`'s clearing is verified against `c`'s contract. -/
theorem Verified.scrubSel {c : Prog isa} {fs : List (Nat × List (Nat × Nat))}
    (hA : ScrubAbi A) (h : Verified target c (sig.contract A pre post wa stack leak))
    (hfs : FramesOk fs) (hsz : sizeOf fs ≤ stack) (hrb : sig.retBits A.ptrBits ≤ 64)
    (hpost : PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits)) :
    Verified target (Impl.Scrub.RISCV64.scrubSel (sig.retBits A.ptrBits) fs c)
      (sig.contract A pre post wa stack leak) := by
  obtain ⟨hcor, hct, hsat⟩ := h
  have run : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      abiPreserved s u ∧ (sig.contract A pre post wa stack leak).post s u ∧ u.sp = s.sp := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, hp⟩ := hcor s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    exact ⟨ha, hp, ha.2.1⟩
  have tail : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      ∃ m U, (∀ x, ¬ (x - (s.sp - BitVec.ofNat 64 (sizeOf fs))).toNat < sizeOf fs → m x = u.mem x) ∧
        Exec isa (scrubTailSel (sig.retBits A.ptrBits) fs) u (tailSelTr fs s.sp)
          { u with gpr := finG (sig.retBits A.ptrBits) u.gpr, mem := m, unknowns := U } := by
    intro s t u hs he
    obtain ⟨h16s, hsts, -⟩ := contract_pre_scrub hA hs
    obtain ⟨-, -, hsp⟩ := run s t u hs he
    obtain ⟨m, U, hm, e⟩ := tailSel_run hrb hfs u
      (by rw [hsp]; rcases hsts with h0 | h0 <;> omega_using [h0, hsz]) (by rw [hsp]; exact h16s)
    refine ⟨m, U, fun x hx => hm x (by rw [hsp]; exact hx), ?_⟩
    rw [← hsp]; exact e
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, u, he, -⟩ := hcor s hs
    obtain ⟨ha, hq, hsp⟩ := run s t u hs he
    obtain ⟨m, U, hm, et⟩ := tail s t u hs he
    refine ⟨_, _, .seq he et, ⟨fun r hr => ?_, hsp, ?_⟩, ?_⟩
    · obtain ⟨h1, h2⟩ := not_scratch_preserved r hr
      simp only [finG, h1, h2, ite_false]
      exact ha.1 r hr
    · show finG (sig.retBits A.ptrBits) u.gpr .ra = _
      simp only [finG, show Reg.ra ∉ scratchRegs by decide, ite_false, show Reg.ra ≠ .a0 by decide]
      exact ha.2.2
    · refine hpost s u _ hs hq (fun x ⟨g, hg, hx⟩ => hm x fun hb => ?_) ?_
      · obtain ⟨-, hsts, -⟩ := contract_pre_scrub hA hs
        have hS : sizeOf fs ≤ s.sp.toNat := by rcases hsts with h0 | h0 <;> omega_using [h0, hsz]
        by_cases h0 : stack = 0
        · subst h0; omega_using [hsz, hb]
        · exact regions_out hA hs g hg x hx (below_le hsz (by omega_using [hsts, h0, hS]) hb)
      · show (finG (sig.retBits A.ptrBits) u.gpr .a0).setWidth _ = _
        simp only [finG, show Reg.a0 ∉ scratchRegs by decide, ite_false, ite_true]
        exact fixA_low hrb _
  · cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨_, _, -, et₁⟩ := tail s₁ _ _ h₁ a₁
    obtain ⟨_, _, -, et₂⟩ := tail s₂ _ _ h₂ a₂
    obtain ⟨rfl, -⟩ := Exec.det b₁ et₁
    obtain ⟨rfl, -⟩ := Exec.det b₂ et₂
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, contract_pub_sp hA hp]

end

/-! ## A registration's code, scrubbed -/

/-- `FramesOk`, decided. -/
def framesOkB (fs : List (Nat × List (Nat × Nat))) : Bool :=
  fs.all fun f => decide (0 < f.1) && decide (f.1 ≤ 2048) && decide (f.1 % 16 = 0) &&
    f.2.all fun p => decide (8 * (p.1 + p.2) ≤ f.1)

theorem framesOk_of {fs : List (Nat × List (Nat × Nat))} (h : framesOkB fs = true) : FramesOk fs := by
  intro f hf
  simp only [framesOkB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h f hf
  exact ⟨h1, h2, h3, h4⟩

theorem scrubSelCode_verified {api : Api} (r : Unscrubbed api target) (fs : List (Nat × List (Nat × Nat)))
    (hfs : FramesOk fs) (hsz : sizeOf fs ≤ r.stack) (hrb : retBitsOf r ≤ 64)
    (hpost : PostOut r.contract (retBitsOf r)) :
    Verified target (scrubSel (retBitsOf r) fs r.code) r.contract := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  unfold retBitsOf at hrb hp ⊢
  rw [e] at hv hp ⊢
  have hrb' := hrb
  exact Verified.scrubSel (ScrubAbi.of r.consts api.sig r.tables) hv hfs hsz hrb' hp

/-- Where the residue analysis of `r`'s function starts holds of the states its contract
starts from, if the `e.2` bytes from what each register `e.1` of `bp0` holds are in its
regions. -/
theorem scrubSel_pre {api : Api} (r : Unscrubbed api target) (bp0 : List (Reg × Nat))
    (hbp : ∀ s, r.contract.pre s → ∀ e ∈ bp0, ∀ i < e.2, ∃ g ∈ s.rd ++ s.wr,
      g.Contains (s.gpr e.1 + BitVec.ofNat 64 i) 1) :
    ∀ s, r.contract.pre s → r.stack ≤ s.sp.toNat ∧
      (∀ g ∈ s.rd ++ s.wr, ∀ x, g.Contains x 1 → ¬ (x - (s.sp - BitVec.ofNat 64 r.stack)).toNat < r.stack) ∧
      ∀ e ∈ bp0, ∀ i < e.2, ¬ (s.gpr e.1 + BitVec.ofNat 64 i - (s.sp - BitVec.ofNat 64 r.stack)).toNat < r.stack := by
  intro s hs
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hs' := hs
  rw [e] at hs'
  have hA := ScrubAbi.of r.consts api.sig r.tables
  have hout := regions_out hA hs'
  obtain ⟨-, hsts, -⟩ := contract_pre_scrub hA hs'
  refine ⟨?_, hout, fun e he i hi => ?_⟩
  · rcases hsts with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    · exact h0
  obtain ⟨g, hg, hc⟩ := hbp s hs e he i hi
  exact hout g hg _ hc

/-- `r`'s code followed by the clearing of only the runs of `fs` returns without secret
residue if the residue analysis of the whole, stated of `code`, `W` and `rb`, which are
`r`'s code, stack and result width (so that the kernel evaluates it without the
registration, whose proofs mention the code), ends in `done`. -/
theorem scrubSel_noResidue {api : Api} (r : Unscrubbed api target) (fs : List (Nat × List (Nat × Nat)))
    (bp0 : List (Reg × Nat)) (hfs : FramesOk fs) (hsz : sizeOf fs ≤ r.stack) (hrb : retBitsOf r ≤ 64)
    (hpost : PostOut r.contract (retBitsOf r))
    (hbp : ∀ s, r.contract.pre s → ∀ e ∈ bp0, ∀ i < e.2, ∃ g ∈ s.rd ++ s.wr,
      g.Contains (s.gpr e.1 + BitVec.ofNat 64 i) 1)
    (code : Prog isa) (W rb : Nat) (hc : r.code = code) (hW : r.stack = W) (hr : retBitsOf r = rb)
    (hres : ∃ hc, (rtaint.check (RTaint.init W bp0) (scrubSel rb fs code) hc).any (RTaint.done rb) = true) :
    NoResidue (scrubSel (retBitsOf r) fs r.code) r.contract (retBitsOf r) :=
  RTaint.noResidue_of_verified (scrubSelCode_verified r fs hfs hsz hrb hpost) (scrubSel_pre r bp0 hbp)
    (by subst hc hW hr; exact hres)

/-! ## A buffer the first argument points to -/

theorem args_of (cs : List (String × List (BitVec 64))) (sig : Sig) (ts : List (String × List FnTable))
 :
    ((abi.withConsts cs).withTables sig ts).args = abi.args := by
  unfold Abi.withTables; split <;> unfold Abi.withConsts <;> split <;> rfl

theorem abi_args_head {ws : List Nat} {f : State → List (BitVec 64)} (h : abi.args ws = some f)
    (hne : ws ≠ []) (s : State) : ∃ vs, f s = s.gpr .a0 :: vs := by
  simp only [abi] at h
  split at h
  · cases h
    obtain ⟨w, ws', rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨((argRegs.take (w :: ws').length).map s.gpr).tail, by simp [argRegs, List.take_succ_cons]⟩
  · split at h
    · cases h
      exact ⟨(argRegs.map s.gpr ++ (List.range (ws.length - argRegs.length)).map (stackArg s)).tail,
        by simp [argRegs]⟩
    · cases h

/-- The array the first parameter of `sig` is, at `a0`, is among the regions of a state
the contract starts from. -/
theorem firstArray_mem {A : Abi isa} (hA : ScrubAbi A) (hargs : A.args = abi.args) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {nm : String} {m : Bool} {e : Elem}
    {n : Nat} {rest : List (String × Param)} (hp : sig.params = (nm, .array m e n) :: rest) {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) :
    ⟨s.gpr .a0, n * e.size⟩ ∈ s.rd ++ s.wr := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals hv
  obtain ⟨-, hrd, hwr, -⟩ := h
  rw [hargs] at hv
  have hne : (sig.words A.ptrBits).map (·.bits A.ptrBits) ≠ [] := by
    simp only [Sig.words, hp, List.flatMap_cons, Param.words, List.cons_append, List.map_cons, ne_eq,
      reduceCtorEq, not_false_eq_true]
  obtain ⟨vs, hvs⟩ := abi_args_head hv hne s
  have hb : (⟨s.gpr .a0, n * e.size⟩, m) ∈ Sig.bufs sig.params (vals s) := by
    rw [hp, hvs]; exact List.mem_cons_self
  cases m with
  | false =>
    apply List.mem_append_left; apply hA.rdSub; rw [hrd]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
      by simp⟩, rfl⟩
  | true =>
    apply List.mem_append_right; rw [← hA.wr, hwr]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
      rfl⟩, rfl⟩

/-- `scrubSel_noResidue`'s `hbp` for no buffer (`bp0 = []`). -/
theorem hbp_nil {api : Api} (r : Unscrubbed api target) :
    ∀ s, r.contract.pre s → ∀ q ∈ ([] : List (Reg × Nat)), ∀ i < q.2, ∃ g ∈ s.rd ++ s.wr,
      g.Contains (s.gpr q.1 + BitVec.ofNat 64 i) 1 :=
  fun _ _ _ hq => nomatch hq

/-- `scrubSel_noResidue`'s `hbp` for `bp0 = [(a0, n * e.size)]`, of a function whose first
parameter is an array of `n` elements of `e`. -/
theorem hbp_firstArray {api : Api} (r : Unscrubbed api target) {nm : String} {m : Bool} {e : Elem}
    {n : Nat} {rest : List (String × Param)} (hp : api.sig.params = (nm, .array m e n) :: rest) :
    ∀ s, r.contract.pre s → ∀ q ∈ [(Reg.a0, n * e.size)], ∀ i < q.2, ∃ g ∈ s.rd ++ s.wr,
      g.Contains (s.gpr q.1 + BitVec.ofNat 64 i) 1 := by
  intro s hs q hq i hi
  simp only [List.mem_singleton] at hq
  subst hq
  obtain ⟨pre, post, leak, eq⟩ := r.ofSig
  rw [eq] at hs
  refine ⟨_, firstArray_mem (ScrubAbi.of r.consts api.sig r.tables)
    (args_of r.consts api.sig r.tables) hp hs, ?_⟩
  have e' : s.gpr .a0 + BitVec.ofNat 64 i - s.gpr .a0 = BitVec.ofNat 64 i := by bv_omega
  simp only [Region.Contains, e', BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [this, hi]

end VG.RISCV64.Scrub
