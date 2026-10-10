import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified

/-!
# Ed448's point functions on x86-64: their `Verified`

Untrusted: everything here is checked by Lean. The facts of
`Spec.Ed448.Point64`'s contracts on x86-64 (`fnPre`: `ws` in `rdi`), which
the functions meet (`fn_correct`, from `fn_regs`): the callee-saved
registers are restored, and every byte they write is in the result's slots,
slots 12–20 or the product's words, which the return address is apart from;
the spec's coordinates are the slots' field elements (`elemAt_eq`).
Constant time by taint tracking (only `rsp` and `ws` are public, and every
address is `ws` plus a constant), and a state satisfying the precondition.
-/

namespace VG.Proof.Ed448.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Point64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E clob ofs ofs_off' valAt_mod)
open VG.Impl.X448.X86_64 (slot ACC)
open VG.Spec.Ed448.Point64 (elemAt pointAt Keeps affine)

/-- The spec's coordinate at slot `i` is the slot's field element. -/
theorem elemAt_eq (m : Mem) (base : Addr) (i : Index) : elemAt m base (slot i.val) = E m base i :=
  Fin.ext (by rw [elemAt, Fin.val_ofNat, valAt_mod])

/-- The spec's point at slot `i` is the slots' point. -/
theorem pointAt_eq (m : Mem) (base : Addr) (i : Nat) (hi : i + 2 < 22) :
    pointAt m base i = pt (E m base) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ := by
  simp only [pointAt, pt]
  rw [show Spec.X448.Field64.slotAt i = slot (⟨i, by omega⟩ : Index).val from rfl,
    show Spec.X448.Field64.slotAt (i + 1) = slot (⟨i + 1, by omega⟩ : Index).val from rfl,
    show Spec.X448.Field64.slotAt (i + 2) = slot (⟨i + 2, by omega⟩ : Index).val from rfl,
    elemAt_eq, elemAt_eq, elemAt_eq]

/-- The facts of the shared contracts about the state: `ws` in `rdi`, writable for its 8192
bytes, apart from the return address, and not wrapping around. -/
def fnPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 8192⟩] ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 8192⟩ ∧
    (s.gpr .rdi).toNat + 8192 ≤ 2 ^ 64

/-- What every function's analysis may consider public. -/
def fnPub (s₁ s₂ : State) : Prop := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi

/-- The doubling's contract on x86-64. -/
def doubleK : Contract isa where
  pre := fnPre
  post s s' := pointAt s'.mem (s.gpr .rdi) 0 = Spec.Ed448.Point56.pointDouble (pointAt s.mem (s.gpr .rdi) 0) ∧
    Keeps 0 (s.gpr .rdi) s.mem s'.mem
  pub := fnPub

/-- The affine addition's contract on x86-64. -/
def addK : Contract isa where
  pre s := fnPre s ∧ elemAt s.mem (s.gpr .rdi) (Spec.X448.Field64.slotAt 11) = Spec.Ed448.d
  post s s' := pointAt s'.mem (s.gpr .rdi) 3 = Spec.Ed448.pointAdd (pointAt s.mem (s.gpr .rdi) 0)
      (affine (elemAt s.mem (s.gpr .rdi) (Spec.X448.Field64.slotAt 8))
        (elemAt s.mem (s.gpr .rdi) (Spec.X448.Field64.slotAt 9))) ∧
    Keeps 3 (s.gpr .rdi) s.mem s'.mem
  pub := fnPub

theorem fopValid_dest : ∀ op : FOp, fopValid op → fopDest op < 22
  | .mul _ _ _, h | .add _ _ _, h | .sub _ _ _, h => h.1
  | .sqr _ _, h => h.1

/-- The program's results are in the three slots from `r`, or in slots 12–20. -/
abbrev OutsOk (r : Nat) (ops : List FOp) : Prop :=
  ∀ op ∈ ops, (r ≤ fopDest op ∧ fopDest op < r + 3) ∨ (12 ≤ fopDest op ∧ fopDest op ≤ 20)

/-- A function running the field program `ops`, with its results in the three slots from `r`:
the calling convention kept, the slots' values `evalOps ops` of theirs, and `Keeps`. -/
theorem fn_correct (r : Nat) (ops : List FOp) (hv : ∀ op ∈ ops, fopValid op)
    (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (fn ops) = true)
    (hmx : (fn ops).allInstrs (fun i => !loadsMxcsr i) = true) (hout : OutsOk r ops)
    (s : State) (hs : fnPre s) :
    ∃ t s', Exec isa (fn ops) s t s' ∧ abiPreserved s s' ∧
      E s'.mem (s.gpr .rdi) = evalOps ops (E s.mem (s.gpr .rdi)) ∧ Keeps r (s.gpr .rdi) s.mem s'.mem := by
  obtain ⟨hrd, hwr, hret, hnw⟩ := hs
  have hscr : Scr s (s.gpr .rdi) := ⟨rfl, by rw [hwr]; simp, hnw⟩
  obtain ⟨t, s', he, hg, _, _, hv', hm⟩ := fn_regs ops hv hk hscr
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨fun r hr => hg r ?_, ?_⟩, hv', ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine Mem.readW_congr fun i hi => hm _ (fun op hop => ?_) ?_
    all_goals
      have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      simp only [Region.Contains, Nat.not_le] at hx
    · have := fopValid_dest op (hv op hop)
      simp only [OutOf, ofs, slot]; omega
    · simp only [ofs, ACC]; omega
  · intro i hi hp hown
    simp only [Spec.X448.Field64.wsBytes, Spec.X448.Field64.slotAt, Spec.Ed448.Point64.ownAt,
      Spec.Ed448.Point64.ownEnd] at hi hp hown
    refine hm _ (fun op hop => ?_) ?_
    · have := hout op hop
      simp only [OutOf, slot]
      rw [ofs_off' _ (by omega)]
      omega
    · rw [ofs_off' _ (by omega)]
      simp only [ACC]; omega

theorem doubleOps_outs : OutsOk 0 doubleOps := by decide

theorem addAffineOps_outs : OutsOk 3 addAffineOps := by decide

/-- The doubling meets `doubleK`. -/
theorem double_correct (hk : ∀ r ∈ keptRegs, KeepReg.keeps r doubleFn = true)
    (hmx : doubleFn.allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (hs : doubleK.pre s) :
    ∃ tr s', Exec isa doubleFn s tr s' ∧ abiPreserved s s' ∧ doubleK.post s s' := by
  obtain ⟨tr, s', he, ha, hv, hk'⟩ := fn_correct 0 doubleOps doubleOps_valid hk hmx doubleOps_outs s hs
  refine ⟨tr, s', he, ha, ?_, hk'⟩
  rw [pointAt_eq _ _ 0 (by decide), pointAt_eq _ _ 0 (by decide), hv]
  exact (doubleOps_eval _).trans (double_eq _)

/-- The affine addition meets `addK`. -/
theorem add_correct (hk : ∀ r ∈ keptRegs, KeepReg.keeps r addFn = true)
    (hmx : addFn.allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (hs : addK.pre s) :
    ∃ tr s', Exec isa addFn s tr s' ∧ abiPreserved s s' ∧ addK.post s s' := by
  obtain ⟨tr, s', he, ha, hv, hk'⟩ :=
    fn_correct 3 addAffineOps addAffineOps_valid hk hmx addAffineOps_outs s hs.1
  have hd := hs.2
  rw [show Spec.X448.Field64.slotAt 11 = slot (11 : Index).val from rfl, elemAt_eq] at hd
  refine ⟨tr, s', he, ha, ?_, hk'⟩
  rw [pointAt_eq _ _ 3 (by decide), pointAt_eq _ _ 0 (by decide), hv,
    show Spec.X448.Field64.slotAt 8 = slot (8 : Index).val from rfl,
    show Spec.X448.Field64.slotAt 9 = slot (9 : Index).val from rfl, elemAt_eq, elemAt_eq]
  refine (addAffineOps_eval _).trans ?_
  rw [hd, addWith_d]
  rfl

/-! ## Constant time -/

theorem fnPub_agree {s₁ s₂ : State} (hp : fnPub s₁ s₂) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsp]) s₁ s₂ := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.2
  · exact hp.1

/-! ## The shared contracts -/

/-- A state satisfying the doubling's precondition. -/
def fnSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem doubleK_implies : doubleK.Implies (Spec.Ed448.Point64.doubleContract X86_64.abi) := by
  sig_implies [Spec.Ed448.Point64.doubleContract, Spec.Ed448.Point64.sig, X86_64.abi, X86_64.argRegs,
    doubleK, fnPre, fnPub] [fnSat] using fnSat

end VG.Proof.Ed448.X86_64.Point64

namespace VG.Proof.Ed448.X86_64.Point64

open VG VG.X86_64

/-- The memory of `addSat`: `d`'s 56 bytes in slot 11 of the working space at `0x1000`, and zeros
elsewhere. -/
def addSatMem : Mem := fun a =>
  if (a - 0x1300).toNat < 56 then BitVec.ofNat 8 (Spec.Ed448.d.val >>> (8 * (a - 0x1300).toNat)) else 0

/-- A state satisfying the affine addition's precondition. -/
def addSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := addSatMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem addSat_d : Spec.Ed448.Point64.elemAt addSatMem 0x1000 (Spec.X448.Field64.slotAt 11) = Spec.Ed448.d := by
  decide +kernel

theorem addK_implies : addK.Implies (Spec.Ed448.Point64.addAffineContract X86_64.abi) :=
  { pre := by sig_implies_pre [Spec.Ed448.Point64.addAffineContract, Spec.Ed448.Point64.sig,
      Spec.Ed448.Point64.dSlot, Spec.Ed448.Point64.sumSlot, Spec.Ed448.Point64.pSlot,
      Spec.Ed448.Point64.qSlot, X86_64.abi, X86_64.argRegs, addK, fnPre, fnPub]
    post := by
      intro s s' _ h
      sig_post [Spec.Ed448.Point64.addAffineContract, Spec.Ed448.Point64.sig, Spec.Ed448.Point64.dSlot,
        Spec.Ed448.Point64.sumSlot, Spec.Ed448.Point64.pSlot, Spec.Ed448.Point64.qSlot, X86_64.abi,
        X86_64.argRegs, addK, fnPre, fnPub]
      exact h
    pub := by sig_implies_pub [Spec.Ed448.Point64.addAffineContract, Spec.Ed448.Point64.sig,
      Spec.Ed448.Point64.dSlot, Spec.Ed448.Point64.sumSlot, Spec.Ed448.Point64.pSlot,
      Spec.Ed448.Point64.qSlot, X86_64.abi, X86_64.argRegs, addK, fnPre, fnPub]
    sat := ⟨addSat, by
      unfold Spec.Ed448.Point64.addAffineContract
      exact Sig.contract_pre_of_check (by decide +kernel) (by
        sig_reduce [Sig.wfPre, Spec.Ed448.Point64.sig, Spec.Ed448.Point64.dSlot, X86_64.abi,
          X86_64.argRegs, addSat]
        exact ⟨by decide, addSat_d⟩)⟩ }

end VG.Proof.Ed448.X86_64.Point64
