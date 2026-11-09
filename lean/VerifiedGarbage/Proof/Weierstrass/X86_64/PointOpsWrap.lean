module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.PointOps
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.PointOps
meta import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.X86_64.MulPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
meta import VerifiedGarbage.Proof.Weierstrass.PointOpsContract

/-!
# Point operations as functions on x86-64: the registers they keep

A function's body runs between `saves`, which copies `rbp` and `r12`–`r15`
into `xmm0`–`xmm4` and changes nothing else that the proofs follow
(`saves_ok`), and `restores`, which copies them back and changes only them
(`restores_ok`): a run of `wrap d` is a run of `d` from a state that keeps
every register and the memory (`wrap_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Weierstrass.X86_64.PointOps
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64

/-- The registers `restores` writes. -/
abbrev keptRegs : List Reg := kept.map Prod.fst

private theorem setXmm_gpr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
private theorem setXmm_mem (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
private theorem setXmm_rd (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
private theorem setXmm_wr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl

theorem saves_ok (s : State) : WP isa (.block saves) s fun t => Keeps [] s t := by
  apply WP.of_runBlock
  simp only [saves, kept, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, Option.some.injEq, exists_eq_left', Keeps, setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr,
    implies_true, and_self]

theorem restores_ok (s : State) : WP isa (.block restores) s fun t => Keeps keptRegs s t := by
  apply WP.of_runBlock
  simp only [restores, kept, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2]

/-- A run of `wrap d`: `d` from a state keeping every register and the
memory, then `restores`, which keeps all but `keptRegs`. -/
theorem wrap_ok {d : Prog isa} {s : State} {F : State → Prop}
    (h : ∀ s₁, Keeps [] s s₁ → s₁.syms = s.syms →
      WP isa d s₁ fun t => ∀ u, Keeps keptRegs t u → u.syms = t.syms → F u) :
    WP isa (wrap d) s F :=
  WP.seq (WP.mono_syms (saves_ok s) fun s₁ k₁ y₁ =>
    WP.seq (WP.mono (h s₁ k₁ y₁) fun t ht => WP.mono_syms (restores_ok t) fun u ku yu => ht u ku yu))

/-- `ProgKeep` from `Keeps` of registers the field arithmetic may write. -/
theorem progKeep_of_keeps {M : Mod} {base : Addr} {W : List Nat} {s t : State} {rs : List Reg}
    (hk : Keeps rs s t) (hr : ∀ r ∈ rs, r ∈ clob M.n) : ProgKeep M base W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')), hk.2.2.1, hk.2.2.2, fun x _ _ => congrFun hk.2.1 x⟩

/-- `wrap d` keeps what `d` keeps, for a precondition `P` and a postcondition
`F` that the registers `saves` and `restores` write do not affect. -/
theorem wrap_keep_ok {M : Mod} {base : Addr} {W : List Nat} {d : Prog isa} {s : State}
    {P F : State → Prop} (hclob : ∀ r ∈ keptRegs, r ∈ clob M.n)
    (hP : ∀ x y, ProgKeep M base W x y → Keeps [] x y → y.syms = x.syms → P x → P y)
    (hF : ∀ x y, ProgKeep M base W x y → Keeps keptRegs x y → y.syms = x.syms → F x → F y)
    (hs : P s) (hd : ∀ x, P x → WP isa d x fun t => ProgKeep M base W x t ∧ F t) :
    WP isa (wrap d) s fun t => ProgKeep M base W s t ∧ F t := by
  apply wrap_ok
  intro s₁ k₁ y₁
  have p₁ : ProgKeep M base W s s₁ := progKeep_of_keeps k₁ (by simp)
  refine WP.mono (hd s₁ (hP s s₁ p₁ k₁ y₁ hs)) fun t ⟨kt, ft⟩ u ku yu => ?_
  have pu : ProgKeep M base W t u := progKeep_of_keeps ku hclob
  exact ⟨(p₁.trans kt).trans pu, hF t u pu ku yu ft⟩

/-! ## The callee-saved registers -/

/-! ## Timing -/

theorem saves_ct : ScratchCT (.block saves) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem restores_ct : ScratchCT (.block restores) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- `wrap d` is constant time for runs agreeing on the field values `E` of
the slots `V` if `d` is. -/
theorem wrap_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    {V W : List Nat} {E : Nat → Fin m} {d : Prog isa}
    (hd : RelCT isa (FieldPair M base size m Sl V E) d
      (fun s t => ∃ E', FieldPair M base size m Sl W E' s t)) :
    RelCT isa (FieldPair M base size m Sl V E) (wrap d)
      (fun s t => ∃ E', FieldPair M base size m Sl W E' s t) :=
  RelCT.seq (fieldProgram_relCT saves_ct fun s h => WP.mono (saves_ok s) fun _ k => h.of_keeps k (by simp))
    (RelCT.seq hd (RelCT.exists_ fun E' =>
      (fieldProgram_relCT (V := W) (E := E') restores_ct fun s h =>
        WP.mono (restores_ok s) fun _ k => h.of_keeps k (by decide)).mono
        (fun _ _ h => h) fun _ _ h => ⟨E', h⟩))

end VG.Proof.Weierstrass.X86_64.PointOps
