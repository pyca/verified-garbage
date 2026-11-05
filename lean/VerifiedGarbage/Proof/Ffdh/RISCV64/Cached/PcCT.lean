module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcCorrect
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcCorrect
public meta import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public meta import VerifiedGarbage.Proof.Framework.RelCT
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Omega
-- separate module: the precompute's constant-time proof, apart from its correctness proof's chain of modules

/-!
# `vg_ffdh_generate_key_precompute` on RISC-V: constant time, and verified

The public data `PD`: the exchange's data of the precompute (`pcx`) and the
table's address. Each predicate (`At Φ`) says that the state is one of a run
from a state meeting the contract with that data, as `Φ` of that state says;
the registers the code uses as addresses or counts are functions of the
data there (`pins_*`), and where a piece computes from memory (`recognize`
the width, `bound` the bound's bit length) the next predicate fixes the
result, by correctness.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Precompute
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Impl.Ffdh.RISCV64.VettedValidation (tableSym tableConsts)

/-- The public data of a precompute. -/
structure PD where
  x : XD
  sym : Addr

def pdOf (s : State) : PD := ⟨pcx s, s.syms tableSym⟩

/-- A state of a run from a state meeting the contract, with the data `d`. -/
def At (Φ : State → State → Prop) (d : PD) (t : State) : Prop :=
  ∃ s, pcContract.pre s ∧ pdOf s = d ∧ Φ s t

theorem At.step {Φ Ψ : State → State → Prop} {c : Prog isa} (h : ∀ s t, pcContract.pre s → Φ s t → WP isa c t (Ψ s))
    (d : PD) (t : State) (ht : At Φ d t) : WP isa c t (At Ψ d) :=
  let ⟨s, hs, hd, hΦ⟩ := ht
  WP.mono (h s t hs hΦ) fun _ hu => ⟨s, hs, hd, hu⟩

/-- `Pins` from registers that the predicate fixes as functions of the data. -/
theorem pins_at {Φ : State → State → Prop} {rs : List Reg} (f : PD → Reg → BitVec 64)
    (h : ∀ s t, pcContract.pre s → Φ s t → ∀ r ∈ rs, t.gpr r = f (pdOf s) r) : Pins (At Φ) rs :=
  pins_of f fun d t ⟨s, hs, hd, hΦ⟩ r hr => by rw [← hd]; exact h s t hs hΦ r hr

/-! ## The predicates -/

def Φ0 (s t : State) : Prop := t = s

def Φ2 (s t : State) : Prop := PF s t ∧ t.gpr .a5 = BitVec.ofNat 64 (pcCap s)

/-- The registers the body keeps from the front. -/
def Ex (s t : State) : Prop :=
  t.gpr .a2 = s.gpr .a2 ∧ t.gpr .a3 = s.gpr .a3 ∧ t.gpr .a4 = s.gpr .a4 ∧
    t.gpr .a5 = BitVec.ofNat 64 (pcCap s) ∧ t.wr = s.wr

theorem Ex.keep {s t u : State} (h : Ex s t) (k : Keep [.a0, .s0, .t3, .t4, .t5] t u) : Ex s u :=
  ⟨(k.gpr (by decide)).trans h.1, (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1,
    (k.gpr (by decide)).trans h.2.2.2.1, k.2.2.trans h.2.2.2.2⟩

def Φ3 (s t : State) : Prop := Base (pcx s) t ∧ Ex s t
def Φ4 (s t : State) : Prop := X2 (pcx s) t ∧ Ex s t
def Φ5 (s t : State) : Prop := X3 (pcx s) t ∧ Ex s t
def Φ6 (s t : State) : Prop := X4 (pcx s) t ∧ Ex s t
def ΦM (s t : State) : Prop := MP (pcx s) t
def Φ7 (s t : State) : Prop := MP (pcx s) t ∧ t.gpr .s3 = BitVec.ofNat 64 (blOf (pcx s))
def Φ8 (s t : State) : Prop := t.gpr .s6 = s.gpr .a5

/-! ## Pins -/

theorem pins_Φ0 : Pins (At Φ0) [.a5] := pins_at (fun d _ => d.x.S) fun s t _ h r hr => by
  rw [List.mem_singleton] at hr; subst hr; rw [h]; rfl

theorem pins_Φ1 : Pins (At PF) [.a0, .a1, .a2] :=
  pins_at (fun d r => if r = .a0 then d.x.D else if r = .a1 then BitVec.ofNat 64 d.x.L else BitVec.ofNat 64 d.x.k)
    fun s t _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.a0
      · rw [h.a1]; exact (ofNat_toNat64 _).symm
      · rw [h.a2]; exact (ofNat_toNat64 _).symm

theorem sym_Φ1 : ∀ d t₁ t₂, At PF d t₁ → At PF d t₂ → t₁.syms tableSym = t₂.syms tableSym := by
  rintro d t₁ t₂ ⟨s₁, _, e₁, h₁⟩ ⟨s₂, _, e₂, h₂⟩
  rw [h₁.syms, h₂.syms]
  exact (congrArg PD.sym e₁).trans (congrArg PD.sym e₂).symm

theorem pins_Φ2 : Pins (At Φ2) [.s6] := pins_at (fun d _ => d.x.S) fun s t _ h r hr => by
  rw [List.mem_singleton] at hr; subst hr; exact h.1.s6

theorem pins_atBase {Φ : State → State → Prop} (h : ∀ s t, Φ s t → Base (pcx s) t) : Pins (At Φ) baseRegs :=
  fun d t₁ t₂ ⟨s₁, _, e₁, h₁⟩ ⟨s₂, _, e₂, h₂⟩ r hr => by
    have := pins_base (Φ := fun x t => Base x t) (fun _ _ h => h) d.x t₁ t₂
      (by rw [← e₁]; exact h _ _ h₁) (by rw [← e₂]; exact h _ _ h₂) r hr
    exact this

theorem pins_Φ5 : Pins (At Φ5) (baseRegs ++ ([.t4] : List Reg)) :=
  fun d t₁ t₂ ⟨s₁, _, e₁, h₁⟩ ⟨s₂, _, e₂, h₂⟩ r hr =>
    pins_X3 d.x t₁ t₂ (by rw [← e₁]; exact h₁.1) (by rw [← e₂]; exact h₂.1) r hr

theorem pins_ΦM : Pins (At ΦM) (baseRegs ++ ([.a2, .a3, .a4] : List Reg)) := by
  intro d t₁ t₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pins_atBase (Φ := ΦM) (fun _ _ h => h.base) d t₁ t₂ h₁ h₂ r hr
  · refine pins_at (Φ := ΦM) (rs := [.a2, .a3, .a4])
      (fun d r => if r = .a2 then d.x.D else if r = .a3 then BitVec.ofNat 64 d.x.L else BitVec.ofNat 64 d.x.k)
      (fun s t _ h r hr => ?_) d t₁ t₂ h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h.a2, h.a3, h.a4]

theorem pins_Φ7 : Pins (At Φ7) (baseRegs ++ ([.a5, .s3] : List Reg)) := by
  intro d t₁ t₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pins_atBase (Φ := Φ7) (fun _ _ h => h.1.base) d t₁ t₂ h₁ h₂ r hr
  · refine pins_at (Φ := Φ7) (rs := [.a5, .s3])
      (fun d r => if r = .a5 then BitVec.ofNat 64
          (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups d.x.k d.x.db)
        else BitVec.ofNat 64 (blOf d.x))
      (fun s t _ h r hr => ?_) d t₁ t₂ h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1.a5, h.2]

theorem pins_Φ8 : Pins (At Φ8) [.s6] := pins_at (fun d _ => d.x.S) fun s t _ h r hr => by
  rw [List.mem_singleton] at hr; subst hr; exact h

/-! ## The steps, by correctness -/

theorem S0 (s t : State) (hs : pcContract.pre s) (h : Φ0 s t) : WP isa (.block front) t (PF s) := by
  subst h; exact pcFront_ok (pp_of hs)

theorem S1 (s t : State) (hs : pcContract.pre s) (h : PF s t) :
    WP isa VG.Impl.Ffdh.RISCV64.VettedValidation.recognize t (Φ2 s) := recog_ok (pp_of hs) h

theorem S2 (s t : State) (hs : pcContract.pre s) (h : Φ2 s t) : WP isa (.block post) t (Φ3 s) :=
  WP.mono (post_ok (pp_of hs) h.1) fun _ ⟨b, a2, a3, a4, a5, _, _, w⟩ => ⟨b, a2, a3, a4, a5.trans h.2, w⟩

theorem S3 (s t : State) (_ : pcContract.pre s) (h : Φ3 s t) : WP isa Precompute.loadN t (Φ4 s) :=
  WP.mono (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadN_X h.1) (by rfl)) fun _ ⟨⟨h', _⟩, k⟩ => ⟨h', h.2.keep k⟩

theorem S4 (s t : State) (_ : pcContract.pre s) (h : Φ4 s t) : WP isa (.block Precompute.check1) t (Φ5 s) :=
  WP.mono (WP.keep [.a0, .s0, .t3, .t4, .t5] (check1_X h.1) (by rfl)) fun _ ⟨⟨h', _⟩, k⟩ => ⟨h', h.2.keep k⟩

theorem S5 (s t : State) (_ : pcContract.pre s) (h : Φ5 s t) : WP isa Precompute.check2 t (Φ6 s) :=
  WP.mono (WP.keep [.a0, .s0, .t3, .t4, .t5] (check2_X h.1) (by rfl)) fun _ ⟨⟨h', _⟩, k⟩ => ⟨h', h.2.keep k⟩

theorem valid_of {s : State} (hs : pcContract.pre s) : Spec.Rsa.modulusValid (pcx s).p (pcx s).k = true :=
  Proof.Ffdh.domainValid_mod (pp_of hs).dv

theorem SM (s t : State) (hs : pcContract.pre s) (h : Φ6 s t) : ΦM s t :=
  mp_of (pp_of hs) h.1 h.2.2.2.2.2 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1

theorem SB (s t : State) (_ : pcContract.pre s) (h : ΦM s t) : WP isa bound t (Φ7 s) :=
  WP.mono (bound_step h) fun _ ⟨h', _⟩ => h'

theorem SR (s t : State) (_ : pcContract.pre s) (h : Φ7 s t) :
    WP isa (.seq width (.seq (.block metadata) (.seq VG.Impl.Ffdh.RISCV64.r2 (.seq storePrefix
      (.seq table (.block [.li .a0 1])))))) t (Φ8 s) :=
  WP.mono (rest_ok h.1 h.2) fun _ ⟨_, _, h6, _⟩ => h6

/-! ## Constant time -/

/-- Code the taint analysis with the table's address public proves constant
time. -/
theorem two_taint_tbl {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    (hsym : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.syms tableSym = s₂.syms tableSym) {hc : VG.Taint.Hint T}
    (h : (VG.Taint.check (taintSym [tableSym]) (ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [tableSym]) (ofRegs rs) (fun _ _ ⟨a, h₁, h₂, hsp⟩ =>
    ⟨⟨hsp, fun r hr => hpin a _ _ h₁ h₂ r (mem_ofRegs.mp hr)⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsym a _ _ h₁ h₂⟩) h

theorem main_rel : RelCT isa (Two (At ΦM)) main (Two (At Φ8)) := by
  unfold main
  simp only [seqs]
  exact RelCT.seq (two_post (two_taint _ pins_ΦM (by taint_decide)) (At.step SB))
    (two_post (two_taint _ pins_Φ7 (by taint_decide)) (At.step SR))

theorem pc_rel : RelCT isa (Two (At Φ0)) Precompute.code fun _ _ => True := by
  unfold Precompute.code
  refine RelCT.seq (two_post (two_taint _ pins_Φ0 (by taint_decide)) (At.step S0))
    (RelCT.seq (two_post (two_taint_tbl _ pins_Φ1 sym_Φ1 (by taint_decide)) (At.step S1))
      (RelCT.seq (two_post (two_taint _ pins_Φ2 (by taint_decide)) (At.step S2))
        (RelCT.seq (R := Two (At Φ6)) ?_
          (RelCT.seq (R := Two (At Φ8)) ?_ (two_taint _ pins_Φ8 (by taint_decide))))))
  · unfold VG.Impl.Ffdh.RISCV64.loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_atBase (Φ := Φ3) fun _ _ h => h.1) (by taint_decide)) (At.step S3))
      (RelCT.seq (two_post (two_taint _ (pins_atBase (Φ := Φ4) fun _ _ h => h.1.1) (by taint_decide)) (At.step S4))
        (two_post (two_taint _ pins_Φ5 (by taint_decide)) (At.step S5)))
  · refine RelCT.ite (fun s₁ s₂ ⟨d, ⟨u₁, hu₁, _, h₁⟩, ⟨u₂, hu₂, _, h₂⟩, _⟩ => ?_)
      (RelCT.mono main_rel (fun s₁ s₂ ⟨⟨d, ⟨u₁, hu₁, e₁, h₁⟩, ⟨u₂, hu₂, e₂, h₂⟩, hsp⟩, _⟩ =>
        ⟨d, ⟨u₁, hu₁, e₁, SM u₁ s₁ hu₁ h₁⟩, ⟨u₂, hu₂, e₂, SM u₂ s₂ hu₂ h₂⟩, hsp⟩) fun _ _ h => h)
      (RelCT.of_false fun s₁ s₂ ⟨⟨d, ⟨u₁, hu₁, _, h₁⟩, _, _⟩, hc⟩ => by
        rw [Steps.eval_zero, h₁.1.2.2.mpr (valid_of hu₁)] at hc
        exact absurd hc (by decide))
    rw [Steps.eval_zero, Steps.eval_zero, h₁.1.2.2.mpr (valid_of hu₁), h₂.1.2.2.mpr (valid_of hu₂)]

theorem pdOf_eq {s t : State} (hp : pcContract.pub s t) : pdOf s = pdOf t := by
  obtain ⟨⟨_, hb, h0, h1, h2, h3, h4, h5, h6⟩, hsym⟩ := hp
  have eb : pcDom s = pcDom t := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp hb
  unfold pdOf pcx
  simp only [pcDom] at eb
  rw [eb, h0, h2, h3, h4, h5, h6, hsym]

theorem pc_ct : ConstantTime isa pcContract.pre pcContract.pub Precompute.code :=
  RelCT.constantTime (pc_rel.mono (fun s t ⟨hs, ht, hp⟩ =>
    ⟨pdOf s, ⟨s, hs, rfl, rfl⟩, ⟨t, ht, (pdOf_eq hp).symm, rfl⟩, hp.1.1⟩) fun _ _ h => h)

/-- `vg_ffdh_generate_key_precompute`, with the vetted groups' table. -/
theorem pc_verified :
    Verified target Precompute.code (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts)) :=
  Verified.of_correct pc_correct pc_ct pc_implies

end VG.Proof.Ffdh.RISCV64.Cached
