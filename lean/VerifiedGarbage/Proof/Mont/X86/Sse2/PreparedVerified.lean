module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedABI
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
import VerifiedGarbage.Proof.Mont.X86.ArgWs
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
import VerifiedGarbage.Proof.Mont.X86.Compact.Satisfiable
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Time
public import VerifiedGarbage.Proof.Mont.X86.Sse2.TimeTaint

/-! # `vg_rsa_mont_mul` on x86 with SSE2: verified

The kernel's numbers: `N = 2 w` words of 32 bits, the modulus at array 0,
`-m⁻¹`'s low word at header byte 56, the scratch at array 2 (its `8 N + 28`
bytes run on into array 3), the operands and the result at their arrays.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.Mont (Layout Operand wOf arrAt aM)
open VG.Proof.Mont.X86.Dynamic (ofs_far)

/-- What `body preparedParams` takes of a state meeting the contract's precondition. -/
theorem prReady {s : State} (A : PrABI s) :
    Ready preparedParams (wsOf s) (lenOf s) (2 * wOf s.mem (wsOf s)) (arrAt (wOf s.mem (wsOf s)) 2)
      (arrAt (wOf s.mem (wsOf s)) 0) 56 (arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat)
      (arrAt (wOf s.mem (wsOf s)) (arg s 3).toNat) (arrAt (wOf s.mem (wsOf s)) (arg s 4).toNat) s := by
  have Ly := A.lay
  have hinv := Compact.prepared_inverse (by have := A.layout.1; omega_arith) A.inverse
  have hb := A.rightLt
  rw [Compact.numAt_val32, Compact.numAt_val32] at hb
  exact ⟨A.entry, Ly, preparedParams_ok A,
    VG.Proof.Mont.X86.Square.low_inverse s.mem (wsOf s) _ _ Ly.hN hinv, hb⟩

theorem preparedBody_noSp : NoSp (seqs [.block preparedParams, withParams, .block restoreRegs]) :=
  NoSp.of_all (by decide +kernel)

theorem prepared_correct (s : State) (h : (Proof.Rsa.Mont.mulContract abi 56).pre s) :
    ∃ tr t, Exec isa preparedBody s tr t ∧ abiPreserved s t ∧ (Proof.Rsa.Mont.mulContract abi 56).post s t := by
  have A := prAbi_of h
  have R := prReady A
  obtain ⟨tr, t, E, lt, cong, mem, cs, -, -⟩ := body_ok R.entry R.ly preparedBody_noSp R.par R.inv R.bLt
  have Ly := A.lay
  have hs := Ly.s_le
  have hol := Ly.o_le
  have hst := A.stackBound
  have hb := A.bound
  have po := Compact.operand_apart (w := wOf s.mem (wsOf s)) A.output
  have e2 : arrAt (wOf s.mem (wsOf s)) 2 + 16 * (wOf s.mem (wsOf s) + 2) = arrAt (wOf s.mem (wsOf s)) 4 := by
    unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have e3 : arrAt (wOf s.mem (wsOf s)) 3 = arrAt (wOf s.mem (wsOf s)) 2 + 8 * (wOf s.mem (wsOf s) + 2) := by
    unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  refine ⟨tr, t, E, ⟨cs, ?_⟩, ?_⟩
  · refine Mem.readW_congr fun i hi => mem _ (fun r hr => ?_) (fun hc => ?_)
    · have := ofs_far (base := wsOf s) (size := lenOf s) (x := (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i)
        fun hc => A.retScratch _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only at this ⊢ <;> omega_arith
    · have := (s.gpr .esp).isLt
      simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        at hc
      omega_arith
  · sig_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_, ?_⟩
    · rw [Compact.numAt_val32, Compact.numAt_val32]; exact lt
    · rw [Compact.numAt_val32, Compact.numAt_val32, Compact.numAt_val32, Compact.numAt_val32,
        show 64 * wOf s.mem (wsOf s) = 32 * (2 * wOf s.mem (wsOf s)) by omega_arith]
      exact cong
    · intro i hi hj
      apply mem _ (fun r hr => ?_) (fun hc => ?_)
      · rw [show ofs (wsOf s) (wsOf s + BitVec.ofNat 64 i) = i by
          simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by simp only [lenOf] at hb; omega_arith)]]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have h2 := hj Proof.Rsa.Mont.aAcc (by simp)
        have h3 := hj Proof.Rsa.Mont.aTmp (by simp)
        have ho := hj (arg s 2).toNat (by simp)
        simp only [Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] at h2 h3
        generalize wOf s.mem (wsOf s) = w at *
        have e2' : arrAt w 2 + 16 * (w + 2) = arrAt w 4 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
        have e3' : arrAt w 3 = arrAt w 2 + 8 * (w + 2) := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
        rcases hr with rfl | rfl <;> simp only <;> omega_arith
      · have := (s.gpr .esp).isLt
        have := (arg s 0).isLt
        have := A.stackLo
        refine A.stkScratch (wsOf s + BitVec.ofNat 64 i) ?_ ?_
        · simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
            at hc ⊢
          omega_arith
        · simp only [Region.Contains, lenOf, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth,
            BitVec.toNat_ofNat]
          omega_arith

theorem prepared_publicArgs {s t : State} (H : (Proof.Rsa.Mont.mulContract abi 56).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 5, arg s i = arg t i) ∧ wOf s.mem (wsOf s) = wOf t.mem (wsOf t) := by
  sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, fun i hi => ?_, List.singleton_inj.mp (by with_reducible assumption)⟩
  match i, hi with
  | 0, _ => with_reducible assumption
  | 1, _ => with_reducible assumption
  | 2, _ => with_reducible assumption
  | 3, _ => with_reducible assumption
  | 4, _ => with_reducible assumption

/-- The 24 bytes from `esp` (the return address and the arguments) lie apart
from the registers' frame and the working space. -/
theorem PrABI.argsApart {s : State} (A : PrABI s) :
    ∀ r ∈ (pushed rs4 s).wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 24⟩ r := by
  intro r hr
  rw [pushed_wr, A.wr] at hr
  have := (s.gpr .esp).isLt
  have := A.stackLo
  have := A.stackBound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · intro x hx hf
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, List.length_cons,
      List.length_nil] at hx hf
    omega_arith
  · intro x hx hw
    by_cases h4 : (x - (s.gpr .esp).setWidth 64).toNat < 4
    · exact A.retScratch x (by simp only [Region.Contains]; omega_arith) hw
    · refine A.argScratch x hw ?_
      simp only [Region.Contains, argAddr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
        BitVec.toNat_ofNat] at hx h4 ⊢
      omega_arith

/-- A byte of the arguments, above the registers' frame. -/
theorem PrABI.argByte {s : State} (A : PrABI s) {k : Nat} (h4 : 4 ≤ k) (hk : k < 24) :
    (pushed rs4 s).mem (X86.Taint.argByte (pushed rs4 s) (16 + k)) =
      (arg s ((k - 4) / 4)).extractLsb' (8 * ((k - 4) % 4)) 8 := by
  have hlo := A.stackLo
  have hhi := A.stackBound
  have e : X86.Taint.argByte (pushed rs4 s) (16 + k) = X86.Taint.argByte s k := by
    simp only [X86.Taint.argByte, pushed_esp]
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat,
      List.length_cons, List.length_nil]
    omega_arith
  have h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  have F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [e, F1 _ fun r hr hc => ?_, X86.Taint.argByte_eq (n := 24) (by omega_arith) h4 hk,
    Mem.readW_byte s.mem (argAddr s ((k - 4) / 4)) (Nat.mod_lt _ (by decide))]
  · rfl
  · simp only [List.mem_singleton] at hr; subst hr
    have := (s.gpr .esp).isLt
    simp only [Region.Contains, X86.Taint.argByte, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
      BitVec.toNat_ofNat, List.length_cons, List.length_nil] at hc
    omega_arith

theorem agree_pr {s₁ s₂ : State} (A₁ : PrABI s₁) (A₂ : PrABI s₂) (sp : s₁.gpr .esp = s₂.gpr .esp)
    (args : ∀ i < 5, arg s₁ i = arg s₂ i) : X86.Taint.Agree prTaint (pushed rs4 s₁) (pushed rs4 s₂) := by
  have ab : ∀ {s : State}, PrABI s → X86.Taint.argByte (pushed rs4 s) 16 = (s.gpr .esp).setWidth 64 := by
    intro s A
    have := A.stackLo
    simp only [X86.Taint.argByte, pushed_esp]
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat,
      List.length_cons, List.length_nil]
    omega_arith
  have fit : ∀ {s : State}, PrABI s → ((pushed rs4 s).gpr .esp).toNat + 16 = (s.gpr .esp).toNat := by
    intro s A
    have := A.stackLo
    rw [pushed_esp, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat, List.length_cons, List.length_nil]
    omega_arith
  have wf : ∀ {s : State}, PrABI s → X86.Taint.Wf prTaint (pushed rs4 s) := fun {s} A =>
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
      fun _ => ⟨by show _ + 16 + 24 ≤ _; have := fit A; have := A.stackBound; omega_arith,
        by show ∀ r ∈ _, Region.Disjoint ⟨X86.Taint.argByte _ 16, 24⟩ r; rw [ab A]; exact A.argsApart⟩,
      fun _ h => (List.not_mem_nil h).elim, by show _ + 16 < _; have := fit A; have := A.stackBound; omega_arith,
      fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0)⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf A₁, wf A₂,
    X86.Taint.slotsOk_empty, X86.Taint.slotsAgree_empty, fun _ => by rw [pushed_esp, pushed_esp, sp],
    fun k h4 hk => ?_⟩
  · simp only [prTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; rw [pushed_esp, pushed_esp, sp]
  · have hk' : k < 24 := hk
    show (pushed rs4 s₁).mem (X86.Taint.argByte (pushed rs4 s₁) (16 + k)) =
      (pushed rs4 s₂).mem (X86.Taint.argByte (pushed rs4 s₂) (16 + k))
    rw [A₁.argByte h4 hk', A₂.argByte h4 hk', args _ (by omega_arith)]

/-- Two runs with the same numbers and arguments. -/
def PrPair (W : Addr) (L N S mo inv o a b : Nat) (s₁ s₂ : State) : Prop :=
  BPair preparedParams W L N S mo inv o a b s₁ s₂ ∧ PrABI s₁ ∧ PrABI s₂ ∧ ∀ i < 5, arg s₁ i = arg s₂ i

theorem prepared_constantTime :
    ConstantTime isa (Proof.Rsa.Mont.mulContract abi 56).pre (Proof.Rsa.Mont.mulContract abi 56).pub
      preparedBody := by
  apply RelCT.constantTime
  refine RelCT.mono (P := fun s₁ s₂ => ∃ W L N S mo inv o a b, PrPair W L N S mo inv o a b s₁ s₂)
    (RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => body_relCT (fun _ _ h => h.1) fun x y tx ty x' y' ⟨s₁, s₂, P, ex, ey⟩ e₁ e₂ =>
        ⟨preparedParams_constantTime _ _ _ _ _ _ trivial trivial
          (by rw [ex, ey]; exact agree_pr P.2.1 P.2.2.1 P.1.2.2 P.2.2.2) e₁ e₂, trivial⟩) ?_ fun _ _ _ => trivial
  rintro s₁ s₂ ⟨h₁, h₂, hp⟩
  obtain ⟨sp, args, hw⟩ := prepared_publicArgs hp
  have R := prReady (prAbi_of h₂)
  simp only [wsOf, lenOf, ← args 0 (by decide), ← args 1 (by decide), ← args 2 (by decide),
    ← args 3 (by decide), ← args 4 (by decide)] at R hw
  rw [← hw] at R
  exact ⟨_, _, _, _, _, _, _, _, _, ⟨prReady (prAbi_of h₁), R, sp⟩, prAbi_of h₁, prAbi_of h₂, args⟩

theorem prepared_satisfiable : ∃ s, (Proof.Rsa.Mont.mulContract abi 56).pre s := by
  sig_implies_sat [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes, stackBelow]
    [Compact.satState, arg, argAddr, Mem.readW, Mem.read] using Compact.satState

theorem prepared_verified : Verified target preparedBody (Proof.Rsa.Mont.mulContract abi 56) :=
  ⟨prepared_correct, prepared_constantTime, prepared_satisfiable⟩

end VG.Proof.Mont.X86.Sse2
