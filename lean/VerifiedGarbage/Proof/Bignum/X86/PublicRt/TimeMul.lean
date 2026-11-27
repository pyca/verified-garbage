module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Correct
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Bignum.X86.PublicRt.TimeBase`, which this module and modules that import it used -/

section

/-! # What the timing of public RSA at a run-time width checks its pieces from

Every loop runs over a number's width, read from the arguments on the stack,
so the taint analysis needs them public: `τA`, the arguments above `esp`,
`edi` and `esp`, and `τF`, the same inside the frame of 36 bytes of a
multiplication's call. The arguments lie in a writable region of the
contract, which the analysis would not take as public: the runs are related
from states whose permissions are narrowed to the output and the working
space (`relCT_narrow`), which `ArgsOk` describes.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86

/-- The arguments, `edi` and `esp`. -/
def τA : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 44 }

/-- `τA` in the frame of a multiplication's call. -/
def τF : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 44, stk := [some 36] }

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (s : State) : Prop :=
  (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ r

theorem ArgsOk.keep {s t : State} (A : ArgsOk s) {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) :
    ArgsOk t :=
  ⟨by rw [K.1 _ sp]; exact A.1, by rw [K.2.2, K.1 _ sp]; exact A.2⟩

theorem τA_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τA s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem agreeA {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s₁ s₂ : State}
    (h₁ : RtIn base bytes len args s₁) (h₂ : RtIn base bytes len args s₂)
    (A₁ : ArgsOk s₁) (A₂ : ArgsOk s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) : VG.X86.Taint.Agree τA s₁ s₂ := by
  have f₁ := A₁.1
  have f₂ := A₂.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τA_wf A₁, τA_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τA, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h₁.scratch.edi_toNat.trans h₂.scratch.edi_toNat.symm)
    · exact sp
  · simp only [τA] at hk
    rw [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s₁ _ = arg s₂ _ from
      (h₁.stack _ (by omega_using [hk])).value.trans (h₂.stack _ (by omega_using [hk])).value.symm)

theorem argByte_alloc {s : State} (low : 36 ≤ (s.gpr .esp).toNat) (k : Nat) :
    VG.X86.Taint.argByte (allocFrame 36 s) (36 + k) = VG.X86.Taint.argByte s k := by
  simp only [VG.X86.Taint.argByte, allocFrame_esp]
  rw [VG.X86.Taint.sub_setWidth low, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem τF_wf {s : State} (A : ArgsOk s) (low : 36 ≤ (s.gpr .esp).toNat) :
    VG.X86.Taint.Wf τF (allocFrame 36 s) := by
  have f := A.1
  have eN : ((allocFrame 36 s).gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by
    rw [allocFrame_esp, sub_toNat low]
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨?_, fun r hr => ?_⟩, fun _ h => (List.not_mem_nil h).elim, ?_, fun p hp => ?_, fun h => absurd h (by decide)⟩
  · show _ + 36 + 44 ≤ _; omega_using [f, eN]
  · rw [show VG.X86.Taint.depth τF.stk = 36 + 0 from rfl, argByte_alloc low, VG.X86.Taint.argByte, BitVec.add_zero]
    rw [allocFrame_wr, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [VG.X86.Taint.sub_setWidth low]
      exact (Offset.base_disjoint_below _ (by decide)).symm.symm
    · exact A.2 r hr
  · show _ + 36 < _; omega_using [eN]
  · simp only [τF, VG.X86.Taint.frameList, List.mem_singleton] at hp
    subst hp
    simp only [allocFrame_wr, allocFrame_esp, List.getElem?_cons_zero, addr, BitVec.add_zero]

theorem agreeF {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s₁ s₂ : State}
    (h₁ : RtIn base bytes len args s₁) (h₂ : RtIn base bytes len args s₂)
    (A₁ : ArgsOk s₁) (A₂ : ArgsOk s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) (low : 36 ≤ (s₁.gpr .esp).toNat) :
    VG.X86.Taint.Agree τF (allocFrame 36 s₁) (allocFrame 36 s₂) := by
  have G := agreeA h₁ h₂ A₁ A₂ sp
  have low₂ : 36 ≤ (s₂.gpr .esp).toNat := sp ▸ low
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τF_wf A₁ low, τF_wf A₂ low₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => by simp only [allocFrame_esp, sp],
    fun k h4 hk => ?_⟩
  · simp only [τF, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide)]
      exact G.rf.1 _ (by simp [τA])
    · simp only [allocFrame_esp, sp]
  · rw [show VG.X86.Taint.depth τF.stk = 36 from rfl, argByte_alloc low, argByte_alloc low₂, allocFrame_mem,
      allocFrame_mem]
    have := G.argMem k h4 hk
    rwa [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add] at this

/-- Constant time on narrowed permissions: runs from states narrowed to the
regions `R` and `W` (which code that terminates from them writes in) leak the
same traces as from the states themselves. -/
theorem relCT_narrow {c : Prog isa} {Pr Pn : State → State → Prop} (R W : State → List Region)
    (hw : ∀ s₁ s₂, Pr s₁ s₂ → Covers (R s₁ ++ W s₁) (s₁.rd ++ s₁.wr) ∧ Covers (W s₁) s₁.wr ∧
      Covers (R s₂ ++ W s₂) (s₂.rd ++ s₂.wr) ∧ Covers (W s₂) s₂.wr ∧
      (∃ F, WP isa c (s₁.withRegions (R s₁) (W s₁)) F) ∧ (∃ F, WP isa c (s₂.withRegions (R s₂) (W s₂)) F) ∧
      Pn (s₁.withRegions (R s₁) (W s₁)) (s₂.withRegions (R s₂) (W s₂)))
    (h : RelCT isa Pn c fun _ _ => True) : RelCT isa Pr c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨c₁, w₁, c₂, w₂, ⟨_, u₁, n₁, en₁, -⟩, ⟨_, u₂, n₂, en₂, -⟩, hn⟩ := hw _ _ hp
  obtain ⟨x₁, -⟩ := regionModel.inline (s := s₁) (r := R s₁) (w := W s₁) en₁ c₁ w₁
  obtain ⟨x₂, -⟩ := regionModel.inline (s := s₂) (r := R s₂) (w := W s₂) en₂ c₂ w₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ x₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ x₂
  exact ⟨(h _ _ _ _ _ _ hn en₁ en₂).1, trivial⟩

end VG.Proof.Bignum.X86.PublicRt

end

end

/-! # The trace of a multiplication by a call, in public RSA at a run-time width

Two runs of `mul o a b` leak the same trace when both are ready for it
(`MulIn`) from the same stack pointer: the frame's arguments are written
from public values (`τF`), after which each run's call meets the callee's
precondition (`CallOk`, from `mulArgs_call`) and the arguments agree.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- What a multiplication by number `b` needs in a run: `Env`, number `b` below the modulus, and the
arguments apart from the writable regions. -/
def MulIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (b : Nat) (s : State) : Prop :=
  (∃ M, Env base bytes len args M s ∧ val32 s.mem base (numAt len b) (nw len) < M) ∧ ArgsOk s

/-- The state of the call: the callee's precondition, its arguments and the regions it is given. -/
def CallOk (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (o a b : Nat)
    (g : State) : Prop :=
  (Proof.Rsa.MontMul.mulContract abi 56).pre (calleeOf g base bytes) ∧ g.gpr .esp = sp - BitVec.ofNat 32 36 ∧
    (∀ i < 9, arg (calleeOf g base bytes) i = mulArg len o a b (BitVec.ofNat 32 base.toNat) (args 9) i) ∧
    (⟨(g.gpr .esp).setWidth 64, 36⟩ : Region) ∈ g.wr ∧ (⟨base, bytes⟩ : Region) ∈ g.wr

theorem mulArgs_call {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (hbytes : bytes = (args 9).toNat * 8) {o a b : Nat} (ho : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4) (ho0 : o ≠ 0)
    {s : State} (I : MulIn base bytes len args b s) {sp : BitVec 32} (hsp : s.gpr .esp = sp) :
    WP isa (.block (mulArgs o a b)) (allocFrame 36 s) (CallOk base bytes len args sp o a b) := by
  obtain ⟨⟨M, E, hB⟩, -⟩ := I
  have h := E.pi
  have R := E.room
  have low := R.low
  have hsp' := (s.gpr .esp).isLt
  have nwr := h.scratch.nowrap
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  refine WP.mono (mulArgs_ok (f := allocFrame 36 s) (len := len) (o := o) (a := a) (b := b)
    (argAt_alloc (by rw [← h.outLen]; exact (h.stack 1 (by decide)).readSrc))
    (argAt_alloc (h.stack 9 (by decide)).readSrc) h.upper (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb])
    (by rw [fEsp, VG.X86.sub_toNat (by omega_using [low])]; omega_using [])
    (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)) fun g ⟨Kg, Fg, Rg⟩ => ?_
  have gEsp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by rw [Kg.1 _ (by decide), fEsp]
  have hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem := by
    have := Fg; rwa [fEsp, allocFrame_mem] at this
  have hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      mulArg len o a b (s.gpr .edi) (args 9) i := by
    intro i hi; rw [Kg.1 _ (by decide), Rg i hi, allocFrame_gpr _ _ (by decide)]
  have hinv : (val32 s.mem base numOff (nw len) * w32 s.mem base invOff + 1) % 2 ^ 32 = 0 := by
    rw [E.mod]; exact E.inv
  have edi : s.gpr .edi = BitVec.ofNat 32 base.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [h.scratch.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (h.fits (j := 0) (by decide)).1; simp only [numAt, numOff] at this; omega_using [nwr, this])]
  refine ⟨callee_pre (callee_abi h hbytes R ho ha hb ho0 gEsp hFg hread hinv (by rw [E.mod]; exact hB)) R gEsp,
    by rw [gEsp, hsp],
    fun i hi => ?_, ?_, ?_⟩
  · rw [callee_arg (base := base) (bytes := bytes) low gEsp hread hi, edi]
  · rw [Kg.2.2, allocFrame_wr, gEsp]; exact List.mem_cons_self ..
  · rw [Kg.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ h.scratch.wr

/-- The callee's public data from its stack pointer and its arguments. -/
theorem rtPub_of {s t : State} (sp : s.gpr .esp = t.gpr .esp) (args : ∀ i < 9, arg s i = arg t i) :
    (Proof.Rsa.MontMul.mulContract abi 56).pub s t := by
  have a0 := args 0 (by decide); have a1 := args 1 (by decide); have a2 := args 2 (by decide)
  have a3 := args 3 (by decide); have a4 := args 4 (by decide); have a5 := args 5 (by decide)
  have a6 := args 6 (by decide); have a7 := args 7 (by decide); have a8 := args 8 (by decide)
  sig_pub [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes]
  sig_and_intros
  all_goals with_reducible assumption

theorem calleeOf_eq {g : State} {base : Addr} {bytes : Nat} {sp : BitVec 32}
    (hsp : g.gpr .esp = sp - BitVec.ofNat 32 36) :
    calleeOf g base bytes =
      g.callEntry.withRegions [⟨(sp - BitVec.ofNat 32 36).setWidth 64, 36⟩] [⟨base, bytes⟩] := by
  simp only [calleeOf, argAddr_callEntry, hsp, Nat.mul_zero, BitVec.add_zero]

theorem mul_relCT {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} (hbytes : bytes = (args 9).toNat * 8)
    (sp : BitVec 32) {o a b : Nat} (ho : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4) (ho0 : o ≠ 0)
    (hT : (VG.Taint.check taint τF (.block (mulArgs o a b)) (.block [])).isSome = true) :
    RelCT isa (fun s t => s.gpr .esp = sp ∧ t.gpr .esp = sp ∧ MulIn base bytes len args b s ∧
        MulIn base bytes len args b t)
      (PublicRt.mul o a b) (fun _ _ => True) := by
  unfold PublicRt.mul
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  have blk := (RelCT.taint (A := taint) (P := fun f₁ f₂ => ∃ s₁ s₂, (s₁.gpr .esp = sp ∧ s₂.gpr .esp = sp ∧
      MulIn base bytes len args b s₁ ∧ MulIn base bytes len args b s₂) ∧ f₁ = allocFrame 36 s₁ ∧
      f₂ = allocFrame 36 s₂) τF (fun _ _ ⟨s₁, s₂, ⟨e₁, e₂, I₁, I₂⟩, q₁, q₂⟩ => by
        obtain ⟨⟨M₁, E₁, -⟩, A₁⟩ := I₁
        obtain ⟨⟨M₂, E₂, -⟩, A₂⟩ := I₂
        subst q₁ q₂
        exact agreeF E₁.pi E₂.pi A₁ A₂ (e₁.trans e₂.symm) (by have := E₁.room.low; omega_using [this])) hT).wp
    (F₁ := CallOk base bytes len args sp o a b) (F₂ := CallOk base bytes len args sp o a b)
    (fun _ _ ⟨s₁, s₂, ⟨e₁, e₂, I₁, I₂⟩, q₁, q₂⟩ => by
      subst q₁ q₂
      exact ⟨mulArgs_call hbytes ho ha hb ho0 I₁ e₁, mulArgs_call hbytes ho ha hb ho0 I₂ e₂⟩)
  refine VG.RelCT.seq blk ?_
  refine RelCT.call (k := Proof.Rsa.MontMul.mulContract abi 56) VG.Proof.Mont.X86.Sse2.at_correct
    VG.Proof.Mont.X86.Sse2.at_constantTime
    [⟨(sp - BitVec.ofNat 32 36).setWidth 64, 36⟩] [⟨base, bytes⟩] ?_
  rintro g₁ g₂ ⟨-, ⟨A₁, sp₁, arg₁, fr₁, sc₁⟩, ⟨A₂, sp₂, arg₂, fr₂, sc₂⟩⟩
  have c₁ := calleeOf_eq (base := base) (bytes := bytes) sp₁
  have c₂ := calleeOf_eq (base := base) (bytes := bytes) sp₂
  rw [sp₁] at fr₁
  rw [sp₂] at fr₂
  refine ⟨c₁ ▸ A₁, c₂ ▸ A₂, ?_, Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_,
    Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_, by rw [sp₁, sp₂]⟩
  · rw [← c₁, ← c₂]
    refine rtPub_of ?_ fun i hi => (arg₁ i hi).trans (arg₂ i hi).symm
    simp only [calleeOf, State.withRegions_gpr, State.callEntry_esp, sp₁, sp₂]
  · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
    · exact List.mem_append_right _ fr₁
    · exact List.mem_append_right _ sc₁
  · rw [List.mem_singleton.mp hr]; exact sc₁
  · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
    · exact List.mem_append_right _ fr₂
    · exact List.mem_append_right _ sc₂
  · rw [List.mem_singleton.mp hr]; exact sc₂

end VG.Proof.Bignum.X86.PublicRt
