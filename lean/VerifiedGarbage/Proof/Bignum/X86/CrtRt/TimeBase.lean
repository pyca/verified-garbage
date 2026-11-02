module

import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Top
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # What the timing of private CRT at a run-time width checks its pieces from

As for public RSA (`PublicRt/TimeBase.lean`): the eighteen arguments above
`esp`, `edi` and `esp` are public (`τA`; `τF` inside the frame of a
multiplication's call), on states whose permissions are narrowed to the
output and the working space (`ArgsOk`). Two runs of `mul c o a b` leak the
same trace when each is ready for it (`MulIn`: the context and slot `b`
below its modulus) from the same `esp` (`mul_relCT`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both argByte_alloc calleeOf calleeOf_eq rtPub_of callee_pre argAt_alloc)

/-- The arguments, `edi` and `esp`. -/
def τA : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 76 }

/-- `τA` in the frame of a multiplication's call. -/
def τF : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 76, stk := [some 36] }

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (s : State) : Prop :=
  (s.gpr .esp).toNat + 76 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ r

theorem ArgsOk.keep {s t : State} (A : ArgsOk s) {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs := by decide) :
    ArgsOk t :=
  ⟨by rw [K.1 _ sp]; exact A.1, by rw [K.2.2, K.1 _ sp]; exact A.2⟩

/-- `τA`, and `esi` (a pointer) public. -/
def τAs : VG.X86.Taint.T := { regs := .ofList [.edi, .esp, .esi], flags := false, argLen := 76 }

theorem τAs_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τAs s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem τA_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τA s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem agreeA {s₁ s₂ : State} (h₁ : In Ex base bytes len args s₁) (h₂ : In Ex base bytes len args s₂)
    (A₁ : ArgsOk s₁) (A₂ : ArgsOk s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) : VG.X86.Taint.Agree τA s₁ s₂ := by
  have f₁ := A₁.1
  have f₂ := A₂.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τA_wf A₁, τA_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τA, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h₁.edi.trans h₂.edi.symm)
    · exact sp
  · simp only [τA] at hk
    rw [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s₁ _ = arg s₂ _ from
      (h₁.stack _ (by omega)).value.trans (h₂.stack _ (by omega)).value.symm)

theorem agreeAs {s₁ s₂ : State} (h₁ : In Ex base bytes len args s₁) (h₂ : In Ex base bytes len args s₂)
    (A₁ : ArgsOk s₁) (A₂ : ArgsOk s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) (si : s₁.gpr .esi = s₂.gpr .esi) :
    VG.X86.Taint.Agree τAs s₁ s₂ := by
  have G := agreeA h₁ h₂ A₁ A₂ sp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τAs_wf A₁, τAs_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => G.argMem k h4 hk⟩
  simp only [τAs, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact G.rf.1 _ (by simp [τA])
  · exact sp
  · exact si

theorem τF_wf {s : State} (A : ArgsOk s) (low : 36 ≤ (s.gpr .esp).toNat) :
    VG.X86.Taint.Wf τF (allocFrame 36 s) := by
  have f := A.1
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨?_, fun r hr => ?_⟩, fun _ h => (List.not_mem_nil h).elim, ?_, fun p hp => ?_, fun h => absurd h (by decide)⟩
  · show _ + 36 + 76 ≤ _
    rw [allocFrame_esp, sub_toNat low]; omega
  · rw [show VG.X86.Taint.depth τF.stk = 36 + 0 from rfl, argByte_alloc low, VG.X86.Taint.argByte, BitVec.add_zero]
    rw [allocFrame_wr, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [VG.X86.Taint.sub_setWidth low]
      exact (Offset.base_disjoint_below _ (by decide)).symm.symm
    · exact A.2 r hr
  · show _ + 36 < _
    rw [allocFrame_esp, sub_toNat low]; omega
  · simp only [τF, VG.X86.Taint.frameList, List.mem_singleton] at hp
    subst hp
    simp only [allocFrame_wr, allocFrame_esp, List.getElem?_cons_zero, addr, BitVec.add_zero]

theorem agreeF {s₁ s₂ : State} (h₁ : In Ex base bytes len args s₁) (h₂ : In Ex base bytes len args s₂)
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

/-- What a run of `sized` keeps: the inputs, the arguments apart and `esp`. -/
def Run (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  In Ex base bytes len args s ∧ ArgsOk s ∧ s.gpr .esp = sp

theorem Run.agree {sp : BitVec 32} {s t : State} (R₁ : Run Ex base bytes len args sp s)
    (R₂ : Run Ex base bytes len args sp t) : VG.X86.Taint.Agree τA s t :=
  agreeA R₁.1 R₂.1 R₁.2.1 R₂.2.1 (R₁.2.2.trans R₂.2.2.symm)

theorem taint_both {τ : VG.X86.Taint.T} {P F : State → Prop} {c : Prog isa}
    (hag : ∀ s t, P s → P t → VG.X86.Taint.Agree τ s t)
    (hc : VG.Taint.Hint VG.X86.Taint.T) (hT : (VG.Taint.check taint τ c hc).isSome = true)
    (hw : ∀ s, P s → WP isa c s F) : RelCT isa (Both P) c (Both F) :=
  relCT_both (RelCT.taint (A := taint) τ (fun s t h => hag s t h.1 h.2) hT) hw

/-- What a multiplication by slot `b` of the context `c` needs of a run. -/
def MulIn (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (c : Ctx) (b : Nat)
    (s : State) : Prop :=
  (∃ M, CtxOk Ex base bytes len args c M s ∧ sv s.mem base len c b < M) ∧ ArgsOk s ∧ s.gpr .esp = sp

/-- The state of the call: the callee's precondition, its arguments and the regions it is given. -/
def CallOk (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (c : Ctx) (o a b : Nat)
    (g : State) : Prop :=
  (Proof.Rsa.MontMul.mulContract abi 56).pre (calleeOf g base bytes) ∧ g.gpr .esp = sp - BitVec.ofNat 32 36 ∧
    (∀ i < 9, arg (calleeOf g base bytes) i = callArg (BitVec.ofNat 32 base.toNat) (args wsLenArg)
      (bc len c / 8) numBase invOff (lo len (.slot c 1)) (lo len (.slot c o)) (lo len (.slot c a))
      (lo len (.slot c b)) i) ∧
    (⟨(g.gpr .esp).setWidth 64, 36⟩ : Region) ∈ g.wr ∧ (⟨base, bytes⟩ : Region) ∈ g.wr

theorem mulArgs_call {sp : BitVec 32} {c : Ctx} {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a)
    (ha : a ≤ 8) (hb3 : 3 ≤ b) (hb : b ≤ 8) {s : State} (I : MulIn Ex base bytes len args sp c b s) :
    WP isa (.block (mulArgs c o a b)) (allocFrame 36 s) (CallOk base bytes len args sp c o a b) := by
  obtain ⟨⟨M, C, hB⟩, -, hsp⟩ := I
  have h := C.inp
  have R := h.room
  have low := R.low
  have hsp' := (s.gpr .esp).isLt
  have nwr := h.scratch.nowrap
  have top := h.top
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have hm := C.mod
  simp only [sv, z0] at hm hB
  refine WP.mono (mulArgs_ok (f := allocFrame 36 s) (len := len) (c := c) (o := o) (a := a) (b := b)
    (argAt_alloc h.width) (argAt_alloc (h.arg (i := wsLenArg) (by decide))) h.upper' (by omega) (by omega)
    (by omega) (by rw [fEsp, VG.X86.sub_toNat (by omega)]; omega)
    (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)) fun g ⟨Kg, Fg, Rg⟩ => ?_
  have gEsp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by rw [Kg.1 _ (by decide), fEsp]
  have hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem := by
    have := Fg; rwa [fEsp, allocFrame_mem] at this
  have hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      callArg (s.gpr .edi) (args wsLenArg) (bc len c / 8) numBase invOff (lo len (.slot c 1))
        (lo len (.slot c o)) (lo len (.slot c a)) (lo len (.slot c b)) i := by
    intro i hi; rw [Kg.1 _ (by decide), Rg i hi, allocFrame_gpr _ _ (by decide)]
  have e8 := bc_dvd len c
  have cw : 2 * (bc len c / 8) = cwc len c := cwc_eq len c
  have edi : s.gpr .edi = BitVec.ofNat 32 base.toNat := by
    rw [← h.edi_eq]; apply BitVec.eq_of_toNat_eq
    rw [h.hbase, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← h.hbase]; exact (args 16).isLt)]
  refine ⟨callee_pre (callee_abi h.scratch h.hbytes R (h.offs c ho3 ho ha3 ha hb3 hb) gEsp hFg hread
    (by rw [cw, hm]; exact C.inv) (by rw [cw, hm]; exact hB)) R gEsp, by rw [gEsp, hsp], fun i hi => ?_, ?_, ?_⟩
  · rw [callee_arg (base := base) (bytes := bytes) low gEsp hread hi, edi]
  · rw [Kg.2.2, allocFrame_wr, gEsp]; exact List.mem_cons_self ..
  · rw [Kg.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ h.scratch.wr

theorem mul_relCT (sp : BitVec 32) {c : Ctx} {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a)
    (ha : a ≤ 8) (hb3 : 3 ≤ b) (hb : b ≤ 8)
    (hT : (VG.Taint.check taint τF (.block (mulArgs c o a b)) (.block [])).isSome = true) :
    RelCT isa (Both (MulIn Ex base bytes len args sp c b)) (CrtRt.mul c o a b) (fun _ _ => True) := by
  unfold CrtRt.mul
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  have blk := (RelCT.taint (A := taint) (P := fun f₁ f₂ => ∃ s₁ s₂, Both (MulIn Ex base bytes len args sp c b) s₁ s₂ ∧
      f₁ = allocFrame 36 s₁ ∧ f₂ = allocFrame 36 s₂) τF (fun _ _ ⟨s₁, s₂, ⟨I₁, I₂⟩, q₁, q₂⟩ => by
        obtain ⟨⟨M₁, C₁, -⟩, A₁, e₁⟩ := I₁
        obtain ⟨⟨M₂, C₂, -⟩, A₂, e₂⟩ := I₂
        subst q₁ q₂
        exact agreeF C₁.inp C₂.inp A₁ A₂ (e₁.trans e₂.symm) (by have := C₁.inp.room.low; omega)) hT).wp
    (F₁ := CallOk base bytes len args sp c o a b) (F₂ := CallOk base bytes len args sp c o a b)
    (fun _ _ ⟨s₁, s₂, ⟨I₁, I₂⟩, q₁, q₂⟩ => by
      subst q₁ q₂
      exact ⟨mulArgs_call ho3 ho ha3 ha hb3 hb I₁, mulArgs_call ho3 ho ha3 ha hb3 hb I₂⟩)
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

/-- A multiplication's relation, with each run's `cmul_ok`. -/
theorem mul_both (sp : BitVec 32) {c : Ctx} {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a)
    (ha : a ≤ 8) (hb3 : 3 ≤ b) (hb : b ≤ 8)
    (hT : (VG.Taint.check taint τF (.block (mulArgs c o a b)) (.block [])).isSome = true)
    {P F : State → Prop} (hP : ∀ s, P s → MulIn Ex base bytes len args sp c b s)
    (hw : ∀ s, P s → WP isa (CrtRt.mul c o a b) s F) : RelCT isa (Both P) (CrtRt.mul c o a b) (Both F) :=
  relCT_both ((mul_relCT sp ho3 ho ha3 ha hb3 hb hT).mono (fun _ _ h => ⟨hP _ h.1, hP _ h.2⟩) fun _ _ h => h) hw

end

/-- A loop of `N` iterations, each related from the runs at its count. -/
theorem relCT_countLoop {body : Prog isa} {N : Nat} (hN : 0 < N) (I : Nat → State → Prop)
    (hstep : ∀ j < N, RelCT isa (Both (I j)) body
      (Both fun u => I (j + 1) u ∧ u.zf = some (decide (j + 1 = N)))) :
    RelCT isa (Both (I 0)) (.loop body .ne) (Both (I N)) := by
  refine (VG.RelCT.loop (M := isa) (Q := Both (I N)) (fun n (s t : State) => ∃ j, n = N - j ∧ j < N ∧ Both (I j) s t)
    (fun n => ?_) N).mono (fun _ _ h => ⟨0, by omega, hN, h⟩) fun _ _ h => h
  refine VG.RelCT.exists_ (M := isa) (P := fun j (s t : State) => n = N - j ∧ j < N ∧ Both (I j) s t) (fun j => ?_)
  by_cases hj : j < N ∧ n = N - j
  · obtain ⟨hj, rfl⟩ := hj
    refine (hstep j hj).mono (fun _ _ h => h.2.2) ?_
    rintro s t ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩
    have e₁ : isa.eval .ne s = some (!decide (j + 1 = N)) := by show s.zf.map (!·) = _; rw [z₁]; rfl
    have e₂ : isa.eval .ne t = some (!decide (j + 1 = N)) := by show t.zf.map (!·) = _; rw [z₂]; rfl
    refine ⟨e₁.trans e₂.symm, fun h => ?_, fun h => ?_⟩
    · rw [e₁] at h
      have : j + 1 = N := by simpa using h
      exact this ▸ ⟨I₁, I₂⟩
    · rw [e₁] at h
      have : j + 1 ≠ N := by simpa using h
      exact ⟨N - (j + 1), by omega, j + 1, rfl, by omega, I₁, I₂⟩
  · exact VG.RelCT.of_false fun _ _ h => hj ⟨h.2.1, h.1⟩

end VG.Proof.Bignum.X86.CrtRt
