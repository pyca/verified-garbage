module

import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Mul
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # What the timing of the precomputation at a run-time width checks its pieces from

As for public RSA (`PublicRt/TimeBase.lean`): the six arguments above `esp`,
`edi` and `esp` are public (`τA`; `τF` inside the frame of a
multiplication's call), on states whose permissions are narrowed to `pre` and
the working space (`ArgsOk`). Two runs of the square `mul 4 4 4 5` leak the
same trace when each is ready for it (`MulIn`) from the same `esp`
(`mul_relCT`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputeRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both argByte_alloc calleeOf calleeOf_eq rtPub_of callee_pre argAt_alloc
  mulBody_noSp mulArgs_ok mulArg numAt wb nw)

/-- The arguments, `edi` and `esp`. -/
def τA : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 28 }

/-- `τA` in the frame of a multiplication's call. -/
def τF : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 28, stk := [some 36] }

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (s : State) : Prop :=
  (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 28⟩ r

theorem ArgsOk.keep {s t : State} (A : ArgsOk s) {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs := by decide) :
    ArgsOk t :=
  ⟨by rw [K.1 _ sp]; exact A.1, by rw [K.2.2, K.1 _ sp]; exact A.2⟩

theorem τA_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τA s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem agreeA {s₁ s₂ : State} (h₁ : PcIn base bytes len args s₁) (h₂ : PcIn base bytes len args s₂)
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

theorem τF_wf {s : State} (A : ArgsOk s) (low : 36 ≤ (s.gpr .esp).toNat) :
    VG.X86.Taint.Wf τF (allocFrame 36 s) := by
  have f := A.1
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨?_, fun r hr => ?_⟩, fun _ h => (List.not_mem_nil h).elim, ?_, fun p hp => ?_, fun h => absurd h (by decide)⟩
  · show _ + 36 + 28 ≤ _
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

theorem agreeF {s₁ s₂ : State} (h₁ : PcIn base bytes len args s₁) (h₂ : PcIn base bytes len args s₂)
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

theorem taint_both {P F : State → Prop} {c : Prog isa}
    (hag : ∀ s t, P s → P t → VG.X86.Taint.Agree τA s t)
    (hc : VG.Taint.Hint VG.X86.Taint.T) (hT : (VG.Taint.check taint τA c hc).isSome = true)
    (hw : ∀ s, P s → WP isa c s F) : RelCT isa (Both P) c (Both F) :=
  relCT_both (RelCT.taint (A := taint) τA (fun s t h => hag s t h.1 h.2) hT) hw

/-- What the square needs of a run: `PcIn`, the room for calls, the modulus `M`, its inverse and number 4
below it. -/
structure Ready (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (M : Nat) (s : State) : Prop where
  pi : PcIn base bytes len args s
  room : CallRoom (s.gpr .esp) base bytes
  top : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  mod : val32 s.mem base numOff (nw len) = M
  inv : (M * w32 s.mem base invOff + 1) % 2 ^ 32 = 0
  lt : val32 s.mem base (numAt len 4) (nw len) < M

/-- What a run of the square needs: `Ready`, the arguments apart and `esp`. -/
def MulIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  (∃ M, Ready base bytes len args M s) ∧ ArgsOk s ∧ s.gpr .esp = sp

/-- The state of the call: the callee's precondition, its arguments and the regions it is given. -/
def CallOk (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (g : State) : Prop :=
  (Proof.Rsa.MontMul.mulContract abi 56).pre (calleeOf g base bytes) ∧ g.gpr .esp = sp - BitVec.ofNat 32 36 ∧
    (∀ i < 9, arg (calleeOf g base bytes) i = callArg (BitVec.ofNat 32 base.toNat) (args 5)
      (Spec.Rsa.modulusWords len) numOff invOff (numAt len 5) (numAt len 4) (numAt len 4) (numAt len 4) i) ∧
    (⟨(g.gpr .esp).setWidth 64, 36⟩ : Region) ∈ g.wr ∧ (⟨base, bytes⟩ : Region) ∈ g.wr

theorem mulArgs_call {sp : BitVec 32} {s : State} (I : MulIn base bytes len args sp s) :
    WP isa (.block (mulArgs 4 4 4 5)) (allocFrame 36 s) (CallOk base bytes len args sp) := by
  obtain ⟨⟨M, C⟩, -, hsp⟩ := I
  have h := C.pi
  have R := C.room
  have low := R.low
  have hsp' := (s.gpr .esp).isLt
  have nwr := h.scratch.nowrap
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  refine WP.mono (mulArgs_ok (f := allocFrame 36 s) (len := len) (o := 4) (a := 4) (b := 4) (wl := 5)
    (argAt_alloc h.width) (argAt_alloc (h.stack 5 (by decide)).readSrc) h.upper (by omega) (by omega)
    (by omega) (by rw [fEsp, VG.X86.sub_toNat (by omega)]; omega)
    (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)) fun g ⟨Kg, Fg, Rg⟩ => ?_
  have gEsp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by rw [Kg.1 _ (by decide), fEsp]
  have hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem := by
    have := Fg; rwa [fEsp, allocFrame_mem] at this
  have hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      callArg (s.gpr .edi) (args 5) (Spec.Rsa.modulusWords len) numOff invOff (numAt len 5) (numAt len 4)
        (numAt len 4) (numAt len 4) i := by
    intro i hi; rw [Kg.1 _ (by decide), Rg i hi, mulArg_eq, allocFrame_gpr _ _ (by decide)]
  have edi : s.gpr .edi = BitVec.ofNat 32 base.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [h.edi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (h.fits (j := 0) (by decide)).1; have := VG.Proof.Bignum.X86.PublicRt.wb_ge h.lower; omega)]
  refine ⟨callee_pre (callee_abi h.scratch h.hbytes R h.offs gEsp hFg hread (by rw [C.mod]; exact C.inv)
    (by rw [C.mod]; exact C.lt)) R gEsp, by rw [gEsp, hsp], fun i hi => ?_, ?_, ?_⟩
  · rw [callee_arg (base := base) (bytes := bytes) low gEsp hread hi, edi]
  · rw [Kg.2.2, allocFrame_wr, gEsp]; exact List.mem_cons_self ..
  · rw [Kg.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ h.scratch.wr

theorem mul_relCT (sp : BitVec 32)
    (hT : (VG.Taint.check taint τF (.block (mulArgs 4 4 4 5)) (.block [])).isSome = true) :
    RelCT isa (Both (MulIn base bytes len args sp)) (PublicRt.mul 4 4 4 5) (fun _ _ => True) := by
  unfold PublicRt.mul
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  have blk := (RelCT.taint (A := taint) (P := fun f₁ f₂ => ∃ s₁ s₂, Both (MulIn base bytes len args sp) s₁ s₂ ∧
      f₁ = allocFrame 36 s₁ ∧ f₂ = allocFrame 36 s₂) τF (fun _ _ ⟨s₁, s₂, ⟨I₁, I₂⟩, q₁, q₂⟩ => by
        obtain ⟨⟨M₁, C₁⟩, A₁, e₁⟩ := I₁
        obtain ⟨⟨M₂, C₂⟩, A₂, e₂⟩ := I₂
        subst q₁ q₂
        exact agreeF C₁.pi C₂.pi A₁ A₂ (e₁.trans e₂.symm) (by have := C₁.room.low; omega)) hT).wp
    (F₁ := CallOk base bytes len args sp) (F₂ := CallOk base bytes len args sp)
    (fun _ _ ⟨s₁, s₂, ⟨I₁, I₂⟩, q₁, q₂⟩ => by
      subst q₁ q₂
      exact ⟨mulArgs_call I₁, mulArgs_call I₂⟩)
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

end

end VG.Proof.Bignum.X86.PrecomputeRt
