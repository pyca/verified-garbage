module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified

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
    (argAt_alloc (h.stack 9 (by decide)).readSrc) h.upper (by omega) (by omega) (by omega)
    (by rw [fEsp, VG.X86.sub_toNat (by omega)]; omega)
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
    rw [h.scratch.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (h.fits (j := 0) (by decide)).1; simp only [numAt, numOff] at this; omega)]
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
        exact agreeF E₁.pi E₂.pi A₁ A₂ (e₁.trans e₂.symm) (by have := E₁.room.low; omega)) hT).wp
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
