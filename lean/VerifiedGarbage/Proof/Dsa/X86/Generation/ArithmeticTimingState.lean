module

public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Offset

/-! Public argument bytes persist across the reused RSA arithmetic routines. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt

def arithmeticTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .edi], flags := false, argLen := 16 }

structure ArithmeticFrame (sp : BitVec 32) (args : Nat → Byte) (s : State) : Prop where
  stack : s.gpr .esp = sp
  fits : sp.toNat + 16 ≤ 2 ^ 32
  apart : ∀ r ∈ s.wr, Region.Disjoint ⟨sp.setWidth 64, 16⟩ r
  bytes : ∀ k, 4 ≤ k → k < 16 → s.mem (off (sp.setWidth 64) k) = args k

def ArithmeticPair (base : Addr) (size len count : Nat) (sp : BitVec 32) (args : Nat → Byte)
    (s t : State) : Prop :=
  RtWs Impl.Dsa.X86.Generation.arithmeticLay s base size len count ∧
  RtWs Impl.Dsa.X86.Generation.arithmeticLay t base size len count ∧
  ArithmeticFrame sp args s ∧ ArithmeticFrame sp args t

theorem ArithmeticFrame.after {sp : BitVec 32} {args : Nat → Byte} {s t : State}
    {base : Addr} {size : Nat} {rs : List Reg}
    (h : ArithmeticFrame sp args s) (ws : Rt.Ws s base size)
    (K : Keeps rs s t) (stack : .esp ∉ rs) (F : Outside base 0 size s.mem t.mem) :
    ArithmeticFrame sp args t := by
  refine ⟨(K.1 .esp stack).trans h.stack, h.fits, ?_, ?_⟩
  · intro r hr
    rw [K.2.2] at hr
    exact h.apart r hr
  · intro k lo hi
    rw [F _ (Or.inr ?_), h.bytes k lo hi]
    have sep := h.apart _ ws.wr (off (sp.setWidth 64) k)
      (Offset.contains_base _ (by omega : k + 1 ≤ 16) (by omega))
    change ¬ (ofs base (off (sp.setWidth 64) k) + 1 ≤ size) at sep
    omega

theorem ArithmeticFrame.wf {sp : BitVec 32} {args : Nat → Byte} {s : State}
    (h : ArithmeticFrame sp args s) : VG.X86.Taint.Wf arithmeticTaint s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim,
    fun _ => by rw [h.stack]; exact ⟨h.fits, h.apart⟩,
    fun _ h => (List.not_mem_nil h).elim⟩

theorem ArithmeticFrame.after_key {sp : BitVec 32} {args : Nat → Byte} {s t : State}
    {L : Impl.Rsa.X86.KeyRt.Lay} {base : Addr} {size len count : Nat} {rs : List Reg}
    {js ds : List Nat} (h : ArithmeticFrame sp args s) (ws : RtWs L s base size len count)
    (K : Keeps rs s t) (stack : .esp ∉ rs)
    (F : VG.Proof.Rsa.X86.Keys.Keep base (kw len) js ds s.mem t.mem)
    (arrays : ∀ j ∈ js, j < count) (headers : ∀ d ∈ ds, d + 4 ≤ Impl.Rsa.X86.Keys.hdr) :
    ArithmeticFrame sp args t :=
  h.after ⟨ws.ws.workspace.wr, ws.ws.workspace.nowrap⟩ K stack (keep_outside ws.ws F arrays headers)

theorem ArithmeticFrame.agree {sp : BitVec 32} {args : Nat → Byte} {s t : State}
    {L : Impl.Rsa.X86.KeyRt.Lay} {base : Addr} {size len count : Nat}
    (a : ArithmeticFrame sp args s) (b : ArithmeticFrame sp args t)
    (ws : RtWs L s base size len count) (wt : RtWs L t base size len count) :
    VG.X86.Taint.Agree arithmeticTaint s t := by
  refine ⟨⟨?_, fun h => nomatch h⟩, fun h => absurd rfl h, a.wf, b.wf,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty,
    fun _ => a.stack.trans b.stack.symm, ?_⟩
  · intro r hr
    have mem : r ∈ ([Reg.esp, .edi] : List Reg) := by
      simpa only [arithmeticTaint, RegSet.mem_ofList] using hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact a.stack.trans b.stack.symm
    · exact BitVec.eq_of_toNat_eq (ws.edi.trans wt.edi.symm)
  · intro k lo hi
    simp only [arithmeticTaint, VG.X86.Taint.depth, Nat.zero_add, VG.X86.Taint.argByte]
    change s.mem (off ((s.gpr .esp).setWidth 64) k) = t.mem (off ((t.gpr .esp).setWidth 64) k)
    rw [a.stack, b.stack, a.bytes k lo hi, b.bytes k lo hi]

theorem ArithmeticPair.agree {base : Addr} {size len count : Nat} {sp : BitVec 32} {args : Nat → Byte}
    {s t : State} (h : ArithmeticPair base size len count sp args s t) :
    VG.X86.Taint.Agree arithmeticTaint s t :=
  h.2.2.1.agree h.2.2.2 h.1 h.2.1

end VG.Proof.Dsa.X86.Generation
