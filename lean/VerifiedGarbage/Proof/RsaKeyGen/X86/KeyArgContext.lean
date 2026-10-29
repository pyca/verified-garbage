module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateArgs
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset

/-! # Workspace header writes leave every original key argument readable -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

def argsRegion (p : BitVec 32) : Region := ⟨(p + 20#32).setWidth 64, 72⟩

/-- `StkOk` with 52 bytes: room below `sp` for a call of `vg_rsa_keygen_inverse` (twelve bytes
of arguments, its return address and the 36 bytes its contract keeps apart from the workspace). -/
def DeepStk (sp : BitVec 32) (base : Addr) (size : Nat) : Prop :=
  52 ≤ sp.toNat ∧ sp.toNat + 92 ≤ 2 ^ 32 ∧ (sp.toNat ≤ base.toNat ∨ base.toNat + size + 52 ≤ sp.toNat)

structure Context (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base size
  header : 72 ≤ size
  sp : s.gpr .esp = p
  fit : p.toNat + 92 ≤ 2 ^ 32
  separate : (argsRegion p).Disjoint ⟨base, size⟩
  read : ∀ i < 18, readSrc s (.mem (arg i)) = some (inputs i)
  deep : DeepStk p base size

theorem Context.address {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {i : Nat} (index : i < 18) :
    s.ea (arg i) = off (argsRegion p).base (4 * i) := by
  change addr (s.gpr .esp) (20 + 4 * i) = _
  rw [C.sp, addr_eq (by have := C.fit; omega)]
  have start : (p + 20#32).setWidth 64 = off (p.setWidth 64) 20 := addr_eq (by have := C.fit; omega)
  change off (p.setWidth 64) (20 + 4 * i) = off ((p + 20#32).setWidth 64) (4 * i)
  rw [start]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]

theorem Context.keep {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s t : State} {rs : List Reg}
    (C : Context base size p inputs s) (K : Keeps rs s t) (F : Frame [⟨base, size⟩] s.mem t.mem)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) :
    Context base size p inputs t := by
  have spT : t.gpr .esp = p := (K.1 .esp esp).trans C.sp
  have C0 : Context base size p inputs t := by
    refine ⟨C.scratch.of_keeps K edi esp, C.header, spT, C.fit, C.separate, ?_, C.deep⟩
    intro i index
    have eaT : t.ea (arg i) = s.ea (arg i) := by
      change addr (t.gpr .esp) _ = addr (s.gpr .esp) _
      rw [K.1 .esp esp]
    have memory : t.mem.readW (s.ea (arg i)) 32 = s.mem.readW (s.ea (arg i)) 32 := by
      rw [C.address index]
      exact F.readW (r := argsRegion p)
        (Offset.contains_base _ (by change 4 * i + 4 ≤ 72; omega) (by omega : 4 * i < 2 ^ 64))
        (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact C.separate) (by decide)
    have same : readSrc t (.mem (arg i)) = readSrc s (.mem (arg i)) := by
      show t.load32 (t.ea (arg i)) = s.load32 (s.ea (arg i))
      simp only [State.load32, eaT, K.2.1, K.2.2, memory]
    exact same.trans (C.read i index)
  exact C0

/-- The arguments lie above the stack a call uses. -/
theorem args_below_disjoint {p : BitVec 32} (low : 52 ≤ p.toNat) (fit : p.toNat + 92 ≤ 2 ^ 32) :
    (argsRegion p).Disjoint (below p 52) := by
  intro x hx hb
  simp only [argsRegion, Region.Contains] at hx hb
  have e₁ : ((p + 20#32).setWidth 64).toNat = p.toNat + 20 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have e₂ : ((p - 52#32).setWidth 64).toNat = p.toNat - 52 := by
    rw [BitVec.toNat_setWidth, sub_toNat low]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub, e₁] at hx
  rw [BitVec.toNat_sub, e₂] at hb
  have := x.isLt
  omega

/-- `Context.keep`, for code that also writes the stack below `esp` that a call uses. -/
theorem Context.keepBelow {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s t : State}
    {rs : List Reg} (C : Context base size p inputs s) (K : Keeps rs s t)
    (F : Frame [⟨base, size⟩, below p 52] s.mem t.mem)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) :
    Context base size p inputs t := by
  have spT : t.gpr .esp = p := (K.1 .esp esp).trans C.sp
  refine ⟨C.scratch.of_keeps K edi esp, C.header, spT, C.fit, C.separate, ?_, C.deep⟩
  intro i index
  have eaT : t.ea (arg i) = s.ea (arg i) := by
    change addr (t.gpr .esp) _ = addr (s.gpr .esp) _
    rw [K.1 .esp esp]
  have memory : t.mem.readW (s.ea (arg i)) 32 = s.mem.readW (s.ea (arg i)) 32 := by
    rw [C.address index]
    refine F.readW (r := argsRegion p)
      (Offset.contains_base _ (by change 4 * i + 4 ≤ 72; omega) (by omega : 4 * i < 2 ^ 64)) ?_ (by decide)
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact C.separate
    · exact args_below_disjoint C.deep.1 C.fit
  have same : readSrc t (.mem (arg i)) = readSrc s (.mem (arg i)) := by
    show t.load32 (t.ea (arg i)) = s.load32 (s.ea (arg i))
    simp only [State.load32, eaT, K.2.1, K.2.2, memory]
  exact same.trans (C.read i index)

end VG.Proof.RsaKeyGen.X86.KeyArgs
