module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.Arm.Isa

/-! The sieve reads the candidate and RSA table and writes only local word 64. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

def sieveRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r10, .r11, .r12]

def sieveLocal (sp : BitVec 32) : Region := ⟨State.addr (sp + 64#32), 4⟩

structure SieveContext (dst base : BitVec 32) (n : Nat) (s : State) : Prop where
  read : ReadContext dst n s
  widthBound : n ≤ 1024
  savedBase : s.mem.readW (State.addr s.sp) 32 = base
  tableFits : base.toNat + (arrAt ((n + 7) / 8) 34 + 4096) ≤ 2 ^ 32
  table : TableData base n s.mem
  tableReadable : ∀ i < 1024, InRegions (s.rd ++ s.wr)
    (off (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i)) 4
  tableStack : ∀ i < 1024, (⟨off (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i), 4⟩ : Region).Disjoint
    ⟨State.addr s.sp, 72⟩
  outputStack : (⟨State.addr dst, n⟩ : Region).Disjoint ⟨State.addr s.sp, 72⟩

theorem sieveLocal_sub {s : State} (stack : Workspace s s.sp 72) :
    (sieveLocal s.sp).Sub ⟨State.addr s.sp, 72⟩ := by
  unfold sieveLocal
  rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
  exact Offset.sub_base _ (by decide)

theorem sieveLocal_separate {s : State} (stack : Workspace s s.sp 72) {d : Nat} (fit : d + 4 ≤ 64) :
    (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint (sieveLocal s.sp) := by
  unfold sieveLocal
  rw [VG.Arm.addr_add (by have := stack.nowrap; omega), VG.Arm.addr_add (by have := stack.nowrap; omega)]
  exact Offset.disjoint _ (.inl fit) (by omega) (by decide)

theorem sieveLocal_frame (s : State) (value : BitVec 32) :
    Frame [sieveLocal s.sp] s.mem (s.mem.writeW (State.addr (s.sp + 64#32)) value) :=
  (Frame.refl [sieveLocal s.sp] s.mem).writeW (r := sieveLocal s.sp) (by simp) value
    (Region.contains_self _ 4)

theorem SieveContext.after_frame {s t : State} {dst base : BitVec 32} {n : Nat} {rs : List Reg}
    (h : SieveContext dst base n s) (changed : Frame [sieveLocal s.sp] s.mem t.mem) (rest : Rest rs s t) :
    SieveContext dst base n t := by
  have stack := h.read.frame.space
  have localSub := sieveLocal_sub stack
  have slots : SavedFrame (readValues dst n) [4, 12] t := h.read.frame.after_frame changed rest (by
    intro d hd r hr
    rw [List.mem_singleton] at hr
    subst r
    exact sieveLocal_separate stack (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega))
  refine ⟨⟨slots, h.read.positive, h.read.countFits, h.read.bufferFits, ?_⟩,
    h.widthBound, ?_, h.tableFits, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [rest.rd, rest.wr]
    exact h.read.readable i hi
  · rw [rest.sp]
    have equal := changed.readW (a := State.addr (s.sp + BitVec.ofNat 32 0)) (w := 32)
      (r := ⟨State.addr (s.sp + BitVec.ofNat 32 0), 4⟩)
      (Region.contains_self _ _) (by
        intro r hr
        rw [List.mem_singleton] at hr
        subst r
        exact sieveLocal_separate stack (by decide : 0 + 4 ≤ 64)) (by decide)
    simp only [BitVec.add_zero] at equal
    exact equal.trans h.savedBase
  · intro i hi
    have equal := changed.readW (a := off (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i)) (w := 32)
      (r := ⟨off (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i), 4⟩)
      (Region.contains_self _ _) (by
        intro r hr
        rw [List.mem_singleton] at hr
        subst r
        exact (h.tableStack i hi).sub_right localSub) (by decide)
    exact (congrArg BitVec.toNat equal).trans (h.table i hi)
  · intro i hi
    rw [rest.rd, rest.wr]
    exact h.tableReadable i hi
  · rw [rest.sp]
    exact h.tableStack
  · rw [rest.sp]
    exact h.outputStack

theorem SieveContext.after_memory {s t : State} {dst base : BitVec 32} {n : Nat} {rs : List Reg}
    (h : SieveContext dst base n s) (memory : t.mem = s.mem) (rest : Rest rs s t) :
    SieveContext dst base n t := h.after_frame (by rw [memory]; exact Frame.refl _ _) rest

theorem SieveContext.bytes_after {s t : State} {dst base : BitVec 32} {n : Nat}
    (h : SieveContext dst base n s) (changed : Frame [sieveLocal s.sp] s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr dst) n := by
  refine rsa_bytes_frame changed (by have := h.read.countFits; omega) ?_
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact h.outputStack.sub_right (sieveLocal_sub h.read.frame.space)

end VG.Proof.Ffdh.Arm.ParameterCandidate
