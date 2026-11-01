module

import VerifiedGarbage.Impl.Bignum.Arm.CombExp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.TCB.Arm.Isa

/-! The running Montgomery power and the fixed public comb controls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest)

structure Power (base : BitVec 32) (len w M g E : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = M
  coprime : Nat.Coprime (2 ^ (64*w)) M
  bound : numAt s.mem (State.addr base) w 6 < M
  value : numAt s.mem (State.addr base) w 6 % M = g^E * 2^(64*w) % M
  one : numAt s.mem (State.addr base) w 7 = 1
  r2 : numAt s.mem (State.addr base) w 4 = 2^(128*w) % M

structure Controls (base source table : BitVec 32) (bytes N : Nat) (s : State) : Prop where
  sourcePtr : s.mem.readW (off (State.addr base) 128) 32 = source
  byteCount : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 bytes
  bitCount : s.mem.readW (off (State.addr base) 136) 32 = BitVec.ofNat 32 N
  spacing : s.mem.readW (off (State.addr base) 204) 32 = BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N)
  tablePtr : s.mem.readW (off (State.addr base) 232) 32 = table

def Counter (base : BitVec 32) (i : Nat) (s : State) : Prop :=
  s.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 i

theorem Controls.after_header {base source table : BitVec 32} {bytes N : Nat} {s t : State}
    (h : Controls base source table bytes N s)
    (header : ∀ d, d+4≤256 → t.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32) :
    Controls base source table bytes N t := by
  exact ⟨(header 128 (by decide)).trans h.sourcePtr, (header 132 (by decide)).trans h.byteCount,
    (header 136 (by decide)).trans h.bitCount, (header 204 (by decide)).trans h.spacing,
    (header 232 (by decide)).trans h.tablePtr⟩

theorem Power.after_y {s t : State} {base : BitVec 32} {len w M g E F : Nat}
    (h : Power base len w M g E s) (ready : ArithmeticReady base len w t)
    (modulus : numAt t.mem (State.addr base) w 0 = M)
    (keeps : Keeps (State.addr base) len w 6 s.mem t.mem)
    (bound : numAt t.mem (State.addr base) w 6 < M)
    (value : numAt t.mem (State.addr base) w 6 % M = g^F * 2^(64*w) % M) :
    Power base len w M g F t := by
  have fits : arrAt w 8 ≤ 8*len := h.ready.width ▸ h.ready.layout.2.2.1
  refine ⟨ready,modulus,h.coprime,bound,value,?_,?_⟩
  · exact (keeps_array_num keeps fits (q:=7)
      (by simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) (by decide)).trans h.one
  · exact (keeps_array_num keeps fits (q:=4)
      (by simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) (by decide)).trans h.r2

theorem Power.of_mem {s t : State} {base : BitVec 32} {len w M g E : Nat} {rs : List Reg}
    (h : Power base len w M g E s) (mem : t.mem=s.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0=base) : Power base len w M g E t := by
  refine ⟨h.ready.of_mem mem rest ptr,?_,h.coprime,?_,?_,?_,?_⟩ <;> rw [mem]
  · exact h.modulus
  · exact h.bound
  · exact h.value
  · exact h.one
  · exact h.r2

theorem Power.after_header {s t : State} {base : BitVec 32} {len w M g E d : Nat} {v : BitVec 32}
    {rs : List Reg} (h : Power base len w M g E s) (lo : 128≤d) (hi : d+4≤256)
    (mem : t.mem=s.mem.writeW (off (State.addr base) d) v) (rest : Rest rs s t)
    (ptr : t.gpr .r0=base) :
    Power base len w M g E t ∧ Frame [⟨State.addr base,8*len⟩] s.mem t.mem := by
  obtain ⟨ready,frame,arrays⟩ := h.ready.after_header lo hi mem rest ptr
  refine ⟨⟨ready,?_,h.coprime,?_,?_,?_,?_⟩,frame⟩
  · rw [arrays 0 (by decide)]; exact h.modulus
  · rw [arrays 6 (by decide)]; exact h.bound
  · rw [arrays 6 (by decide)]; exact h.value
  · rw [arrays 7 (by decide)]; exact h.one
  · rw [arrays 4 (by decide)]; exact h.r2

end VG.Proof.Bignum.Arm.CombExp
