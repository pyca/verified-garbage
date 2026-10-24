module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyChoice
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! One record either caps the exponent and stops, or advances without changing memory. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def recordClobbers : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11]

theorem policyStep_ok {s : State} {B src rec : Addr} {Z k N n : Nat} {dom : List Byte} {g : Policy.Group}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (source : Source src dom s) (record : PolicyRecordAt B rec g s)
 (shape : dom.length=2*k ∨ dom.length=3*k) (positive : 0<k) (size : k<2^28)
 (domain : word s.mem B (8*sDom)=src) (length : word s.mem B (8*sDL)=BitVec.ofNat 64 dom.length)
 (keyLength : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (width : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (fit : N<2^64)
 (pointer : s.gpr .x4=rec) (count : s.gpr .x7=BitVec.ofNat 64 n) (countPositive : 0<n) :
 WP isa Policy.record s fun t =>
 (t.mem=if k=g.len ∧ dom=g.domain.take dom.length then
  s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N g.bits)) else s.mem) ∧
 (t.gpr .x7=BitVec.ofNat 64 (if k=g.len ∧ dom=g.domain.take dom.length then 0 else n-1)) ∧
 t.gpr .x4=off rec (8+3*g.len) ∧ Keep recordClobbers s t := by
 unfold Policy.record
 rw [WP.seq_iff]
 refine WP.mono (policyRecordHead scratch room base keyLength pointer record.readLen record.readBits
  record.length record.bits record.lenFit record.bitsFit) ?_
 rintro a ⟨⟨pointerA,capA,testA,memA⟩,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (policyChoice_ok (scratch.congr restA.wr) room
  ((restA.gpr .x0 (by decide)).trans base) (source.of_mem memA restA)
  (record.after_mem memA restA) shape positive size (memA ▸ domain) (memA ▸ length)
  (memA ▸ width) fit pointerA capA testA) ?_
 rintro b ⟨memB,countB,restB⟩
 let matched := k=g.len ∧ dom=g.domain.take dom.length
 have mem : b.mem=if matched then
  s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N g.bits)) else s.mem := by rw [memB,memA]
 have lengthB : b.mem.readW rec 32=BitVec.ofNat 32 g.len := by
  rw [mem]
  split_ifs
  · have frame : Outside B (8*sBits) 8 s.mem
      (s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N g.bits))) := writeW_outside _ _ _ (by decide)
    exact (Mem.readW_congr fun i hi => frame _ (Or.inr (record.separate i hi))).trans record.length
  · exact record.length
 have countValue : b.gpr .x7=BitVec.ofNat 64 (if matched then 1 else n) := by
  rw [countB,restA.gpr .x7 (by decide),count]
  split_ifs <;> rfl
 have countPos : 0<(if matched then 1 else n) := by split_ifs <;> omega
 have rest := restA.trans restB
 refine WP.mono (policyRecordTail ((restB.gpr .x4 (by simp [choiceClobbers])).trans pointerA)
  countValue (by rw [rest.rd,rest.wr];exact record.readLen) lengthB record.lenFit countPos) ?_
 rintro t ⟨⟨pointerT,countT,memT⟩,restT⟩
 refine ⟨memT.trans mem,?_,pointerT,(rest.trans restT).mono (by simp [choiceClobbers,recordClobbers])⟩
 rw [countT]
 change BitVec.ofNat 64 ((if matched then 1 else n)-1)=BitVec.ofNat 64 (if matched then 0 else n-1)
 split_ifs <;> rfl

end VG.Proof.Ffdh.AArch64.Cached
