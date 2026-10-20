module

public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-! # Fixed-address XOR padding byte -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64

def xorByteCode (sc : Reg) (off value : Nat) : List Instr :=
 [.ldrb .x9 sc off,.movz .x .x10 (BitVec.ofNat 16 value) 0,
  .logic .eor .x .x9 .x9 .x10,.strb .x9 sc off]

theorem xorByte_ok {s : State} {sc : Reg} {off value : Nat}
    (h9 : sc≠.x9) (h10 : sc≠.x10) (ho : off<4096)
    (hw : InRegions s.wr (s.gpr sc+BitVec.ofNat 64 off) 1) :
    WP isa (.block (xorByteCode sc off value)) s fun t=>Keep [.x9,.x10] s t ∧
      t.mem=s.mem.writeW (s.gpr sc+BitVec.ofNat 64 off)
        (s.mem (s.gpr sc+BitVec.ofNat 64 off) ^^^ BitVec.ofNat 8 value) := by
  unfold xorByteCode
  refine wp_ldrb ho rfl (by obtain ⟨r,hr,hc⟩:=hw; exact ⟨r,List.mem_append_right _ hr,hc⟩) fun a ha ea=>wp_movz fun b hb eb=>wp_eor fun c hc ec=>?_
  have hh := (ha.trans hb).trans hc
  refine wp_strb ho (by rw [hh.get sc (by simp [h9,h10])]) (by rw [hh.wr]; exact hw) fun t ht=>wp_nil ?_
  refine ⟨(hh.keep.trans ht.keep).mono (by simp),?_⟩
  rw [ht.mem,ec,hb.get .x9,ea,eb,hc.mem,hb.mem,ha.mem]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem stateAt_writeXor {m : Mem} {p : Addr} {j : Nat} {b : Byte} (hj : j<200) :
    Spec.Sha3.stateAt (m.writeW (p+BitVec.ofNat 64 j) (m (p+BitVec.ofNat 64 j) ^^^ b)) p=
      Proof.Sha3.xorByte (Spec.Sha3.stateAt m p) j b := by
  apply Proof.Sha3.stateAt_xorByte hj
  · simp only [Proof.Sha3.writeW8_apply,↓reduceIte]
  · intro i hi hn
    simp only [Proof.Sha3.writeW8_apply,Proof.Sha3.ne_of_lt200 hi hj hn,ite_false]

end VG.Proof.MlKem.AArch64.FixedHash
