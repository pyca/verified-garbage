module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashArgs
import Mathlib.Tactic.Convert

/-! # Each public PRF counter selects its own 32-byte digest slot -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def prfDstArgs (dst : Nat) : List Instr :=
  [.mov .eax (.mem (incoming 21)), .alu .add .eax (.imm (BitVec.ofNat 32 dst)),
    .mov .ecx (.mem (stackAt oI)), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .add .eax (.reg .ecx), .store (stackAt 16) .eax]

theorem prfDstArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s)
    (dst i : Nat) (counter : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 i) :
    WP isa (.block (prfDstArgs dst)) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 16)
        (g.workspace + BitVec.ofNat 32 (dst + 32 * i)) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 16, 4⟩] s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold prfDstArgs incoming stackAt
  refine wp_ldm rfl (h.readArg (by decide : 21 < 23)) fun a A => ?_
  refine wp_addS rfl fun b B _ => ?_
  have Kpre : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Mpre : b.mem = s.mem := B.mem.trans A.mem
  have hb := h.after (by rw [Mpre]; exact Frame.refl _ _) Kpre (Kpre.1 .esp (by decide))
  refine wp_ldm rfl (by
    rw [hb.address (by decide : oI < VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20 + 92)]
    exact hb.inner.read (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) fun c C => ?_
  refine wp_addS rfl fun d D _ => ?_
  refine wp_addS rfl fun e E _ => ?_
  refine wp_addS rfl fun f F _ => ?_
  refine wp_addS rfl fun u U _ => ?_
  refine wp_addS rfl fun v V _ => ?_
  refine wp_addS rfl fun w W _ => ?_
  have Kcalc : Keeps [.eax, .ecx] s w := (Kpre.mono (by decide)).trans
    ((C.keeps.mono (by decide)).trans ((D.keeps.mono (by decide)).trans
      ((E.keeps.mono (by decide)).trans ((F.keeps.mono (by decide)).trans
        ((U.keeps.mono (by decide)).trans ((V.keeps.mono (by decide)).trans (W.keeps.mono (by decide))))))))
  have Mcalc : w.mem = s.mem := W.mem.trans (V.mem.trans (U.mem.trans (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans Mpre))))))
  have hw := h.after (by rw [Mcalc]; exact Frame.refl _ _) Kcalc (Kcalc.1 .esp (by decide))
  refine WP.mono (storeLocal_ok hw .eax (by decide : 16 + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) ?_
  rintro t ⟨ht, M, Ft, Kt⟩
  refine ⟨ht, ?_, by rw [Mcalc] at Ft; exact Ft, Kcalc.trans (Kt.mono (by simp))⟩
  rw [Mcalc, W.gpr, V.other .eax (by decide), U.other .eax (by decide), F.other .eax (by decide),
    E.other .eax (by decide), D.other .eax (by decide), C.other .eax (by decide),
    B.gpr, A.gpr, h.argumentValue (by decide : 21 < 23), V.gpr, U.gpr, F.gpr, E.gpr, D.gpr,
    C.gpr, Mpre, hb.address (by decide : oI < VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20 + 92), counter] at M
  change t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 16)
    ((g.workspace + BitVec.ofNat 32 dst) +
      (((((BitVec.ofNat 32 i + BitVec.ofNat 32 i) + (BitVec.ofNat 32 i + BitVec.ofNat 32 i)) +
      ((BitVec.ofNat 32 i + BitVec.ofNat 32 i) + (BitVec.ofNat 32 i + BitVec.ofNat 32 i))) +
      (((BitVec.ofNat 32 i + BitVec.ofNat 32 i) + (BitVec.ofNat 32 i + BitVec.ofNat 32 i)) +
      ((BitVec.ofNat 32 i + BitVec.ofNat 32 i) + (BitVec.ofNat 32 i + BitVec.ofNat 32 i)))) +
      ((((BitVec.ofNat 32 i + BitVec.ofNat 32 i) + (BitVec.ofNat 32 i + BitVec.ofNat 32 i)) +
      ((BitVec.ofNat 32 i + BitVec.ofNat 32 i) + (BitVec.ofNat 32 i + BitVec.ofNat 32 i))) +
      (((BitVec.ofNat 32 i + BitVec.ofNat 32 i) + (BitVec.ofNat 32 i + BitVec.ofNat 32 i)) +
      ((BitVec.ofNat 32 i + BitVec.ofNat 32 i) + (BitVec.ofNat 32 i + BitVec.ofNat 32 i)))))) at M
  simp only [← BitVec.ofNat_add, BitVec.add_assoc] at M
  convert M using 2 <;> congr 2 <;> omega

end VG.Proof.RsaPkcs1Enc.X86.Dec
