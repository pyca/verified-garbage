module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.HeaderRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Header
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The run-time header writes `Header.code`'s memory for the width at byte 4 -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HeaderRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.HeaderRt
open VG.Proof.RsaKeyGen.X86.Header (headerMemory pointerMemory storePair_ok)
open VG.Impl.Mont.X86 (sc)

theorem pointers_ok {w : Nat} (k : Nat) : ∀ (n : Nat) {s : State} {base : Addr} {size : Nat}
    (_ : Scr s base size) (_ : 64 + 8 * (k + n) ≤ size) (_ : s.gpr .edx = 0#32)
    (_ : s.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (slot w k))
    (_ : s.gpr .ecx = BitVec.ofNat 32 (stride w)),
    WP isa (.block ((List.range' k n).flatMap pointer)) s fun t =>
      t.mem = (List.range' k n).foldl (pointerMemory base (s.gpr .edi) w) s.mem ∧ Keeps [.eax] s t
  | 0, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Keeps.refl _ _⟩
  | n + 1, s, base, size, scratch, fit, zero, eax, ecx => by
    rw [List.range'_succ, List.flatMap_cons]
    unfold pointer
    refine WP.block_append (WP.block_append (WP.mono (storePair_ok scratch (offset := 64 + 8 * k) (by omega))
      fun a ⟨M, _, K⟩ => ?_))
    refine wp_addS rfl fun b B _ => WP.block_nil ?_
    have Kb : Keeps [.eax] s b := (K.mono (by decide)).widen B.keeps
    have ih := pointers_ok (w := w) (k + 1) n (s := b) (scratch.of_keeps Kb (by decide)) (by omega)
      (by rw [Kb.1 .edx (by decide)]; exact zero)
      (by
        rw [B.gpr, K.1 .eax (by decide), K.1 .ecx (by decide), eax, ecx, BitVec.add_assoc, ← BitVec.ofNat_add, Kb.1 .edi (by decide)]
        congr 2
        simp only [slot, stride, Nat.succ_mul]
        omega)
      (by rw [Kb.1 .ecx (by decide)]; exact ecx)
    refine WP.mono ih fun t ⟨Mt, Kt⟩ => ⟨?_, Kb.trans Kt⟩
    rw [Mt, Kb.1 .edi (by decide), B.mem, M, eax, zero, List.foldl_cons]
    rfl

theorem code_ok {s : State} {base : Addr} {size w : Nat} (scratch : Scr s base size) (fit : 256 ≤ size)
    (bound : w ≤ 128) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block code) s fun t =>
      t.mem = headerMemory base (s.gpr .edi) w s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  unfold code
  simp only [List.cons_append]
  refine wp_movS (readSrc_sc scratch (d := 4) (by omega)) fun a A _ => wp_movS rfl fun b B _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun c C => wp_movS rfl fun d D _ => ?_
  have Kd : Keeps [.eax, .ecx, .edx] s d :=
    (((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps
  have zero : d.gpr .edx = 0#32 := D.gpr
  have width : d.gpr .eax = BitVec.ofNat 32 w := by
    rw [D.other .eax (by decide), C.gpr, B.gpr, A.gpr, len]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have Md : d.mem = s.mem := by rw [D.mem, C.mem, B.mem, A.mem]
  show WP isa (.block ([.store (sc 48) .eax, .store (sc (48 + 4)) .edx] ++ _)) d _
  refine WP.block_append (WP.mono (storePair_ok (scratch.of_keeps Kd (by decide)) (offset := 48) (by omega))
    fun e ⟨Me, _, Ke⟩ => ?_)
  refine wp_addS rfl fun f F _ => wp_movS rfl fun h H _ => ?_
  have Kh : Keeps [.eax, .ecx, .edx] s h := ((Kd.widen Ke).widen F.keeps).widen H.keeps
  have strideF : f.gpr .ecx = BitVec.ofNat 32 (stride w) := by
    rw [F.gpr, Ke.1 .ecx (by decide), D.other .ecx (by decide), C.other .ecx (by decide), B.other .ecx (by decide),
      A.gpr, len]
    apply BitVec.eq_of_toNat_eq
    have sixteen : (16 : BitVec 32).toNat = 16 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, stride, sixteen]
    omega
  have zeroH : h.gpr .edx = 0#32 := by
    rw [H.other .edx (by decide), F.other .edx (by decide), Ke.1 .edx (by decide)]; exact zero
  show WP isa (.block ([.store (sc 224) .eax, .store (sc (224 + 4)) .edx] ++ _)) h _
  refine WP.block_append (WP.mono (storePair_ok (scratch.of_keeps Kh (by decide)) (offset := 224) (by omega))
    fun i ⟨Mi, _, Ki⟩ => ?_)
  refine wp_movS rfl fun j J _ => wp_addS rfl fun l Lr _ => ?_
  have Kl : Keeps [.eax, .ecx, .edx] s l := ((Kh.widen Ki).widen J.keeps).widen Lr.keeps
  have edi : l.gpr .edi = s.gpr .edi := Kl.1 .edi (by decide)
  have eaxL : l.gpr .eax = l.gpr .edi + BitVec.ofNat 32 (slot w 0) := by
    rw [Lr.gpr, J.gpr, edi, Ki.1 .edi (by decide), Kh.1 .edi (by decide),
      show slot w 0 = 256 by simp [slot, VG.Impl.Bignum.hdrBytes]]
    rfl
  have ecxL : l.gpr .ecx = BitVec.ofNat 32 (stride w) := by
    rw [Lr.other .ecx (by decide), J.other .ecx (by decide), Ki.1 .ecx (by decide), H.other .ecx (by decide)]
    exact strideF
  have zeroL : l.gpr .edx = 0#32 := by
    rw [Lr.other .edx (by decide), J.other .edx (by decide), Ki.1 .edx (by decide)]; exact zeroH
  rw [List.range_eq_range']
  refine WP.mono (pointers_ok 0 8 (scratch.of_keeps Kl (by decide)) (by omega) zeroL eaxL ecxL)
    fun t ⟨Mt, Kt⟩ => ⟨?_, Kl.widen Kt⟩
  have strideH : h.gpr .eax = BitVec.ofNat 32 (stride w) := by rw [H.gpr]; exact strideF
  rw [Mt, edi, Lr.mem, J.mem, Mi, strideH, zeroH, H.mem, F.mem, Me, width, zero, Md]
  unfold headerMemory
  rw [List.range_eq_range']

end VG.Proof.RsaKeyGen.X86.HeaderRt
