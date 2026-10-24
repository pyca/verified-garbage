module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.MillerRabin.Equality32
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # A runtime comparison accumulates every native-word difference -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop count1_zf ptr4)

def equalBody : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .alu .xor .eax (.mem (at_ .ecx 0)),
    .alu .or .ebx (.reg .eax), .alu .add .ebp (.imm 4), .alu .add .ecx (.imm 4),
    .alu .sub .esi (.imm 1)]

theorem equalLoop_ok {s : State} {W : Addr} {L x y N : Nat} (hw : Ws s W L)
    (positive : 0 < N) (aFit : x + 4 * N ≤ L) (bFit : y + 4 * N ≤ L)
    (aPtr : PtrAt s W .ebp x) (bPtr : PtrAt s W .ecx y)
    (count : (s.gpr .esi).toNat = N) (zero : s.gpr .ebx = 0#32) :
    WP isa (.loop (.block equalBody) .ne) s fun t =>
      t.mem = s.mem ∧ t.gpr .ebx = xorWords s.mem W x y N ∧
      Keeps [.eax, .ebx, .ebp, .ecx, .esi] s t := by
  refine WP.mono (countLoop positive (fun i t => Keeps [.eax, .ebx, .ebp, .ecx, .esi] s t ∧
    PtrAt t W .ebp (x + 4 * i) ∧ PtrAt t W .ecx (y + 4 * i) ∧
    (t.gpr .esi).toNat = N - i ∧ t.mem = s.mem ∧ t.gpr .ebx = xorWords s.mem W x y i) ?_
    ⟨Keeps.refl _ _, by simpa using aPtr, by simpa using bPtr, by simpa using count, rfl, zero⟩)
    fun t ⟨K, _, _, _, M, V⟩ => ⟨M, V, K⟩
  rintro i t index ⟨K, bp, cx, countI, M, V⟩
  have ht := hw.of_keeps K
  unfold equalBody
  refine wp_movS (readSrc_ptr ht bp (d := 0) (by omega)) fun a A _ => ?_
  have cxA : PtrAt a W .ecx (y + 4 * i) := by rw [PtrAt, A.other .ecx (by decide)]; exact cx
  refine wp_logicS (.inr rfl) (readSrc_ptr (ht.of_keeps A.keeps) cxA (d := 0) (by omega)) fun b B => ?_
  refine wp_orS rfl fun c C => ?_
  refine wp_addS rfl fun d D _ => wp_addS rfl fun e E _ => wp_subZ rfl fun u U Z => WP.block_nil ?_
  have esiE : e.gpr .esi = t.gpr .esi := by
    rw [E.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide),
      B.other .esi (by decide), A.other .esi (by decide)]
  obtain ⟨nextCount, last⟩ := count1_zf countI index
  refine ⟨⟨(((((K.widen A.keeps).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).widen U.keeps,
    ?_, ?_, by rw [U.gpr, esiE]; exact nextCount, ?_, ?_⟩, by rw [Z, esiE, last]⟩
  · rw [PtrAt, U.other .ebp (by decide), E.other .ebp (by decide), D.gpr,
      C.other .ebp (by decide), B.other .ebp (by decide), A.other .ebp (by decide)]
    exact ptr4 bp
  · rw [PtrAt, U.other .ecx (by decide), E.gpr, D.other .ecx (by decide),
      C.other .ecx (by decide), B.other .ecx (by decide), A.other .ecx (by decide)]
    exact ptr4 cx
  · rw [U.mem, E.mem, D.mem, C.mem, B.mem, A.mem, M]
  · rw [U.other .ebx (by decide), E.other .ebx (by decide), D.other .ebx (by decide),
      C.gpr, B.other .ebx (by decide), A.other .ebx (by decide), V,
      B.gpr, A.gpr, A.mem, M, Nat.add_zero, Nat.add_zero, xorWords_succ]
    rfl

end VG.Proof.MillerRabin.X86
