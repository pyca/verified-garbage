module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FermatExponent
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialDivisor
import VerifiedGarbage.Proof.RsaKeyGen.FermatExponent
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The usual RSA exponent needs one whole-word reduction and no general gcd -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FermatExponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.FermatExponent

theorem xor_one {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t .eax (s.gpr .eax ^^^ 1) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .xor .eax (.imm 1) :: is)) s Q :=
  cons (by simp only [exec, execAlu, readSrc, Option.bind_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _))

theorem code_ok (s : State) (p : BitVec 32) (w endOffset : Nat)
    (positive : 0 < w) (lengthBound : 4 * (2 * w) < 2 ^ 32) (fit : p.toNat + 4 * (2 * w) ≤ 2 ^ 32)
    (candidateRead : ∀ i < 2 * w, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) (4 * i)) 4)
    (endRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) endOffset) 4)
    (endValue : s.mem.readW (addr (s.gpr .esp) endOffset) 32 = p + BitVec.ofNat 32 (4 * (2 * w)))
    (ptr : s.gpr .edi = p) :
    WP isa (code endOffset) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (val32 s.mem (p.setWidth 64) 0 (2 * w)) 65537 = 1)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t := by
  unfold code init
  refine WP.seq (wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => wp_movS rfl fun c C _ => WP.block_nil ?_)
  have K : Keeps [.ebx, .esi, .ebp] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  have prime : c.gpr .ebx = 65537#32 := by rw [C.other .ebx (by decide), B.other .ebx (by decide), A.gpr]; rfl
  have inv : c.gpr .esi = 65535#32 := by rw [C.other .esi (by decide), B.gpr]; rfl
  have sp : c.gpr .esp = s.gpr .esp := K.1 .esp (by decide)
  refine WP.seq (WP.mono (Trial.divisor_ok c p w endOffset positive lengthBound fit
    (by intro i index; rw [K.2.1, K.2.2]; exact candidateRead i index)
    (by rw [K.2.1, K.2.2, sp]; exact endRead)
    (by rw [M, sp]; exact endValue) ((K.1 .edi (by decide)).trans ptr) C.gpr
    (by rw [prime]; decide) (by rw [prime]; decide) (by rw [prime]; decide)
    (by rw [prime, inv]; decide +kernel)) fun d ⟨V, Md, Kd⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s d := (K.mono (by decide)).widen Kd
  refine xor_one fun t T => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (Md.trans M), Kall.widen T.keeps⟩
  rw [T.gpr, V, M, prime]
  change BitVec.ofNat 32 (decide (val32 s.mem (p.setWidth 64) 0 (2 * w) % 65537 = 0)).toNat ^^^ 1 = _
  have coprime := VG.Proof.RsaKeyGen.coprime65537 (val32 s.mem (p.setWidth 64) 0 (2 * w))
  by_cases divides : val32 s.mem (p.setWidth 64) 0 (2 * w) % 65537 = 0
  · rw [decide_eq_true divides, decide_eq_false (by omega : ¬ Nat.gcd (val32 s.mem (p.setWidth 64) 0 (2 * w)) 65537 = 1)]
    rfl
  · rw [decide_eq_false divides, decide_eq_true (coprime.mpr divides)]
    rfl

end VG.Proof.RsaKeyGen.X86.FermatExponent
