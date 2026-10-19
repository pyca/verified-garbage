module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptAlLoad
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AltLength

/-! # Select one alternative-length candidate with arithmetic masks -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc

theorem alBody_ok {s : State} {k : Nat} (p : Addr)
    (lower : 64 ≤ k) (upper : k ≤ 1024)
    (ptr0 : s.ea ⟨.esi, 0⟩ = p) (ptr1 : s.ea ⟨.esi, 1⟩ = p + 1)
    (read0 : InRegions (s.rd ++ s.wr) p 1) (read1 : InRegions (s.rd ++ s.wr) (p + 1) 1)
    (mask : s.gpr .ebx = BitVec.ofNat 32 (bitMask (k - 11)))
    (limit : s.gpr .ebp = BitVec.ofNat 32 (k - 11)) :
    WP isa (.block alBody) s fun t => t.mem = s.mem ∧
      Keeps [.eax, .edx, .edi, .esi, .ecx] s t ∧
      t.gpr .edi = (let c := candidate k (s.mem p) (s.mem (p + 1))
        if c ≤ k - 11 then BitVec.ofNat 32 c else s.gpr .edi) ∧
      t.gpr .esi = s.gpr .esi + 2 ∧ t.gpr .ecx = s.gpr .ecx - 1 ∧
      t.zf = some (s.gpr .ecx - 1 == 0) := by
  unfold alBody
  rw [WP.block_append_iff]
  refine WP.mono (alLoad_ok p ptr0 ptr1 read0 read1) ?_
  rintro a ⟨Ma, Ka, high, low⟩
  refine wp_addS rfl fun b B _ => ?_
  refine wp_logicS (Or.inl rfl) rfl fun c C => ?_
  have candidateC : c.gpr .eax = BitVec.ofNat 32 (candidate k (s.mem p) (s.mem (p + 1))) := by
    rw [C.gpr, B.gpr, high, low, B.other .ebx (by decide), Ka.1 .ebx (by decide), mask]
    simp only [ite_true, ← BitVec.ofNat_add, ← BitVec.ofNat_and]
    rfl
  refine wp_movS rfl fun d D _ => ?_
  refine wp_subS rfl fun e E _ => ?_
  refine wp_shr (by decide) fun f F _ => ?_
  refine wp_subS rfl fun u U _ => ?_
  have maskU : u.gpr .edx = if candidate k (s.mem p) (s.mem (p + 1)) ≤ k - 11 then BitVec.allOnes 32 else 0 := by
    rw [U.gpr, F.gpr, E.gpr, D.gpr, D.other .eax (by decide), candidateC,
      C.other .ebp (by decide), B.other .ebp (by decide), Ka.1 .ebp (by decide), limit]
    exact le_mask (by omega) (candidate_bound lower upper _ _)
  refine wp_logicS (Or.inr rfl) rfl fun v V => ?_
  refine wp_logicS (Or.inl rfl) rfl fun w W => ?_
  refine wp_logicS (Or.inr rfl) rfl fun x X => ?_
  have ediX : x.gpr .edi = (let c := candidate k (s.mem p) (s.mem (p + 1))
      if c ≤ k - 11 then BitVec.ofNat 32 c else s.gpr .edi) := by
    rw [X.gpr, W.gpr, V.gpr, W.other .edi (by decide), V.other .edi (by decide),
      U.other .edi (by decide), F.other .edi (by decide), E.other .edi (by decide),
      D.other .edi (by decide), C.other .edi (by decide), B.other .edi (by decide), Ka.1 .edi (by decide),
      V.other .edx (by decide), maskU, U.other .eax (by decide), F.other .eax (by decide),
      E.other .eax (by decide), D.other .eax (by decide), candidateC]
    simp only [show ¬AluOp.xor = AluOp.and from by decide, ite_true, ite_false]
    by_cases choose : candidate k (s.mem p) (s.mem (p + 1)) ≤ k - 11
    · simp only [choose, ite_true, BitVec.and_allOnes]
      rw [BitVec.xor_comm (BitVec.ofNat 32 (candidate k (s.mem p) (s.mem (p + 1)))) (s.gpr .edi),
        ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · simp only [choose, ite_false]
      change s.gpr .edi ^^^ ((BitVec.ofNat 32 (candidate k (s.mem p) (s.mem (p + 1))) ^^^ s.gpr .edi) &&& 0#32) = s.gpr .edi
      rw [BitVec.and_zero, BitVec.xor_zero]
  refine wp_addS rfl fun y Y _ => ?_
  refine wp_subi fun t T _ Z => WP.block_nil ?_
  have Kpre : Keeps [.eax, .edx, .edi] a x := (B.keeps.mono (by decide)).trans
    ((C.keeps.mono (by decide)).trans ((D.keeps.mono (by decide)).trans
      ((E.keeps.mono (by decide)).trans ((F.keeps.mono (by decide)).trans
        ((U.keeps.mono (by decide)).trans ((V.keeps.mono (by decide)).trans
          ((W.keeps.mono (by decide)).trans (X.keeps.mono (by decide)))))))))
  have K : Keeps [.eax, .edx, .edi, .esi, .ecx] s t := (Ka.mono (by decide)).trans
    ((Kpre.mono (by decide)).trans ((Y.keeps.mono (by decide)).trans (T.keeps.mono (by decide))))
  have M : t.mem = s.mem := T.mem.trans (Y.mem.trans (X.mem.trans (W.mem.trans (V.mem.trans (U.mem.trans (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans (Ma)))))))))))
  refine ⟨M, K, ?_, ?_, ?_, ?_⟩
  · rw [T.other .edi (by decide), Y.other .edi (by decide), ediX]
  · rw [T.other .esi (by decide), Y.gpr, Kpre.1 .esi (by decide), Ka.1 .esi (by decide)]
  · rw [T.gpr, Y.other .ecx (by decide), Kpre.1 .ecx (by decide), Ka.1 .ecx (by decide)]
  · rw [Y.other .ecx (by decide), Kpre.1 .ecx (by decide), Ka.1 .ecx (by decide)] at Z
    exact Z

end VG.Proof.RsaPkcs1Enc.X86.Dec
