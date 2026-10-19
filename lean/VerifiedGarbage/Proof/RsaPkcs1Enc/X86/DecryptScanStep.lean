module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Enc.ByteZero
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Word32
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps

/-! # Scan one encoded-message byte without branching on its value -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def zbit (b : Byte) : BitVec 32 := BitVec.ofNat 32 (decide (b = 0)).toNat

theorem scanBody_ok (s : State) (p : Addr)
    (ptr : s.ea ⟨.esi, 0⟩ = p) (read : InRegions (s.rd ++ s.wr) p 1) :
    WP isa (.block scanBody) s fun t =>
      t.mem = s.mem ∧
      t.gpr .ebp = s.gpr .ebp ||| (-((s.gpr .ebx ^^^ 1) &&& zbit (s.mem p)) &&& s.gpr .edi) ∧
      t.gpr .ebx = s.gpr .ebx ||| zbit (s.mem p) ∧
      t.gpr .edi = s.gpr .edi + 1 ∧ t.gpr .esi = s.gpr .esi + 1 ∧
      t.gpr .ecx = s.gpr .ecx - 1 ∧ t.zf = some (s.gpr .ecx - 1 == 0) ∧
      Keeps [.eax, .edx, .ebp, .ebx, .edi, .esi, .ecx] s t := by
  unfold scanBody negate
  refine wp_loadByte ptr read fun a A => ?_
  refine wp_subS rfl fun b B _ => ?_
  refine wp_shr (by decide) fun c C _ => ?_
  have Z : c.gpr .eax = zbit (s.mem p) := by
    rw [C.gpr, B.gpr, A.gpr, VG.Proof.RsaPkcs1Enc.byte_zero32]
    rfl
  refine wp_movS rfl fun d D _ => ?_
  refine wp_logicS (Or.inr rfl) rfl fun e E => ?_
  refine wp_logicS (Or.inl rfl) rfl fun f F => ?_
  refine wp_logicS (Or.inr rfl) rfl fun g G => ?_
  refine wp_addS rfl fun h H _ => ?_
  have mask : h.gpr .edx = -((s.gpr .ebx ^^^ 1) &&& zbit (s.mem p)) := by
    rw [H.gpr, G.gpr, F.gpr, E.gpr, D.gpr,
      E.other .eax (by decide), D.other .eax (by decide), Z,
      C.other .ebx (by decide), B.other .ebx (by decide), A.other .ebx (by decide)]
    simp only [ite_true]
    exact VG.Proof.RsaPkcs1Enc.Word32.negate_eq _
  refine wp_logicS (Or.inl rfl) rfl fun i I => ?_
  have Kpre : Keeps [.eax, .edx] s i :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans
      ((C.keeps.mono (by decide)).trans ((D.keeps.mono (by decide)).trans
        ((E.keeps.mono (by decide)).trans ((F.keeps.mono (by decide)).trans
          ((G.keeps.mono (by decide)).trans ((H.keeps.mono (by decide)).trans (I.keeps.mono (by decide)))))))))
  have MI : i.gpr .edx = -((s.gpr .ebx ^^^ 1) &&& zbit (s.mem p)) &&& s.gpr .edi := by
    rw [I.gpr, mask, H.other .edi (by decide), G.other .edi (by decide), F.other .edi (by decide),
      E.other .edi (by decide), D.other .edi (by decide), C.other .edi (by decide),
      B.other .edi (by decide), A.other .edi (by decide)]
    rfl
  have ZI : i.gpr .eax = zbit (s.mem p) := by
    rw [I.other .eax (by decide), H.other .eax (by decide), G.other .eax (by decide),
      F.other .eax (by decide), E.other .eax (by decide), D.other .eax (by decide), Z]
  refine wp_orS rfl fun j J => ?_
  refine wp_orS rfl fun k K => ?_
  refine wp_addS rfl fun l L _ => ?_
  refine wp_addS rfl fun m M _ => ?_
  refine wp_subi fun t T _ Zt => WP.block_nil ?_
  have Ktail : Keeps [.ebp, .ebx, .edi, .esi, .ecx] i t :=
    (J.keeps.mono (by decide)).trans ((K.keeps.mono (by decide)).trans
      ((L.keeps.mono (by decide)).trans ((M.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (Kpre.mono (by decide)).trans (Ktail.mono (by decide))⟩
  · rw [T.mem, M.mem, L.mem, K.mem, J.mem, I.mem, H.mem, G.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
  · rw [T.other .ebp (by decide), M.other .ebp (by decide), L.other .ebp (by decide),
      K.other .ebp (by decide), J.gpr, MI, Kpre.1 .ebp (by decide)]
  · rw [T.other .ebx (by decide), M.other .ebx (by decide), L.other .ebx (by decide), K.gpr,
      J.other .ebx (by decide), J.other .eax (by decide), ZI, Kpre.1 .ebx (by decide)]
  · rw [T.other .edi (by decide), M.other .edi (by decide), L.gpr,
      K.other .edi (by decide), J.other .edi (by decide), Kpre.1 .edi (by decide)]
  · rw [T.other .esi (by decide), M.gpr, L.other .esi (by decide),
      K.other .esi (by decide), J.other .esi (by decide), Kpre.1 .esi (by decide)]
  · rw [T.gpr, M.other .ecx (by decide), L.other .ecx (by decide),
      K.other .ecx (by decide), J.other .ecx (by decide), Kpre.1 .ecx (by decide)]
  · rw [Zt, M.other .ecx (by decide), L.other .ecx (by decide),
      K.other .ecx (by decide), J.other .ecx (by decide), Kpre.1 .ecx (by decide)]

end VG.Proof.RsaPkcs1Enc.X86.Dec
