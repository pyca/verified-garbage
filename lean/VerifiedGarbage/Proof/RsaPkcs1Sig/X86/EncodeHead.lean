module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeBytes

/-! # Start the encoding and derive the padding-string count -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86

theorem ofNat_sub3 {k n : Nat} (bound : n + 11 ≤ k) (hk : k ≤ 1024) :
    BitVec.ofNat 32 k - BitVec.ofNat 32 n - 3 = BitVec.ofNat 32 (k - n - 3) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : (3 : BitVec 32).toNat = 3 := rfl
  rw [this]
  omega

theorem head_ok {s0 s : State} {k n : Nat} (buf : Buf s0 k) (hk : k ≤ 1024)
    (bound : n + 11 ≤ k) (h : W s0 [] s)
    (length : s.gpr .ecx = BitVec.ofNat 32 k) (info : s.gpr .ebx = BitVec.ofNat 32 n) :
    WP isa (.block head) s fun t => W s0 [0x00, 0x01] t ∧ t.gpr .eax = 0xff ∧
      t.gpr .ebx = BitVec.ofNat 32 (k - n - 3) ∧ Keeps [.eax, .edi, .ebx] s t := by
  unfold head
  refine WP.block_append (WP.mono (putBytes_ok buf [0x00, 0x01] (by simp; omega) h)
    fun u ⟨hu, ku⟩ => ?_)
  unfold headTail
  refine wp_movS rfl fun v V _ => ?_
  refine wp_subS rfl fun w U _ => ?_
  refine wp_subS rfl fun x X _ => ?_
  refine wp_movS rfl fun y Y _ => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  have rest : Keeps [.eax, .ebx] u t :=
    ((((V.keeps.mono (by decide)).widen U.keeps).widen X.keeps).widen Y.keeps).widen T.keeps
  have mem : t.mem = u.mem := T.mem.trans (Y.mem.trans (X.mem.trans (U.mem.trans V.mem)))
  have cursor : t.gpr .edi = u.gpr .edi := rest.1 _ (by decide)
  refine ⟨hu.after rest (by decide) mem cursor, T.gpr, ?_,
    (ku.mono (by decide)).trans (rest.mono (by decide))⟩
  rw [T.other .ebx (by decide), Y.gpr, X.gpr, U.gpr, V.gpr,
    V.other .ebx (by decide), ku.1 .ecx (by decide), ku.1 .ebx (by decide), length, info]
  exact ofNat_sub3 bound hk

end VG.Proof.RsaPkcs1Sig.X86
