module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Width
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

@[expose] public section

namespace VG.Proof.Mont.X86.PreparedSquare
open VG.Proof.Mont.X86.Square
open VG.Impl.Mont.X86.PreparedSquare
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.PreparedSquare
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def digit (s : State) (W : Addr) (S inv : Nat) : Nat :=
  (w32 s.mem W (S+16)*w32 s.mem W inv) % 2^32

def digitStore : List Instr := ptr .edx argInv .eax ++
  [.mov .edx (.mem (at_ .edx 0)), .mov .eax (.mem (sc 16)), .mul .edx,
   .mov .ecx (.reg .edi), .alu .add .ecx (.imm 24), .alu .add .ecx (.reg .esi),
   .store (at_ .ecx 0) .eax, .mov .ebx (.reg .eax)]

theorem digitStore_ok {s : State} {W : Addr} {L S inv k : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (base : A 0 = BitVec.ofNat 32 W.toNat)
    (iv : A 4 = BitVec.ofNat 32 inv) (il : inv+4≤L) (tl : S+16+4≤L) (ql : S+24+4*k+4≤L)
    (edi : PtrAt s W .edi S) (si : s.gpr .esi = BitVec.ofNat 32 (4*k)) :
    WP isa (.block digitStore) s fun t =>
      t.mem = s.mem.writeW (off W (S+24+4*k)) (BitVec.ofNat 32 (digit s W S inv)) ∧
      t.gpr .ebx = BitVec.ofNat 32 (digit s W S inv) ∧
      Keeps [.eax, .edx, .ecx, .ebx] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block digitStore) s fun t =>
      t.mem = s.mem.writeW (off W (S+24+4*k)) (BitVec.ofNat 32 (digit s W S inv)) ∧
      t.gpr .ebx = BitVec.ofNat 32 (digit s W S inv) ∧ Keeps [.eax, .edx, .ecx, .ebx] s t := by
    unfold digitStore
    apply WP.block_append
    refine WP.mono (ptr_ok ha (r := .edx) (t := .eax) (i := 4) (by decide) (by decide) (by decide))
      fun t1 ⟨edx1, _, m1, K1⟩ => ?_
    have hw1 := hw.of_keeps K1
    have pinv : PtrAt t1 W .edx inv := by
      rw [PtrAt, edx1, base, iv, ← BitVec.ofNat_add, BitVec.toNat_ofNat]
    refine wp_movS (by simpa using readSrc_ptr hw1 pinv (d := 0) (by omega)) fun t2 u2 _ => ?_
    have hw2 := hw1.of_keeps u2.keeps
    have edi2 : PtrAt t2 W .edi S := by rw [PtrAt, u2.other _ (by decide), K1.1 _ (by decide)]; exact edi
    refine wp_movS (readSrc_ptr hw2 edi2 (d := 16) (by omega)) fun t3 u3 _ => wp_mul fun t4 m4 => ?_
    have K4 : Keeps [.eax, .edx] s t4 :=
      (K1.mono (by decide)).trans ((u2.keeps.mono (by decide)).trans ((u3.keeps.mono (by decide)).trans m4.keeps))
    have mem4 : t4.mem = s.mem := m4.mem.trans (u3.mem.trans (u2.mem.trans m1))
    have ea4 : t4.gpr .eax = BitVec.ofNat 32 (digit s W S inv) := by
      rw [m4.eax, u3.gpr, u3.other _ (by decide), u2.gpr, u2.mem, m1]
      apply BitVec.eq_of_toNat_eq
      simp only [digit, w32, BitVec.toNat_ofNat, Nat.mod_mod]
    have edi4 : t4.gpr .edi = BitVec.ofNat 32 (W.toNat+S) := by
      apply BitVec.eq_of_toNat_eq
      rw [K4.1 _ (by decide), edi, BitVec.toNat_ofNat]
    have si4 : t4.gpr .esi = BitVec.ofNat 32 (4*k) := (K4.1 _ (by decide)).trans si
    refine wp_movS rfl fun t5 u5 _ => wp_addS rfl fun t6 u6 _ => wp_addS rfl fun t7 u7 _ => ?_
    have c7 : PtrAt t7 W .ecx (S+24+4*k) := by
      rw [PtrAt, u7.gpr, u6.gpr, u5.gpr, edi4, u6.other _ (by decide), u5.other _ (by decide), si4]
      change (((BitVec.ofNat 32 (W.toNat+S)+BitVec.ofNat 32 24)+BitVec.ofNat 32 (4*k))).toNat = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, BitVec.toNat_ofNat]
      congr 1
      omega
    have ea7 : t7.gpr .eax = BitVec.ofNat 32 (digit s W S inv) := by
      rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), ea4]
    have K7 : Keeps [.eax, .edx, .ecx, .ebx] s t7 :=
      (K4.mono (by decide)).trans ((u5.keeps.mono (by decide)).trans
        ((u6.keeps.mono (by decide)).trans (u7.keeps.mono (by decide))))
    have hw7 := hw.of_keeps K7
    refine wp_storeS (ea_ptr hw7 c7 (d := 0) (by omega)) (ws_write hw7 (y := S+24+4*k) (n := 4) ql)
      fun t8 m8 => wp_movS rfl fun t9 u9 _ => WP.block_nil ?_
    refine ⟨?_, ?_, K7.trans ((m8.keeps _).trans (u9.keeps.mono (by decide)))⟩
    · rw [u9.mem, m8.mem, u7.mem, u6.mem, u5.mem, mem4, ea7, Nat.add_zero]
    · rw [u9.gpr, m8.gpr, ea7]
  exact WP.mono (scalar_frame (by simp [digitStore, ptr, argInv, scalar]) body)
    fun t ⟨⟨mem, ebx, keep⟩, xmm⟩ => ⟨mem, ebx, keep, xmm⟩

end VG.Proof.Mont.X86.PreparedSquare
