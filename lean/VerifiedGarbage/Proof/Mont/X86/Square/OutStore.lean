module

public import VerifiedGarbage.Proof.Mont.X86.Square.DigitFull

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def outStore : List Instr := [.mov .eax (.mem (sc 20)), .mov .ecx (.reg .edi),
  .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .esi), .store (at_ .ecx 0) .eax]

theorem outStore_ok {s : State} {W : Addr} {L S k : Nat} (hw : Ws s W L)
    (tl : S+20+4≤L) (ql : S+52+4*k+4≤L)
    (edi : PtrAt s W .edi S) (si : s.gpr .esi = BitVec.ofNat 32 (4*k)) :
    WP isa (.block outStore) s fun t =>
      t.mem = s.mem.writeW (off W (S+52+4*k)) (s.mem.readW (off W (S+20)) 32) ∧
      Keeps [.eax, .ecx] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block outStore) s fun t =>
      t.mem = s.mem.writeW (off W (S+52+4*k)) (s.mem.readW (off W (S+20)) 32) ∧
      Keeps [.eax, .ecx] s t := by
    unfold outStore
    refine wp_movS (readSrc_ptr hw edi (d := 20) (by omega)) fun t1 u1 _ =>
      wp_movS rfl fun t2 u2 _ => wp_addS rfl fun t3 u3 _ => wp_addS rfl fun t4 u4 _ => ?_
    have c4 : PtrAt t4 W .ecx (S+52+4*k) := by
      rw [PtrAt, u4.gpr, u3.gpr, u2.gpr, u1.other _ (by decide)]
      have eq : s.gpr .edi = BitVec.ofNat 32 (W.toNat+S) := by
        apply BitVec.eq_of_toNat_eq; rw [edi, BitVec.toNat_ofNat]
      rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), si, eq]
      change (((BitVec.ofNat 32 (W.toNat+S)+BitVec.ofNat 32 52)+BitVec.ofNat 32 (4*k))).toNat = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, BitVec.toNat_ofNat]; congr 1; omega
    have ea4 : t4.gpr .eax = s.mem.readW (off W (S+20)) 32 := by
      rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
    have K4 : Keeps [.eax, .ecx] s t4 :=
      (u1.keeps.mono (by decide)).trans ((u2.keeps.mono (by decide)).trans
        ((u3.keeps.mono (by decide)).trans (u4.keeps.mono (by decide))))
    have hw4 := hw.of_keeps K4
    refine wp_storeS (ea_ptr hw4 c4 (d := 0) (by omega)) (ws_write hw4 (y := S+52+4*k) (n := 4) ql)
      fun t5 m5 => WP.block_nil ?_
    refine ⟨?_, K4.trans (m5.keeps _)⟩
    rw [m5.mem, ea4, Nat.add_zero, u4.mem, u3.mem, u2.mem, u1.mem]
  exact WP.mono (scalar_frame (by simp [outStore, scalar]) body)
    fun t ⟨⟨mem, keep⟩, xmm⟩ => ⟨mem, keep, xmm⟩

end VG.Proof.Mont.X86.Square
