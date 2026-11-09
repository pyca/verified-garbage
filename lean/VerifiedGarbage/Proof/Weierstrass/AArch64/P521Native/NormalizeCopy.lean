module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeLayout
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! The table-to-workspace copies used by the unrolled normalization schedule. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def normalizeCopy : Nat → Nat → Nat → List Instr
  | 0,_,_ => []
  | n+1,a,o => .ldr .x .x1 .x26 a :: .str .x .x1 .x0 o :: normalizeCopy n (a+8) (o+8)

theorem normalize_copy_ok {base table : Addr} {W : Nat} (apart : TableWorkspaceApart base table W) :
    ∀n {s : State} {a o : Nat},Scr s base W → Ptr s .x26 table 3456 →
      a+8*n≤3456 → o+8*n≤W → a%8=0 → o%8=0 →
      WP isa (.block (normalizeCopy n a o)) s fun t =>
        wordsVal t.mem base o n=wordsVal s.mem table a n ∧ KeepRegs [.x1] s t ∧
        Outside base o (8*n) s.mem t.mem
  | 0,s,a,o,_,_,_,_,_,_ => WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | n+1,s,a,o,hs,pt,ha,ho,ha8,ho8 => by
    change WP isa (.block (([.ldr .x .x1 .x26 a] : List Instr)++
      (([.str .x .x1 .x0 o] : List Instr)++normalizeCopy n (a+8) (o+8)))) s _
    rw [WP.block_append_iff]
    refine WP.mono (ldR_ok pt (d:=a) (by omega_arith) ha8 .x1) fun u ⟨loaded,ku,_⟩ => ?_
    have hsu := hs.of_keeps ku (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (stR_ok hsu.ptrW (d:=o) (by omega_arith) ho8 .x1) fun v stored => ?_
    have kv : KeepRegs [.x1] s v := by
      rw [stored]
      exact ⟨ku.gpr,ku.rd,ku.wr,ku.sp⟩
    have ov : Outside base o 8 s.mem v.mem := by
      rw [stored,ku.mem]
      exact writeW_outside s.mem base (d:=o) (u.gpr .x1) (by have h:=hs.enc; omega_arith)
    have first : word v.mem base o=word s.mem table a := by
      rw [stored,word_writeW_self,loaded]
    have hsv := hs.of_keepRegs kv (by decide)
    have ptv := pt.of_keepRegs kv (by decide)
    refine WP.mono (normalize_copy_ok apart n hsv ptv (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith)) fun t ⟨tail,kt,ot⟩ => ?_
    have wordSaved : word t.mem base o=word v.mem base o := ot.word (Or.inl (by omega_arith))
      (by have h:=hs.enc; omega_arith)
    have tableUnchanged := apart.wordsVal (ov.mono (by omega_arith) (by omega_arith)) n (a+8) (by omega_arith)
    refine ⟨?_,kv.trans kt,?_⟩
    · simp only [wordsVal]
      rw [wordSaved,first,tail,tableUnchanged]
    · exact (ov.mono (by omega_arith) (by omega_arith)).trans (ot.mono (by omega_arith) (by omega_arith))

end VG.Proof.Weierstrass.AArch64.P521Native
