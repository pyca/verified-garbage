module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeCopy
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Store normalized coordinates from workspace to the disjoint stack table. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64

theorem TableWorkspaceApart.disjoint {base table : Addr} {W : Nat}
    (apart : TableWorkspaceApart base table W) : Region.Disjoint ⟨base,W⟩ ⟨table,3456⟩ := by
  intro x hx ht
  have dlt : ofs table x<3456 := by change (x-table).toNat+1≤3456 at ht; change (x-table).toNat<3456; omega_arith
  have address : off table (ofs table x)=x := by
    dsimp only [off,ofs]
    rw [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_comm,BitVec.sub_add_cancel]
  have low := apart _ dlt
  rw [address] at low
  change (x-base).toNat+1≤W at hx
  change W≤(x-base).toNat at low
  omega_arith

def normalizeStoreCopy : Nat → Nat → Nat → List Instr
  | 0,_,_ => []
  | n+1,a,o => .ldr .x .x1 .x0 a :: .str .x .x1 .x26 o :: normalizeStoreCopy n (a+8) (o+8)

theorem normalize_store_copy_ok {base table : Addr} {W : Nat}
    (apart : Region.Disjoint ⟨base,W⟩ ⟨table,3456⟩) :
    ∀n {s : State} {a o : Nat},Scr s base W → PtrW s .x26 table 3456 →
      a+8*n≤W → o+8*n≤3456 → a%8=0 → o%8=0 →
      WP isa (.block (normalizeStoreCopy n a o)) s fun t =>
        wordsVal t.mem table o n=wordsVal s.mem base a n ∧ KeepRegs [.x1] s t ∧
        Outside table o (8*n) s.mem t.mem
  | 0,s,a,o,_,_,_,_,_,_ => WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | n+1,s,a,o,hs,pt,ha,ho,ha8,ho8 => by
    change WP isa (.block (([.ldr .x .x1 .x0 a] : List Instr)++
      (([.str .x .x1 .x26 o] : List Instr)++normalizeStoreCopy n (a+8) (o+8)))) s _
    rw [WP.block_append_iff]
    refine WP.mono (ldR_ok hs.ptr (d:=a) (by omega_arith) ha8 .x1) fun u ⟨loaded,ku,_⟩ => ?_
    have ptu := pt.of_keepRegs (Keeps.regs ku) (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (stR_ok ptu (d:=o) (by omega_arith) ho8 .x1) fun v stored => ?_
    have kv : KeepRegs [.x1] s v := by
      rw [stored]
      exact ⟨ku.gpr,ku.rd,ku.wr,ku.sp⟩
    have ov : Outside table o 8 s.mem v.mem := by
      rw [stored,ku.mem]
      exact writeW_outside s.mem table (d:=o) (u.gpr .x1) (by omega_arith)
    have first : word v.mem table o=word s.mem base a := by
      rw [stored,word_writeW_self,loaded]
    have hsv := hs.of_keepRegs kv (by decide)
    have ptv := pt.of_keepRegs kv (by decide)
    refine WP.mono (normalize_store_copy_ok apart n hsv ptv (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith)) fun t ⟨tail,kt,ot⟩ => ?_
    have wordSaved : word t.mem table o=word v.mem table o := ot.word (Or.inl (by omega_arith)) (by omega_arith)
    have workspaceUnchanged : Unch base [(W,2^64)] s.mem v.mem :=
      (ov.mono (by omega_arith : 0≤o) (by omega_arith : o+8≤0+3456)).unch_far apart
    have sourceSame := workspaceUnchanged.wordsVal (d:=a+8) (k:=n)
      (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by omega_arith))
      (by have h:=hs.enc; omega_arith)
    refine ⟨?_,kv.trans kt,?_⟩
    · simp only [VG.Proof.Mont.wordsVal]
      rw [wordSaved,first,tail,sourceSame]
    · exact (ov.mono (by omega_arith) (by omega_arith)).trans (ot.mono (by omega_arith) (by omega_arith))

end VG.Proof.Weierstrass.AArch64.P521Native
