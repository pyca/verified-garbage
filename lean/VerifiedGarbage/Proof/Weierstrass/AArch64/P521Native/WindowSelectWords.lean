module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowSelectWord
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Arbitrary-length exact scalar mux with in-place and disjoint source support. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def windowSeparated (a o n : Nat) : Prop := a=o ∨ a+8*n≤o ∨ o+8*n≤a

def windowSelectWords (a b o n : Nat) : List Instr :=
  (List.range n).flatMap fun i => windowSelectWord (a+8*i) (b+8*i) (o+8*i)

theorem window_select_words {s : State} {base : Addr} {size a b o n : Nat}
    (hs : Scr s base size) (ha : a+8*n≤size) (hb : b+8*n≤size) (ho : o+8*n≤size)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (sepA : windowSeparated a o n) (sepB : windowSeparated b o n) (takeB : Bool)
    (mask : s.gpr .x3=if takeB then BitVec.allOnes 64 else 0) :
    ∀k≤n, WP isa (.block (windowSelectWords a b o k)) s fun t =>
      (∀i<k,word t.mem base (o+8*i)=
        if takeB then word s.mem base (b+8*i) else word s.mem base (a+8*i)) ∧
      KeepRegs [.x1,.x2] s t ∧ Outside base o (8*k) s.mem t.mem
  | 0,_ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      ⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | k+1,hk => by
    have hn := hs.nowrap
    rw [windowSelectWords,List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (window_select_words hs ha hb ho ha8 hb8 ho8 sepA sepB takeB mask k (by omega_arith))
      fun u ⟨eu,ku,ou⟩ => ?_
    have hu := hs.of_keepRegs ku (by decide)
    have mu : u.gpr .x3=if takeB then BitVec.allOnes 64 else 0 := (ku.gpr _ (by decide)).trans mask
    refine WP.mono (window_select_word hu (a:=a+8*k) (b:=b+8*k) (o:=o+8*k)
      (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) takeB mu) fun t ⟨et,kt⟩ => ?_
    have ot : Outside base (o+8*k) 8 u.mem t.mem := by
      rw [et]; exact writeW_outside _ _ _ (by omega_arith)
    have before (d : Nat) (hd : d+8*n≤size) (sep : windowSeparated d o n) :
        word u.mem base (d+8*k)=word s.mem base (d+8*k) := by
      rcases sep with h | h | h
      · subst d; exact ou.word (by omega_arith) (by omega_arith)
      · exact ou.word (by omega_arith) (by omega_arith)
      · exact ou.word (by omega_arith) (by omega_arith)
    refine ⟨fun i hi => ?_,ku.trans kt,?_⟩
    · rcases Nat.lt_or_ge i k with h | h
      · rw [ot.word (by omega_arith) (by omega_arith),eu i h]
      · have ik : i=k := by omega_arith
        subst i
        rw [et,word_writeW_self,before a ha sepA,before b hb sepB]
    · exact (ou.mono (by omega_arith) (by omega_arith)).trans
        (ot.mono (by omega_arith) (by omega_arith))

end VG.Proof.Weierstrass.AArch64.P521Native
