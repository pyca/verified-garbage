module

public import VerifiedGarbage.Impl.Rsa.X86.Chain
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-! One carry-preserving word, sharing the existing add/subtract arithmetic lemmas. -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Chain
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

def Rel (op : AluOp) (v a b p cin cout : Nat) : Prop :=
  if op = .adc then v+p*cout=a+b+cin else v+b+cin=a+p*cout

theorem rel_join {op : AluOp} {v a b p cin c w x y r c' : Nat}
    (h : Rel op v a b p cin c) (hw : Rel op w x y r c c') :
    Rel op (v+p*w) (a+p*x) (b+p*y) (r*p) cin c' := by
  unfold Rel at *
  split_ifs at * with hop
  · have E := congrArg (p*·) hw
    simp only [Nat.mul_add,Nat.mul_left_comm,Nat.mul_comm] at E ⊢
    omega
  · have E := congrArg (p*·) hw
    simp only [Nat.mul_add,Nat.mul_left_comm,Nat.mul_comm] at E ⊢
    omega

theorem rel_step {op : AluOp} {v a b p cin c w x y c' : Nat}
    (h : Rel op v a b p cin c) (hw : Rel op w x y (2^32) c c') :
    Rel op (v+p*w) (a+p*x) (b+p*y) (2^32*p) cin c' := by
  exact rel_join h hw

theorem word_ok {s : State} {base : Addr} {size a b d j : Nat} {op : AluOp} {cin : Bool}
    (hw : Ws s base size) (hop : op=.adc ∨ op=.sbb)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (ha : a+4*j+4≤size) (hb : b+4*j+4≤size) (hd : d+4*j+4≤size)
    (cf : s.cf=some cin) :
    WP isa (.block (VG.Impl.Rsa.X86.Chain.word op (4*j))) s fun t =>
      Outside base (d+4*j) 4 s.mem t.mem ∧ Keeps [.eax] s t ∧
      ∃ cout : Bool, t.cf=some cout ∧
        Rel op (w32 t.mem base (d+4*j)) (w32 s.mem base (a+4*j))
          (w32 s.mem base (b+4*j)) (2^32) cin.toNat cout.toNat := by
  unfold VG.Impl.Rsa.X86.Chain.word
  refine wp_movS (readSrc_ptr hw pa ha) fun s₁ U cf₁ => ?_
  have hw₁ := hw.of_keeps U.keeps
  have pb₁ : PtrAt s₁ base .ebx b := by rw [PtrAt,U.other _ (by decide)]; exact pb
  have read := readSrc_ptr hw₁ pb₁ hb
  have carry : s₁.cf=some cin := by rw [cf₁,cf]
  have Step : WP isa (.block [.alu op .eax (.mem (at_ .ebx (4*j)))]) s₁ fun t =>
      Keeps [.eax] s₁ t ∧ t.mem=s₁.mem ∧ ∃ cout : Bool,t.cf=some cout ∧
        Rel op (t.gpr .eax).toNat (w32 s.mem base (a+4*j))
          (w32 s.mem base (b+4*j)) (2^32) cin.toNat cout.toNat := by
    rcases hop with rfl|rfl
    · refine wp_adcS read carry fun t T C => WP.block_nil ⟨T.keeps,T.mem,_,C,?_⟩
      have H := adc_rel (s₁.gpr .eax) (s₁.mem.readW (off base (b+4*j)) 32) cin
      simpa [Rel,T.gpr,U.gpr,U.mem,w32] using H
    · refine wp_sbbS read carry fun t T C => WP.block_nil ⟨T.keeps,T.mem,_,C,?_⟩
      have H := sbb_rel (s₁.gpr .eax) (s₁.mem.readW (off base (b+4*j)) 32) cin
      simpa [Rel,T.gpr,U.gpr,U.mem,w32] using H
  change WP isa (.block ([.alu op .eax (.mem (at_ .ebx (4*j)))] ++
    [.store (at_ .edi (4*j)) .eax])) s₁ _
  refine WP.block_append (WP.mono Step fun t ⟨K,M,c,C,V⟩ => ?_)
  have hw₂ := hw₁.of_keeps K
  have pd₂ : PtrAt t base .edi d := by rw [PtrAt,K.1 _ (by decide),U.other _ (by decide)];exact pd
  refine wp_storeS (ea_ptr hw₂ pd₂ (by omega)) (ws_write hw₂ hd) fun u S => WP.block_nil ?_
  refine ⟨?_,(U.keeps.trans K).trans (S.keeps _),c,by rw [S.cf,C],?_⟩
  · rw [S.mem,M,U.mem]
    exact writeW32_outside _ _ _ (by have := hw.nowrap;omega)
  · rw [S.mem,w32_write_self]
    exact V

end VG.Proof.Rsa.X86.Chain
