module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamChunk
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamFirst
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamValue
import VerifiedGarbage.Proof.Framework.Omega

/-! The stored low words and live accumulator together equal the product
of the processed input prefix with the complete second operand. -/

-- separate module: invariant shared by the streamed multiplication chunks
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

structure StreamInv (s₀ : State) (pa pt : Addr) (B i : Nat) (rs : List Reg) (s : State) : Prop where
  product : wordsVal s.mem pt 0 i+2^(64*i)*regsVal s rs=wordsVal s₀.mem pa 0 i*B
  b : regsVal s bRegs=B
  zero : s.gpr .x2=0
  a0 : s.gpr .x3=word s₀.mem pa (8*i)
  a1 : s.gpr .x4=word s₀.mem pa (8*i+8)
  memory : Outside pt 0 64 s₀.mem s.mem
  kept : KeepRegs streamClob s₀ s

def StableInput (s₀ : State) (pa pt : Addr) : Prop :=
  ∀m,Outside pt 0 64 s₀.mem m → ∀d,d+8≤72 → word m pa d=word s₀.mem pa d

theorem arithmetic_frame {s : State} {code : List Instr} {out clob : List Reg} {T A B : Nat}
    (hb : regsVal s bRegs=B) (hz : s.gpr .x2=0)
    (h2 : .x2∉clob) (hbs : ∀r∈bRegs,r∉clob)
    (h : WP isa (.block code) s fun u =>
      regsVal u out=T+A*regsVal s bRegs ∧ Keeps clob s u) :
    WP isa (.block code) s fun u =>
      regsVal u out=T+A*B ∧ regsVal u bRegs=B ∧ u.gpr .x2=0 ∧ Keeps clob s u :=
  WP.mono h fun u ⟨e,k⟩ => ⟨by rw [e,hb],
    (regsVal_congr fun r hr => k.gpr r (hbs r hr)).trans hb,(k.gpr _ h2).trans hz,k⟩

theorem stream_step {s₀ s : State} {pa pt : Addr} {B i : Nat} {rs next out clob : List Reg}
    {code : List Instr} {r0 r1 : Reg}
    (ha : Ptr s₀ .x1 pa 72) (ht : PtrW s₀ .x27 pt 64)
    (stable : StableInput s₀ pa pt) (inv : StreamInv s₀ pa pt B i rs s)
    (hi : i+4≤9) (ho : out=[r0,r1]++next) (hnd : r0≠r1)
    (hc1 : .x1∉clob) (hc27 : .x27∉clob)
    (hn : ∀r∈next,r∉([.x3,.x4] : List Reg))
    (hc : ∀r∈(.x3::.x4::clob),r∈streamClob)
    (arith : WP isa (.block code) s fun u =>
      regsVal u out=regsVal s rs+((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*B ∧
      regsVal u bRegs=B ∧ u.gpr .x2=0 ∧ Keeps clob s u) :
    WP isa (.block (code++(spillPair r0 r1 (8*i)++loadPair (8*(i+2))))) s
      (StreamInv s₀ pa pt B (i+2) next) := by
  have ha' := ha.of_keepRegs inv.kept (by decide)
  have ht' := ht.of_keepRegs inv.kept (by decide)
  have hread : ∀m,Outside pt (8*i) 16 s.mem m →
      word m pa (8*(i+2))=word s.mem pa (8*(i+2)) ∧
      word m pa (8*(i+2)+8)=word s.mem pa (8*(i+2)+8) := by
    intro m hm
    have hm' := inv.memory.trans (hm.mono (by omega_arith) (by omega_arith))
    exact ⟨(stable m hm' _ (by omega_arith)).trans (stable s.mem inv.memory _ (by omega_arith)).symm,
      (stable m hm' _ (by omega_arith)).trans (stable s.mem inv.memory _ (by omega_arith)).symm⟩
  refine WP.mono (chunk_ok ha' ht' (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) hnd ho hc1 hc27 hn hread arith)
    fun t ⟨prod,a0,a1,b,z,k,om⟩ => ?_
  have whole := inv.memory.trans (om.mono (by omega_arith) (by omega_arith))
  have C : (s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat=wordsVal s₀.mem pa (8*i) 2 := by
    rw [inv.a0,inv.a1]
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  rw [C] at prod
  have hprefix := spill_prefix (i:=i) (by omega_arith) om
  have hA := wordsVal_split s₀.mem pa 0 i 2
  simp only [Nat.zero_add] at hA
  have hp : 2^(64*(i+2))=2^(64*i)*2^128 := by
    rw [Nat.mul_add,Nat.pow_add,show (64*2 : Nat)=128 from rfl]
  refine ⟨?_,b,z,?_,?_,whole,inv.kept.trans (k.mono hc)⟩
  · rw [hprefix,hp,hA]
    exact extend_product inv.product prod
  · rw [a0,stable s.mem inv.memory _ (by omega_arith)]
  · rw [a1,stable s.mem inv.memory _ (by omega_arith)]

end VG.Proof.Mont.AArch64.P521Field
