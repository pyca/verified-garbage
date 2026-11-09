module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamMiddle
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulLast
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Spill eight low limbs and load only the final input limb. -/

-- separate module: the final partial load does not require a tenth readable limb
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure TailInv (s₀ : State) (pa pt : Addr) (B : Nat) (s : State) : Prop where
  product : wordsVal s.mem pt 0 8+2^512*regsVal s row8In=wordsVal s₀.mem pa 0 8*B
  b : regsVal s bRegs=B
  zero : s.gpr .x2=0
  top : s.gpr .x3=word s₀.mem pa 64
  memory : Outside pt 0 64 s₀.mem s.mem
  kept : KeepRegs streamClob s₀ s

def stage6Code : List Instr := pair6Code++(spillPair .x22 .x23 48++[.ldr .x .x3 .x1 64])

theorem stage6_ok {s₀ s : State} {pa pt : Addr} {B : Nat}
    (ha : Ptr s₀ .x1 pa 72) (ht : PtrW s₀ .x27 pt 64)
    (stable : StableInput s₀ pa pt) (inv : StreamInv s₀ pa pt B 6 row6In s) :
    WP isa (.block stage6Code) s (TailInv s₀ pa pt B) := by
  rw [stage6Code,WP.block_append_iff]
  refine WP.mono (pair6_value s inv.zero) fun u ⟨prod,ku⟩ => ?_
  have hread : ∀m,Outside pt 48 16 u.mem m → word m pa 64=word u.mem pa 64 := by
    intro m hm
    rw [ku.mem] at hm ⊢
    have hw := inv.memory.trans (hm.mono (o':=0) (n':=64) (by decide) (by decide))
    exact (stable m hw 64 (by decide)).trans (stable s.mem inv.memory 64 (by decide)).symm
  refine WP.mono (spill_load_last_ok
    ((ha.of_keepRegs inv.kept (by decide)).of_keeps ku (by decide))
    ((ht.of_keepRegs inv.kept (by decide)).of_keepRegs
      (VG.Proof.Mont.AArch64.Keeps.regs ku) (by decide)) (by decide) hread)
    fun t ⟨stored,atop,kt,om⟩ => ?_
  have en : regsVal t row8In=regsVal u row8In := regsVal_congr fun r hr =>
    kt.gpr r ((show ∀r∈row8In,r∉([.x3] : List Reg) from by decide) r hr)
  have eout : regsVal u pair6Out=regsVal u [.x22,.x23]+2^128*regsVal u row8In := by
    have ho : pair6Out=([.x22,.x23] : List Reg)++row8In := rfl
    rw [ho,regsVal_append]
    rfl
  have C : (s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat=wordsVal s₀.mem pa 48 2 := by
    rw [inv.a0,inv.a1]
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  rw [inv.b,C] at prod
  have chunk : wordsVal t.mem pt 48 2+2^128*regsVal t row8In =
      regsVal s row6In+wordsVal s₀.mem pa 48 2*B := by
    rw [stored,en,←eout]; exact prod
  have om' : Outside pt 48 16 s.mem t.mem := by rw [ku.mem] at om; exact om
  have whole := inv.memory.trans (om'.mono (o':=0) (n':=64) (by decide) (by decide))
  have hprefix := spill_prefix (i:=6) (by decide) om'
  have hA := wordsVal_split s₀.mem pa 0 6 2
  simp only [Nat.zero_add] at hA
  have hp := Nat.pow_add (2 : Nat) 384 128
  simp only [Nat.reduceAdd] at hp
  refine ⟨?_,?_,?_,?_,whole,?_⟩
  · rw [hprefix,hp,hA]
    have e := extend_product inv.product chunk
    simp only [Nat.reduceMul] at e ⊢
    exact e
  · rw [regsVal_congr (s:=u) (fun r hr => kt.gpr r
      ((show ∀r∈bRegs,r∉([.x3] : List Reg) from by decide) r hr))]
    rw [regsVal_congr (s:=s) (fun r hr => ku.gpr r
      ((show ∀r∈bRegs,r∉(.x14::pair6Out) from by decide) r hr))]
    exact inv.b
  · rw [kt.gpr _ (by decide),ku.gpr _ (by decide),inv.zero]
  · rw [atop,ku.mem,stable s.mem inv.memory 64 (by decide)]
  · exact inv.kept.trans (((VG.Proof.Mont.AArch64.Keeps.regs ku).mono (by decide)).trans
      (kt.mono (by decide)))

def stream8Code : List Instr := stream6Code++stage6Code

theorem stream8_ok {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt) :
    WP isa (.block stream8Code) s (TailInv s pa pt (wordsVal s.mem pb 0 9)) := by
  rw [stream8Code,WP.block_append_iff]
  refine WP.mono (stream6_ok ha hb ht stable) fun u inv => ?_
  exact stage6_ok ha ht stable inv

end VG.Proof.Mont.AArch64.P521Field
