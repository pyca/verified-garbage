module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamInvariant
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulLast
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamBounds

/-! The streaming product invariant, its tail, and the exact native instruction schedule. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def firstStreamCode : List Instr :=
  (row0Loads++pair0Code)++(spillPair .x15 .x16 0++loadPair 16)

theorem stream_init {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt) :
    WP isa (.block firstStreamCode) s (StreamInv s pa pt (wordsVal s.mem pb 0 9) 2 row2In) := by
  have hread : ∀m,Outside pt 0 16 s.mem m →
      word m pa 16=word s.mem pa 16 ∧ word m pa 24=word s.mem pa 24 := by
    intro m hm
    have hwide := hm.mono (o':=0) (n':=64) (by decide) (by decide)
    exact ⟨stable m hwide 16 (by decide),stable m hwide 24 (by decide)⟩
  refine WP.mono (chunk_ok ha ht (by decide) (by decide) (by decide) (by decide)
    (r0:=.x15) (r1:=.x16) (out:=pair0Out) (next:=row2In)
    (by decide) rfl (by decide) (by decide) (by decide) hread (firstPair_loaded ha hb))
    fun t ⟨prod,a0,a1,b,z,k,om⟩ => ?_
  refine ⟨?_,b,z,a0,a1,om.mono (by decide) (by decide),k.mono (by decide)⟩
  exact prod

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def stage2Code : List Instr := pair2Code++(spillPair .x17 .x19 16++loadPair 32)
def stage4Code : List Instr := pair4Code++(spillPair .x20 .x21 32++loadPair 48)

theorem stage2_ok {s₀ s : State} {pa pt : Addr} {B : Nat}
    (ha : Ptr s₀ .x1 pa 72) (ht : PtrW s₀ .x27 pt 64)
    (stable : StableInput s₀ pa pt) (inv : StreamInv s₀ pa pt B 2 row2In s) :
    WP isa (.block stage2Code) s (StreamInv s₀ pa pt B 4 row4In) := by
  exact stream_step ha ht stable inv (by decide) (out:=pair2Out) (r0:=.x17) (r1:=.x19)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (arithmetic_frame inv.b inv.zero (by decide) (by decide) (pair2_value s inv.zero))

theorem stage4_ok {s₀ s : State} {pa pt : Addr} {B : Nat}
    (ha : Ptr s₀ .x1 pa 72) (ht : PtrW s₀ .x27 pt 64)
    (stable : StableInput s₀ pa pt) (inv : StreamInv s₀ pa pt B 4 row4In s) :
    WP isa (.block stage4Code) s (StreamInv s₀ pa pt B 6 row6In) := by
  exact stream_step ha ht stable inv (by decide) (out:=pair4Out) (r0:=.x20) (r1:=.x21)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (arithmetic_frame inv.b inv.zero (by decide) (by decide) (pair4_value s inv.zero))

def stream6Code : List Instr := firstStreamCode++(stage2Code++stage4Code)

theorem stream6_ok {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt) :
    WP isa (.block stream6Code) s (StreamInv s pa pt (wordsVal s.mem pb 0 9) 6 row6In) := by
  rw [stream6Code,WP.block_append_iff]
  refine WP.mono (stream_init ha hb ht stable) fun u inv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (stage2_ok ha ht stable inv) fun v inv' => ?_
  exact stage4_ok ha ht stable inv'

end VG.Proof.Mont.AArch64.P521Field

end

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

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure ProductInv (s₀ : State) (pa pt : Addr) (B : Nat) (s : State) : Prop where
  product : wordsVal s.mem pt 0 8+2^512*regsVal s row8In=wordsVal s₀.mem pa 0 9*B
  zero : s.gpr .x2=0
  memory : Outside pt 0 64 s₀.mem s.mem
  kept : KeepRegs streamClob s₀ s

theorem finish_product {s₀ s : State} {pa pt : Addr} {B : Nat}
    (inv : TailInv s₀ pa pt B s)
    (ha : wordsVal s₀.mem pa 0 9<2^521) (hb : B<2^521) :
    WP isa (.block (row8LowCode++row8HighCode)) s (ProductInv s₀ pa pt B) := by
  have ae := wordsVal_succ_top s₀.mem pa 0 8
  simp only [Nat.reduceAdd,Nat.reduceMul,Nat.zero_add] at ae
  have atop := top_limb_bound (L:=wordsVal s₀.mem pa 0 8)
    (A:=wordsVal s₀.mem pa 0 9) (top:=(word s₀.mem pa 64).toNat) ae ha
  have aTopReg : (s.gpr .x3).toNat<512 := by rw [inv.top]; exact atop
  have be : B=regsVal s bLowRegs+2^512*(s.gpr .x13).toNat := by
    rw [←inv.b]
    have hbr : bRegs=bLowRegs++[.x13] := rfl
    rw [hbr,regsVal_append]
    simp only [regsVal,Nat.mul_zero,Nat.add_zero,
      show bLowRegs.length=8 from rfl,Nat.reduceMul]
  have btop := top_limb_bound (L:=regsVal s bLowRegs) (A:=B)
    (top:=(s.gpr .x13).toNat) be hb
  have hpref := wordsVal_lt s₀.mem pa 0 8
  simp only [Nat.reduceMul] at hpref
  have ht := tail_acc_bound (P:=wordsVal s₀.mem pa 0 8)
    (S:=wordsVal s.mem pt 0 8) (T:=regsVal s row8In) (B:=B) hpref inv.product
  have hbound := final_row_bound (T:=regsVal s row8In) (B:=B) (s.gpr .x3) ht hb aTopReg
  have hbound' : regsVal s row8In+(s.gpr .x3).toNat*regsVal s bRegs<2^576 := by
    rw [inv.b]; exact hbound
  refine WP.mono (row8_value s (mulHi_small _ _ aTopReg btop) hbound') fun t ⟨prod,k⟩ => ?_
  refine ⟨?_,(k.gpr _ (by decide)).trans inv.zero,?_,?_⟩
  · rw [inv.b,inv.top] at prod
    have e := last_limb_identity inv.product prod
    rw [←ae] at e
    rw [k.mem]
    exact e
  · rw [k.mem]; exact inv.memory
  · exact inv.kept.trans ((VG.Proof.Mont.AArch64.Keeps.regs k).mono (by decide))

def productCode : List Instr := stream8Code++(row8LowCode++row8HighCode)

theorem product_ok {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt)
    (ha' : wordsVal s.mem pa 0 9<2^521) (hb' : wordsVal s.mem pb 0 9<2^521) :
    WP isa (.block productCode) s (ProductInv s pa pt (wordsVal s.mem pb 0 9)) := by
  rw [productCode,WP.block_append_iff]
  refine WP.mono (stream8_ok ha hb ht stable) fun u inv => ?_
  exact finish_product inv ha' hb'

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def nativeProductCode : List Instr := (mulFnBlocks.flatten.drop 16).take 354
def nativeProductRest : List Instr := (mulFnBlocks.flatten.drop 55).take 315

theorem chunks_eq {α : Type} {xs ys : List α} (n : Nat)
    (ht : xs.take n=ys.take n) (hd : xs.drop n=ys.drop n) : xs=ys := by
  calc
    xs = xs.take n++xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n++ys.drop n := by rw [ht,hd]
    _ = ys := List.take_append_drop n ys

theorem nativeProduct_split : nativeProductCode=row0Code++nativeProductRest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem product_normalized : productCode=(row0Loads++row0Arithmetic)++nativeProductRest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

/-- Moving independent loads is used only by the proof. The emitted product
retains exactly the interleaved load/product schedule measured on M1. -/
theorem native_product_ok {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt)
    (ha' : wordsVal s.mem pa 0 9<2^521) (hb' : wordsVal s.mem pb 0 9<2^521) :
    WP isa (.block nativeProductCode) s (ProductInv s pa pt (wordsVal s.mem pb 0 9)) := by
  have h := product_ok ha hb ht stable ha' hb'
  rw [product_normalized,WP.block_append_iff] at h
  rw [nativeProduct_split,WP.block_append_iff]
  exact WP.hoistLoads row0_hoist h

end VG.Proof.Mont.AArch64.P521Field

end
