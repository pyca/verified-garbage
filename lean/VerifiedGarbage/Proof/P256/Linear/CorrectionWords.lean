import VerifiedGarbage.Proof.P256.Linear.CorrectionValue

namespace VG.Proof.P256.Linear
open VG.Proof.Ed25519.Word64
open VG.Proof.P256.VerifySparse (four)

private theorem pow320 : (2:Nat)^320=2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 := by
  decide +kernel

abbrev W5 := Word × Word × Word × Word × Word

def w5value (a : W5) := five a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2

def subWords (a b c d e x y z w v : Word) : W5 × Bool :=
  let c0 := carryOut a (~~~x) true
  let c1 := carryOut b (~~~y) c0
  let c2 := carryOut c (~~~z) c1
  let c3 := carryOut d (~~~w) c2
  let c4 := carryOut e (~~~v) c3
  ((addCarry a (~~~x) true,addCarry b (~~~y) c0,addCarry c (~~~z) c1,
    addCarry d (~~~w) c2,addCarry e (~~~v) c3),!c4)

theorem subWords_value (a b c d e x y z w v : Word) :
    w5value (subWords a b c d e x y z w v).1+five x y z w v=
      five a b c d e+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(subWords a b c d e x y z w v).2.toNat := by
  have h := subFive_value a b c d e x y z w v
  simp only [pow320] at h
  exact h

def subQ (a b c d e : Word) : W5 × Bool :=
  let q := e+1
  let ds := addCarry d (q<<<32) false
  let es := addCarry e 0 (carryOut d (q<<<32) false)
  subWords a b c ds es (0-q) ((q<<<32)-1) 0 q q

private theorem subQ_finish (a b c d e ds es : Word) (co : Bool)
    (he : e.toNat≤20)
    (hd : ds.toNat+2^64*co.toNat=d.toNat+(e.toNat+1)*2^32)
    (hh : es.toNat=e.toNat+co.toNat) :
    w5value (subWords a b c ds es (0-(e+1)) (((e+1)<<<32)-1) 0 (e+1) (e+1)).1+(e.toNat+1)*p=
      five a b c d e+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(subWords a b c ds es (0-(e+1)) (((e+1)<<<32)-1) 0 (e+1) (e+1)).2.toNat := by
  have hsub := subWords_value a b c ds es (0-(e+1)) (((e+1)<<<32)-1) 0 (e+1) (e+1)
  generalize hr : subWords a b c ds es (0-(e+1)) (((e+1)<<<32)-1) 0 (e+1) (e+1) = output at hsub ⊢
  exact subtractQ_equation a b c d e ds es co (w5value output.1)
    output.2.toNat he hd hh hsub

private theorem qShift_value (e : Word) (he : e.toNat≤20) :
    ((e+1)<<<32).toNat=(e.toNat+1)*2^32 := by
  have hq : (e+1).toNat=e.toNat+1 := by
    simp only [BitVec.toNat_add,show (1 : Word).toNat=1 from rfl]
    omega
  simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,hq]
  omega

private theorem tinyAdd_value (e : Word) (co : Bool) (he : e.toNat≤20) :
    (addCarry e 0 co).toNat=e.toNat+co.toNat := by
  have h := addCarry_value e 0 co
  have hc := Bool.toNat_le co
  have hl := (addCarry e 0 co).isLt
  change (addCarry e 0 co).toNat+2^64*(carryOut e 0 co).toNat=e.toNat+0+co.toNat at h
  omega

private theorem lowAdd_value (d x : Word) (n : Nat) (hx : x.toNat=n) :
    (addCarry d x false).toNat+2^64*(carryOut d x false).toNat=d.toNat+n := by
  have h := addCarry_value d x false
  simpa only [Bool.toNat_false,Nat.add_zero,hx] using h

private theorem prepareQ_value (d e : Word) (he : e.toNat≤20) :
    let q : Word := e+1
    let co := carryOut d (q<<<32) false
    let ds := addCarry d (q<<<32) false
    let es := addCarry e 0 co
    ds.toNat+2^64*co.toNat=d.toNat+(e.toNat+1)*2^32 ∧ es.toNat=e.toNat+co.toNat := by
  exact ⟨lowAdd_value d _ _ (qShift_value e he),tinyAdd_value e _ he⟩

theorem subQ_value (a b c d e : Word) (he : e.toNat≤20) :
    w5value (subQ a b c d e).1+(e.toNat+1)*p=
      five a b c d e+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(subQ a b c d e).2.toNat := by
  let co := carryOut d ((e+1)<<<32) false
  let ds := addCarry d ((e+1)<<<32) false
  let es := addCarry e 0 co
  have hp := prepareQ_value d e he
  exact subQ_finish a b c d e ds es co he hp.1 hp.2

def correctionWords (a b c d e : Word) : Word × Word × Word × Word :=
  let w := (subQ a b c d e).1
  addBack w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2

theorem correctionWords_value (a b c d e : Word) (hn : five a b c d e<21*p) :
    let w:=correctionWords a b c d e;
    four w.1 w.2.1 w.2.2.1 w.2.2.2=five a b c d e%p := by
  have he : e.toNat≤20 := by
    simp only [five,p_value] at hn
    omega
  have hq : e.toNat=five a b c d e/2^256 := by
    have hl := four_lt a b c d
    simp only [five]
    omega
  have hv := subQ_value a b c d e he
  dsimp only [correctionWords]
  generalize hw : subQ a b c d e = result at hv ⊢
  obtain ⟨neg,hneg,hmod⟩ := correction_value (five a b c d e) e.toNat
    result.2.toNat result.1.1 result.1.2.1 result.1.2.2.1 result.1.2.2.2.1 result.1.2.2.2.2 hn hq hv
  rw [addBack_value _ _ _ _ _ neg hneg]
  exact hmod

end VG.Proof.P256.Linear
