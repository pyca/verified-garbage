module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicFinishCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorPower
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPlan
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicFinishCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorPower
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Generator exponentiation reuses the verified public-power timing proof -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64

def GeneratorPlan.powerCall (p : GeneratorPlan) (mi : BitVec 64) : Call3Public where
  bytes := ⟨⟨p.B, activeBytes, pWorkspace, outerWords, p.len / 8⟩,
    off p.B VG.Impl.Dsa.Generation.Layout.exponent, p.len⟩
  minv := mi
  modulus := Spec.Dsa.decodeBE p.pb
  base := p.hp
  baseLen := p.len
  output := off p.B VG.Impl.Dsa.Generation.Layout.g
  outputLen := p.len
  parentInverse := 0
  greater := p.pPositive
  odd := p.pOdd
  lower := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  fits := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  upper := by dsimp only; decide
  width48 := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  basePositive := by rcases p.width with h | h | h <;> rw [h] <;> decide
  baseFits := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  expPositive := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  expLimit := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  extent := by dsimp only; decide
  childLow := by dsimp only; decide
  childHigh := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  offsetBound := by dsimp only; decide
  outputPositive := by rcases p.width with h | h | h <;> rw [h] <;> decide
  outputBound := by rcases p.width with h | h | h <;> rw [h] <;> decide
  outputWidth := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide

structure GeneratorPowerReady (p : GeneratorPlan) (mi : BitVec 64) (s : State) : Prop where
  parent : Good s p.B activeBytes outerWords 0
  child : ChildReady s.mem p.B pWorkspace (p.len / 8) (Spec.Dsa.decodeBE p.pb) mi
  base : word s.mem p.B 272 = p.hp
  exponent : word s.mem p.B 288 = off p.B VG.Impl.Dsa.Generation.Layout.exponent
  length : word s.mem p.B 328 = BitVec.ofNat 64 p.len
  hSource : Src s p.B activeBytes p.hp p.hb
  eSource : Src s p.B activeBytes (off p.B VG.Impl.Dsa.Generation.Layout.exponent) p.eb
  output : ∀ i < p.len, InRegions s.wr (off (off p.B VG.Impl.Dsa.Generation.Layout.g) i) 1

theorem generatorPower_call {p : GeneratorPlan} {mi : BitVec 64} {s : State}
    (h : GeneratorPowerReady p mi s) :
    PublicPower.CallPre ⟨.input .g, .pLen⟩ ⟨.input .x, .pLen⟩
      ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩ (p.powerCall mi, p.eb) s := by
  have hb : OperandBytes s p.B activeBytes ⟨.input .g, .pLen⟩ p.hb :=
    ⟨by change word s.mem p.B 328 = _; rw [p.hLength]; exact h.length,
      by change Src s p.B activeBytes (word s.mem p.B 272) p.hb; rw [h.base]; exact h.hSource⟩
  have he : OperandBytes s p.B activeBytes ⟨.input .x, .pLen⟩ p.eb :=
    ⟨by change word s.mem p.B 328 = _; rw [p.eLength]; exact h.length,
      by change Src s p.B activeBytes (word s.mem p.B 288) p.eb; rw [h.exponent]; exact h.eSource⟩
  exact ⟨⟨h.parent, h.child, ⟨p.hb, p.eb, hb, he, p.hLength, p.eLength⟩,
    h.base, h.exponent, rfl, h.length, h.output, p.gParentOutside⟩, h.eSource, p.eLength⟩

def GeneratorPowerBefore (p : GeneratorPlan) (s : State) : Prop := ∃ mi, GeneratorPowerReady p mi s

theorem generatorPower_inverse {p : GeneratorPlan} {s t : State} {mi mj : BitVec 64}
    (hs : GeneratorPowerReady p mi s) (ht : GeneratorPowerReady p mj t) : mi = mj := by
  have positive : 0 < p.len / 8 := by rcases p.width with h | h | h <;> omega
  have ls : (word s.mem (off p.B pWorkspace) (slot (p.len / 8) Public.aN)).toNat =
      Spec.Dsa.decodeBE p.pb % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.len / 8) _ _ _ positive, hs.child.modulus]
  have lt : (word t.mem (off p.B pWorkspace) (slot (p.len / 8) Public.aN)).toNat =
      Spec.Dsa.decodeBE p.pb % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.len / 8) _ _ _ positive, ht.child.modulus]
  have hi := hs.child.inverse
  have hj := ht.child.inverse
  rw [ls] at hi
  rw [lt] at hj
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact p.pOdd) hi hj

theorem generatorPower_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two GeneratorPowerBefore) (Impl.Dsa.X86_64.Generation.generatorPower Sq.mm M.mm)
      (fun _ _ => True) := by
  apply (PublicPower.corePublicPow_ct M Sq (a := ⟨.input .g, .pLen⟩)
    (b := ⟨.input .x, .pLen⟩) (output := ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩)
    (o := pWorkspace) (by trivial) (by trivial) (by change VG.Impl.Dsa.Generation.Layout.g < 2 ^ 31; decide) (by taint_decide)).mono
  · intro s t ⟨p, ⟨mi, hs⟩, ⟨mj, ht⟩⟩
    have eq := generatorPower_inverse hs ht
    subst mj
    exact ⟨(p.powerCall mi, p.eb), ⟨generatorPower_call hs, rfl⟩, ⟨generatorPower_call ht, rfl⟩⟩
  · exact fun _ _ h => h

end VG.Proof.Dsa.X86_64.Generation
