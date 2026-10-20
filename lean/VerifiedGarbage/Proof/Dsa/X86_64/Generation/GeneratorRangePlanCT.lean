module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorEvaluateCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorWorkspaceCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding

/-! # Instantiate range timing with the exact generator inputs and computed output -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.Generation.Layout VG.Impl.RsaOaep.X86_64

def GeneratorPlan.rangeWorkspace (p : GeneratorPlan) (xb : List Byte) (hx : xb.length = p.len) :
    GeneratorWorkspacePublic where
  frame := {
    B := p.A, F := p.F, arena := p.B, hp := p.hp, Z := p.Z, w := p.len / 8
    pb := p.pb, xb := xb
    pLength := by rw [p.pLength]; rcases p.width with h | h | h <;> rw [h] <;> decide
    xLength := hx.trans p.pLength.symm
    separate := p.frameHeaders }
  base := p.arithmeticBase.symm
  room := p.workspaceRoom
  lower := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  upper := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  outside := p.frameOutside

theorem generatorRange_plan {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    {xb : List Byte} (hx : xb.length = p.len) (result : Bool)
    (h : GeneratorMemory p W s)
    (src : Src s p.A p.Z (if result then off p.B g else p.hp) xb) :
    GeneratorWorkspaceBefore (p.len / 8) p.len result (p.rangeWorkspace xb hx) s := by
  obtain ⟨V, R⟩ := h.rep
  exact ⟨⟨h.layout.rsp, fun k hk => h.layout.ld (by unfold frameBytes; omega),
    (R.fr 5 (by decide)).trans h.base, (R.fr 21 (by decide)).trans h.input,
    h.pArithmetic, src, fun _ => p.pOdd⟩, h.arithmetic, rfl, p.pLength⟩

theorem generatorInputRange_ct (len : Nat) (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame len false)
      (fun _ _ => True) := by
  apply two_map (fun p : GeneratorPlan => p.rangeWorkspace p.hb p.hLength) ?_
    (generatorRangeFromFrame_ct len false hl)
  intro p s ⟨⟨W, h⟩, he⟩
  have ready := generatorRange_plan p.hLength false h h.hArithmetic
  subst len
  exact ready

def GeneratorOutputBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  GeneratorBefore len p s ∧ Spec.Rsa.bytesAt s.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value

theorem generatorOutput_source {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s)
    (hg : Spec.Rsa.bytesAt s.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value) :
    Src s p.A p.Z (off p.B g) (Spec.Dsa.encodeBE p.len p.value) := by
  have hlen := VG.Proof.Dsa.encodeBE_length p.len p.value
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => p.gArithmeticOutside i (hlen ▸ hi)⟩
  · obtain ⟨r, hr, hc⟩ := h.gWrite i (hlen ▸ hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have eq := congrArg (fun bs : List Byte => bs[i]?) hg
    simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range,
      show i < p.len from hlen ▸ hi, ↓reduceIte, Option.map_some, List.getElem?_eq_getElem hi,
      Option.some.injEq] using eq

theorem generatorOutputRange_ct (len : Nat) (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorOutputBefore len)) (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame len true)
      (fun _ _ => True) := by
  apply two_map (fun p : GeneratorPlan => p.rangeWorkspace (Spec.Dsa.encodeBE p.len p.value)
    (VG.Proof.Dsa.encodeBE_length p.len p.value)) ?_ (generatorRangeFromFrame_ct len true hl)
  intro p s ⟨⟨⟨W, h⟩, he⟩, hg⟩
  have ready := generatorRange_plan (VG.Proof.Dsa.encodeBE_length p.len p.value) true h
    (generatorOutput_source h hg)
  subst len
  exact ready

end VG.Proof.Dsa.X86_64.Generation
