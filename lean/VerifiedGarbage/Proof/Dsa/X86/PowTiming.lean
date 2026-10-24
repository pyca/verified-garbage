module

public import VerifiedGarbage.Proof.Dsa.X86.PowCoreTiming
public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.PowCore

/-! # Constant-time traces of the shared IA-32 exponentiation body

Two runs from the same stack pointer and working space, each ready for the
body (`BodyIn`), leak the same trace: the saves read the argument and store
through public pointers, the core's traces agree (`core_relCT`), and it
leaves `edi` as it found it, through which the restores read. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

/-- What the body needs of a run on entry: the working space at its first argument, the 96 bytes
of stack below `esp` apart from it, and the modulus odd and above 1. -/
def BodyIn (n : Nat) (s : State) : Prop :=
  ∃ size, Entry s ((arg s 0).setWidth 64) size ∧ CallRoom (s.gpr .esp) ((arg s 0).setWidth 64) size ∧
    contextBytes n ≤ size ∧ 1 < wordsVal s.mem ((arg s 0).setWidth 64) (slot n 0) n ∧
    wordsVal s.mem ((arg s 0).setWidth 64) (slot n 0) n % 2 = 1

theorem edi_of_scr {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    s.gpr .edi = BitVec.ofNat 32 base.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := hs.edi_toNat
  have := (s.gpr .edi).isLt
  rw [hs.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem body_relCT (n e : Nat) (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg t 0) ∧ BodyIn n s ∧ BodyIn n t)
      (body n e) (fun _ _ => True) := by
  unfold body
  have saveCT : RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg t 0))
      (.block save) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    unfold save
    rw [List.append_assoc]
    exact RelCT.block_append (RelCT.seq (scratchArgument_relCT 0)
      (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl))
  have saved := (saveCT.mono (P' := fun (s t : State) => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg t 0) ∧ BodyIn n s ∧ BodyIn n t)
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) fun _ _ h => h).wpDep
    (F := fun (σ u : State) => CoreIn n ((arg σ 0).setWidth 64) (σ.gpr .esp) u ∧
      (∀ r ∈ calleeSaved, r ≠ .edi → u.gpr r = σ.gpr r))
    fun s t ⟨_, _, _, _, B₁, B₂⟩ => by
      have go : ∀ σ, BodyIn n σ → WP isa (.block save) σ fun u =>
          CoreIn n ((arg σ 0).setWidth 64) (σ.gpr .esp) u ∧ (∀ r ∈ calleeSaved, r ≠ .edi → u.gpr r = σ.gpr r) := by
        intro σ ⟨size, E, R, hz, hm1, hodd⟩
        have hz24 : 24 ≤ size := by simp only [contextBytes, slot, stride] at hz; omega
        refine WP.mono (save_ok E hz24) fun u ⟨Su, _, Ou, Ku⟩ => ?_
        have hv : wordsVal u.mem ((arg σ 0).setWidth 64) (slot n 0) n =
            wordsVal σ.mem ((arg σ 0).setWidth 64) (slot n 0) n := by
          rw [wordsVal_eq_val32, wordsVal_eq_val32]
          exact Ou.val32 (by simp only [slot]; omega) (by have := E.nowrap; simp only [slot, stride] at hz ⊢; omega)
        exact ⟨⟨size, _, Su, R, Ku.1 _ (by decide), hz, hv, hm1, hodd⟩,
          fun r hr hne => Ku.1 r (by revert hr hne; cases r <;> simp [calleeSaved])⟩
      exact ⟨go s B₁, go t B₂⟩
  refine VG.RelCT.seq (R := fun u v => ∃ p : Addr × BitVec 32, Both (CoreIn n p.1 p.2) u v)
    (saved.mono (fun _ _ h => h) fun u v ⟨_, σ₁, σ₂, ⟨SP, A0, _⟩, ⟨C₁, _⟩, ⟨C₂, _⟩⟩ =>
      ⟨((arg σ₁ 0).setWidth 64, σ₁.gpr .esp), C₁, by rw [A0, SP]; exact C₂⟩) ?_
  refine VG.RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) ?_
    ((checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) (by rfl) rfl).mono
      (fun _ _ h => h) (fun _ _ _ => trivial))
  refine VG.RelCT.exists_ fun p => ?_
  have go : ∀ u, CoreIn n p.1 p.2 u → WP isa (core n e) u fun w => w.gpr .edi = BitVec.ofNat 32 p.1.toNat := by
    intro u ⟨size, m, hs, R, esp, hz, hv, hm1, hodd⟩
    rw [← esp] at R
    exact WP.mono (core_ok hs R hz hn hn48 he hen hv hm1 hodd) fun w ⟨_, _, K⟩ => by
      rw [K.1 _ (by decide)]; exact edi_of_scr hs
  refine ((core_relCT (base := p.1) (sp := p.2) hn hn48 he hen).wp (F₁ := fun (w : State) => w.gpr .edi = BitVec.ofNat 32 p.1.toNat)
    (F₂ := fun (w : State) => w.gpr .edi = BitVec.ofNat 32 p.1.toNat) fun u v h => ⟨go u h.1, go v h.2⟩).mono
    (fun _ _ h => h) fun w₁ w₂ ⟨_, e₁, e₂⟩ => agree_regs (rs := [.edi]) fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      rw [e₁, e₂]

end VG.Proof.Dsa.X86.Pow
