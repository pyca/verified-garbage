module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Representation

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationForwardRotate
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block

/-! Alias-safe in-place workspace representation boundaries around field calls. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime value)
open VG.Proof.Ed25519.AArch64
open VG.Impl.Mont.AArch64 (loadsR storesR)

abbrev representationRegs := VG.Impl.Weierstrass.AArch64.P521Native.representationRegs

theorem representation_regs_value (s : State) :
    value ((List.range 9).map (fun j => s.gpr (representationReg j)))=regsVal s representationRegs := rfl

abbrev representationMemoryCode := VG.Impl.Weierstrass.AArch64.P521Native.representationMemoryCode

theorem representation_memory_ok (code : List Instr) (f : Nat → Nat) (clob : List Reg)
    (hr : Reg.x0∉clob) (hc : ∀r∈representationRegs,r∈clob)
    (convert : ∀s : State,regsVal s representationRegs<fieldPrime →
      WP isa (.block code) s fun t => regsVal t representationRegs=f (regsVal s representationRegs) ∧
        regsVal t representationRegs<fieldPrime ∧ Keeps clob s t)
    {s : State} {base : Addr} {size d : Nat} (hs : Scr s base size)
    (hd : d+72≤size) (hd8 : d%8=0) (bound : wordsVal s.mem base d 9<fieldPrime) :
    WP isa (.block (representationMemoryCode code d)) s fun t =>
      wordsVal t.mem base d 9=f (wordsVal s.mem base d 9) ∧ wordsVal t.mem base d 9<fieldPrime ∧
      KeepRegs clob s t ∧ Outside base d 72 s.mem t.mem := by
  rw [representationMemoryCode,VG.Impl.Weierstrass.AArch64.P521Native.representationMemoryCode,WP.block_append_iff]
  refine WP.mono (loadsR_ok representationRegs hs.ptr (by simpa only [show representationRegs.length=9 from rfl] using hd)
    hd8 (by decide) (by decide)) fun u ⟨loaded,ku,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (convert u (by rw [loaded]; exact bound)) fun v ⟨value,boundV,kv⟩ => ?_
  have kept : Keeps clob s v := (ku.mono hc).trans kv
  have hp := hs.ptrW.of_keepRegs (Keeps.regs kept) hr
  refine WP.mono (storesR_ok representationRegs hp (by simpa only [show representationRegs.length=9 from rfl] using hd)
    hd8 (by decide)) fun t ⟨stored,kt,ot⟩ => ?_
  simp only [show representationRegs.length=9 from rfl] at stored ot
  rw [loaded] at value
  exact ⟨stored.trans value,stored ▸ boundV,(Keeps.regs kept).trans (kt.mono (by simp)),
    by rw [kept.mem] at ot; exact ot⟩

theorem representation_from_memory {s : State} {base : Addr} {size d : Nat} (hs : Scr s base size)
    (hd : d+72≤size) (hd8 : d%8=0) (bound : wordsVal s.mem base d 9<fieldPrime) :
    WP isa (.block (representationMemoryCode representationFromCode d)) s fun t =>
      wordsVal t.mem base d 9=fromMontValue (wordsVal s.mem base d 9) ∧ wordsVal t.mem base d 9<fieldPrime ∧
      KeepRegs representationClob s t ∧ Outside base d 72 s.mem t.mem := by
  apply representation_memory_ok representationFromCode fromMontValue representationClob (by decide) (by decide)
    (fun s bound => ?_) hs hd hd8 bound
  have h := representation_from_value s (by rwa [representation_regs_value])
  exact WP.mono h fun t ⟨v,b,k,_⟩ => by
    rw [representation_regs_value,representation_regs_value] at v
    rw [representation_regs_value] at b
    exact ⟨v,b,k⟩

theorem representation_to_memory {s : State} {base : Addr} {size d : Nat} (hs : Scr s base size)
    (hd : d+72≤size) (hd8 : d%8=0) (bound : wordsVal s.mem base d 9<fieldPrime) :
    WP isa (.block (representationMemoryCode representationToCode d)) s fun t =>
      wordsVal t.mem base d 9=toMontValue (wordsVal s.mem base d 9) ∧ wordsVal t.mem base d 9<fieldPrime ∧
      KeepRegs representationToClob s t ∧ Outside base d 72 s.mem t.mem := by
  apply representation_memory_ok representationToCode toMontValue representationToClob (by decide) (by decide)
    (fun s bound => ?_) hs hd hd8 bound
  have h := representation_to_value s (by rwa [representation_regs_value])
  exact WP.mono h fun t ⟨v,b,k,_⟩ => by
    rw [representation_regs_value,representation_regs_value] at v
    rw [representation_regs_value] at b
    exact ⟨v,b,k⟩

end VG.Proof.Mont.AArch64.P521Field
