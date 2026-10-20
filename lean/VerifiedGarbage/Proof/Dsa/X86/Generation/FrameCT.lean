module
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords

/-! # Relate public frame words while allowing unused frame contents to differ -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure PublicFrame where
  base : Addr
  words : Nat → BitVec 32

def FrameAt (slots : List Nat) (p : PublicFrame) (s : State) : Prop :=
  SearchFrame s p.base ∧ ∀ i ∈ slots, s.mem.readW (off p.base (4 * i)) 32 = p.words i

theorem frameAt_pins (slots : List Nat) : Pins (FrameAt slots) [.esp] := by
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (hs.1.esp_toNat.trans ht.1.esp_toNat.symm)

theorem FrameAt.keep {slots : List Nat} {p : PublicFrame} {s t : State} {rs : List Reg}
    (R : FrameAt slots p s) (mem : t.mem = s.mem) (K : Keeps rs s t) (sp : .esp ∉ rs) : FrameAt slots p t :=
  ⟨R.1.keeps K sp, by intro i hi; rw [mem]; exact R.2 i hi⟩

def observedWords (base : Addr) (s : State) : Nat → BitVec 32 := fun i => s.mem.readW (off base (4 * i)) 32

theorem observedWords_rep (base : Addr) (s : State) : FrameWords s.mem base (observedWords base s) := fun _ _ => rfl
end VG.Proof.Dsa.X86.Generation
