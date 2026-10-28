module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.TimingSeg
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Array 6 zeroed, seeded or set to one reads the same addresses in every run

The taint analysis takes the header's pointers and width for secret: each
loop and store is checked with the registers it addresses through public,
which every run holds the same, as correctness gives (`seg`). -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.PrepareRt
open VG.Proof.RsaKeyGen.X86 (seg rawBlock ptr_value)
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)

/-- Prepared, for some candidate. -/
def Held (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s

theorem edi_at {g : Geometry} {s : State} (C : Context g s) : s.gpr .edi = BitVec.ofNat 32 g.W.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [C.base, BitVec.toNat_ofNat, Nat.add_zero]

theorem nat_at {x : BitVec 32} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)]

/-- A segment that addresses through `edi` alone. -/
theorem baseSeg {g : Geometry} {X Y : State → Prop} {c : Prog isa} (C : ∀ s, X s → Context g s)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr [.edi])) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) :=
  seg [.edi] (fun _ => BitVec.ofNat 32 g.W.toNat) (fun s S r mem => by
    obtain rfl := List.mem_singleton.mp mem; exact edi_at (C s S)) raw run

/-- A segment that addresses through one pointer. -/
theorem ptrSeg {g : Geometry} {X Y : State → Prop} {c : Prog isa} (r : Reg) (x : Nat)
    (P : ∀ s, X s → PtrAt s g.W r x)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr [r])) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) :=
  seg [r] (fun _ => BitVec.ofNat 32 (g.W.toNat + x)) (fun s S r' mem => by
    obtain rfl := List.mem_singleton.mp mem; exact ptr_value (P s S)) raw run

section
variable {g : Geometry} {capacity : Nat} {p : BitVec 32}

/-- About to zero array 6. -/
def ZeroAt (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Held g capacity p s ∧ PtrAt s g.W .ebp (g.array 6) ∧ (s.gpr .ecx).toNat = 4 * g.words ∧ s.gpr .eax = 0

theorem zeroLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.ebp, .ecx])) zeroLoop (fun _ _ => True) :=
  (erased_relCT (σ := τr []) zeroLoop zeroLoop (VG.Taint.hintOf taint (τr [.ebp, .ecx]) (Code.erase zeroLoop))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem zero_trace (v : g.Valid) :
    RelCT isa (fun s t => Held g capacity p s ∧ Held g capacity p t) zero
      (fun u z => Held g capacity p u ∧ Held g capacity p z) := by
  unfold zero
  refine RelCT.seq (R := fun u z => ZeroAt g capacity p u ∧ ZeroAt g capacity p z)
    (baseSeg (fun _ ⟨_, S⟩ => S.context) (rawBlock (by decide +kernel)) fun s ⟨c, S⟩ =>
      WP.mono (zeroArgs_ok v S.context) fun _ ⟨P, count, zero, M, K⟩ =>
        ⟨⟨c, S.keepSame K (by decide) (by decide) M⟩, P, count, zero⟩) ?_
  refine seg [.ebp, .ecx] (fun r => if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 6)
    else BitVec.ofNat 32 (4 * g.words)) (fun s S r mem => ?_) zeroLoop_raw fun s ⟨⟨c, S⟩, P, count, zero⟩ =>
      WP.mono (zeroLoop_run v S P count zero) fun _ ⟨T, _⟩ => ⟨c, T⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact ptr_value S.2.1
  · exact nat_at S.2.2.1

/-- About to set the top word. -/
def TopAt (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Held g capacity p s ∧ PtrAt s g.W .ebp (g.array 6) ∧ s.gpr .edx = BitVec.ofNat 32 (8 * g.w)

theorem seed_trace (v : g.Valid) :
    RelCT isa (fun s t => Held g capacity p s ∧ Held g capacity p t) seed
      (fun u z => Held g capacity p u ∧ Held g capacity p z) := by
  unfold seed top
  refine RelCT.seq (zero_trace v) (RelCT.block_append
    (RelCT.seq (R := fun u z => TopAt g capacity p u ∧ TopAt g capacity p z) ?_ ?_))
  · exact baseSeg (fun _ ⟨_, S⟩ => S.context) (rawBlock (by decide +kernel)) fun s ⟨c, S⟩ =>
      WP.mono (topArgs_ok v S.context) fun _ ⟨P, D, M, K⟩ => ⟨⟨c, S.keepSame K (by decide) (by decide) M⟩, P, D⟩
  refine seg [.ebp, .edx] (fun r => if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 6)
    else BitVec.ofNat 32 (8 * g.w)) (fun s S r mem => ?_) (rawBlock (by decide +kernel))
    fun s ⟨⟨c, S⟩, P, D⟩ => WP.mono (topStore_ok v S P D) fun _ ⟨T, _⟩ => ⟨c, T⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact ptr_value S.2.1
  · exact S.2.2

/-- About to store one. -/
def OneAt (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Held g capacity p s ∧ PtrAt s g.W .ebp (g.array 6)

theorem one_trace (v : g.Valid) :
    RelCT isa (fun s t => Held g capacity p s ∧ Held g capacity p t) one
      (fun u z => Held g capacity p u ∧ Held g capacity p z) := by
  unfold one
  refine RelCT.seq (zero_trace v) (RelCT.block_append
    (RelCT.seq (R := fun u z => OneAt g capacity p u ∧ OneAt g capacity p z) ?_ ?_))
  · exact baseSeg (fun _ ⟨_, S⟩ => S.context) (rawBlock (by decide +kernel)) fun s ⟨c, S⟩ =>
      WP.mono (WitnessRt.ptr_short v S.context 6 (by decide) .ebp) fun _ ⟨P, M, K⟩ =>
        ⟨⟨c, S.keepSame K (by decide) (by decide) M⟩, P⟩
  exact ptrSeg .ebp (g.array 6) (fun _ S => S.2) (rawBlock (by decide +kernel)) fun s ⟨⟨c, S⟩, P⟩ =>
    WP.mono (oneStore_ok v S P) fun _ ⟨T, _⟩ => ⟨c, T⟩

end

end VG.Proof.RsaKeyGen.X86.PrepareRt
