module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Montgomery
public import VerifiedGarbage.Proof.MillerRabin.X86.ArgumentState
public import VerifiedGarbage.Proof.Bignum.X86.RtCall
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Initialize the shared Montgomery call's small argument frame. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation
open VG.Proof.MillerRabin.X86
open VG.Proof.Mont.X86

theorem montgomery_stores {f s : State} {values constants : Nat → BitVec 32} {first count : Nat}
    (H : ArgumentState f values first s) (bound : first + count ≤ 9)
    (eq : ∀ i, first ≤ i → i < first + count → constants i = values i)
    (low : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32)
    (fr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (montgomeryStores constants first count)) s
      (ArgumentState f values (first + count)) := by
  induction count generalizing first s with
  | zero => exact WP.block_nil (by simpa only [Nat.add_zero] using H)
  | succ count ih =>
    simp only [montgomeryStores, List.cons_append, List.nil_append]
    refine wp_movS rfl fun t U _ => ?_
    have T := H.of_keeps (U.keeps.mono (by decide)) U.mem
    refine T.store (by omega) low fr (U.gpr.trans (eq first (by omega) (by omega))) fun u HU => ?_
    exact (show first + 1 + count = first + (count + 1) by omega) ▸
      ih HU (by omega) (fun i hi hj => eq i (by omega) (by omega))

theorem montgomery_arguments {f : State} {n o a b : Nat}
    (low : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32)
    (fr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (montgomeryArgs n o a b)) f fun g =>
      ArgumentState f (fun i => if i = 0 then f.gpr .edi else montgomeryWord n o a b i) 9 g := by
  let values := fun i => if i = 0 then f.gpr .edi else montgomeryWord n o a b i
  have H := ArgumentState.initial f values
  unfold montgomeryArgs
  refine H.store (by decide) low fr rfl fun s HS => ?_
  exact montgomery_stores HS (by decide) (fun i hi _ => by
    simp only [show i ≠ 0 by omega, ite_false]) low fr

theorem montgomery_arguments_ready {f : State} {n o a b : Nat}
    (low : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32)
    (fr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (montgomeryArgs n o a b)) f fun g =>
      Keeps [.eax, .edx] f g ∧ Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem g.mem ∧
      ∀ i < 9, g.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        VG.Proof.Bignum.X86.RtCall.callArg (f.gpr .edi) (BitVec.ofNat 32 (montgomeryBytes / 8))
          n (VG.Impl.Mont.X86.Dynamic.slot n 0) 0 montgomeryScratch
          (VG.Impl.Mont.X86.Dynamic.slot n o) (VG.Impl.Mont.X86.Dynamic.slot n a)
          (VG.Impl.Mont.X86.Dynamic.slot n b) i := by
  refine WP.mono (montgomery_arguments low fr) fun g H => ⟨H.keeps, H.frame, ?_⟩
  intro i hi
  rw [H.words i hi]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Dsa.X86.Generation
