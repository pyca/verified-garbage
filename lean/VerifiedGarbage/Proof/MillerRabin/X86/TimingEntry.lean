module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryValues
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingCoreState
import VerifiedGarbage.Proof.MillerRabin.X86.EntryArgs
import VerifiedGarbage.Proof.MillerRabin.X86.EntryMarker

/-! # The reviewed input contract initializes each run's private timing invariant -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.RsaKeyGen VG.Impl.MillerRabin.X86

def entrySecret (s : State) : CoreSecret :=
  ⟨initialValues s 0, initialValues s, (fun _ => 0), mrA (initialValues s 0) % 64, (entered s).mem⟩

theorem Entry.coreMath {s : State} (E : Entry s) : CoreMath (geometry s) (entrySecret s) := by
  have minimum : 3 ≤ initialValues s 0 := E.prepared.1
  have odd : initialValues s 0 % 2 = 1 := E.prepared.2.1
  have lt : initialValues s aX < initialValues s 0 := E.prepared.2.2.2.1
  have one : initialValues s aOne = 2 ^ (64 * (geometry s).w) % initialValues s 0 := E.prepared.2.2.2.2.1
  refine ⟨odd, lt, ?_, Nat.mod_lt _ (by decide), E.marker⟩
  change initialValues s aOne < initialValues s 0
  rw [one]
  exact Nat.mod_lt _ (by omega)

theorem Entry.base {s : State} (E : Entry s) :
    WP isa (.block [.mov .edi (.mem (at_ .esp 20))]) (entered s) fun t =>
      CoreStart (geometry s) (arg s 1).toNat ((entered s).gpr .esp) (entrySecret s) t ∧
      Keeps [.edi] (entered s) t := by
  have read := E.read_arg (i := 0) (by decide : 0 < 2)
  change readSrc (entered s) (.mem (at_ .esp 20)) = some (arg s 0) at read
  refine wp_movS read fun t T _ => WP.block_nil ?_
  have mem : t.mem = (entered s).mem := T.mem
  have workspace : (⟨wsOf s, lenOf s⟩ : Region) ∈ t.wr := by
    rw [T.wr, entered, Compact.entered, pushed_wr, E.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have base : PtrAt t (wsOf s) .edi 0 := by
    rw [PtrAt, T.gpr, Nat.add_zero, E.ws_toNat]
    exact (Nat.mod_eq_of_lt (arg s 0).isLt).symm
  refine ⟨⟨⟨E.data mem workspace base, E.modulus mem, ?_, ?_⟩, E.coreMath, mem⟩, T.keeps⟩
  · apply E.caller.keepFrame T.keeps (by decide)
    rw [T.mem]
    exact Frame.refl _ _
  · intro j known
    change j ∈ [0, 5, 9, 10, 27] at known
    simp only [List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl | rfl <;> decide

theorem geometry_eq {s t : State} (a0 : arg s 0 = arg t 0) (a1 : arg s 1 = arg t 1)
    (width : Proof.Rsa.Mont.wOf s.mem (wsOf s) = Proof.Rsa.Mont.wOf t.mem (wsOf t)) : geometry s = geometry t := by
  unfold geometry
  rw [width, wsOf, wsOf, lenOf, lenOf, a0, a1]

end VG.Proof.MillerRabin.X86
