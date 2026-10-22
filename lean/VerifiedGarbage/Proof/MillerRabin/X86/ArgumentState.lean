module

public import VerifiedGarbage.Proof.MillerRabin.X86.Pointer
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! # An invariant while assembling the shared Montgomery call's arguments

Each store extends a prefix of initialized arguments. A single induction
invariant tracks their values and the frame, rather than expanding nine
nested memory updates at every call site.
-/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86

structure ArgumentState (f : State) (values : Nat → BitVec 32) (n : Nat) (s : State) : Prop where
  keeps : Keeps [.eax, .edx] f s
  frame : Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem s.mem
  words : ∀ i < n, s.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 = values i

namespace ArgumentState

theorem initial (f : State) (values : Nat → BitVec 32) : ArgumentState f values 0 f :=
  ⟨Keeps.refl _ _, Frame.refl _ _, by intro i hi; omega⟩

theorem of_keeps {f s t : State} {values : Nat → BitVec 32} {n : Nat}
    (h : ArgumentState f values n s) (K : Keeps [.eax, .edx] s t) (m : t.mem = s.mem) :
    ArgumentState f values n t :=
  ⟨h.keeps.trans K, m ▸ h.frame, fun i hi => m ▸ h.words i hi⟩

theorem read_source {f s : State} {values : Nat → BitVec 32} {n : Nat}
    (h : ArgumentState f values n s) {m : MemOp} {v : BitVec 32}
    (hb : m.base ∉ [.eax, .edx]) (hr : readSrc f (.mem m) = some v)
    (apart : Region.Disjoint ⟨f.ea m, 4⟩ ⟨(f.gpr .esp).setWidth 64, 36⟩) :
    readSrc s (.mem m) = some v := by
  have ea : s.ea m = f.ea m := by
    simp only [State.ea, h.keeps.1 m.base hb]
  have mem : s.mem.readW (f.ea m) 32 = f.mem.readW (f.ea m) 32 :=
    h.frame.readW (r := ⟨f.ea m, 4⟩)
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
      (by intro r hr; rw [List.mem_singleton.mp hr]; exact apart) (by decide)
  simpa only [readSrc, State.load32, ea, h.keeps.2.1, h.keeps.2.2, mem] using hr

theorem store {f s : State} {values : Nat → BitVec 32} {n : Nat} {r : Reg}
    (h : ArgumentState f values n s) (hn : n < 9)
    (low : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32)
    (fr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr)
    (value : s.gpr r = values n) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, ArgumentState f values (n + 1) t → WP isa (.block is) t Q) :
    WP isa (.block (.store (sp (4 * n)) r :: is)) s Q := by
  obtain ⟨ea, wr⟩ := VG.Proof.Bignum.X86.PublicRt.frame_store
    (by rw [h.keeps.1 .esp (by decide)])
    (by rw [h.keeps.1 .esp (by decide)]; exact low)
    (by rw [h.keeps.2.2]; exact fr) (k := 4 * n) (by omega)
  refine wp_storeS ea wr fun t M => k t ⟨h.keeps.trans (M.keeps _), ?_, ?_⟩
  · rw [M.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega : 4 * n + 4 ≤ 36) (by omega))
  · intro i hi
    rw [M.mem, value]
    by_cases he : i = n
    · subst i
      exact Mem.readW_writeW_self32 _ _ _
    · rw [VG.Proof.Bignum.X86.PublicRt.frame_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.words i (by omega)

end ArgumentState
end VG.Proof.MillerRabin.X86
