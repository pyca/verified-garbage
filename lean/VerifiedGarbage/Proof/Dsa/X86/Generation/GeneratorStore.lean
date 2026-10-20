module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateStore
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReadyMemory

/-! # Serialize a successful generator without invalidating the prepared modulus -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem generatorStore_ok {s : State} {G : PrimeConfig} {frame : Addr} {parent : BitVec 32}
    (R : PrimeReady G s) (F : SearchFrame s frame)
    (saved : s.mem.readW (off frame 20) 32 = parent)
    (fit : (parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).toNat + G.len ≤ 2 ^ 32)
    (write : ∀ e k, e + k ≤ G.len → InRegions s.wr
      ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).setWidth 64 + BitVec.ofNat 64 e) k)
    (apart : Region.Disjoint
      ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).setWidth 64, G.len⟩ ⟨G.base, G.size⟩) :
    WP isa (generatorStore G.len) s fun t => PrimeReady G t ∧
      Spec.Rsa.bytesAt t.mem ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).setWidth 64) G.len =
        Spec.Dsa.encodeBE G.len (wordsVal s.mem G.base (slot G.n 6) G.n) ∧
      Outside ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).setWidth 64) 0 G.len s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have room : slot G.n 6 + 8 * G.n ≤ G.size := by
    have := slot_bound (n := G.n) (by decide : 6 < 9)
    have := R.context.size_le
    unfold stride at *
    omega
  unfold generatorStore
  refine WP.seq (WP.mono (bufferPointer_ok F saved .esi _) fun a ⟨si, mem, Ka⟩ => ?_)
  have S := R.context.scr.of_keeps Ka (by decide) (by decide)
  refine WP.mono (storePublic_ok S room G.lenMin (by unfold PrimeConfig.n; omega) G.lenWords
    (by rw [si]; exact fit) (by intro e k h; rw [Ka.2.2, si]; exact write e k h)
    (by
      rw [si]
      exact apart.symm.sub_left (Offset.sub_base _ room)))
    fun t ⟨value, O, Kt⟩ => ?_
  rw [si] at value O
  rw [mem] at value O
  have K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t :=
    (Ka.mono (by decide)).trans (Kt.mono (by decide))
  refine ⟨R.sameWorkspace ?_ K (by decide) (by decide), value, O, K⟩
  intro d hd
  have frame := copyOutside_frame O
  exact frame.readW (r := ⟨G.base, G.size⟩)
    (Offset.contains_base _ hd (by have := R.context.scr.nowrap; omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact apart.symm) (by decide)
end VG.Proof.Dsa.X86.Generation
