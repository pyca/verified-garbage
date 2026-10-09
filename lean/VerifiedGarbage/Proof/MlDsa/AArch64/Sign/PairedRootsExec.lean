import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
import VerifiedGarbage.Proof.Framework.AArch64.Call

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64

/-- Executing within the caller's writable regions and reserved stack
cannot alter the separate immutable paired inverse table. -/
theorem PairedRoots.exec {S : Nat} {s u : State} {code : Prog isa} {tr : List Leak}
    (h : PairedRoots S s) (he : Exec isa code s tr u)
    (hd : 16*code.aarch64Depth≤S) (hS : S<2^64) : PairedRoots S u := by
  have hf := Frame.below_mono (VG.AArch64.Exec.frameSp he (by omega)) hd hS
  obtain ⟨hr,hw,hsp⟩ := VG.AArch64.Exec.rdwr he
  have hy := VG.AArch64.Exec.syms he
  refine ⟨?_,by simpa only [hy] using h.fit,?_,?_,?_⟩
  · intro i hi
    rw [hy,hf.readW (r:=⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩)
      (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)]
    · exact h.held i hi
    · intro r hm
      rcases List.mem_append.mp hm with hm|hm
      · exact h.writable r hm
      · obtain rfl := List.mem_singleton.mp hm
        exact h.stack
  · simpa only [hy,hr,hw] using h.readable
  · simpa only [hy,hw] using h.writable
  · simpa only [hy,hsp] using h.stack

theorem WP.pairedRoots {S : Nat} {s : State} {code : Prog isa} {post : State → Prop}
    (hw : WP isa code s post) (h : PairedRoots S s)
    (hd : 16*code.aarch64Depth≤S) (hS : S<2^64) :
    WP isa code s fun u=>post u ∧ PairedRoots S u := by
  obtain ⟨tr,u,he,hpost⟩ := hw
  exact ⟨tr,u,he,hpost,h.exec he hd hS⟩

end VG.Proof.MlDsa.AArch64.Sign
