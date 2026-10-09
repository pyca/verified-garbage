import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsFrame

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64

/-- A proved stack-depth bound preserves immutable root tables across an
entire existing phase, even when its semantic postcondition omits a frame. -/
theorem StaticRoots.execution {S : Nat} {s t : State} {code : Prog isa} {trace : List Leak}
    (h : StaticRoots S s) (he : Exec isa code s trace t)
    (hd : 16*code.aarch64Depth≤S) (hS : S<2^64) : StaticRoots S t := by
  have hf := Frame.below_mono (VG.AArch64.Exec.frameSp he (by omega)) hd hS
  obtain ⟨hr,hw,hsp⟩ := VG.AArch64.Exec.rdwr he
  have preserve {name : String} {words : List (BitVec 64)} (ht : StaticTable S name words s) :
      StaticTable S name words t := by
    apply ht.frame hf ?_ hr hw hsp (VG.AArch64.Exec.syms he)
    intro r hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ht.writable r hm
    · obtain rfl := List.mem_singleton.mp hm
      exact ht.stack
  exact ⟨preserve h.forward,preserve h.inverse⟩

theorem StaticRoots.phase {S : Nat} {s : State} {code : Prog isa} {Q : State → Prop}
    (h : StaticRoots S s) (hd : 16*code.aarch64Depth≤S) (hS : S<2^64)
    (hc : WP isa code s Q) : WP isa code s fun t => Q t ∧ StaticRoots S t := by
  obtain ⟨trace,t,he,hq⟩ := hc
  exact ⟨trace,t,he,hq,h.execution he hd hS⟩

end VG.Proof.MlDsa.AArch64.Sign
