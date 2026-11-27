module
public import VerifiedGarbage.Proof.MlKem.X86_64.VLay

import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: code with MXCSR `0x1FBF`

ML-KEM's code sets no MXCSR of its own: its dispatchers run `vg_mcdt_enter`
first. Its arithmetic once ran inside a `withMxcsr`, which loaded MXCSR
through the eight bytes `mxR` of `scratch`; `noMx_ok` states what its proofs
need in the shape they had then.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-! ## MXCSR -/

/-- The bytes of `scratch` through which ML-KEM's arithmetic once loaded MXCSR. -/
abbrev mxR (sP : Addr) : Region := ⟨sP + BitVec.ofNat 64 768, 8⟩

theorem mx_sub (sP : Addr) : Region.Sub (mxR sP) (pR sP) := Offset.sub_base sP (by decide)

/-- What the proofs of ML-KEM's arithmetic need, in the shape they had when it
ran inside a `withMxcsr`: `c` runs from `s` itself, which differs from `s`
in no register and no byte, and leaves `mxR` as it finds it. -/
theorem noMx_ok {c : Prog isa} {sP : Addr} {s : State} {Q : State → Prop}
    (hc : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxR sP] s.mem s1.mem → WP isa c s1 Q) :
    WP isa c s fun s' => ∃ s2, Q s2 ∧ Frame [mxR sP] s2.mem s'.mem ∧ Keep [] s2 s' :=
  WP.mono (hc s (Keep.refl _ _) (Frame.refl _ _)) fun s' h => ⟨s', h, Frame.refl _ _, Keep.refl _ _⟩

/-! ## Regions of `scratch` -/

theorem pR_sub_tab (sP : Addr) : Region.Sub ⟨sP, 256⟩ (pR sP) := Region.sub_prefix (by decide)

theorem pR_sub_S (sP : Addr) : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by decide)

/-- The regions of `scratch` within it, and `f`. -/
theorem frame_fs {fP sP : Addr} {m m' : Mem} {rs : List Region} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (pR fP) ∨ Region.Sub r (pR sP)) : Frame [pR fP, pR sP] m m' :=
  h.sub fun r hr => (hs r hr).elim (fun h => ⟨_, List.mem_cons_self .., h⟩)
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

end VG.Proof.MlKem.X86_64
