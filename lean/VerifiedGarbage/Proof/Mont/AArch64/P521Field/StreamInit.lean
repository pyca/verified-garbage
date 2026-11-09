module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamInvariant
import VerifiedGarbage.Proof.Framework.Omega

/-! Establish the streaming invariant after the first sixteen product bytes. -/

-- separate module: bootstrap the common streamed-product invariant
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def firstStreamCode : List Instr :=
  (row0Loads++pair0Code)++(spillPair .x15 .x16 0++loadPair 16)

theorem stream_init {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt) :
    WP isa (.block firstStreamCode) s (StreamInv s pa pt (wordsVal s.mem pb 0 9) 2 row2In) := by
  have hread : ∀m,Outside pt 0 16 s.mem m →
      word m pa 16=word s.mem pa 16 ∧ word m pa 24=word s.mem pa 24 := by
    intro m hm
    have hwide := hm.mono (o':=0) (n':=64) (by decide) (by decide)
    exact ⟨stable m hwide 16 (by decide),stable m hwide 24 (by decide)⟩
  refine WP.mono (chunk_ok ha ht (by decide) (by decide) (by decide) (by decide)
    (r0:=.x15) (r1:=.x16) (out:=pair0Out) (next:=row2In)
    (by decide) rfl (by decide) (by decide) (by decide) hread (firstPair_loaded ha hb))
    fun t ⟨prod,a0,a1,b,z,k,om⟩ => ?_
  refine ⟨?_,b,z,a0,a1,om.mono (by decide) (by decide),k.mono (by decide)⟩
  exact prod

end VG.Proof.Mont.AArch64.P521Field
