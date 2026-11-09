module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamInit
import VerifiedGarbage.Proof.Framework.Block

/-! The middle four rows of the native product. -/

-- separate module: instantiate the common invariant at the two middle chunks
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def stage2Code : List Instr := pair2Code++(spillPair .x17 .x19 16++loadPair 32)
def stage4Code : List Instr := pair4Code++(spillPair .x20 .x21 32++loadPair 48)

theorem stage2_ok {s₀ s : State} {pa pt : Addr} {B : Nat}
    (ha : Ptr s₀ .x1 pa 72) (ht : PtrW s₀ .x27 pt 64)
    (stable : StableInput s₀ pa pt) (inv : StreamInv s₀ pa pt B 2 row2In s) :
    WP isa (.block stage2Code) s (StreamInv s₀ pa pt B 4 row4In) := by
  exact stream_step ha ht stable inv (by decide) (out:=pair2Out) (r0:=.x17) (r1:=.x19)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (arithmetic_frame inv.b inv.zero (by decide) (by decide) (pair2_value s inv.zero))

theorem stage4_ok {s₀ s : State} {pa pt : Addr} {B : Nat}
    (ha : Ptr s₀ .x1 pa 72) (ht : PtrW s₀ .x27 pt 64)
    (stable : StableInput s₀ pa pt) (inv : StreamInv s₀ pa pt B 4 row4In s) :
    WP isa (.block stage4Code) s (StreamInv s₀ pa pt B 6 row6In) := by
  exact stream_step ha ht stable inv (by decide) (out:=pair4Out) (r0:=.x20) (r1:=.x21)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (arithmetic_frame inv.b inv.zero (by decide) (by decide) (pair4_value s inv.zero))

def stream6Code : List Instr := firstStreamCode++(stage2Code++stage4Code)

theorem stream6_ok {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt) :
    WP isa (.block stream6Code) s (StreamInv s pa pt (wordsVal s.mem pb 0 9) 6 row6In) := by
  rw [stream6Code,WP.block_append_iff]
  refine WP.mono (stream_init ha hb ht stable) fun u inv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (stage2_ok ha ht stable inv) fun v inv' => ?_
  exact stage4_ok ha ht stable inv'

end VG.Proof.Mont.AArch64.P521Field
