module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The witness mask stores through a public workspace-array pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.Rsa.Mont (arrAt)

structure MaskStoreData where
  base : BitVec 32
  capacity : Nat
  words : Nat
  index : Nat

def MaskStoreStart (p : MaskStoreData) (s : State) : Prop :=
  ArithmeticReady p.base p.capacity p.words s ∧ s.gpr .r5 = BitVec.ofNat 32 p.index

private def MaskStoreHead (p : MaskStoreData) (s : State) : Prop :=
  s.gpr .r4 = p.base + BitVec.ofNat 32 (arrAt p.words 1) ∧ s.gpr .r5 = BitVec.ofNat 32 p.index

private theorem loadBase_ok (p : MaskStoreData) (s : State) (h : MaskStoreStart p s) :
    WP isa (.block [.ldrSp .r0 0]) s (MaskStoreStart p) := by
  have raw : WP isa (.block [.ldrSp .r0 0]) s fun t =>
      (t.gpr .r0 = p.base ∧ t.mem = s.mem) ∧ Rest [.r0] s t := by
    refine withRest_all [.r0] ?_ (by rfl) (by rfl)
    ffrun [BitVec.add_zero, h.1.stackRead, h.1.saved]
  exact WP.mono raw (fun _ post => ⟨h.1.of_mem post.1.2 post.2 post.1.1,
    (post.2.gpr .r5 (by simp)).trans h.2⟩)

private theorem loadArray_ok (p : MaskStoreData) (s : State) (h : MaskStoreStart p s) :
    WP isa (.block [.ldr .r4 .r0 72]) s (MaskStoreHead p) := by
  have fits : arrAt p.words 8 ≤ 8 * p.capacity := h.1.width ▸ h.1.layout.2.2.1
  have size : 128 ≤ 8 * p.capacity := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem p.base h.1.workspace.nowrap (Nat.le_refl _) h.1.layout
  rw [h.1.width] at header
  have addr72 : State.addr (p.base + 72#32) = off (State.addr p.base) 72 :=
    VG.Arm.addr_add (by have := h.1.workspace.nowrap; omega)
  have raw : WP isa (.block [.ldr .r4 .r0 72]) s fun t =>
      t.gpr .r4 = p.base + BitVec.ofNat 32 (arrAt p.words 1) ∧ Rest [.r4] s t := by
    refine withRest_all [.r4] ?_ (by rfl) (by rfl)
    ffrun [h.1.ptr, addr72, h.1.workspace.read (off := 72) (by omega), header.array 1 (by decide)]
  exact WP.mono raw (fun _ post => ⟨post.1, (post.2.gpr .r5 (by simp)).trans h.2⟩)

theorem witnessMaskStore_ct : RelCT isa (Two MaskStoreStart)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskStore) (fun _ _ => True) := by
  have base : RelCT isa (Two MaskStoreStart) (.block [.ldrSp .r0 0]) (Two MaskStoreStart) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) loadBase_ok
  have array : RelCT isa (Two MaskStoreStart) (.block [.ldr .r4 .r0 72]) (Two MaskStoreHead) := by
    refine two_piece [.r0] ?_ (by taint_decide) loadArray_ok
    intro _ _ _ left right r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact left.1.ptr.trans right.1.ptr.symm
  have tail : RelCT isa (Two MaskStoreHead)
      (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskStore.drop 2)) (fun _ _ => True) := by
    refine two_taint [.r4, .r5] ?_ (by taint_decide)
    intro _ _ _ left right r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact left.1.trans right.1.symm
    · exact left.2.trans right.2.symm
  exact RelCT.block_append (base.seq (RelCT.block_append (array.seq tail)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
