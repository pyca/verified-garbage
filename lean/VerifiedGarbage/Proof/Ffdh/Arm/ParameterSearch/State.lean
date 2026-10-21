module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Params
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller

/-! The native search retains its full public tape while advancing an offset and u64 budget. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)

structure SearchBuffers (p : SearchParams) (s : State) : Prop where
  controller : Controller p.control s
  output : Workspace s p.c.out p.c.length
  used : Workspace s p.c.usedPtr 8
  scratch : Workspace s p.c.base (8 * p.c.capacity)
  tapeRead : InRegions (s.rd ++ s.wr) (State.addr p.c.tape) p.c.bytes.length
  tapeBytes : Spec.Rsa.bytesAt s.mem (State.addr p.c.tape) p.c.bytes.length = p.c.bytes
  stack : InRegions (s.rd ++ s.wr) (State.addr s.sp) 24
  below : 208 ≤ s.sp.toNat
  stackSeparate : ∀ r ∈ [⟨State.addr p.c.out, p.c.length⟩, ⟨State.addr p.c.usedPtr, 8⟩,
    ⟨State.addr p.c.base, 8 * p.c.capacity⟩, ⟨State.addr p.control, 128⟩,
    ⟨State.addr p.c.tape, p.c.bytes.length⟩],
    (⟨State.addr s.sp, 24⟩ : Region).Disjoint r ∧ (FrameStack.belowA s.sp 208).Disjoint r

structure SearchLive (p : SearchParams) (used remaining : Nat) (s : State) : Prop where
  buffers : SearchBuffers p s
  usedBound : used ≤ p.c.bytes.length
  remainingBound : remaining ≤ p.attempts
  counter : s.mem.readW (State.addr p.control) 64 = BitVec.ofNat 64 remaining
  width : s.mem.readW (VG.Proof.Mont.off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.c.length
  entropy : s.mem.readW (VG.Proof.Mont.off (State.addr p.control) 16) 64 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)
  saved : ∀ j ∈ searchSlots, lowWord s.mem p.control j = searchValues p used j

def searchClobbers : List Reg := [.r0, .r1, .r2, .r3, .r9, .r10, .r11, .r12, .lr]

def searchOutput (p : SearchParams) (result : Spec.Ffdh.ParameterSearchResult) (m : Mem) : Prop :=
  Spec.Rsa.bytesAt m (State.addr p.c.out) p.c.length = match result with
    | .accepted prime _ => Spec.Rsa.i2osp prime p.c.length
    | _ => List.replicate p.c.length 0

def searchPolicy (p : SearchParams) (result : Spec.Ffdh.ParameterSearchResult) : List (BitVec 64) :=
  [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.c.length,
    BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits), BitVec.ofNat 64 result.requested]

structure SearchDone (p : SearchParams) (result : Spec.Ffdh.ParameterSearchResult) (s : State) : Prop where
  buffers : SearchBuffers p s
  usedBound : result.used ≤ p.c.bytes.length
  usedPtr : lowWord s.mem p.control 6 = p.c.usedPtr
  used : lowWord s.mem p.control 4 = BitVec.ofNat 32 result.used
  status : lowWord s.mem p.control 13 = BitVec.ofNat 32 result.status
  policy : Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 = searchPolicy p result
  output : searchOutput p result s.mem

end VG.Proof.Ffdh.Arm.ParameterSearch
