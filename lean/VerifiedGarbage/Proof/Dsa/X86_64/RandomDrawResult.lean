module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr

/-! Value and status observations after one complete draw. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def RandomNonceValue (C : RandomContext) (k : Nat) (s : State) : Prop :=
  ∃ copied : List Byte, copied.length = (VG.Proof.Dsa.significant C.qBytes).1 ∧
    (∀ i (hi : i < copied.length), s.mem
      (off C.B (200 + C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1) + BitVec.ofNat 64 i) = copied[i]) ∧
    Spec.Dsa.decodeBE copied = k

theorem RandomNonceValue.congr {C : RandomContext} {k : Nat} {s t : State}
    (h : RandomNonceValue C k s) (hm : t.mem = s.mem) : RandomNonceValue C k t := by
  obtain ⟨bs, hl, hv, hd⟩ := h
  exact ⟨bs, hl, by rw [hm]; exact hv, hd⟩

def randomNextCandidate (C : RandomContext) (used : Nat) : Nat :=
  Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
    ((C.rand.drop used).take (VG.Proof.Dsa.significant C.qBytes).1)

theorem random_draw_full_result {C : RandomContext} {used draws : Nat} {s : State}
    (hr : RandomReady C used draws s) (hstatus : word s.mem C.B Random.oStatus = 4)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hdpos : 0 < draws) (hdbound : draws < 2 ^ 64) :
    WP isa Random.draw s fun t =>
      let accepted := decide (0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes)
      RandomReady C (used + (VG.Proof.Dsa.significant C.qBytes).1)
        (if accepted then draws else draws - 1) t ∧
      word t.mem C.B Random.oStatus = (if accepted then 1 else if draws = 1 then 0 else 4) ∧
      RandomNonceValue C (randomNextCandidate C used) t := by
  refine WP.mono (random_draw_full_ok hr.scr hr.sp hr.rand hr.randLen hr.usedWord hr.width
    hr.qLen hr.mask hr.q hr.draws hr.randSrc hr.qSrc C.qlen C.randBound C.positive hfull hdpos hdbound)
    fun t ⟨m, copied, hclen, hcv, hcdec, hcopy, htm, hkt⟩ => ?_
  let n := (VG.Proof.Dsa.significant C.qBytes).1
  let accepted := decide (0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes)
  have htm' : t.mem = randomDrawFinishMem
      (m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + n))) C.B accepted draws := by
    rw [htm, hclen, hcdec]; rfl
  refine ⟨hr.after_draw accepted hfull hcopy htm' hkt, ?_, copied, hclen, ?_, hcdec⟩
  · rw [htm', random_drawFinish_status]
    have he : word (m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + n))) C.B Random.oStatus = 4 := by
      rw [(writeW_outside _ C.B _ (by decide)).word (by decide) (by decide), (hcopy.mono (o' := 200) (n' := 32) (by have := VG.Proof.Dsa.significant_fits C.qBytes; omega) (by have := C.qlen; have := VG.Proof.Dsa.significant_fits C.qBytes; omega)).word (by decide) (by decide)]
      exact hstatus
    rw [he]
  · intro i hi
    have hnfit : n ≤ C.qBytes.length := VG.Proof.Dsa.significant_fits C.qBytes
    have ho : ofs C.B (off C.B (200 + C.qBytes.length - n) + BitVec.ofNat 64 i) =
        200 + C.qBytes.length - n + i := random_nonce_offset C.B hnfit C.qlen (by omega)
    rw [htm', random_drawFinish_outside _ C.B accepted draws _ (by rw [ho]; right; omega),
      (writeW_outside _ C.B _ (by decide)) _ (by rw [ho]; right; unfold Random.oUsed; omega)]
    exact hcv i hi

end VG.Proof.Dsa.X86_64
