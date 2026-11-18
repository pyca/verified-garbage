module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomMask
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! ### `Dsa.X86_64.RandomDraw`, which only this module used -/

section

/-! A full scalar draw: copy, account for bytes, compare and update fuel. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_draw_full_ok {s : State} {B R Q : Addr} {used draws : Nat} {qBytes rand : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hR : word s.mem B Random.oRand = R)
    (hrlen : word s.mem B Random.oRandLen = BitVec.ofNat 64 rand.length)
    (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 (VG.Proof.Dsa.significant qBytes).1)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 qBytes.length)
    (hm : word s.mem B Random.oMask = randomMaskValue (VG.Proof.Dsa.significant qBytes).2.toNat)
    (hq : word s.mem B Random.oQ = Q + BitVec.ofNat 64
      (qBytes.length - (VG.Proof.Dsa.significant qBytes).1))
    (hd : word s.mem B Random.oDraws = BitVec.ofNat 64 draws)
    (hrand : Src s B Random.frameBytes R rand) (hqs : Src s B Random.frameBytes Q qBytes)
    (hqlen : qBytes.length ≤ 32) (hrbound : rand.length < 2 ^ 64)
    (hpos : 0 < (VG.Proof.Dsa.significant qBytes).1)
    (hfull : used + (VG.Proof.Dsa.significant qBytes).1 ≤ rand.length)
    (hdpos : 0 < draws) (hdbound : draws < 2 ^ 64) :
    WP isa Random.draw s fun t => ∃ m : Mem, ∃ copied : List Byte,
      copied.length = (VG.Proof.Dsa.significant qBytes).1 ∧
      (∀ i (hi : i < copied.length), m
        (off B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1) + BitVec.ofNat 64 i) = copied[i]) ∧
      Spec.Dsa.decodeBE copied = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qBytes)
        ((rand.drop used).take (VG.Proof.Dsa.significant qBytes).1) ∧
      Outside B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1)
        (VG.Proof.Dsa.significant qBytes).1 s.mem m ∧
      t.mem = randomDrawFinishMem
        (m.writeW (off B Random.oUsed) (BitVec.ofNat 64 (used + copied.length))) B
        (decide (0 < Spec.Dsa.decodeBE copied ∧ Spec.Dsa.decodeBE copied < Spec.Dsa.decodeBE qBytes)) draws ∧
      Keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] s t := by
  let n := (VG.Proof.Dsa.significant qBytes).1
  have hnfit : n ≤ qBytes.length := VG.Proof.Dsa.significant_fits qBytes
  unfold Random.draw
  refine WP.seq (WP.mono (random_drawHead_ok hs hsp hrlen hu hn (by omega_using [hfull]) hrbound (by omega_using [hrbound, hfull]))
    fun a ⟨hac, ham, hka⟩ => ?_)
  change a.cf = some (decide (rand.length - used < n)) at hac
  have hshort : ¬ rand.length - used < n := by omega_using [hfull]
  refine WP.ite false (by simp only [eval, hac, hshort, decide_false])
    (fun h => Bool.noConfusion h) (fun _ => ?_)
  have has := hs.congr hka.2.2
  have hasp := (hka.gpr (by decide)).trans hsp
  have harand := hrand.congrK (show InScr B Random.frameBytes s.mem a.mem from by
    rw [ham]; exact InScr.refl _ _ _) hka
  refine WP.seq (WP.mono (random_copy_draw_ok has hasp
    (by rw [ham]; exact hR) (by rw [ham]; exact hu) (by rw [ham]; exact hn)
    (by rw [ham]; exact hl) (by rw [ham]; exact hm) harand hqlen hpos hfull)
    fun b ⟨copied, hclen, hcv, hcdec, hbf, hkb⟩ => ?_)
  have hbk := hka.trans hkb
  have hbs := hs.congr hbk.2.2
  have hbsp := (hbk.gpr (by decide)).trans hsp
  have hbf' : Outside B 200 32 s.mem b.mem := by
    rw [← ham]
    exact hbf.mono (by omega_using [hnfit]) (by omega_using [hqlen, hnfit])
  have hbu : word b.mem B Random.oUsed = BitVec.ofNat 64 used := by
    rw [hbf'.word (by decide) (by decide)]; exact hu
  have hbn : word b.mem B Random.oWidth = BitVec.ofNat 64 n := by
    rw [hbf'.word (by decide) (by decide)]; exact hn
  refine WP.seq (WP.mono (random_used_ok hbs hbsp hbu hbn)
    fun c ⟨hcm, hkc⟩ => ?_)
  have hck := hbk.trans hkc
  have hcs := hs.congr hck.2.2
  have hcsp := (hck.gpr (by decide)).trans hsp
  have hcf : Outside B Random.oUsed 8 b.mem c.mem := by
    rw [hcm]; exact writeW_outside _ _ _ (by decide)
  have hcqsrc := hqs.congrK
    ((InScr.of_outside hbf' (by decide)).trans (InScr.of_outside hcf (by decide))) hck
  have hcl : word c.mem B Random.oQLen = BitVec.ofNat 64 qBytes.length := by
    rw [hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hl
  have hcn : word c.mem B Random.oWidth = BitVec.ofNat 64 n := by
    rw [hcf.word (by decide) (by decide)]; exact hbn
  have hcq : word c.mem B Random.oQ = Q + BitVec.ofNat 64 (qBytes.length - n) := by
    rw [hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hq
  have hccv : ∀ i (hi : i < copied.length), c.mem
      (off B (200 + qBytes.length - n) + BitVec.ofNat 64 i) = copied[i] := by
    intro i hi
    rw [hcf _ (by
      rw [random_nonce_offset B hnfit hqlen (by omega_using [hclen, hi])]
      right
      unfold Random.oUsed
      omega_using [hnfit])]
    exact hcv i hi
  refine WP.seq (WP.mono (random_check_candidate_ok hcs hcsp hcl hcn hcq hcqsrc
      hqlen hpos hclen rfl hccv)
    fun d ⟨hdz, hdm, hkd⟩ => ?_)
  have hdk := hck.trans hkd
  have hdd : word d.mem B Random.oDraws = BitVec.ofNat 64 draws := by
    rw [hdm, hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hd
  refine WP.mono (random_drawFinish_ok (hs.congr hdk.2.2)
    ((hdk.gpr (by decide)).trans hsp) hdd hdz hdpos hdbound)
    fun t ⟨htm, hkt⟩ => ?_
  refine ⟨b.mem, copied, hclen, hcv, hcdec, (by rw [← ham]; exact hbf), ?_, (hdk.trans hkt).mono (by decide)⟩
  rw [htm, hdm, hcm, hclen]

end VG.Proof.Dsa.X86_64

end

end


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
      rw [(writeW_outside _ C.B _ (by decide)).word (by decide) (by decide), (hcopy.mono (o' := 200) (n' := 32) (by have := VG.Proof.Dsa.significant_fits C.qBytes; omega_using [this]) (by have := C.qlen; have := VG.Proof.Dsa.significant_fits C.qBytes; omega_arith)).word (by decide) (by decide)]
      exact hstatus
    rw [he]
  · intro i hi
    have hnfit : n ≤ C.qBytes.length := VG.Proof.Dsa.significant_fits C.qBytes
    have ho : ofs C.B (off C.B (200 + C.qBytes.length - n) + BitVec.ofNat 64 i) =
        200 + C.qBytes.length - n + i := random_nonce_offset C.B hnfit C.qlen (by omega_using [hclen, hi])
    rw [htm', random_drawFinish_outside _ C.B accepted draws _ (by rw [ho]; right; omega_using [hnfit]),
      (writeW_outside _ C.B _ (by decide)) _ (by rw [ho]; right; unfold Random.oUsed; omega_using [hnfit])]
    exact hcv i hi

end VG.Proof.Dsa.X86_64
