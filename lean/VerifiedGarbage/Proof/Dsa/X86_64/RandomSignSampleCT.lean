module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawResult
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Dsa.X86_64.Random
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.Dsa.X86_64.Random
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToDual
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawResult
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding

/-! ### `Dsa.X86_64.RandomSampleCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.RandomSampleLoopCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.RandomSampleStep`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.RandomSamplePublic`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.RandomDrawCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.RandomDrawFinishCT`, which only this module used -/

section

/-! The draw's final branches reveal only acceptance and its public retry budget. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomDrawFinishPublic where
  B : Addr
  draws : Nat
  accept : Bool

def RandomDrawFinishPre (p : RandomDrawFinishPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  word s.mem p.B Random.oDraws = BitVec.ofNat 64 p.draws ∧
  s.zf = some (!p.accept) ∧ 0 < p.draws ∧ p.draws < 2 ^ 64

theorem random_drawFinish_ct : RelCT isa (Two RandomDrawFinishPre) Random.drawFinish (fun _ _ => True) := by
  unfold Random.drawFinish
  refine two_ite (fun p s t hs ht => by simp only [eval, hs.2.2.2.1, ht.2.2.2.1]) ?_ ?_
  · apply two_taint [.rsp] ?_ (by taint_decide)
    intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.1.2.1.trans ht.1.2.1.symm
  · refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rsp = p.B ∧
        s.zf = some (decide (p.draws = 1))) [.rsp] ?_ (by taint_decide) ?_) ?_
    · intro p s t hs ht r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hs.1.2.1.trans ht.1.2.1.symm
    · intro p s ⟨⟨hs, hsp, hd, _, hpos, hbound⟩, _⟩
      exact WP.mono (random_decrement_ok hs hsp hd hpos hbound)
        (fun _ ⟨_, hz, _, hk⟩ => ⟨(hk.gpr (by decide)).trans hsp, hz⟩)
    · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
      · apply two_taint [.rsp] ?_ (by taint_decide)
        intro p s t hs ht r hr
        rw [List.mem_singleton] at hr
        subst r
        exact hs.1.1.trans ht.1.1.symm
      · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomDrawCheckCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.RandomDrawCheck`, which only this module used -/

section

/-! Isolate the draw prefix before the acceptance branch. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomDrawCheck : Prog isa :=
  .seq Random.copy (.seq (.block [.mov .rax (.mem (Random.sp Random.oUsed)),
    .alu .add .rax (.mem (Random.sp Random.oWidth)), .store (Random.sp Random.oUsed) .rax]) Random.inRange)

theorem random_drawCheck_ok {C : RandomContext} {s : State} {used draws : Nat}
    (hr : RandomReady C used draws s)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length) :
    WP isa randomDrawCheck s fun t =>
      Scr t C.B Random.frameBytes ∧ t.gpr .rsp = C.B ∧
      word t.mem C.B Random.oDraws = BitVec.ofNat 64 draws ∧
      t.zf = some (!decide (0 < Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
        ((C.rand.drop used).take (VG.Proof.Dsa.significant C.qBytes).1) ∧
        Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
        ((C.rand.drop used).take (VG.Proof.Dsa.significant C.qBytes).1) < Spec.Dsa.decodeBE C.qBytes)) := by
  let B := C.B
  let Q := C.Q
  let qBytes := C.qBytes
  let n := (VG.Proof.Dsa.significant qBytes).1
  have hnfit := VG.Proof.Dsa.significant_fits qBytes
  have hs := hr.scr
  have hsp := hr.sp
  have hR := hr.rand
  have hu := hr.usedWord
  have hn := hr.width
  have hl := hr.qLen
  have hm := hr.mask
  have hq := hr.q
  have hd := hr.draws
  have hrand := hr.randSrc
  have hqs := hr.qSrc
  have hqlen := C.qlen
  have hpos := C.positive
  dsimp only [qBytes] at *
  unfold randomDrawCheck
  refine WP.seq (WP.mono (random_copy_draw_ok hs hsp
    hR hu hn
    hl hm hrand hqlen hpos hfull)
    fun b ⟨copied, hclen, hcv, hcdec, hbf, hkb⟩ => ?_)
  have hbk := hkb
  have hbs := hs.congr hbk.2.2
  have hbsp := (hbk.gpr (by decide)).trans hsp
  have hbf' : Outside B 200 32 s.mem b.mem := by
    exact hbf.mono (by omega_using [hnfit]) (by omega_using [hnfit, hqlen])
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
  refine WP.mono (random_check_candidate_ok hcs hcsp hcl hcn hcq hcqsrc
      hqlen hpos hclen rfl hccv)
    fun d ⟨hdz, hdm, hkd⟩ => ?_
  have hdk := hck.trans hkd
  have hdd : word d.mem B Random.oDraws = BitVec.ofNat 64 draws := by
    rw [hdm, hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hd
  exact ⟨hs.congr hdk.2.2, (hdk.gpr (by decide)).trans hsp, hdd,
    by rw [hdz, hcdec]⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomRangeCT`, which only this module used -/

section

/-! The range check leaks its public pointers and width only. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomRangePublic where
  B : Addr
  Q : Addr
  qLen : Nat
  width : Nat

def RandomRangePre (p : RandomRangePublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  word s.mem p.B Random.oQLen = BitVec.ofNat 64 p.qLen ∧
  word s.mem p.B Random.oWidth = BitVec.ofNat 64 p.width ∧
  word s.mem p.B Random.oQ = p.Q

def RandomRangeRegs (p : RandomRangePublic) (s : State) : Prop :=
  s.gpr .rdx = off p.B (Random.oNonce + p.qLen) ∧
  s.gpr .r10 = p.Q + BitVec.ofNat 64 p.width ∧ s.gpr .r11 = BitVec.ofNat 64 p.width

theorem random_inRange_ct : RelCT isa (Two RandomRangePre) Random.inRange (fun _ _ => True) := by
  unfold Random.inRange
  refine RelCT.seq (two_piece (Ψ := RandomRangeRegs) [.rsp] ?_ (by taint_decide) ?_) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.2.1.trans ht.2.1.symm
  · intro p s ⟨hs, hsp, hl, hn, hq⟩
    exact WP.mono (random_rangeInit_ok hs hsp hl hn hq) fun _ ⟨hd, h10, h11, _, _, _, _⟩ => ⟨hd, h10, h11⟩
  · apply two_taint [.r10, .rdx, .r11] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.1.trans ht.1.symm
    · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomCopyCT`, which only this module used -/

section

/-! Copying a masked draw leaks addresses and width, not random bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomCopyPublic where
  B : Addr
  R : Addr
  used : Nat
  qLen : Nat
  width : Nat

def RandomCopyPublic.src (p : RandomCopyPublic) : Addr := p.R + BitVec.ofNat 64 p.used
def RandomCopyPublic.dst (p : RandomCopyPublic) : Addr :=
  off p.B Random.oNonce + BitVec.ofNat 64 p.qLen - BitVec.ofNat 64 p.width

def RandomCopyPre (p : RandomCopyPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  word s.mem p.B Random.oRand = p.R ∧
  word s.mem p.B Random.oUsed = BitVec.ofNat 64 p.used ∧
  word s.mem p.B Random.oQLen = BitVec.ofNat 64 p.qLen ∧
  word s.mem p.B Random.oWidth = BitVec.ofNat 64 p.width ∧
  0 < p.width ∧ p.width < 2 ^ 64 ∧
  InRegions (s.rd ++ s.wr) p.src 1 ∧ InRegions s.wr p.dst 1

def RandomCopyMid (p : RandomCopyPublic) (s : State) : Prop :=
  s.gpr .rsp = p.B ∧ s.gpr .r10 = p.src ∧ s.gpr .rdx = p.dst ∧
  s.gpr .r11 = BitVec.ofNat 64 p.width

def RandomCopyTail (p : RandomCopyPublic) (s : State) : Prop :=
  s.gpr .r10 = p.src + 1 ∧ s.gpr .rdx = p.dst + 1 ∧
  s.gpr .r11 = BitVec.ofNat 64 (p.width - 1) ∧ s.zf = some (decide (p.width = 1))

private theorem header_ok {p : RandomCopyPublic} {s : State} (h : RandomCopyPre p s) :
    WP isa (.block Random.copyHeader) s (RandomCopyMid p) := by
  obtain ⟨hs, hsp, hr, hu, hl, hn, _⟩ := h
  refine WP.mono (WP.keep [.r10, .r11, .rdx] (Q := fun t =>
    t.gpr .r10 = p.src ∧ t.gpr .rdx = p.dst ∧ t.gpr .r11 = BitVec.ofNat 64 p.width) ?_ rfl)
    fun _ ⟨ht, hk⟩ => ⟨(hk.gpr (by decide)).trans hsp, ht⟩
  unfold Random.copyHeader Random.address RandomCopyPublic.src RandomCopyPublic.dst
  xrun [List.append_assoc, List.cons_append, List.nil_append, random_ea_sp, hsp,
    hs.ld (d := Random.oRand) (by decide), hs.ld (d := Random.oUsed) (by decide),
    hs.ld (d := Random.oWidth) (by decide), hs.ld (d := Random.oQLen) (by decide), hr, hu, hl, hn]
  rfl

private theorem init_tail {p : RandomCopyPublic} {s : State} (h : RandomCopyPre p s) :
    WP isa (.block Random.copyInit) s (RandomCopyTail p) := by
  obtain ⟨hs, hsp, hr, hu, hl, hn, hp, hb, hread, hwrite⟩ := h
  exact WP.mono (random_copyInit_ok hs hsp hr hu hn hl rfl rfl rfl hp hb hread hwrite)
    fun _ ⟨h10, hd, h11, hz, _, _⟩ => ⟨h10, hd, h11, hz⟩

theorem random_copy_ct : RelCT isa (Two RandomCopyPre) Random.copy (fun _ _ => True) := by
  unfold Random.copy
  refine RelCT.seq (two_post (Ψ := RandomCopyTail) ?_ (fun _ _ h => init_tail h)) ?_
  · unfold Random.copyInit
    apply RelCT.block_append
    refine RelCT.seq (two_piece (Ψ := RandomCopyMid) [.rsp] ?_ (by taint_decide)
      (fun _ _ h => header_ok h)) ?_
    · intro p s t hs ht r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hs.2.1.trans ht.2.1.symm
    · apply two_taint [.rsp, .r10, .rdx, .r11] ?_ (by taint_decide)
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm
  · unfold Random.copyRest
    refine two_ite (fun p s t hs ht => by simp only [eval, hs.2.2.2, ht.2.2.2]) ?_ ?_
    · apply two_taint [.r10, .rdx, .r11] ?_ (by taint_decide)
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.1.trans ht.1.1.symm
      · exact hs.1.2.1.trans ht.1.2.1.symm
      · exact hs.1.2.2.1.trans ht.1.2.2.1.symm
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomDrawPublic`, which this module and modules that import it used -/

section

/-! Public draw parameters, with random bytes existential in the state predicate. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

structure RandomDrawPublic where
  B : Addr
  R : Addr
  Q : Addr
  qBytes : List Byte
  randLen : Nat
  used : Nat
  draws : Nat
  qlen : qBytes.length ≤ 32
  positive : 0 < (VG.Proof.Dsa.significant qBytes).1
  randBound : randLen < 2 ^ 64
  usedBound : used ≤ randLen
  drawsPos : 0 < draws
  drawsBound : draws < 2 ^ 64

def RandomDrawPublic.width (p : RandomDrawPublic) : Nat := (VG.Proof.Dsa.significant p.qBytes).1

def RandomDrawPublic.context (p : RandomDrawPublic) (rand : List Byte)
    (hlen : rand.length = p.randLen) (m : Mem) : RandomContext where
  B := p.B
  initialMem := m
  R := p.R
  Q := p.Q
  qBytes := p.qBytes
  rand := rand
  qlen := p.qlen
  positive := p.positive
  randBound := by rw [hlen]; exact p.randBound

def RandomDrawPre (p : RandomDrawPublic) (s : State) : Prop :=
  ∃ rand, ∃ hlen : rand.length = p.randLen, ∃ m,
    RandomReady (p.context rand hlen m) p.used p.draws s

def RandomDrawFullPre (p : RandomDrawPublic) (s : State) : Prop :=
  RandomDrawPre p s ∧ p.used + p.width ≤ p.randLen

theorem RandomDrawPre.sp {p : RandomDrawPublic} {s : State} (h : RandomDrawPre p s) : s.gpr .rsp = p.B := by
  obtain ⟨_, _, _, hr⟩ := h
  exact hr.sp

end VG.Proof.Dsa.X86_64

end

end

/-! The copy-and-check prefix leaks only public addresses and widths. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def RandomDrawPublic.range (p : RandomDrawPublic) : RandomRangePublic :=
  ⟨p.B, p.Q + BitVec.ofNat 64 (p.qBytes.length - p.width), p.qBytes.length, p.width⟩

def RandomDrawCheckMid (p : RandomDrawPublic) (s : State) : Prop :=
  RandomRangePre p.range s ∧ word s.mem p.B Random.oUsed = BitVec.ofNat 64 p.used

theorem random_draw_copy_ct : RelCT isa (Two RandomDrawFullPre) Random.copy (fun _ _ => True) := by
  refine two_map (fun p => (⟨p.B, p.R, p.used, p.qBytes.length, p.width⟩ : RandomCopyPublic)) ?_ random_copy_ct
  intro p s ⟨⟨rand, hlen, m, hr⟩, hfull⟩
  have hn := VG.Proof.Dsa.significant_fits p.qBytes
  have hq := p.qlen
  have hp := p.positive
  refine ⟨hr.scr, hr.sp, hr.rand, hr.usedWord, hr.qLen, hr.width, hp, by dsimp only [RandomDrawPublic.width]; omega_using [hn, hq], ?_, ?_⟩
  · have hh := hr.randSrc.rd p.used (by dsimp only [RandomDrawPublic.context]; rw [hlen]; dsimp only [RandomDrawPublic.width] at hfull; omega_using [hfull, hp])
    exact hh
  · change InRegions s.wr (off p.B Random.oNonce + BitVec.ofNat 64 p.qBytes.length - BitVec.ofNat 64 p.width) 1
    unfold RandomDrawPublic.width
    rw [random_nonce_addr p.B hn]
    exact hr.scr.st8 (by dsimp only [Random.frameBytes, RandomDrawPublic.width]; omega_using [hq])

private theorem copy_mid {p : RandomDrawPublic} {s : State} (h : RandomDrawFullPre p s) :
    WP isa Random.copy s (RandomDrawCheckMid p) := by
  obtain ⟨⟨rand, hlen, m, hr⟩, hfull⟩ := h
  have hn := VG.Proof.Dsa.significant_fits p.qBytes
  have hq := p.qlen
  refine WP.mono (random_copy_draw_ok hr.scr hr.sp hr.rand hr.usedWord hr.width hr.qLen hr.mask
    hr.randSrc hq p.positive (by dsimp only [RandomDrawPublic.context]; rw [hlen]; exact hfull)) fun t ⟨_, _, _, _, hf, hk⟩ => ?_
  dsimp only [RandomDrawPublic.context] at hf
  have hf' : Outside p.B 200 32 s.mem t.mem := hf.mono (by omega_using [hn]) (by omega_using [hn, hq])
  have hw (d : Nat) (hd : d + 8 ≤ 200) : word t.mem p.B d = word s.mem p.B d :=
    hf'.word (Or.inl hd) (by omega_using [hd])
  exact ⟨⟨hr.scr.congr hk.2.2, (hk.gpr (by decide)).trans hr.sp,
    (hw _ (by decide)).trans hr.qLen, (hw _ (by decide)).trans hr.width,
    (hw _ (by decide)).trans hr.q⟩, (hw _ (by decide)).trans hr.usedWord⟩

private theorem used_range {p : RandomDrawPublic} {s : State} (h : RandomDrawCheckMid p s) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oUsed)),
      .alu .add .rax (.mem (Random.sp Random.oWidth)), .store (Random.sp Random.oUsed) .rax]) s
      (RandomRangePre p.range) := by
  obtain ⟨⟨hs, hsp, hl, hn, hq⟩, hu⟩ := h
  refine WP.mono (random_used_ok hs hsp hu hn) fun t ⟨hm, hk⟩ => ?_
  have hw (d : Nat) (hd : d + 8 ≤ 144 ∨ 152 ≤ d) (hb : d + 8 ≤ 2 ^ 64) :
      word t.mem p.B d = word s.mem p.B d := by
    rw [hm]
    exact (writeW_outside _ p.B _ (by decide)).word hd hb
  exact ⟨hs.congr hk.2.2, (hk.gpr (by decide)).trans hsp,
    (hw _ (by decide) (by decide)).trans hl,
    (hw _ (by decide) (by decide)).trans hn,
    (hw _ (by decide) (by decide)).trans hq⟩

theorem random_drawCheck_ct : RelCT isa (Two RandomDrawFullPre) randomDrawCheck (fun _ _ => True) := by
  unfold randomDrawCheck
  refine RelCT.seq (two_post random_draw_copy_ct (fun _ _ h => copy_mid h)) ?_
  refine RelCT.seq (two_piece (Ψ := fun p s => RandomRangePre p.range s) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => used_range h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.1.2.1.trans ht.1.2.1.symm
  · exact two_map RandomDrawPublic.range (fun _ _ h => h) random_inRange_ct

end VG.Proof.Dsa.X86_64

end

end

/-! A draw leaks its public bounds and the declassified acceptance decision. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomDrawDecisionPublic where
  draw : RandomDrawPublic
  accept : Bool

def randomDrawAccept (p : RandomDrawPublic) (rand : List Byte) : Bool :=
  let k := Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE p.qBytes) ((rand.drop p.used).take p.width)
  decide (0 < k ∧ k < Spec.Dsa.decodeBE p.qBytes)

def RandomDrawDecisionPre (p : RandomDrawDecisionPublic) (s : State) : Prop :=
  ∃ rand, ∃ hlen : rand.length = p.draw.randLen, ∃ m,
    RandomReady (p.draw.context rand hlen m) p.draw.used p.draw.draws s ∧
    (p.draw.used + p.draw.width ≤ p.draw.randLen → randomDrawAccept p.draw rand = p.accept)

theorem RandomDrawDecisionPre.drawPre {p : RandomDrawDecisionPublic} {s : State}
    (h : RandomDrawDecisionPre p s) : RandomDrawPre p.draw s := by
  obtain ⟨rand, hlen, m, hr, _⟩ := h
  exact ⟨rand, hlen, m, hr⟩

def RandomDrawHeadPost (p : RandomDrawDecisionPublic) (s : State) : Prop :=
  RandomDrawDecisionPre p s ∧ s.cf = some (decide (p.draw.randLen - p.draw.used < p.draw.width))

private theorem head_ok {p : RandomDrawDecisionPublic} {s : State} (h : RandomDrawDecisionPre p s) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oRandLen)),
      .alu .sub .rax (.mem (Random.sp Random.oUsed)), .alu .cmp .rax (.mem (Random.sp Random.oWidth))]) s
      (RandomDrawHeadPost p) := by
  obtain ⟨rand, hlen, m, hr, ha⟩ := h
  have hrlen : word s.mem p.draw.B Random.oRandLen = BitVec.ofNat 64 p.draw.randLen := by
    simpa only [RandomDrawPublic.context, hlen] using hr.randLen
  have hw := VG.Proof.Dsa.significant_fits p.draw.qBytes
  have hq := p.draw.qlen
  refine WP.mono (random_drawHead_ok hr.scr hr.sp hrlen hr.usedWord hr.width p.draw.usedBound p.draw.randBound
    (by dsimp only [RandomDrawPublic.context]; omega_using [hw, hq])) fun t ⟨hc, hm, hk⟩ => ?_
  exact ⟨⟨rand, hlen, m, hr.congr hm hk, ha⟩, hc⟩

private theorem full_of_head {p : RandomDrawDecisionPublic} {s : State}
    (h : RandomDrawHeadPost p s) (hc : isa.eval .b s = some false) :
    p.draw.used + p.draw.width ≤ p.draw.randLen := by
  simp only [eval, h.2, Option.some.injEq, decide_eq_false_iff_not] at hc
  have := p.draw.usedBound
  omega_using [hc, this]

def RandomDrawDecisionFull (p : RandomDrawDecisionPublic) (s : State) : Prop :=
  RandomDrawDecisionPre p s ∧ p.draw.used + p.draw.width ≤ p.draw.randLen

private theorem check_finish {p : RandomDrawDecisionPublic} {s : State} (h : RandomDrawDecisionFull p s) :
    WP isa randomDrawCheck s (RandomDrawFinishPre ⟨p.draw.B, p.draw.draws, p.accept⟩) := by
  obtain ⟨⟨rand, hlen, m, hr, ha⟩, hfull⟩ := h
  refine WP.mono (random_drawCheck_ok hr (by dsimp only [RandomDrawPublic.context]; rw [hlen]; exact hfull))
    fun t ⟨hs, hsp, hd, hz⟩ => ?_
  refine ⟨hs, hsp, hd, ?_, p.draw.drawsPos, p.draw.drawsBound⟩
  change t.zf = some (!p.accept)
  change t.zf = some (!(randomDrawAccept p.draw rand)) at hz
  rw [ha hfull] at hz
  exact hz

private theorem full_ct : RelCT isa (Two RandomDrawDecisionFull)
    (.seq randomDrawCheck Random.drawFinish) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map RandomDrawDecisionPublic.draw
    (fun _ _ h => ⟨h.1.drawPre, h.2⟩) random_drawCheck_ct) (fun _ _ h => check_finish h)) ?_
  exact two_map (fun p => (⟨p.draw.B, p.draw.draws, p.accept⟩ : RandomDrawFinishPublic))
    (fun _ _ h => h) random_drawFinish_ct

theorem random_draw_ct : RelCT isa (Two RandomDrawDecisionPre) Random.draw (fun _ _ => True) := by
  unfold Random.draw
  refine RelCT.seq (two_piece (Ψ := RandomDrawHeadPost) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => head_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.drawPre.sp.trans ht.drawPre.sp.symm
  · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
    · apply two_taint [.rsp] ?_ (by taint_decide)
      intro p s t hs ht r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hs.1.1.drawPre.sp.trans ht.1.1.drawPre.sp.symm
    · intro s t ts tt u v ⟨p, hs, ht⟩ es et
      have hp : Two RandomDrawDecisionFull s t :=
        ⟨p, ⟨hs.1.1, full_of_head hs.1 hs.2⟩, ht.1.1, full_of_head ht.1 ht.2⟩
      cases es with
      | seq sc sr => cases sr with
        | seq su sr => cases sr with
          | seq sk sf =>
            cases et with
            | seq tc tr => cases tr with
              | seq tu tr => cases tr with
                | seq tk tf =>
                  have hh := full_ct _ _ _ _ _ _ hp (.seq (.seq sc (.seq su sk)) sf)
                    (.seq (.seq tc (.seq tu tk)) tf)
                  simpa only [List.append_assoc] using hh

end VG.Proof.Dsa.X86_64

end

end

/-! The public sampling trace determines the next draw's declassified decision. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomSamplePublic where
  draw : RandomDrawPublic
  trace : List Nat
  valid : 1 < Spec.Dsa.decodeBE draw.qBytes

def RandomSampleTracePre (p : RandomSamplePublic) (s : State) : Prop :=
  ∃ rand, ∃ hlen : rand.length = p.draw.randLen, ∃ m,
    RandomReady (p.draw.context rand hlen m) p.draw.used p.draw.draws s ∧
    word s.mem p.draw.B Random.oStatus = 4 ∧
    (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE p.draw.qBytes) p.draw.draws (rand.drop p.draw.used)).trace = p.trace

def RandomSamplePublic.accept (p : RandomSamplePublic) : Bool := p.trace.head? == some 1

theorem RandomSampleTracePre.decision {p : RandomSamplePublic} {s : State} (h : RandomSampleTracePre p s) :
    RandomDrawDecisionPre ⟨p.draw, p.accept⟩ s := by
  obtain ⟨rand, hlen, m, hr, _, ht⟩ := h
  refine ⟨rand, hlen, m, hr, ?_⟩
  intro hfull
  have hwidth := VG.Proof.Dsa.random_drawBytes_scan p.draw.qBytes
  have hlen' : Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE p.draw.qBytes) ≤ (rand.drop p.draw.used).length := by
    rw [hwidth, List.length_drop, hlen]
    exact Nat.le_sub_of_add_le' hfull
  have hp := p.draw.drawsPos
  obtain ⟨fuel, he⟩ := Nat.exists_eq_succ_of_ne_zero (by omega_using [hp] : p.draw.draws ≠ 0)
  change p.draw.draws = fuel + 1 at he
  have hh := VG.Proof.Dsa.Random.sample_trace_head _ fuel _ p.valid hlen'
  rw [← he, ht, hwidth] at hh
  exact hh.symm

theorem RandomSampleTracePre.congr {p : RandomSamplePublic} {s t : State}
    (h : RandomSampleTracePre p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    RandomSampleTracePre p t := by
  obtain ⟨rand, hlen, m, hr, hs, ht⟩ := h
  exact ⟨rand, hlen, m, hr.congr hm hk, by rw [hm]; exact hs, ht⟩

def RandomSamplePublic.next (p : RandomSamplePublic)
    (hfull : p.draw.used + p.draw.width ≤ p.draw.randLen) (hf : 1 < p.draw.draws) : RandomSamplePublic where
  draw := { p.draw with
    used := p.draw.used + p.draw.width
    draws := p.draw.draws - 1
    usedBound := hfull
    drawsPos := by omega_using [hf]
    drawsBound := by have := p.draw.drawsBound; omega_using [this] }
  trace := p.trace.tail
  valid := p.valid

theorem random_sample_trace_next {p : RandomSamplePublic} {rand : List Byte}
    (hlen : rand.length = p.draw.randLen)
    (ht : (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE p.draw.qBytes) p.draw.draws (rand.drop p.draw.used)).trace = p.trace)
    (hfull : p.draw.used + p.draw.width ≤ p.draw.randLen) (hf : 1 < p.draw.draws)
    (ha : p.accept = false) :
    (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE p.draw.qBytes) (p.draw.draws - 1)
      (rand.drop (p.draw.used + p.draw.width))).trace = p.trace.tail := by
  have hw := VG.Proof.Dsa.random_drawBytes_scan p.draw.qBytes
  have hlen' : Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE p.draw.qBytes) ≤ (rand.drop p.draw.used).length := by
    rw [hw, List.length_drop, hlen]
    exact Nat.le_sub_of_add_le' hfull
  have he : p.draw.draws - 1 + 1 = p.draw.draws := by omega_using [hf]
  have hh := VG.Proof.Dsa.Random.sample_trace_retry _ (p.draw.draws - 1) _ p.valid hlen'
    (by rw [he, ht]; exact ha)
  rw [he, ht, hw, List.drop_drop] at hh
  exact hh.symm

end VG.Proof.Dsa.X86_64

end

end

/-! A draw's public status and the trace suffix retained after rejection. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomSampleStepStatus (p : RandomSamplePublic) : Nat :=
  if p.draw.used + p.draw.width ≤ p.draw.randLen then
    if p.accept then 1 else if p.draw.draws = 1 then 0 else 4
  else 2

def RandomSampleStepPost (p : RandomSamplePublic) (s : State) : Prop :=
  Scr s p.draw.B Random.frameBytes ∧ s.gpr .rsp = p.draw.B ∧
  word s.mem p.draw.B Random.oStatus = BitVec.ofNat 64 (randomSampleStepStatus p) ∧
  ∀ (hfull : p.draw.used + p.draw.width ≤ p.draw.randLen) (hf : 1 < p.draw.draws),
    p.accept = false → RandomSampleTracePre (p.next hfull hf) s

theorem random_sample_step {p : RandomSamplePublic} {s : State} (h : RandomSampleTracePre p s) :
    WP isa Random.draw s (RandomSampleStepPost p) := by
  obtain ⟨rand, hlen, m, hr, hs, ht⟩ := h
  have hwidth := VG.Proof.Dsa.significant_fits p.draw.qBytes
  have hqlen := p.draw.qlen
  by_cases hfull : p.draw.used + p.draw.width ≤ p.draw.randLen
  · have hacc : randomDrawAccept p.draw rand = p.accept := by
      have hh := VG.Proof.Dsa.Random.sample_trace_head (Spec.Dsa.decodeBE p.draw.qBytes) (p.draw.draws - 1)
        (rand.drop p.draw.used) p.valid (by
          rw [VG.Proof.Dsa.random_drawBytes_scan, List.length_drop, hlen]
          exact Nat.le_sub_of_add_le' hfull)
      rw [show p.draw.draws - 1 + 1 = p.draw.draws by have := p.draw.drawsPos; omega_using [this], ht,
        VG.Proof.Dsa.random_drawBytes_scan] at hh
      exact hh.symm
    refine WP.mono (random_draw_full_result hr hs
      (by dsimp only [RandomDrawPublic.context]; rw [hlen]; exact hfull) p.draw.drawsPos p.draw.drawsBound)
      fun t ⟨htr, hstatus, _⟩ => ?_
    change RandomReady (p.draw.context rand hlen m) (p.draw.used + p.draw.width)
      (if randomDrawAccept p.draw rand then p.draw.draws else p.draw.draws - 1) t at htr
    change word t.mem p.draw.B Random.oStatus =
      (if randomDrawAccept p.draw rand then 1 else if p.draw.draws = 1 then 0 else 4) at hstatus
    rw [hacc] at htr hstatus
    refine ⟨htr.scr, htr.sp, ?_, ?_⟩
    · unfold randomSampleStepStatus
      rw [ite_eq_left hfull]
      cases ha : p.accept <;> by_cases hf : p.draw.draws = 1 <;>
        simp only [ha, hf, ite_true, ite_false, Bool.false_eq_true] at hstatus ⊢ <;> exact hstatus
    · intro hf hn ha
      simp only [ha, Bool.false_eq_true, ite_false] at htr
      refine ⟨rand, hlen, m, htr, ?_, ?_⟩
      · change word t.mem p.draw.B Random.oStatus = 4
        rw [ha, ite_eq_right (by decide), ite_eq_right (by omega_using [hn] : p.draw.draws ≠ 1)] at hstatus
        exact hstatus
      · exact random_sample_trace_next hlen ht hf hn ha
  · have hshort : (p.draw.context rand hlen m).rand.length - p.draw.used <
        (VG.Proof.Dsa.significant (p.draw.context rand hlen m).qBytes).1 := by
      dsimp only [RandomDrawPublic.context]
      rw [hlen]
      have := p.draw.usedBound
      unfold RandomDrawPublic.width at hfull
      omega_using [hfull, this]
    refine WP.mono (random_draw_short_ok hr.scr hr.sp hr.randLen hr.usedWord hr.width hr.usedBound
      (p.draw.context rand hlen m).randBound (by dsimp only [RandomDrawPublic.context]; omega_using [hwidth, hqlen]) hshort)
      fun t ⟨_, hm, hk⟩ => ?_
    have htr := hr.after_status hm hk
    refine ⟨htr.scr, htr.sp, ?_, fun hf _ _ => False.elim (hfull hf)⟩
    rw [hm]
    change word (s.mem.writeW (off p.draw.B Random.oStatus) (2 : BitVec 64)) p.draw.B Random.oStatus = _
    rw [word_writeW_self, randomSampleStepStatus, ite_eq_right hfull]
    rfl

theorem RandomSampleStepPost.congr {p : RandomSamplePublic} {s t : State}
    (h : RandomSampleStepPost p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    RandomSampleStepPost p t :=
  ⟨h.1.congr hk.2.2, (hk.gpr (by decide)).trans h.2.1, by rw [hm]; exact h.2.2.1,
    fun hf hn ha => (h.2.2.2 hf hn ha).congr hm hk⟩

theorem random_sample_status_four {p : RandomSamplePublic} (h : randomSampleStepStatus p = 4) :
    p.draw.used + p.draw.width ≤ p.draw.randLen ∧ 1 < p.draw.draws ∧ p.accept = false := by
  unfold randomSampleStepStatus at h
  split at h
  next hf =>
    cases ha : p.accept <;> simp only [ha, Bool.false_eq_true, ite_true, ite_false] at h
    · have hp := p.draw.drawsPos
      by_cases hn : p.draw.draws = 1
      · rw [ite_eq_left hn] at h; contradiction
      · exact ⟨hf, by omega_using [hp, hn], rfl⟩
    · contradiction
  next => contradiction

end VG.Proof.Dsa.X86_64

end

end

/-! The sampling loop reveals only the specified sequence of draw decisions. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomSampleBody : Prog isa :=
  .seq Random.draw (.block [.mov .rax (.mem (Random.sp Random.oStatus)), .alu .cmp .rax (.imm 4)])

def RandomSampleTestPost (p : RandomSamplePublic) (s : State) : Prop :=
  RandomSampleStepPost p s ∧ s.zf = some (BitVec.ofNat 64 (randomSampleStepStatus p) == 4)

private theorem step_ct : RelCT isa (Two RandomSampleTracePre) randomSampleBody (fun _ _ => True) := by
  unfold randomSampleBody
  refine RelCT.seq (two_post (two_map (fun p => (⟨p.draw, p.accept⟩ : RandomDrawDecisionPublic))
    (fun _ _ h => h.decision) random_draw_ct) (fun _ _ h => random_sample_step h)) ?_
  apply two_taint [.rsp] ?_ (by taint_decide)
  intro p s t hs ht r hr
  rw [List.mem_singleton] at hr
  subst r
  exact hs.2.1.trans ht.2.1.symm

private theorem step_ok {p : RandomSamplePublic} {s : State} (h : RandomSampleTracePre p s) :
    WP isa randomSampleBody s (RandomSampleTestPost p) := by
  refine WP.seq (WP.mono (random_sample_step h) fun t ht => ?_)
  exact WP.mono (random_statusTest_ok ht.1 ht.2.1 ht.2.2.1)
    (fun _ ⟨hz, hm, hk⟩ => ⟨ht.congr hm hk, hz⟩)

private theorem status_bound (p : RandomSamplePublic) : randomSampleStepStatus p ≤ 4 := by
  unfold randomSampleStepStatus
  split
  · split
    · decide
    · split <;> decide
  · decide

def RandomSampleTraceAt (n : Nat) (p : RandomSamplePublic) (s : State) : Prop :=
  p.draw.draws = n ∧ RandomSampleTracePre p s

theorem random_sampleLoop_ct (n : Nat) :
    RelCT isa (Two (RandomSampleTraceAt n)) (.loop randomSampleBody .e)
      (Two fun (B : Addr) s => s.gpr .rsp = B) := by
  refine RelCT.loop (M := isa) (fun n => Two (RandomSampleTraceAt n)) ?_ n
  intro fuel
  have hc : RelCT isa (Two (RandomSampleTraceAt fuel)) randomSampleBody
      (Two fun p s => p.draw.draws = fuel ∧ RandomSampleTestPost p s) := by
    refine two_post (step_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.2) h) (fun _ _ _ => trivial)) ?_
    intro p s ⟨hn, hs⟩
    exact WP.mono (step_ok hs) fun _ ht => ⟨hn, ht⟩
  refine hc.mono (fun _ _ h => h) ?_
  intro s t ⟨p, ⟨hn, hs⟩, ⟨_, ht⟩⟩
  have he : isa.eval .e s = isa.eval .e t := by simp only [eval, hs.2, ht.2]
  refine ⟨he, fun _ => ⟨p.draw.B, hs.1.2.1, ht.1.2.1⟩, ?_⟩
  intro hcontinue
  have hfour : randomSampleStepStatus p = 4 := by
    simp only [eval, hs.2, Option.some.injEq, beq_iff_eq] at hcontinue
    have hn' := congrArg BitVec.toNat hcontinue
    have hb := status_bound p
    change randomSampleStepStatus p % 2 ^ 64 = 4 at hn'
    omega_using [hb, hn']
  obtain ⟨hfull, hf, ha⟩ := random_sample_status_four hfour
  refine ⟨p.draw.draws - 1, by omega_using [hn, hf], p.next hfull hf, ?_, ?_⟩
  · exact ⟨rfl, hs.1.2.2.2 hfull hf ha⟩
  · exact ⟨rfl, ht.1.2.2.2 hfull hf ha⟩

end VG.Proof.Dsa.X86_64

end

end

/-! The complete sampler's leakage is determined by its public decision trace. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def RandomSamplePre (p : RandomSamplePublic) (s : State) : Prop :=
  p.draw.draws = 128 ∧ ∃ rand, ∃ hlen : rand.length = p.draw.randLen, ∃ m draws,
    RandomReady (p.draw.context rand hlen m) p.draw.used draws s ∧
    (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE p.draw.qBytes) 128 (rand.drop p.draw.used)).trace = p.trace

private theorem init_ok {p : RandomSamplePublic} {s : State} (h : RandomSamplePre p s) :
    WP isa (.block [.mov .rax (.imm 128), .store (Random.sp Random.oDraws) .rax,
      .mov .rax (.imm 4), .store (Random.sp Random.oStatus) .rax]) s (RandomSampleTraceAt 128 p) := by
  obtain ⟨hn, rand, hlen, m, draws, hr, ht⟩ := h
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = (s.mem.writeW (off p.draw.B Random.oDraws) (128 : BitVec 64)).writeW
        (off p.draw.B Random.oStatus) (4 : BitVec 64)) (by
      xrun [random_ea_sp, hr.sp, hr.scr.st (d := Random.oDraws) (by decide),
        hr.scr.st (d := Random.oStatus) (by decide)]
      rfl) rfl) fun t ⟨hm, hk⟩ => ?_
  obtain ⟨htr, hs⟩ := random_sample_init_ready hr hm hk
  refine ⟨hn, rand, hlen, m, ?_, hs, ?_⟩
  · rw [hn]; exact htr
  · rw [hn]; exact ht

theorem random_sample_ct : RelCT isa (Two RandomSamplePre) Random.sample (fun _ _ => True) := by
  unfold Random.sample
  refine RelCT.seq (two_piece (Ψ := RandomSampleTraceAt 128) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => init_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    obtain ⟨_, _, _, _, _, hs, _⟩ := hs
    obtain ⟨_, _, _, _, _, ht, _⟩ := ht
    exact hs.sp.trans ht.sp.symm
  · refine RelCT.seq (random_sampleLoop_ct 128) ?_
    apply two_taint [.rsp] ?_ (by taint_decide)
    intro B s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomSampleAgreement`, which this module and modules that import it used -/

section

/-! Apply sampler leakage to contexts with independent secret tapes and memories. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_context_eq {C D : RandomContext}
    (hb : C.B = D.B) (hm : C.initialMem = D.initialMem)
    (hr : C.R = D.R) (hq : C.Q = D.Q) (hbytes : C.qBytes = D.qBytes) (hrand : C.rand = D.rand) : C = D := by
  cases C
  cases D
  cases hb
  cases hm
  cases hr
  cases hq
  cases hbytes
  cases hrand
  rfl

theorem random_sample_agreement {C D : RandomContext} {used da db : Nat} {s t : State}
    (hs : RandomReady C used da s) (ht : RandomReady D used db t)
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hB : C.B = D.B) (hR : C.R = D.R) (hQ : C.Q = D.Q) (hqBytes : C.qBytes = D.qBytes)
    (hlen : C.rand.length = D.rand.length)
    (htrace : (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE C.qBytes) 128 (C.rand.drop used)).trace =
      (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE D.qBytes) 128 (D.rand.drop used)).trace)
    {ts tt : List Leak} {u v : State} (es : Exec isa Random.sample s ts u) (et : Exec isa Random.sample t tt v) :
    ts = tt := by
  let p : RandomSamplePublic := {
    draw := {
      B := C.B
      R := C.R
      Q := C.Q
      qBytes := C.qBytes
      randLen := C.rand.length
      used := used
      draws := 128
      qlen := C.qlen
      positive := C.positive
      randBound := C.randBound
      usedBound := hs.usedBound
      drawsPos := by decide
      drawsBound := by decide }
    trace := (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE C.qBytes) 128 (C.rand.drop used)).trace
    valid := hq }
  have hcs : p.draw.context C.rand rfl C.initialMem = C :=
    random_context_eq rfl rfl rfl rfl rfl rfl
  have hds : p.draw.context D.rand hlen.symm D.initialMem = D :=
    random_context_eq hB rfl hR hQ hqBytes rfl
  have hp : Two RandomSamplePre s t := by
    refine ⟨p, ⟨rfl, C.rand, rfl, C.initialMem, da, ?_, rfl⟩,
      rfl, D.rand, hlen.symm, D.initialMem, db, ?_, ?_⟩
    · rw [hcs]; exact hs
    · rw [hds]; exact ht
    · change (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE C.qBytes) 128 (D.rand.drop used)).trace = _
      rw [hqBytes]
      exact htrace.symm
  exact (random_sample_ct _ _ _ _ _ _ hp es et).1

end VG.Proof.Dsa.X86_64

end

end

/-! Transfer public argument and trace agreement to the complete nonce sampler. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_draw_agree {s t : State} {used : Nat} (hpub : RandomSignPublicAgree s t)
    (htrace : (randomSignDraw (randomInput s) used).trace = (randomSignDraw (randomInput t) used).trace) :
    (randomSignDraw (randomInput s) used).used = (randomSignDraw (randomInput t) used).used ∧
      (randomSignDraw (randomInput s) used).scalar.isSome = (randomSignDraw (randomInput t) used).scalar.isSome ∧
      Random.sampleStatus (randomSignDraw (randomInput s) used) = Random.sampleStatus (randomSignDraw (randomInput t) used) := by
  have hq : (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key).params.q =
      (Spec.Dsa.privateKeyBytes (randomInput t).pLen (randomInput t).qLen (randomInput t).key).params.q := by
    rw [← random_q_decode, ← random_q_decode, hpub.qbytes]
  unfold randomSignDraw at htrace ⊢
  rw [hq] at htrace ⊢
  exact Random.sample_trace_agree htrace

theorem random_sign_sample_agreement {extra : Nat} {s t a b : State}
    {hs : RandomSignABI extra s} {ht : RandomSignABI extra t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    {used fuel : Nat} (ha : RandomSignRunning hs hqs used fuel a) (hb : RandomSignRunning ht hqt used fuel b)
    (hpub : RandomSignPublicAgree s t)
    (htrace : (randomSignDraw (randomInput s) used).trace = (randomSignDraw (randomInput t) used).trace)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa Random.sample a tsa u) (eb : Exec isa Random.sample b tsb w) :
    tsa = tsb := by
  obtain ⟨ma, da, hra⟩ := ha.ready
  obtain ⟨mb, db, hrb⟩ := hb.ready
  apply random_sample_agreement hra hrb hqs hpub.base (hpub.args 3 (by decide)) _ hpub.qbytes _ _ ea eb
  · change s.gpr .rcx + s.gpr .r9 = t.gpr .rcx + t.gpr .r9
    rw [hpub.regs .rcx (by decide), hpub.regs .r9 (by decide)]
  · simp only [randomContextOf, randomInput, bytesAt_length, hpub.args 4 (by decide)]
  · change (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (randomQBytes s)) 128 ((randomInput s).rand.drop used)).trace =
      (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (randomQBytes t)) 128 ((randomInput t).rand.drop used)).trace
    rw [random_q_decode, random_q_decode]
    exact htrace

end VG.Proof.Dsa.X86_64
