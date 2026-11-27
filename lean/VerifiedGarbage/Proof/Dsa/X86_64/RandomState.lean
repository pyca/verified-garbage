module

public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomMask
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame

/-! ### `Dsa.X86_64.RandomDrawControl`, which this module and modules that import it used -/

section

/-! Public tape bounds and status writes for a scalar draw. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

private theorem sub_nat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

theorem random_drawHead_ok {s : State} {B : Addr} {len used width : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hl : word s.mem B Random.oRandLen = BitVec.ofNat 64 len)
    (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hw : word s.mem B Random.oWidth = BitVec.ofNat 64 width)
    (hused : used ≤ len) (hlen : len < 2 ^ 64) (hwidth : width < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oRandLen)),
      .alu .sub .rax (.mem (Random.sp Random.oUsed)),
      .alu .cmp .rax (.mem (Random.sp Random.oWidth))]) s fun t =>
      t.cf = some (decide (len - used < width)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.cf = some (decide (len - used < width)) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩
  xrun [random_ea_sp, hsp, hs.ld (d := Random.oRandLen) (by decide),
    hs.ld (d := Random.oUsed) (by decide), hs.ld (d := Random.oWidth) (by decide),
    hl, hu, hw, sub_nat hused, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len - used < 2 ^ 64 by omega_using [hlen]), Nat.mod_eq_of_lt hwidth]

theorem random_status_ok {s : State} {B : Addr} (v : BitVec 32)
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B) :
    WP isa (.block [.mov .rax (.imm v), .store (Random.sp Random.oStatus) .rax]) s fun t =>
      t.gpr .rax = v.signExtend 64 ∧
      t.mem = s.mem.writeW (off B Random.oStatus) (v.signExtend 64) ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.gpr .rax = v.signExtend 64 ∧
      t.mem = s.mem.writeW (off B Random.oStatus) (v.signExtend 64)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, hk⟩ => ⟨ha, hm, hk⟩
  xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide)]

theorem random_draw_short_ok {s : State} {B : Addr} {len used width : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hl : word s.mem B Random.oRandLen = BitVec.ofNat 64 len)
    (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hw : word s.mem B Random.oWidth = BitVec.ofNat 64 width)
    (hused : used ≤ len) (hlen : len < 2 ^ 64) (hwidth : width < 2 ^ 64)
    (hshort : len - used < width) :
    WP isa Random.draw s fun t =>
      t.gpr .rax = 2 ∧ t.mem = s.mem.writeW (off B Random.oStatus) (2 : BitVec 64) ∧
      Keep [.rax] s t := by
  unfold Random.draw
  refine WP.seq (WP.mono (random_drawHead_ok hs hsp hl hu hw hused hlen hwidth)
    fun u ⟨huc, hum, hku⟩ => ?_)
  refine WP.ite true (by simp only [eval, huc, hshort, decide_true]) (fun _ => ?_)
    (fun h => Bool.noConfusion h)
  refine WP.mono (random_status_ok 2 (hs.congr hku.2.2) ((hku.gpr (by decide)).trans hsp))
    fun t ⟨hta, htm, hkt⟩ => ?_
  exact ⟨hta, by rw [htm, hum]; rfl, (hku.trans hkt).mono (by decide)⟩

theorem random_used_ok {s : State} {B : Addr} {used width : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hw : word s.mem B Random.oWidth = BitVec.ofNat 64 width) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oUsed)),
      .alu .add .rax (.mem (Random.sp Random.oWidth)), .store (Random.sp Random.oUsed) .rax]) s fun t =>
      t.mem = s.mem.writeW (off B Random.oUsed) (BitVec.ofNat 64 (used + width)) ∧
      Keep [.rax] s t := by
  refine WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off B Random.oUsed) (BitVec.ofNat 64 (used + width))) ?_ rfl
  xrun [random_ea_sp, hsp, hs.ld (d := Random.oUsed) (by decide),
    hs.ld (d := Random.oWidth) (by decide), hs.st (d := Random.oUsed) (by decide),
    hu, hw, BitVec.ofNat_add]

def randomDrawFinishMem (m : Mem) (B : Addr) (accept : Bool) (draws : Nat) : Mem :=
  if accept then m.writeW (off B Random.oStatus) (1 : BitVec 64)
  else
    let m' := m.writeW (off B Random.oDraws) (BitVec.ofNat 64 (draws - 1))
    if draws = 1 then m'.writeW (off B Random.oStatus) (0 : BitVec 64) else m'

theorem random_decrement_ok {s : State} {B : Addr} {draws : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hd : word s.mem B Random.oDraws = BitVec.ofNat 64 draws)
    (hpos : 0 < draws) (hbound : draws < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oDraws)), .alu .sub .rax (.imm 1),
      .store (Random.sp Random.oDraws) .rax]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (draws - 1) ∧ t.zf = some (decide (draws = 1)) ∧
      t.mem = s.mem.writeW (off B Random.oDraws) (BitVec.ofNat 64 (draws - 1)) ∧ Keep [.rax] s t := by
  have hz : (BitVec.ofNat 64 (draws - 1) == 0) = decide (draws = 1) := by
    rw [ofNat64_beq_zero (by omega_using [hbound])]
    exact decide_eq_decide.mpr (by omega_using [hpos])
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 (draws - 1) ∧ t.zf = some (decide (draws = 1)) ∧
      t.mem = s.mem.writeW (off B Random.oDraws) (BitVec.ofNat 64 (draws - 1))) ?_ rfl)
    fun _ ⟨⟨ha, hz, hm⟩, hk⟩ => ⟨ha, hz, hm, hk⟩
  xrun [random_ea_sp, hsp, hs.ld (d := Random.oDraws) (by decide),
    hs.st (d := Random.oDraws) (by decide), hd, ofNat64_pred hpos hbound, hz]

/-- Rejection consumes one unit of fuel; only exhausting it changes status. -/
theorem random_drawFinish_ok {s : State} {B : Addr} {draws : Nat} {accept : Bool}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hd : word s.mem B Random.oDraws = BitVec.ofNat 64 draws)
    (hz : s.zf = some (!accept)) (hpos : 0 < draws) (hbound : draws < 2 ^ 64) :
    WP isa Random.drawFinish s fun t =>
      t.mem = randomDrawFinishMem s.mem B accept draws ∧ Keep [.rax] s t := by
  unfold Random.drawFinish
  cases accept with
  | true =>
    refine WP.ite true (by simp only [eval, hz, Bool.not_true, Option.map_some, Bool.not_false])
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    exact WP.mono (random_status_ok 1 hs hsp) fun _ ⟨_, hm, hk⟩ => ⟨hm, hk⟩
  | false =>
    refine WP.ite false (by simp only [eval, hz, Bool.not_false, Option.map_some, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    refine WP.seq (WP.mono (random_decrement_ok hs hsp hd hpos hbound)
      fun u ⟨hua, huz, hum, hku⟩ => ?_)
    have hus := hs.congr hku.2.2
    have husp := (hku.gpr (by decide)).trans hsp
    by_cases hd1 : draws = 1
    · refine WP.ite true (by simp only [eval, huz, hd1, decide_true]) (fun _ => ?_)
        (fun h => Bool.noConfusion h)
      have hua0 : u.gpr .rax = 0 := by rw [hua, hd1]; rfl
      refine WP.mono (WP.keep [] (Q := fun t =>
        t.mem = u.mem.writeW (off B Random.oStatus) (0 : BitVec 64))
        (by xrun [random_ea_sp, husp, hus.st (d := Random.oStatus) (by decide), hua0]) rfl)
        fun t ⟨htm, hkt⟩ => ?_
      exact ⟨by rw [htm, hum]; simp only [randomDrawFinishMem, Bool.false_eq_true,
        ite_false, hd1, ite_true], (hku.trans hkt).mono (by decide)⟩
    · refine WP.ite false (by simp only [eval, huz, hd1, decide_false])
        (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
      exact ⟨by rw [hum]; simp only [randomDrawFinishMem, Bool.false_eq_true,
        ite_false, hd1], hku⟩

theorem random_drawFinish_outside (m : Mem) (B : Addr) (accept : Bool) (draws : Nat) :
    Outside B 160 40 m (randomDrawFinishMem m B accept draws) := by
  cases accept with
  | true => exact (writeW_outside _ B _ (by decide)).mono (by decide) (by decide)
  | false =>
    unfold randomDrawFinishMem
    simp only [Bool.false_eq_true, ite_false]
    split
    · exact ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide)).trans
        ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))
    · exact (writeW_outside _ B _ (by decide)).mono (by decide) (by decide)

theorem random_drawFinish_status (m : Mem) (B : Addr) (accept : Bool) (draws : Nat) :
    word (randomDrawFinishMem m B accept draws) B Random.oStatus =
      if accept then 1 else if draws = 1 then 0 else word m B Random.oStatus := by
  cases accept with
  | true => exact word_writeW_self _ _ _ _
  | false =>
    simp only [randomDrawFinishMem, Bool.false_eq_true, ite_false]
    split
    · exact word_writeW_self _ _ _ _
    · exact (writeW_outside _ B _ (by decide)).word (by decide) (by decide)

theorem random_drawFinish_draws (m : Mem) (B : Addr) (accept : Bool) (draws : Nat) :
    word (randomDrawFinishMem m B accept draws) B Random.oDraws =
      if accept then word m B Random.oDraws else BitVec.ofNat 64 (draws - 1) := by
  cases accept with
  | true => exact (writeW_outside _ B _ (by decide)).word (by decide) (by decide)
  | false =>
    simp only [randomDrawFinishMem, Bool.false_eq_true, ite_false]
    split
    · rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]
    · exact word_writeW_self _ _ _ _

theorem random_drawFinish_word (m : Mem) (B : Addr) (accept : Bool) (draws d : Nat)
    (hd : d + 8 ≤ 2 ^ 64)
    (hd1 : d + 8 ≤ 160 ∨ 168 ≤ d) (hd2 : d + 8 ≤ 192 ∨ 200 ≤ d) :
    word (randomDrawFinishMem m B accept draws) B d = word m B d := by
  cases accept with
  | true => exact (writeW_outside _ B _ (by decide)).word hd2 hd
  | false =>
    simp only [randomDrawFinishMem, Bool.false_eq_true, ite_false]
    split
    · exact ((writeW_outside _ B (d := Random.oStatus) (0 : BitVec 64) (by decide)).word hd2 hd).trans
        ((writeW_outside _ B (d := Random.oDraws) (BitVec.ofNat 64 (draws - 1)) (by decide)).word hd1 hd)
    · exact (writeW_outside _ B _ (by decide)).word hd1 hd

end VG.Proof.Dsa.X86_64

end

end

/-! The sampler state retained across rejected draws. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomContext where
  B : Addr
  initialMem : Mem
  R : Addr
  Q : Addr
  qBytes : List Byte
  rand : List Byte
  qlen : qBytes.length ≤ 32
  randBound : rand.length < 2 ^ 64
  positive : 0 < (VG.Proof.Dsa.significant qBytes).1

def randomWriteRanges : List (Nat × Nat) := [(144, 8), (160, 72)]

structure RandomReady (C : RandomContext) (used draws : Nat) (s : State) : Prop where
  scr : Scr s C.B Random.frameBytes
  sp : s.gpr .rsp = C.B
  rand : word s.mem C.B Random.oRand = C.R
  randLen : word s.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length
  usedWord : word s.mem C.B Random.oUsed = BitVec.ofNat 64 used
  width : word s.mem C.B Random.oWidth = BitVec.ofNat 64 (VG.Proof.Dsa.significant C.qBytes).1
  qLen : word s.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length
  mask : word s.mem C.B Random.oMask = randomMaskValue (VG.Proof.Dsa.significant C.qBytes).2.toNat
  q : word s.mem C.B Random.oQ = C.Q + BitVec.ofNat 64
    (C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1)
  draws : word s.mem C.B Random.oDraws = BitVec.ofNat 64 draws
  randSrc : Src s C.B Random.frameBytes C.R C.rand
  qSrc : Src s C.B Random.frameBytes C.Q C.qBytes
  usedBound : used ≤ C.rand.length
  frame : Frm C.B randomWriteRanges C.initialMem s.mem
  padding : ∀ i < C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1,
    s.mem (off C.B (200 + i)) = 0

theorem RandomReady.congr {C : RandomContext} {used draws : Nat} {s t : State}
    (h : RandomReady C used draws s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    RandomReady C used draws t := by
  have hf : InScr C.B Random.frameBytes s.mem t.mem := by rw [hm]; exact InScr.refl _ _ _
  exact ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.sp,
    by rw [hm]; exact h.rand, by rw [hm]; exact h.randLen,
    by rw [hm]; exact h.usedWord, by rw [hm]; exact h.width,
    by rw [hm]; exact h.qLen, by rw [hm]; exact h.mask,
    by rw [hm]; exact h.q, by rw [hm]; exact h.draws,
    h.randSrc.congrK hf hk, h.qSrc.congrK hf hk, h.usedBound, by rw [hm]; exact h.frame, by rw [hm]; exact h.padding⟩

/-- Reconstruct the persistent state from the exact memory effects of a draw. -/
theorem RandomReady.after_draw {C : RandomContext} {used draws : Nat} {s t : State} {m : Mem}
    (h : RandomReady C used draws s) (accept : Bool)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hcopy : Outside C.B (200 + C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1)
      (VG.Proof.Dsa.significant C.qBytes).1 s.mem m)
    (hm : t.mem = randomDrawFinishMem
      (m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + (VG.Proof.Dsa.significant C.qBytes).1)))
      C.B accept draws)
    (hk : Keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] s t) :
    RandomReady C (used + (VG.Proof.Dsa.significant C.qBytes).1)
      (if accept then draws else draws - 1) t := by
  have hnfit := VG.Proof.Dsa.significant_fits C.qBytes
  have hcopyCoarse : Outside C.B 200 32 s.mem m := hcopy.mono (by omega_using [hnfit]) (by have := C.qlen; omega_using [hnfit, this])
  let m' := m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + (VG.Proof.Dsa.significant C.qBytes).1))
  have hused : Outside C.B Random.oUsed 8 m m' := writeW_outside _ _ _ (by decide)
  have hfinish := random_drawFinish_outside m' C.B accept draws
  have hf : InScr C.B Random.frameBytes s.mem t.mem := by
    rw [hm]
    exact ((InScr.of_outside hcopyCoarse (by decide)).trans
      (InScr.of_outside hused (by decide))).trans (InScr.of_outside hfinish (by decide))
  have hw (d : Nat) (hd : d + 8 ≤ 200)
      (hu : d + 8 ≤ 144 ∨ 152 ≤ d) (hdraw : d + 8 ≤ 160 ∨ 168 ≤ d)
      (hstatus : d + 8 ≤ 192 ∨ 200 ≤ d) : word t.mem C.B d = word s.mem C.B d := by
    rw [hm, random_drawFinish_word _ _ _ _ d (by omega_using [hd]) hdraw hstatus,
      hused.word hu (by omega_using [hd]), hcopyCoarse.word (Or.inl hd) (by omega_using [hd])]
  refine ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.sp,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.rand,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.randLen, ?_,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.width,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.qLen,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.mask,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.q, ?_,
    h.randSrc.congrK hf hk, h.qSrc.congrK hf hk, hfull, ?_, ?_⟩
  · rw [hm, random_drawFinish_word _ _ _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, random_drawFinish_draws]
    cases accept with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [hused.word (by decide) (by decide), hcopyCoarse.word (by decide) (by decide)]
      exact h.draws
  · rw [hm]
    exact ((h.frame.trans (Frm.of_outside (hcopyCoarse.mono (by decide) (by decide))
      (show (160, 72) ∈ randomWriteRanges by decide))).trans
      (Frm.of_outside hused (show (144, 8) ∈ randomWriteRanges by decide))).trans
      (Frm.of_outside (hfinish.mono (by decide) (by decide)) (show (160, 72) ∈ randomWriteRanges by decide))
  · intro i hi
    have ho : ofs C.B (off C.B (200 + i)) = 200 + i := by
      have he : off C.B (200 + i) + BitVec.ofNat 64 0 = off C.B (200 + i) := BitVec.add_zero _
      simpa only [he, Nat.add_zero] using ofs_off C.B (d := 200 + i) (i := 0) (by have := C.qlen; omega_using [hi, this])
    rw [hm, hfinish _ (by rw [ho]; right; omega_using []),
      hused _ (by rw [ho]; right; unfold Random.oUsed; omega_using []),
      hcopy _ (by rw [ho]; left; omega_using [hi])]
    exact h.padding i hi

theorem RandomReady.after_status {C : RandomContext} {used draws : Nat} {s t : State} {status : BitVec 64}
    (h : RandomReady C used draws s)
    (hm : t.mem = s.mem.writeW (off C.B Random.oStatus) status) (hk : Keep [.rax] s t) :
    RandomReady C used draws t := by
  have hf : Outside C.B Random.oStatus 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  have hi := InScr.of_outside hf (show Random.oStatus + 8 ≤ Random.frameBytes by decide)
  have hw (d : Nat) (hd : d + 8 ≤ 192) : word t.mem C.B d = word s.mem C.B d :=
    hf.word (Or.inl hd) (by omega_using [hd])
  refine ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.sp,
    (hw _ (by decide)).trans h.rand, (hw _ (by decide)).trans h.randLen,
    (hw _ (by decide)).trans h.usedWord, (hw _ (by decide)).trans h.width,
    (hw _ (by decide)).trans h.qLen, (hw _ (by decide)).trans h.mask,
    (hw _ (by decide)).trans h.q, (hw _ (by decide)).trans h.draws,
    h.randSrc.congrK hi hk, h.qSrc.congrK hi hk, h.usedBound,
    h.frame.trans (Frm.of_outside (hf.mono (by decide) (by decide))
      (show (160, 72) ∈ randomWriteRanges by decide)), ?_⟩
  intro i hi'
  have ho : ofs C.B (off C.B (200 + i)) = 200 + i := by
    have he : off C.B (200 + i) + BitVec.ofNat 64 0 = off C.B (200 + i) := BitVec.add_zero _
    simpa only [he, Nat.add_zero] using ofs_off C.B (d := 200 + i) (i := 0) (by have := C.qlen; omega_using [hi', this])
  rw [hf _ (by rw [ho]; right; unfold Random.oStatus; omega_using [])]
  exact h.padding i hi'

end VG.Proof.Dsa.X86_64
