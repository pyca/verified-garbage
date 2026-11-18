module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomMask
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Spec.Dsa.Random
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-! ### `Dsa.X86_64.RandomPrepareState`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.RandomPrepare`, which this module and modules that import it used -/

section

/-! Initialization of the sampler, including its exact memory effects. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomPrepareFinish.lean`, which only this module imported.
section

/-! The public q>1 decision and mask store at the end of initialization. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

private theorem finishTail_ok {s : State} {B : Addr} {w : Nat} {b : Byte} {m : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (h8 : s.gpr .r8 = m) (h9 : s.gpr .r9 = b.setWidth 64)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) :
    WP isa (.block [.store (Random.sp Random.oMask) .r8,
      .mov .rax (.imm 0), .mov .rcx (.imm 1),
      .alu .cmp .r11 (.imm 2), .cmov .ae .rax (.reg .rcx),
      .alu .cmp .r9 (.imm 2), .cmov .ae .rax (.reg .rcx)]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) m ∧ Keep [.rax, .rcx, .r11, .r9] s t := by
  have hb : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  refine WP.mono (WP.keep [.rax, .rcx, .r11, .r9] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) m) ?_ rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  by_cases hw2 : w < 2 <;> by_cases hb2 : b.toNat < 2 <;>
    xrun [execCmov, eval, random_ea_sp, hsp, hs.st (d := Random.oMask) (by decide),
      h8, h9, h11, BitVec.ult, show (2 : BitVec 64).toNat = 2 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, hb, hw2, hb2] <;> rfl

theorem random_prepareFinish_ok {s : State} {B : Addr} {w : Nat} {b : Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (ha : s.gpr .rax = b.setWidth 64) (h11 : s.gpr .r11 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) :
    WP isa Random.prepareFinish s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) (randomMaskValue b.toNat) ∧
      Keep [.rax, .rcx, .r8, .r9, .r11] s t := by
  unfold Random.prepareFinish
  refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun u => u.gpr .r9 = b.setWidth 64 ∧ u.mem = s.mem)
      (by xrun [ha]) rfl) fun u ⟨⟨hu9, hum⟩, hku⟩ => ?_)
  refine WP.seq (WP.mono (random_mask_ok u) fun v ⟨hv8, hvm, hkv⟩ => ?_)
  have hua := (hku.gpr (show Reg.rax ∉ [Reg.r9] by decide)).trans ha
  have hb : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  rw [hua, hb] at hv8
  have hk := hku.trans hkv
  refine WP.mono (finishTail_ok (hs.congr hk.2.2) ((hk.gpr (by decide)).trans hsp)
      hv8 ((hkv.gpr (by decide)).trans hu9) ((hk.gpr (by decide)).trans h11) hw)
    fun t ⟨hta, htm, hkt⟩ => ?_
  exact ⟨hta, by rw [htm, hvm, hum], (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomPrepareMem (m : Mem) (B p : Addr) (bs : List Byte) : Mem :=
  (((randomClearMem m B).writeW (off B Random.oQ)
    (p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1))).writeW
    (off B Random.oWidth) (BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1)).writeW
    (off B Random.oMask) (randomMaskValue (VG.Proof.Dsa.significant bs).2.toNat)

theorem random_prepare_ok {s : State} {B p : Addr} {bs : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hq : word s.mem B Random.oQ = p)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Random.frameBytes p bs)
    (hpos : 0 < bs.length) (hbound : bs.length < 2 ^ 64) :
    WP isa Random.prepare s fun t =>
      t.gpr .rax = BitVec.ofNat 64
        (if (VG.Proof.Dsa.significant bs).1 < 2 ∧
          (VG.Proof.Dsa.significant bs).2.toNat < 2 then 0 else 1) ∧
      t.mem = randomPrepareMem s.mem B p bs ∧
      Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s t := by
  unfold Random.prepare
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (random_clear_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.2.2
  have husp := (hku.gpr (show Reg.rsp ∉ [Reg.rax] by decide)).trans hsp
  have huq : word u.mem B Random.oQ = p := by
    rw [hum, (random_clear_outside s.mem B).word (by decide) (by decide)]; exact hq
  have hul : word u.mem B Random.oQLen = BitVec.ofNat 64 bs.length := by
    rw [hum, (random_clear_outside s.mem B).word (by decide) (by decide)]; exact hl
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun v =>
      v.gpr .r10 = p ∧ v.gpr .r11 = BitVec.ofNat 64 bs.length ∧ v.mem = u.mem)
      (by xrun [random_ea_sp, husp, hus.ld (d := Random.oQ) (by decide),
        hus.ld (d := Random.oQLen) (by decide), huq, hul]) rfl)
    fun v ⟨⟨hv10, hv11, hvm⟩, hkv⟩ => ?_
  have hk := hku.trans hkv
  have hvsrc := hsrc.congrK (show InScr B Random.frameBytes s.mem v.mem from by
    rw [hvm, hum]; exact InScr.of_outside (random_clear_outside s.mem B) (by decide)) hk
  refine WP.seq (WP.mono (random_significant_ok hv10 hv11 hvsrc hpos hbound)
    fun w ⟨hw10, hw11, hwa, hwm, hkw⟩ => ?_)
  have hkw' := hk.trans hkw
  have hws := hs.congr hkw'.2.2
  have hwsp := (hkw'.gpr (by decide)).trans hsp
  refine WP.seq (WP.mono (WP.keep [] (Q := fun x => x.mem =
      (w.mem.writeW (off B Random.oQ) (p + BitVec.ofNat 64
        (bs.length - (VG.Proof.Dsa.significant bs).1))).writeW
      (off B Random.oWidth) (BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1))
      (by xrun [random_ea_sp, hwsp, hws.st (d := Random.oQ) (by decide),
        hws.st (d := Random.oWidth) (by decide), hw10, hw11]) rfl)
    fun x ⟨hxm, hkx⟩ => ?_)
  have hkx' := hkw'.trans hkx
  refine WP.mono (random_prepareFinish_ok (hs.congr hkx'.2.2)
    ((hkx'.gpr (by decide)).trans hsp) ((hkx.gpr (by decide)).trans hwa)
    ((hkx.gpr (by decide)).trans hw11)
    (by have := VG.Proof.Dsa.significant_fits bs; omega_using [hbound, this]))
    fun t ⟨hta, htm, hkt⟩ => ?_
  exact ⟨hta, by rw [htm, hxm, hwm, hvm, hum]; rfl,
    (hkx'.trans hkt).mono (by decide)⟩

/-- Initialization returns success exactly for the spec's admissible modulus. -/
theorem random_prepare_valid {s : State} {B p : Addr} {bs : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hq : word s.mem B Random.oQ = p)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Random.frameBytes p bs)
    (hpos : 0 < bs.length) (hbound : bs.length < 2 ^ 64) :
    WP isa Random.prepare s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if 1 < Spec.Dsa.decodeBE bs then 1 else 0) ∧
      t.mem = randomPrepareMem s.mem B p bs ∧
      Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s t := by
  refine WP.mono (random_prepare_ok hs hsp hq hl hsrc hpos hbound)
    fun t ⟨hta, htm, hkt⟩ => ⟨?_, htm, hkt⟩
  rw [hta]
  have hv := VG.Proof.Dsa.random_valid_scan_ge bs
  by_cases h : 1 < Spec.Dsa.decodeBE bs
  · have hn : ¬ ((VG.Proof.Dsa.significant bs).1 < 2 ∧
        (VG.Proof.Dsa.significant bs).2.toNat < 2) := by omega_using [hv, h]
    rw [ite_eq_right hn, ite_eq_left h]
  · have hn : (VG.Proof.Dsa.significant bs).1 < 2 ∧
        (VG.Proof.Dsa.significant bs).2.toNat < 2 := by omega_using [hv, h]
    rw [ite_eq_left hn, ite_eq_right h]

theorem random_prepare_width (m : Mem) (B p : Addr) (bs : List Byte) :
    word (randomPrepareMem m B p bs) B Random.oWidth =
      BitVec.ofNat 64 (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE bs)) := by
  unfold randomPrepareMem
  rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self,
    VG.Proof.Dsa.random_drawBytes_scan]

theorem random_prepare_pointer (m : Mem) (B p : Addr) (bs : List Byte) :
    word (randomPrepareMem m B p bs) B Random.oQ =
      p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1) := by
  unfold randomPrepareMem
  rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide),
    (writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]

theorem random_prepare_mask (m : Mem) (B p : Addr) (bs : List Byte) :
    word (randomPrepareMem m B p bs) B Random.oMask =
      randomMaskValue (VG.Proof.Dsa.significant bs).2.toNat := by
  unfold randomPrepareMem
  rw [word_writeW_self]

/-- All caller fields before q, and all memory after the nonce, are unchanged. -/
theorem random_prepare_outside (m : Mem) (B p : Addr) (bs : List Byte) :
    Outside B 168 64 m (randomPrepareMem m B p bs) := by
  unfold randomPrepareMem
  exact ((((random_clear_outside m B).mono (by decide) (by decide)).trans
    ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))

theorem random_prepare_zero (m : Mem) (B p : Addr) (bs : List Byte)
    (i : Nat) (hi : i < 32) :
    randomPrepareMem m B p bs (off B (200 + i)) = 0 := by
  have ho : ofs B (off B (200 + i)) = 200 + i := by
    have he : off B (200 + i) + BitVec.ofNat 64 0 = off B (200 + i) := BitVec.add_zero _
    simpa only [he, Nat.add_zero] using ofs_off B (d := 200 + i) (i := 0) (by omega_using [hi])
  unfold randomPrepareMem
  rw [(writeW_outside _ B _ (by decide)) _ (by rw [ho]; right; simp only [Random.oMask]; omega_using []),
    (writeW_outside _ B _ (by decide)) _ (by rw [ho]; right; simp only [Random.oWidth]; omega_using []),
    (writeW_outside _ B _ (by decide)) _ (by rw [ho]; right; simp only [Random.oQ]; omega_using [])]
  exact random_clear_byte m B i hi

end VG.Proof.Dsa.X86_64

end

end

/-! Initialize the persistent sampler state from the public q buffer. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_prepare_ready {C : RandomContext} {used draws : Nat} {s : State}
    (hs : Scr s C.B Random.frameBytes) (hsp : s.gpr .rsp = C.B)
    (hR : word s.mem C.B Random.oRand = C.R)
    (hRL : word s.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length)
    (hU : word s.mem C.B Random.oUsed = BitVec.ofNat 64 used)
    (hD : word s.mem C.B Random.oDraws = BitVec.ofNat 64 draws)
    (hQ : word s.mem C.B Random.oQ = C.Q)
    (hQL : word s.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length)
    (hRand : Src s C.B Random.frameBytes C.R C.rand)
    (hQS : Src s C.B Random.frameBytes C.Q C.qBytes)
    (hFrame : Frm C.B randomWriteRanges C.initialMem s.mem)
    (hUsed : used ≤ C.rand.length) (hq : 1 < Spec.Dsa.decodeBE C.qBytes) :
    WP isa Random.prepare s fun t => t.gpr .rax = 1 ∧ RandomReady C used draws t := by
  have hfit := VG.Proof.Dsa.significant_fits C.qBytes
  refine WP.mono (random_prepare_valid hs hsp hQ hQL hQS
    (by have := C.positive; omega_using [hfit, this]) (by have := C.qlen; omega_using [this]))
    fun t ⟨hta, htm, hkt⟩ => ?_
  have hf : Outside C.B 168 64 s.mem t.mem := by
    rw [htm]; exact random_prepare_outside _ _ _ _
  have hfs := InScr.of_outside hf (show 168 + 64 ≤ Random.frameBytes by decide)
  have hw (d : Nat) (hd : d + 8 ≤ 168) : word t.mem C.B d = word s.mem C.B d :=
    hf.word (Or.inl hd) (by omega_using [hd])
  refine ⟨?_, hs.congr hkt.2.2, (hkt.gpr (by decide)).trans hsp,
    (hw _ (by decide)).trans hR, (hw _ (by decide)).trans hRL,
    (hw _ (by decide)).trans hU, ?_, (hw _ (by decide)).trans hQL, ?_, ?_,
    (hw _ (by decide)).trans hD, hRand.congrK hfs hkt, hQS.congrK hfs hkt, hUsed,
    hFrame.trans (Frm.of_outside (hf.mono (by decide) (by decide))
      (show (160, 72) ∈ randomWriteRanges by decide)), ?_⟩
  · rw [hta, ite_eq_left hq]; rfl
  · rw [htm, random_prepare_width, VG.Proof.Dsa.random_drawBytes_scan]
  · rw [htm, random_prepare_mask]
  · rw [htm, random_prepare_pointer]
  · intro i hi
    rw [htm]
    exact random_prepare_zero _ _ _ _ i (by have := C.qlen; omega_using [hi, this])

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomSignInit`, which only this module used -/

section

/-! Initialize randomized signing from the shared ABI's arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_init {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes s) fun t =>
      ((∃ m draws, t.gpr .rax = 1 ∧ RandomReady (randomContextOf h m hq) 0 draws t) ∧
      RandomSaved s t.mem ∧ word t.mem (randomBase s) Random.oAttempts = 8 ∧
      Src t (randomBase s) Random.frameBytes (s.gpr .rcx) (randomInput s).key ∧
      Src t (randomBase s) Random.frameBytes (stackArg s 1) (randomInput s).digest) ∧
      Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] (allocState Random.frameBytes s) t := by
  refine WP.keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] ?_ (by rfl)
  have hsp : (allocState Random.frameBytes s).gpr .rsp = randomBase s := by
    simp only [allocState, State.setReg, ite_true]; rfl
  refine WP.seq (WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
    fun u ⟨hum, hku⟩ => ?_)
  have hus := (random_alloc_scr h).congr hku.2.2
  have husp := (hku.gpr (by decide)).trans hsp
  have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
  have hframe : InScr (randomBase s) Random.frameBytes (allocState Random.frameBytes s).mem u.mem := by
    rw [hum]
    exact InScr.of_outside (random_entry_outside _ _) (by decide)
  have hqs := (random_initial_q h).congrK hframe hku
  have hrs := (random_initial_rand h).congrK hframe hku
  have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocState Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact random_entry_values _ _ p hp
  have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9 :=
    hv (168, s.gpr .rcx + s.gpr .r9) (by simp [randomEntryValues, allocState, State.setReg])
  have huu : word u.mem (randomBase s) Random.oUsed = 0 :=
    hv (144, 0) (by simp [randomEntryValues])
  have hau : word u.mem (randomBase s) Random.oAttempts = 8 :=
    hv (152, 8) (by simp [randomEntryValues])
  let C := randomContextOf h u.mem hq
  have hr : word u.mem C.B Random.oRand = C.R :=
    hsaved (112, stackArg s 3) (by simp [randomSavedValues])
  have hrl : word u.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length := by
    simpa only [Random.oRandLen, C, randomContextOf, randomInput, bytesAt_length, ofNat_toNat64] using
      hsaved (120, stackArg s 4) (by simp [randomSavedValues])
  have hql : word u.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length := by
    simpa only [Random.oQLen, C, randomContextOf, random_q_length h, ofNat_toNat64] using
      hsaved (88, stackArg s 0) (by simp [randomSavedValues])
  refine WP.mono (WP.keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] (random_prepare_ready (C := C) (draws := (word u.mem C.B Random.oDraws).toNat)
    hus husp hr hrl huu (ofNat_toNat64 _).symm hqu hql hrs hqs (Frm.refl _ _ _) (Nat.zero_le _) hq) rfl)
    fun t ⟨⟨hta, htr⟩, hkp⟩ => ?_
  have hw (d : Nat) (hd : d + 8 ≤ 144 ∨ d = 152) : word t.mem (randomBase s) d = word u.mem (randomBase s) d := by
    apply htr.frame.word_eq
    · intro r hr
      simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_using [hd]
    · omega_using [hd]
  have hpf : InScr (randomBase s) Random.frameBytes u.mem t.mem := InScr.of_frm htr.frame (by
    intro r hr
    simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  exact ⟨⟨u.mem, _, hta, htr⟩, hsaved.congr (fun d _ hd => hw d (Or.inl hd)),
    (hw _ (Or.inr rfl)).trans hau,
    ((random_initial_key h).congrK hframe hku).congrK hpf hkp,
    ((random_initial_digest h).congrK hframe hku).congrK hpf hkp⟩

end VG.Proof.Dsa.X86_64

end

end


/-! The persistent state of the bounded randomized-signing loop. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomVolatile : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

theorem random_saved_not_volatile {r : Reg} (h : r ∈ calleeSaved) : r ∉ randomVolatile := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

structure RandomSignRunning {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (used fuel : Nat) (t : State) : Prop where
  ready : ∃ m draws, RandomReady (randomContextOf h m hq) used draws t
  saved : RandomSaved s t.mem
  attempts : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  key : Src t (randomBase s) Random.frameBytes (s.gpr .rcx) (randomInput s).key
  digest : Src t (randomBase s) Random.frameBytes (stackArg s 1) (randomInput s).digest
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem random_sign_init_running {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes s) fun t =>
      t.gpr .rax = 1 ∧ RandomSignRunning h hq 0 8 t := by
  refine WP.mono_mx (by decide) (random_sign_init h hq)
    fun t ⟨⟨⟨m, draws, hrax, hr⟩, hs, ha, hkey, hdigest⟩, hk⟩ hmx => ?_
  have hkv : Keep randomVolatile (allocState Random.frameBytes s) t := hk.mono (by decide)
  refine ⟨hrax, ⟨m, draws, hr⟩, hs, ha, hk.2.1, hk.2.2, hkey, hdigest, ?_, ?_⟩
  · intro r hr hne
    rw [hkv.gpr (random_saved_not_volatile hr)]
    simp only [allocState, State.setReg, ite_eq_right hne]
  · rw [hmx]
    rfl

theorem RandomSignRunning.congr {extra : Nat} {s t u : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hm : u.mem = t.mem) (hk : Keep [.rax] t u)
    (hmx : u.mxcsr = t.mxcsr) : RandomSignRunning h hq used fuel u := by
  obtain ⟨m, draws, hready⟩ := hr.ready
  have hf : InScr (randomBase s) Random.frameBytes t.mem u.mem := by rw [hm]; exact InScr.refl _ _ _
  refine ⟨⟨m, draws, hready.congr hm hk⟩, by rw [hm]; exact hr.saved,
    by rw [hm]; exact hr.attempts, hk.2.1.trans hr.rd, hk.2.2.trans hr.wr,
    hr.key.congrK hf hk, hr.digest.congrK hf hk, ?_, ?_⟩
  · intro r hc hne
    exact ((hk.mono (show ∀ r ∈ [Reg.rax], r ∈ randomVolatile by decide)).gpr
      (random_saved_not_volatile hc)).trans (hr.callee r hc hne)
  · rw [hmx]; exact hr.mxcsr

end VG.Proof.Dsa.X86_64
