module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
public import VerifiedGarbage.Impl.Bignum.CrtLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Impl.Rsa.AArch64
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import Aesop.BuiltinRules

/-! ### `Dsa.AArch64.NewChild`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.ChildCount`, which this module and modules that import it used -/

section

/-! # Public child width and workspace selection -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev childCount (offset : Nat) : List Instr :=
  ([mov .x1 .x0, ldh .x12 argLen, .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3] : List Instr) ++ Core.enter offset

theorem childCount_ok {s : State} {B : Addr} {Z offset len : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (ho : offset < 2 ^ 16) (hlen : len < 2 ^ 32)
    (hl : word s.mem B (8 * argLen) = BitVec.ofNat 64 len) :
    WP isa (.block (childCount offset)) s fun t =>
      t.gpr .x1 = B ∧ t.gpr .x0 = off B offset ∧ t.gpr .x12 = BitVec.ofNat 64 ((len + 7) / 8) ∧
      t.mem = s.mem ∧ Keep [.x1, .x0, .x12, .x4] s t := by
  refine WP.mono (WP.keep [.x1, .x0, .x12, .x4] (Q := fun t =>
      t.gpr .x1 = B ∧ t.gpr .x0 = off B offset ∧ t.gpr .x12 = BitVec.ofNat 64 ((len + 7) / 8) ∧
      t.mem = s.mem) ?_ rfl rfl rfl) fun t ⟨⟨hsi, hd, h12, hm⟩, hk⟩ => ⟨hsi, hd, h12, hm, hk⟩
  unfold childCount Core.enter
  simp only [List.cons_append, List.nil_append]
  have hoff : (BitVec.ofNat 16 offset).setWidth 64 = BitVec.ofNat 64 offset := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [ho]
  have hwidth : (BitVec.ofNat 64 len + (7#64)) >>> 3 = BitVec.ofNat 64 ((len + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow]
    omega_using [hlen]
  brun [hdi, hl, hdr_enc (show argLen < 32 by decide), hoff, hwidth,
    hs.ld (Nat.le_trans (show 8 * argLen + 8 ≤ pWorkspace by decide) hZ)]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ChildBases`, which this module and modules that import it used -/

section

/-! # Constructing a child workspace header before loading its modulus -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev childBases : List Instr :=
  ([sth .x12 sW, sth .x1 Crt.sLink] : List Instr) ++ setBases

theorem childBases_ok {s : State} {B parent : Addr} {Z w : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hsi : s.gpr .x1 = parent)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (hZ : 136 ≤ Z) :
    WP isa (.block childBases) s fun t =>
      Good t B Z w (word s.mem B (8 * sMinv)) ∧ word t.mem B (8 * Crt.sLink) = parent ∧
      Outside B 48 88 s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  unfold childBases
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem =
    (s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 w)).writeW (off B (8 * Crt.sLink)) parent) ?_ rfl rfl rfl)
    fun u ⟨hum, hku⟩ => ?_
  · brun [hdr_enc (show sW < 32 by decide), hdr_enc (show Crt.sLink < 32 by decide), hdi, hsi, h12, hs.st (d := 8 * sW) (Nat.le_trans (by decide) hZ), hs.st (d := 8 * Crt.sLink) hZ]
  have hudi := (hku.gpr .x0 (show Reg.x0 ∉ [] by decide)).trans hdi
  have hu12 := (hku.gpr .x12 (show Reg.x12 ∉ [] by decide)).trans h12
  refine WP.mono (setBases_ok (hs.congr hku.wr) hudi hu12 (Nat.le_trans (by decide) hZ))
    fun t ⟨htarr, hft, hkt⟩ => ?_
  have hks := hku.trans hkt
  refine ⟨⟨hs.congr hks.wr, (hks.gpr .x0 (by decide)).trans hdi, ⟨?_, ?_, htarr⟩⟩, ?_, ?_, hks.mono (by decide)⟩
  · rw [hft.word (Or.inl (by decide)) (by decide), hum,
      (writeW_outside _ B _ (d := 8 * Crt.sLink) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hft.word (Or.inl (by decide)) (by decide), hum,
      (writeW_outside _ B _ (d := 8 * Crt.sLink) (by decide)).word (Or.inl (by decide)) (by decide),
      (writeW_outside _ B _ (d := 8 * sW) (by decide)).word (Or.inr (by decide)) (by decide)]
  · rw [hft.word (Or.inr (by decide)) (by decide), hum, word_writeW_self]
  · intro x hx
    rw [hft x (by change ofs B x < 64 ∨ 128 ≤ ofs B x; change ofs B x < 48 ∨ 136 ≤ ofs B x at hx; omega_using [hx]), hum]
    rw [writeW_outside _ B _ (d := 8 * Crt.sLink) (by decide) x
      (by change ofs B x < 128 ∨ 136 ≤ ofs B x; change ofs B x < 48 ∨ 136 ≤ ofs B x at hx; omega_using [hx])]
    exact writeW_outside _ B _ (d := 8 * sW) (by decide) x
      (by change ofs B x < 48 ∨ 56 ≤ ofs B x; change ofs B x < 48 ∨ 136 ≤ ofs B x at hx; omega_using [hx])

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.InitFrame`, which the modules that import this one used -/

section

/-! # Changes permitted while initializing one DSA child -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def initRanges (o wx : Nat) : List (Nat × Nat) := [(128, 16), (o, slot wx 8)]

theorem init_call_frame {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : Frm B (callRanges arg argLen) mem mem') : Frm B (initRanges o wx) mem mem' := by
  apply hf.widen
  intro r hr
  simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨(128, 16), by simp [initRanges], by decide⟩

theorem init_child_frame {B : Addr} {o wx d n : Nat} {mem mem' : Mem}
    (hf : Outside (off B o) d n mem mem') (hd : d + n ≤ slot wx 8)
    (ho : o + slot wx 8 ≤ 2 ^ 64) : Frm B (initRanges o wx) mem mem' := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  apply (Frm.of_outside_off hf (by omega_using [ho, hslot]) (by omega_using [hd, ho])).widen
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨(o, slot wx 8), by simp [initRanges], by simp only; omega_using [hd]⟩

theorem init_source {s t : State} {B p : Addr} {Z o wx : Nat} {bytes : List Byte} {rs : List Reg}
    (hf : Frm B (initRanges o wx) s.mem t.mem) (hk : Keep rs s t)
    (hZ : 144 ≤ Z) (hhi : o + slot wx 8 ≤ Z) (hs : Src s B Z p bytes) : Src t B Z p bytes := by
  apply hs.congrK _ hk
  apply InScr.of_frm hf
  intro r hr
  simp only [initRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only <;> omega_arith

theorem init_word {B : Addr} {o wx d : Nat} {mem mem' : Mem}
    (hf : Frm B (initRanges o wx) mem mem') (hd : d + 8 ≤ o)
    (ha : d + 8 ≤ 128 ∨ 144 ≤ d) (ho : o < 2 ^ 64) : word mem' B d = word mem B d := by
  apply hf.word_eq _ (by omega_using [hd, ho])
  intro r hr
  simp only [initRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha
  · exact Or.inl hd

/-- Initializing a disjoint child preserves an already initialized modulus. -/
theorem init_ready {B : Addr} {o wx other ow m : Nat} {mi : BitVec 64} {mem mem' : Mem}
    (hf : Frm B (initRanges o wx) mem mem') (hready : ChildReady mem B other ow m mi)
    (hlo : 144 ≤ other) (hhi : other + slot ow 8 ≤ 2 ^ 64)
    (hsep : other + slot ow 8 ≤ o ∨ o + slot wx 8 ≤ other) : ChildReady mem' B other ow m mi := by
  have hslot : 256 ≤ slot ow 8 := by unfold slot hdrBytes; omega_using []
  have he : ∀ d, d + 8 ≤ slot ow 8 → word mem' (off B other) d = word mem (off B other) d := by
    intro d hd
    rw [word_off, word_off]
    apply hf.word_eq _ (by omega_using [hhi, hd])
    intro r hr
    simp only [initRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; omega_using [hlo]
    · rcases hsep with hsep | hsep
      · left; omega_using [hd, hsep]
      · right; omega_using [hsep]
  have hn := slot_le (w := ow) (show VG.Impl.Bignum.Public.aN < 8 by decide)
  refine ⟨hready.header.of_words (fun i hi => he _ (by omega_using [hslot, hi])), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => he _ (by omega_using [hn, hi]))]
    exact hready.modulus
  · rw [he _ (by omega_using [hn])]
    exact hready.inverse

end VG.Proof.Dsa.AArch64

end

end

/-! # Creating a linked arithmetic child from its public operand length -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem newChild_ok {s : State} {B : Addr} {Z o w len : Nat} {parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (hZ : pWorkspace ≤ Z)
    (ho : o < 2 ^ 16) (hlen : len < 2 ^ 32)
    (hl : word s.mem B (8 * argLen) = BitVec.ofNat 64 len)
    (hlo : slot w 8 ≤ o) (hhi : o + slot ((len + 7) / 8) 8 + tabBytes ((len + 7) / 8) ≤ Z) :
    WP isa (.block (childCount o ++ childBases)) s fun t => ∃ mi : BitVec 64,
      SubCtx t B Z o w ((len + 7) / 8) mi ∧
      Outside (off B o) 48 88 s.mem t.mem ∧ Keep [.x1, .x0, .x12, .x3, .x4] s t := by
  have hslot : 256 ≤ slot ((len + 7) / 8) 8 := by unfold slot hdrBytes; omega_using []
  have hroot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  rw [WP.block_append_iff]
  refine WP.mono (childCount_ok hg.scr hg.x0 hZ ho hlen hl)
    fun u ⟨husi, hudi, hu12, hum, hku⟩ => ?_
  have hus : Scr u (off B o) (slot ((len + 7) / 8) 8) :=
    (hg.scr.congr hku.wr).sub (by omega_using [hhi]) (by omega_using [hslot])
  refine WP.mono (childBases_ok hus hudi husi hu12 (by omega_using [hslot])) fun t ⟨hgt, hlink, hft, hkt⟩ => ?_
  have hf : Outside (off B o) 48 88 s.mem t.mem := by rw [← hum]; exact hft
  have hff : Frm (off B o) [(48, 88)] s.mem t.mem := Frm.of_outside hf (by simp)
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi
    exact hff.word_below (L := 136) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)
      (by have := hg.scr.nowrap; omega_using [ho]) (by omega_using [ho]) (by omega_using [hlo, hroot, hi])
  have hk := hku.trans hkt
  exact ⟨_, ⟨hg.scr.congr hk.wr, hgt.x0, hgt.hdr, hlink,
    (hb _ (by decide)).trans hg.hdr.hw,
    fun j hj => (hb _ (by unfold sArr; omega_using [hj])).trans (hg.hdr.harr j hj), hlo, hhi⟩,
    hf, hk.mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Initializing the Montgomery inverse for each odd DSA modulus -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev initInverse : List Instr :=
  ([ldh .x3 (sArr aN), ld .x3 .x3] : List Instr) ++ minv ++
    ([sth .x15 sMinv] : List Instr)

theorem initInverse_ok {s : State} {B : Addr} {Z w : Nat} {oldMinv : BitVec 64}
    (hg : Good s B Z w oldMinv) (hZ : slot w 8 ≤ Z)
    (hodd : (word s.mem B (slot w aN)).toNat % 2 = 1) :
    WP isa (.block initInverse) s fun t => ∃ mi : BitVec 64,
      Good t B Z w mi ∧ ((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧
      Outside B (8 * sMinv) 8 s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x6, .x15] s t := by
  have hhdr : ∀ i < 32, 8 * i + 8 ≤ Z := fun i hi =>
    Nat.le_trans (hdr_lt_slot w 8 hi) hZ
  have hn : slot w aN + 8 ≤ Z := by
    have h := slot_le (w := w) (show aN < 8 by decide)
    omega_using [hZ, h]
  unfold initInverse
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun u =>
      u.gpr .x3 = word s.mem B (slot w aN) ∧ u.mem = s.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨hub, hum⟩, hku⟩ => ?_
  · brun [hdr_enc (show sArr aN < 32 by decide), hg.x0, hg.hdr.harr aN (by decide),
      hg.scr.ld (hhdr (sArr aN) (by decide)), hg.scr.ld hn]
  rw [WP.block_append_iff]
  refine WP.mono (minv_ok u (by rw [hub]; exact hodd)) fun v ⟨hvi, hkv, hvm⟩ => ?_
  have hks := hku.trans hkv
  have hvdi := (hks.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hg.x0
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = v.mem.writeW (off B (8 * sMinv)) (v.gpr .x15)) ?_ rfl rfl rfl)
    fun t ⟨htm, hkt⟩ => ?_
  · brun [hdr_enc (show sMinv < 32 by decide), hvdi,
      (hg.scr.congr hks.wr).st (hhdr sMinv (by decide))]
  have hf : Outside B (8 * sMinv) 8 s.mem t.mem := by
    rw [htm, hvm, hum]
    exact writeW_outside _ _ _ (by decide)
  have hktotal := hks.trans hkt
  refine ⟨v.gpr .x15, ⟨hg.scr.congr hktotal.wr, (hktotal.gpr .x0 (by decide)).trans hg.x0,
    ⟨?_, ?_, ?_⟩⟩, by rw [hub] at hvi; exact hvi, hf, hktotal.mono (by decide)⟩
  · exact (hf.word (Or.inl (by decide)) (by decide)).trans hg.hdr.hw
  · rw [htm, word_writeW_self]
  · intro j hj
    exact (hf.word (Or.inr (by unfold sArr sMinv; omega_using [])) (by unfold sArr; omega_using [hj])).trans (hg.hdr.harr j hj)

end VG.Proof.Dsa.AArch64
