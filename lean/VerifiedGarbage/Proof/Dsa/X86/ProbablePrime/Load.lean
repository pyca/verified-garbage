module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Memory

import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportRegions
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessZeros
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSave
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.RegionOutside
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract
/-! # The candidate's octets become arrays 0 and 5 of the workspace -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.ProbablePrime VG.Impl.Bignum.X86.PublicContext

theorem Environment.Valid.slotFit {E : Environment} (_ : E.Valid) {j : Nat} (index : j ≤ 27) :
    slot E.width j + 8 * E.width + 16 ≤ E.scratch := by
  unfold Environment.scratch scratchBytes slot stride VG.Impl.Bignum.hdrBytes
  have := Nat.mul_le_mul_right (8 * E.width + 16) (show j + 1 ≤ 28 by omega_arith)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega_arith

theorem Environment.Valid.geometry {E : Environment} (v : E.Valid) : E.geometry.Valid := by
  refine ⟨v.bits.width_low, by have := v.bits.width_high; change VG.Impl.Dsa.X86.ProbablePrime.width E.bits ≤ 128; omega_arith, ?_⟩
  change E.geometry.array 28 ≤ E.size
  rw [← VG.Proof.RsaKeyGen.X86.Prepared.slot_eq E.geometry 28]
  have := v.room
  change E.scratch ≤ E.size
  omega_arith

/-- A stage that writes only the arrays keeps the input. -/
theorem Input.keepArrays {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t : State}
    (I : Input E c entropy s) {o n : Nat} (O : Outside E.base o n s.mem t.mem) (low : 256 ≤ o)
    (high : o + n ≤ E.scratch) {regs : List Reg} (K : Keeps regs s t) (edi : .edi ∉ regs) (esp : .esp ∉ regs)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Input E c entropy t := by
  have room := v.room
  have read (d : Nat) (small : d + 4 ≤ 256) : t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    BitVec.eq_of_toNat_eq (O.w32 (Or.inl (by omega_arith)) (by omega_arith))
  refine ⟨I.scratch.of_keeps K edi esp, (K.1 .esp esp).trans I.stack, ?_, ?_, ?_, ?_,
    I.memory.keep v K (v.work_of_outside O (by omega_arith)) (v.tail_of_outside O high) symbol⟩
  · rw [read 28 (by decide)]; exact I.randPtr
  · unfold w32; rw [read 32 (by decide)]; exact I.randLength
  · unfold w32; rw [read 40 (by decide)]; exact I.capacity
  · rw [read 44 (by decide)]; exact I.usedPtr

theorem load_raw {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : Input E c entropy s) (odd : c % 2 = 1) :
    WP isa (load E.words E.width) s fun t =>
      val32 t.mem E.base (slot E.width 0) (2 * E.width) = c ∧
      val32 t.mem E.base (slot E.width 5) (2 * E.width) = c - 1 ∧
      Outside E.base (slot E.width 0) (slot E.width 5 + 8 * E.width - slot E.width 0) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have b := v.bits
  have room := v.room
  have fit := v.workspaceFit
  have slot0 := v.slotFit (j := 0) (by decide)
  have slot5 := v.slotFit (j := 5) (by decide)
  have twoW := b.words_le
  have twoK := b.words_two
  have bytes := b.bytes_eq
  have e0 : slot E.width 0 = 256 := by unfold slot VG.Impl.Bignum.hdrBytes; omega_arith
  have e5 : slot E.width 5 = 256 + 5 * (8 * E.width + 16) := by unfold slot stride VG.Impl.Bignum.hdrBytes; rfl
  have eS : E.scratch = 256 + 28 * (8 * E.width + 16) := by
    unfold Environment.scratch scratchBytes slot stride VG.Impl.Bignum.hdrBytes; rfl
  have hk : E.words = E.bits / 32 := rfl
  have hw : E.width = width E.bits := rfl
  have hh : VG.Impl.Bignum.hdrBytes = 256 := rfl
  have hs : stride E.width = 8 * E.width + 16 := rfl
  unfold load
  refine WP.seq (wp_movS (v := s.gpr .edi) rfl fun a A _ => wp_addS (v := BitVec.ofNat 32 E.scratch) rfl
    fun e B _ => WP.block_nil ?_)
  have Ke : Keeps [.esi] s e := (A.keeps.mono (by decide)).trans B.keeps
  have Se := I.scratch.of_keeps Ke (by decide)
  have esi : e.gpr .esi = e.gpr .edi + BitVec.ofNat 32 E.scratch := by
    rw [B.gpr, A.gpr, Ke.1 .edi (by decide)]
  have srcAddr : (e.gpr .esi).setWidth 64 = off E.base E.scratch := by
    rw [esi]; exact Se.ea (by omega_arith)
  have dstAddr : (e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64 = off E.base (slot E.width 0) :=
    Se.ea (by omega_arith)
  have srcNat : (e.gpr .esi).toNat = E.workspace.toNat + E.scratch := by
    rw [esi, BitVec.toNat_add, Se.edi_toNat, v.baseNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith : E.scratch < 2 ^ 32), Nat.mod_eq_of_lt (by omega_arith)]
  have dstNat : (e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).toNat = E.workspace.toNat + slot E.width 0 := by
    rw [BitVec.toNat_add, Se.edi_toNat, v.baseNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith : slot E.width 0 < 2 ^ 32), Nat.mod_eq_of_lt (by omega_arith)]
  have C : VG.Proof.RsaKeyGen.X86.Import.Context
      ⟨e.gpr .esi, e.gpr .edi + BitVec.ofNat 32 (slot E.width 0), E.words⟩ e := by
    refine VG.Proof.RsaKeyGen.X86.Import.context_of_regions (by show 0 < E.words; omega_arith)
      (by show (e.gpr .esi).toNat + 4 * E.words ≤ 2 ^ 32; omega_arith)
      (by show (e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).toNat + 4 * E.words ≤ 2 ^ 32; omega_arith) ?_ ?_ ?_
    · change InRegions _ ((e.gpr .esi).setWidth 64) (4 * E.words)
      rw [srcAddr]; exact Se.read (by omega_arith)
    · change InRegions _ ((e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64) (4 * E.words)
      rw [dstAddr]; exact Se.write (by omega_arith)
    · change (⟨(e.gpr .esi).setWidth 64, 4 * E.words⟩ : Region).Disjoint
        ⟨(e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64, 4 * E.words⟩
      rw [srcAddr, dstAddr]
      exact Offset.disjoint E.base (Or.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  have loaded := VG.Proof.RsaKeyGen.X86.Import.load_ok C rfl rfl
  change WP isa (VG.Impl.RsaKeyGen.X86.Import.load E.words (slot E.width 0)) e _ at loaded
  refine WP.seq (WP.mono loaded fun f ⟨value, F, Kf⟩ => ?_)
  change (f.mem.read ((e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64) (4 * E.words)).toNat =
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt e.mem ((e.gpr .esi).setWidth 64) (4 * E.words)) at value
  rw [dstAddr, srcAddr, VG.Proof.Bignum.read_eq_val32] at value
  have low : val32 f.mem E.base (slot E.width 0) E.words = c := by
    rw [value, ← I.memory.candidate]
    unfold Environment.candidate
    rw [hk, bytes, show e.mem = s.mem from by rw [B.mem, A.mem]]
  change Frame [⟨(e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64, 4 * E.words⟩] e.mem f.mem at F
  rw [dstAddr] at F
  have Of : Outside E.base (slot E.width 0) (4 * E.words) e.mem f.mem := frame_outside F (by omega_arith)
  have Sf := Se.of_keeps Kf (by decide)
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.WitnessLoad.zeros_ok Sf (slot E.width 0 + 4 * E.words)
    (2 * E.width - E.words) (by omega_arith)) fun g ⟨Zg, Og, Kg⟩ => ?_)
  have Sg := Sf.of_keeps Kg (by decide)
  have whole : val32 g.mem E.base (slot E.width 0) (2 * E.width) = c := by
    rw [show 2 * E.width = E.words + (2 * E.width - E.words) by omega_arith, val32_append, Zg, Nat.mul_zero,
      Nat.add_zero, Og.val32 (Or.inl (by omega_arith)) (by omega_arith), low]
  refine WP.mono (VG.Proof.RsaKeyGen.X86.CandidateSave.save_ok Sg (n := 2 * E.width)
    (src := slot E.width 0) (dst := slot E.width 5) (by omega_arith) (by omega_arith) (by omega_arith) (Or.inr (Or.inr (by omega_arith)))
    (by rw [whole]; exact odd)) fun t ⟨minus, Ot, Kt⟩ => ?_
  rw [whole] at minus
  refine ⟨?_, by omega_arith, ?_, ?_⟩
  · rw [Ot.val32 (Or.inl (by omega_arith)) (by omega_arith)]; exact whole
  · rw [B.mem, A.mem] at Of
    exact ((Of.mono (by omega_arith) (by omega_arith)).trans (Og.mono (by omega_arith) (by omega_arith))).trans
      (Ot.mono (by omega_arith) (by omega_arith))
  · exact (((Ke.mono (by decide)).trans (Kf.mono (by decide))).trans (Kg.mono (by decide))).trans
      (Kt.mono (by decide))

theorem load_ok {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : Input E c entropy s) (count : w32 s.mem E.base 152 = 0) (odd : c % 2 = 1) :
    WP isa (load E.words E.width) s fun t =>
      Loaded E c entropy t ∧ WorkFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have slot5 := v.slotFit (j := 5) (by decide)
  have e0 : slot E.width 0 = 256 := by unfold slot VG.Impl.Bignum.hdrBytes; omega_arith
  have e5 : slot E.width 5 = 256 + 5 * (8 * E.width + 16) := by unfold slot stride VG.Impl.Bignum.hdrBytes; rfl
  have eS : E.scratch = 256 + 28 * (8 * E.width + 16) := by
    unfold Environment.scratch scratchBytes slot stride VG.Impl.Bignum.hdrBytes; rfl
  refine WP.mono_syms (load_raw v I odd) fun t ⟨value, minus, O, K⟩ syms => ?_
  have fit := v.workspaceFit
  refine ⟨⟨I.keepArrays v O (by omega_arith) (by omega_arith) K (by decide) (by decide) (by rw [syms]), ?_, ?_, ?_⟩,
    v.work_of_outside O (by have := v.room; omega_arith), v.tail_of_outside O (by omega_arith), K⟩
  · rw [← VG.Proof.RsaKeyGen.X86.Prepared.slot_eq]; exact value
  · rw [← VG.Proof.RsaKeyGen.X86.Prepared.slot_eq]; exact minus
  · rw [O.w32 (Or.inl (by omega_arith)) (by omega_arith)]; exact count

end VG.Proof.Dsa.X86.ProbablePrime
