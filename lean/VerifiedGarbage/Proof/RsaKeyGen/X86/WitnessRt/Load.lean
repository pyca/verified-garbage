module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Sample
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportEncoding
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
import VerifiedGarbage.Proof.RsaKeyGen.WitnessSample
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.RegionOutside
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A witness drawn from the entropy into array 6 and sampled, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessRt

theorem importArgs_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) {input : Import.Geometry}
    (count : input.count = g.words) (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst) :
    WP isa (.block importArgs) s fun t =>
      t.mem = s.mem ∧ Keeps [.ebx, .ecx, .edx] s t ∧ t.gpr .esi = input.sourcePtr 0 ∧
      t.gpr .ebx = input.destPtr 0 ∧ t.gpr .ecx = BitVec.ofNat 32 input.count := by
  obtain ⟨fit, -, many, words⟩ := fits v
  have bound := v.maxWidth
  have head := v.headerFit
  have nowrap := C.ws.nowrap
  unfold importArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (draw_ok v C) fun a ⟨D, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.block_append (WP.mono (ptr_short v Ca 6 (by decide) .ebx) fun b ⟨P, Mb, Kb⟩ => ?_)
  refine wp_addS rfl fun c Cc _ => wp_subS rfl fun d Dd _ => ?_
  have Kd : Keeps [.ebx, .edx] s d := (((Ka.mono (by decide)).widen Kb).widen Cc.keeps).widen Dd.keeps
  refine wp_movS (readSrc_ptr (C.ws.of_keeps Kd) (r := .edi) (x := 0) (d := 48)
    (by rw [PtrAt, Kd.1 .edi (by decide)]; exact C.base) (by omega)) fun e E _ =>
    wp_addS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.ebx, .ecx, .edx] s t := ((Kd.mono (by decide)).widen E.keeps).widen T.keeps
  have edx : (b.gpr .edx).toNat = 8 * g.w := by
    rw [Kb.1 .edx (by decide), D, BitVec.toNat_ofNat]; omega
  have sum : PtrAt c g.W .ebx (g.array 6 + 8 * g.w) := by
    rw [PtrAt, Cc.gpr, ptr_add P, edx]
  have ebx : PtrAt d g.W .ebx (g.array 6 + 8 * g.w - 4) := by
    rw [PtrAt, Dd.gpr, ptr_sub sum 4 (by change 4 ≤ _; omega)]
    rfl
  have base := C.base
  refine ⟨by rw [T.mem, E.mem, Dd.mem, Cc.mem, Mb, Ma], K, ?_, ?_, ?_⟩
  · rw [K.1 .esi (by decide), source]
    simp only [Import.Geometry.sourcePtr, Nat.mul_zero, BitVec.add_zero]
  · rw [T.other .ebx (by decide), E.other .ebx (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [ebx]
    unfold Import.Geometry.destPtr
    rw [← destination, count, Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.sub_zero,
      BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, base]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr, BitVec.toNat_add, E.gpr, BitVec.toNat_ofNat, count]
    change (w32 d.mem g.W 48 + w32 d.mem g.W 48) % 2 ^ 32 = _
    rw [Dd.mem, Cc.mem, Mb, Ma, C.width]
    omega

theorem load_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {input : Import.Geometry} (I : Import.Context input s)
    (count : input.count = g.words) (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst) :
    WP isa load s fun t =>
      Prepare.Data g c capacity p t ∧
      val32 t.mem g.W (g.array 6) g.words =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (4 * g.words)) ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  obtain ⟨fit, -, many, -⟩ := fits v
  have nowrap := S.ready.scratch.nowrap
  refine WP.seq (WP.mono (importArgs_ok v S.ready.context count source destination)
    fun a ⟨M, K, Ps, Pd, Pc⟩ => ?_)
  have Ia : Import.Context input a := ⟨I.positive, I.sourceFit, I.destFit,
    fun i index => by rw [K.2.1, K.2.2]; exact I.readable i index,
    fun i index => by rw [K.2.2]; exact I.writable i index, I.separate⟩
  refine WP.mono (Import.code_ok Ia Ps Pd Pc) fun t T => ?_
  have value := T.os2ip
  have F := T.frame
  rw [M] at value F
  have dstAddr : input.dst.setWidth 64 = off g.W (g.array 6) := by
    rw [← destination]
    exact S.ready.scratch.ea (d := g.array 6) (by omega)
  have region : input.destRegion = ⟨off g.W (g.array 6), 4 * input.count⟩ := by
    unfold Import.Geometry.destRegion
    rw [dstAddr]
  rw [region, count] at F
  rw [dstAddr, count, VG.Proof.Bignum.read_eq_val32] at value
  have O := frame_outside F (by omega)
  have Kt : Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := (K.mono (by decide)).trans (T.keeps.mono (by decide))
  exact ⟨WitnessMont.data_outside v S O Kt (by decide) (by decide), value, O, Kt⟩

theorem drawn_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {input : Import.Geometry} (I : Import.Context input s)
    (count : input.count = g.words) (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * g.w) :
    WP isa drawn s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (8 * g.w)))
      Prepare.Data g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = sampled.1 ∧
      t.gpr .eax = cmask sampled.2 ∧ Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps clob s t := by
  obtain ⟨-, -, -, words⟩ := fits v
  refine WP.seq (WP.mono (load_ok v S I count source destination) fun a ⟨A, Va, Oa, Ka⟩ => ?_)
  rw [show 4 * g.words = 8 * g.w by omega] at Va
  refine WP.mono (sample_ok v A.ready.context A.ready.modulus.candidate Va odd (by rw [shape]; omega))
    fun t ⟨Vt, mask, Ot, Kt, _⟩ => ?_
  exact ⟨WitnessMont.data_outside v A Ot Kt (by unfold clob; decide) (by unfold clob; decide), Vt, mask,
    Oa.trans Ot, (Ka.mono (by unfold clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessRt
