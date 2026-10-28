module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadPrime
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Widen
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportEncoding
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A prime imported at the run-time width, through its argument pointer -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (arr S num)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

/-- `Key.loadPrime_ok` for the prime at argument `i`. -/
theorem loadPrime_ok {s : State} {B : Addr} {Z n k i out : Nat} {p : BitVec 32}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (ho : out < 32) (persistent : 15 ≤ out)
    (A : VG.Proof.Bignum.X86.CallArgument s B Z (i + 4) p)
    (fit : p.toNat + 4 * k ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (p.setWidth 64) (4 * k))
    (separate : Region.Disjoint ⟨p.setWidth 64, 4 * k⟩ ⟨B, Z⟩) :
    WP isa (loadPrime i out) s fun t =>
      Ws t B Z n 32 ∧ Outs B (VG.Proof.RsaKeyGen.X86.Key.loadPrimeRanges n k out) s.mem t.mem ∧
      num t.mem B n out = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (4 * k)) ∧
      num t.mem B n out < 2 ^ (32 * k) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have small : k ≤ n := by omega
  have nBound := h.old.wle
  have words : Width.prime.words n = k := by simp only [Width.words]; omega
  have space : arr n 0 + 4 * k ≤ Z := by
    have F := h.arr_fit (j := 0) (by decide)
    unfold S at F
    omega
  have noWrap := h.old.workspace.nowrap
  unfold loadPrime VG.Impl.Rsa.X86.Keys.seqs
  simp only [List.cons_append]
  refine WP.seq (wp_movS A.readSrc fun u U _ => ?_)
  have hu := h.keep U.keeps (by rw [U.mem]; exact Outside.refl _ _ _ _)
  refine hu.ptr_ok (arr 0) (r := .ebx) (t := .edx) (by decide) (by decide) (by change arr n 0 < _; omega)
    fun a Ka ma Pa => ?_
  have ha := hu.keep Ka (by rw [ma]; exact Outside.refl _ _ _ _)
  refine ha.bytes_ok .prime .ecx fun b Kb mb eb => ?_
  refine wp_addS rfl fun c Cc _ => wp_subS rfl fun d D _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide)
    fun e Ee => WP.block_nil ?_
  have Ke : Keeps [.esi, .ebx, .edx, .ecx] s e :=
    (((U.keeps.mono (by decide)).trans (Ka.mono (by decide))).trans (Kb.mono (by decide))).trans
      (((Cc.keeps.mono (by decide)).trans (D.keeps.mono (by decide))).trans (Ee.keeps.mono (by decide)))
  have me : e.mem = s.mem := by rw [Ee.mem, D.mem, Cc.mem, mb, ma, U.mem]
  have he := h.keep Ke (by rw [me]; exact Outside.refl _ _ _ _)
  have ebx_b : PtrAt b B .ebx (arr n 0) := by rw [PtrAt, Kb.1 _ (by decide)]; exact Pa
  have ecx_b : (b.gpr .ecx).toNat = 4 * k := by rw [eb, words]
  have edi_s : (s.gpr .edi).toNat = B.toNat := h.old.workspace.edi_toNat
  have edi_e : e.gpr .edi = s.gpr .edi := Ke.1 _ (by decide)
  -- The import's geometry: from `p` to array 0, `k` words.
  have context := VG.Proof.RsaKeyGen.X86.Import.context_workspace (out := arr n 0) he.old.workspace positive space fit
    (by rw [Ke.2.1, Ke.2.2]; exact readable) separate
  have source : e.gpr .esi = (⟨p, e.gpr .edi + BitVec.ofNat 32 (arr n 0), k⟩ : VG.Proof.RsaKeyGen.X86.Import.Geometry).sourcePtr 0 := by
    rw [Ee.other _ (by decide), D.other _ (by decide), Cc.other _ (by decide), Kb.1 _ (by decide), Ka.1 _ (by decide),
      U.gpr]
    simp only [VG.Proof.RsaKeyGen.X86.Import.Geometry.sourcePtr, Nat.mul_zero, BitVec.add_zero]
  have destination : e.gpr .ebx = (⟨p, e.gpr .edi + BitVec.ofNat 32 (arr n 0), k⟩ : VG.Proof.RsaKeyGen.X86.Import.Geometry).destPtr 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [Ee.other _ (by decide), D.gpr, Cc.gpr]
    unfold VG.Proof.RsaKeyGen.X86.Import.Geometry.destPtr
    rw [Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.sub_zero, BitVec.toNat_sub, BitVec.toNat_add,
      BitVec.toNat_add, BitVec.toNat_add, ebx_b, ecx_b, edi_e, edi_s, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (4 : BitVec 32).toNat = 4 from rfl]
    dsimp only
    omega
  have count : e.gpr .ecx = BitVec.ofNat 32 k := by
    apply BitVec.eq_of_toNat_eq
    rw [Ee.gpr, BitVec.toNat_ushiftRight, D.other _ (by decide), Cc.other _ (by decide), ecx_b,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.Import.code_ok context source destination count)
    fun v T => ?_)
  have value := T.os2ip
  have F := T.frame
  have Kv := T.keeps
  have dest : (e.gpr .edi + BitVec.ofNat 32 (arr n 0)).setWidth 64 = off B (arr n 0) :=
    he.old.workspace.ea (d := arr n 0) (by omega)
  change (v.mem.read ((e.gpr .edi + BitVec.ofNat 32 (arr n 0)).setWidth 64) (4 * k)).toNat =
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt e.mem (p.setWidth 64) (4 * k)) at value
  rw [dest, me] at value
  have imported : val32 v.mem B (arr n 0) k = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (4 * k)) := by
    rw [← VG.Proof.Bignum.read_eq_val32]
    exact value
  change Frame [⟨(e.gpr .edi + BitVec.ofNat 32 (arr n 0)).setWidth 64, 4 * k⟩] e.mem v.mem at F
  rw [dest, me] at F
  have Ov : Outside B (arr n 0) (4 * k) s.mem v.mem := VG.Proof.RsaKeyGen.frame_outside F (by omega)
  have Kev : Keeps [.eax, .ebx, .ecx, .edx, .esi] s v := (Ke.mono (by decide)).trans (Kv.mono (by decide))
  have hv := h.keep Kev (Ov.mono (Nat.zero_le _) (by omega))
  have before : arr n 0 + 4 * k ≤ arr n out := by
    have H := VG.Proof.Rsa.X86.Keys.arr_end (w := n) (show 0 < out by omega)
    unfold S at H
    omega
  have outFit := h.arr_fit (j := out) ho
  unfold S at outFit
  refine WP.mono (widen_ok hv .prime (arr out) (arr 0) (by rw [words]; exact small)
    (by change arr n out + _ ≤ Z; omega) (by change arr n 0 + _ ≤ Z; rw [words]; exact space)
    (Or.inl (by change arr n 0 + _ ≤ arr n out; rw [words]; exact before)))
    fun t ⟨ht, Ot, _, copied, Kt⟩ => ?_
  change Outside B (arr n out) (4 * (n + 2)) v.mem t.mem at Ot
  change val32 t.mem B (arr n out) n = val32 v.mem B (arr n 0) (Width.prime.words n) at copied
  rw [words] at copied
  refine ⟨ht, ?_, copied.trans imported, ?_,
    (Kev.mono (by decide)).trans (Kt.mono (by decide))⟩
  · exact (Outs.of_outside Ov (by simp [VG.Proof.RsaKeyGen.X86.Key.loadPrimeRanges])).trans
      (Outs.of_outside (Ot.mono (o' := arr n out) (n' := S n) (Nat.le_refl _) (by unfold S; omega))
        (by simp [VG.Proof.RsaKeyGen.X86.Key.loadPrimeRanges]))
  · change val32 t.mem B (arr n out) n < _
    rw [copied]
    exact val32_lt _ _ _ _

end VG.Proof.RsaKeyGen.X86.KeyRuntime
