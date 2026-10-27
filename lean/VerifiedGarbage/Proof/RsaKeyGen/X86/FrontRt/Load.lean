module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Pointer
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportEncoding
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWord
import VerifiedGarbage.Proof.RsaKeyGen.Bits32

import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside

/-! # The candidate drawn into array 0 at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

/-- The import of array `j`: its `2 w` words from the octets at `src`. -/
def importGeometry (src edi : BitVec 32) (w j : Nat) : VG.Proof.RsaKeyGen.X86.Import.Geometry :=
  ⟨src, edi + BitVec.ofNat 32 (slot w j), 2 * w⟩

theorem ptr_eq {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) {r : Reg} {x : Nat}
    (P : PtrAt s W r x) (fit : x < L) : s.gpr r = s.gpr .edi + BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  have nowrap := S.scratch.nowrap
  have bound := fit
  rw [P, BitVec.toNat_add, BitVec.toNat_ofNat, S.edi_toNat]
  omega

theorem importArgs_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) (j : Nat) (index : j < 32)
    (fit : slot w j < L) (src : BitVec 32) :
    WP isa (.block (importArgs j)) s fun u =>
      u.mem = s.mem ∧ Keeps [.ebx, .ecx, .edx] s u ∧
      u.gpr .ebx = (importGeometry src (s.gpr .edi) w j).destPtr 0 ∧
      u.gpr .ecx = BitVec.ofNat 32 (importGeometry src (s.gpr .edi) w j).count := by
  have head := S.header
  have bound := S.widthBound
  have width := S.width
  unfold importArgs
  refine WP.block_append (WP.mono (lenPtr_ok S j index (by decide : Reg.edx ≠ .ebx) (by decide) (by decide))
    fun a ⟨P, M, K⟩ => ?_)
  have Sa := S.keepMem K (by decide) (by decide) M
  refine wp_movS Sa.lenRead fun b B _ => wp_addS rfl fun c C _ => wp_subS rfl fun d D _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u U => WP.block_nil ?_
  have edi : a.gpr .edi = s.gpr .edi := K.1 .edi (by decide)
  have ebx : a.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 (slot w j) := by rw [ptr_eq Sa P fit, edi]
  have Ku : Keeps [.ebx, .ecx, .edx] s u :=
    ((((K.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen U.keeps
  refine ⟨by rw [U.mem, D.mem, C.mem, B.mem, M], Ku, ?_, ?_⟩
  · rw [U.other .ebx (by decide), D.gpr, C.gpr, B.other .ebx (by decide), ebx, B.gpr]
    unfold VG.Proof.RsaKeyGen.X86.Import.Geometry.destPtr importGeometry
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]
    omega
  · rw [U.gpr, D.other .ecx (by decide), C.other .ecx (by decide), B.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, importGeometry]
    omega

theorem importAt_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) (j : Nat) (index : j < 32)
    (fit : slot w j + 8 * w ≤ L) {src : BitVec 32} (source : s.gpr .esi = src)
    (sourceFit : src.toNat + 8 * w ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (src.setWidth 64) (8 * w))
    (separate : (⟨src.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩) :
    WP isa (importAt j) s fun t =>
      val32 t.mem W (slot w j) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (src.setWidth 64) (8 * w)) ∧
      Frame [⟨off W (slot w j), 8 * w⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx, .edx] s t := by
  have width := S.width
  have C : VG.Proof.RsaKeyGen.X86.Import.Context (importGeometry src (s.gpr .edi) w j) s :=
    VG.Proof.RsaKeyGen.X86.Import.context_workspace S.scratch (out := slot w j) (n := 2 * w) (by omega) (by omega)
      (by omega)
      (by rw [show 4 * (2 * w) = 8 * w by omega]; exact readable)
      (by rw [show 4 * (2 * w) = 8 * w by omega]; exact separate)
  have below : slot w j < L := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by omega)) fit
  have dstAddr : (s.gpr .edi + BitVec.ofNat 32 (slot w j)).setWidth 64 = off W (slot w j) :=
    S.scratch.ea below
  unfold importAt
  refine WP.seq (WP.mono (importArgs_ok S j index below src)
    fun a ⟨M, K, Pd, Pc⟩ => ?_)
  have Ca : VG.Proof.RsaKeyGen.X86.Import.Context (importGeometry src (s.gpr .edi) w j) a :=
    ⟨C.positive, C.sourceFit, C.destFit, fun i index => by rw [K.2.1, K.2.2]; exact C.readable i index,
      fun i index => by rw [K.2.2]; exact C.writable i index, C.separate⟩
  have Ps : a.gpr .esi = (importGeometry src (s.gpr .edi) w j).sourcePtr 0 := by
    rw [K.1 .esi (by decide), source]
    simp only [VG.Proof.RsaKeyGen.X86.Import.Geometry.sourcePtr, importGeometry, Nat.mul_zero, BitVec.add_zero]
  refine WP.mono (VG.Proof.RsaKeyGen.X86.Import.code_ok Ca Ps Pd Pc) fun t T => ?_
  have value := T.os2ip
  have frame := T.frame
  rw [M] at value frame
  simp only [VG.Proof.RsaKeyGen.X86.Import.Geometry.destRegion, importGeometry] at frame value
  rw [dstAddr, show 4 * (2 * w) = 8 * w by omega] at frame value
  refine ⟨?_, frame, (K.mono (by decide)).widen T.keeps⟩
  rw [← VG.Proof.Bignum.read_eq_val32, show 4 * (2 * w) = 8 * w by omega]
  exact value

theorem bits_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    WP isa (.block bits) s fun t =>
      val32 t.mem W 256 (2 * w) = Spec.RsaKeyGen.candidate (64 * w) (val32 s.mem W 256 (2 * w)) ∧
      Outside W 256 (8 * w) s.mem t.mem ∧ Keeps [.eax, .ebx] s t := by
  have head := S.header
  have nowrap := S.scratch.nowrap
  have width := S.width
  unfold bits
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.CandidateBits.forceWord_ok 1 S.scratch (by omega))
    fun a ⟨low, Oa, Ka⟩ => ?_)
  have Sa := S.keep Ka (by decide) (by decide)
    (BitVec.eq_of_toNat_eq (Oa.w32 (d := 4) (Or.inl (by omega)) (by omega)))
  refine wp_movS Sa.lenRead fun b B _ => wp_addS rfl fun c C _ => ?_
  have Kc : Keeps [.eax, .ebx] a c := (B.keeps.trans C.keeps).mono (by decide)
  have P : PtrAt c W .ebx (8 * w) := by
    rw [PtrAt, C.gpr, B.gpr, BitVec.toNat_add, BitVec.toNat_ofNat, B.other .edi (by decide), Sa.edi_toNat]
    omega
  have hw := Sa.ws.of_keeps Kc
  refine wp_movS (readSrc_ptr hw P (d := 252) (by omega)) fun d D _ => wp_orS rfl fun e E => ?_
  have Ke : Keeps [.eax, .ebx] c e := (D.keeps.trans E.keeps).mono (by decide)
  have Pe : PtrAt e W .ebx (8 * w) := by
    rw [PtrAt, E.other .ebx (by decide), D.other .ebx (by decide)]; exact P
  have hwe := hw.of_keeps Ke
  refine wp_storeS (ea_ptr hwe Pe (d := 252) (by omega)) (ws_write hwe (y := 8 * w + 252) (n := 4) (by omega))
    fun t T => WP.block_nil ?_
  have Mc : c.mem = a.mem := by rw [C.mem, B.mem]
  have Ot : Outside W (8 * w + 252) 4 a.mem t.mem := by
    rw [T.mem, E.mem, D.mem, Mc]; exact writeW32_outside _ _ _ (by omega)
  have topT : w32 t.mem W (8 * w + 252) = w32 a.mem W (8 * w + 252) ||| 3 * 2 ^ 30 := by
    rw [T.mem, w32_write_self, E.gpr, D.gpr, Mc, BitVec.toNat_or]
    rfl
  have topA : w32 a.mem W (8 * w + 252) = w32 s.mem W (8 * w + 252) := Oa.w32 (Or.inr (by omega)) (by omega)
  have lowT : w32 t.mem W 256 = w32 a.mem W 256 := by rw [T.mem, E.mem, D.mem, Mc]; exact w32_write_ne nowrap (by omega) (by omega) (by omega) _
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)),
    ((Ka.mono (by decide)).trans Kc).trans Ke |>.widen (T.keeps [])⟩
  rw [show 64 * w = 32 * (2 * w) by omega]
  apply VG.Proof.RsaKeyGen.val32_candidate (by omega)
  · rw [lowT, low]
    rfl
  · rw [show 256 + 4 * (2 * w - 1) = 8 * w + 252 by omega, topT, topA]
  · intro j first last
    rw [T.mem, E.mem, D.mem, Mc, w32_write_ne nowrap (by omega) (by omega) (by omega) _]
    exact Oa.w32 (by omega) (by omega)

theorem count_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    WP isa (.block count) s fun t =>
      word t.mem W 152 = BitVec.ofNat 64 (8 * w) ∧ Outside W 152 8 s.mem t.mem ∧ Keeps [.eax] s t := by
  have head := S.header
  have bound := S.widthBound
  unfold count
  refine wp_movS S.lenRead fun a A _ =>
    wp_storeS ((S.scratch.of_keeps A.keeps (by decide)).ea (d := 152) (by omega))
      ((S.scratch.of_keeps A.keeps (by decide)).write (by omega)) fun b B =>
    wp_movS rfl fun c C _ => ?_
  have Kc := (A.keeps.widen (B.keeps [])).trans C.keeps
  have Sc := S.scratch.of_keeps Kc (by decide)
  refine wp_storeS (Sc.ea (d := 156) (by omega)) (Sc.write (by omega)) fun t T => WP.block_nil ?_
  have pair : (0#32 ++ BitVec.ofNat 32 (8 * w)) = BitVec.ofNat 64 (8 * w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or,
      Nat.mod_eq_of_lt (show 8 * w < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show 8 * w < 2 ^ 64 by omega)]
  have memory : t.mem = s.mem.writeW (off W 152) (BitVec.ofNat 64 (8 * w)) := by
    rw [T.mem, C.mem, B.mem, A.mem, C.gpr, A.gpr]
    have high : off W 156 = off W 152 + BitVec.ofNat 64 4 := by
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [high, ← VG.Proof.Rc2.Word32.write64_pair]
    change s.mem.writeW (off W 152) (0#32 ++ BitVec.ofNat 32 (8 * w)) = _
    rw [pair]
  refine ⟨?_, ?_, Kc.widen (T.keeps [])⟩
  · rw [memory]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [memory]
    exact writeW_outside _ _ _ (by decide)

theorem load_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) {rand : BitVec 32}
    (sourceFit : rand.toNat + 8 * w ≤ 2 ^ 32) (sourceEq : s.mem.readW (off W 28) 32 = rand)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) (8 * w))
    (separate : (⟨rand.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩) :
    WP isa load s fun t =>
      val32 t.mem W (slot w 0) (2 * w) = Spec.RsaKeyGen.candidate (64 * w)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (rand.setWidth 64) (8 * w))) ∧
      word t.mem W 152 = BitVec.ofNat 64 (8 * w) ∧
      Frame [⟨off W (slot w 0), 8 * w⟩, ⟨off W 152, 8⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .ecx, .edx] s t := by
  have head := S.header
  have nowrap := S.scratch.nowrap
  have slot0 := VG.Proof.RsaKeyGen.X86.ExponentRt.slot0_eq w
  unfold load
  refine WP.seq (wp_movS (readSrc_sc S.scratch (d := 28) (by omega)) fun a A _ => WP.block_nil ?_)
  have Sa := S.keepMem A.keeps (by decide) (by decide) A.mem
  refine WP.seq (WP.mono (importAt_ok Sa 0 (by decide) (by rw [slot0]; omega) (by rw [A.gpr]; exact sourceEq)
    sourceFit (by rw [A.keeps.2.1, A.keeps.2.2]; exact readable) separate) fun b ⟨value, Fb, Kb⟩ => ?_)
  rw [A.mem, slot0] at value Fb
  have Ob := VG.Proof.RsaKeyGen.frame_outside Fb (by omega)
  have Sb := Sa.keep Kb (by decide) (by decide)
    (by rw [A.mem]; exact BitVec.eq_of_toNat_eq (Ob.w32 (d := 4) (Or.inl (by omega)) (by omega)))
  refine WP.block_append (WP.mono (bits_ok Sb) fun c ⟨cand, Oc, Kc⟩ => ?_)
  have Sc := Sb.keep Kc (by decide) (by decide) (BitVec.eq_of_toNat_eq (Oc.w32 (d := 4) (Or.inl (by omega)) (by omega)))
  refine WP.mono (count_ok Sc) fun t ⟨countT, Ot, Kt⟩ => ?_
  rw [slot0]
  have kept : val32 t.mem W 256 (2 * w) = val32 c.mem W 256 (2 * w) :=
    Ot.val32 (Or.inr (by omega)) (by omega)
  refine ⟨by rw [kept, cand, value], countT, ?_, ?_⟩
  · have Fc := VG.Proof.Bignum.outside_frame Oc (by omega)
    have Ft := VG.Proof.Bignum.outside_frame Ot (by decide)
    exact ((Fb.mono (fun _ mem => by obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)).trans
      (Fc.mono (fun _ mem => by obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self))).trans
      (Ft.mono (fun _ mem => List.mem_cons_of_mem _ mem))
  · exact (A.keeps.mono (by decide)).trans ((Kb.trans (Kc.mono (by decide))).trans (Kt.mono (by decide)))

/-- The workspace at `edi` and the stack pointer `q`. -/
def Base (W : Addr) (L w : Nat) (q : BitVec 32) (s : State) : Prop := Space W L w s ∧ s.gpr .esp = q

/-- The candidate's source, at header byte 28. -/
structure LoadIn (W : Addr) (L w : Nat) (q rand : BitVec 32) (s : State) : Prop where
  base : Base W L w q s
  source : s.mem.readW (off W 28) 32 = rand
  sourceFit : rand.toNat + 8 * w ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) (8 * w)
  separate : (⟨rand.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩

end VG.Proof.RsaKeyGen.X86.FrontRt
