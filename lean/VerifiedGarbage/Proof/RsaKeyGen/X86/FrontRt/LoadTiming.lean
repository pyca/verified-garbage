module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Load
import VerifiedGarbage.Proof.RsaKeyGen.X86.TimingSeg
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWord
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

/-! # The run-time width's imports and candidate load read the same addresses in every run -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

/-- The public registers' values: `esp`, `edi` and those `extra` gives. -/
def regs (W : Addr) (q : BitVec 32) (extra : Reg → BitVec 32) (r : Reg) : BitVec 32 :=
  if r = .esp then q else if r = .edi then BitVec.ofNat 32 W.toNat else extra r

theorem Space.edi_value {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    s.gpr .edi = BitVec.ofNat 32 W.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := S.scratch.nowrap
  have := S.header
  rw [S.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem Base.vals {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (B : Base W L w q s)
    (extra : Reg → BitVec 32) : ∀ r ∈ [Reg.esp, .edi], s.gpr r = regs W q extra r := by
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact B.2
  · exact B.1.edi_value

/-- A block with `rs` public leaks the same trace. -/
theorem rawBlock {rs : List Reg} {code : List Instr}
    (L : (VG.Taint.check taint (τr rs) (.block code) (.block [])).map (taint.le (τr [])) = some true) :
    RelCT isa (VG.X86.Taint.Agree (τr rs)) (.block code) (fun _ _ => True) :=
  (erased_relCT (σ := τr []) (.block code) (.block code) (.block []) rfl rfl rfl L).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

/-- About to import array `j` from the octets at `src`, `esi` at them. -/
structure SourceIn (W : Addr) (L w : Nat) (q src : BitVec 32) (s : State) : Prop where
  base : Base W L w q s
  esi : s.gpr .esi = src
  sourceFit : src.toNat + 8 * w ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (src.setWidth 64) (8 * w)
  separate : (⟨src.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩

/-- The import's arguments set. -/
structure ImportIn (W : Addr) (L w : Nat) (q src : BitVec 32) (j : Nat) (s : State) : Prop where
  base : Base W L w q s
  context : VG.Proof.RsaKeyGen.X86.Import.Context (importGeometry src (BitVec.ofNat 32 W.toNat) w j) s
  esi : s.gpr .esi = (importGeometry src (BitVec.ofNat 32 W.toNat) w j).sourcePtr 0
  ebx : s.gpr .ebx = (importGeometry src (BitVec.ofNat 32 W.toNat) w j).destPtr 0
  ecx : s.gpr .ecx = BitVec.ofNat 32 (importGeometry src (BitVec.ofNat 32 W.toNat) w j).count

theorem importArgs_trace {W : Addr} {L w : Nat} {q src : BitVec 32} (j : Nat) (index : j < 32)
    (fit : slot w j + 8 * w ≤ L)
    (raw : (VG.Taint.check taint (τr [.esp, .edi]) (.block (importArgs j)) (.block [])).map
      (taint.le (τr [])) = some true) :
    RelCT isa (fun s t => SourceIn W L w q src s ∧ SourceIn W L w q src t) (.block (importArgs j))
      (fun u z => ImportIn W L w q src j u ∧ ImportIn W L w q src j z) := by
  refine seg [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.base.vals _) (rawBlock raw) fun s S => ?_
  have Sp := S.base.1
  have width := Sp.width
  have sourceFit := S.sourceFit
  have below : slot w j < L := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by omega)) fit
  have C : VG.Proof.RsaKeyGen.X86.Import.Context (importGeometry src (s.gpr .edi) w j) s :=
    VG.Proof.RsaKeyGen.X86.Import.context_workspace Sp.scratch (out := slot w j) (n := 2 * w) (by omega) (by omega)
      (by omega)
      (by rw [show 4 * (2 * w) = 8 * w by omega]; exact S.readable)
      (by rw [show 4 * (2 * w) = 8 * w by omega]; exact S.separate)
  rw [Sp.edi_value] at C
  refine WP.mono (importArgs_ok Sp j index below src) fun u ⟨M, K, Pd, Pc⟩ => ?_
  rw [Sp.edi_value] at Pd Pc
  refine ⟨⟨Sp.keepMem K (by decide) (by decide) M, (K.1 .esp (by decide)).trans S.base.2⟩,
    ⟨C.positive, C.sourceFit, C.destFit, fun i index => by rw [K.2.1, K.2.2]; exact C.readable i index,
      fun i index => by rw [K.2.2]; exact C.writable i index, C.separate⟩, ?_, Pd, Pc⟩
  rw [K.1 .esi (by decide), S.esi]
  simp only [VG.Proof.RsaKeyGen.X86.Import.Geometry.sourcePtr, importGeometry, Nat.mul_zero, BitVec.add_zero]

theorem import_trace {W : Addr} {L w : Nat} {q src : BitVec 32} (j : Nat) (fit : slot w j + 8 * w ≤ L)
    (header : 8 ≤ slot w j) :
    RelCT isa (fun s t => ImportIn W L w q src j s ∧ ImportIn W L w q src j t) VG.Impl.RsaKeyGen.X86.Import.code
      (fun u z => Base W L w q u ∧ Base W L w q z) := by
  refine seg [.esp, .edi, .esi, .ebx, .ecx]
    (regs W q fun r => if r = .esi then (importGeometry src (BitVec.ofNat 32 W.toNat) w j).sourcePtr 0
      else if r = .ebx then (importGeometry src (BitVec.ofNat 32 W.toNat) w j).destPtr 0
      else BitVec.ofNat 32 (importGeometry src (BitVec.ofNat 32 W.toNat) w j).count) (fun s S => by
        intro r mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl | rfl | rfl
        · exact S.base.2
        · exact S.base.1.edi_value
        · exact S.esi
        · exact S.ebx
        · exact S.ecx)
    (VG.Proof.RsaKeyGen.X86.Import.code_trace.mono (fun _ _ h => h) (fun _ _ _ => trivial)) fun s S => ?_
  have Sp := S.base.1
  have nowrap := Sp.scratch.nowrap
  have width := Sp.width
  refine WP.mono (VG.Proof.RsaKeyGen.X86.Import.code_ok S.context S.esi S.ebx S.ecx) fun t T => ?_
  have frame := T.frame
  have dstAddr : ((BitVec.ofNat 32 W.toNat) + BitVec.ofNat 32 (slot w j)).setWidth 64 = off W (slot w j) := by
    have below : slot w j < L := by omega
    rw [← Sp.edi_value]; exact Sp.scratch.ea below
  simp only [VG.Proof.RsaKeyGen.X86.Import.Geometry.destRegion, importGeometry] at frame
  rw [dstAddr] at frame
  have O : Outside W (slot w j) (4 * (2 * w)) s.mem t.mem := VG.Proof.RsaKeyGen.frame_outside frame (by omega)
  have len : t.mem.readW (off W 4) 32 = s.mem.readW (off W 4) 32 :=
    BitVec.eq_of_toNat_eq (O.w32 (d := 4) (Or.inl (by omega)) (by omega))
  exact ⟨Sp.keep T.keeps (by decide) (by decide) len, (T.keeps.1 .esp (by decide)).trans S.base.2⟩

/-- Array `j` imported from the octets at `src`. -/
theorem importAt_trace {W : Addr} {L w : Nat} {q src : BitVec 32} (j : Nat) (index : j < 32)
    (fit : slot w j + 8 * w ≤ L) (header : 8 ≤ slot w j)
    (raw : (VG.Taint.check taint (τr [.esp, .edi]) (.block (importArgs j)) (.block [])).map
      (taint.le (τr [])) = some true) :
    RelCT isa (fun s t => SourceIn W L w q src s ∧ SourceIn W L w q src t) (importAt j)
      (fun u z => Base W L w q u ∧ Base W L w q z) :=
  RelCT.seq (importArgs_trace j index fit raw) (import_trace j fit header)

def bitsHead : List Instr :=
  VG.Impl.RsaKeyGen.X86.CandidateBits.forceWord 256 1 ++ [.mov .ebx (.mem (sc 4)), .alu .add .ebx (.reg .edi)]

def bitsTail : List Instr :=
  [.mov .eax (.mem (at_ .ebx 252)), .alu .or .eax (.imm 0xc0000000), .store (at_ .ebx 252) .eax]

theorem bits_split : bits ++ count = bitsHead ++ (bitsTail ++ count) := by
  simp only [bits, bitsHead, bitsTail, List.append_assoc, List.cons_append, List.nil_append]

theorem bitsHead_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (B : Base W L w q s) :
    WP isa (.block bitsHead) s fun c => Base W L w q c ∧ PtrAt c W .ebx (8 * w) := by
  have S := B.1
  have head := S.header
  have nowrap := S.scratch.nowrap
  have width := S.width
  unfold bitsHead
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.CandidateBits.forceWord_ok 1 S.scratch (by omega))
    fun a ⟨_, Oa, Ka⟩ => ?_)
  have Sa := S.keep Ka (by decide) (by decide)
    (BitVec.eq_of_toNat_eq (Oa.w32 (d := 4) (Or.inl (by omega)) (by omega)))
  refine wp_movS Sa.lenRead fun b B' _ => wp_addS rfl fun c C _ => WP.block_nil ?_
  have Kc : Keeps [.eax, .ebx] s c := (Ka.mono (by decide)).trans ((B'.keeps.trans C.keeps).mono (by decide))
  refine ⟨⟨Sa.keepMem ((B'.keeps.trans C.keeps).mono (by decide) : Keeps [.ebx] a c) (by decide) (by decide)
    (by rw [C.mem, B'.mem]), (Kc.1 .esp (by decide)).trans B.2⟩, ?_⟩
  rw [PtrAt, C.gpr, B'.gpr, BitVec.toNat_add, BitVec.toNat_ofNat, B'.other .edi (by decide), Sa.edi_toNat]
  omega

theorem bitsTail_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) (P : PtrAt s W .ebx (8 * w)) :
    WP isa (.block (bitsTail ++ count)) s fun _ => True := by
  have head := S.header
  have nowrap := S.scratch.nowrap
  have width := S.width
  have hw := S.ws
  unfold bitsTail
  refine WP.block_append (wp_movS (readSrc_ptr hw P (d := 252) (by omega)) fun d D _ => wp_orS rfl fun e E => ?_)
  have Ke : Keeps [.eax] s e := (D.keeps.trans E.keeps).mono (by decide)
  have Pe : PtrAt e W .ebx (8 * w) := by
    rw [PtrAt, E.other .ebx (by decide), D.other .ebx (by decide)]; exact P
  have hwe := hw.of_keeps Ke
  refine wp_storeS (ea_ptr hwe Pe (d := 252) (by omega)) (ws_write hwe (y := 8 * w + 252) (n := 4) (by omega))
    fun t T => WP.block_nil ?_
  have Ot : Outside W (8 * w + 252) 4 s.mem t.mem := by
    rw [T.mem, E.mem, D.mem]; exact writeW32_outside _ _ _ (by omega)
  have St := S.keep (Ke.widen (T.keeps [])) (by decide) (by decide)
    (BitVec.eq_of_toNat_eq (Ot.w32 (d := 4) (Or.inl (by omega)) (by omega)))
  exact WP.mono (count_ok St) fun _ _ => trivial

theorem load_trace {W : Addr} {L w : Nat} {q rand : BitVec 32} (width : 4 ≤ w) (space : slot w 5 ≤ L) :
    RelCT isa (fun s t => LoadIn W L w q rand s ∧ LoadIn W L w q rand t) load (fun _ _ => True) := by
  unfold load
  have source := seg (X := LoadIn W L w q rand) (Y := SourceIn W L w q rand) (c := .block [.mov .esi (.mem (sc 28))]) [.esp, .edi] (regs W q fun _ => 0)
    (fun s S => S.base.vals _) (rawBlock (by decide +kernel)) fun s S => by
      have head := S.base.1.header
      refine wp_movS (readSrc_sc S.base.1.scratch (d := 28) (by omega)) fun t T _ => WP.block_nil ?_
      refine ⟨⟨S.base.1.keepMem T.keeps (by decide) (by decide) T.mem, (T.other .esp (by decide)).trans S.base.2⟩,
        T.gpr.trans S.source, S.sourceFit, by rw [T.keeps.2.1, T.keeps.2.2]; exact S.readable, S.separate⟩
  have head := seg (X := Base W L w q) (Y := fun c => Base W L w q c ∧ PtrAt c W .ebx (8 * w)) (c := .block bitsHead)
    [.esp, .edi]
    (regs W q fun _ => 0) (fun s S => S.vals _) (rawBlock (by decide +kernel)) fun s S => bitsHead_ok S
  have tail := seg (X := fun c => Base W L w q c ∧ PtrAt c W .ebx (8 * w)) (Y := fun _ => True)
    (c := .block (bitsTail ++ count)) [.esp, .edi, .ebx]
    (regs W q fun _ => BitVec.ofNat 32 (W.toNat + 8 * w)) (fun s S => by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact S.1.2
      · exact S.1.1.edi_value
      · exact ptr_value S.2) (rawBlock (by decide +kernel)) fun s S => bitsTail_ok S.1.1 S.2
  have fit : slot w 0 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega
  refine RelCT.seq source (RelCT.seq (importAt_trace 0 (by decide) fit
    (by unfold slot VG.Impl.Bignum.hdrBytes; omega) (by decide +kernel)) ?_)
  rw [bits_split]
  exact (RelCT.block_append (RelCT.seq head tail)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.FrontRt
