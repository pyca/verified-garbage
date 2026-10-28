module

import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Load
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRoundTiming
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.TimingSeg
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.OrLoopRt
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.RegionOutside
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext

/-! # A witness drawn and sampled at the run-time width reads the same addresses in every run

The taint analysis takes what code reads from the workspace for secret, the
header's pointers too: the draw is checked in segments, each run holding the
same pointers and counts at a segment's start, which correctness gives
(`seg`). -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.WitnessRt
open VG.Proof.RsaKeyGen.X86.WitnessRound (Work)

/-- The public registers' values: `esp` at `p`, `edi` at the workspace, and
those `extra` gives. -/
def regs (g : Geometry) (p : BitVec 32) (extra : Reg → BitVec 32) (r : Reg) : BitVec 32 :=
  if r = .esp then p else if r = .edi then BitVec.ofNat 32 g.W.toNat else extra r

theorem edi_value {g : Geometry} {s : State} (C : Context g s) : s.gpr .edi = BitVec.ofNat 32 g.W.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [C.base, BitVec.toNat_ofNat, Nat.add_zero]

theorem toNat_value {x : BitVec 32} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)]

section
variable {g : Geometry} {capacity : Nat} {p : BitVec 32}

theorem _root_.VG.Proof.RsaKeyGen.X86.WitnessRound.Work.context {s : State} (S : Work g capacity p s) : Context g s := by
  obtain ⟨_, D, _⟩ := S
  exact D.ready.context

theorem _root_.VG.Proof.RsaKeyGen.X86.WitnessRound.Work.sp {s : State} (S : Work g capacity p s) : s.gpr .esp = p := by
  obtain ⟨_, D, _⟩ := S
  exact D.ready.caller.sp

theorem _root_.VG.Proof.RsaKeyGen.X86.WitnessRound.Work.keep (v : g.Valid) {s t : State} (S : Work g capacity p s) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) (O : Outside g.W (g.array 6) (4 * g.words) s.mem t.mem) :
    Work g capacity p t := by
  obtain ⟨c, D, odd, large⟩ := S
  exact ⟨c, WitnessMont.data_outside v D O K edi esp, odd, large⟩

theorem _root_.VG.Proof.RsaKeyGen.X86.WitnessRound.Work.keepMem (v : g.Valid) {s t : State} (S : Work g capacity p s) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) (M : t.mem = s.mem) : Work g capacity p t :=
  S.keep v K edi esp (by rw [M]; exact Outside.refl _ _ _ _)

/-- Every run holds the same `esp`, `edi` and, in `r`, the pointer at `x`. -/
theorem ptrSeg {X Y : State → Prop} {c : Prog isa} (r : Reg) (x : Nat) (notSp : r ≠ .esp) (notBase : r ≠ .edi)
    (work : ∀ s, X s → Work g capacity p s) (ptr : ∀ s, X s → PtrAt s g.W r x)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, r])) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) := by
  refine seg [.esp, .edi, r] (regs g p fun _ => BitVec.ofNat 32 (g.W.toNat + x)) (fun s S r' mem => ?_) raw run
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact (work s S).sp
  · exact edi_value (work s S).context
  · simp only [regs, notSp, notBase, ↓reduceIte]
    exact ptr_value (ptr s S)

/-- Every run holds the same `esp` and `edi`. -/
theorem baseSeg {X Y : State → Prop} {c : Prog isa} (work : ∀ s, X s → Work g capacity p s)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) := by
  refine seg [.esp, .edi] (regs g p fun _ => 0) (fun s S r mem => ?_) raw run
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact (work s S).sp
  · exact edi_value (work s S).context

/-- Prepared, with a pointer at `x` in `r`. -/
def At (g : Geometry) (capacity : Nat) (p : BitVec 32) (r : Reg) (x : Nat) (s : State) : Prop :=
  Work g capacity p s ∧ PtrAt s g.W r x

theorem ptr6_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) (.block (VG.Impl.MillerRabin.X86.ptr .ebp 6))
      (fun u z => At g capacity p .ebp (g.array 6) u ∧ At g capacity p .ebp (g.array 6) z) :=
  baseSeg (fun _ S => S) (rawBlock (by decide +kernel)) fun s S =>
    WP.mono (ptr_short v S.context 6 (by decide) .ebp) fun _ ⟨P, M, K⟩ =>
      ⟨S.keepMem v K (by decide) (by decide) M, P⟩

/-! ## Frames of the blocks whose results the trace does not need -/

theorem lowerAt_frame {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x) (fit : x + 4 ≤ L) :
    WP isa (.block lowerAt) s fun t => t.mem = s.mem ∧ Keeps [.eax, .ebx] s t := by
  unfold lowerAt
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega)) fun b B _ => wp_orS rfl fun c Cc =>
    wp_logicS (.inr rfl) rfl fun d D => wp_orS rfl fun e E => ?_
  refine wp_cmpi fun f F cf _ => wp_sbb_self cf fun h H => wp_logicS (.inr rfl) rfl fun i I =>
    wp_movS rfl fun j J _ => wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  exact ⟨by rw [T.mem, J.mem, I.mem, H.mem, F.mem, E.mem, D.mem, Cc.mem, B.mem],
    (((((((((B.keeps.mono (by decide)).widen Cc.keeps).widen D.keeps).widen E.keeps).trans
      (F.keeps _)).widen H.keeps).widen I.keeps).widen J.keeps).widen T.keeps)⟩

theorem fallbackLow_frame {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x)
    (fit : x + 4 ≤ L) :
    WP isa (.block fallbackLow) s fun t => Outside W x 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold fallbackLow
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B => wp_logicS (.inl rfl) rfl fun c C => ?_
  have Kc : Keeps [.ecx] s c := (A.keeps.widen B.keeps).widen C.keeps
  have Pc : PtrAt c W .ebp x := by rw [PtrAt, Kc.1 .ebp (by decide)]; exact P
  refine wp_orS (readSrc_ptr (hw.of_keeps Kc) Pc (d := 0) (by omega)) fun d D => ?_
  have Kd : Keeps [.ecx] s d := Kc.widen D.keeps
  have wd := hw.of_keeps Kd
  have Pd : PtrAt d W .ebp x := by rw [PtrAt, Kd.1 .ebp (by decide)]; exact P
  refine wp_storeS (ea_ptr wd Pd (d := 0) (by omega)) (ws_write wd (y := x + 0) (n := 4) (by omega))
    fun t T => WP.block_nil ⟨?_, Kd.widen (T.keeps [])⟩
  rw [T.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
  exact writeW32_outside _ _ _ (by have := hw.nowrap; omega)

theorem fallbackHigh_frame {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebx x)
    (fit : x + 4 ≤ L) :
    WP isa (.block fallbackHigh) s fun t => Outside W x 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold fallbackHigh
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B =>
    wp_logicS (.inl rfl) rfl fun c C => wp_logicS (.inr rfl) rfl fun d D => ?_
  have Kd : Keeps [.ecx] s d := ((A.keeps.widen B.keeps).widen C.keeps).widen D.keeps
  have Pd : PtrAt d W .ebx x := by rw [PtrAt, Kd.1 .ebx (by decide)]; exact P
  refine wp_logicS (.inl rfl) (readSrc_ptr (hw.of_keeps Kd) Pd (d := 0) (by omega)) fun e E => ?_
  have Ke : Keeps [.ecx] s e := Kd.widen E.keeps
  have we := hw.of_keeps Ke
  have Pe : PtrAt e W .ebx x := by rw [PtrAt, Ke.1 .ebx (by decide)]; exact P
  refine wp_storeS (ea_ptr we Pe (d := 0) (by omega)) (ws_write we (y := x + 0) (n := 4) (by omega))
    fun t T => WP.block_nil ⟨?_, Ke.widen (T.keeps [])⟩
  rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
  exact writeW32_outside _ _ _ (by have := hw.nowrap; omega)

/-! ## The sampler's segments -/

theorem mark_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) (.block mark)
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, -⟩ := fits v
  unfold mark
  exact RelCT.block_append (RelCT.seq (ptr6_trace v)
    (ptrSeg .ebp (g.array 6) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2) (rawBlock (by decide +kernel))
      fun s S => WP.mono (markAt_ok S.1.context.ws S.2 (n := g.words) (by omega) fit) fun _ ⟨_, _, O, K⟩ =>
        S.1.keep v K (by decide) (by decide) (O.mono (by omega) (by omega))))

/-- About to compare the witness with the candidate. -/
def Comparing (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Work g capacity p s ∧ PtrAt s g.W .esi (g.array 6) ∧ PtrAt s g.W .ebp (g.array 0) ∧
    (s.gpr .edx).toNat = 4 * g.words ∧ s.gpr .ecx = cmask false

theorem lessLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .esi, .ebp, .edx])) lessLoop
    (fun _ _ => True) :=
  (erased_relCT (σ := τr []) lessLoop lessLoop
    (VG.Taint.hintOf taint (τr [.esp, .edi, .esi, .ebp, .edx]) (Code.erase lessLoop))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem less_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) less
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, below, many, words⟩ := fits v
  have bound := v.maxWidth
  have nowrap := v.headerFit
  unfold less
  refine RelCT.seq (R := fun u z => Comparing g capacity p u ∧ Comparing g capacity p z)
    (baseSeg (fun _ S => S) (rawBlock (by decide +kernel)) fun s S =>
      WP.mono (lessArgs_ok v S.context) fun _ ⟨esi, ebp, edx, ecx, M, K⟩ =>
        ⟨S.keepMem v K (by decide) (by decide) M, esi, ebp, edx, ecx⟩) ?_
  refine seg [.esp, .edi, .esi, .ebp, .edx] (regs g p fun r => if r = .esi then BitVec.ofNat 32 (g.W.toNat + g.array 6)
    else if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 0) else BitVec.ofNat 32 (4 * g.words))
    (fun s S r mem => ?_) lessLoop_raw fun s S => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    · exact S.1.sp
    · exact edi_value S.1.context
    · exact ptr_value S.2.1
    · exact ptr_value S.2.2.1
    · exact toNat_value S.2.2.2.1
  · exact WP.mono (VG.Proof.Bignum.X86.PublicRt.compareLoop_ok S.1.context.ws (x := g.array 6) (y := g.array 0)
      (N := g.words) (by omega) (by omega) (by omega) S.2.1 S.2.2.1 S.2.2.2.1 S.2.2.2.2) fun _ ⟨M, _, K⟩ =>
        S.1.keepMem v K (by decide) (by decide) M

theorem restore_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) (.block restore)
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, -⟩ := fits v
  unfold restore
  exact RelCT.block_append (RelCT.seq (ptr6_trace v)
    (ptrSeg .ebp (g.array 6) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2) (rawBlock (by decide +kernel))
      fun s S => WP.mono (restoreAt_ok S.1.context.ws S.2 (by omega)) fun _ ⟨_, O, _, K⟩ =>
        S.1.keep v K (by decide) (by decide) (O.mono (by omega) (by omega))))

/-- About to scan the witness's words above its lowest. -/
def Scanning (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Work g capacity p s ∧ PtrAt s g.W .ebp (g.array 6 + 4) ∧ (s.gpr .ecx).toNat = g.words - 1 ∧ s.gpr .ebx = 0#32

theorem orLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebp, .ecx])) orLoop (fun _ _ => True) :=
  (erased_relCT (σ := τr []) orLoop orLoop (VG.Taint.hintOf taint (τr [.esp, .edi, .ebp, .ecx]) (Code.erase orLoop))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem scan_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) scan
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, words⟩ := fits v
  unfold scan
  refine RelCT.seq (R := fun u z => Scanning g capacity p u ∧ Scanning g capacity p z)
    (baseSeg (fun _ S => S) (rawBlock (by decide +kernel)) fun s S =>
      WP.mono (scanArgs_ok v S.context) fun _ ⟨P, count, zero, M, K⟩ =>
        ⟨S.keepMem v K (by decide) (by decide) M, P, count, zero⟩) ?_
  refine seg [.esp, .edi, .ebp, .ecx] (regs g p fun r => if r = .ebp then BitVec.ofNat 32 (g.W.toNat + (g.array 6 + 4))
    else BitVec.ofNat 32 (g.words - 1)) (fun s S r mem => ?_) orLoop_raw fun s S => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl
    · exact S.1.sp
    · exact edi_value S.1.context
    · exact ptr_value S.2.1
    · exact toNat_value S.2.2.1
  · exact WP.mono (FrontRt.orLoop_ok S.1.context.ws (by omega) (by omega) S.2.1 S.2.2.1 S.2.2.2) fun _ ⟨_, M, _, K⟩ =>
      S.1.keepMem v K (by decide) (by decide) M

theorem finish_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) (.block (lower ++ fallback))
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, words⟩ := fits v
  unfold lower fallback
  simp only [List.append_assoc]
  have lowerT : RelCT isa (fun s t => At g capacity p .ebp (g.array 6) s ∧ At g capacity p .ebp (g.array 6) t)
      (.block lowerAt) (fun u z => Work g capacity p u ∧ Work g capacity p z) :=
    ptrSeg .ebp (g.array 6) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2) (rawBlock (by decide +kernel))
      fun s S => WP.mono (lowerAt_frame S.1.context.ws S.2 (by omega)) fun _ ⟨M, K⟩ =>
        S.1.keepMem v K (by decide) (by decide) M
  have lowT : RelCT isa (fun s t => At g capacity p .ebp (g.array 6) s ∧ At g capacity p .ebp (g.array 6) t)
      (.block fallbackLow) (fun u z => At g capacity p .ebp (g.array 6) u ∧ At g capacity p .ebp (g.array 6) z) :=
    ptrSeg .ebp (g.array 6) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2) (rawBlock (by decide +kernel))
      fun s S => WP.mono (fallbackLow_frame S.1.context.ws S.2 (by omega)) fun _ ⟨O, K⟩ =>
        ⟨S.1.keep v K (by decide) (by decide) (O.mono (by omega) (by omega)), by
          rw [PtrAt, K.1 .ebp (by decide)]; exact S.2⟩
  have topT : RelCT isa (fun s t => At g capacity p .ebp (g.array 6) s ∧ At g capacity p .ebp (g.array 6) t)
      (.block fallbackTop) (fun u z => At g capacity p .ebx (g.array 6 + 4 * g.words - 4) u ∧
        At g capacity p .ebx (g.array 6 + 4 * g.words - 4) z) :=
    baseSeg (fun _ S => S.1) (rawBlock (by decide +kernel)) fun s S =>
      WP.mono (fallbackTop_ok v S.1.context S.2) fun _ ⟨P, M, K⟩ => ⟨S.1.keepMem v K (by decide) (by decide) M, P⟩
  have highT : RelCT isa (fun s t => At g capacity p .ebx (g.array 6 + 4 * g.words - 4) s ∧
      At g capacity p .ebx (g.array 6 + 4 * g.words - 4) t)
      (.block fallbackHigh) (fun u z => Work g capacity p u ∧ Work g capacity p z) :=
    ptrSeg .ebx (g.array 6 + 4 * g.words - 4) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2)
      (rawBlock (by decide +kernel)) fun s S => WP.mono (fallbackHigh_frame S.1.context.ws S.2 (by omega))
        fun _ ⟨O, K⟩ => S.1.keep v K (by decide) (by decide) (O.mono (by omega) (by omega))
  exact RelCT.block_append (RelCT.seq (ptr6_trace v) (RelCT.block_append (RelCT.seq lowerT
    (RelCT.block_append (RelCT.seq (ptr6_trace v) (RelCT.block_append (RelCT.seq lowT
      (RelCT.block_append (RelCT.seq topT highT)))))))))

theorem sample_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) sample
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  unfold sample
  exact RelCT.seq (mark_trace v) (RelCT.seq (less_trace v) (RelCT.seq (restore_trace v)
    (RelCT.seq (scan_trace v) (finish_trace v))))

/-! ## The witness's draw -/

/-- `Import.code`'s arguments set for the draw `input`. -/
def Importing (g : Geometry) (capacity : Nat) (p : BitVec 32) (input : Import.Geometry) (s : State) : Prop :=
  Work g capacity p s ∧ Import.Context input s ∧ s.gpr .esi = input.sourcePtr 0 ∧
    s.gpr .ebx = input.destPtr 0 ∧ s.gpr .ecx = BitVec.ofNat 32 input.count ∧
    input.dst.setWidth 64 = off g.W (g.array 6)

theorem load_trace (v : g.Valid) {input : Import.Geometry} (count : input.count = g.words) :
    RelCT isa (fun s t => WitnessRound.Initial g capacity p input s ∧ WitnessRound.Initial g capacity p input t) load
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, -⟩ := fits v
  unfold load
  refine RelCT.seq (R := fun u z => Importing g capacity p input u ∧ Importing g capacity p input z)
    (baseSeg (fun _ ⟨c, D, odd, large, _⟩ => ⟨c, D, odd, large⟩) (rawBlock (by decide +kernel))
      fun s ⟨c, D, odd, large, _, I, source, destination⟩ =>
        WP.mono (importArgs_ok v D.ready.context count source destination) fun t ⟨M, K, Ps, Pd, Pc⟩ =>
          ⟨(show Work g capacity p s from ⟨c, D, odd, large⟩).keepMem v K (by decide) (by decide) M,
            ⟨I.positive, I.sourceFit, I.destFit, fun i index => by rw [K.2.1, K.2.2]; exact I.readable i index,
              fun i index => by rw [K.2.2]; exact I.writable i index, I.separate⟩, Ps, Pd, Pc,
            by rw [← destination]; exact D.ready.scratch.ea (d := g.array 6) (by omega)⟩) ?_
  refine seg [.esp, .edi, .esi, .ebx, .ecx] (regs g p fun r => if r = .esi then input.sourcePtr 0
    else if r = .ebx then input.destPtr 0 else BitVec.ofNat 32 input.count) (fun s S r mem => ?_)
    (VG.Proof.RsaKeyGen.X86.Import.code_trace.mono (fun _ _ h => h) (fun _ _ _ => trivial)) fun s S => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    · exact S.1.sp
    · exact edi_value S.1.context
    · exact S.2.2.1
    · exact S.2.2.2.1
    · exact S.2.2.2.2.1
  · obtain ⟨Sw, I, Ps, Pd, Pc, dstAddr⟩ := S
    have C := Sw.context
    have nowrap := C.ws.nowrap
    refine WP.mono (VG.Proof.RsaKeyGen.X86.Import.code_ok I Ps Pd Pc) fun t T => ?_
    have F := T.frame
    have region : input.destRegion = ⟨off g.W (g.array 6), 4 * input.count⟩ := by
      unfold Import.Geometry.destRegion
      rw [dstAddr]
    rw [region, count] at F
    exact Sw.keep v T.keeps (by decide) (by decide) (frame_outside F (by omega))

end

end VG.Proof.RsaKeyGen.X86.WitnessRt
