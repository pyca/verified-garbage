module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MrExponentRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Scan
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Code
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowBit
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentReady
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Miller–Rabin's exponent at the run-time width reads the same addresses in every run

The pointers and counts come from the prepared header, which the taint
analysis takes for secret: each run computes them from the same header, so
they agree once correctness gives their values, and the loops are then
checked with them public.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.MrExponentRt
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)

/-- Runs from states whose registers `rs` hold the same values `f r` leak
the same trace (`raw`), and each run ends in `Y` by correctness. -/
theorem seg {X Y : State → Prop} {c : Prog isa} (rs : List Reg) (f : Reg → BitVec 32)
    (vals : ∀ s, X s → ∀ r ∈ rs, s.gpr r = f r)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr rs)) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have agree : VG.X86.Taint.Agree (τr rs) s t :=
    agree_regs fun r mem => (vals s S r mem).trans (vals t T r mem).symm
  exact ⟨(raw _ _ _ _ _ _ agree E G).1, wp_result (run s S) E, wp_result (run t T) G⟩

/-- A trace from a relation, and each run ending in `Y`. -/
theorem withRuns {X Y : State → Prop} {c : Prog isa} {R : State → State → Prop}
    (raw : RelCT isa (fun s t => X s ∧ X t) c R) (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  exact ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1, wp_result (run s S) E, wp_result (run t T) G⟩

/-- Prepared, for some candidate. -/
def Prepared (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s

/-- The workspace pointer, from the header's base. -/
theorem edi_value {g : Geometry} {s : State} (C : Context g s) : s.gpr .edi = BitVec.ofNat 32 g.W.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [C.base, BitVec.toNat_ofNat, Nat.add_zero]

theorem ptr_value {s : State} {W : Addr} {r : Reg} {x : Nat} (P : PtrAt s W r x) :
    s.gpr r = BitVec.ofNat 32 (W.toNat + x) := by
  apply BitVec.eq_of_toNat_eq
  rw [P, BitVec.toNat_ofNat]

theorem prepared_pair {g : Geometry} {capacity : Nat} {p : BitVec 32} {s t : State}
    (S : Prepared g capacity p s) (T : Prepared g capacity p t) : Pair g [.edi] s t := by
  obtain ⟨_, S⟩ := S
  obtain ⟨_, T⟩ := T
  refine ⟨S.context, T.context, agree_regs fun r mem => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.caller.sp.trans T.caller.sp.symm
  · exact (edi_value S.context).trans (edi_value T.context).symm

/-- In the scan's frame. -/
def Framed (g : Geometry) (capacity : Nat) (p : BitVec 32) (a : State) : Prop :=
  ∃ s, Prepared g capacity p s ∧ a = allocFrame 20 s

/-- Ready to scan: `ebp` at array 5 and `edi` its pairs. -/
structure Scanning (g : Geometry) (p : BitVec 32) (a : State) : Prop where
  ws : Ws a g.W g.L
  stack : VG.Proof.RsaKeyGen.X86.Sieve.StackContext (p - 20#32) a
  ebp : PtrAt a g.W .ebp (g.array 5)
  count : (a.gpr .edi).toNat = g.w

theorem scan_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) scan
      (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) := by
  refine withRuns (R := fun _ _ => True) ?_ fun s ⟨c, S⟩ => WP.mono (scan_ok v S) fun t ⟨_, F, K⟩ =>
    ⟨c, (Ready.keepStack v S K (by decide) (by decide) F).1⟩
  unfold scan
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  have setupRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block scanSetup) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have setup := seg (X := Framed g capacity p) (Y := Scanning g p) [.esp, .edi]
    (fun r => if r = .esp then p - 20#32 else BitVec.ofNat 32 g.W.toNat) (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [allocFrame_esp, S.caller.sp]; rfl
      · rw [allocFrame_gpr _ _ (by decide)]; exact edi_value S.context) setupRaw (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      have sp := S.caller.sp
      have St : VG.Proof.RsaKeyGen.X86.Sieve.StackContext (p - 20#32) (allocFrame 20 s) := by
        rw [← sp]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; have := S.caller.low; omega)
      have C := S.context
      have Ci : Context g (allocFrame 20 s) :=
        ⟨⟨List.mem_cons_of_mem _ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, allocFrame_gpr _ _ (by decide)]; exact C.base,
          C.width, C.stride, C.pointers⟩
      exact WP.mono (scanSetup_ok v Ci St) fun a ⟨_, _, P, count, _, _, K⟩ =>
        ⟨Ci.ws.of_keeps K, St.keep K (by decide), P, count⟩)
  have loopRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .edi])) (.loop (.block pairStep) .ne)
      (fun _ _ => True) :=
    (erased_relCT (.loop (.block pairStep) .ne) (.loop (.block pairStep) .ne)
      (VG.Taint.hintOf taint (τr [.esp, .ebp, .edi]) (Code.erase (.loop (.block pairStep) .ne)))
      (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have positive := v.minWidth
  have maxWidth := v.maxWidth
  have fit := v.arrayFit (j := 5) (by decide)
  unfold Geometry.words at fit
  have loop := seg (X := Scanning g p) (Y := fun a => VG.Proof.RsaKeyGen.X86.Sieve.StackContext (p - 20#32) a)
    [.esp, .ebp, .edi]
    (fun r => if r = .esp then p - 20#32 else if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 5)
      else BitVec.ofNat 32 g.w) (fun a A => by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact A.stack.sp
      · exact ptr_value A.ebp
      · change a.gpr .edi = BitVec.ofNat 32 g.w
        apply BitVec.eq_of_toNat_eq
        rw [A.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) loopRaw
    (fun a A => WP.mono (scanLoop_ok A.ws (by omega) (by omega) A.ebp A.count) fun _ ⟨_, _, K⟩ =>
      A.stack.keep K (by decide))
  have restoreRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (VG.Impl.Mont.X86.at_ .esp 0))])
      (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have restore := seg (X := fun a => VG.Proof.RsaKeyGen.X86.Sieve.StackContext (p - 20#32) a)
    (Y := fun _ => True) [.esp] (fun _ => p - 20#32) (fun a A r mem => by
      obtain rfl := List.mem_singleton.mp mem
      exact A.sp) restoreRaw (fun a A => wp_movS (A.read 0 (by decide)) fun _ _ _ => WP.block_nil trivial)
  exact (RelCT.seq setup (RelCT.seq loop restore)).mono
    (fun a b ⟨s₁, s₂, ⟨S₁, S₂⟩, e₁, e₂⟩ => ⟨⟨s₁, S₁, e₁⟩, ⟨s₂, S₂, e₂⟩⟩) (fun _ _ _ => trivial)

/-- Before a pass: its top word zero and a mask in `ecx`. -/
def Halving (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ w32 s.mem g.W (g.array 27 + 4 * g.words) = 0 ∧ ∃ choice, s.gpr .ecx = cmask choice

/-- After a pass: `ebp` past array 27. -/
def Halved (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ w32 s.mem g.W (g.array 27 + 4 * g.words) = 0 ∧
    PtrAt s g.W .ebp (g.array 27 + 4 * g.words)

/-- The stack pointer and the workspace pointer, the same in every run. -/
def baseRegs (g : Geometry) (p : BitVec 32) (extra : Reg → BitVec 32) : Reg → BitVec 32
  | .esp => p
  | .edi => BitVec.ofNat 32 g.W.toNat
  | r => extra r

theorem base_vals {g : Geometry} {c capacity : Nat} {p : BitVec 32} {s : State} (S : Ready g c capacity p s)
    (extra : Reg → BitVec 32) : ∀ r ∈ [Reg.esp, .edi], s.gpr r = baseRegs g p extra r := by
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.caller.sp
  · exact edi_value S.context

theorem markerBlock_keep {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Prepared g capacity p s) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.LowBit.code ++ VG.Impl.RsaKeyGen.X86.Exponent.saveMarker)) s
      (Prepared g capacity p) := by
  obtain ⟨c, S⟩ := S
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.LowBit.code_ok s) fun a ⟨_, Ma, Ka⟩ => ?_)
  have Ksa : Keeps VG.Proof.RsaKeyGen.X86.Exponent.clob s a := Ka.mono (by decide)
  have head := v.headerFit
  refine WP.mono (VG.Proof.RsaKeyGen.X86.Header.storePair_ok (S.scratch.of_keeps Ksa (by decide)) (offset := 136)
    (by omega)) fun t ⟨_, Ot, Kt⟩ => ?_
  have O : Outside g.W 136 8 s.mem t.mem := by rw [← Ma]; exact Ot
  exact ⟨c, VG.Proof.RsaKeyGen.X86.Exponent.ready_keep v S (outs_prepared O ⟨(136, 8), by
    unfold VG.Proof.RsaKeyGen.X86.Exponent.preparedRanges VG.Proof.RsaKeyGen.X86.Exponent.ranges
    exact List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩) (Ksa.trans (Kt.mono (by decide)))⟩

theorem marker_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) marker
      (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) := by
  unfold marker
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (VG.Impl.RsaKeyGen.X86.LowBit.code ++ VG.Impl.RsaKeyGen.X86.Exponent.saveMarker)) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  exact RelCT.seq (scan_trace v) (seg [.esp, .edi] (baseRegs g p fun _ => 0) (fun _ ⟨_, S⟩ => base_vals S _) raw
    fun _ S => markerBlock_keep v S)

theorem copyTops_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) copyTops
      (fun s t => Halving g capacity p s ∧ Halving g capacity p t) := by
  have topsRaw : RelCT isa (VG.X86.Taint.Agree (roundTaint copyRegisters))
      (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.at_ .ebx 0) .eax, .store (VG.Impl.Mont.X86.at_ .ebp 0) .eax,
        .mov .ecx (.imm (BitVec.allOnes 32))]) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (roundTaint copyRegisters)) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  refine withRuns (R := fun _ _ => True) ?_ fun s ⟨c, S⟩ => WP.mono (copyTops_ok v S)
    fun t ⟨T, _, top, mask, _, _, _⟩ => ⟨c, T, top, true, mask⟩
  unfold copyTops
  exact RelCT.seq ((copy_trace v _ 0 (by decide) (by decide)).mono (fun _ _ ⟨S, T⟩ => prepared_pair S T)
    (fun _ _ H => H)) topsRaw

theorem half_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Halving g capacity p s ∧ Halving g capacity p t) half
      (fun s t => Halved g capacity p s ∧ Halved g capacity p t) := by
  have loopRaw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.esi, .ebp, .edi])) (.loop (.block halfStep) .ne)
      (fun _ _ => True) :=
    (erased_relCT (.loop (.block halfStep) .ne) (.loop (.block halfStep) .ne)
      (VG.Taint.hintOf taint (roundTaint [.esi, .ebp, .edi]) (Code.erase (.loop (.block halfStep) .ne)))
      (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (roundTaint [.esi, .ebp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  refine withRuns (R := fun _ _ => True) ?_ fun s ⟨c, S, top, choice, mask⟩ =>
    WP.mono (halfStage_ok v S top mask) fun t ⟨T, _, topT, _, P, _, _⟩ => ⟨c, T, topT, P⟩
  unfold half
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    ((pointer_pair_relCT v .ebp 27 (by decide) (by decide) [.edi] (by decide)).mono
      (fun _ _ ⟨⟨c₁, S, _⟩, ⟨c₂, T, _⟩⟩ => prepared_pair ⟨c₁, S⟩ ⟨c₂, T⟩) (fun _ _ H => H))
    (words_pair_relCT v [.ebp, .edi] (by decide)))) ?_
  exact loopRaw.mono (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem halfIf_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (j : Nat) :
    RelCT isa (fun s t => Halved g capacity p s ∧ Halved g capacity p t) (halfIf j)
      (fun s t => Halved g capacity p s ∧ Halved g capacity p t) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (VG.Impl.RsaKeyGen.X86.SigMask.code VG.Impl.RsaKeyGen.X86.Exponent.markerOffset j))
      (fun _ _ => True) :=
    (erased_relCT (.block (VG.Impl.RsaKeyGen.X86.SigMask.code VG.Impl.RsaKeyGen.X86.Exponent.markerOffset j))
      (.block (VG.Impl.RsaKeyGen.X86.SigMask.code 136 1)) (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have head := v.headerFit
  have sig := seg (X := Halved g capacity p) (Y := Halving g capacity p) [.esp, .edi] (baseRegs g p fun _ => 0)
    (fun _ ⟨_, S, _⟩ => base_vals S _) raw fun s ⟨c, S, top, _⟩ => by
      refine WP.mono (VG.Proof.RsaKeyGen.X86.SigMask.code_ok S.scratch
        (by unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega)) fun t ⟨mask, M, K⟩ => ?_
      have outs : Outs g.W (VG.Proof.RsaKeyGen.X86.Exponent.preparedRanges g) s.mem t.mem := by
        rw [M]; exact Outs.refl _ _ _
      exact ⟨c, VG.Proof.RsaKeyGen.X86.Exponent.ready_keep v S outs (K.mono (by decide)), by rw [M]; exact top, _, mask⟩
  unfold halfIf
  exact RelCT.seq sig (half_trace v)

theorem finish_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Halved g capacity p s ∧ Halved g capacity p t) (.block finish) (fun _ _ => True) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebp])) (.block finish) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebp])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  refine (seg (X := Halved g capacity p) (Y := fun _ => True) [.esp, .edi, .ebp]
    (baseRegs g p fun _ => BitVec.ofNat 32 (g.W.toNat + (g.array 27 + 4 * g.words))) (fun s ⟨_, S, _, P⟩ => ?_) raw
    fun s ⟨_, S, _, P⟩ => WP.mono (finish_ok v S.scratch P) fun _ _ => trivial).mono (fun _ _ H => H) fun _ _ _ => trivial
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact S.caller.sp
  · exact edi_value S.context
  · exact ptr_value P

/-- Miller–Rabin's exponent at the run-time width leaks no more than the
prepared header. -/
theorem code_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) code (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (marker_trace v) (RelCT.seq (copyTops_trace v) (RelCT.seq (half_trace v)
    (RelCT.seq (halfIf_trace v 1) (RelCT.seq (halfIf_trace v 2) (RelCT.seq (halfIf_trace v 3) (finish_trace v))))))

end VG.Proof.RsaKeyGen.X86.MrExponentRt
