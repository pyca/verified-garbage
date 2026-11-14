module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FrontRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatchTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.LoadTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Close
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Near
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Other
import VerifiedGarbage.Proof.RsaKeyGen.X86.NearFinish
import VerifiedGarbage.Proof.RsaKeyGen.X86.NearValues
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.TimingSeg
import VerifiedGarbage.Proof.RsaKeyGen.X86.OrLoopRt
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Load
import VerifiedGarbage.Proof.RsaKeyGen.X86.SievePattern
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentStageTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Sieve
import VerifiedGarbage.Proof.Framework.X86.SymFrame

/-! ### `RsaKeyGen.X86.FrontRt.CloseTiming`, which only this module used -/

section

/-! # The distance to `p` at the run-time width reads the same addresses in every run -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

theorem Framed.base {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) : Base W L w q s :=
  ⟨F.space, F.stack.sp⟩

/-- The subtraction's loop and `edi` restored, with its pointers and count public. -/
theorem subRest_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .ebx, .edi, .edx]))
    (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))])) (fun _ _ => True) :=
  (erased_relCT (σ := τr [.esp]) (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))]))
    (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))]))
    (VG.Taint.hintOf taint (τr [.esp, .ebp, .ebx, .edi, .edx])
      (Code.erase (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))]))))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem selectRest_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .ebx, .edi]))
    (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))])) (fun _ _ => True) :=
  (erased_relCT (σ := τr [.esp]) (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))]))
    (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))]))
    (VG.Taint.hintOf taint (τr [.esp, .ebp, .ebx, .edi])
      (Code.erase (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))]))))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem orLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .ecx]))
    (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
    (fun _ _ => True) :=
  (erased_relCT (σ := τr [.esp])
    (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
    (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
    (VG.Taint.hintOf taint (τr [.esp, .ebp, .ecx]) (Code.erase
      (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

/-- `[out] := [a] − [b]`, its borrow a mask in `ecx`; `E` holds of `esi` throughout. -/
theorem sub_trace {W : Addr} {L w : Nat} {q : BitVec 32} (E : BitVec 32 → Prop) {out a b : Nat}
    (Io : Arrays out) (Ia : Arrays a) (Ib : Arrays b) (oa : out ≠ a) (ob : out ≠ b)
    (raw : (VG.Taint.check taint (τr [.esp, .edi]) (.block (lenPtr .ebp .edx a ++ lenPtr .ebx .edx b ++
      lenPtr .eax .edx out ++ ([.mov .edx (.mem (sc 4)), .mov .edi (.reg .eax), .mov .ecx (.imm 0)] : List Instr)))
      (.block [])).map
      (taint.le (τr [])) = some true) :
    RelCT isa (fun s t => (Framed W L w q s ∧ E (s.gpr .esi)) ∧ (Framed W L w q t ∧ E (t.gpr .esi))) (sub out a b)
      (fun u z => (Framed W L w q u ∧ E (u.gpr .esi) ∧ ∃ c : Bool, u.gpr .ecx = cmask c) ∧
        (Framed W L w q z ∧ E (z.gpr .esi) ∧ ∃ c : Bool, z.gpr .ecx = cmask c)) := by
  unfold sub
  have setup := seg (X := fun s => Framed W L w q s ∧ E (s.gpr .esi))
    (Y := fun u => (∃ s₀, SubSet W L w q out a b s₀ u) ∧ E (u.gpr .esi))
    (c := .block (lenPtr .ebp .edx a ++ lenPtr .ebx .edx b ++ lenPtr .eax .edx out ++
      [.mov .edx (.mem (sc 4)), .mov .edi (.reg .eax), .mov .ecx (.imm 0)]))
    [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.1.base.vals _) (rawBlock raw) fun s S =>
      WP.mono (subSetup_ok S.1 Io Ia Ib) fun u ⟨Pa, Pb, Po, cnt, ecx0, Mu, Ku⟩ =>
        ⟨⟨s, S.1, Pa, Pb, Po, cnt, ecx0, Mu, Ku⟩, by rw [Ku.1 .esi (by decide)]; exact S.2⟩
  have rest := seg (X := fun u => (∃ s₀, SubSet W L w q out a b s₀ u) ∧ E (u.gpr .esi))
    (Y := fun u => Framed W L w q u ∧ E (u.gpr .esi) ∧ ∃ c : Bool, u.gpr .ecx = cmask c)
    (c := .seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))])) [.esp, .ebp, .ebx, .edi, .edx]
    (fun r => if r = .esp then q else if r = .ebp then BitVec.ofNat 32 (W.toNat + slot w a)
      else if r = .ebx then BitVec.ofNat 32 (W.toNat + slot w b)
      else if r = .edi then BitVec.ofNat 32 (W.toNat + slot w out) else BitVec.ofNat 32 (4 * (2 * w)))
    (fun u ⟨⟨s₀, H⟩, _⟩ => by
      have bound := H.framed.space.widthBound
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl
      · exact (H.keeps.1 .esp (by decide)).trans H.framed.stack.sp
      · exact ptr_value H.aPtr
      · exact ptr_value H.bPtr
      · exact ptr_value H.outPtr
      · change u.gpr .edx = BitVec.ofNat 32 (4 * (2 * w))
        apply BitVec.eq_of_toNat_eq
        rw [H.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]) subRest_raw fun u ⟨⟨s₀, H⟩, e⟩ =>
      WP.mono (subRest_ok H Io Ia Ib oa ob) fun t ⟨⟨c, mask, _⟩, _, Kt, Ft⟩ =>
        ⟨Ft, by rw [Kt.1 .esi (by decide), ← H.keeps.1 .esi (by decide)]; exact e, c, mask⟩
  exact RelCT.seq setup rest

/-- A mask: all ones or zero. -/
def IsMask (x : BitVec 32) : Prop := ∃ k : Bool, x = cmask k

theorem difference_trace {W : Addr} {L w : Nat} {q : BitVec 32} :
    RelCT isa (fun s t => Framed W L w q s ∧ Framed W L w q t) difference
      (fun u z => Framed W L w q u ∧ Framed W L w q z) := by
  unfold difference
  have first := sub_trace (W := W) (L := L) (w := w) (q := q) (fun _ => True) arrays2 arrays0 arrays4 (by decide)
    (by decide) (by decide +kernel)
  have save := seg (X := fun s => Framed W L w q s ∧ True ∧ ∃ c : Bool, s.gpr .ecx = cmask c)
    (Y := fun u => Framed W L w q u ∧ IsMask (u.gpr .esi)) (c := .block [.mov .esi (.reg .ecx)]) []
    (fun _ => 0) (fun _ _ _ mem => nomatch mem) (rawBlock (by decide +kernel)) fun s S =>
      wp_movS rfl fun u U _ => WP.block_nil ⟨S.1.keepMem U.keeps (by decide) (by decide) U.mem,
        by obtain ⟨c, mask⟩ := S.2.2; exact ⟨c, by rw [U.gpr, mask]⟩⟩
  have second := sub_trace (W := W) (L := L) (w := w) (q := q) IsMask arrays3 arrays4 arrays0 (by decide)
    (by decide) (by decide +kernel)
  have selectSetup := seg (X := fun s => Framed W L w q s ∧ IsMask (s.gpr .esi) ∧ ∃ c : Bool, s.gpr .ecx = cmask c)
    (Y := fun u => ∃ s₀ k, SelectSet W L w q k s₀ u)
    (c := .block (lenPtr .ebp .edx 3 ++ lenPtr .ebx .edx 2 ++ [.mov .edi (.mem (sc 4)), .mov .ecx (.reg .esi)]))
    [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.1.base.vals _) (rawBlock (by decide +kernel)) fun s S => by
      obtain ⟨k, mask⟩ := S.2.1
      exact WP.mono (selectSetup_ok S.1 mask) fun u H => ⟨s, k, H⟩
  have selectRest := seg (X := fun u => ∃ s₀ k, SelectSet W L w q k s₀ u) (Y := Framed W L w q)
    (c := .seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))])) [.esp, .ebp, .ebx, .edi]
    (fun r => if r = .esp then q else if r = .ebp then BitVec.ofNat 32 (W.toNat + slot w 3)
      else if r = .ebx then BitVec.ofNat 32 (W.toNat + slot w 2) else BitVec.ofNat 32 (4 * (2 * w)))
    (fun u ⟨s₀, k, H⟩ => by
      have bound := H.framed.space.widthBound
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl
      · exact (H.keeps.1 .esp (by decide)).trans H.framed.stack.sp
      · exact ptr_value H.fromPtr
      · exact ptr_value H.toPtr
      · change u.gpr .edi = BitVec.ofNat 32 (4 * (2 * w))
        apply BitVec.eq_of_toNat_eq
        rw [H.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]) selectRest_raw fun u ⟨s₀, k, H⟩ =>
      WP.mono (selectRest_ok H) fun _ H' => H'.2.2.2
  exact (RelCT.seq (first.mono (fun _ _ ⟨S, T⟩ => ⟨⟨S, trivial⟩, ⟨T, trivial⟩⟩) (fun _ _ h => h))
    (RelCT.seq save (RelCT.seq second (RelCT.seq selectSetup selectRest))))

/-- Scanning array 2's low words: `ebp` at them and their count in `ecx`. -/
structure Scanning (W : Addr) (L w : Nat) (q : BitVec 32) (u : State) : Prop where
  ws : Ws u W L
  sp : u.gpr .esp = q
  ptr : PtrAt u W .ebp (slot w 2)
  count : (u.gpr .ecx).toNat = 2 * w - 4
  zero : u.gpr .ebx = 0#32

/-- At array 2's top four words. -/
structure Scanned (W : Addr) (L w : Nat) (q : BitVec 32) (u : State) : Prop where
  ws : Ws u W L
  sp : u.gpr .esp = q
  ptr : PtrAt u W .ebp (slot w 2 + 4 * (2 * w - 4))

theorem near_trace {W : Addr} {L w : Nat} {q : BitVec 32} (width : 4 ≤ w) (bound : w ≤ 64)
    (space : slot w 5 ≤ L) :
    RelCT isa (fun s t => Base W L w q s ∧ Base W L w q t) near (fun _ _ => True) := by
  have fit : slot w 2 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega_using [space]
  unfold near orScan
  have setup := seg (X := Base W L w q) (Y := Scanning W L w q)
    (c := .block ([.mov .ebx (.imm 0)] ++ lenPtr .ebp .edx 2 ++
      [.mov .ecx (.mem (sc 4)), .shift .shr .ecx 2, .alu .sub .ecx (.imm 4)]))
    [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.vals _) (rawBlock (by decide +kernel)) fun s S =>
      WP.mono (orScanSetup_ok S.1) fun u ⟨P, cnt, zero, _, K⟩ =>
        ⟨S.1.ws.of_keeps K, (K.1 .esp (by decide)).trans S.2, P, cnt, zero⟩
  have loop := seg (X := Scanning W L w q) (Y := Scanned W L w q)
    (c := .loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
    [.esp, .ebp, .ecx]
    (fun r => if r = .esp then q else if r = .ebp then BitVec.ofNat 32 (W.toNat + slot w 2)
      else BitVec.ofNat 32 (2 * w - 4)) (fun u U => by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact U.sp
      · exact ptr_value U.ptr
      · change u.gpr .ecx = BitVec.ofNat 32 (2 * w - 4)
        apply BitVec.eq_of_toNat_eq
        rw [U.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]) orLoop_raw fun u U =>
      WP.mono (orLoop_ok U.ws (by omega_using [width]) (by omega_using [fit]) U.ptr U.count U.zero) fun t ⟨_, _, P, K⟩ =>
        ⟨U.ws.of_keeps K, (K.1 .esp (by decide)).trans U.sp, P⟩
  have last := seg (X := Scanned W L w q) (Y := fun _ => True) (c := .block (top ++ VG.Impl.RsaKeyGen.X86.Near.finish))
    [.esp, .ebp] (fun r => if r = .esp then q else BitVec.ofNat 32 (W.toNat + (slot w 2 + 4 * (2 * w - 4))))
    (fun u U => by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact U.sp
      · exact ptr_value U.ptr) (rawBlock (by decide +kernel)) fun u U =>
      WP.block_append (WP.mono (topAt_ok U.ws U.ptr (by omega_using [width, fit])) fun b ⟨C, _⟩ =>
        WP.mono (VG.Proof.RsaKeyGen.X86.Near.finish_ok b (by rw [C]; exact VG.Proof.RsaKeyGen.X86.Near.nibble_bound _))
          fun _ _ => trivial)
  exact (RelCT.seq (RelCT.seq setup loop) last).mono (fun _ _ h => h) (fun _ _ _ => trivial)

/-- The workspace pointer saved at the bottom of the distance check's frame. -/
theorem frameStore_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (B : Base W L w q s)
    (fit : 40 ≤ q.toNat) (separateStack : q.toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ q.toNat) :
    WP isa (.block [.store (at_ .esp 0) .edi]) (allocFrame 20 s) (Framed W L w (q - 20#32)) := by
  have Sb := B.1
  have spB := B.2
  have nowrap := Sb.scratch.nowrap
  have head := Sb.header
  have St := FilterStack.allocated_context (s := s) (by rw [spB]; omega_using [fit])
  rw [spB] at St
  have apartQ : (⟨W, L⟩ : Region).Disjoint ⟨(q - 20#32).setWidth 64, 20⟩ := by
    have H := FilterStack.allocated_apart (s := s) (bytes := 20) (by rw [spB]; omega_using [fit]) nowrap
      (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))
    rw [spB] at H
    exact H
  have Sc : Space W L w (allocFrame 20 s) :=
    ⟨FilterStack.allocated_scratch Sb.scratch (by rw [spB]; omega_using [fit])
      (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega_using [h])),
      Sb.width, Sb.widthBound, Sb.space, Sb.len⟩
  refine WP.mono (St.store 0 (by decide) .edi) fun c ⟨Mc, Oc, Kc, Stc⟩ => ?_
  have Fc := VG.Proof.Bignum.outside_frame Oc (by decide)
  have Wc : VG.Proof.MillerRabin.X86.WorkspaceFrame ⟨W, L, w⟩ [] (allocFrame 20 s).mem c.mem :=
    VG.Proof.RsaKeyGen.X86.workspace_of_frame (g := ⟨W, L, w⟩) Fc nowrap (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact apartQ.sub_right (Offset.sub_base _ (by decide)))
  refine ⟨Sc.keep Kc (by decide) (by decide) (Wc.read32 (d := 4) (by change 4 + 4 ≤ L; omega_using [head]) (fun _ mem => nomatch mem)),
    Stc, apartQ, ?_⟩
  rw [Mc, Mem.readW_writeW_self32, allocFrame_gpr _ _ (by decide), Sb.edi_value]

theorem other_trace {W : Addr} {L w : Nat} {q p : BitVec 32} (width : 4 ≤ w) (bound : w ≤ 64)
    (space : slot w 5 ≤ L) (fit : 40 ≤ q.toNat)
    (separateStack : q.toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ q.toNat) :
    RelCT isa (fun s t => OtherIn W L w q p s ∧ OtherIn W L w q p t) other (fun _ _ => True) := by
  unfold other
  have source := seg (X := OtherIn W L w q p) (Y := SourceIn W L w q p) (c := .block [.mov .esi (.mem (sc 20))])
    [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.base.vals _) (rawBlock (by decide +kernel)) fun s S => by
      have head := S.base.1.header
      refine wp_movS (readSrc_sc S.base.1.scratch (d := 20) (by omega_using [head])) fun t T _ => WP.block_nil ?_
      refine ⟨⟨S.base.1.keepMem T.keeps (by decide) (by decide) T.mem, (T.other .esp (by decide)).trans S.base.2⟩,
        T.gpr.trans S.pointer, S.sourceFit, by rw [T.keeps.2.1, T.keeps.2.2]; exact S.readable, S.separate⟩
  have f4 : slot w 4 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega_using [space]
  have store := seg (X := fun a => ∃ s, Base W L w q s ∧ a = allocFrame 20 s) (Y := Framed W L w (q - 20#32))
    (c := .block [.store (at_ .esp 0) .edi]) [.esp, .edi] (regs W (q - 20#32) fun _ => 0) (fun a ⟨s, S, e⟩ => by
      subst e
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [allocFrame_esp, S.2]; rfl
      · rw [allocFrame_gpr _ _ (by decide)]; exact S.1.edi_value) (rawBlock (by decide +kernel))
    fun a ⟨s, S, e⟩ => by subst e; exact frameStore_ok S fit separateStack
  refine RelCT.seq source (RelCT.seq (importAt_trace 4 (by decide) f4
    (by unfold slot stride VG.Impl.Bignum.hdrBytes; omega_using []) (by decide +kernel)) ?_)
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  refine (RelCT.seq store (RelCT.seq difference_trace ((near_trace width bound space).mono
    (fun _ _ ⟨U, Z⟩ => ⟨U.base, Z.base⟩) (fun _ _ h => h)))).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s₁, s₂, ⟨S₁, S₂⟩, e₁, e₂⟩
  exact ⟨⟨s₁, S₁, e₁⟩, ⟨s₂, S₂, e₂⟩⟩

theorem close_trace {W : Addr} {L w : Nat} {q p plen : BitVec 32} (width : 4 ≤ w) (bound : w ≤ 64)
    (space : slot w 5 ≤ L) (fit : 40 ≤ q.toNat)
    (separateStack : q.toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ q.toNat) :
    RelCT isa (fun s t => CloseIn W L w q p plen s ∧ CloseIn W L w q p plen t) close (fun _ _ => True) := by
  unfold close
  have check := seg (X := CloseIn W L w q p plen)
    (Y := fun u => CloseIn W L w q p plen u ∧ isa.eval .e u = some (decide (plen = 0#32)))
    (c := .block [.mov .eax (.mem (sc 24)), .alu .cmp .eax (.imm 0)]) [.esp, .edi] (regs W q fun _ => 0)
    (fun s S => S.base.vals _) (rawBlock (by decide +kernel)) fun s S => by
      have head := S.base.1.header
      refine wp_movS (readSrc_sc S.base.1.scratch (d := 24) (by omega_using [head])) fun a A _ =>
        wp_cmpS rfl fun b B Z => WP.block_nil ?_
      have K : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
      have M : b.mem = s.mem := B.mem.trans A.mem
      refine ⟨⟨⟨S.base.1.keepMem K (by decide) (by decide) M, (K.1 .esp (by decide)).trans S.base.2⟩,
        by rw [M]; exact S.pointer, by rw [M]; exact S.length,
        fun h => by rw [K.2.1, K.2.2]; exact S.source h⟩, ?_⟩
      change b.zf = _
      rw [Z, A.gpr, S.length]
      change some (plen - 0#32 == 0#32) = _
      rw [BitVec.sub_zero]
      rfl
  refine RelCT.seq check (VG.RelCT.ite (fun _ _ ⟨U, Z⟩ => U.2.trans Z.2.symm) ?_ ?_)
  · exact (rawBlock (rs := []) (by decide +kernel)).mono (fun _ _ _ => agree_regs (by intro r mem; cases mem))
      (fun _ _ h => h)
  · refine (other_trace (p := p) width bound space fit separateStack).mono ?_ (fun _ _ h => h)
    rintro u z ⟨⟨⟨U, cu⟩, ⟨Z, _⟩⟩, no⟩
    rw [cu] at no
    have nonzero : plen ≠ 0#32 := fun h => by simp [h] at no
    obtain ⟨fu, ru, su⟩ := U.source nonzero
    obtain ⟨fz, rz, sz⟩ := Z.source nonzero
    exact ⟨⟨U.base, U.pointer, fu, ru, su⟩, ⟨Z.base, Z.pointer, fz, rz, sz⟩⟩

end VG.Proof.RsaKeyGen.X86.FrontRt

end

end

/-! ### `RsaKeyGen.X86.CandidateSieveLeak`, which only this module used -/

section

/-! # Rejected-candidate leakage permits the sieve pattern and passing candidates hide their values -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.Proof.RsaKeyGen

theorem candidate_op_composite {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte}
    (enough : E.length ≤ entropy.length)
    (close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) = false)
    (composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) = true) :
    Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy = some (.rejected, entropy.drop E.length) := by
  unfold Spec.RsaKeyGen.candidateOp
  rw [candidateStep_eq E.length _ _ _ (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega_using [this]), ite_t enough]
  change afterDraw (8 * E.length) (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes)
    (candidateValue E entropy) (entropy.drop E.length) = _
  simp only [afterDraw, close, composite, Bool.false_eq_true, Bool.not_true, Bool.false_and, ↓reduceIte]

theorem composite_candidates_eq {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (rEnough : E.length ≤ rBytes.length) (sEnough : E.length ≤ sBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (rComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = true)
    (sComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = true) :
    candidateValue E rBytes = candidateValue E sBytes := by
  unfold SameLeak at leak
  rw [candidateLeak_eq, candidateLeak_eq, candidate_op_composite v rEnough rClose rComposite,
    candidate_op_composite v sEnough sClose sComposite] at leak
  have rCount : rBytes.length - (rBytes.drop E.length).length = E.length := by rw [List.length_drop]; omega_using [rEnough]
  have sCount : sBytes.length - (sBytes.drop E.length).length = E.length := by rw [List.length_drop]; omega_using [sEnough]
  change 3 :: (rBytes.take (rBytes.length - (rBytes.drop E.length).length)).map (·.toNat) =
    3 :: (sBytes.take (sBytes.length - (sBytes.drop E.length).length)).map (·.toNat) at leak
  rw [rCount, sCount] at leak
  have bytes := map_toNat_inj (List.cons.inj leak).2
  unfold candidateValue
  rw [bytes]

theorem sieve_pattern {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (rEnough : E.length ≤ rBytes.length) (sEnough : E.length ≤ sBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes)) :
    Sieve.SamePattern E.sieveGeometry (candidateValue E rBytes) (candidateValue E sBytes) := by
  cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes)
  · have right := same.symm.trans composite
    have left := composite
    have bits : 64 * E.sieveGeometry.w = 8 * E.length := by change 64 * E.width = _; have := v.length_eq; omega_using [this]
    apply Sieve.samePattern_passing rfl (candidate_large v rBytes) (candidate_large v sBytes)
    · rw [bits]; exact left
    · rw [bits]; exact right
  · rw [composite_candidates_eq v rEnough sEnough leak rClose sClose composite (same.symm.trans composite)]
    exact Sieve.samePattern_refl _ _

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # The candidate drawn and filtered at its run-time width hides the filtered values -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateSieveStageTiming.lean`, which only this module imported.
section

/-! # The shared leak controls sieve rejection and the complete remaining candidate path -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

/-- After the code for the width: both runs wrote the same status, or both go
on with `eax = 4`, the drawn candidates neither too close nor divisible. -/
def FrontPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop :=
  (s.gpr .eax = t.gpr .eax ∧ s.gpr .eax ≠ 4) ∨
  (s.gpr .eax = 4 ∧ t.gpr .eax = 4 ∧ DrawnPair E eBytes pBytes qBytes rBytes sBytes s t ∧
    Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false ∧
    Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false ∧
    Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = false ∧
    Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = false)

/-- A status written by both runs. -/
theorem drawn_done_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (status : Nat) (small : status < 4) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFinish.used status) (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  refine ((drawn_used_trace v status).wp (F₁ := fun (u : State) => u.gpr .eax = BitVec.ofNat 32 status)
    (F₂ := fun (u : State) => u.gpr .eax = BitVec.ofNat 32 status) fun s t P =>
    ⟨WP.mono (finish_used_ok (status := status) v (P.left.finishReady v)) fun _ H => H.1.1,
      WP.mono (finish_used_ok (status := status) v (P.right.finishReady v)) fun _ H => H.1.1⟩).mono
    (fun _ _ P => P) ?_
  rintro u z ⟨_, U, Z⟩
  refine Or.inl ⟨U.trans Z.symm, ?_⟩
  rw [U]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega_using [small])] at this
  change status = 4 at this
  omega_using [small, this]

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FrontRt/SieveTiming.lean`, which only this module imported.
section

/-! # Trial division at the run-time width releases only the trial divisors' pattern -/

section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen.X86.Sieve
open VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.RsaKeyGen.X86.Sieve (tableCount tableAddress stackSlots)

theorem enter_ok {g : Geometry} {c : Nat} {s : State} (S : SieveIn g c s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Mont.X86.sc 4)), .alu .add .edi (.imm 256)]) s (BodyIn g c) := by
  obtain ⟨C, pointer, symbol, lenRead⟩ := S
  refine wp_movS lenRead fun a A _ => wp_addS rfl fun b B _ => WP.block_nil ?_
  have Kb : Keeps [.edx, .edi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  refine ⟨⟨C.stack.keep Kb (by decide), ?_, ?_, ?_, ?_⟩, by rw [B.gpr, A.other .edi (by decide)]; exact pointer,
    by rw [B.other .edx (by decide), A.gpr], by rw [B.syms, A.syms]; exact symbol⟩
  · intro i index; rw [Kb.2.1, Kb.2.2]; exact C.candidateRead i index
  · intro i index d mem; rw [Kb.2.1, Kb.2.2]; exact C.tableRead i index d mem
  · intro i index; rw [Mb]; exact C.tableWords i index
  · rw [Mb]; exact C.candidateValue

theorem enter_trace {g : Geometry} {c d : Nat} :
    RelCT isa (fun s t => SieveIn g c s ∧ SieveIn g d t)
      (.block [.mov .edx (.mem (VG.Impl.Mont.X86.sc 4)), .alu .add .edi (.imm 256)])
      (fun u z => BodyIn g c u ∧ BodyIn g d z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have A : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact S.1.stack.sp.trans T.1.stack.sp.symm
    · have H := congrArg (fun x : BitVec 32 => x - 256#32) (S.2.1.trans T.2.1.symm)
      simpa only [BitVec.add_sub_cancel] using H
  exact ⟨((rawBlock (rs := [.esp, .edi]) (by decide +kernel)) _ _ _ _ _ _ A E G).1,
    wp_result (enter_ok S) E, wp_result (enter_ok T) G⟩

theorem setup_trace {g : Geometry} (v : g.Valid) {c d : Nat} (low : 4 ≤ g.sp.toNat)
    (length : g.limit = tableCount g.w) (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t)
      (.seq (.block candidateSlots) (.seq tableAddress (.block tableSlots)))
      (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t) := by
  have first : RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t) (.block candidateSlots)
      (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have A : VG.X86.Taint.Agree (τr [.esp]) s t :=
      agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.1.stack.sp.trans T.1.stack.sp.symm)
    have trace := ((rawBlock (rs := [.esp]) (code := candidateSlots) (by decide +kernel)) _ _ _ _ _ _ A E G).1
    have U := wp_result (candidateSlots_ok v S.1 S.2.1 S.2.2.1) E
    have Z := wp_result (candidateSlots_ok v T.1 T.2.1 T.2.2.1) G
    exact ⟨trace, U.1.context.stack.sp, Z.1.context.stack.sp⟩
  have middle : RelCT isa (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp)
      tableAddress (VG.X86.Taint.Agree (τr [.esp])) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have Ls : 4 ≤ (s.gpr .esp).toNat := by rw [S]; exact low
    have Lt : 4 ≤ (t.gpr .esp).toNat := by rw [T]; exact low
    have U := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol s Ls) E
    have Z := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol t Lt) G
    refine ⟨?_, agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact
      (U.gpr .esp (by decide)).trans (S.trans (T.symm.trans (Z.gpr .esp (by decide)).symm)))⟩
    rw [symFrame_trace Ls E, symFrame_trace Lt G, S, T]
  have raw : RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t)
      (.seq (.block candidateSlots) (.seq tableAddress (.block tableSlots))) (fun _ _ => True) :=
    RelCT.seq first (RelCT.seq middle (rawBlock (by decide +kernel)))
  intro s t tr ur u z ⟨S, T⟩ E G
  exact ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1,
    (wp_result (setup_ok v S.1 S.2.1 S.2.2.1 length S.2.2.2 low candidateFar tableFar) E).1,
    (wp_result (setup_ok v T.1 T.2.1 T.2.2.1 length T.2.2.2 low candidateFar tableFar) G).1⟩

theorem body_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t) sieveBody (VG.X86.Taint.Agree (τr [.esp])) := by
  have setup := setup_trace (c := c) (d := d) v low length candidateFar tableFar
  intro s t tr ur u z H E G
  cases E with
  | seq A E =>
    cases E with
    | seq B E =>
      cases E with
      | seq C L =>
        cases G with
        | seq D G =>
          cases G with
          | seq F G =>
            cases G with
            | seq K N =>
              have R := RelCT.seq setup (loop_trace v pattern) _ _ _ _ _ _ H
                (.seq (.seq A (.seq B C)) L) (.seq (.seq D (.seq F K)) N)
              simpa only [List.append_assoc] using R

theorem sieve_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => SieveIn g c (allocFrame 20 s) ∧ SieveIn g d (allocFrame 20 t)) sieve (fun _ _ => True) := by
  unfold sieve
  apply RelCT.frameAlloc
  refine (RelCT.seq enter_trace (RelCT.seq (body_trace v pattern length low candidateFar tableFar)
    (rawBlock (by decide +kernel)))).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, H, rfl, rfl⟩
  exact H

end VG.Proof.RsaKeyGen.X86.FrontRt
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

structure ClearedPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop
    extends InputPair E eBytes pBytes qBytes rBytes sBytes s t where
  zerosLeft : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0
  zerosRight : Spec.Rsa.bytesAt t.mem (E.out.setWidth 64) E.length = List.replicate E.length 0

theorem load_rt_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (enough : E.length ≤ E.randLength) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.FrontRt.load
      (DrawnPair E eBytes pBytes qBytes rBytes sBytes) := by
  intro s t tr ur u z P A B
  have five := v.slotFit (j := 5) (by decide)
  have trace := (FrontRt.load_trace v.width_bounds.1 (by omega_using [five]) _ _ _ _ _ _
    ⟨P.left.loadIn v enough, P.right.loadIn v enough⟩ A B).1
  obtain ⟨DU, _, _⟩ := wp_result (load_rt_ok v P.left P.zerosLeft enough) A
  obtain ⟨DZ, _, _⟩ := wp_result (load_rt_ok v P.right P.zerosRight enough) B
  exact ⟨trace, DU, DZ⟩

theorem close_rt_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) =
      Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.FrontRt.close
      (WithFlag (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
        (Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes))) := by
  intro s t tr ur u z P A B
  have five := v.slotFit (j := 5) (by decide)
  have trace := (FrontRt.close_trace v.width_bounds.1 v.width_bounds.2 (by omega_using [five]) (by have := v.low; omega_using [this])
    v.stackApart _ _ _ _ _ _ ⟨P.left.closeIn v, P.right.closeIn v⟩ A B).1
  obtain ⟨DU, flagU, _, _⟩ := wp_result (close_rt_ok v P.left) A
  obtain ⟨DZ, flagZ, _, _⟩ := wp_result (close_rt_ok v P.right) B
  exact ⟨trace, ⟨DU, DZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem sieve_rt_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (pattern : Sieve.SamePattern E.sieveGeometry (candidateValue E rBytes) (candidateValue E sBytes))
    (same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.FrontRt.sieve
      (WithFlag (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
        (Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes))) := by
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) := v.stackFar E.workspaceRegion
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tableFar : E.tableRegion.Disjoint (below E.p 136) := v.stackFar E.tableRegion
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  intro s t tr ur u z P A B
  have trace := (FrontRt.sieve_trace v.sieve_valid pattern rfl
    (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega_using [this])]; have := v.low; omega_using [this])
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    _ _ _ _ _ _ ⟨P.left.sieveIn v, P.right.sieveIn v⟩ A B).1
  obtain ⟨DU, flagU, _, _⟩ := wp_result (sieve_rt_ok v P.left) A
  obtain ⟨DZ, flagZ, _, _⟩ := wp_result (sieve_rt_ok v P.right) B
  exact ⟨trace, ⟨DU, DZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem sieve_front_rt_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (.seq VG.Impl.RsaKeyGen.X86.FrontRt.sieve (.seq (.block [.alu .cmp .eax (.imm 0)])
        (.ite .ne (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 3) (.block [.mov .eax (.imm 4)]))))
      (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  have schedules := schedule_eq v length rEnough leak
  have same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) := by
    have H := congrArg Sched.comp schedules
    rw [schedule_composite rClose, schedule_composite sClose] at H
    exact H
  have pattern := sieve_pattern v rEnough (by rw [← length]; exact rEnough) leak rClose sClose same
  have initialTrace := sieve_rt_pair_trace (eBytes := eBytes) (pBytes := pBytes) (qBytes := qBytes) v pattern same
  cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes)
  · have right := same.symm.trans composite
    rw [composite] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) (branch_false ?_))
    have raw : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block [.mov .eax (.imm 4)]) (VG.X86.Taint.Agree (τr [])) :=
      checkedBlockInvariant rfl rfl
    have four {e p r : List Byte} {x : State} (D : Drawn E e p r x) :
        WP isa (.block [.mov .eax (.imm 4)]) x fun u => u.gpr .eax = 4 ∧ Drawn E e p r u :=
      wp_movS rfl fun u U _ => WP.block_nil ⟨U.gpr, D.keepMem v U.mem U.keeps (by decide) (by decide) U.syms⟩
    refine ((raw.mono (fun _ _ _ => agree_regs (by intro r mem; cases mem)) (fun _ _ _ => trivial)).wp
      (fun _ _ P => ⟨four P.left, four P.right⟩)).mono (fun _ _ P => P) ?_
    rintro u z ⟨_, ⟨U, DU⟩, ⟨Z, DZ⟩⟩
    exact Or.inr ⟨U, Z, ⟨DU, DZ⟩, rClose, sClose, composite, right⟩
  · rw [composite] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_true (drawn_done_trace v 3 (by decide))

theorem front_rt_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes)
      VG.Impl.RsaKeyGen.X86.FrontRt.code (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  have schedules := schedule_eq v length rEnough leak
  have same : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) =
      Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) := by
    have H := congrArg Sched.close schedules
    rw [schedule_close, schedule_close] at H
    exact H
  have initialTrace := close_rt_pair_trace (eBytes := eBytes) v same
  unfold VG.Impl.RsaKeyGen.X86.FrontRt.code
  refine RelCT.seq (load_rt_pair_trace v enough) ?_
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes)
  · rw [close] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_false (sieve_front_rt_trace v length rEnough leak close (same.symm.trans close))
  · rw [close] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_true (drawn_done_trace v 2 (by decide))

end VG.Proof.RsaKeyGen.X86.Candidate
