module

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
        rw [H.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) subRest_raw fun u ⟨⟨s₀, H⟩, e⟩ =>
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
        rw [H.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) selectRest_raw fun u ⟨s₀, k, H⟩ =>
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
  have fit : slot w 2 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega
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
        rw [U.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) orLoop_raw fun u U =>
      WP.mono (orLoop_ok U.ws (by omega) (by omega) U.ptr U.count U.zero) fun t ⟨_, _, P, K⟩ =>
        ⟨U.ws.of_keeps K, (K.1 .esp (by decide)).trans U.sp, P⟩
  have last := seg (X := Scanned W L w q) (Y := fun _ => True) (c := .block (top ++ VG.Impl.RsaKeyGen.X86.Near.finish))
    [.esp, .ebp] (fun r => if r = .esp then q else BitVec.ofNat 32 (W.toNat + (slot w 2 + 4 * (2 * w - 4))))
    (fun u U => by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact U.sp
      · exact ptr_value U.ptr) (rawBlock (by decide +kernel)) fun u U =>
      WP.block_append (WP.mono (topAt_ok U.ws U.ptr (by omega)) fun b ⟨C, _⟩ =>
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
  have St := FilterStack.allocated_context (s := s) (by rw [spB]; omega)
  rw [spB] at St
  have apartQ : (⟨W, L⟩ : Region).Disjoint ⟨(q - 20#32).setWidth 64, 20⟩ := by
    have H := FilterStack.allocated_apart (s := s) (bytes := 20) (by rw [spB]; omega) nowrap
      (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega))
    rw [spB] at H
    exact H
  have Sc : Space W L w (allocFrame 20 s) :=
    ⟨FilterStack.allocated_scratch Sb.scratch (by rw [spB]; omega)
      (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega)),
      Sb.width, Sb.widthBound, Sb.space, Sb.len⟩
  refine WP.mono (St.store 0 (by decide) .edi) fun c ⟨Mc, Oc, Kc, Stc⟩ => ?_
  have Fc := VG.Proof.Bignum.outside_frame Oc (by decide)
  have Wc : VG.Proof.MillerRabin.X86.WorkspaceFrame ⟨W, L, w⟩ [] (allocFrame 20 s).mem c.mem :=
    VG.Proof.RsaKeyGen.X86.workspace_of_frame (g := ⟨W, L, w⟩) Fc nowrap (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact apartQ.sub_right (Offset.sub_base _ (by decide)))
  refine ⟨Sc.keep Kc (by decide) (by decide) (Wc.read32 (d := 4) (by change 4 + 4 ≤ L; omega) (fun _ mem => nomatch mem)),
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
      refine wp_movS (readSrc_sc S.base.1.scratch (d := 20) (by omega)) fun t T _ => WP.block_nil ?_
      refine ⟨⟨S.base.1.keepMem T.keeps (by decide) (by decide) T.mem, (T.other .esp (by decide)).trans S.base.2⟩,
        T.gpr.trans S.pointer, S.sourceFit, by rw [T.keeps.2.1, T.keeps.2.2]; exact S.readable, S.separate⟩
  have f4 : slot w 4 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega
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
    (by unfold slot stride VG.Impl.Bignum.hdrBytes; omega) (by decide +kernel)) ?_)
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
      refine wp_movS (readSrc_sc S.base.1.scratch (d := 24) (by omega)) fun a A _ =>
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
