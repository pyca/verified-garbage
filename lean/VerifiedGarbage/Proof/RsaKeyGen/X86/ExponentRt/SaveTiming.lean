module

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Copy
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Saving and restoring the candidate at a run-time width have public loop bounds

The pointers and the count of the copies are computed from the length in
the header, which the taint analysis takes for secret: each run computes
them from the same length, so they agree once correctness gives their
values (`publish`), and the loops are then checked with them public.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt

/-- Runs from states agreeing on `rs` leak the same trace (`raw`); by
correctness each run leaves the same values `f r` in the registers `qs`,
which therefore agree afterwards. -/
theorem publish {X Y : State → Prop} {c : Prog isa} {rs : List Reg} (qs : List Reg) (f : Reg → BitVec 32)
    (agree : ∀ s t, X s → X t → VG.X86.Taint.Agree (τr rs) s t)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr rs)) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s (fun u => Y u ∧ ∀ r ∈ qs, u.gpr r = f r)) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => (Y u ∧ Y z) ∧ VG.X86.Taint.Agree (τr qs) u z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  obtain ⟨Yu, Fu⟩ := wp_result (run s S) E
  obtain ⟨Yz, Fz⟩ := wp_result (run t T) G
  exact ⟨(raw _ _ _ _ _ _ (agree s t S T) E G).1, ⟨Yu, Yz⟩, agree_regs fun r mem => (Fu r mem).trans (Fz r mem).symm⟩

/-- Runs leaking the same trace (`raw`) whose final states each satisfy `Y`
by correctness. -/
theorem checked {X Y : State → Prop} {P Q : State → State → Prop} {c : Prog isa}
    (raw : RelCT isa P c Q) (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => (X s ∧ X t) ∧ P s t) c (fun u z => (Y u ∧ Y z) ∧ Q u z) := by
  intro s t tr ur u z ⟨⟨S, T⟩, H⟩ E G
  obtain ⟨trace, post⟩ := raw _ _ _ _ _ _ H E G
  exact ⟨trace, ⟨wp_result (run s S) E, wp_result (run t T) G⟩, post⟩

/-- The working space, the stack and the length `8 w` in the header. -/
structure Space (workspace p : BitVec 32) (size w : Nat) (s : State) : Prop where
  scratch : Scr s (workspace.setWidth 64) size
  stack : s.gpr .esp = p
  width : 4 ≤ w
  widthBound : w ≤ 64
  space : slot w 5 + 8 * w ≤ size
  len : s.mem.readW (off (workspace.setWidth 64) 4) 32 = BitVec.ofNat 32 (8 * w)

theorem Space.workspace {workspace p : BitVec 32} {size w : Nat} {s : State}
    (S : Space workspace p size w s) : s.gpr .edi = workspace := by
  apply BitVec.eq_of_toNat_eq
  rw [S.scratch.edi_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans workspace.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem Space.keep {workspace p : BitVec 32} {size w : Nat} {s t : State} (S : Space workspace p size w s)
    {rs : List Reg} (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs)
    (L : t.mem.readW (off (workspace.setWidth 64) 4) 32 = s.mem.readW (off (workspace.setWidth 64) 4) 32) :
    Space workspace p size w t :=
  ⟨S.scratch.of_keeps K edi esp, (K.1 .esp esp).trans S.stack, S.width, S.widthBound, S.space, L.trans S.len⟩

theorem Space.agree {workspace p : BitVec 32} {size w : Nat} {s t : State}
    (S : Space workspace p size w s) (T : Space workspace p size w t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.stack.trans T.stack.symm
  · exact S.workspace.trans T.workspace.symm

theorem Space.header {workspace p : BitVec 32} {size w : Nat} {s : State}
    (S : Space workspace p size w s) : 256 + 8 * w ≤ slot w 5 ∧ slot w 5 + 8 * w ≤ size :=
  ⟨slot5_ge w, S.space⟩

/-- The registers of a copy: its source and destination, at `x` and `y`. -/
def copyRegs (workspace p : BitVec 32) (w src dst : Nat) : Reg → BitVec 32
  | .esp => p
  | .edi => workspace
  | .ebp => workspace + BitVec.ofNat 32 src
  | .ebx => workspace + BitVec.ofNat 32 dst
  | .esi => BitVec.ofNat 32 (2 * w)
  | .ecx => BitVec.allOnes 32
  | _ => 0

/-- A copy about to run: the working space and its pointers. -/
structure CopyIn (workspace p : BitVec 32) (size w src dst : Nat) (s : State) : Prop where
  space : Space workspace p size w s
  regs : ∀ r ∈ [Reg.esp, .edi, .ebp, .ebx, .esi, .ecx], s.gpr r = copyRegs workspace p w src dst r

theorem copy_trace {workspace p : BitVec 32} {size w src dst : Nat}
    (fits : slot w 5 + 8 * w ≤ size → src + 8 * w ≤ size ∧ dst + 8 * w ≤ size ∧
      (dst + 8 * w ≤ src ∨ src + 8 * w ≤ dst) ∧ 8 ≤ dst) :
    RelCT isa (fun s t => (CopyIn workspace p size w src dst s ∧ CopyIn workspace p size w src dst t) ∧
        VG.X86.Taint.Agree (τr [.esp, .edi, .ebp, .ebx, .esi, .ecx]) s t) copyLoop
      (fun u z => (Space workspace p size w u ∧ Space workspace p size w z) ∧
        VG.X86.Taint.Agree (τr [.esp, .edi]) u z) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebp, .ebx, .esi, .ecx])) copyLoop
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT copyLoop copyLoop
      (VG.Taint.hintOf taint (τr [.esp, .edi, .ebp, .ebx, .esi, .ecx]) (Code.erase copyLoop))
      (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)
  refine checked raw fun s S => ?_
  obtain ⟨fit, dstFit, apart, headerApart⟩ := fits S.space.space
  have nowrap := S.space.scratch.nowrap
  have hws : Ws s (workspace.setWidth 64) size := ⟨S.space.scratch.wr, nowrap⟩
  have edi : s.gpr .edi = workspace := S.space.workspace
  refine WP.mono (copyLoop_ok hws (x := dst) (y := src) (N := 2 * w) (by have := S.space.width; omega) (by omega)
    (by omega) (by omega)
    (ptrAt_edi S.space.scratch (by rw [S.regs .ebx (by simp), edi]; rfl))
    (ptrAt_edi S.space.scratch (by rw [S.regs .ebp (by simp), edi]; rfl))
    (by rw [S.regs .esi (by simp)]; change (BitVec.ofNat 32 (2 * w)).toNat = 2 * w
        rw [BitVec.toNat_ofNat]; have := S.space.widthBound; omega)
    (S.regs .ecx (by simp))) fun u ⟨O, _, K⟩ => ?_
  exact S.space.keep K (by decide) (by decide)
    (BitVec.eq_of_toNat_eq (O.w32 (d := 4) (Or.inl (by omega)) (by omega)))

theorem save_trace {workspace p : BitVec 32} {size w : Nat} :
    RelCT isa (fun s t => Space workspace p size w s ∧ Space workspace p size w t) save
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  unfold save
  have setupRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block saveSetup)
      (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have setup := publish (X := Space workspace p size w) (Y := CopyIn workspace p size w 256 (slot w 5))
    [.esp, .edi, .ebp, .ebx, .esi, .ecx] (copyRegs workspace p w 256 (slot w 5)) (fun _ _ S T => S.agree T)
    setupRaw (fun s S => ?_)
  rotate_left
  · have header := S.header
    refine WP.mono (saveSetup_ok S.scratch S.widthBound (by omega) S.len) fun d ⟨K, M, ebp, ebx, esi, ecx⟩ => ?_
    have Sd : Space workspace p size w d := S.keep K (by decide) (by decide) (by rw [M])
    have regs : ∀ r ∈ [Reg.esp, .edi, .ebp, .ebx, .esi, .ecx], d.gpr r = copyRegs workspace p w 256 (slot w 5) r := by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Sd.stack
      · exact Sd.workspace
      · rw [ebp, S.workspace]; rfl
      · rw [ebx, S.workspace]; rfl
      · apply BitVec.eq_of_toNat_eq; rw [esi]; change 2 * w = (BitVec.ofNat 32 (2 * w)).toNat
        rw [BitVec.toNat_ofNat]; have := S.widthBound; omega
      · exact ecx
    exact ⟨⟨Sd, regs⟩, regs⟩
  have loop := copy_trace (workspace := workspace) (p := p) (size := size) (w := w) (src := 256) (dst := slot w 5)
    fun h => by have := slot5_ge w; exact ⟨by omega, h, Or.inr (by omega), by omega⟩
  have ptrRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (savedPtr .ebx .edx)) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have ptr := publish (X := Space workspace p size w) (Y := fun _ => True) [.esp, .edi, .ebx]
    (copyRegs workspace p w 256 (slot w 5)) (fun _ _ S T => S.agree T) ptrRaw (fun s S => ?_)
  rotate_left
  · refine WP.mono (savedPtr_block_ok S.scratch (by have := S.header; omega) S.len (by decide) (by decide)
      (by decide)) fun d ⟨K, _, ebx⟩ => ⟨trivial, ?_⟩
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · rw [K.1 .esp (by decide)]; exact S.stack
    · rw [K.1 .edi (by decide)]; exact S.workspace
    · rw [ebx, S.workspace]; rfl
  have dec : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebx])) (.block decrementAt)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel)
  exact RelCT.seq setup (RelCT.seq loop (RelCT.seq (ptr.mono (fun _ _ H => H.1) (fun _ _ H => H.2)) dec))

end VG.Proof.RsaKeyGen.X86.ExponentRt
