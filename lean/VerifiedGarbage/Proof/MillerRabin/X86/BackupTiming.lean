module

public import VerifiedGarbage.Proof.MillerRabin.X86.TaintStage
import VerifiedGarbage.Proof.Framework.Offset

/-! # Saving and restoring borrowed scratch bytes retains public metadata -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

namespace PieceInput

theorem after_stack {s t : State} {base : Addr} {bytes w d n : Nat} {sp len : BitVec 32}
    (h : PieceInput base bytes w sp len s) (K : Keeps transferClobbers s t)
    (frame : Frame [⟨off (byteAddr (s.gpr .esp)) d, n⟩] s.mem t.mem)
    (fit : d + n ≤ VG.Impl.MillerRabin.X86.frameBytes) (apart : savedLength + 4 ≤ d) :
    PieceInput base bytes w sp len t := by
  have stack : t.gpr .esp = sp := (K.1 _ (by decide)).trans h.stack
  refine ⟨h.context.of_keeps K, by rw [stack, ← h.stack]; exact h.room,
    K.2.2.trans h.wr, stack, h.capacity, ?_, ?_⟩
  · exact (h.context.stack_frame_readW fit frame (by have := h.capacity; omega : 48 + 4 ≤ bytes)).trans h.width
  · rw [← h.stack]
    refine (frame.readW (r := ⟨off (byteAddr (s.gpr .esp)) savedLength, 4⟩)
      (Region.contains_self _ _) ?_ (by decide)).trans ?_
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl apart) (by decide) (by change d + n ≤ 1132 at fit; omega)
    · rw [h.stack]
      exact h.length

theorem after_workspace {s t : State} {base : Addr} {bytes w d n : Nat} {sp len : BitVec 32}
    (h : PieceInput base bytes w sp len s) (K : Keeps transferClobbers s t)
    (frame : Frame [⟨off base d, n⟩] s.mem t.mem) (fit : d + n ≤ bytes) (apart : 52 ≤ d) :
    PieceInput base bytes w sp len t := by
  have stack : t.gpr .esp = sp := (K.1 _ (by decide)).trans h.stack
  refine ⟨h.context.of_keeps K, by rw [stack, ← h.stack]; exact h.room,
    K.2.2.trans h.wr, stack, h.capacity, ?_, ?_⟩
  · refine (frame.readW (r := ⟨off base 48, 4⟩) (Region.contains_self _ _) ?_ (by decide)).trans h.width
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl apart) (by decide) (by have := h.context.ws.nowrap; omega)
  · rw [← h.stack]
    have eq := congrArg (BitVec.setWidth 32) (h.context.ws_frame_read fit frame
      (by decide : savedLength + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes))
    change t.mem.readW (off (byteAddr (s.gpr .esp)) savedLength) 32 =
      s.mem.readW (off (byteAddr (s.gpr .esp)) savedLength) 32 at eq
    exact eq.trans (by rw [h.stack]; exact h.length)

theorem save_tail {s : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (h : PieceInput base bytes w sp len s) (hf : arrAt w 28 ≤ bytes) :
    WP isa saveTail s (PieceInput base bytes w sp len) := by
  refine WP.mono (saveTail_ok h.context hf h.width) ?_
  intro t result
  have frame := result.frame
  rw [h.context.stack_address (by decide)] at frame
  exact h.after_stack result.keeps frame (by decide) (by decide)

theorem restore_tail {s : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (h : PieceInput base bytes w sp len s) (hf : arrAt w 28 ≤ bytes) :
    WP isa restoreTail s (PieceInput base bytes w sp len) := by
  have fit : scratch w + 32 ≤ bytes := by
    have := scratch_start w
    have := array_monotone w (by decide : 2 ≤ 28)
    omega
  refine WP.mono (restoreTail_ok h.context hf h.width) ?_
  intro t result
  have frame := result.frame
  rw [ptr32_addr (by have := h.context.ws.nowrap; omega : base.toNat + scratch w < 2 ^ 32)] at frame
  exact h.after_workspace result.keeps frame fit (by unfold scratch; omega)

theorem cert_ct {base : Addr} {bytes w : Nat} {sp len : BitVec 32} {c : Prog isa}
    (cert : PieceCert c) :
    RelCT isa (fun s t => PieceInput base bytes w sp len s ∧ PieceInput base bytes w sp len t) c
      (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := cert
  exact RelCT.taint (A := taint) pieceTaint (fun _ _ ⟨h₁, h₂⟩ => h₁.agree h₂) checked

theorem save_protected_ct {base : Addr} {bytes w : Nat} {sp len : BitVec 32} (hf : arrAt w 28 ≤ bytes) :
    RelCT isa (fun s t => PieceInput base bytes w sp len s ∧ PieceInput base bytes w sp len t)
      saveProtected (fun _ _ => True) := by
  have tailCT := (cert_ct (base := base) (bytes := bytes) (w := w) (sp := sp) (len := len) save_tail_cert).wp
    (F₁ := PieceInput base bytes w sp len) (F₂ := PieceInput base bytes w sp len)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨h₁.save_tail hf, h₂.save_tail hf⟩)
  exact tailCT.seq ((cert_ct save_array_cert).mono
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ _ => trivial))

theorem restore_protected_ct {base : Addr} {bytes w : Nat} {sp len : BitVec 32} (hf : arrAt w 28 ≤ bytes) :
    RelCT isa (fun s t => PieceInput base bytes w sp len s ∧ PieceInput base bytes w sp len t)
      restoreProtected (fun _ _ => True) := by
  have tailCT := (cert_ct (base := base) (bytes := bytes) (w := w) (sp := sp) (len := len) restore_tail_cert).wp
    (F₁ := PieceInput base bytes w sp len) (F₂ := PieceInput base bytes w sp len)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨h₁.restore_tail hf, h₂.restore_tail hf⟩)
  exact tailCT.seq ((cert_ct restore_array_cert).mono
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ _ => trivial))

end PieceInput
end VG.Proof.MillerRabin.X86
