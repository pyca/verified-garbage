module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEntry

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Native cdecl argument entry composes with the complete key body -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyDispatch.lean`, which only this module imported.
section

/-! # Public width dispatch selects the complete native key operation -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem dispatch_ok {E : Environment} {s : State} {w : Nat} (h : Input E s)
    (size : E.n = 4 * w) (small : w < 2 ^ 32) (value : s.gpr .eax = BitVec.ofNat 32 w)
    (choices : List Nat) (member : w ∈ choices) (bounded : ∀ v ∈ choices, v < 2 ^ 32) :
    WP isa (dispatch choices) s fun t =>
      Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  induction choices generalizing s with
  | nil => cases member
  | cons v rest ih =>
    unfold dispatch
    refine WP.seq (wp_cmpS rfl fun a A Z => WP.block_nil ?_)
    have ha : Input E a := h.keep (h.ws.rest (A.keeps [])) (A.keeps []) (by intro d hd; rw [A.mem])
    have condition : isa.eval .e a = some (decide (w = v)) := by
      change a.zf = _
      rw [Z, value]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      rw [BitVec.sub_eq_iff_eq_add]
      change (BitVec.ofNat 32 w = 0#32 + BitVec.ofNat 32 v) ↔ w = v
      rw [BitVec.zero_add, ← BitVec.toNat_inj]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (bounded v List.mem_cons_self)]
    by_cases same : w = v
    · refine WP.ite true (by rw [condition, decide_eq_true same]) (fun _ => ?_) (fun bad => nomatch bad)
      rw [← same, ← size]
      refine WP.mono (sized_ok ha) fun t ⟨ht, result, F, K⟩ => ?_
      rw [A.mem] at result F
      exact ⟨ht, result, F, (A.keeps _).trans K⟩
    · refine WP.ite false (by rw [condition, decide_eq_false same]) (fun bad => nomatch bad) (fun _ => ?_)
      refine WP.mono (ih ha (by rw [A.gpr]; exact value) (List.mem_cons.mp member |>.resolve_left same)
        (fun j hj => bounded j (List.mem_cons_of_mem _ hj))) fun t ⟨ht, result, F, K⟩ => ?_
      rw [A.mem] at result F
      exact ⟨ht, result, F, (A.keeps _).trans K⟩

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyFront.lean`, which only this module imported.
section

/-! # The public modulus byte length selects a supported native key width -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.Key

theorem front_ok {E : Environment} {s : State} (h : Input E s) :
    WP isa (.seq (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4]) (dispatch widths)) s fun t =>
      Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have valid := h.valid.length
  have dimensions := h.valid.widths
  let w := E.primeLength / 8
  have bounds : 4 ≤ w ∧ w ≤ 64 := by unfold w; obtain ⟨_, _, _⟩ := valid; omega
  have width : E.n = 4 * w := by unfold w Environment.n; obtain ⟨_, _, _⟩ := valid; omega
  have lengthBound : 2 * E.primeLength < 2 ^ 32 := by omega
  have space := h.ws.hdr_le
  refine WP.seq (wp_movS (readSrc_sc h.ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.hdr at space; omega))
    fun a A _ => wp_shr (by decide) fun b B _ => WP.block_nil ?_)
  have memory : b.mem = s.mem := B.mem.trans A.mem
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have hb := h.keep (h.ws.rest K) K (by intro d hd; rw [memory])
  have selected : b.gpr .eax = BitVec.ofNat 32 w := by
    rw [B.gpr, A.gpr, h.arguments 1 (by decide)]
    change BitVec.ofNat 32 (2 * E.primeLength) >>> 4 = BitVec.ofNat 32 w
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt lengthBound, Nat.mod_eq_of_lt (by omega : w < 2 ^ 32)]
    change (2 * E.primeLength) / 16 = w
    unfold w
    omega
  refine WP.mono (dispatch_ok hb width (by omega) selected widths ?_ ?_)
    fun t ⟨ht, result, F, Kt⟩ => ?_
  · exact List.mem_map.mpr ⟨w - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have H := List.mem_range.mp hi
    omega
  · rw [memory] at result F
    exact ⟨ht, result, F, (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys

structure EntryInput (E : Environment) (p : BitVec 32) (s : State) : Prop where
  arguments : KeyArgs.Entry E.base E.size p E.argument s
  outWrite : ∀ i < 7, InRegions s.wr (E.outputRegion i).base (E.outputRegion i).len
  exponentRead : InRegions (s.rd ++ s.wr) E.exponentRegion.base E.exponentRegion.len
  argsOutput : ∀ i < 7, (KeyArgs.argsRegion p).Disjoint (E.outputRegion i)

def bodyClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem enter_input_ok {E : Environment} {p : BitVec 32} {s : State} (v : E.Valid) (I : EntryInput E p s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.enter s fun t =>
      Input E t ∧ Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  refine WP.mono (KeyArgs.enter_ok I.arguments) fun t ⟨C, header, O, K⟩ => ?_
  have dimensions := v.widths
  have ws : Ws t E.base E.size E.n 32 :=
    ⟨C.scratch, v.bankFit, by omega, by omega⟩
  have input : Input E t := by
    refine ⟨v, ws, header, ?_, ?_⟩
    · intro i hi
      rw [K.2.2]
      exact I.outWrite i hi
    · rw [K.2.1, K.2.2]
      exact I.exponentRead
  have frame : Frame [E.workspaceRegion] s.mem t.mem :=
    outs_scratch_frame (by have := C.scratch.nowrap; omega)
      (Outs.of_outside (rs := [(0, 72)]) O (List.mem_singleton_self _))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; change 0 + 72 ≤ E.size; exact I.arguments.header)
  exact ⟨input, frame, K⟩

theorem body_ok {E : Environment} {p : BitVec 32} {s : State} (v : E.Valid) (I : EntryInput E p s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.body s fun t =>
      Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps bodyClob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Key.body
  refine WP.seq (WP.mono (enter_input_ok v I) fun a ⟨Ia, F, K⟩ => ?_)
  refine WP.mono (front_ok Ia) fun t ⟨ht, result, Ft, Kt⟩ => ?_
  unfold BodyOutcome at result
  rw [Ia.exponent_preserved F, Ia.output_preserved (by decide : 2 < 7) F,
    Ia.output_preserved (by decide : 3 < 7) F] at result
  refine ⟨ht, result, ?_, (K.mono (by unfold bodyClob; decide)).trans (Kt.mono (by unfold bodyClob; decide))⟩
  exact (F.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self ..)).trans Ft

end VG.Proof.RsaKeyGen.X86.Key
