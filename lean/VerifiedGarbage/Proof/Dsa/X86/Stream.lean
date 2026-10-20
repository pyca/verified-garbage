module
public import VerifiedGarbage.Proof.Dsa.X86.StreamFrame
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.X86.StreamInit
import VerifiedGarbage.Proof.Dsa.X86.StreamLoop
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Complete streaming reduction, including the empty input -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86

theorem reduceStream_ok {n size m len : Nat} {base : Addr} {s : State} {p : BitVec 32} {src : Src}
    (h : Context n m base size s) (hm : 255 < m) (hlen : len < 2 ^ 32)
    (hsrc : LenSrc base size n s src len)
    (inp : StreamInput s base (contextBytes n) p len) (hp : s.gpr .esi = p) :
    WP isa (reduceStream n src) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len) % m ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold reduceStream
  refine streamInit_ok h fun u cu Y B O K' => ?_
  have K : Keeps powerClob s u := K'.mono (by decide)
  have esi : u.gpr .esi = p := by rw [K'.1 _ (by decide)]; exact hp
  refine WP.seq (wp_movS (hsrc u cu.scr K.2.1 K.2.2 O) fun u₁ v₁ _ => WP.block_nil ?_)
  refine WP.seq (wp_addS rfl fun u₂ v₂ _ => wp_cmpS rfl fun u₃ f₃ z₃ => WP.block_nil ?_)
  have K₃ : Keeps powerClob u u₃ := ((v₁.keeps.mono (by decide)).widen v₂.keeps).trans (f₃.keeps _)
  have m₃ : u₃.mem = u.mem := by rw [f₃.mem, v₂.mem, v₁.mem]
  have c₃ : Context n m base size u₃ := ⟨cu.scr.of_keeps K₃ (by decide), cu.size_le,
    m₃ ▸ cu.modulus, cu.gt_one, m₃ ▸ cu.inverse⟩
  have esi₂ : u₂.gpr .esi = p := by rw [v₂.other _ (by decide), v₁.other _ (by decide), esi]
  have ebx₂ : u₂.gpr .ebx = p + BitVec.ofNat 32 len := by
    rw [v₂.gpr, v₁.gpr, v₁.other _ (by decide), esi, BitVec.add_comm]
  have z : (p - (p + BitVec.ofNat 32 len) == 0) = decide (len = 0) := by
    rw [show p - (p + BitVec.ofNat 32 len) = BitVec.ofNat 32 0 - BitVec.ofNat 32 len by bv_omega,
      counter_equal (by decide) hlen]
    exact decide_eq_decide.mpr eq_comm
  rw [esi₂, ebx₂, z] at z₃
  by_cases hz : len = 0
  · refine WP.ite true (by simp only [eval, z₃, hz, decide_true]) (fun _ => WP.block_nil ⟨c₃, ?_, by rw [m₃]; exact O,
      K.trans K₃⟩) (fun h => Bool.noConfusion h)
    rw [m₃, Y, hz]
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, Spec.Dsa.decodeBE, List.foldl_nil, Nat.zero_mod]
  · refine WP.ite false (by simp only [eval, z₃, hz, decide_false]) (fun h => Bool.noConfusion h) (fun _ => ?_)
    have Os : Outs base (streamRanges n) s.mem u₃.mem := by rw [m₃]; exact O
    have Ks : Keeps powerClob s u₃ := K.trans K₃
    have count : u₃.gpr .esi = p := by rw [f₃.gpr, esi₂]
    have stop : u₃.gpr .ebx = p + BitVec.ofNat 32 len := by rw [f₃.gpr, ebx₂]
    refine WP.mono (streamLoop_ok c₃ hm (by omega) hlen (inp.keep Ks) count stop
      (by rw [m₃]; exact Y) (by rw [m₃, B]; decide)) fun t I => ⟨I.context, ?_, Os.trans I.mem, Ks.trans I.keeps⟩
    rw [I.value, inp.bytes (streamRanges_whole (Nat.le_refl _) Os)]

end VG.Proof.Dsa.X86
