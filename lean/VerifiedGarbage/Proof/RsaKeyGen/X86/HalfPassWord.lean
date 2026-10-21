module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.HalfPass
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ExponentWord

/-! # One exponent word is halved or retained under the secret mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.HalfPass

theorem select_word (old shifted : BitVec 32) (choice : Bool) :
    old ^^^ ((shifted ^^^ old) &&& cmask choice) = if choice then shifted else old := by
  cases choice
  · rw [show cmask false = 0#32 from rfl, BitVec.and_zero, BitVec.xor_zero]
    rfl
  · rw [show cmask true = BitVec.allOnes 32 from rfl, BitVec.and_allOnes, BitVec.xor_comm shifted old,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rfl

theorem step_ok {s : State} {base : Addr} {size src out index : Nat} (scratch : Scr s base size)
    (pointer : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * index))
    (srcFit : src + 4 * index + 8 ≤ size) (outFit : out + 4 * index + 4 ≤ size)
    {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa (.block (step src out)) s fun t =>
      Outside base (out + 4 * index) 4 s.mem t.mem ∧
      w32 t.mem base (out + 4 * index) =
        (if choice then w32 s.mem base (src + 4 * index) / 2 +
          2 ^ 31 * (w32 s.mem base (src + 4 * index + 4) % 2) else w32 s.mem base (src + 4 * index)) ∧
      Keeps [.eax, .ebx, .edx] s t := by
  unfold step
  refine wp_movS (readSrc_at' scratch pointer (by omega)) fun a A _ =>
    wp_logicS (.inl rfl) rfl fun b B => wp_ror (by decide) fun c C => ?_
  have Kc : Keeps [.eax, .ebx, .edx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have pc : c.gpr .ebp = c.gpr .edi + BitVec.ofNat 32 (4 * index) := by
    rw [Kc.1 .ebp (by decide), Kc.1 .edi (by decide)]; exact pointer
  refine wp_movS (readSrc_at' (scratch.of_keeps Kc (by decide)) pc (by omega)) fun d D _ =>
    wp_shr (by decide) fun e E _ => wp_addS rfl fun f F _ => ?_
  have Kf : Keeps [.eax, .ebx, .edx] s f := ((Kc.widen D.keeps).widen E.keeps).widen F.keeps
  have pf : f.gpr .ebp = f.gpr .edi + BitVec.ofNat 32 (4 * index) := by
    rw [Kf.1 .ebp (by decide), Kf.1 .edi (by decide)]; exact pointer
  refine wp_movS (readSrc_at' (scratch.of_keeps Kf (by decide)) pf (by omega)) fun g G _ =>
    wp_xor fun h H => wp_and fun i I => wp_xor fun j J => ?_
  have Kj : Keeps [.eax, .ebx, .edx] s j := (((Kf.widen G.keeps).widen H.keeps).widen I.keeps).widen J.keeps
  have pj : j.gpr .ebp = j.gpr .edi + BitVec.ofNat 32 (4 * index) := by
    rw [Kj.1 .ebp (by decide), Kj.1 .edi (by decide)]; exact pointer
  have Sj := scratch.of_keeps Kj (by decide)
  refine wp_storeS (Sj.ea_at' pj (by omega)) (Sj.write outFit) fun t T => WP.block_nil ?_
  have M : j.mem = s.mem := J.mem.trans (I.mem.trans (H.mem.trans (G.mem.trans
    (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem))))))))
  have old : g.gpr .ebx = s.mem.readW (off base (src + 4 * index)) 32 := by
    rw [G.gpr, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
  have half : f.gpr .edx = (s.mem.readW (off base (src + 4 * index)) 32 >>> 1) +
      (s.mem.readW (off base (src + 4 * index + 4)) 32 &&& 1).rotateRight 1 := by
    rw [F.gpr, E.gpr, D.gpr, E.other .eax (by decide), D.other .eax (by decide), C.gpr, B.gpr, A.gpr,
      C.mem, B.mem, A.mem]
    rw [show src + 4 + 4 * index = src + 4 * index + 4 by omega]
    rfl
  have selected : j.gpr .ebx = if choice then f.gpr .edx else g.gpr .ebx := by
    rw [J.gpr, I.other .ebx (by decide), H.other .ebx (by decide), I.gpr, H.gpr,
      G.other .edx (by decide), H.other .ecx (by decide),
      G.other .ecx (by decide), Kf.1 .ecx (by decide), mask, select_word]
  refine ⟨?_, ?_, Kj.widen (T.keeps [])⟩
  · rw [T.mem, M]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  · rw [T.mem, w32_write_self, selected, old, half]
    cases choice
    · rfl
    · exact VG.Proof.Mont.X86.Dynamic.shifted_word _ _

end VG.Proof.RsaKeyGen.X86.HalfPass
