module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Import
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Exact effects of one native-word big-endian import -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Import

theorem decrement {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t .ecx (s.gpr .ecx - 1) →
      t.zf = some (s.gpr .ecx - 1 == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub .ecx (.imm 1) :: is)) s Q :=
  cons (by simp only [exec, execAlu, readSrc, Option.bind_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem step_ok (s : State) (src dst : Addr)
    (source : s.ea (at_ .esi) = src) (destination : s.ea (at_ .ebx) = dst)
    (readable : InRegions (s.rd ++ s.wr) src 4) (writable : InRegions s.wr dst 4) :
    WP isa (.block step) s fun t =>
      t.mem = s.mem.writeW dst (bswap (s.mem.readW src 32)) ∧
      t.gpr .esi = s.gpr .esi + 4 ∧ t.gpr .ebx = s.gpr .ebx - 4 ∧
      t.gpr .ecx = s.gpr .ecx - 1 ∧ t.zf = some (s.gpr .ecx - 1 == 0) ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  unfold step
  refine wp_movS (by change s.load32 (s.ea (at_ .esi)) = _; rw [source, State.load32,
    ite_eq_left_iff.mpr (fun h => absurd readable h)]) fun a A _ => ?_
  refine wp_bswap fun b B => ?_
  refine wp_storeS (a := dst)
    (by change (b.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = dst
        rw [B.other .ebx (by decide), A.other .ebx (by decide)]; exact destination)
    (by rw [B.wr, A.wr]; exact writable) fun c C => ?_
  refine wp_addS rfl fun d D _ => wp_subS rfl fun e E _ => decrement fun t T Z => WP.block_nil ?_
  have Kc := C.keeps []
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem, B.gpr, A.gpr]
  · rw [T.other .esi (by decide), E.other .esi (by decide), D.gpr,
      Kc.1 .esi (by decide), B.other .esi (by decide), A.other .esi (by decide)]
  · rw [T.other .ebx (by decide), E.gpr, D.other .ebx (by decide), Kc.1 .ebx (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide)]
  · rw [T.gpr, E.other .ecx (by decide), D.other .ecx (by decide), Kc.1 .ecx (by decide),
      B.other .ecx (by decide), A.other .ecx (by decide)]
  · rw [Z, E.other .ecx (by decide), D.other .ecx (by decide), Kc.1 .ecx (by decide),
      B.other .ecx (by decide), A.other .ecx (by decide)]
  · exact (((((A.keeps.mono (by decide)).widen B.keeps).widen Kc).widen D.keeps).widen E.keeps).widen T.keeps

end VG.Proof.RsaKeyGen.X86.Import
