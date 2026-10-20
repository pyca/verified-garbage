module
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify

import VerifiedGarbage.Proof.Dsa.X86.OutputPointer
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Masked writes of the two fixed-width signature scalars -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem writeScalar_ok {s : State} {base : Addr} {size qLen input n : Nat} {out : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (hn : n = (qLen + 7) / 8) (h4 : 4 ≤ qLen) (hmax : qLen ≤ 32) (hw4 : qLen % 4 = 0)
    (hc : contextBytes n ≤ size)
    (Ri : OperandReady s base n (.local input) qLen)
    (second accepted : Bool)
    (hm : flagW base (Layout.field .mask) s = if accepted then BitVec.allOnes 32 else 0)
    (hp : out = pointerValue base s (.input .out) + (if second then BitVec.ofNat 32 qLen else 0))
    (hf : out.toNat + qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ qLen → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (hd : Region.Disjoint ⟨off base (slot n 5), 8 * n⟩ ⟨out.setWidth 64, qLen⟩) :
    WP isa (SignVerify.writeScalar qLen input second) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) qLen =
        (if accepted then Spec.Dsa.encodeBE qLen (operandValue s base (.local input) qLen)
          else List.replicate qLen 0) ∧
      Keeps powerClob s t ∧
      (∀ a, contextBytes n ≤ ofs base a → qLen ≤ ofs (out.setWidth 64) a → t.mem a = s.mem a) := by
  have N : n ≤ 48 := by omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have B := slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at B
  have hslot : slot n 5 + 8 * n ≤ size := by omega
  have hb : Layout.field .mask + 4 ≤ size := by
    have H : 8256 ≤ size := hz
    change 8248 ≤ size
    omega
  unfold SignVerify.writeScalar
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreLoad_ok hs hz hslot h4 (by omega) hw4 Ri.toReadableComponent
    (Ri.slot (by decide))) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have OW := slotOutside_whole Ou (by decide)
  have Pu : pointerValue base u (.input .out) = pointerValue base s (.input .out) :=
    pointerValue_keep Ku (by decide) OW (by omega) _
  have Fu : flagW base (Layout.field .mask) u = flagW base (Layout.field .mask) s :=
    pointerValue_keep Ku (by decide) OW (by omega) (.input .mask)
  refine WP.seq (WP.block_append (WP.mono (outputPointer_ok (hs.of_keeps Ku (by decide)) hz second)
    fun v ⟨Pv, Kv, Ov⟩ => ?_))
  have P : v.gpr .esi = out := by rw [Pv, Pu, hp]
  have Ksv : Keeps powerClob s v := (Ku.mono (by decide)).trans (Kv.mono (by decide))
  refine wp_movS (readSrc_sc (hs.of_keeps Ksv (by decide)) hb) fun w vw _ => WP.block_nil ?_
  have Ksw : Keeps powerClob s w := Ksv.widen vw.keeps
  have Pw : w.gpr .esi = out := (vw.other _ (by decide)).trans P
  have Fw : w.gpr .ecx = if accepted then BitVec.allOnes 32 else 0 := by
    rw [vw.gpr]
    change flagW base (Layout.field .mask) v = _
    simpa only [flagW, Ov] using Fu.trans hm
  refine WP.mono (storeComponent_ok (hs.of_keeps Ksw (by decide)) accepted Fw hslot h4 (by omega) hw4
    (by rw [Pw]; exact hf) (by intro e k hek; rw [Pw, Ksw.2.2]; exact hw e k hek)
    (by rw [Pw]; exact hd)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, Ksw.trans (Kt.mono (by decide)), ?_⟩
  · simpa only [Pw, vw.mem, Ov, Vu] using Vt
  · intro a ha hb
    rw [Pw] at Ot
    rw [Ot a (.inr (by simpa using hb)), vw.mem, Ov, OW a (.inr (by simpa using ha))]

end VG.Proof.Dsa.X86
