module

import VerifiedGarbage.Proof.Rsa.X86.KcFrames
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
import VerifiedGarbage.Proof.Bignum.X86.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86.KcInputs

/-! # Importing one key component into its zeroed workspace array

`inputsRt`: the arrays at the width of the modulus's length, argument 1;
`load_ok` reverses an input's bytes into its zeroed array.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86 (reverseBytes)
open VG.Impl.Rsa.X86.KeyRt (Lay arrPtr)
open VG.Impl.Rsa.X86.KeyCheck (nArr scratchArg)
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S)
open VG.Proof.Rsa.X86.KeyRt

theorem Inputs.scratchFrame {g : CallGeometry} {s : State} {m : Mem} (h : Inputs g s)
    (frame : Outside g.base 0 g.size s.mem m) : Frame g.writes s.mem m := by
  have fit := h.ws.workspace.nowrap
  have f := outside_frame frame (by omega)
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    f.mono (rs' := g.writes) (by simp [CallGeometry.writes, off])

/-- The arrays at the width of the modulus's length. -/
theorem inputsRt {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    RtWs (VG.Impl.Rsa.X86.KeyCheckRt.lay g.full) s g.base g.size (g.args 1).toNat nArr := by
  have ws := h.ws
  rw [len.width] at ws
  refine ⟨ws, ⟨_, len.upper, rfl, ?_⟩, ?_, Nat.le_trans len.upper (by decide), Nat.le_refl 1⟩
  · have a := h.arguments 1 (by cases g.full <;> decide)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← len.scratch]; exact h.arguments (scratchArg g.full) (by omega)

theorem load_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (i : Nat)
    (hi : 2 * i < scratchArg g.full) {j : Nat}
    (hj : j < nArr) (zero : num s.mem g.base (kw (g.args 1).toNat) j = 0) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.load (VG.Impl.Rsa.X86.KeyCheckRt.lay g.full) (2 * i) j) s fun t =>
      Inputs g t ∧ Keep g.base (kw (g.args 1).toNat) [j] [] s.mem t.mem ∧
      num t.mem g.base (kw (g.args 1).toNat) j =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (g.buffer (2 * i)).base (g.buffer (2 * i)).len) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have r := inputsRt h len
  have positive := h.inputPositive i hi
  have bound := h.inputBound i hi
  have sourceFit := h.inputFit i hi
  have sourceRead := h.inputRead i hi
  have apart := h.inputApart i hi ⟨g.base, g.size⟩ (by simp [CallGeometry.writes])
  have nw := r.ws.workspace.nowrap
  have fits := r.ws.arr_fit hj
  have wd := len.width
  simp only [S] at fits
  have up := h.upper
  have kwEq : kw (g.args 1).toNat = 2 * g.n := by rw [wd]
  simp only [CallGeometry.buffer] at positive bound sourceFit sourceRead apart ⊢
  generalize hL : (g.args (2 * i + 1)).toNat = L at positive bound sourceFit sourceRead apart ⊢
  have srcLen : L < 2 ^ 32 := by omega
  have Lw : L ≤ 4 * kw (g.args 1).toNat := by omega
  unfold VG.Impl.Rsa.X86.KeyRt.load
  simp only [List.cons_append, List.nil_append]
  have a₀ := h.arguments (2 * i) (by omega)
  have a₁ := h.arguments (2 * i + 1) (by omega)
  refine WP.seq (wp_movS a₀.readSrc fun u₁ U₁ _ => ?_)
  have h₁ := h.after U₁.keeps (by decide) (by decide) (by rw [U₁.mem]; exact Frame.refl _ _)
  refine wp_movS (h₁.arguments (2 * i + 1) (by omega)).readSrc fun u₂ U₂ _ => ?_
  have K₂ : Keeps [.esi, .ecx] s u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have m₂ : u₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  have r₂ := r.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc r₂) r₂.lenLe r₂.edi (by decide) (by decide) (by omega) fun v Kv mv pv _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  let dst := v.gpr .ebx
  have dstAddr : byteAddr dst = off g.base (arr (kw (g.args 1).toNat) j) :=
    VG.Proof.Bignum.X86.PublicRt.byteAddr_ptr pv (by omega)
  have dstNat : dst.toNat = g.base.toNat + arr (kw (g.args 1).toNat) j := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega)]
  have K₄ : Keeps [.ebx, .ecx, .edx, .esi] v v₄ :=
    (u₃.keeps.mono (by decide)).trans (u₄.keeps.mono (by decide))
  have m₄ : v₄.mem = s.mem := by rw [u₄.mem, u₃.mem, mv, m₂]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have ebx₄ : v₄.gpr .ebx = dst := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide)]
  have esi₄ : v₄.gpr .esi = g.args (2 * i) + BitVec.ofNat 32 (L - 1) := by
    have ecx₂ : v.gpr .ecx = BitVec.ofNat 32 L := by
      rw [Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [u₄.gpr, u₃.gpr, ecx₂, Kv.1 _ (by decide), U₂.other _ (by decide), U₁.gpr]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ :=
    (K₂.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  have vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (g.args (2 * i))) L := by
    rw [keep.2.1, keep.2.2]; exact sourceRead
  have vw : InRegions v₄.wr (byteAddr dst) L := by
    rw [keep.2.2, dstAddr]; exact r.ws.workspace.write (by omega)
  have hsub : Region.Sub ⟨off g.base (arr (kw (g.args 1).toNat) j), L⟩ ⟨g.base, g.size⟩ := by
    have := Offset.sub g.base (d := arr (kw (g.args 1).toNat) j) (n := L) (e := 0) (k := g.size) (Nat.zero_le _)
      (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have apart' : Region.Disjoint ⟨byteAddr (g.args (2 * i)), L⟩ ⟨g.base, g.size⟩ := apart
  have hd : Region.Disjoint ⟨byteAddr (g.args (2 * i)), L⟩ ⟨off g.base (arr (kw (g.args 1).toNat) j), L⟩ :=
    apart'.sub_right hsub
  have fit : (g.args (2 * i)).toNat + L ≤ 2 ^ 32 := sourceFit
  have ctx := reverseCtx_of_regions v₄ (g.args (2 * i)) dst srcLen fit (by omega) vr vw
    (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v₄ ctx (by omega) esi₄ ebx₄ ecx₄) fun t I => ?_
  have Ot : Outside g.base (arr (kw (g.args 1).toNat) j) (4 * kw (g.args 1).toNat) v₄.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    have ek : ofs g.base a = arr (kw (g.args 1).toNat) j + k := by
      rw [he, byteAddr_add (by omega), dstAddr]
      exact ofs_off g.base (by omega)
    omega
  have O : Outside g.base 0 g.size s.mem t.mem := by
    rw [← m₄]; exact Ot.mono (Nat.zero_le _) (by omega)
  have keepT : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := keep.trans (I.rest.mono (by decide))
  refine ⟨h.after keepT (by decide) (by decide) (h.scratchFrame O), ?_, ?_, keepT⟩
  · rw [← m₄]; exact Keep.of_arr (d := 0) (by simpa using Ot) (by simp only [S]; omega) (by simp)
  have input : Spec.Rsa.bytesAt v₄.mem (byteAddr (g.args (2 * i))) L =
      Spec.Rsa.bytesAt s.mem (byteAddr (g.args (2 * i))) L := by rw [m₄]
  have padding : ∀ k, L ≤ k → k < 4 * kw (g.args 1).toNat →
      t.mem (off g.base (arr (kw (g.args 1).toNat) j) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_, m₄]
    · exact byte_zero_of_val32 zero (by omega)
    · intro i hi he
      rw [byteAddr_add (by omega), dstAddr] at he
      have e := congrArg (fun a => (a - off g.base (arr (kw (g.args 1).toNat) j)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64)] at e
      omega
  have value := I.os2ip fit (by omega : dst.toNat + L ≤ 2 ^ 32)
  rw [dstAddr, input] at value
  change val32 t.mem g.base (arr (kw (g.args 1).toNat) j) (kw (g.args 1).toNat) = _
  rw [← read_eq_val32]
  have ext := val32_zero_extension t.mem (off g.base (arr (kw (g.args 1).toNat) j)) (n := kw (g.args 1).toNat)
    Lw (by intro k hk hkn; exact padding k hk hkn)
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

end VG.Proof.Rsa.X86.KeyCheck
