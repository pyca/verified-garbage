module

public import VerifiedGarbage.Proof.Rsa.X86.RvInputs
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

/-! # Importing one recovery input into its zeroed workspace array

`load_ok` reverses an input's bytes into its zeroed narrow array, all `w + 2`
of its words, so that a wide array's number is the input too.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86 (reverseBytes)
open VG.Impl.Rsa.X86.KeyRt (Lay arrPtr)
open VG.Impl.Rsa.X86.Recover (nArr width)
open VG.Impl.Rsa.X86.Keys (hdr)
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S)
open VG.Proof.Rsa.X86.KeyRt

theorem load_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (i : Fin 3) {j : Nat}
    (hj : j < nArr) (zero : val32 s.mem g.B (arr g.toGeo.w j) (g.toGeo.w + 2) = 0) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.load VG.Impl.Rsa.X86.RecoverRt.nar (4 + 2 * i.val) j) s fun t =>
      Inputs g t ∧ Keep g.B g.toGeo.w [j] [] s.mem t.mem ∧
      val32 t.mem g.B (arr g.toGeo.w j) (g.toGeo.w + 2) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (g.buffer (4 + 2 * i.val)).base (g.buffer (4 + 2 * i.val)).len) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have kn := kw_nar g.n
  change val32 s.mem g.B (arr (width g.n) j) (width g.n + 2) = 0 at zero
  change WP isa _ s fun t => Inputs g t ∧ Keep g.B (width g.n) [j] [] s.mem t.mem ∧
    val32 t.mem g.B (arr (width g.n) j) (width g.n + 2) = _ ∧ _
  rw [← kn] at zero ⊢
  have r := h.rt len
  have positive := h.inputPositive i
  have bound := h.inputBound i
  have sourceFit := h.inputFit i
  have sourceRead := h.inputRead i
  have apart := h.inputApart i ⟨g.B, g.Z⟩ (by simp [CallGeometry.writes])
  have nw := r.ws.workspace.nowrap
  have fits := r.ws.arr_fit hj
  simp only [S] at fits
  have up := h.upper
  have kwEq : kw (8 * g.n + 8) = 2 * g.n + 2 := kw_nar g.n
  simp only [CallGeometry.buffer] at positive bound sourceFit sourceRead apart ⊢
  generalize hL : (g.args (4 + 2 * i.val + 1)).toNat = L at positive bound sourceFit sourceRead apart ⊢
  have srcLen : L < 2 ^ 32 := by omega
  have Lw : L ≤ 4 * (kw (8 * g.n + 8) + 2) := by omega
  unfold VG.Impl.Rsa.X86.KeyRt.load
  simp only [List.cons_append, List.nil_append]
  have a₀ := h.arguments (4 + 2 * i.val) (by omega)
  have a₁ := h.arguments (4 + 2 * i.val + 1) (by omega)
  refine WP.seq (wp_movS a₀.readSrc fun u₁ U₁ _ => ?_)
  have h₁ := h.after U₁.keeps (by decide) (by decide) (by rw [U₁.mem]; exact Frame.refl _ _)
  refine wp_movS (h₁.arguments (4 + 2 * i.val + 1) (by omega)).readSrc fun u₂ U₂ _ => ?_
  have K₂ : Keeps [.esi, .ecx] s u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have m₂ : u₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  have r₂ := r.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc r₂) r₂.lenLe r₂.edi (by decide) (by decide) (by omega) fun v Kv mv pv _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  let dst := v.gpr .ebx
  have dstAddr : byteAddr dst = off g.B (arr (kw (8 * g.n + 8)) j) :=
    VG.Proof.Bignum.X86.PublicRt.byteAddr_ptr pv (by omega)
  have dstNat : dst.toNat = g.B.toNat + arr (kw (8 * g.n + 8)) j := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega)]
  have K₄ : Keeps [.ebx, .ecx, .edx, .esi] v v₄ :=
    (u₃.keeps.mono (by decide)).trans (u₄.keeps.mono (by decide))
  have m₄ : v₄.mem = s.mem := by rw [u₄.mem, u₃.mem, mv, m₂]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have ebx₄ : v₄.gpr .ebx = dst := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide)]
  have esi₄ : v₄.gpr .esi = g.args (4 + 2 * i.val) + BitVec.ofNat 32 (L - 1) := by
    have ecx₂ : v.gpr .ecx = BitVec.ofNat 32 L := by
      rw [Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [u₄.gpr, u₃.gpr, ecx₂, Kv.1 _ (by decide), U₂.other _ (by decide), U₁.gpr]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ :=
    (K₂.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  have vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (g.args (4 + 2 * i.val))) L := by
    rw [keep.2.1, keep.2.2]; exact sourceRead
  have vw : InRegions v₄.wr (byteAddr dst) L := by
    rw [keep.2.2, dstAddr]; exact r.ws.workspace.write (by omega)
  have hsub : Region.Sub ⟨off g.B (arr (kw (8 * g.n + 8)) j), L⟩ ⟨g.B, g.Z⟩ := by
    have := Offset.sub g.B (d := arr (kw (8 * g.n + 8)) j) (n := L) (e := 0) (k := g.Z) (Nat.zero_le _)
      (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have apart' : Region.Disjoint ⟨byteAddr (g.args (4 + 2 * i.val)), L⟩ ⟨g.B, g.Z⟩ := apart
  have hd : Region.Disjoint ⟨byteAddr (g.args (4 + 2 * i.val)), L⟩ ⟨off g.B (arr (kw (8 * g.n + 8)) j), L⟩ :=
    apart'.sub_right hsub
  have fit : (g.args (4 + 2 * i.val)).toNat + L ≤ 2 ^ 32 := sourceFit
  have ctx := reverseCtx_of_regions v₄ (g.args (4 + 2 * i.val)) dst srcLen fit (by omega) vr vw
    (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v₄ ctx (by omega) esi₄ ebx₄ ecx₄) fun t I => ?_
  have Ot : Outside g.B (arr (kw (8 * g.n + 8)) j) (4 * (kw (8 * g.n + 8) + 2)) v₄.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    have ek : ofs g.B a = arr (kw (8 * g.n + 8)) j + k := by
      rw [he, byteAddr_add (by omega), dstAddr]
      exact ofs_off g.B (by omega)
    omega
  have O : Outside g.B 0 g.Z s.mem t.mem := by
    rw [← m₄]; exact Ot.mono (Nat.zero_le _) (by omega)
  have keepT : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := keep.trans (I.rest.mono (by decide))
  refine ⟨h.after keepT (by decide) (by decide) (h.scratchFrame (by
    rw [← m₄]
    have : hdr ≤ arr (kw (8 * g.n + 8)) j := Nat.le_add_right _ _
    exact Ot.mono (by unfold hdr at this; omega) (by omega))), ?_, ?_, keepT⟩
  · rw [← m₄]; exact Keep.of_arr (d := 0) (by simpa using Ot) (by simp only [S]; omega) (by simp)
  have input : Spec.Rsa.bytesAt v₄.mem (byteAddr (g.args (4 + 2 * i.val))) L =
      Spec.Rsa.bytesAt s.mem (byteAddr (g.args (4 + 2 * i.val))) L := by rw [m₄]
  have padding : ∀ k, L ≤ k → k < 4 * (kw (8 * g.n + 8) + 2) →
      t.mem (off g.B (arr (kw (8 * g.n + 8)) j) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_, m₄]
    · exact byte_zero_of_val32 zero (by omega)
    · intro i hi he
      rw [byteAddr_add (by omega), dstAddr] at he
      have e := congrArg (fun a => (a - off g.B (arr (kw (8 * g.n + 8)) j)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64)] at e
      omega
  have value := I.os2ip fit (by omega : dst.toNat + L ≤ 2 ^ 32)
  rw [dstAddr, input] at value
  rw [← read_eq_val32]
  have ext := val32_zero_extension t.mem (off g.B (arr (kw (8 * g.n + 8)) j)) (n := kw (8 * g.n + 8) + 2)
    Lw (by intro k hk hkn; exact padding k hk hkn)
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

end VG.Proof.Rsa.X86.Recover
