module

public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Core
public import VerifiedGarbage.Proof.Rsa.X86.CvFrames
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
import VerifiedGarbage.Proof.Bignum.X86.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.InvParts

/-! # CRT parameter calculation at a run-time width: the inputs

`Inputs.rt`: the arrays at the width of the modulus's length, argument 7.
`load_ok` reverses an input's bytes into its zeroed array, and `loads_ok`
zeroes the arrays and loads the four inputs, the state `core_ok` starts
from.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86 (reverseBytes)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr seqs)
open VG.Impl.Rsa.X86.KeyRt (Lay arrPtr)
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr inputArgs)
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot wp_seqs_cons)
open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.CrtValues (CallGeometry Inputs inputBytes)

/-- The lengths, and the working space argument at the working space. -/
structure Lengths (g : CallGeometry) : Prop where
  lower : 64 ≤ (g.args 7).toNat
  upper : (g.args 7).toNat ≤ 1024
  width : g.n = Spec.Rsa.modulusWords (g.args 7).toNat
  pSmall : (g.args 9).toNat < (g.args 7).toNat
  qSmall : (g.args 11).toNat < (g.args 7).toNat
  dpLen : g.args 1 = g.args 9
  dqLen : g.args 3 = g.args 11
  qiLen : g.args 5 = g.args 9
  scratch : g.args 14 = BitVec.ofNat 32 g.base.toNat

theorem scratchFrame {g : CallGeometry} {s : State} {m : Mem} (h : Inputs g s)
    (frame : Outside g.base 0 g.size s.mem m) : Frame g.writes s.mem m := by
  have fit := h.ws.workspace.nowrap
  have f := outside_frame frame (by omega)
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    f.mono (rs' := g.writes) (by simp [CallGeometry.writes, off])

/-- The arrays at the width of the modulus's length. -/
theorem inputsRt {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    RtWs lay s g.base g.size (g.args 7).toNat nArr := by
  have ws := h.ws
  rw [len.width] at ws
  refine ⟨ws, ?_, ?_, len.upper, by decide⟩
  · have a := h.arguments 7 (by decide)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← len.scratch]; exact h.arguments 14 (by decide)

theorem load_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (i : Fin 4) {j : Nat}
    (hj : j < nArr) (zero : num s.mem g.base (kw (g.args 7).toNat) j = 0) :
    WP isa (load (6 + 2 * i.val) j) s fun t =>
      Inputs g t ∧ Keep g.base (kw (g.args 7).toNat) [j] [] s.mem t.mem ∧
      num t.mem g.base (kw (g.args 7).toNat) j =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (g.buffer (6 + 2 * i.val)).base (g.buffer (6 + 2 * i.val)).len) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have r := inputsRt h len
  have positive := h.inputPositive i
  have bound := h.inputBound i
  have sourceFit := h.inputFit i
  have sourceRead := h.inputRead i
  have apart := h.inputApart i ⟨g.base, g.size⟩ (by simp [CallGeometry.writes])
  have nw := r.ws.workspace.nowrap
  have fits := r.ws.arr_fit hj
  have wd := len.width
  simp only [S] at fits
  have up := h.upper
  have kwEq : kw (g.args 7).toNat = 2 * g.n := by rw [wd]
  simp only [CallGeometry.buffer] at positive bound sourceFit sourceRead apart ⊢
  generalize hL : (g.args (6 + 2 * i.val + 1)).toNat = L at positive bound sourceFit sourceRead apart ⊢
  have srcLen : L < 2 ^ 32 := by omega
  have Lw : L ≤ 4 * kw (g.args 7).toNat := by omega
  unfold load inputArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_movS (h.arguments _ (by omega)).readSrc fun u₁ U₁ _ => ?_)
  have h₁ := h.after U₁.keeps (by decide) (by decide) (by rw [U₁.mem]; exact Frame.refl _ _)
  refine wp_movS (h₁.arguments _ (by omega)).readSrc fun u₂ U₂ _ => ?_
  have K₂ : Keeps [.esi, .ecx] s u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have m₂ : u₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  have r₂ := r.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc r₂) r₂.lenLe r₂.edi (by decide) (by decide) (by omega) fun v Kv mv pv _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  let dst := v.gpr .ebx
  have dstAddr : byteAddr dst = off g.base (arr (kw (g.args 7).toNat) j) :=
    VG.Proof.Bignum.X86.PublicRt.byteAddr_ptr pv (by omega)
  have dstNat : dst.toNat = g.base.toNat + arr (kw (g.args 7).toNat) j := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega)]
  have K₄ : Keeps [.ebx, .ecx, .edx, .esi] v v₄ :=
    (u₃.keeps.mono (by decide)).trans (u₄.keeps.mono (by decide))
  have m₄ : v₄.mem = s.mem := by rw [u₄.mem, u₃.mem, mv, m₂]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have ebx₄ : v₄.gpr .ebx = dst := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide)]
  have esi₄ : v₄.gpr .esi = g.args (6 + 2 * i.val) + BitVec.ofNat 32 (L - 1) := by
    have ecx₂ : v.gpr .ecx = BitVec.ofNat 32 L := by
      rw [Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [u₄.gpr, u₃.gpr, ecx₂, Kv.1 _ (by decide), U₂.other _ (by decide), U₁.gpr]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ :=
    (K₂.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  have vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (g.args (6 + 2 * i.val))) L := by
    rw [keep.2.1, keep.2.2]; exact sourceRead
  have vw : InRegions v₄.wr (byteAddr dst) L := by
    rw [keep.2.2, dstAddr]; exact r.ws.workspace.write (by omega)
  have hsub : Region.Sub ⟨off g.base (arr (kw (g.args 7).toNat) j), L⟩ ⟨g.base, g.size⟩ := by
    have := Offset.sub g.base (d := arr (kw (g.args 7).toNat) j) (n := L) (e := 0) (k := g.size) (Nat.zero_le _)
      (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have apart' : Region.Disjoint ⟨byteAddr (g.args (6 + 2 * i.val)), L⟩ ⟨g.base, g.size⟩ := apart
  have hd : Region.Disjoint ⟨byteAddr (g.args (6 + 2 * i.val)), L⟩ ⟨off g.base (arr (kw (g.args 7).toNat) j), L⟩ :=
    apart'.sub_right hsub
  have fit : (g.args (6 + 2 * i.val)).toNat + L ≤ 2 ^ 32 := sourceFit
  have ctx := reverseCtx_of_regions v₄ (g.args (6 + 2 * i.val)) dst srcLen fit (by omega) vr vw
    (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v₄ ctx (by omega) esi₄ ebx₄ ecx₄) fun t I => ?_
  have Ot : Outside g.base (arr (kw (g.args 7).toNat) j) (4 * kw (g.args 7).toNat) v₄.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    have ek : ofs g.base a = arr (kw (g.args 7).toNat) j + k := by
      rw [he, byteAddr_add (by omega), dstAddr]
      exact ofs_off g.base (by omega)
    omega
  have O : Outside g.base 0 g.size s.mem t.mem := by
    rw [← m₄]; exact Ot.mono (Nat.zero_le _) (by omega)
  have keepT : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := keep.trans (I.rest.mono (by decide))
  refine ⟨h.after keepT (by decide) (by decide) (scratchFrame h O), ?_, ?_, keepT⟩
  · rw [← m₄]; exact Keep.of_arr (d := 0) (by simpa using Ot) (by simp only [S]; omega) (by simp)
  have input : Spec.Rsa.bytesAt v₄.mem (byteAddr (g.args (6 + 2 * i.val))) L =
      Spec.Rsa.bytesAt s.mem (byteAddr (g.args (6 + 2 * i.val))) L := by rw [m₄]
  have padding : ∀ k, L ≤ k → k < 4 * kw (g.args 7).toNat →
      t.mem (off g.base (arr (kw (g.args 7).toNat) j) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_, m₄]
    · exact byte_zero_of_val32 zero (by omega)
    · intro i hi he
      rw [byteAddr_add (by omega), dstAddr] at he
      have e := congrArg (fun a => (a - off g.base (arr (kw (g.args 7).toNat) j)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64)] at e
      omega
  have value := I.os2ip fit (by omega : dst.toNat + L ≤ 2 ^ 32)
  rw [dstAddr, input] at value
  change val32 t.mem g.base (arr (kw (g.args 7).toNat) j) (kw (g.args 7).toNat) = _
  rw [← read_eq_val32]
  have ext := val32_zero_extension t.mem (off g.base (arr (kw (g.args 7).toNat) j)) (n := kw (g.args 7).toNat)
    Lw (by intro k hk hkn; exact padding k hk hkn)
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

def arithmeticGeometry (g : CallGeometry) (m : Mem) : Geometry :=
  ⟨g.base, g.size, Spec.Rsa.os2ip (inputBytes g m 1), Spec.Rsa.os2ip (inputBytes g m 2),
    Spec.Rsa.os2ip (inputBytes g m 3), Spec.Rsa.os2ip (inputBytes g m 0)⟩

theorem loads_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa loads s fun t => Inputs g t ∧ Start (arithmeticGeometry g s.mem) (g.args 7).toNat t ∧
      Outside g.base 16 (g.size - 16) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have r := inputsRt h len
  have header := r.ws.hdr_le
  have fits := r.ws.fits
  have nw := r.ws.workspace.nowrap
  have fit := fun j (hj : j < nArr) => r.ws.fit64 (j := j) hj
  have kwEq : kw (g.args 7).toNat = 2 * g.n := by rw [len.width]
  unfold loads
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroArrays_ok r (n := nArr) (by decide) (by decide)) fun z ⟨rz, oz, zeros, kz⟩ => ?_
  have a0 : arr (kw (g.args 7).toNat) 0 = hdr := by simp [arr]
  have fitsN : hdr + 4 * (nArr * (kw (g.args 7).toNat + 2)) ≤ g.size := by
    simp only [arr, S] at fits; rw [Nat.mul_left_comm] at fits; exact fits
  rw [a0] at oz
  have Oz : Outside g.base 0 g.size s.mem z.mem := oz.mono (Nat.zero_le _) (by omega)
  have Bz : Outside g.base 16 (g.size - 16) s.mem z.mem := oz.mono (by unfold hdr; omega) (by unfold hdr at *; omega)
  have hz := h.after (kz.mono (rs' := [.eax, .ecx, .edx, .ebp]) (by decide)) (by decide) (by decide) (scratchFrame h Oz)
  have zero : ∀ j < nArr, num z.mem g.base (kw (g.args 7).toNat) j = 0 := fun j hj => by
    have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zeros j hj) (a := 0) (c := kw (g.args 7).toNat) (by omega)
    simpa only [Nat.mul_zero, Nat.add_zero] using part
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok hz len 0 (j := aDQ) (by decide) (zero _ (by decide))) fun u ⟨hu, ku, vu, ru⟩ => ?_
  have ru' := inputsRt hu len
  have Ou := keep_outside ru'.ws ku (by simp; decide) (by simp)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok hu len 1 (j := aP) (by decide)
    (by rw [ku.num (by decide) (by simp) (fit _ (by decide))]; exact zero _ (by decide))) fun v ⟨hv, kv, vv, rv⟩ => ?_
  have Ov := keep_outside (inputsRt hv len).ws kv (by simp; decide) (by simp)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok hv len 2 (j := aQ) (by decide)
    (by rw [kv.num (by decide) (by simp) (fit _ (by decide)), ku.num (by decide) (by simp) (fit _ (by decide))]
        exact zero _ (by decide))) fun x ⟨hx, kx, vx, rx⟩ => ?_
  have Ox := keep_outside (inputsRt hx len).ws kx (by simp; decide) (by simp)
  refine WP.mono (load_ok hx len 3 (j := aD) (by decide)
    (by rw [kx.num (by decide) (by simp) (fit _ (by decide)), kv.num (by decide) (by simp) (fit _ (by decide)),
          ku.num (by decide) (by simp) (fit _ (by decide))]
        exact zero _ (by decide))) fun t ⟨ht, kt, vt, rt⟩ => ?_
  have K : Keep g.base (kw (g.args 7).toNat) [aDQ, aP, aQ, aD] [] z.mem t.mem :=
    ku.mono.trans (kv.mono.trans (kx.mono.trans kt.mono))
  have R : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    (kz.mono (by decide)).trans (ru.trans (rv.trans (rx.trans rt)))
  have K' : Keep g.base (2 * g.n) [aDQ, aP, aQ, aD] [] z.mem t.mem := by rw [← kwEq]; exact K
  have body := hz.keepBody K' (by decide) (by simp)
  refine ⟨ht, ?_, Bz.trans body, R⟩
  refine ⟨inputsRt ht len, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change num t.mem g.base (kw (g.args 7).toNat) aDQ = Spec.Rsa.os2ip (inputBytes g s.mem 0)
    rw [kt.num (by decide) (by simp) (fit _ (by decide)), kx.num (by decide) (by simp) (fit _ (by decide)),
      kv.num (by decide) (by simp) (fit _ (by decide)), vu]
    change Spec.Rsa.os2ip (inputBytes g z.mem 0) = _
    rw [h.inputFrame Oz]
  · change num t.mem g.base (kw (g.args 7).toNat) aP = Spec.Rsa.os2ip (inputBytes g s.mem 1)
    rw [kt.num (by decide) (by simp) (fit _ (by decide)), kx.num (by decide) (by simp) (fit _ (by decide)), vv]
    change Spec.Rsa.os2ip (inputBytes g u.mem 1) = _
    rw [h.inputFrame (Oz.trans Ou)]
  · change num t.mem g.base (kw (g.args 7).toNat) aQ = Spec.Rsa.os2ip (inputBytes g s.mem 2)
    rw [kt.num (by decide) (by simp) (fit _ (by decide)), vx]
    change Spec.Rsa.os2ip (inputBytes g v.mem 2) = _
    rw [h.inputFrame ((Oz.trans Ou).trans Ov)]
  · change num t.mem g.base (kw (g.args 7).toNat) aD = Spec.Rsa.os2ip (inputBytes g s.mem 3)
    rw [vt]
    change Spec.Rsa.os2ip (inputBytes g x.mem 3) = _
    rw [h.inputFrame (((Oz.trans Ou).trans Ov).trans Ox)]
  · change w32 t.mem g.base (arr (kw (g.args 7).toNat) aDD + 4 * kw (g.args 7).toNat) = 0
    rw [K.word (by unfold S; omega) (by decide) (by simp) (fit _ (by decide))]
    have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zeros aDD (by decide))
      (a := kw (g.args 7).toNat) (c := 1) (by omega)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using part
  · intro j hj
    have jfit : j < nArr := by
      simp only [zeroC, List.mem_cons, List.not_mem_nil, or_false] at hj
      unfold nArr; omega
    have separate : ∀ k ∈ [aDQ, aP, aQ, aD], k ≠ j := by
      simp only [zeroC, List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [aDQ, aP, aQ, aD, List.mem_cons, List.not_mem_nil, or_false]
      omega
    change num t.mem g.base (kw (g.args 7).toNat) j = 0
    rw [K.num separate (by simp) (fit _ jfit)]
    exact zero j jfit

end VG.Proof.Rsa.X86.CrtValuesRt
