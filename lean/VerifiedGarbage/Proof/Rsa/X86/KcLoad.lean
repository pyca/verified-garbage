module

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

/-! ### `Rsa.X86.KcFrames`, which this module and modules that import it used -/

section

/-! # Scratch frames preserve CRT input bytes and saved registers -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

theorem Inputs.keepBody {g : CallGeometry} {s : State} {m : Mem} {js ds : List Nat}
    (h : Inputs g s) (keep : Keep g.base (2 * g.n) js ds s.mem m)
    (hj : ∀ j ∈ js, j < nArr) (hd : ∀ d ∈ ds, 16 ≤ d ∧ d + 4 ≤ hdr) :
    Outside g.base 16 (g.size - 16) s.mem m := by
  have header := h.ws.hdr_le
  intro a ha
  apply keep a
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, jmem, rfl⟩ | ⟨d, dmem, rfl⟩
  · have bound := h.ws.arr_fit (hj j jmem)
    have lower : hdr ≤ arr (2 * g.n) j := Nat.le_add_right _ _
    dsimp only
    unfold hdr at header lower
    omega_using [ha, bound, lower]
  · have bound := hd d dmem
    dsimp only
    unfold hdr at header bound
    omega_using [header, ha, bound]

def inputBytes (g : CallGeometry) (m : Mem) (i : Nat) : List Byte :=
  Spec.Rsa.bytesAt m (g.buffer (2 * i)).base (g.buffer (2 * i)).len

theorem Inputs.inputFrame {g : CallGeometry} {s : State} {m : Mem} (h : Inputs g s)
    (frame : Outside g.base 0 g.size s.mem m) (i : Nat) (hi : 2 * i < scratchArg g.full) : inputBytes g m i = inputBytes g s.mem i := by
  exact scratch_bytes frame (by have := h.inputBound i hi; have := h.upper; omega_arith)
    (h.inputApart i hi _ (by simp [CallGeometry.writes]))

end VG.Proof.Rsa.X86.KeyCheck

end

end

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
  obtain f := outside_frame frame (by omega_using [fit])
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
  · rw [← len.scratch]; exact h.arguments (scratchArg g.full) (by omega_using [])

theorem load_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (i : Nat)
    (hi : 2 * i < scratchArg g.full) {j : Nat}
    (hj : j < nArr) (zero : num s.mem g.base (kw (g.args 1).toNat) j = 0) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.load (VG.Impl.Rsa.X86.KeyCheckRt.lay g.full) (2 * i) j) s fun t =>
      Inputs g t ∧ Keep g.base (kw (g.args 1).toNat) [j] [] s.mem t.mem ∧
      num t.mem g.base (kw (g.args 1).toNat) j =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (g.buffer (2 * i)).base (g.buffer (2 * i)).len) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain r := inputsRt h len
  obtain positive := h.inputPositive i hi
  obtain bound := h.inputBound i hi
  obtain sourceFit := h.inputFit i hi
  obtain sourceRead := h.inputRead i hi
  obtain apart := h.inputApart i hi ⟨g.base, g.size⟩ (by simp [CallGeometry.writes])
  have nw := r.ws.workspace.nowrap
  obtain fits := r.ws.arr_fit hj
  have wd := len.width
  simp only [S] at fits
  have up := h.upper
  obtain kwEq : kw (g.args 1).toNat = 2 * g.n := by rw [wd]
  simp only [CallGeometry.buffer] at positive bound sourceFit sourceRead apart ⊢
  generalize hL : (g.args (2 * i + 1)).toNat = L at positive bound sourceFit sourceRead apart ⊢
  obtain srcLen : L < 2 ^ 32 := by omega_using [hL]
  obtain Lw : L ≤ 4 * kw (g.args 1).toNat := by omega_using [kwEq, bound]
  unfold VG.Impl.Rsa.X86.KeyRt.load
  simp only [List.cons_append, List.nil_append]
  obtain a₀ := h.arguments (2 * i) (by omega_using [hi])
  obtain a₁ := h.arguments (2 * i + 1) (by omega_using [hi])
  refine WP.seq (wp_movS a₀.readSrc fun u₁ U₁ _ => ?_)
  obtain h₁ := h.after U₁.keeps (by decide) (by decide) (by rw [U₁.mem]; exact Frame.refl _ _)
  refine wp_movS (h₁.arguments (2 * i + 1) (by omega_using [hi])).readSrc fun u₂ U₂ _ => ?_
  obtain K₂ : Keeps [.esi, .ecx] s u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  obtain m₂ : u₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  obtain r₂ := r.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc r₂) r₂.lenLe r₂.edi (by decide) (by decide) (by omega_using [nw, fits]) fun v Kv mv pv _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  let dst := v.gpr .ebx
  obtain dstAddr : byteAddr dst = off g.base (arr (kw (g.args 1).toNat) j) :=
    VG.Proof.Bignum.X86.PublicRt.byteAddr_ptr pv (by omega_using [nw, fits])
  obtain dstNat : dst.toNat = g.base.toNat + arr (kw (g.args 1).toNat) j := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega_using [nw, fits])]
  obtain K₄ : Keeps [.ebx, .ecx, .edx, .esi] v v₄ :=
    (u₃.keeps.mono (by decide)).trans (u₄.keeps.mono (by decide))
  obtain m₄ : v₄.mem = s.mem := by rw [u₄.mem, u₃.mem, mv, m₂]
  obtain ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  obtain ebx₄ : v₄.gpr .ebx = dst := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide)]
  obtain esi₄ : v₄.gpr .esi = g.args (2 * i) + BitVec.ofNat 32 (L - 1) := by
    obtain ecx₂ : v.gpr .ecx = BitVec.ofNat 32 L := by
      rw [Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [u₄.gpr, u₃.gpr, ecx₂, Kv.1 _ (by decide), U₂.other _ (by decide), U₁.gpr]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [positive])]
  obtain keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ :=
    (K₂.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  obtain vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (g.args (2 * i))) L := by
    rw [keep.2.1, keep.2.2]; exact sourceRead
  obtain vw : InRegions v₄.wr (byteAddr dst) L := by
    rw [keep.2.2, dstAddr]; exact r.ws.workspace.write (by omega_using [fits, Lw])
  obtain hsub : Region.Sub ⟨off g.base (arr (kw (g.args 1).toNat) j), L⟩ ⟨g.base, g.size⟩ := by
    have := Offset.sub g.base (d := arr (kw (g.args 1).toNat) j) (n := L) (e := 0) (k := g.size) (Nat.zero_le _)
      (by omega_using [fits, Lw])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have apart' : Region.Disjoint ⟨byteAddr (g.args (2 * i)), L⟩ ⟨g.base, g.size⟩ := apart
  obtain hd : Region.Disjoint ⟨byteAddr (g.args (2 * i)), L⟩ ⟨off g.base (arr (kw (g.args 1).toNat) j), L⟩ :=
    apart'.sub_right hsub
  have fit : (g.args (2 * i)).toNat + L ≤ 2 ^ 32 := sourceFit
  obtain ctx := reverseCtx_of_regions v₄ (g.args (2 * i)) dst srcLen fit (by omega_arith) vr vw
    (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v₄ ctx (by omega_using [positive]) esi₄ ebx₄ ecx₄) fun t I => ?_
  obtain Ot : Outside g.base (arr (kw (g.args 1).toNat) j) (4 * kw (g.args 1).toNat) v₄.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    obtain ek : ofs g.base a = arr (kw (g.args 1).toNat) j + k := by
      rw [he, byteAddr_add (by omega_using [nw, fits, Lw, dstNat, hk]), dstAddr]
      exact ofs_off g.base (by omega_arith)
    omega_arith
  obtain O : Outside g.base 0 g.size s.mem t.mem := by
    rw [← m₄]; exact Ot.mono (Nat.zero_le _) (by omega_using [fits])
  obtain keepT : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := keep.trans (I.rest.mono (by decide))
  refine ⟨h.after keepT (by decide) (by decide) (h.scratchFrame O), ?_, ?_, keepT⟩
  · rw [← m₄]; exact Keep.of_arr (d := 0) (by simpa using Ot) (by simp only [S]; omega_using []) (by simp)
  obtain input : Spec.Rsa.bytesAt v₄.mem (byteAddr (g.args (2 * i))) L =
      Spec.Rsa.bytesAt s.mem (byteAddr (g.args (2 * i))) L := by rw [m₄]
  obtain padding : ∀ k, L ≤ k → k < 4 * kw (g.args 1).toNat →
      t.mem (off g.base (arr (kw (g.args 1).toNat) j) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_, m₄]
    · exact byte_zero_of_val32 zero (by omega_using [hkn])
    · intro i hi he
      rw [byteAddr_add (by omega_using [nw, fits, Lw, dstNat, hi]), dstAddr] at he
      obtain e := congrArg (fun a => (a - off g.base (arr (kw (g.args 1).toNat) j)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega_arith : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega_using [hL, hi] : i < 2 ^ 64)] at e
      omega_arith
  obtain value := I.os2ip fit (by omega_arith : dst.toNat + L ≤ 2 ^ 32)
  rw [dstAddr, input] at value
  change val32 t.mem g.base (arr (kw (g.args 1).toNat) j) (kw (g.args 1).toNat) = _
  rw [← read_eq_val32]
  obtain ext := val32_zero_extension t.mem (off g.base (arr (kw (g.args 1).toNat) j)) (n := kw (g.args 1).toNat)
    Lw (by intro k hk hkn; exact padding k hk hkn)
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

end VG.Proof.Rsa.X86.KeyCheck
