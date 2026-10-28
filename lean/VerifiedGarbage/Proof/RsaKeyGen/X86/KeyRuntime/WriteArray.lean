module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextFar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWriteArray
import VerifiedGarbage.Proof.Bignum.X86.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! # One masked key output, through the pointer and length arguments, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (kOk)
open VG.Proof.RsaKeyGen.X86.Key (Environment)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)
open VG.Proof.Bignum.X86 (byteAddr)

/-- `Key.writeArray_ok` with the pointer and length from arguments `pointer` and `length`. -/
theorem writeArray_ok {E : Environment} {sp : BitVec 32} {s : State} {j pointer length len : Nat}
    {p : BitVec 32} (valid : E.Valid) (h : VG.Proof.Rsa.X86.Keys.Ws s E.base E.size E.n 32)
    (C : Context E.base E.size sp E.argument s) (hj : j < 32) (nonzero : j ≠ aZero)
    (hp : pointer < 18) (hl : length < 18)
    (pointerEq : E.argument pointer = p) (lengthEq : E.argument length = BitVec.ofNat 32 len)
    (positive : 0 < len) (bound : len ≤ 4 * E.n)
    (fit : p.toNat + len ≤ 2 ^ 32) (write : InRegions s.wr (p.setWidth 64) len)
    (separate : Region.Disjoint ⟨E.base, E.size⟩ ⟨p.setWidth 64, len⟩)
    (far : (argsRegion sp).Disjoint ⟨p.setWidth 64, len⟩)
    (zero : num s.mem E.base E.n aZero = 0) (accept : Bool)
    (mask : slot s.mem E.base kOk = if accept then 1 else 0) :
    WP isa (writeArray j pointer length) s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ Context E.base E.size sp E.argument t ∧
      Spec.Rsa.bytesAt t.mem (p.setWidth 64) len =
        Spec.Rsa.i2osp ((if accept then num s.mem E.base E.n j else 0) % 2 ^ (8 * len)) len ∧
      Frame [⟨off E.base (arr E.n j), S E.n⟩, ⟨p.setWidth 64, len⟩] s.mem t.mem ∧
      (∀ d, d + 4 ≤ hdr → slot t.mem E.base d = slot s.mem E.base d) ∧
      (∀ k, k < 32 → k ≠ j → num t.mem E.base E.n k = num s.mem E.base E.n k) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have H := context_workspace valid C h
  have fits := h.arr_fit hj
  have fit64 := h.fit64 hj
  have head := h.hdr_le
  have nowrap := h.workspace.nowrap
  unfold S at fits fit64
  unfold writeArray arraySetup
  refine WP.seq (WP.seq (WP.mono (sel_ok H hj (by decide) hj (by decide)
    (by rw [mask]; cases accept <;> decide) (Or.inl nonzero)) fun u ⟨Hu, Ou, selected, Ku⟩ => ?_))
  have raw : Outside E.base (arr E.n j) (S E.n) s.mem u.mem := by
    intro a ha
    apply Ou a
    intro r hr
    change r ∈ [(arr E.n j, S E.n)] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact ha
  have ownFrame := VG.Proof.Bignum.outside_frame raw (by unfold S; exact fit64)
  have ownFar : (argsRegion sp).Disjoint ⟨off E.base (arr E.n j), S E.n⟩ :=
    C.separate.sub_right (Offset.sub_base E.base (by unfold S; exact fits))
  have Cu := C.keepFar Ku ownFrame (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact ownFar)
  have chosen : num u.mem E.base E.n j = if accept then num s.mem E.base E.n j else 0 := by
    rw [selected, mask, zero]
    cases accept <;> rfl
  have Pu := context_argument Cu (i := pointer) hp
  have Lu := context_argument Cu (i := length) hl
  simp only [List.cons_append, List.nil_append]
  refine wp_movS Pu.readSrc fun a A _ => ?_
  refine wp_movS (Lu.keep A.keeps (by decide) (by rw [A.mem]; exact Outside.refl _ _ _ _)).readSrc
    fun b Bb _ => ?_
  have Kab : Keeps [.ebx, .ecx] u b := (A.keeps.mono (by decide)).trans (Bb.keeps.mono (by decide))
  have mb : b.mem = u.mem := Bb.mem.trans A.mem
  have Hb := Hu.keep Kab (by rw [mb]; exact Outside.refl _ _ _ _)
  have ebx_b : b.gpr .ebx = p := by rw [Bb.other _ (by decide), A.gpr, pointerEq]
  have ecx_b : b.gpr .ecx = BitVec.ofNat 32 len := by rw [Bb.gpr, lengthEq]
  refine Hb.ptr_ok (arr j) (r := .esi) (t := .edx) (by decide) (by decide)
    (by change arr E.n j < _; omega) fun c Kc mc Pc => ?_
  refine wp_addS rfl fun d D _ => wp_subS rfl fun e Ee _ => WP.block_nil ?_
  have Kce : Keeps [.esi] c e := (D.keeps.mono (by decide)).trans (Ee.keeps.mono (by decide))
  have me : e.mem = u.mem := by rw [Ee.mem, D.mem, mc, mb]
  have Kue : Keeps [.ebx, .ecx, .esi, .edx] u e :=
    ((Kab.mono (by decide)).trans (Kc.mono (by decide))).trans (Kce.mono (by decide))
  have Kse : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s e := (Ku.mono (by decide)).trans (Kue.mono (by decide))
  have ebx_e : e.gpr .ebx = p := by
    rw [Ee.other _ (by decide), D.other _ (by decide), Kc.1 _ (by decide), ebx_b]
  have ecx_e : e.gpr .ecx = BitVec.ofNat 32 len := by
    rw [Ee.other _ (by decide), D.other _ (by decide), Kc.1 _ (by decide), ecx_b]
  have ecx_c : c.gpr .ecx = BitVec.ofNat 32 len := by rw [Kc.1 _ (by decide), ecx_b]
  have srcNat : (c.gpr .esi).toNat = E.base.toNat + arr E.n j := by
    have P : (c.gpr .esi).toNat = (E.base.toNat + arr E.n j) % 2 ^ 32 := Pc
    rw [P, Nat.mod_eq_of_lt (by omega)]
  have lenSmall : len < 2 ^ 32 := by omega
  have esi_e : e.gpr .esi = c.gpr .esi + BitVec.ofNat 32 (len - 1) := by
    rw [Ee.gpr, D.gpr, ecx_c]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (1 : BitVec 32).toNat = 1 from rfl]
    have := (c.gpr .esi).isLt
    omega
  have source : byteAddr (c.gpr .esi) = off E.base (arr E.n j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [byteAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, srcNat]
    omega
  have rd : e.rd ++ e.wr = s.rd ++ s.wr := by rw [Kse.2.1, Kse.2.2]
  refine WP.mono (VG.Proof.Bignum.X86.reverseBuffer_ok e (src := c.gpr .esi) (dst := p) positive
    (by omega) fit lenSmall
    (by rw [rd, source]; exact h.workspace.read (by omega))
    (by rw [Kse.2.2]; exact write)
    (by rw [source]; exact separate.sub_left (Offset.sub_base E.base (by omega)))
    ebx_e esi_e ecx_e)
    fun t ⟨V, F, _, Kt⟩ => ?_
  rw [source, me] at V
  rw [me] at F
  change Frame [⟨p.setWidth 64, len⟩] u.mem t.mem at F
  have all : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := Kse.trans (Kt.mono (by decide))
  have prefixValue : (u.mem.read (off E.base (arr E.n j)) len).toNat =
      num u.mem E.base E.n j % 2 ^ (8 * len) := by
    rw [VG.Proof.Bignum.read_prefix u.mem _ bound, BitVec.toNat_setWidth, VG.Proof.Bignum.read_eq_val32]
  refine ⟨h.rest all, Cu.keepFar ((Kue.mono (rs' := [.eax, .ebx, .ecx, .esi, .edx]) (by decide)).trans (Kt.mono (by decide))) F
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact far), ?_, ?_, ?_, ?_, all⟩
  · change Spec.Rsa.bytesAt t.mem (p.setWidth 64) len = _ at V
    rw [V, prefixValue, chosen]
  · exact (ownFrame.mono (by simp)).trans (F.mono (by simp))
  · intro d hd
    change w32 t.mem E.base d = w32 s.mem E.base d
    rw [VG.Proof.RsaKeyGen.X86.Key.output_word h separate F (by omega)]
    exact Ou.slot hd (by simp)
  · intro k hk different
    rw [VG.Proof.RsaKeyGen.X86.Key.output_num h separate F hk]
    exact Ou.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact Ne.symm different)
      (by simp) (h.fit64 hk)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
