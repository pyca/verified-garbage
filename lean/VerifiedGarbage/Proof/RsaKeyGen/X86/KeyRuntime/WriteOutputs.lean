module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExport
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWriteArray
import VerifiedGarbage.Proof.Bignum.X86.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! ### `RsaKeyGen.X86.KeyRuntime.WriteArray`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.ContextWorkspace`, which this module and modules that import it used -/

section

/-! # Establish the three runtime widths from the retained cdecl arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Rsa.X86.KeyRt (kw RtWs)
open VG.Proof.Bignum.X86 (CallArgument)
open VG.Proof.RsaKeyGen.X86.Key (Environment)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

theorem context_workspace {E : Environment} {p : BitVec 32} {s : State}
    (v : E.Valid) (C : Context E.base E.size p E.argument s)
    (old : VG.Proof.Rsa.X86.Keys.Ws s E.base E.size E.n 32) : Ws s E.base E.size E.n 32 := by
  obtain ⟨lo, hi, nk, kp, ke, plen⟩ := v.widths
  have width : E.n % 4 = 0 := by omega_using [nk, ke]
  have resize (k : Nat) (positive : 0 < k) (small : k ≤ E.n) :
      VG.Proof.Rsa.X86.Keys.Ws s E.base E.size k 32 := by
    refine ⟨old.workspace, Nat.le_trans ?_ old.fits, positive, Nat.le_trans small old.wle⟩
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Proof.Rsa.X86.Keys.S
    omega_using [small]
  have wsValue : BitVec.ofNat 32 E.base.toNat = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    simp only [Environment.base, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    have bound := E.workspace.isLt
    omega_using []
  have wsArg : CallArgument s E.base E.size 20 (BitVec.ofNat 32 E.base.toNat) := by
    rw [wsValue]
    exact context_argument C (i := 16) (by decide)
  refine ⟨?_, ?_, ?_, width, ⟨lo, hi⟩, by rw [C.sp]; exact C.deep⟩
  · refine ⟨?_, ⟨2 * E.primeLength, by omega_using [hi, plen], ?_, context_argument C (i := 3) (by decide)⟩,
      wsArg, by omega_using [hi], by decide⟩
    · simpa only [kw_full width] using old
    · change kw (2 * E.primeLength) = kw (4 * E.n)
      rw [plen]
      congr 1
      omega_using []
  · refine ⟨?_, ⟨E.primeLength, by omega_using [hi, plen], ?_, context_argument C (i := 5) (by decide)⟩,
      wsArg, by omega_using [hi], by decide⟩
    · simpa only [kw_prime width] using resize (E.n / 2) (by omega_using [lo]) (by omega_using [])
    · change kw E.primeLength = kw (2 * E.n)
      rw [plen]
  · have kw8 : kw 8 = 2 := by decide
    refine ⟨?_, ⟨E.exponentLength, by have := v.exponentLength; omega_using [this], ?_,
      context_argument C (i := 15) (by decide)⟩, wsArg, by decide, by decide⟩
    · simpa only [kw8] using resize 2 (by decide) (by omega_using [lo])
    · have bounds := v.exponentLength
      change kw E.exponentLength = kw 8
      simp only [kw, Spec.Rsa.modulusWords]
      omega_using [bounds]

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.ContextFar`, which this module and modules that import it used -/

section

/-! # The cdecl arguments survive writes away from them, such as the key outputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

/-- `Context.keep` for writes to any regions apart from the arguments. -/
theorem Context.keepFar {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s t : State}
    {rs : List Reg} (C : Context base size p inputs s) (K : Keeps rs s t) {writes : List Region}
    (F : Frame writes s.mem t.mem) (far : ∀ r ∈ writes, (argsRegion p).Disjoint r)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) :
    Context base size p inputs t := by
  have spT : t.gpr .esp = p := (K.1 .esp esp).trans C.sp
  refine ⟨C.scratch.of_keeps K edi esp, C.header, spT, C.fit, C.separate, ?_, C.deep⟩
  intro i index
  have eaT : t.ea (arg i) = s.ea (arg i) := by
    change addr (t.gpr .esp) _ = addr (s.gpr .esp) _
    rw [K.1 .esp esp]
  have memory : t.mem.readW (s.ea (arg i)) 32 = s.mem.readW (s.ea (arg i)) 32 := by
    rw [C.address index]
    exact F.readW (r := argsRegion p)
      (Offset.contains_base _ (by change 4 * i + 4 ≤ 72; omega_using [index]) (by omega_using [index] : 4 * i < 2 ^ 64))
      far (by decide)
  have same : readSrc t (.mem (arg i)) = readSrc s (.mem (arg i)) := by
    show t.load32 (t.ea (arg i)) = s.load32 (s.ea (arg i))
    simp only [State.load32, eaT, K.2.1, K.2.2, memory]
  exact same.trans (C.read i index)

end VG.Proof.RsaKeyGen.X86.KeyArgs

end

end

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

/-- `writeArray j pointer length`, with the pointer and length from arguments `pointer` and `length`. -/
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
  obtain H := context_workspace valid C h
  obtain fits := h.arr_fit hj
  obtain fit64 := h.fit64 hj
  have head := h.hdr_le
  have nowrap := h.workspace.nowrap
  unfold S at fits fit64
  unfold writeArray arraySetup
  refine WP.seq (WP.seq (WP.mono (sel_ok H hj (by decide) hj (by decide)
    (by rw [mask]; cases accept <;> decide) (Or.inl nonzero)) fun u ⟨Hu, Ou, selected, Ku⟩ => ?_))
  obtain raw : Outside E.base (arr E.n j) (S E.n) s.mem u.mem := by
    intro a ha
    apply Ou a
    intro r hr
    change r ∈ [(arr E.n j, S E.n)] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact ha
  obtain ownFrame := VG.Proof.Bignum.outside_frame raw (by unfold S; exact fit64)
  obtain ownFar : (argsRegion sp).Disjoint ⟨off E.base (arr E.n j), S E.n⟩ :=
    C.separate.sub_right (Offset.sub_base E.base (by unfold S; exact fits))
  obtain Cu := C.keepFar Ku ownFrame (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact ownFar)
  obtain chosen : num u.mem E.base E.n j = if accept then num s.mem E.base E.n j else 0 := by
    rw [selected, mask, zero]
    cases accept <;> rfl
  obtain Pu := context_argument Cu (i := pointer) hp
  obtain Lu := context_argument Cu (i := length) hl
  simp only [List.cons_append, List.nil_append]
  refine wp_movS Pu.readSrc fun a A _ => ?_
  refine wp_movS (Lu.keep A.keeps (by decide) (by rw [A.mem]; exact Outside.refl _ _ _ _)).readSrc
    fun b Bb _ => ?_
  obtain Kab : Keeps [.ebx, .ecx] u b := (A.keeps.mono (by decide)).trans (Bb.keeps.mono (by decide))
  obtain mb : b.mem = u.mem := Bb.mem.trans A.mem
  obtain Hb := Hu.keep Kab (by rw [mb]; exact Outside.refl _ _ _ _)
  obtain ebx_b : b.gpr .ebx = p := by rw [Bb.other _ (by decide), A.gpr, pointerEq]
  obtain ecx_b : b.gpr .ecx = BitVec.ofNat 32 len := by rw [Bb.gpr, lengthEq]
  refine Hb.ptr_ok (arr j) (r := .esi) (t := .edx) (by decide) (by decide)
    (by change arr E.n j < _; omega_using [fits, nowrap]) fun c Kc mc Pc => ?_
  refine wp_addS rfl fun d D _ => wp_subS rfl fun e Ee _ => WP.block_nil ?_
  obtain Kce : Keeps [.esi] c e := (D.keeps.mono (by decide)).trans (Ee.keeps.mono (by decide))
  obtain me : e.mem = u.mem := by rw [Ee.mem, D.mem, mc, mb]
  obtain Kue : Keeps [.ebx, .ecx, .esi, .edx] u e :=
    ((Kab.mono (by decide)).trans (Kc.mono (by decide))).trans (Kce.mono (by decide))
  obtain Kse : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s e := (Ku.mono (by decide)).trans (Kue.mono (by decide))
  obtain ebx_e : e.gpr .ebx = p := by
    rw [Ee.other _ (by decide), D.other _ (by decide), Kc.1 _ (by decide), ebx_b]
  obtain ecx_e : e.gpr .ecx = BitVec.ofNat 32 len := by
    rw [Ee.other _ (by decide), D.other _ (by decide), Kc.1 _ (by decide), ecx_b]
  obtain ecx_c : c.gpr .ecx = BitVec.ofNat 32 len := by rw [Kc.1 _ (by decide), ecx_b]
  obtain srcNat : (c.gpr .esi).toNat = E.base.toNat + arr E.n j := by
    have P : (c.gpr .esi).toNat = (E.base.toNat + arr E.n j) % 2 ^ 32 := Pc
    rw [P, Nat.mod_eq_of_lt (by omega_using [fits, nowrap])]
  obtain lenSmall : len < 2 ^ 32 := by omega_using [bound, fits, nowrap]
  obtain esi_e : e.gpr .esi = c.gpr .esi + BitVec.ofNat 32 (len - 1) := by
    rw [Ee.gpr, D.gpr, ecx_c]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (1 : BitVec 32).toNat = 1 from rfl]
    have := (c.gpr .esi).isLt
    omega_using [positive]
  obtain source : byteAddr (c.gpr .esi) = off E.base (arr E.n j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [byteAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, srcNat]
    omega_using []
  obtain rd : e.rd ++ e.wr = s.rd ++ s.wr := by rw [Kse.2.1, Kse.2.2]
  refine WP.mono (VG.Proof.Bignum.X86.reverseBuffer_ok e (src := c.gpr .esi) (dst := p) positive
    (by omega_using [bound, fits, nowrap, srcNat]) fit lenSmall
    (by rw [rd, source]; exact h.workspace.read (by omega_using [bound, fits]))
    (by rw [Kse.2.2]; exact write)
    (by rw [source]; exact separate.sub_left (Offset.sub_base E.base (by omega_using [bound, fits])))
    ebx_e esi_e ecx_e)
    fun t ⟨V, F, _, Kt⟩ => ?_
  rw [source, me] at V
  rw [me] at F
  change Frame [⟨p.setWidth 64, len⟩] u.mem t.mem at F
  obtain all : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := Kse.trans (Kt.mono (by decide))
  obtain prefixValue : (u.mem.read (off E.base (arr E.n j)) len).toNat =
      num u.mem E.base E.n j % 2 ^ (8 * len) := by
    rw [VG.Proof.Bignum.read_prefix u.mem _ bound, BitVec.toNat_setWidth, VG.Proof.Bignum.read_eq_val32]
  refine ⟨h.rest all, Cu.keepFar ((Kue.mono (rs' := [.eax, .ebx, .ecx, .esi, .edx]) (by decide)).trans (Kt.mono (by decide))) F
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact far), ?_, ?_, ?_, ?_, all⟩
  · change Spec.Rsa.bytesAt t.mem (p.setWidth 64) len = _ at V
    rw [V, prefixValue, chosen]
  · exact (ownFrame.mono (by simp)).trans (F.mono (by simp))
  · intro d hd
    change w32 t.mem E.base d = w32 s.mem E.base d
    rw [VG.Proof.RsaKeyGen.X86.Key.output_word h separate F (by omega_using [head, hd])]
    exact Ou.slot hd (by simp)
  · intro k hk different
    rw [VG.Proof.RsaKeyGen.X86.Key.output_num h separate F hk]
    exact Ou.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact Ne.symm different)
      (by simp) (h.fit64 hk)

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The seven masked key outputs and the status, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (kOk kStatus outputIndex)
open VG.Proof.RsaKeyGen.X86.Key (Environment ExportProgress OutputInput portResult portFrame_global
  portFrame_other outputIndex_bound outputIndex_zero outputIndex_injective WrittenCore CoreOutcome)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)

/-- What the outputs need beyond `ExportProgress`: the arguments, and outputs apart from them. -/
structure OutputArgs (E : Environment) (sp : BitVec 32) (s : State) : Prop where
  valid : E.Valid
  context : Context E.base E.size sp E.argument s
  apart : ∀ i < 7, (argsRegion sp).Disjoint (E.outputs.region i)

theorem port_ok {E : Environment} {sp : BitVec 32} {m : Mem} {accept : Bool} {i : Nat} {s : State}
    (P : ExportProgress E.outputs m accept i s) (A : OutputArgs E sp s) (hi : i < 7) :
    WP isa (writePort i) s fun t =>
      ExportProgress E.outputs m accept (i + 1) t ∧ OutputArgs E sp t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have h := P.input
  refine WP.mono (writeArray_ok (p := E.outputs.pointer i) (len := E.outputs.length i) A.valid h.ws A.context
    (outputIndex_bound hi) (Ne.symm (outputIndex_zero hi)) (by omega_using [hi]) (by omega_using [hi]) rfl
    (by simp only [VG.Proof.RsaKeyGen.X86.Key.OutputGeometry.length, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl)
    (h.valid.lengthPositive i hi) (h.valid.lengthBound i hi) (h.valid.fit i hi)
    (h.writable i hi) (h.valid.scratchApart i hi) (A.apart i hi) P.zero accept P.mask)
    fun t ⟨ht, Ct, value, F, header, other, K⟩ => ?_
  refine ⟨⟨h.after ht K header, (other aZero (by decide) (outputIndex_zero hi)).trans P.zero,
    (header kOk (by decide)).trans P.mask, ?_, ?_, ?_⟩, ⟨A.valid, Ct, A.apart⟩,
    portFrame_global h hi F, K⟩
  · intro d hd
    exact (header d hd).trans (P.header d hd)
  · intro j lower upper
    exact (other (outputIndex j) (outputIndex_bound upper)
      (outputIndex_injective upper hi (by omega_using [lower]))).trans (P.pending j (by omega_using [lower]) upper)
  · intro j lower upper
    by_cases last : j = i
    · subst j
      unfold portResult
      rw [← P.pending i (Nat.le_refl _) hi]
      exact value
    · exact (portFrame_other h hi upper (by omega_using [last]) F).trans (P.done j (by omega_using [lower, last]) upper)

theorem ports_ok {E : Environment} {sp : BitVec 32} {m : Mem} {accept : Bool} {i count : Nat} {s : State}
    (P : ExportProgress E.outputs m accept i s) (A : OutputArgs E sp s) (bound : i + count ≤ 7) :
    WP isa (writePorts i count) s fun t =>
      ExportProgress E.outputs m accept (i + count) t ∧ OutputArgs E sp t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  induction count generalizing i s with
  | zero => exact WP.block_nil ⟨P, A, Frame.refl _ _, Keeps.refl _ _⟩
  | succ count ih =>
    unfold writePorts
    refine WP.seq (WP.mono (port_ok P A (by omega_using [bound])) fun u ⟨Pu, Au, Fu, Ku⟩ => ?_)
    refine WP.mono (ih Pu Au (by omega_using [bound])) fun t ⟨Pt, At, Ft, Kt⟩ => ?_
    have index : i + 1 + count = i + (count + 1) := by omega_using []
    rw [index] at Pt
    exact ⟨Pt, At, Fu.trans Ft, Ku.trans Kt⟩

theorem writeOutputs_ok {E : Environment} {sp : BitVec 32} {s : State} (h : OutputInput E.outputs s)
    (A : OutputArgs E sp s) (accept : Bool) (mask : slot s.mem E.base kOk = if accept then 1 else 0) :
    WP isa writeOutputs s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ (t.gpr .eax).toNat = slot s.mem E.base kStatus ∧
      (∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (E.outputs.region i).base (E.outputs.region i).len =
        portResult E.outputs s.mem accept i) ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have H := context_workspace A.valid A.context h.ws
  have fits := h.ws.arr_fit (j := aZero) (by decide)
  have fit64 := h.ws.fit64 (j := aZero) (by decide)
  unfold writeOutputs seqs
  refine WP.seq (WP.mono (zero_ok H .modulus (arr aZero) (by change arr E.n aZero + _ ≤ E.size; exact fits))
    fun u ⟨Hu, Ou, zero, Ku⟩ => ?_)
  change Outside E.base (arr E.n aZero) (S E.n) s.mem u.mem at Ou
  change val32 u.mem E.base (arr E.n aZero) (E.n + 2) = 0 at zero
  have clear : Keep E.base E.n [aZero] [] s.mem u.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ou) (by unfold S; omega_using []) (by simp)
  have header : ∀ d, d + 4 ≤ hdr → slot u.mem E.base d = slot s.mem E.base d :=
    fun d hd => clear.slot hd (by simp)
  have Pu : ExportProgress E.outputs s.mem accept 0 u := by
    refine ⟨h.after Hu.old Ku header, ?_, (header kOk (by decide)).trans mask, header, ?_, ?_⟩
    · change val32 u.mem E.base (arr E.n aZero) E.n = 0
      have Z := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 0) (c := E.n) (by omega_using [])
      simpa only [Nat.mul_zero, Nat.add_zero] using Z
    · intro i _ hi
      exact clear.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact outputIndex_zero hi)
        (by simp) (h.ws.fit64 (outputIndex_bound hi))
    · intro i hi
      omega_using [hi]
  have ownFrame := VG.Proof.Bignum.outside_frame Ou fit64
  have Fu : Frame E.outputs.writes s.mem u.mem := by
    apply ownFrame.sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨E.outputs.scratch, List.mem_cons_self, Offset.sub_base E.base fits⟩
  have Au : OutputArgs E sp u := ⟨A.valid, A.context.keepFar Ku ownFrame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact A.context.separate.sub_right (Offset.sub_base E.base fits)), A.apart⟩
  refine WP.seq (WP.mono (ports_ok Pu Au (by decide : 0 + 7 ≤ 7)) fun v ⟨Pv, _, Fv, Kv⟩ => ?_)
  have head := Pv.input.ws.hdr_le
  refine wp_movS (readSrc_sc Pv.input.ws.workspace (by unfold kStatus hdr at *; omega_using [head]))
    fun t T _ => WP.block_nil ?_
  refine ⟨Pv.input.ws.rest T.keeps, ?_, ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (T.keeps.mono (by decide)))⟩
  · rw [T.gpr]
    exact Pv.header kStatus (by decide)
  · intro i hi
    rw [T.mem]
    exact Pv.done i hi hi
  · rw [T.mem]
    exact Fu.trans Fv

theorem writeCore_ok {E : Environment} {sp : BitVec 32} {s : State} {e p q : Nat}
    (h : OutputInput E.outputs s) (A : OutputArgs E sp s) (result : CoreOutcome E.base E.n e p q s.mem) :
    WP isa writeOutputs s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ WrittenCore E.outputs e p q t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
  VG.Proof.RsaKeyGen.X86.Key.writeCore_of (g := E.outputs) (fun accept mask => writeOutputs_ok h A accept mask) result

end VG.Proof.RsaKeyGen.X86.KeyRuntime
