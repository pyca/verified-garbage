module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Frame
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.ReverseEncoding
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.MulMod
import VerifiedGarbage.Proof.Rsa.RecoverProduct
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Dsa.Frame
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.MontContract
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.KeyBits32
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops

/-!
# `vg_rsa_recover_primes_det` on i686: the inputs, `d e` and the outputs

The inputs and their regions; `n`, `e` and `d` read into the
working space; the product `M = d e`; the factors written out under the mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

structure CallGeometry extends Geo

def CallGeometry.buffer (g : CallGeometry) (i : Nat) : Region :=
  ⟨byteAddr (g.args i), (g.args (i + 1)).toNat⟩

/-- What the call may write: the working space, the outputs, and the 40 bytes below `sp`, where the
calls of `vg_rsa_mont_mul_at` put their frames. -/
def CallGeometry.writes (g : CallGeometry) : List Region :=
  [⟨g.B, g.Z⟩, g.buffer 0, g.buffer 2, VG.X86.below g.sp 96]

/-- The modulus's length (argument 5), of the width the arrays have, and the working space argument
at the working space. -/
structure Lengths (g : CallGeometry) : Prop where
  lower : 64 ≤ (g.args 5).toNat
  upper : (g.args 5).toNat ≤ 1024
  width : g.n = Spec.Rsa.modulusWords (g.args 5).toNat
  scratch : g.args 10 = BitVec.ofNat 32 g.B.toNat
  bytes : g.Z = (g.args 11).toNat * 8
  pLen : g.args 1 = g.args 5
  qLen : g.args 3 = g.args 5

structure Inputs (g : CallGeometry) (s : State) : Prop where
  ws : Ws s g.B g.Z g.toGeo.w nArr
  lower : 8 ≤ g.n
  upper : g.n ≤ 128
  esp : s.gpr .esp = g.sp
  room : VG.Proof.Mont.X86.CallRoom g.sp g.B g.Z
  top : g.sp.toNat + 52 ≤ 2 ^ 32
  arguments : ∀ i, i < 12 → CallArgument s g.B g.Z i (g.args i)
  stackApart : ∀ i, i < 12 → ∀ r ∈ g.writes, Region.Disjoint ⟨stackAddress s i, 4⟩ r
  inputPositive : ∀ j : Fin 3, 0 < (g.buffer (4 + 2 * j.val)).len
  inputBound : ∀ j : Fin 3, (g.buffer (4 + 2 * j.val)).len ≤ 8 * g.n
  inputFit : ∀ j : Fin 3, (g.args (4 + 2 * j.val)).toNat + (g.buffer (4 + 2 * j.val)).len ≤ 2 ^ 32
  inputRead : ∀ j : Fin 3, InRegions (s.rd ++ s.wr) (g.buffer (4 + 2 * j.val)).base (g.buffer (4 + 2 * j.val)).len
  inputApart : ∀ j : Fin 3, ∀ r ∈ g.writes, (g.buffer (4 + 2 * j.val)).Disjoint r
  outputPositive : ∀ j : Fin 2, 0 < (g.buffer (2 * j.val)).len
  outputBound : ∀ j : Fin 2, (g.buffer (2 * j.val)).len ≤ 8 * g.n
  outputFit : ∀ j : Fin 2, (g.args (2 * j.val)).toNat + (g.buffer (2 * j.val)).len ≤ 2 ^ 32
  outputWrite : ∀ j : Fin 2, InRegions s.wr (g.buffer (2 * j.val)).base (g.buffer (2 * j.val)).len
  outputScratch : ∀ j : Fin 2, (g.buffer (2 * j.val)).Disjoint ⟨g.B, g.Z⟩
  outputSeparate : ∀ i j : Fin 2, i ≠ j → (g.buffer (2 * i.val)).Disjoint (g.buffer (2 * j.val))
  wrEq : s.wr = g.wr

theorem Inputs.after {g : CallGeometry} {s t : State} {regs : List Reg} (h : Inputs g s)
    (rest : Keeps regs s t) (di : .edi ∉ regs) (sp : .esp ∉ regs) (frame : Frame g.writes s.mem t.mem) :
    Inputs g t := by
  refine ⟨h.ws.rest rest di sp, h.lower, h.upper, by rw [rest.1 _ sp]; exact h.esp, h.room, h.top, ?_, ?_, h.inputPositive, h.inputBound,
    h.inputFit, ?_, h.inputApart, h.outputPositive, h.outputBound, h.outputFit, ?_, h.outputScratch,
    h.outputSeparate, by rw [rest.2.2]; exact h.wrEq⟩
  · exact fun i hi => (h.arguments i hi).frame rest sp frame (h.stackApart i hi)
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, rest.1 _ sp]]
    exact h.stackApart i hi r hr
  · intro j; rw [rest.2.1, rest.2.2]; exact h.inputRead j
  · intro j; rw [rest.2.2]; exact h.outputWrite j

theorem Inputs.keepBody {g : CallGeometry} {s : State} {m : Mem} {js ds : List Nat}
    (h : Inputs g s) (keep : Keep g.B g.toGeo.w js ds s.mem m)
    (hj : ∀ j ∈ js, j < nArr) (hd : ∀ d ∈ ds, SlotOk d) :
    Outside g.B 16 (g.Z - 16) s.mem m :=
  keepBody_of h.ws.hdr_le keep (fun j hm => h.ws.arr_fit (hj j hm)) hd

/-- The narrow arrays at the run-time width. -/
theorem Inputs.rt {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    VG.Proof.Rsa.X86.KeyRt.RtWs VG.Impl.Rsa.X86.RecoverRt.nar s g.B g.Z (8 * g.n + 8) nArr := by
  have ws : Ws s g.B g.Z (VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8)) nArr := by rw [kw_nar]; exact h.ws
  have up := h.upper
  refine ⟨ws, ⟨_, len.upper, ?_, ?_⟩, ?_, by omega, by decide⟩
  · simp only [VG.Impl.Rsa.X86.KeyRt.Lay.toLen, VG.Impl.Rsa.X86.RecoverRt.lay, VG.Proof.Rsa.X86.KeyRt.kw,
      Spec.Rsa.modulusWords, len.width]
    omega
  · have a := h.arguments 5 (by decide)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← len.scratch]; exact h.arguments 10 (by decide)

theorem Inputs.scratchFrame {g : CallGeometry} {s : State} (h : Inputs g s) {m m' : Mem}
    (frame : Outside g.B 16 (g.Z - 16) m m') : Frame g.writes m m' := by
  have out : Outside g.B 0 g.Z m m' :=
    frame.mono (by decide) (by have := h.ws.hdr_le; unfold hdr at this; omega)
  have f := outside_frame out (by have := h.ws.workspace.nowrap; omega)
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    f.mono (rs' := g.writes) (by simp [CallGeometry.writes, off])

/-- What a stage changes, within what the call may write. -/
theorem stage_writes (g : CallGeometry) (hz : 16 ≤ g.Z) :
    ∀ r ∈ stageR g.toGeo, ∃ r' ∈ g.writes, Region.Sub r r' := by
  intro r hr
  simp only [stageR, VG.Proof.Bignum.X86.CrtRt.frameR, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp [CallGeometry.writes], fun _ h => h⟩
  · exact ⟨⟨g.B, g.Z⟩, by simp [CallGeometry.writes], VG.Offset.sub_base _ (by omega)⟩

/-- The working space's length argument, at its length in `u64`s. -/
theorem Inputs.wsLen {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    CallArgument s g.B g.Z 11 (BitVec.ofNat 32 (g.Z / 8)) := by
  have a := h.arguments 11 (by decide)
  have e : g.Z / 8 = (g.args 11).toNat := by rw [len.bytes]; omega
  rwa [e, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- An argument's word lies apart from what a stage changes. -/
theorem Inputs.stageApart {g : CallGeometry} {s : State} (h : Inputs g s) {i : Nat} (hi : i < 12) :
    ∀ r ∈ stageR g.toGeo, Region.Disjoint ⟨stackAddress s i, 4⟩ r := fun r hr => by
  obtain ⟨r', hr', sub⟩ := stage_writes g (by have := h.ws.hdr_le; unfold hdr at this; omega) r hr
  exact (h.stackApart i hi r' hr').sub_right sub

theorem Inputs.of_KS {g : CallGeometry} {s t : State} {A AW V : Nat → Nat}
    {live liveW ls : List Nat} (h : Inputs g s)
    (ks : KS g.toGeo s A live AW liveW V ls t) : Inputs g t :=
  h.after ks.rest (by decide) (by decide) (ks.frame.sub (stage_writes g (by have := h.ws.hdr_le; unfold hdr at this; omega)))

end VG.Proof.Rsa.X86.Recover

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

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev mTop (g : Geo) : Nat := 2 ^ (32 * g.W - 1)
def AW1 (e d : Nat) : Nat → Nat := upd (upd (fun _ => 0) wE e) wD d
def AWp (g : Geo) (e d : Nat) : Nat → Nat := upd (upd (AW1 e d) wMod (mTop g)) wM (d * e)

theorem product_core_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {e d eLen dLen : Nat}
    (h : KS g s0 A [aN] (upd (AW1 e d) wMod (mTop g))
      [wMod, wZ, wE, wD, wM, wMod] (fun _ => 0) [] s)
    (ePos : 0 < eLen) (eBound : eLen ≤ 8 * g.n) (dBound : dLen ≤ 8 * g.n)
    (eFits : e < 2 ^ (8 * eLen)) (dFits : d < 2 ^ (8 * dLen))
    (count : s.gpr .esi = BitVec.ofNat 32 (8 * eLen)) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.mulMod VG.Impl.Rsa.X86.RecoverRt.wid wZ wE wD wM wMod wT) s fun t =>
      KS g s0 A [aN] (AWp g e d) [wM, wMod, wZ] (fun _ => 0) [] t := by
  have upper := h.upper
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.mulMod_ok h.rtW (by decide) (by omega) (by omega) count)
    fun t ⟨_, k, r, value⟩ => ?_
  rw [kw_wid] at k value
  have gZ : num s.mem g.B g.W wZ = 0 := by
    rw [h.arrsW wZ (by simp)]; simp [AW1, upd, wZ, wMod, wD, wE]
  have gE : num s.mem g.B g.W wE = e := by
    rw [h.arrsW wE (by simp)]; simp [AW1, upd, wMod, wD, wE]
  have gD : num s.mem g.B g.W wD = d := by
    rw [h.arrsW wD (by simp)]; simp [AW1, upd, wMod, wD]
  have gA : num s.mem g.B g.W wM = 0 := by
    rw [h.arrsW wM (by simp)]; simp [AW1, upd, wM, wMod, wD, wE]
  have gM : num s.mem g.B g.W wMod = mTop g := by
    rw [h.arrsW wMod (by simp)]; simp [upd]
  have expBound : 8 * dLen + 8 * eLen ≤ 32 * g.W - 1 := by
    change 8 * dLen + 8 * eLen ≤ 32 * (2 * (2 * g.n + 2) + 2) - 1
    omega
  have dSmall : d < mTop g := Nat.lt_of_lt_of_le dFits
    (Nat.pow_le_pow_right (by decide) (by omega))
  have result := value gZ (by rw [gA, gM]; exact Nat.two_pow_pos _)
    (by rw [gD, gM]; exact dSmall) (by
      rw [gM, show 2 * mTop g = 2 ^ (32 * g.W - 1 + 1) by rw [Nat.pow_succ, Nat.mul_comm],
        show 32 * g.W - 1 + 1 = 32 * g.W by have := h.wsW.wpos; omega])
  rw [gA, gE, gD, gM, VG.Proof.Rsa.recover_product_exact dFits eFits expBound] at result
  have hd : ∀ d ∈ [sB, sC], SlotOk d := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl) <;> decide
  refine h.core k (fun j hj => h.wsW.arr_fit (by
      simp only [VG.Proof.Rsa.X86.KeyRt.mulArrs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hd (r.mono (by decide))
    (h.arrs_W k (by simp only [List.mem_singleton]; rintro j rfl; decide) hd) h.live_lt ?_ ?_
    (by simp) (by simp)
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · rw [result]; simp [AWp, upd]
    · rw [k.num (by decide) (by decide) (h.wsW.fit64 (by decide)), gM]
      simp [AWp, upd, wM, wMod]
    · rw [k.num (by decide) (by decide) (h.wsW.fit64 (by decide)), gZ]
      simp [AWp, AW1, upd, wM, wMod, wZ, wE, wD]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro j (rfl | rfl | rfl) <;> decide

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def inputBytes (g : CallGeometry) (m : Mem) (i : Fin 3) : List Byte :=
  Spec.Rsa.bytesAt m (g.buffer (4 + 2 * i.val)).base (g.buffer (4 + 2 * i.val)).len

def inputValue (g : CallGeometry) (m : Mem) (i : Fin 3) : Nat := Spec.Rsa.os2ip (inputBytes g m i)

theorem inputValue_lt (g : CallGeometry) (m : Mem) (i : Fin 3) :
    inputValue g m i < 2 ^ (8 * (g.buffer (4 + 2 * i.val)).len) := by
  have h := VG.Proof.Rsa.lt_of_os2ip (inputBytes g m i)
  simpa only [inputValue, inputBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range,
    show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] using h

theorem Inputs.inputFrame {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s)
    (frame : Frame g.writes m m') (i : Fin 3) : inputBytes g m' i = inputBytes g m i :=
  VG.Proof.Rsa.rsa_bytes_frame frame (by have := h.inputBound i; have := h.upper; omega) (h.inputApart i)

structure LS (g : CallGeometry) (s0 : State) (A : Nat → Nat) (s : State) : Prop where
  inputs : Inputs g s
  frame : Outside g.B 16 (g.Z - 16) s0.mem s.mem
  rest : Keeps opRegs s0 s
  full : ∀ j < nArr, val32 s.mem g.B (arr g.toGeo.w j) (g.toGeo.w + 2) = A j

theorem LS.load {g : CallGeometry} {s0 s : State} {A : Nat → Nat} (h : LS g s0 A s) (len : Lengths g)
    (i : Fin 3) {j : Nat} (hj : j < nArr) (zero : A j = 0) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.load VG.Impl.Rsa.X86.RecoverRt.nar (4 + 2 * i.val) j) s fun t =>
      LS g s0 (upd A j (inputValue g s0.mem i)) t := by
  refine WP.mono (load_ok h.inputs len i hj (by rw [h.full j hj, zero])) fun t ⟨inputs, k, v, r⟩ => ?_
  have value : val32 t.mem g.B (arr g.toGeo.w j) (g.toGeo.w + 2) = inputValue g s0.mem i := by
    change _ = Spec.Rsa.os2ip (inputBytes g s.mem i) at v
    rw [h.inputs.inputFrame (h.inputs.scratchFrame h.frame) i] at v
    exact v
  refine ⟨inputs, h.frame.trans (h.inputs.keepBody k (by simpa using hj) (by simp)), h.rest.trans r, ?_⟩
  intro l hl
  by_cases eq : l = j
  · subst l; rw [upd_self]; exact value
  · rw [upd_ne _ _ eq, k.full (by simpa using Ne.symm eq) (by simp) (h.inputs.ws.fit64 hl), h.full l hl]

theorem zero_ls {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.zeroArrays VG.Impl.Rsa.X86.RecoverRt.nar nArr) s (LS g s (fun _ => 0)) := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroArrays_ok (h.rt len) (n := nArr) (by decide) (by decide))
    fun t ⟨_, f, z, r⟩ => ?_
  rw [kw_nar] at f z
  have fit := h.ws.fits
  change hdr + nArr * (4 * (width g.n + 2)) ≤ g.Z at fit
  have fit' : hdr + 4 * (nArr * (width g.n + 2)) ≤ g.Z := by simpa only [Nat.mul_left_comm] using fit
  have a0 : arr (width g.n) 0 = hdr := by simp [arr]
  rw [a0] at f
  have header := h.ws.hdr_le
  have O : Outside g.B 16 (g.Z - 16) s.mem t.mem := f.mono (by unfold hdr; omega) (by unfold hdr at *; omega)
  exact ⟨h.after (r.mono (rs' := [.eax, .ecx, .edx, .ebp]) (by decide)) (by decide) (by decide) (h.scratchFrame O),
    O, r.mono (by decide), z⟩

def Aload (n e d : Nat) : Nat → Nat := upd (upd (upd (fun _ => 0) aN n) (2 * wE) e) (2 * wD) d

theorem loads_ls {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.loads s
      (LS g s (Aload (inputValue g s.mem 0) (inputValue g s.mem 1) (inputValue g s.mem 2))) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.loads
  simp only [seqs]
  refine WP.seq (WP.mono (zero_ls h len) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (h1.load len 0 (j := aN) (by decide) rfl) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (h2.load len 1 (j := 2 * wE) (by decide) (by simp [upd, aN, wE])) fun s3 h3 => ?_)
  exact h3.load len 2 (j := 2 * wD) (by decide) (by simp [upd, aN, wE, wD])

theorem LS.number {g : CallGeometry} {s0 s : State} {A : Nat → Nat} (h : LS g s0 A s)
    {j : Nat} (hj : j < nArr) (bound : A j < 2 ^ (32 * g.toGeo.w)) :
    num s.mem g.B g.toGeo.w j = A j := by
  rw [← h.full j hj] at bound ⊢
  exact VG.Proof.Dsa.val32_prefix_of_lt (by omega) bound

theorem LS.wide {g : CallGeometry} {s0 s : State} {A : Nat → Nat} (h : LS g s0 A s)
    {j : Nat} (hj : j < 22) (zero : A (2 * j + 1) = 0) :
    num s.mem g.B g.toGeo.W j = A (2 * j) := by
  apply numW_of (h.full (2 * j) (by unfold nArr; omega))
  rw [h.number (by unfold nArr; omega) (by rw [zero]; exact Nat.two_pow_pos _), zero]

theorem loads_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.loads s fun t =>
      KS g.toGeo s (fun _ => inputValue g s.mem 0) [aN]
        (AW1 (inputValue g s.mem 1) (inputValue g s.mem 2)) [wZ, wE, wD, wM, wMod]
        (fun _ => 0) [] t := by
  refine WP.mono (loads_ls h len) fun t ht => ?_
  have header := h.ws.hdr_le
  have nw := h.ws.workspace.nowrap
  refine ⟨ht.inputs.rt len, h.lower, h.upper, outside_stage ht.frame (by omega) (by unfold hdr at header; omega),
    ht.inputs.esp, ht.inputs.room, ht.inputs.top, ht.inputs.wsLen len, by rw [len.bytes]; omega, ht.rest, ?_, ?_, by simp,
    by decide, by decide, by simp, h.wrEq, fun i hi => ⟨h.arguments i hi, h.stageApart hi⟩⟩
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    have value : Aload (inputValue g s.mem 0) (inputValue g s.mem 1) (inputValue g s.mem 2) aN =
        inputValue g s.mem 0 := rfl
    rw [ht.number (by decide) ?_, value]
    rw [value]
    apply Nat.lt_of_lt_of_le (inputValue_lt g s.mem 0)
    apply Nat.pow_le_pow_right (by decide)
    have := h.inputBound 0
    change 8 * (g.buffer (4 + 2 * (0 : Fin 3).val)).len ≤ 32 * (2 * g.n + 2)
    omega
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rw [ht.wide (by decide) (by simp [Aload, upd, wZ, wE, wD, wM, wMod, aN])] <;> rfl

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.RecoverRt (setTop wid)
open VG.Impl.Rsa.X86.Recover (wMod)
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S)
open VG.Proof.Rsa.X86.KeyRt

theorem setTop_ok {s : State} {B : Addr} {Z len N : Nat} (h : RtWs wid s B Z len N) (hj : wMod < N) :
    WP isa (.block setTop) s fun t =>
      RtWs wid t B Z len N ∧ Keep B (kw len) [wMod] [] s.mem t.mem ∧
      num t.mem B (kw len) wMod =
        val32 s.mem B (arr (kw len) wMod) (kw len - 1) + 2 ^ (32 * (kw len - 1)) * 2 ^ 31 ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have fit := h.ws.arr_fit hj
  have nowrap := h.ws.workspace.nowrap
  have pos := h.kw_pos
  simp only [S] at fit
  unfold setTop
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (by decide) (by decide) (by omega) fun u K m p e => ?_
  refine wp_addS rfl fun u₁ U₁ _ => wp_subS rfl fun u₂ U₂ _ => wp_movS rfl fun u₃ U₃ _ => ?_
  have K₃ : Keeps [.eax, .ecx, .edx] s u₃ :=
    ((K.mono (by decide)).trans ((U₁.keeps.trans U₂.keeps).mono (by decide))).trans (U₃.keeps.mono (by decide))
  have hu := h.rt.of_keeps K₃
  have ptr : PtrAt u₃ B .eax (arr (kw len) wMod + 4 * (kw len - 1)) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.gpr, U₁.gpr, BitVec.toNat_sub, BitVec.toNat_add, p, e,
      show (12 : BitVec 32).toNat = 12 from rfl]
    omega
  refine wp_storeS (ea_ptr hu ptr (d := 0) (by omega)) (ws_write hu (y := arr (kw len) wMod + 4 * (kw len - 1) + 0)
    (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off B (arr (kw len) wMod + 4 * (kw len - 1))) (0x80000000 : BitVec 32) := by
    rw [T.mem, U₃.gpr, U₃.mem, U₂.mem, U₁.mem, m, Nat.add_zero]
  have frame := writeW32_outside s.mem B (d := arr (kw len) wMod + 4 * (kw len - 1))
    (0x80000000 : BitVec 32) (by omega)
  rw [← mem] at frame
  have Kt : Keeps [.eax, .ecx, .edx] s t := K₃.trans ((T.keeps []).mono (by decide))
  refine ⟨h.keep Kt (by decide) (by decide) (frame.mono (Nat.zero_le _) (by omega)),
    Keep.of_arr frame (by simp only [S]; omega) (by simp), ?_, Kt⟩
  change val32 _ _ _ _ = _
  have expand := val32_succ t.mem B (arr (kw len) wMod) (kw len - 1)
  rw [show kw len - 1 + 1 = kw len by omega] at expand
  rw [expand, frame.val32 (.inl (by omega)) (by omega)]
  congr 2
  simp only [w32]
  rw [mem, Mem.readW_writeW_self32]
  rfl

end VG.Proof.Rsa.X86.Recover

section

/-! # The public iteration count for the exponent product -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Bignum.X86

theorem prodCount_ok {s : State} {base : Addr} {size eLen : Nat}
    (h : CallArgument s base size 7 (BitVec.ofNat 32 eLen)) :
    WP isa (.block prodCount) s fun t => t.gpr .esi = BitVec.ofNat 32 (8 * eLen) ∧
      t.mem = s.mem ∧ Keeps [.esi] s t := by
  unfold prodCount
  refine wp_movS h.readSrc fun u U _ => ?_
  refine wp_addS rfl fun v V _ => ?_
  refine wp_addS rfl fun w W _ => ?_
  refine wp_addS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (W.mem.trans (V.mem.trans U.mem)),
    U.keeps.trans (V.keeps.trans (W.keeps.trans T.keeps))⟩
  rw [T.gpr, W.gpr, V.gpr, U.gpr]
  simp only [← BitVec.ofNat_add]
  congr 1
  omega

end VG.Proof.Rsa.X86.Recover
end

end

section

/-! # Setting up and computing the exact exponent product -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Bignum.X86

theorem prod_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {e d eLen dLen : Nat}
    (h : KS g s0 A [aN] (AW1 e d) [wZ, wE, wD, wM, wMod] (fun _ => 0) [] s)
    (arg : CallArgument s g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ePos : 0 < eLen) (eBound : eLen ≤ 8 * g.n) (dBound : dLen ≤ 8 * g.n)
    (eFits : e < 2 ^ (8 * eLen)) (dFits : d < 2 ^ (8 * dLen)) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.prod s fun t =>
      KS g s0 A [aN] (AWp g e d) [wM, wMod, wZ] (fun _ => 0) [] t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.prod
  refine WP.seq (WP.block_append (WP.mono (setTop_ok h.rtW (by decide))
    fun u ⟨_, k, value, r⟩ => ?_))
  rw [kw_wid] at k value
  have zero : num s.mem g.B g.W wMod = 0 := by
    rw [h.arrsW wMod (by simp)]; simp [AW1, upd, wMod, wD, wE]
  have low : val32 s.mem g.B (arr g.W wMod) (g.W - 1) = 0 := by
    have expand := val32_succ s.mem g.B (arr g.W wMod) (g.W - 1)
    rw [show g.W - 1 + 1 = g.W by have := h.wsW.wpos; omega] at expand
    change val32 _ _ _ _ = 0 at zero
    omega
  have newValue : num u.mem g.B g.W wMod = mTop g := by
    rw [value, low, Nat.zero_add, ← Nat.pow_add]
    congr 1
  have hu := h.write_W k (by decide) (by simp) (r.mono (by decide)) newValue
    (by simp only [List.mem_singleton]; rintro j rfl; decide) (by simp)
  have frame := h.keepBody k (fun j hj => h.wsW.arr_fit (by simp only [List.mem_singleton] at hj; subst j; decide)) (by simp)
  have argU := arg.keep r (by decide) (frame.mono (by omega) (by have := h.ws.hdr_le; unfold hdr at this; omega))
  refine WP.mono (prodCount_ok argU) fun v ⟨count, mem, rv⟩ => ?_
  exact product_core_ok (hu.of_rest rv (by decide) mem) ePos eBound dBound eFits dFits count

end VG.Proof.Rsa.X86.Recover
end

end

section

/-! # The initial recovery validity test -/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Rsa.KeyBits32

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.KeyRt (kw sel_ok arrPtr_ok lenSrc)

theorem output_word {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 2)
    (f : Frame [g.buffer (2 * i.val)] m m') {d : Nat} (bound : d + 4 ≤ g.Z) :
    w32 m' g.B d = w32 m g.B d := by
  unfold w32
  rw [f.readW (r := ⟨g.B, g.Z⟩) (a := off g.B d) (w := 32)
    (Scr.contains h.ws.workspace.nowrap bound)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (h.outputScratch i).symm) (by decide)]

theorem output_num {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 2)
    (f : Frame [g.buffer (2 * i.val)] m m') {j : Nat} (hj : j < nArr) :
    num m' g.B g.toGeo.w j = num m g.B g.toGeo.w j := by
  apply val32_congr
  intro k hk
  have fits := h.ws.arr_fit hj
  unfold S at fits
  exact output_word h i f (by omega)

theorem store_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (i : Fin 2) {j : Nat}
    (hj : j < nArr) (hjz : j ≠ aZero) (zero : num s.mem g.B g.toGeo.w aZero = 0) (accept : Bool)
    (mask : slot s.mem g.B sMask = if accept then 1 else 0) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.store (2 * i.val) j) s fun t =>
      Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer (2 * i.val)).base (g.buffer (2 * i.val)).len =
        Spec.Rsa.i2osp ((if accept then num s.mem g.B g.toGeo.w j else 0) %
          2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len ∧
      Frame [⟨off g.B (arr g.toGeo.w j), S g.toGeo.w⟩, g.buffer (2 * i.val)] s.mem t.mem ∧
      (∀ d, d + 4 ≤ hdr → slot t.mem g.B d = slot s.mem g.B d) ∧
      (∀ k, k < nArr → k ≠ j → num t.mem g.B g.toGeo.w k = num s.mem g.B g.toGeo.w k) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have r := h.rt len
  have kn : kw (8 * g.n + 8) = g.toGeo.w := kw_nar g.n
  have fits := h.ws.arr_fit hj
  have nw := h.ws.workspace.nowrap
  have fit64 := h.ws.fit64 hj
  have up := h.upper
  have hi := i.isLt
  unfold VG.Impl.Rsa.X86.RecoverRt.store
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok r hj (by decide) hj (by decide) (by rw [mask]; cases accept <;> decide) (.inl hjz))
    fun u ⟨ru, ku, vu, rku⟩ => ?_
  rw [kn] at ku vu
  have outside := h.keepBody ku (by simpa using hj) (by simp)
  have frameU := h.scratchFrame outside
  have inputsU := h.after rku (by decide) (by decide) frameU
  have raw : Outside g.B (arr g.toGeo.w j) (S g.toGeo.w) s.mem u.mem := by
    intro a ha
    apply ku a
    intro r hr
    simp only [ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_singleton] at hr
    subst r
    exact ha
  have ownFrame := outside_frame raw fit64
  have chosen : num u.mem g.B g.toGeo.w j = if accept then num s.mem g.B g.toGeo.w j else 0 := by
    rw [vu, mask, zero]; cases accept <;> rfl
  have positive := h.outputPositive i
  have bound := h.outputBound i
  have outFit := h.outputFit i
  have outWrite := h.outputWrite i
  have outScratch := h.outputScratch i
  simp only [CallGeometry.buffer] at positive bound outFit outWrite outScratch ⊢
  generalize hL : (g.args (2 * i.val + 1)).toNat = L at positive bound outFit outWrite outScratch ⊢
  have Lw : L ≤ 4 * g.toGeo.w := by simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega
  simp only [S] at fits
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (inputsU.arguments (2 * i.val) (by omega)).readSrc fun u₁ U₁ _ => ?_
  have h₁ := inputsU.after U₁.keeps (by decide) (by decide) (by rw [U₁.mem]; exact Frame.refl _ _)
  refine wp_movS (h₁.arguments (2 * i.val + 1) (by omega)).readSrc fun u₂ U₂ _ => ?_
  have K₂ : Keeps [.ebx, .ecx] u u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have m₂ : u₂.mem = u.mem := by rw [U₂.mem, U₁.mem]
  have r₂ := ru.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc r₂) r₂.lenLe r₂.edi (by decide) (by decide) (by rw [kn]; omega)
    fun v Kv mv pv _ => ?_
  rw [kn] at pv
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  have srcAddr : byteAddr (v.gpr .esi) = off g.B (arr g.toGeo.w j) :=
    VG.Proof.Bignum.X86.PublicRt.byteAddr_ptr pv (by omega)
  have K₄ : Keeps [.ebx, .ecx, .edx, .esi] u v₄ :=
    ((K₂.mono (by decide)).trans (Kv.mono (by decide))).trans ((u₃.keeps.mono (by decide)).trans
      (u₄.keeps.mono (by decide)))
  have m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, mv, m₂]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have ebx₄ : v₄.gpr .ebx = g.args (2 * i.val) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.other _ (by decide), U₁.gpr]
  have esi₄ : v₄.gpr .esi = v.gpr .esi + BitVec.ofNat 32 (L - 1) := by
    have ecx : v.gpr .ecx = BitVec.ofNat 32 L := by
      rw [Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [u₄.gpr, u₃.gpr, ecx]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have keepU : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ := (rku.mono (by decide)).trans (K₄.mono (by decide))
  have hsub : Region.Sub ⟨off g.B (arr g.toGeo.w j), L⟩ ⟨g.B, g.Z⟩ := by
    have := Offset.sub g.B (d := arr g.toGeo.w j) (n := L) (e := 0) (k := g.Z) (Nat.zero_le _)
      (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine WP.mono (reverseBuffer_ok v₄ (src := v.gpr .esi) (dst := g.args (2 * i.val)) (n := L) (by omega)
    (by omega) outFit (by omega)
    (by rw [keepU.2.1, keepU.2.2, srcAddr]; exact h.ws.workspace.read (by omega))
    (by rw [keepU.2.2]; exact outWrite) (by rw [srcAddr]; exact outScratch.symm.sub_left hsub) ebx₄ esi₄ ecx₄)
    fun t ⟨V, F, _, T⟩ => ?_
  have F' : Frame [⟨byteAddr (g.args (2 * i.val)), L⟩] u.mem t.mem := by rw [← m₄]; exact F
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := keepU.trans (T.mono (by decide))
  have Fb : Frame [g.buffer (2 * i.val)] u.mem t.mem := by simpa [CallGeometry.buffer, hL] using F'
  have fullFrame : Frame g.writes s.mem t.mem :=
    frameU.trans (Fb.mono (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      have cases : i.val = 0 ∨ i.val = 1 := by omega
      rcases cases with e | e <;> simp [CallGeometry.writes, e]))
  refine ⟨h.after all (by decide) (by decide) fullFrame, ?_, ?_, ?_, ?_, all⟩
  · rw [V, srcAddr, m₄, ← chosen]
    have eq : (u.mem.read (off g.B (arr g.toGeo.w j)) (4 * g.toGeo.w)).toNat =
        num u.mem g.B g.toGeo.w j := read_eq_val32 _ _ _ _
    rw [read_prefix u.mem _ (Lw), BitVec.toNat_setWidth, eq]
  · exact (ownFrame.mono (by simp)).trans (F'.mono (by simp))
  · intro d hd
    change w32 t.mem g.B d = w32 s.mem g.B d
    rw [output_word h i Fb (by have := h.ws.hdr_le; omega)]
    exact ku.slot hd (by simp)
  · intro k hk ne
    rw [output_num h i Fb hk]
    exact ku.num (by simpa using Ne.symm ne) (by simp) (h.ws.fit64 hk)
end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def bodyWrites (g : CallGeometry) : List Region :=
  [⟨off g.B 16, g.Z - 16⟩, g.buffer 0, g.buffer 2, VG.X86.below g.sp 96]

theorem storeFrame_body {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 2)
    {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.B (arr g.toGeo.w j), S g.toGeo.w⟩, g.buffer (2 * i.val)] m m') :
    Frame (bodyWrites g) m m' := by
  apply f.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨⟨off g.B 16, g.Z - 16⟩, by simp [bodyWrites], Offset.sub g.B ?_ ?_⟩
    · have : hdr ≤ arr g.toGeo.w j := Nat.le_add_right _ _
      unfold hdr at this; omega
    · have := h.ws.arr_fit hj
      have := h.ws.hdr_le
      unfold hdr at this; omega
  · refine ⟨g.buffer (2 * i.val), ?_, fun _ hx => hx⟩
    have cases : i.val = 0 ∨ i.val = 1 := by omega
    rcases cases with e | e <;> simp [bodyWrites, e]

theorem output_preserved {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i k : Fin 2)
    (ne : k ≠ i) {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.B (arr g.toGeo.w j), S g.toGeo.w⟩, g.buffer (2 * i.val)] m m') :
    Spec.Rsa.bytesAt m' (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len =
      Spec.Rsa.bytesAt m (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame f (by have := h.outputBound k; have := h.upper; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.outputScratch k).sub_right (Offset.sub_base g.B (h.ws.arr_fit hj))
  · exact h.outputSeparate k i ne

def resultBytes (g : CallGeometry) (m : Mem) (accept : Bool) (i : Fin 2) (j : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then num m g.B g.toGeo.w j else 0) %
    2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len

theorem stores_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (zero : num s.mem g.B g.toGeo.w aZero = 0) (accept : Bool)
    (mask : slot s.mem g.B sMask = if accept then 1 else 0) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.stores s fun t => Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = resultBytes g s.mem accept 0 5 ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = resultBytes g s.mem accept 1 6 ∧
      t.gpr .eax = BitVec.ofNat 32 accept.toNat ∧ Frame (bodyWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok h len 0 (j := 5) (by decide) (by decide) zero accept mask) fun u ⟨hu, vu, fu, huHeader, huOther, ru⟩ => ?_
  have zeroU : num u.mem g.B g.toGeo.w aZero = 0 := by rw [huOther _ (by decide) (by decide), zero]
  have maskU : slot u.mem g.B sMask = if accept then 1 else 0 := by rw [huHeader _ (by decide), mask]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok hu len 1 (j := 6) (by decide) (by decide) zeroU accept maskU) fun v ⟨hv, vv, fv, hvHeader, _, rv⟩ => ?_
  have maskV : slot v.mem g.B sMask = if accept then 1 else 0 := by rw [hvHeader _ (by decide), maskU]
  refine wp_movS (readSrc_sc hv.ws.workspace (by have := hv.ws.hdr_le; unfold sMask hdr at *; omega)) fun t T _ => WP.block_nil ?_
  have frame : Frame (bodyWrites g) s.mem t.mem := by
    rw [T.mem]
    exact (storeFrame_body h 0 (by decide) fu).trans (storeFrame_body hu 1 (by decide) fv)
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    ru.trans (rv.trans (T.keeps.mono (by decide)))
  refine ⟨hv.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _), ?_, ?_, ?_, frame, all⟩
  · rw [T.mem]
    exact (output_preserved hu 1 0 (by decide) (by decide) fv).trans vu
  · rw [T.mem]
    rw [huOther _ (by decide) (by decide)] at vv
    exact vv
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr]
    change slot v.mem g.B sMask = _
    rw [maskV]; cases accept <;> rfl

end VG.Proof.Rsa.X86.Recover
