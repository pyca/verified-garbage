import VerifiedGarbage.Proof.MlKem.X86.Sample
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Impl.MlDsa.X86.Sample.Common
import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejNtt

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sample.Setup`. -/
section

/-!
# ML-DSA on x86 (32-bit): the layout of the sampling functions

The four sampling functions share a layout
(`Impl/MlDsa/X86/Sample/Common.lean`), described by a `Lay`: their number of
arguments `nA` (the message pointer first), the arguments that are the output
polynomial (`iA`) and `scratch` (`iS`), the rate of the SHAKE they use, the
bytes they squeeze, and the message length: a constant, or (`sampleInBall`)
the second argument. `Pre L` is what their shared contracts' preconditions
say, for the stack of 56 bytes they use (16 for the leaf's frame, 40 for the
calls); `PubP L` that two entry states have the same pointers and `esp`.
`Base` is what holds throughout the body: `esp` as the leaf's frame left it,
the permissions, and memory changed only in the output polynomial, `scratch`,
the 40 bytes of stack below the frame the calls use, and the arguments on the
stack (which `sampleInBall` overwrites; `Ctx` says they are intact, with
`esi = scratch`).
-/

namespace VG.Proof.MlDsa.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Proof.MlKem.X86.Sample (cR E1)

/-- The layout of a sampling function. -/
structure Lay where
  /-- The number of (32-bit) arguments. -/
  nA : Nat
  /-- The argument that is the output polynomial. -/
  iA : Nat
  /-- The argument that is `scratch`. -/
  iS : Nat
  rate : Nat
  outlen : Nat
  /-- The length of the message: a constant, or (`none`) argument 1. -/
  mlen : Option Nat

namespace Lay

/-- The message length. -/
def ml (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Nat := match L.mlen with
  | some k => k
  | none => (arg s₀ 1).toNat

/-- The source of the message length in the code. -/
def lenSrc (L : VG.Proof.MlDsa.X86.Sample.Lay) : Src := match L.mlen with
  | some k => .imm (BitVec.ofNat 32 k)
  | none => .mem (Impl.MlDsa.X86.Sample.argOp 1)

abbrev dP (_L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : BitVec 32 := arg s₀ 0
abbrev aP (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : BitVec 32 := arg s₀ L.iA
abbrev sP (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : BitVec 32 := arg s₀ L.iS
abbrev dA (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Addr := (L.dP s₀).setWidth 64
abbrev aA (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Addr := (L.aP s₀).setWidth 64
abbrev sA (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Addr := (L.sP s₀).setWidth 64
abbrev dR (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Region := ⟨L.dA s₀, L.ml s₀⟩
abbrev aR (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Region := ⟨L.aA s₀, 1024⟩
abbrev sR (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Region := ⟨L.sA s₀, 2048⟩
abbrev gR (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Region := ⟨argAddr s₀ 0, 4 * L.nA⟩
abbrev stkR (_L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Region := ⟨(E0 s₀).setWidth 64 - 56#64, 56⟩
/-- The message. -/
abbrev Msg (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : List Byte := bytesAt s₀.mem (L.dA s₀) (L.ml s₀)
/-- The Keccak functions' working space. -/
abbrev WW (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : BitVec 32 := L.sP s₀ + BitVec.ofNat 32 200
/-- What the body may change. -/
abbrev W (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : List Region := [L.aR s₀, L.sR s₀, VG.Proof.MlKem.X86.Sample.cR s₀, L.gR s₀]
/-- The XOF output. -/
abbrev out (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : List Byte :=
  Spec.Sha3.squeezeFrom L.rate (Proof.MlDsa.Sample.padded L.rate Spec.Sha3.shakeSuffix (L.Msg s₀)) 0 L.outlen

end Lay

/-- What the preconditions of the sampling functions' contracts say, for a
stack of 56 bytes. -/
structure Pre (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) : Prop where
  sp : 56 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * L.nA ≤ 2 ^ 32
  rd : s₀.rd = [L.dR s₀]
  wr : s₀.wr = [L.aR s₀, L.sR s₀, L.gR s₀]
  d_a : (L.dR s₀).Disjoint (L.aR s₀)
  d_s : (L.dR s₀).Disjoint (L.sR s₀)
  d_g : (L.dR s₀).Disjoint (L.gR s₀)
  a_s : (L.aR s₀).Disjoint (L.sR s₀)
  a_g : (L.aR s₀).Disjoint (L.gR s₀)
  s_g : (L.sR s₀).Disjoint (L.gR s₀)
  ret_d : (VG.Proof.MlKem.X86.retR s₀).Disjoint (L.dR s₀)
  ret_a : (VG.Proof.MlKem.X86.retR s₀).Disjoint (L.aR s₀)
  ret_s : (VG.Proof.MlKem.X86.retR s₀).Disjoint (L.sR s₀)
  ret_g : (VG.Proof.MlKem.X86.retR s₀).Disjoint (L.gR s₀)
  stk_d : (L.stkR s₀).Disjoint (L.dR s₀)
  stk_a : (L.stkR s₀).Disjoint (L.aR s₀)
  stk_s : (L.stkR s₀).Disjoint (L.sR s₀)
  stk_g : (L.stkR s₀).Disjoint (L.gR s₀)
  d_fit : (L.dP s₀).toNat + L.ml s₀ ≤ 2 ^ 32
  a_fit : (L.aP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (L.sP s₀).toNat + 2048 ≤ 2 ^ 32
  /-- The message is shorter than a block. -/
  ml_lt : L.ml s₀ < L.rate

/-- The pointers and `esp` agree (and so do the arguments). -/
def PubP (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ ∀ i < L.nA, arg s₀ i = arg s₀' i

/-- The taint analysis proves `c` constant time from the registers `R`. -/
def TaintOk (R : List Reg) (c : Prog isa) : Prop :=
  ∃ hc : Taint.Hint VG.X86.Taint.T, (VG.X86.taint.check (τr R) c hc).isSome = true

/-- The layout's facts about its numbers, and the taint analysis of its
blocks (which depend on them). -/
structure Lay.Ok (L : VG.Proof.MlDsa.X86.Sample.Lay) : Prop where
  iA : L.iA < L.nA
  iS : L.iS < L.nA
  one : 1 < L.nA
  rate : L.rate ∈ Spec.Sha3.rates
  out : 840 + L.outlen + 4 ≤ 2048
  mlen : ∀ k, L.mlen = some k → k < 2 ^ 32
  tLd : VG.Proof.MlDsa.X86.Sample.TaintOk [.esp] (.block [.mov .esi (.mem (Impl.MlDsa.X86.Sample.argOp L.iS))])
  tAbs : VG.Proof.MlDsa.X86.Sample.TaintOk [.esp] (.block (Impl.MlDsa.X86.Sample.absArgs L.rate L.lenSrc))
  tPad : VG.Proof.MlDsa.X86.Sample.TaintOk [.esp] (.block (Impl.MlDsa.X86.Sample.padArgs L.rate L.lenSrc))
  tSqz : VG.Proof.MlDsa.X86.Sample.TaintOk [] (.block (Impl.MlDsa.X86.Sample.sqzArgs L.rate L.outlen))

namespace PubP
variable {L : VG.Proof.MlDsa.X86.Sample.Lay} {s₀ s₀' : State} (hL : L.Ok) (hq : VG.Proof.MlDsa.X86.Sample.PubP L s₀ s₀')
include hL hq

theorem dP : L.dP s₀ = L.dP s₀' := hq.2 0 (by have := hL.one; omega)
theorem aP : L.aP s₀ = L.aP s₀' := hq.2 _ hL.iA
theorem sP : L.sP s₀ = L.sP s₀' := hq.2 _ hL.iS
theorem ml : L.ml s₀ = L.ml s₀' := by
  unfold Lay.ml; split
  · rfl
  · rw [hq.2 1 hL.one]

omit hL in
theorem e1 : VG.Proof.MlKem.X86.Sample.E1 s₀ = VG.Proof.MlKem.X86.Sample.E1 s₀' := by simp only [VG.Proof.MlKem.X86.Sample.E1, P0_esp, hq.1]

end PubP

theorem esp_nat (s₀ : State) (h : 16 ≤ (E0 s₀).toNat) : (VG.Proof.MlKem.X86.Sample.E1 s₀).toNat = (E0 s₀).toNat - 16 :=
  VG.Proof.MlKem.X86.Sample.esp_nat s₀ h

namespace Pre
variable {L : VG.Proof.MlDsa.X86.Sample.Lay} {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Pre L s₀)
include hp

theorem stk_below : L.stkR s₀ = below (E0 s₀) 56 := by
  simp only [Lay.stkR, below]; rw [Taint.sub_setWidth hp.sp]

theorem frame_sub : Region.Sub (frameR s₀) (L.stkR s₀) := by
  rw [hp.stk_below]; exact below_sub (by omega) hp.sp

theorem c_sub : Region.Sub (VG.Proof.MlKem.X86.Sample.cR s₀) (L.stkR s₀) := by
  rw [hp.stk_below, VG.Proof.MlKem.X86.Sample.Pre.cR_eq]
  exact below_inner (sp := E0 s₀) (a := 40) (b := 56) (k := 16) (by omega) hp.sp

theorem frame_c : (frameR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.cR s₀) :=
  VG.Proof.MlKem.X86.Sample.Pre.cR_eq (s₀ := s₀) ▸
    VG.Proof.MlKem.X86.Sample.below_adj (sp := E0 s₀) (a := 16) (b := 40) (by have := hp.sp; omega)

theorem ret_c : (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.cR s₀) :=
  (hp.stk_below ▸ VG.Proof.MlKem.X86.Sample.ret_below (sp := E0 s₀) hp.sp).sub_right hp.c_sub

theorem fr16 : (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region) = frameR s₀ := by
  simp only [frameR, below]; rw [Taint.sub_setWidth (by have := hp.sp; omega)]

theorem hW : ∀ r ∈ L.W s₀, (frameR s₀).Disjoint r ∧ (VG.Proof.MlKem.X86.retR s₀).Disjoint r := by
  intro r hr
  simp only [Lay.W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨hp.stk_a.sub_left hp.frame_sub, hp.ret_a⟩
  · exact ⟨hp.stk_s.sub_left hp.frame_sub, hp.ret_s⟩
  · exact ⟨hp.frame_c, hp.ret_c⟩
  · exact ⟨hp.stk_g.sub_left hp.frame_sub, hp.ret_g⟩

theorem dW : ∀ r ∈ L.W s₀, (L.dR s₀).Disjoint r := by
  intro r hr
  simp only [Lay.W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.d_a
  · exact hp.d_s
  · exact (hp.stk_d.sub_left hp.c_sub).symm
  · exact hp.d_g

theorem sub_s {o n : Nat} (h : o + n ≤ 2048) : Region.Sub ⟨L.sA s₀ + BitVec.ofNat 64 o, n⟩ (L.sR s₀) :=
  sub_of_contains (contains_at h hp.s_fit)

theorem off_eq {o : Nat} (h : o < 2048) :
    (L.sP s₀ + BitVec.ofNat 32 o).setWidth 64 = L.sA s₀ + BitVec.ofNat 64 o :=
  ea_off (by have := hp.s_fit; omega)

theorem reg_s {o n : Nat} (h : o < 2048) :
    reg32 (L.sP s₀ + BitVec.ofNat 32 o) n = ⟨L.sA s₀ + BitVec.ofNat 64 o, n⟩ := by
  show (⟨(L.sP s₀ + BitVec.ofNat 32 o).setWidth 64, n⟩ : Region) = _
  rw [hp.off_eq h]

omit hp in
theorem reg_s0 {n : Nat} : reg32 (L.sP s₀) n = ⟨L.sA s₀ + BitVec.ofNat 64 0, n⟩ := by
  show (⟨(L.sP s₀).setWidth 64, n⟩ : Region) = _
  simp only [BitVec.add_zero]

/-- The push changes nothing but the frame. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide)
    (by rw [saveRegs_len]; exact Nat.le_trans (by decide) hp.sp)
  rw [saveRegs_len] at hf
  exact hf

theorem msg0 : bytesAt (P0 s₀).mem (L.dA s₀) (L.ml s₀) = L.Msg s₀ :=
  VG.Proof.MlKem.bytesAt_frame hp.P0_keep (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.stk_d.sub_left hp.frame_sub).symm) (by have := hp.d_fit; omega)

theorem kbufs : KBufs (VG.Proof.MlKem.X86.Sample.E1 s₀) (L.sP s₀) (L.WW s₀) := by
  have hs := hp.s_fit
  have e := VG.Proof.MlDsa.X86.Sample.esp_nat s₀ (by have := hp.sp; omega)
  have hsp := hp.sp
  refine ⟨by rw [e]; omega, by omega, by rw [VG.Proof.MlKem.X86.Sample.toNat_off (by omega)]; omega, ?_, ?_, ?_⟩
  · rw [VG.Proof.MlDsa.X86.Sample.Pre.reg_s0, hp.reg_s (by omega)]
    exact VG.Proof.MlKem.X86.Sample.disj_at (len := 2048) (by omega) (by omega) hs (by omega)
  · rw [VG.Proof.MlDsa.X86.Sample.Pre.reg_s0]
    exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))
  · rw [hp.reg_s (by omega)]
    exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))

theorem within_s {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat} (ho : o < 2048) (h : o + n ≤ 2048) :
    Within (reg32 (L.sP s₀ + BitVec.ofNat 32 o) n) s.wr := by
  rw [hp.reg_s ho]
  exact ⟨L.sR s₀, by rw [hw, P0_wr, hp.wr]; simp, o, rfl, h⟩

theorem within_s0 {s : State} (hw : s.wr = (P0 s₀).wr) {n : Nat} (h : n ≤ 2048) :
    Within (reg32 (L.sP s₀) n) s.wr := by
  rw [VG.Proof.MlDsa.X86.Sample.Pre.reg_s0]
  exact ⟨L.sR s₀, by rw [hw, P0_wr, hp.wr]; simp, 0, rfl, by simpa using h⟩

/-- An access of `n` bytes at offset `o` of `scratch` is permitted. -/
theorem inS {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat} (h : o + n ≤ 2048) :
    InRegions s.wr (L.sA s₀ + BitVec.ofNat 64 o) n :=
  ⟨L.sR s₀, by rw [hw, P0_wr, hp.wr]; simp, contains_at h hp.s_fit⟩

theorem inS' {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat} (h : o + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (L.sA s₀ + BitVec.ofNat 64 o) n :=
  let ⟨r, hr, hc⟩ := hp.inS hw h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A write within the output polynomial is permitted. -/
theorem inA {s : State} (hw : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 256) :
    InRegions s.wr (Proof.MlDsa.Sample.coeffAddr (L.aA s₀) i) 4 :=
  ⟨L.aR s₀, by rw [hw, P0_wr, hp.wr]; simp, Proof.MlDsa.Sample.coeff_contains _ hi⟩

end Pre

/-! ## What holds throughout the body -/

structure Base (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.MlKem.X86.Sample.E1 s₀
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame (L.W s₀) (P0 s₀).mem s.mem

/-- `Base`, with the arguments intact and `esi = scratch`. -/
structure Ctx (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.Base L s₀ s where
  args : ∀ i < L.nA, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i
  esi : s.gpr .esi = L.sP s₀

namespace Base
variable {L : VG.Proof.MlDsa.X86.Sample.Lay} {s₀ s : State} (hp : VG.Proof.MlDsa.X86.Sample.Pre L s₀) (h : VG.Proof.MlDsa.X86.Sample.Base L s₀ s)
include hp h

theorem msg : bytesAt s.mem (L.dA s₀) (L.ml s₀) = L.Msg s₀ :=
  (VG.Proof.MlKem.bytesAt_frame h.frame hp.dW (by have := hp.d_fit; omega)).trans hp.msg0

theorem argIn {i : Nat} (hi : i < L.nA) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [h.rd, h.wr]
  exact P0_argIn hi hp.sp' (by simp [hp.wr])

theorem argInW {i : Nat} (hi : i < L.nA) : InRegions s.wr (argAddr s₀ i) 4 := by
  rw [h.wr, P0_wr, hp.wr]
  exact ⟨L.gR s₀, by simp, VG.Proof.MlKem.X86.arg_contains hi hp.sp'⟩

omit hp in
theorem argEa {i : Nat} : (s.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := by
  rw [h.esp]; exact P0_argAddr s₀ i

omit hp in
/-- After a call that changes memory only within `rs`, parts of `W`. -/
theorem call {s' : State} (e₁ : s'.rd = s.rd) (e₂ : s'.wr = s.wr)
    (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region} (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ L.W s₀, Region.Sub r r') : VG.Proof.MlDsa.X86.Sample.Base L s₀ s' :=
  ⟨by rw [e₃ .esp (by simp [calleeSaved]), h.esp], by rw [e₁, h.rd], by rw [e₂, h.wr],
    h.frame.trans (fr.sub hs)⟩

end Base

/-- The arguments at the push. -/
theorem args0 {L : VG.Proof.MlDsa.X86.Sample.Lay} {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Pre L s₀) : ∀ i < L.nA, (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
  fun _ hi => P0_arg (by have := hp.sp; omega) hi hp.sp'
    (by rw [hp.fr16]; exact (hp.stk_g.sub_left hp.frame_sub))

/-- The regions a call of the Keccak functions changes are parts of `W`,
apart from the arguments. -/
theorem calls_sub {L : VG.Proof.MlDsa.X86.Sample.Lay} (hL : L.Ok) {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Pre L s₀) :
    ∀ r ∈ [reg32 (L.sP s₀) 200, reg32 (L.sP s₀ + BitVec.ofNat 32 840) L.outlen, reg32 (L.WW s₀) 640,
      below (VG.Proof.MlKem.X86.Sample.E1 s₀) 40], ∃ r' ∈ L.W s₀, Region.Sub r r' ∧ r'.Disjoint (L.gR s₀) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨L.sR s₀, by simp, by rw [Pre.reg_s0]; exact hp.sub_s (by omega), hp.s_g⟩
  · exact ⟨L.sR s₀, by simp, by rw [hp.reg_s (by omega)]; exact hp.sub_s (by have := hL.out; omega), hp.s_g⟩
  · exact ⟨L.sR s₀, by simp, by rw [hp.reg_s (by omega)]; exact hp.sub_s (by omega), hp.s_g⟩
  · exact ⟨VG.Proof.MlKem.X86.Sample.cR s₀, by simp, fun _ h => h, hp.stk_g.sub_left hp.c_sub⟩

end VG.Proof.MlDsa.X86.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sample.Sponge`. -/
section

/-!
# ML-DSA on x86 (32-bit): the SHAKE output of the sampling functions

`sponge` (the start of each sampling function,
`Impl/MlDsa/X86/Sample/Common.lean`) loads `scratch` into `esi` (`ld_piece`),
zeroes the Keccak state at `scratch` (`zero_piece`), absorbs the message, pads
it, and squeezes `outlen` bytes to `scratch + 840` with the verified Keccak
functions (`absorb_call`, `pad_call`, `squeeze_call`), leaving the first
`outlen` bytes of the XOF output of the message there (`Out`), for any layout
`L` (`sponge_piece`). The calls are those of ML-KEM
(`Proof/MlKem/X86/Keccak.lean`), but for a message length and a padding
position that depend on the entry state (`absorb_piece'`, `pad_piece'`).
-/

namespace VG.Proof.MlDsa.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt Repr squeezeFrom shakeSuffix absorb pad rates)
open VG.Proof.MlKem.X86.Sample (cR E1 stateAt_zero zero_write toNat_off)
open VG.Impl.MlDsa.X86.Sample (argOp absArgs padArgs sqzArgs sponge)
open VG.Proof.MlKem (repr_nil shakeSuffix32 bytesAt_getD bytesAt_length)

/-! ## The Keccak calls, for lengths that depend on the entry state -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop}

/-- A call of `vg_keccak_absorb`, from position 0, of `len s₀` bytes. -/
theorem absorb_piece' (E S D W : State → BitVec 32) (rate : Nat) (len : State → Nat) (hr : rate ∈ rates)
    (hlen : ∀ s₀, Pre s₀ → len s₀ < 2 ^ 32)
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → AbsorbAt s (E s₀) (S s₀) (D s₀) (W s₀) rate 0 (len s₀))
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
      E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ D s₀ = D s₀' ∧ W s₀ = W s₀' ∧ len s₀ = len s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      (∀ msg, Repr s.mem ((S s₀).setWidth 64) rate msg → 0 = msg.length % rate →
        Repr s'.mem ((S s₀).setWidth 64) rate (msg ++ bytesAt s.mem ((D s₀).setWidth 64) (len s₀))) →
      B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith rs6 "vg_keccak_absorb_scratch" Impl.Sha3.X86.Stream.absorb) := by
  have hp0 : 0 < rate := by simp [rates] at hr; omega
  refine Piece.callWith Proof.Sha3.X86.Stream.Absorb.absorb_verified.1
    Proof.Sha3.X86.Stream.Absorb.absorb_verified.2.1 absorb_nosp (by decide) (by decide)
    (fun s₀ => [reg32 (D s₀) (len s₀)]) (fun s₀ => [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 24])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [absorb_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact absorb_pre h.esp h.args h.bufs h.fD h.dDS h.dDW h.bD hr hp0 (hlen s₀ h₀) h.cD h.cS h.cW
  · obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃, ← e₄, ← e₅] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨by rw [e₃, e₅], by rw [e₁, e₂, e₄], hsp,
      args6_eq (by rw [h.esp]; exact h.bufs.hE) hsp (absArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_)
      (absorb_post h.esp h.args hE (hlen s₀ h₀) (rate_lt hr) (by have := rate_lt hr; omega) h.bufs.bS h.bD post)
    rw [absorb_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

/-- A call of `vg_keccak_pad`, from position `pos s₀`. -/
theorem pad_piece' (E S W : State → BitVec 32) (rate : Nat) (pos : State → Nat) (sfx : Nat) (hr : rate ∈ rates)
    (hp : ∀ s₀, Pre s₀ → pos s₀ < rate)
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → PadAt s (E s₀) (S s₀) (W s₀) rate (pos s₀) sfx)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
      E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ W s₀ = W s₀' ∧ pos s₀ = pos s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      (∀ msg, Repr s.mem ((S s₀).setWidth 64) rate msg → pos s₀ = msg.length % rate →
        stateAt s'.mem ((S s₀).setWidth 64) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) →
      B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith rs5 "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) := by
  refine Piece.callWith Proof.Sha3.X86.Stream.Pad.pad_verified.1
    Proof.Sha3.X86.Stream.Pad.pad_verified.2.1 pad_nosp (by decide) (by decide)
    (fun _ => []) (fun s₀ => [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 20])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [pad_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact pad_pre h.esp h.args h.bufs hr (hp s₀ h₀) h.cS h.cW
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃, ← e₄] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨rfl, by rw [e₁, e₂, e₃], hsp,
      args5_eq (by rw [h.esp]; exact h.bufs.hE) hsp (padArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_)
      (pad_post h.esp h.args hE (rate_lt hr) (by have := rate_lt hr; have := hp s₀ h₀; omega) h.bufs.bS post)
    rw [pad_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

end

variable {L : VG.Proof.MlDsa.X86.Sample.Lay}

/-! ## `esi = scratch` -/

theorem ld_piece (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L) (fun s₀ s => s = P0 s₀) (VG.Proof.MlDsa.X86.Sample.Ctx L)
    (.block [.mov .esi (.mem (argOp L.iS))]) := by
  obtain ⟨_, ht⟩ := hL.tLd
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) ht
  · subst e
    have b₀ : VG.Proof.MlDsa.X86.Sample.Base L s₀ (P0 s₀) := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
    have a₂ := b₀.argEa (i := L.iS)
    have i₂ := b₀.argIn hp hL.iS
    have v₂ := VG.Proof.MlDsa.X86.Sample.args0 hp L.iS hL.iS
    apply WP.of_runBlock
    simp only [argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      State.load32, State.setReg, Option.map_some, a₂, i₂, v₂, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨⟨by simp, rfl, rfl, Frame.refl _ _⟩, fun i hi => by simpa using VG.Proof.MlDsa.X86.Sample.args0 hp i hi, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]


/-- The arguments are intact after changes to memory only within regions
apart from them. -/
theorem args_frame {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Pre L s₀) {m m' : Mem}
    (h : ∀ i < L.nA, m.readW (argAddr s₀ i) 32 = arg s₀ i) {rs : List Region} (fr : Frame rs m m')
    (hd : ∀ r ∈ rs, (L.gR s₀).Disjoint r) : ∀ i < L.nA, m'.readW (argAddr s₀ i) 32 = arg s₀ i :=
  fun i hi => by rw [fr.readW (VG.Proof.MlKem.X86.arg_contains hi hp.sp') hd (by decide)]; exact h i hi

/-! ## The Keccak state set to zero -/

/-- After `k` words. -/
structure ZInv (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ : State) (k : Nat) (s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.Ctx L s₀ s where
  ebx : s.gpr .ebx = L.sP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (50 - k)
  eax : s.gpr .eax = 0
  zero : ∀ j < 4 * k, s.mem (L.sA s₀ + BitVec.ofNat 64 j) = 0

theorem zinit_piece : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L) (VG.Proof.MlDsa.X86.Sample.Ctx L) (VG.Proof.MlDsa.X86.Sample.ZInv L · 0) (.block (zeroInit 0)) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [zeroInit, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.map_some, Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq,
    exists_eq_left']
  exact ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, by simp [h.esi], by simp, by simp,
    fun j hj => absurd hj (by omega)⟩

theorem zstep {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Pre L s₀) {k : Nat} (hk : k < 50) {s : State} (h : VG.Proof.MlDsa.X86.Sample.ZInv L s₀ k s) :
    WP isa (.block zeroBody) s fun s' => VG.Proof.MlDsa.X86.Sample.ZInv L s₀ (k + 1) s' ∧ VG.X86.eval .ne s' = some (decide (k + 1 < 50)) := by
  have hs := hp.s_fit
  have ea : (L.sP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 =
      L.sA s₀ + BitVec.ofNat 64 (4 * k) := by
    rw [ea_add (by omega)]; rfl
  have hin : InRegions s.wr (L.sA s₀ + BitVec.ofNat 64 (4 * k)) 4 := hp.inS h.wr (by omega)
  have fr : Frame [L.sR s₀] s.mem (s.mem.writeW (L.sA s₀ + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_at (by omega) hs)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, zeroBody, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.ea, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, h.ebx, ea, hin, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, ?_⟩, ?_, by simp [h.esi]⟩, ?_, ?_, by simp [h.eax], ?_⟩, ?_⟩
  · exact h.frame.writeW (r := L.sR s₀) (by simp) _ (contains_at (by omega) hs)
  · rw [h.eax]
    exact VG.Proof.MlDsa.X86.Sample.args_frame hp h.args fr (by simp only [List.mem_singleton, forall_eq]; exact hp.s_g.symm)
  · simp only [ite_true]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next hk
  · rw [h.eax]; exact zero_write h.zero
  · simp only [VG.X86.eval, h.ecx]
    exact cnt_ne hk (by omega)

theorem zloop_piece (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L) (VG.Proof.MlDsa.X86.Sample.ZInv L · 0) (VG.Proof.MlDsa.X86.Sample.ZInv L · 50) (.loop (.block zeroBody) .ne) :=
  Piece.countLoop (by decide) (fun k s₀ s => VG.Proof.MlDsa.X86.Sample.ZInv L s₀ k s) [.ebx]
    (fun k hk s₀ s hp h => VG.Proof.MlDsa.X86.Sample.zstep hp hk h)
    (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.ebx, h'.ebx, hq.sP hL]) (by taint_decide)

/-- `Ctx`, with the Keccak state zero. -/
structure Z (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.Ctx L s₀ s where
  st : stateAt s.mem (L.sA s₀) = Spec.Sha3.zero

theorem zero_piece (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L) (VG.Proof.MlDsa.X86.Sample.Ctx L) (VG.Proof.MlDsa.X86.Sample.Z L) (zeroSt 0) :=
  (Piece.seq VG.Proof.MlDsa.X86.Sample.zinit_piece (VG.Proof.MlDsa.X86.Sample.zloop_piece hL)).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨h.toCtx, stateAt_zero fun j hj => h.zero j (by omega)⟩


/-! ## Absorbing the message -/

theorem ml_ofNat {s₀ : State} : BitVec.ofNat 32 (L.ml s₀) =
    match L.mlen with | some k => BitVec.ofNat 32 k | none => arg s₀ 1 := by
  unfold Lay.ml; cases h : L.mlen <;> simp

theorem absArgs_piece (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L) (VG.Proof.MlDsa.X86.Sample.Z L)
    (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Z L s₀ s ∧ AbsArgs s (L.sP s₀) (L.dP s₀) (L.WW s₀) L.rate 0 (L.ml s₀))
    (.block (absArgs L.rate L.lenSrc)) := by
  obtain ⟨_, ht⟩ := hL.tAbs
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have a₀ := h.argEa (i := 0)
    have i₀ := h.argIn hp (i := 0) (by have := hL.one; omega)
    have v₀ := h.args 0 (by have := hL.one; omega)
    have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp (i := 1) hL.one
    have v₁ := h.args 1 hL.one
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
    have e := VG.Proof.MlDsa.X86.Sample.ml_ofNat (L := L) (s₀ := s₀)
    apply WP.of_runBlock
    cases hm : L.mlen with
    | some k =>
      rw [hm] at e
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, absArgs, Lay.lenSrc, hm, argOp, at_, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
        Option.map_some, Option.bind_some, a₀, i₀, v₀, Option.some.injEq, exists_eq_left']
      exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
        ⟨by simp [h.esi], rfl, rfl, rfl, by simp [e], by simp [h.esi]⟩⟩
    | none =>
      rw [hm] at e
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, absArgs, Lay.lenSrc, hm, argOp, at_, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
        Option.map_some, Option.bind_some, a₀, i₀, v₀, a₁, i₁, v₁, Option.some.injEq,
        exists_eq_left']
      exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
        ⟨by simp [h.esi], rfl, rfl, rfl, by simp [e], by simp [h.esi]⟩⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.e1]


/-- `Ctx` after a call of a Keccak function that changes memory only within
parts of `scratch` and the stack below the frame. -/
theorem Ctx.call {s₀ s s' : State} (hL : L.Ok) (hp : VG.Proof.MlDsa.X86.Sample.Pre L s₀) (h : VG.Proof.MlDsa.X86.Sample.Ctx L s₀ s) (e₁ : s'.rd = s.rd)
    (e₂ : s'.wr = s.wr) (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region}
    (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, r ∈ [reg32 (L.sP s₀) 200, reg32 (L.sP s₀ + BitVec.ofNat 32 840) L.outlen,
      reg32 (L.WW s₀) 640, below (VG.Proof.MlKem.X86.Sample.E1 s₀) 40]) : VG.Proof.MlDsa.X86.Sample.Ctx L s₀ s' := by
  have hs' := fun r hr => VG.Proof.MlDsa.X86.Sample.calls_sub hL hp r (hs r hr)
  refine ⟨h.toBase.call e₁ e₂ e₃ fr fun r hr => ?_, VG.Proof.MlDsa.X86.Sample.args_frame hp h.args fr fun r hr => ?_,
    by rw [e₃ .esi (by simp [calleeSaved]), h.esi]⟩
  · obtain ⟨r', h₁, h₂, -⟩ := hs' r hr; exact ⟨r', h₁, h₂⟩
  · obtain ⟨r', -, h₂, h₃⟩ := hs' r hr; exact h₃.symm.sub_right h₂

/-- `Ctx`, with the message absorbed. -/
structure A1 (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.Ctx L s₀ s where
  st : Repr s.mem (L.sA s₀) L.rate (L.Msg s₀)

theorem absorb_call (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L)
    (fun s₀ s => VG.Proof.MlDsa.X86.Sample.Z L s₀ s ∧ AbsArgs s (L.sP s₀) (L.dP s₀) (L.WW s₀) L.rate 0 (L.ml s₀)) (VG.Proof.MlDsa.X86.Sample.A1 L)
    (callWith rs6 "vg_keccak_absorb_scratch" Impl.Sha3.X86.Stream.absorb) := by
  refine VG.Proof.MlDsa.X86.Sample.absorb_piece' VG.Proof.MlKem.X86.Sample.E1 L.sP L.dP L.WW L.rate L.ml hL.rate
    (fun s₀ hp => by have := hp.ml_lt; have := rate_lt hL.rate; omega) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.e1, hq.sP hL, hq.dP hL, by rw [Lay.WW, Lay.WW, hq.sP hL], hq.ml hL⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · have hk := hp.kbufs
    have hs := hp.s_fit
    refine ⟨h.esp, ha, hk, hp.d_fit, ?_, ?_, (hp.stk_d.sub_left hp.c_sub), ?_, hp.within_s0 h.wr (by omega),
      hp.within_s h.wr (by omega) (by omega)⟩
    · rw [Pre.reg_s0]; exact hp.d_s.sub_right (hp.sub_s (by omega))
    · rw [hp.reg_s (by omega)]; exact hp.d_s.sub_right (hp.sub_s (by omega))
    · refine ⟨L.dR s₀, ?_, 0, (BitVec.add_zero _).symm, by simp⟩
      rw [h.rd, h.wr, pushed_rd, hp.rd]; simp
  · refine ⟨h.toCtx.call hL hp e₁ e₂ e₃ fr fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]
    · have := post [] (repr_nil h.st) (by simp)
      rwa [List.nil_append, h.msg hp] at this

/-! ## Padding -/

theorem padArgs_piece (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L) (VG.Proof.MlDsa.X86.Sample.A1 L)
    (fun s₀ s => VG.Proof.MlDsa.X86.Sample.A1 L s₀ s ∧ PadArgs s (L.sP s₀) (L.WW s₀) L.rate (L.ml s₀) 0x1f)
    (.block (padArgs L.rate L.lenSrc)) := by
  obtain ⟨_, ht⟩ := hL.tPad
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp (i := 1) hL.one
    have v₁ := h.args 1 hL.one
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    have e := VG.Proof.MlDsa.X86.Sample.ml_ofNat (L := L) (s₀ := s₀)
    apply WP.of_runBlock
    cases hm : L.mlen with
    | some k =>
      rw [hm] at e
      simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, padArgs, Lay.lenSrc, hm, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
        Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
      exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
        ⟨by simp [h.esi], rfl, by simp [e], rfl, by simp [h.esi]⟩⟩
    | none =>
      rw [hm] at e
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, padArgs, Lay.lenSrc, hm, argOp, at_, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
        Option.map_some, Option.bind_some, a₁, i₁, v₁, Option.some.injEq,
        exists_eq_left']
      exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
        ⟨by simp [h.esi], rfl, by simp [e], rfl, by simp [h.esi]⟩⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.e1]

/-- `Ctx`, with the message absorbed and padded for SHAKE. -/
structure A2 (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.Ctx L s₀ s where
  st : stateAt s.mem (L.sA s₀) = Proof.MlDsa.Sample.padded L.rate shakeSuffix (L.Msg s₀)

theorem pad_call (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L)
    (fun s₀ s => VG.Proof.MlDsa.X86.Sample.A1 L s₀ s ∧ PadArgs s (L.sP s₀) (L.WW s₀) L.rate (L.ml s₀) 0x1f) (VG.Proof.MlDsa.X86.Sample.A2 L)
    (callWith rs5 "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) := by
  refine VG.Proof.MlDsa.X86.Sample.pad_piece' VG.Proof.MlKem.X86.Sample.E1 L.sP L.WW L.rate L.ml 0x1f hL.rate (fun s₀ hp => hp.ml_lt) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.e1, hq.sP hL, by rw [Lay.WW, Lay.WW, hq.sP hL], hq.ml hL⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · exact ⟨h.esp, ha, hp.kbufs, hp.within_s0 h.wr (by omega), hp.within_s h.wr (by omega) (by omega)⟩
  · refine ⟨h.toCtx.call hL hp e₁ e₂ e₃ fr fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]
    · have := post (L.Msg s₀) h.st (by
        rw [bytesAt_length, Nat.mod_eq_of_lt hp.ml_lt])
      rwa [show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32] at this

/-! ## Squeezing -/

theorem sqArgs_piece (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L) (VG.Proof.MlDsa.X86.Sample.A2 L)
    (fun s₀ s => VG.Proof.MlDsa.X86.Sample.A2 L s₀ s ∧
      AbsArgs s (L.sP s₀) (L.sP s₀ + BitVec.ofNat 32 840) (L.WW s₀) L.rate 0 L.outlen)
    (.block (sqzArgs L.rate L.outlen)) := by
  obtain ⟨_, ht⟩ := hL.tSqz
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, sqzArgs, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
    ⟨by simp [h.esi], rfl, rfl, by simp [h.esi], rfl, by simp [h.esi]⟩⟩

/-- `Ctx`, with the first `outlen` bytes of the XOF output of the message at
`scratch + 840`. -/
structure Out (L : VG.Proof.MlDsa.X86.Sample.Lay) (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.Ctx L s₀ s where
  out : ∀ p < L.outlen, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = (L.out s₀).getD p 0

theorem squeeze_call (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L)
    (fun s₀ s => VG.Proof.MlDsa.X86.Sample.A2 L s₀ s ∧
      AbsArgs s (L.sP s₀) (L.sP s₀ + BitVec.ofNat 32 840) (L.WW s₀) L.rate 0 L.outlen) (VG.Proof.MlDsa.X86.Sample.Out L)
    (callWith rs6 "vg_keccak_squeeze_scratch" Impl.Sha3.X86.Stream.squeeze) := by
  have ho := hL.out
  refine squeeze_piece VG.Proof.MlKem.X86.Sample.E1 L.sP (fun s₀ => L.sP s₀ + BitVec.ofNat 32 840) L.WW L.rate 0 L.outlen hL.rate
    (by omega) (by omega) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.e1, hq.sP hL, by rw [hq.sP hL], by rw [Lay.WW, Lay.WW, hq.sP hL]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr r₁ _ => ?_)
  · have hs := hp.s_fit
    refine ⟨h.esp, ha, hp.kbufs, by rw [VG.Proof.MlKem.X86.Sample.toNat_off (by omega)]; omega, ?_, ?_, ?_,
      hp.within_s0 h.wr (by omega), hp.within_s h.wr (by omega) (by omega),
      hp.within_s h.wr (by omega) (by omega)⟩
    · rw [hp.reg_s (by omega), Pre.reg_s0]
      exact VG.Proof.MlKem.X86.Sample.disj_at (len := 2048) (by omega) (by omega) hs (by omega)
    · rw [hp.reg_s (by omega), hp.reg_s (by omega)]
      exact VG.Proof.MlKem.X86.Sample.disj_at (len := 2048) (by omega) (by omega) hs (by omega)
    · rw [hp.reg_s (by omega)]
      exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))
  · refine ⟨h.toCtx.call hL hp e₁ e₂ e₃ fr fun r hr => ?_, fun p hp' => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h]
    · rw [h.st, hp.off_eq (by omega)] at r₁
      have e := bytesAt_getD s'.mem (L.sA s₀ + BitVec.ofNat 64 840) (len := L.outlen) hp'
      rw [r₁, BitVec.add_assoc, ← BitVec.ofNat_add] at e
      exact e.symm

/-! ## The whole sponge -/

theorem sponge_piece (hL : L.Ok) : Piece (VG.Proof.MlDsa.X86.Sample.Pre L) (VG.Proof.MlDsa.X86.Sample.PubP L) (fun s₀ s => s = P0 s₀) (VG.Proof.MlDsa.X86.Sample.Out L)
    (sponge L.iS L.rate L.lenSrc L.outlen) :=
  Piece.seq (VG.Proof.MlDsa.X86.Sample.ld_piece hL) <| Piece.seq (VG.Proof.MlDsa.X86.Sample.zero_piece hL) <| Piece.seq (VG.Proof.MlDsa.X86.Sample.absArgs_piece hL) <|
    Piece.seq (VG.Proof.MlDsa.X86.Sample.absorb_call hL) <| Piece.seq (VG.Proof.MlDsa.X86.Sample.padArgs_piece hL) <| Piece.seq (VG.Proof.MlDsa.X86.Sample.pad_call hL) <|
    Piece.seq (VG.Proof.MlDsa.X86.Sample.sqArgs_piece hL) (VG.Proof.MlDsa.X86.Sample.squeeze_call hL)

end VG.Proof.MlDsa.X86.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_rej_ntt_poly`

The body is the SHAKE128 output of the seed at `scratch + 840` (`sponge_piece`),
then the 336 iterations of the loop, iteration `t` of which starts with the
coefficients `LA B t = rnFold [] ((G(B, 1008)).take (3t))`
(`Proof/MlDsa/Sample/RejNtt.lean`) stored at `a`, `edi` after them and `ecx`
counting them (`Loop`); the end returns whether there are 256. An iteration
computes the value of its 3 bytes in `eax` (`load_piece`) and, while there are
fewer than 256 coefficients, stores it if it is less than `q` (`try_piece`); its
branches depend on the XOF output, a function of the seed, and so agree in two
runs from the same seed (`Pub`), which the contract lets the function leak.
-/

namespace VG.Proof.MlDsa.X86.Sample.RejNtt

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp rnLoad rnTry rnBody rnInit retJ qImm)
open VG.Spec.MlDsa (Zq q G n)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Sample (cR E1)

/-- The layout: `rejNTT(seed, a, scratch)`, 34 bytes of seed, 1008 bytes of
SHAKE128. -/
def L : VG.Proof.MlDsa.X86.Sample.Lay := { nA := 3, iA := 1, iS := 2, rate := 168, outlen := 1008, mlen := some 34 }

theorem hL : L.Ok :=
  ⟨by decide, by decide, by decide, by decide, by decide, fun k hk => by cases hk; decide,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The pointers, `esp` and the seed agree. -/
def Pub (s₀ s₀' : State) : Prop := VG.Proof.MlDsa.X86.Sample.PubP VG.Proof.MlDsa.X86.Sample.RejNtt.L s₀ s₀' ∧ L.Msg s₀ = L.Msg s₀'

/-! ## The XOF output and the coefficients it gives -/

/-- The XOF output of the seed `B`. -/
abbrev X (B : List Byte) : List Byte := VG.Spec.MlDsa.G B 1008

/-- Byte `k` of it. -/
abbrev xb (B : List Byte) (k : Nat) : Byte := (VG.Proof.MlDsa.X86.Sample.RejNtt.X B).getD k 0

/-- The coefficients sampled after `t` iterations. -/
abbrev LA (B : List Byte) (t : Nat) : List Zq := rnFold [] ((VG.Proof.MlDsa.X86.Sample.RejNtt.X B).take (3 * t))

/-- The value of the 3 bytes of iteration `t`. -/
abbrev z (B : List Byte) (t : Nat) : Nat := rnZ (VG.Proof.MlDsa.X86.Sample.RejNtt.xb B (3 * t)) (VG.Proof.MlDsa.X86.Sample.RejNtt.xb B (3 * t + 1)) (VG.Proof.MlDsa.X86.Sample.RejNtt.xb B (3 * t + 2))

theorem out_eq (s₀ : State) : L.out s₀ = VG.Proof.MlDsa.X86.Sample.RejNtt.X (L.Msg s₀) := (VG.Proof.MlDsa.Sample.G_eq _ _).symm

theorem X_length (B : List Byte) : (VG.Proof.MlDsa.X86.Sample.RejNtt.X B).length = 1008 := VG.Proof.MlDsa.Sample.G_length _ _

theorem take_add_three (M : List Byte) {i : Nat} (h : i + 3 ≤ M.length) :
    M.take (i + 3) = M.take i ++ [M.getD i 0, M.getD (i + 1) 0, M.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < M.length by omega), List.getElem?_eq_getElem (show i + 1 < M.length by omega),
    List.getElem?_eq_getElem (show i + 2 < M.length by omega), Option.getD_some]

theorem LA_succ (B : List Byte) {t : Nat} (ht : t < 336) :
    VG.Proof.MlDsa.X86.Sample.RejNtt.LA B (t + 1) = rnStep (VG.Proof.MlDsa.X86.Sample.RejNtt.LA B t) (VG.Proof.MlDsa.X86.Sample.RejNtt.xb B (3 * t)) (VG.Proof.MlDsa.X86.Sample.RejNtt.xb B (3 * t + 1)) (VG.Proof.MlDsa.X86.Sample.RejNtt.xb B (3 * t + 2)) := by
  simp only [VG.Proof.MlDsa.X86.Sample.RejNtt.LA]
  rw [show 3 * (t + 1) = 3 * t + 3 by omega, VG.Proof.MlDsa.X86.Sample.RejNtt.take_add_three _ (by rw [VG.Proof.MlDsa.X86.Sample.RejNtt.X_length]; omega),
    rnFold_snoc _ (by rw [List.length_take, VG.Proof.MlDsa.X86.Sample.RejNtt.X_length]; omega)]

theorem LA_zero (B : List Byte) : VG.Proof.MlDsa.X86.Sample.RejNtt.LA B 0 = [] := by simp [VG.Proof.MlDsa.X86.Sample.RejNtt.LA, rnFold]

theorem LA_length_le (B : List Byte) (t : Nat) : (VG.Proof.MlDsa.X86.Sample.RejNtt.LA B t).length ≤ 256 := rnFold_length_le (by simp) _

theorem z_lt (B : List Byte) (t : Nat) : VG.Proof.MlDsa.X86.Sample.RejNtt.z B t < 2 ^ 23 := by
  have := (VG.Proof.MlDsa.X86.Sample.RejNtt.xb B (3 * t)).isLt
  have := (VG.Proof.MlDsa.X86.Sample.RejNtt.xb B (3 * t + 1)).isLt
  have := Nat.mod_lt (VG.Proof.MlDsa.X86.Sample.RejNtt.xb B (3 * t + 2)).toNat (show 128 > 0 by decide)
  simp only [VG.Proof.MlDsa.X86.Sample.RejNtt.z, rnZ]; omega

/-! ## The state of the loop -/

/-- After `t` iterations, with the coefficients `La` stored. -/
structure Loop (s₀ : State) (t : Nat) (La : List Zq) (s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.Base VG.Proof.MlDsa.X86.Sample.RejNtt.L s₀ s where
  out : ∀ p < 1008, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) p
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (840 + 3 * t)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (336 - t)
  len : La.length ≤ 256
  edi : s.gpr .edi = L.aP s₀ + BitVec.ofNat 32 (4 * La.length)
  ecx : s.gpr .ecx = BitVec.ofNat 32 La.length
  stored : Stored s.mem (L.aA s₀) La

/-- Within iteration `t`, with the value of its 3 bytes in `eax`. -/
structure Mid (s₀ : State) (t : Nat) (La : List Zq) (s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t La s where
  eax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Sample.RejNtt.z (L.Msg s₀) t)

theorem Loop.flags {s₀ s s' : State} {t : Nat} {La : List Zq} (h : VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t La s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t La s' :=
  ⟨⟨by rw [hg, h.esp], by rw [hr, h.rd], by rw [hw, h.wr], by rw [hm]; exact h.frame⟩,
    by rw [hm]; exact h.out, by rw [hg, h.esi], by rw [hg, h.ebp], h.len, by rw [hg, h.edi], by rw [hg, h.ecx],
    by rw [hm]; exact h.stored⟩

theorem Mid.flags {s₀ s s' : State} {t : Nat} {La : List Zq} (h : VG.Proof.MlDsa.X86.Sample.RejNtt.Mid s₀ t La s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : VG.Proof.MlDsa.X86.Sample.RejNtt.Mid s₀ t La s' :=
  ⟨h.toLoop.flags hg hm hr hw, by rw [hg, h.eax]⟩

theorem linit_piece : Piece (VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L) VG.Proof.MlDsa.X86.Sample.RejNtt.Pub (VG.Proof.MlDsa.X86.Sample.Out VG.Proof.MlDsa.X86.Sample.RejNtt.L) (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ 0 (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 0) s) (.block rnInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp (i := 1) (by decide)
    have v₁ := h.args 1 (by decide)
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, rnInit, argOp, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.map_some,
      Option.bind_some, a₁, i₁, v₁, Option.some.injEq, exists_eq_left']
    rw [VG.Proof.MlDsa.X86.Sample.RejNtt.LA_zero]
    refine ⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, fun p hp' => ?_, by simp [h.esi], rfl,
      by simp, by simp; rfl, by simp, stored_nil _ _⟩
    rw [h.out p hp', VG.Proof.MlDsa.X86.Sample.RejNtt.out_eq]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.1.e1]

/-! ## The value of the 3 bytes -/

theorem load_ok {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L s₀) {t : Nat} (ht : t < 336) {s : State}
    (h : VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t) s) :
    WP isa (.block rnLoad) s fun s' => VG.Proof.MlDsa.X86.Sample.RejNtt.Mid s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t) s' ∧
      VG.X86.eval .b s' = some (decide ((VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t).length < 256)) := by
  have hs := hp.s_fit
  have eb : ∀ o < 3, (L.sP s₀ + BitVec.ofNat 32 (840 + 3 * t) + BitVec.ofNat 32 o).setWidth 64 =
      L.sA s₀ + BitVec.ofNat 64 (840 + (3 * t + o)) := fun o ho => by
    rw [ea_add (by simp only [VG.Proof.MlDsa.X86.Sample.RejNtt.L] at hs ⊢; omega), Nat.add_assoc]
  have e0 := eb 0 (by omega)
  have e1 := eb 1 (by omega)
  have e2 := eb 2 (by omega)
  have i0 := hp.inS' h.wr (o := 840 + (3 * t + 0)) (n := 1) (by omega)
  have i1 := hp.inS' h.wr (o := 840 + (3 * t + 1)) (n := 1) (by omega)
  have i2 := hp.inS' h.wr (o := 840 + (3 * t + 2)) (n := 1) (by omega)
  have v0 := h.out (3 * t + 0) (by omega)
  have v1 := h.out (3 * t + 1) (by omega)
  have v2 := h.out (3 * t + 2) (by omega)
  simp only [Nat.add_zero] at e0 i0 v0
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reducePow, and_self, rnLoad, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.esi, e0, e1, e2, i0, i1, i2, v0, v1, v2,
    Option.some.injEq, exists_eq_left']
  have hz : (BitVec.setWidth 32 (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t)) +
      (BitVec.setWidth 32 (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t + 1))).rotateRight 24 +
      (BitVec.setWidth 32 (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t + 2)) &&& 127).rotateRight 16).toNat = VG.Proof.MlDsa.X86.Sample.RejNtt.z (L.Msg s₀) t := by
    have l0 := (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t)).isLt
    have l1 := (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t + 1)).isLt
    have l2 := (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t + 2)).isLt
    have hm : (BitVec.setWidth 32 (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t + 2)) &&& 127).toNat =
        (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t + 2)).toNat % 128 := by
      rw [show (127 : BitVec 32) = BitVec.ofNat 32 (2 ^ 7 - 1) from rfl, toNat_and_mask _ _ (by decide),
        toNat_byte32]
    have hm' : (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t + 2)).toNat % 128 < 128 := Nat.mod_lt _ (by decide)
    rw [BitVec.toNat_add, BitVec.toNat_add,
      rotr_small (BitVec.setWidth 32 (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t + 2)) &&& 127) (by decide) (by decide)
        (by rw [hm]; omega), hm,
      rotr_small (BitVec.setWidth 32 (VG.Proof.MlDsa.X86.Sample.RejNtt.xb (L.Msg s₀) (3 * t + 1))) (by decide) (by decide)
        (by rw [toNat_byte32]; omega), toNat_byte32, toNat_byte32]
    simp only [VG.Proof.MlDsa.X86.Sample.RejNtt.z, rnZ]
    omega
  have hl := h.len
  refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ebp], h.len,
    by simp [h.edi], by simp [h.ecx], h.stored⟩, eq_ofNat_of_toNat hz⟩, ?_⟩
  simp only [VG.X86.eval, h.ecx, toNat_ofNat32 (show (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t).length < 2 ^ 32 by omega)]
  rfl

theorem load_piece (t : Nat) (ht : t < 336) :
    Piece (VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L) VG.Proof.MlDsa.X86.Sample.RejNtt.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t) s) (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Mid s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t) s ∧
      VG.X86.eval .b s = some (decide ((VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t).length < 256))) (.block rnLoad) :=
  Piece.taint [.esi] (fun s₀ s hp h => VG.Proof.MlDsa.X86.Sample.RejNtt.load_ok hp ht h)
    (fun s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esi, h'.esi, hq.1.sP VG.Proof.MlDsa.X86.Sample.RejNtt.hL]) (by taint_decide)

/-! ## Storing the value -/

theorem zw_ofNat {v : Nat} (hv : v < q) : zw (Fin.ofNat q v) = BitVec.ofNat 32 v := by
  simp only [zw, Fin.val_ofNat, Nat.mod_eq_of_lt hv]

theorem store_ok {s₀ : State} (hp : VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L s₀) {t : Nat} {La : List Zq} {v : Nat} (hv : v < q)
    (hl : La.length < 256) {s : State} (h : VG.Proof.MlDsa.X86.Sample.RejNtt.Mid s₀ t La s) (hrv : s.gpr .eax = BitVec.ofNat 32 v) :
    WP isa (.block [.store (at_ .edi 0) .eax, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]) s
      fun s' => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t (La ++ [Fin.ofNat q v]) s' := by
  have ha := hp.a_fit
  have ea : (L.aP s₀ + BitVec.ofNat 32 (4 * La.length) + BitVec.ofNat 32 0).setWidth 64 =
      coeffAddr (L.aA s₀) La.length := by
    rw [ea_add (by simp only [VG.Proof.MlDsa.X86.Sample.RejNtt.L] at ha ⊢; omega)]; rfl
  have hin : InRegions s.wr (coeffAddr (L.aA s₀) La.length) 4 := hp.inA h.wr hl
  have fa : Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) La.length) (BitVec.ofNat 32 v)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hl)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, h.edi, ea, hin,
    hrv, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, h.frame.writeW (r := L.aR s₀) (by simp) _
    (coeff_contains _ hl)⟩, fun p hp' => ?_, by simp [h.esi], by simp [h.ebp],
    (by simp only [List.length_append, List.length_singleton]; omega), ?_, ?_, ?_⟩
  · refine (fa _ fun r hr hc => ?_).trans (h.out p hp')
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.a_s _ hc ((hp.sub_s (o := 840 + p) (n := 1) (by omega)) _ (Region.contains_self _ _))
  · simp only [ite_true, List.length_append, List.length_singleton]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx, List.length_append, List.length_singleton]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
  · have := stored_snoc h.stored hl (Fin.ofNat q v)
    rwa [VG.Proof.MlDsa.X86.Sample.RejNtt.zw_ofNat hv] at this

theorem LA_then {B : List Byte} {t : Nat} (ht : t < 336) (hl : (VG.Proof.MlDsa.X86.Sample.RejNtt.LA B t).length < 256) (hz : VG.Proof.MlDsa.X86.Sample.RejNtt.z B t < q) :
    VG.Proof.MlDsa.X86.Sample.RejNtt.LA B t ++ [Fin.ofNat q (VG.Proof.MlDsa.X86.Sample.RejNtt.z B t)] = VG.Proof.MlDsa.X86.Sample.RejNtt.LA B (t + 1) := by
  rw [VG.Proof.MlDsa.X86.Sample.RejNtt.LA_succ B ht, rnStep, ifT (by simp only [VG.Spec.MlDsa.n]; omega), ifT hz]

theorem LA_else {B : List Byte} {t : Nat} (ht : t < 336) (hz : ¬ (VG.Proof.MlDsa.X86.Sample.RejNtt.z B t < q)) : VG.Proof.MlDsa.X86.Sample.RejNtt.LA B t = VG.Proof.MlDsa.X86.Sample.RejNtt.LA B (t + 1) := by
  rw [VG.Proof.MlDsa.X86.Sample.RejNtt.LA_succ B ht, rnStep]
  split <;> rfl

theorem LA_full {B : List Byte} {t : Nat} (ht : t < 336) (hl : ¬ (VG.Proof.MlDsa.X86.Sample.RejNtt.LA B t).length < 256) :
    VG.Proof.MlDsa.X86.Sample.RejNtt.LA B t = VG.Proof.MlDsa.X86.Sample.RejNtt.LA B (t + 1) := by
  rw [VG.Proof.MlDsa.X86.Sample.RejNtt.LA_succ B ht, rnStep, ifF (by simp only [VG.Spec.MlDsa.n]; omega)]

theorem nil_piece {Pre' : State → Prop} {Pub' : State → State → Prop} {A B : State → State → Prop}
    (h : ∀ s₀ s, Pre' s₀ → A s₀ s → B s₀ s) : Piece Pre' Pub' A B (.block []) :=
  Piece.taint [] (fun s₀ s hp ha => WP.block_nil_iff.mpr (h s₀ s hp ha))
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

theorem try_piece (t : Nat) (ht : t < 336) :
    Piece (VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L) VG.Proof.MlDsa.X86.Sample.RejNtt.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Mid s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t) s ∧ (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t).length < 256)
      (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) (t + 1)) s) rnTry := by
  refine Piece.seq (B := fun s₀ s => (VG.Proof.MlDsa.X86.Sample.RejNtt.Mid s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t) s ∧ (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t).length < 256) ∧
      VG.X86.eval .b s = some (decide (VG.Proof.MlDsa.X86.Sample.RejNtt.z (L.Msg s₀) t < q))) ?_
    (Piece.ite (fun s₀ => decide (VG.Proof.MlDsa.X86.Sample.RejNtt.z (L.Msg s₀) t < q)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.2]) ?_ ?_)
  · refine Piece.taint [] (fun s₀ s hp ha => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    obtain ⟨h, hl⟩ := ha
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨h.flags rfl rfl rfl rfl, hl⟩, ?_⟩
    have := VG.Proof.MlDsa.X86.Sample.RejNtt.z_lt (L.Msg s₀) t
    simp only [VG.X86.eval, h.eax, toNat_ofNat32 (show VG.Proof.MlDsa.X86.Sample.RejNtt.z (L.Msg s₀) t < 2 ^ 32 by omega)]
    rfl
  · refine Piece.taint [.edi] (fun s₀ s hp ⟨⟨⟨h, hl⟩, _⟩, hb⟩ => ?_)
      (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨h, _⟩, _⟩, _⟩ ⟨⟨⟨h', _⟩, _⟩, _⟩ r hr => ?_) (by taint_decide)
    · have hq : VG.Proof.MlDsa.X86.Sample.RejNtt.z (L.Msg s₀) t < q := of_decide_eq_true hb
      exact (VG.Proof.MlDsa.X86.Sample.RejNtt.store_ok hp hq hl h h.eax).mono fun s' h' => VG.Proof.MlDsa.X86.Sample.RejNtt.LA_then ht hl hq ▸ h'
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.1.aP VG.Proof.MlDsa.X86.Sample.RejNtt.hL, hq.2]
  · exact VG.Proof.MlDsa.X86.Sample.RejNtt.nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => VG.Proof.MlDsa.X86.Sample.RejNtt.LA_else ht (of_decide_eq_false hb) ▸ h.toLoop

theorem end_ok {s₀ : State} {t : Nat} (ht : t < 336) {La : List Zq} {s : State} (h : VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t La s) :
    WP isa (.block [.alu .add .esi (.imm 3), .alu .sub .ebp (.imm 1)]) s
      fun s' => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ (t + 1) La s' ∧ VG.X86.eval .ne s' = some (decide (t + 1 < 336)) := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, ?_, ?_, h.len, by simp [h.edi], by simp [h.ecx],
    h.stored⟩, ?_⟩
  · simp only [ite_true, h.esi]
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ebp]
    exact cnt_next ht
  · simp only [VG.X86.eval, h.ebp]
    exact cnt_ne ht (by omega)

/-! ## An iteration, and the loop -/

theorem body_piece (t : Nat) (ht : t < 336) :
    Piece (VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L) VG.Proof.MlDsa.X86.Sample.RejNtt.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t) s)
      (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ (t + 1) (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) (t + 1)) s ∧ VG.X86.eval .ne s = some (decide (t + 1 < 336)))
      rnBody := by
  refine Piece.seq (VG.Proof.MlDsa.X86.Sample.RejNtt.load_piece t ht) (Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) (t + 1)) s) ?_
    (Piece.taint [] (fun s₀ s _ h => VG.Proof.MlDsa.X86.Sample.RejNtt.end_ok ht h) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)))
  refine Piece.ite (fun s₀ => decide ((VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t).length < 256)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.2]) ?_ ?_
  · exact (VG.Proof.MlDsa.X86.Sample.RejNtt.try_piece t ht).mono (fun _ _ _ ⟨⟨h, _⟩, hb⟩ => ⟨h, of_decide_eq_true hb⟩) fun _ _ _ h => h
  · exact VG.Proof.MlDsa.X86.Sample.RejNtt.nil_piece fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => VG.Proof.MlDsa.X86.Sample.RejNtt.LA_full ht (of_decide_eq_false hb) ▸ h.toLoop

theorem loop_piece : Piece (VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L) VG.Proof.MlDsa.X86.Sample.RejNtt.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ 0 (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 0) s)
    (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ 336 (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 336) s) (.loop rnBody .ne) :=
  Piece.loop (fun t s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ t (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) t) s) (by decide) fun t ht => VG.Proof.MlDsa.X86.Sample.RejNtt.body_piece t ht

/-- The end: 1 in `eax` if there are 256 coefficients, 0 if fewer. -/
structure Fin (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ 336 (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 336) s where
  eax : s.gpr .eax = BitVec.ofNat 32 ((VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 336).length / 256)

theorem fin_piece : Piece (VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L) VG.Proof.MlDsa.X86.Sample.RejNtt.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ 336 (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 336) s) VG.Proof.MlDsa.X86.Sample.RejNtt.Fin
    (.block (retJ .ecx)) := by
  refine Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hl := h.len
  refine wp_movr (wp_shr (by decide) (by decide) fun s' o e => WP.block_nil_iff.mpr ?_)
  have g : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => by
    rw [o.gpr r (by simp [hr])]; simp [State.setReg, hr]
  refine ⟨⟨⟨by rw [g _ (by decide), h.esp], by rw [o.rd]; exact h.rd, by rw [o.wr]; exact h.wr,
    by rw [o.mem]; exact h.frame⟩, by rw [o.mem]; exact h.out, by rw [g _ (by decide), h.esi],
    by rw [g _ (by decide), h.ebp], h.len, by rw [g _ (by decide), h.edi], by rw [g _ (by decide), h.ecx],
    by rw [o.mem]; exact h.stored⟩, ?_⟩
  rw [e]
  simp only [State.setReg, ite_true, h.ecx]
  exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (show (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 336).length < 2 ^ 32 by omega)])

end VG.Proof.MlDsa.X86.Sample.RejNtt

namespace VG.Proof.MlDsa.X86.Sample.RejNtt

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (rnBody rnInit retJ sponge)
open VG.Spec.MlDsa (Zq q G n)
open VG.Spec.Sha3 (bytesAt)

/-! ## The whole function -/

theorem main_piece : Piece (VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L) VG.Proof.MlDsa.X86.Sample.RejNtt.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Sample.RejNtt.Fin
    (.seq (sponge 2 168 (.imm 34) 1008) (.seq (.block rnInit) (.seq (.loop rnBody .ne) (.block (retJ .ecx))))) :=
  Piece.seq ((VG.Proof.MlDsa.X86.Sample.sponge_piece VG.Proof.MlDsa.X86.Sample.RejNtt.hL).pre_mono (fun _ h => h) fun _ _ _ _ h => h.1) <|
    Piece.seq VG.Proof.MlDsa.X86.Sample.RejNtt.linit_piece <| Piece.seq VG.Proof.MlDsa.X86.Sample.RejNtt.loop_piece VG.Proof.MlDsa.X86.Sample.RejNtt.fin_piece

theorem piece : Piece (VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L) VG.Proof.MlDsa.X86.Sample.RejNtt.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Sample.RejNtt.Fin s₀) s₀ s')
    Impl.MlDsa.X86.Sample.rejNTT :=
  Piece.leaf L.W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨by have := hp.sp; omega, by have := hp.sp'; omega⟩)
    (fun _ hp => hp.hW) (fun _ _ _ _ hq => hq.1.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem Pre.of {s₀ : State} (h : (Spec.MlDsa.rejNTTContract X86.abi 56).pre s₀) : VG.Proof.MlDsa.X86.Sample.Pre VG.Proof.MlDsa.X86.Sample.RejNtt.L s₀ := by
  sig_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, show (34 : Nat) < 168 by decide⟩

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂ :=
  VG.Proof.MlKem.map_toNat_inj

/-- The coefficients at `a`, when there are 256. -/
theorem poly_eq {s₀ s : State} (h : VG.Proof.MlDsa.X86.Sample.RejNtt.Loop s₀ 336 (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 336) s) (hl : (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 336).length = 256) :
    Spec.MlDsa.PolyIs s.mem (L.aA s₀) (toPoly (rnFold [] (VG.Spec.MlDsa.G (L.Msg s₀) 1008))) := by
  have e : VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 336 = rnFold [] (VG.Spec.MlDsa.G (L.Msg s₀) 1008) := by
    simp only [VG.Proof.MlDsa.X86.Sample.RejNtt.LA]; rw [List.take_of_length_le (by rw [VG.Proof.MlDsa.X86.Sample.RejNtt.X_length])]
  rw [← e]
  exact stored_polyIs h.stored hl

/-- Memory with the arguments `0`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Sample.rejNTT (Spec.MlDsa.rejNTTContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := h
    refine ⟨⟨e₁, fun i hi => ?_⟩, VG.Proof.MlDsa.X86.Sample.RejNtt.map_toNat_inj e₂⟩
    match i, hi with
    | 0, _ => exact e₃
    | 1, _ => exact e₄
    | 2, _ => exact e₅
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have hl := hfin.len
    by_cases e : (VG.Proof.MlDsa.X86.Sample.RejNtt.LA (L.Msg s₀) 336).length = 256
    · have hp := VG.Proof.MlDsa.X86.Sample.RejNtt.poly_eq hfin.toLoop e
      have hf : (rnFold [] (VG.Spec.MlDsa.G (L.Msg s₀) 1008)).length = 256 := by
        simp only [VG.Proof.MlDsa.X86.Sample.RejNtt.LA] at e; rwa [List.take_of_length_le (by rw [VG.Proof.MlDsa.X86.Sample.RejNtt.X_length])] at e
      rw [e]
      refine ⟨fun _ => hp.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejNTT := 1008 }, ?_⟩⟩
      show Spec.MlDsa.rejNTTPoly 1008 (L.Msg s₀) = some (Spec.MlDsa.polyAt s.mem (L.aA s₀))
      rw [rejNTT_some hf, hp.2]
    · rw [Nat.div_eq_of_lt (by omega)]
      have hf : (rnFold [] (VG.Spec.MlDsa.G (L.Msg s₀) 1008)).length ≠ 256 := by
        simp only [VG.Proof.MlDsa.X86.Sample.RejNtt.LA] at e; rwa [List.take_of_length_le (by rw [VG.Proof.MlDsa.X86.Sample.RejNtt.X_length])] at e
      exact ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide),
        .inr ⟨rfl, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
  · let st := VG.Proof.MlKem.X86.satState VG.Proof.MlDsa.X86.Sample.RejNtt.satMem [⟨0, 34⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 12⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlDsa.X86.Sample.RejNtt

end
