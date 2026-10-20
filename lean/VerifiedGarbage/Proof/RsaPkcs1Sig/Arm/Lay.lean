module

import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Wrap
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The ARMv7 PKCS #1 v1.5 functions: where everything is

`Lay`: what two runs share of where things are: the frame's base `B` (the
stack pointer in the body), its size `F`, the bytes `A` of the stack
arguments, the arguments `argv`, and the buffers the function only reads
(`ro`) and writes (`rw`). Above the frame are the push (`PUSH`, holding the
register arguments, `Impl/RsaPkcs1Sig/Arm/Wrap.lean`) and the stack
arguments (`ARGS`); below it, the `C` bytes the calls' frames use (`LOW`,
56 bytes unless a callee needs more).

`Lay.Ok L σ`: the state `σ` the body starts from has that layout.
`Lay.St L σ s`: a state of the body: `σ`'s stack pointer and permissions,
and memory changed only within the frame, the writable buffers and `LOW`
(`W`). The arguments, in the push and above it, stay as they were
(`St.arg`), and so do the buffers only read (`St.ro`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm

open VG VG.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd)

structure Lay where
  B : BitVec 32
  F : Nat
  A : Nat
  argv : List (BitVec 32)
  ro : List Region
  rw : List Region
  C : Nat := 56

namespace Lay

variable (L : Lay)

abbrev Q : Addr := State.addr L.B
abbrev fr (d : Nat) : Addr := L.Q + BitVec.ofNat 64 d
abbrev FR : Region := ⟨L.Q, L.F⟩
abbrev PUSH : Region := ⟨L.fr L.F, 56⟩
abbrev ARGS : Region := ⟨L.fr (L.F + 56), L.A⟩
abbrev LOW : Region := ⟨L.Q - BitVec.ofNat 64 L.C, L.C⟩
abbrev STK : Region := ⟨L.Q - BitVec.ofNat 64 L.C, L.C + L.F + 56⟩
/-- What the body may write. -/
abbrev W : List Region := L.FR :: L.rw ++ [L.LOW]
/-- Argument `j`'s place. -/
abbrev argA (j : Nat) : Addr := L.fr (Impl.RsaPkcs1Sig.Arm.argOff L.F j)

structure Ok (σ : State) : Prop where
  sp : σ.sp = L.B
  rd : σ.rd = L.ro ++ [L.ARGS]
  wr : σ.wr = L.FR :: L.PUSH :: L.rw
  B56 : L.C ≤ L.B.toNat
  fit : L.B.toNat + L.F + 56 + L.A ≤ 2 ^ 32
  F8 : 8 ≤ L.F
  nargs : L.argv.length = 4 + L.A / 4
  A4 : L.A % 4 = 0
  stk : ∀ r ∈ L.ro ++ L.rw, L.STK.Disjoint r
  wro : ∀ w ∈ L.rw, ∀ r ∈ L.ro ++ [L.ARGS], w.Disjoint r
  wrw : L.rw.Pairwise Region.Disjoint
  fits : ∀ r ∈ L.ro ++ L.rw, r.base.toNat + r.len ≤ 2 ^ 32
  args : ∀ j < L.argv.length, σ.mem.readW (L.argA j) 32 = L.argv.getD j 0

structure St (σ s : State) : Prop where
  ok : L.Ok σ
  sp : s.sp = L.B
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame L.W σ.mem s.mem

end Lay

namespace Lay

variable {L : Lay}

theorem Ok.fr_toNat {σ : State} (h : L.Ok σ) {d : Nat} (hd : d < L.F + 56 + L.A) :
    (L.fr d).toNat = L.B.toNat + d := by
  have := h.fit
  simp only [fr, Q]
  rw [BitVec.toNat_add, Proof.X25519.Arm.addr_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := d) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- `B + d` as an address. -/
theorem Ok.addrB {σ : State} (h : L.Ok σ) {d : Nat} (hd : d < L.F + 56 + L.A) :
    State.addr (L.B + BitVec.ofNat 32 d) = L.fr d :=
  addr_add (by have := h.fit; omega)

/-- A range of the frames is within our stack. -/
theorem sub_stk {d n : Nat} (hd : d + n ≤ L.F + 56) : Region.Sub ⟨L.fr d, n⟩ L.STK := by
  have e : L.fr d = L.Q - BitVec.ofNat 64 L.C + BitVec.ofNat 64 (L.C + d) := by
    simp only [fr]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [e]
  exact Offset.sub_base _ (by omega)

theorem low_stk : Region.Sub L.LOW L.STK := Region.sub_prefix (by omega)

theorem FR_stk : Region.Sub L.FR L.STK := by
  have := sub_stk (L := L) (d := 0) (n := L.F) (by omega)
  simp only [fr, BitVec.add_zero] at this
  exact this

/-- Two ranges of the frames, apart. -/
theorem fr_sep {d n d' n' : Nat} (hs : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 2 ^ 32)
    (h₂ : d' + n' ≤ 2 ^ 32) : Region.Disjoint ⟨L.fr d, n⟩ ⟨L.fr d', n'⟩ :=
  Offset.disjoint _ hs (by omega) (by omega)

/-- A range of the frames misses the `C` bytes below them. -/
theorem fr_low {d n : Nat} (hd : d + n ≤ 2 ^ 32) (hC : L.C ≤ 2 ^ 32 := by simp) :
    Region.Disjoint ⟨L.fr d, n⟩ L.LOW :=
  Offset.disjoint_below _ (by omega)

theorem Ok.low_eq {σ : State} (h : L.Ok σ) : FrameStack.belowA L.B L.C = L.LOW := by
  simp only [FrameStack.belowA, LOW, Q]
  rw [FrameStack.addr_sub' h.B56]

/-- The places of the arguments. -/
theorem argOff_lt {j : Nat} (hj : j < 4 + L.A / 4) :
    L.F ≤ Impl.RsaPkcs1Sig.Arm.argOff L.F j ∧ Impl.RsaPkcs1Sig.Arm.argOff L.F j + 4 ≤ L.F + 56 + L.A ∧
      (j < 4 → Impl.RsaPkcs1Sig.Arm.argOff L.F j + 4 ≤ L.F + 56) ∧
      (4 ≤ j → L.F + 56 ≤ Impl.RsaPkcs1Sig.Arm.argOff L.F j) := by
  simp only [Impl.RsaPkcs1Sig.Arm.argOff]
  split <;> omega

/-- An argument's place is in the push or the stack arguments, apart from
what the body writes. -/
theorem Ok.arg_apart {σ : State} (h : L.Ok σ) {j : Nat} (hj : j < L.argv.length) :
    ∀ r ∈ L.W, Region.Disjoint ⟨L.argA j, 4⟩ r := by
  have hn := h.nargs
  have := h.fit
  have ha := argOff_lt (L := L) (j := j) (by omega)
  intro r hr
  simp only [W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact (Offset.disjoint_base _ (by omega) (by omega))
  · -- A writable buffer misses the push and the stack arguments.
    have hs := h.stk r (List.mem_append_right _ hr)
    rcases (by omega : j < 4 ∨ 4 ≤ j) with hj4 | hj4
    · exact (hs.sub_left (sub_stk (by have := ha.2.2.1 hj4; omega))).symm.symm
    · have hw := h.wro r hr L.ARGS (List.mem_append_right _ (List.mem_singleton_self _))
      refine (hw.sub_right ?_).symm
      exact Offset.sub _ (ha.2.2.2 hj4) (by omega)
  · exact fr_low (by omega) (by have := h.B56; have := L.B.isLt; omega)

/-- An argument's place may be read. -/
theorem Ok.arg_read {σ : State} (h : L.Ok σ) {j : Nat} (hj : j < L.argv.length) :
    InRegions (σ.rd ++ σ.wr) (L.argA j) 4 := by
  have hn := h.nargs
  have := h.fit
  have ha := argOff_lt (L := L) (j := j) (by omega)
  rcases (by omega : j < 4 ∨ 4 ≤ j) with hj4 | hj4
  · refine ⟨L.PUSH, List.mem_append_right _ (by rw [h.wr]; simp), ?_⟩
    exact Offset.contains _ ha.1 (by have := ha.2.2.1 hj4; omega) (by omega)
  · refine ⟨L.ARGS, List.mem_append_left _ (by rw [h.rd]; simp), ?_⟩
    exact Offset.contains _ (ha.2.2.2 hj4) ha.2.1 (by omega)

namespace Ok

variable {σ : State} (h : L.Ok σ)
include h

theorem stk_fr {R : Region} (hR : R ∈ L.ro ∨ R ∈ L.rw) {d n : Nat} (hd : d + n ≤ L.F + 56) :
    Region.Disjoint ⟨L.fr d, n⟩ R :=
  ((h.stk R (List.mem_append.mpr hR)).sub_left (sub_stk hd))

theorem low_buf {R : Region} (hR : R ∈ L.ro ∨ R ∈ L.rw) : L.LOW.Disjoint R :=
  (h.stk R (List.mem_append.mpr hR)).sub_left low_stk

theorem rw_ro {w r : Region} (hw : w ∈ L.rw) (hr : r ∈ L.ro) : w.Disjoint r :=
  h.wro w hw r (List.mem_append_left _ hr)

/-- The push misses what the body writes. -/
theorem push_apart : ∀ r ∈ L.W, L.PUSH.Disjoint r := by
  have := h.fit
  intro r hr
  simp only [W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · exact (h.stk r (List.mem_append_right _ hr)).sub_left (sub_stk (Nat.le_refl _))
  · exact fr_low (by omega) (by have := h.B56; have := L.B.isLt; omega)

end Ok

namespace St

variable {σ s t : State}

theorem arg (h : L.St σ s) {j : Nat} (hj : j < L.argv.length) :
    s.mem.readW (L.argA j) 32 = L.argv.getD j 0 := by
  rw [h.frame.readW (r := ⟨L.argA j, 4⟩) (Region.contains_self _ _) (h.ok.arg_apart hj) (by decide)]
  exact h.ok.args j hj

/-- A buffer only read keeps its bytes. -/
theorem ro {R : Region} (h : L.St σ s) (hR : R ∈ L.ro) :
    Spec.Rsa.bytesAt s.mem R.base R.len = Spec.Rsa.bytesAt σ.mem R.base R.len := by
  refine bytesAt_frame h.frame (fun r hr => ?_) (by have := h.ok.fits R (List.mem_append_left _ hR); omega)
  simp only [W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left FR_stk).symm
  · exact (h.ok.wro r hr R (List.mem_append_left _ hR)).symm
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left low_stk).symm

/-- A buffer only read keeps its words. -/
theorem ro_words {R : Region} (h : L.St σ s) (hR : R ∈ L.ro) {n : Nat} (hn : n * 8 = R.len) :
    Spec.Rsa.wordsAt s.mem R.base n = Spec.Rsa.wordsAt σ.mem R.base n := by
  refine wordsAt_frame h.frame (fun r hr => ?_) (by have := h.ok.fits R (List.mem_append_left _ hR); omega)
  rw [hn]
  simp only [W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left FR_stk).symm
  · exact (h.ok.wro r hr R (List.mem_append_left _ hR)).symm
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left low_stk).symm

/-- The same state, but for registers. -/
theorem regs (h : L.St σ s) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) (m : t.mem = s.mem) :
    L.St σ t :=
  ⟨h.ok, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, m ▸ h.frame⟩

theorem of_rest {ws : List Reg} (h : L.St σ s) (r : Rest ws s t) (m : t.mem = s.mem) : L.St σ t :=
  h.regs r.rd r.wr r.sp m

/-- Memory changed within the frame or the writable buffers. -/
theorem write (h : L.St σ s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ R ∈ L.W, Region.Sub r R) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (sp : t.sp = s.sp) : L.St σ t :=
  ⟨h.ok, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.frame.trans (hf.sub hs)⟩

/-- A store into the frame. -/
theorem frameW (h : L.St σ s) {d n : Nat} (hd : d + n ≤ L.F) (hf : Frame [⟨L.fr d, n⟩] s.mem t.mem)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : L.St σ t :=
  h.write hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.FR, List.mem_cons_self .., Offset.sub_base _ hd⟩) rd wr sp

/-- A range of the frame may be written. -/
theorem inFr (h : L.St σ s) {d n : Nat} (hd : d + n ≤ L.F) : InRegions s.wr (L.fr d) n :=
  ⟨L.FR, by rw [h.wr, h.ok.wr]; simp, Offset.contains_base _ hd (by have := h.ok.fit; omega)⟩

theorem inFrR (h : L.St σ s) {d n : Nat} (hd : d + n ≤ L.F) : InRegions (s.rd ++ s.wr) (L.fr d) n :=
  let ⟨r, hr, hc⟩ := h.inFr hd
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- `ldr r, [sp, #off]` of argument `j`. -/
theorem wp_arg (h : L.St σ s) {j : Nat} (hj : j < L.argv.length) {r : Reg} {is : List Instr}
    {Q : State → Prop} (hoff : Impl.RsaPkcs1Sig.Arm.argOff L.F j < 4096)
    (k : ∀ t, L.St σ t → Upd s t r (L.argv.getD j 0) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp r (Impl.RsaPkcs1Sig.Arm.argOff L.F j) :: is)) s Q := by
  have hn := h.ok.nargs
  have ha := argOff_lt (L := L) (j := j) (by omega)
  refine VG.Proof.Bignum.Arm.wp_loadStack hoff (a := L.argA j) ?_ ?_ fun t u => ?_
  · rw [h.sp]; exact h.ok.addrB (by omega)
  · rw [h.rd, h.wr]; exact h.ok.arg_read hj
  · rw [h.arg hj] at u
    exact k t (h.of_rest (u.rest (ws := [r]) (by simp)) u.mem) u

/-- `ldr r, [sp, #d]` of a word of the frame. -/
theorem wp_slot (h : L.St σ s) {d : Nat} (hd : d + 4 ≤ L.F) (hoff : d < 4096) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, L.St σ t → Upd s t r (s.mem.readW (L.fr d) 32) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp r d :: is)) s Q := by
  refine VG.Proof.Bignum.Arm.wp_loadStack hoff (a := L.fr d) ?_ (h.inFrR hd) fun t u =>
    k t (h.of_rest (u.rest (ws := [r]) (by simp)) u.mem) u
  rw [h.sp]; exact h.ok.addrB (by omega)

/-- `str r, [r12, #d]` into the frame, with `r12 = B`. -/
theorem wp_strFr (h : L.St σ s) {d : Nat} (hd : d + 4 ≤ L.F) (hoff : d < 4096) (h12 : s.gpr .r12 = L.B)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, L.St σ t → Mupd s t (s.mem.writeW (L.fr d) (s.gpr r)) → WP isa (.block is) t Q) :
    WP isa (.block (.str r .r12 d :: is)) s Q := by
  refine Proof.X25519.Arm.wp_str hoff (a := L.fr d) ?_ (h.inFr hd) fun t u => k t ?_ u
  · rw [h12]; exact h.ok.addrB (by omega)
  · refine h.frameW hd ?_ u.rd u.wr u.sp
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- An argument copied to a word of the frame, through `r` and `r12 = B`. -/
theorem wp_copyArg (h : L.St σ s) (h12 : s.gpr .r12 = L.B) {j d : Nat} (hj : j < L.argv.length)
    (hoff : Impl.RsaPkcs1Sig.Arm.argOff L.F j < 4096) (hd : d + 4 ≤ L.F) (hdo : d < 4096) {r : Reg}
    (hr : r ≠ .r12) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, L.St σ t → t.gpr r = L.argv.getD j 0 → (∀ q, q ≠ r → t.gpr q = s.gpr q) →
      t.mem = s.mem.writeW (L.fr d) (L.argv.getD j 0) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp r (Impl.RsaPkcs1Sig.Arm.argOff L.F j) :: .str r .r12 d :: is)) s Q :=
  h.wp_arg hj hoff fun t1 s1 u1 => s1.wp_strFr hd hdo (by rw [u1.other _ (Ne.symm hr), h12])
    fun t2 s2 m2 => k t2 s2 (by rw [m2.gpr, u1.gpr]) (fun q hq => by rw [m2.gpr, u1.other _ hq])
      (by rw [m2.mem, u1.mem, u1.gpr])

end St

/-- A word of the frame read after another is written. -/
theorem readW_fr_other (L : Lay) (m : Mem) {d e : Nat} (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 32) (he : e + 4 ≤ 2 ^ 32) :
    (m.writeW (L.fr e) v).readW (L.fr d) 32 = m.readW (L.fr d) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

/-- A byte of the frame read after a word is written elsewhere. -/
theorem byte_fr_other (L : Lay) (m : Mem) {d e : Nat} (v : BitVec 32) (h : d + 1 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 1 ≤ 2 ^ 32) (he : e + 4 ≤ 2 ^ 32) :
    (m.writeW (L.fr e) v) (L.fr d) = m (L.fr d) :=
  Mem.write_apply fun h' => Offset.sep _ h (by omega) (by omega) (L.fr d) (by simp) h'

end Lay

end VG.Proof.RsaPkcs1Sig.Arm
