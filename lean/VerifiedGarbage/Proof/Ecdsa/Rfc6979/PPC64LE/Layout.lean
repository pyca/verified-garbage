module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-!
# Deterministic ECDSA on PPC64LE: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`) and the 400 bytes of stack below the stack pointer on entry, from
`B` up (`Lay`): the 96 bytes the calls use, then the frame of 256 bytes from
`B + 96` (the stack pointer of the body): its back chain and header, `K`
and `V` (64 bytes each, from `B + 128`), `h` (48 bytes, of which `q` are
used), the number of candidates left, the pointers to `scratch`, `digest`,
`d` and `out` (from `B + 312`); then the frame of 48 bytes holding our
return address (at `B + 384`).
`Ctx` is what holds between the frames' pushes and pops: the permissions,
`sp`, the callee-saved registers, the return address and the pointers in
the frames, and that memory changed only in `out`, `scratch` and the stack.
Code that writes only regions apart from the pointers and the return
address (`Safe`) keeps it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- The buffers and the lowest byte of the stack used (`sp - 400` on entry),
for a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) where
  out : Addr
  d : Addr
  dg : Addr
  scr : Addr
  B : Addr
  q : Nat

namespace Lay

variable {dn : Nat} (L : Lay dn)

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 400⟩
/-- The frame's local variable space, writable. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 128, 224⟩
/-- Our return address's place, writable. -/
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 384, 16⟩
/-- The stack below the frame's pointers: the calls', the back chain, `K`,
`V`, `h` and the count. -/
abbrev LOW : Region := ⟨L.B, 312⟩

/-- What the contract says of where the buffers and the stack are (`d` and
`digest`, which are only read, may overlap). -/
structure Ok : Prop where
  od : L.OUT.Disjoint L.D
  og : L.OUT.Disjoint L.DG
  oc : L.OUT.Disjoint L.SCR
  dc : L.D.Disjoint L.SCR
  gc : L.DG.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  kd : L.STK.Disjoint L.D
  kg : L.STK.Disjoint L.DG
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 2 * L.q ≤ 2 ^ 64
  nd : L.d.toNat + L.q ≤ 2 ^ 64
  ng : L.dg.toNat + dn ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  nB : L.B.toNat + 400 ≤ 2 ^ 64

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame's local variable space. -/
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 352) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 128, 224⟩ :=
  ⟨d - 128, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below the frame's pointers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 312) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (Offset.sub_base _ h))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr fun x hx => hs x (h x hx))]

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 400) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 400) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 400) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 400) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 400) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

/-- The 96 bytes the calls use, apart from `scratch`. -/
theorem low_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 96⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ h₂)

/-- The frame's pointers are apart from every safe region. -/
theorem ptrs_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 312, 32⟩ r := by
  have := h.nB
  rcases hs with hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs

/-- Our return address is apart from every safe region. -/
theorem lr_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 384, 16⟩ r := by
  have := h.nB
  rcases hs with hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs

/-- The buffers that are only read are apart from every safe region. -/
theorem d_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.D.Disjoint r := by
  rcases hs with hs | hs | hs
  · exact h.od.symm.sub_right hs
  · exact h.dc.sub_right hs
  · exact (h.kd.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs

theorem dg_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.DG.Disjoint r := by
  rcases hs with hs | hs | hs
  · exact h.og.symm.sub_right hs
  · exact h.gc.sub_right hs
  · exact (h.kg.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs

end Lay.Ok

/-! ## Between the frames' pushes and pops -/

/-- The state between the frames' pushes and pops: `g` are the registers on
entry, `lr` the return address, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG]
  wr : t.wr = [L.FR, L.LR, L.OUT, L.SCR]
  sp : t.sp = L.B + BitVec.ofNat 64 96
  cs : ∀ r ∈ preserved, t.gpr r = g r
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 312) 64 = L.scr
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 320) 64 = L.dg
  pD : t.mem.readW (L.B + BitVec.ofNat 64 328) 64 = L.d
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 336) 64 = L.out
  lr : t.mem.readW (L.B + BitVec.ofNat 64 384) 64 = lr
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega) a (h a ha)⟩

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `sp` and the callee-saved registers,
and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g lr m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hcs : ∀ r ∈ preserved, t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) : Ctx L g lr m₀ t' := by
  have := hL.nB
  have keep : ∀ d, 312 ≤ d → d + 8 ≤ 344 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 312, 32⟩)
      (Offset.contains _ h₁ (by omega) (by omega)) (fun r hr => hL.ptrs_safe (hs r hr)) (by decide)
  have keepLr : t'.mem.readW (L.B + BitVec.ofNat 64 384) 64 = t.mem.readW (L.B + BitVec.ofNat 64 384) 64 :=
    hf.readW (r := ⟨L.B + BitVec.ofNat 64 384, 16⟩)
      (Offset.contains _ (Nat.le_refl _) (by omega) (by omega)) (fun r hr => hL.lr_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr => (hcs r hr).trans (hc.cs r hr),
    (keep 312 (by omega) (by omega)).trans hc.pScr, (keep 320 (by omega) (by omega)).trans hc.pDg,
    (keep 328 (by omega) (by omega)).trans hc.pD, (keep 336 (by omega) (by omega)).trans hc.pOut,
    keepLr.trans hc.lr, hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame)⟩

/-- Code that writes only registers but the callee-saved ones. -/
theorem regs (hL : L.Ok) (hc : Ctx L g lr m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) : Ctx L g lr m₀ t' :=
  hc.keep hL hrd hwr hsp hg (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- A byte of `d`, as on entry. -/
theorem d_byte (hL : L.Ok) (hc : Ctx L g lr m₀ t) {i : Nat} (hi : i < L.q) :
    t.mem (L.d + BitVec.ofNat 64 i) = m₀ (L.d + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.D) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.od.symm
    · exact hL.dc
    · exact hL.kd.symm) (by show L.q ≤ 2 ^ 64; have := hL.nd; omega) hi

/-- A byte of `digest`, as on entry. -/
theorem dg_byte (hL : L.Ok) (hc : Ctx L g lr m₀ t) {i : Nat} (hi : i < dn) :
    t.mem (L.dg + BitVec.ofNat 64 i) = m₀ (L.dg + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.DG) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.og.symm
    · exact hL.gc
    · exact hL.kg.symm) (by show dn ≤ 2 ^ 64; have := hL.ng; omega) hi

theorem inFr (hc : Ctx L g lr m₀ t) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 352) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : Ctx L g lr m₀ t) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 352) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inScr (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inScrW (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inD (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inDg (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.dg + BitVec.ofNat 64 o) n :=
  ⟨L.DG, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

/-- Regions within the buffers and the frame are permitted. -/
theorem covers (hc : Ctx L g lr m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl <;> simp

theorem coversW (hc : Ctx L g lr m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> simp

end Ctx

/-! ## The layout of a call, and the frames' entry -/

/-- The layout of a call from `s`, with a digest of `dn` bytes and scalars
of `q`. -/
def lay (dn q : Nat) (s : State) : Lay dn :=
  ⟨s.gpr .r3, s.gpr .r4, s.gpr .r5, s.gpr .r6, s.sp - BitVec.ofNat 64 400, q⟩

theorem lay_ok {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcPPC I 400).pre s) :
    (lay I.hashLen I.ecdsa.curve.len s).Ok := by
  obtain ⟨-, -, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp⟩ := h
  have nB : (lay I.hashLen I.ecdsa.curve.len s).B.toNat + 400 ≤ 2 ^ 64 := by
    simp only [lay]
    rw [Offset.toNat_sub_ofNat s.sp 400]
    omega
  exact ⟨od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nB⟩

/-- The state after `mflr r0`. -/
def lrSaved (s : State) : State := s.write .r0 s.lr

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated 256 (pushed .r0 (lrSaved s))

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl

theorem entered_gpr (s : State) {r : Reg} (hr : r ≠ .r0) : (entered s).gpr r = s.gpr r := by
  show (s.write .r0 s.lr).gpr r = _
  simp [State.write, hr]

theorem entered_sp (dn q : Nat) (s : State) :
    (entered s).sp = (lay dn q s).B + BitVec.ofNat 64 96 := by
  show s.sp - 48 - BitVec.ofNat 64 256 = s.sp - BitVec.ofNat 64 400 + BitVec.ofNat 64 96
  bv_omega

theorem entered_wr (dn q : Nat) (s : State) :
    (entered s).wr = (lay dn q s).FR :: (lay dn q s).LR :: s.wr := by
  show (⟨s.sp - 48 - BitVec.ofNat 64 256 + 32, 256 - 32⟩ : Region) :: ⟨s.sp - 48 + 32, 16⟩ :: s.wr = _
  have h₁ : s.sp - 48 - BitVec.ofNat 64 256 + 32 = (lay dn q s).B + BitVec.ofNat 64 128 := by
    show _ = s.sp - BitVec.ofNat 64 400 + BitVec.ofNat 64 128; bv_omega
  have h₂ : s.sp - 48 + 32 = (lay dn q s).B + BitVec.ofNat 64 384 := by
    show _ = s.sp - BitVec.ofNat 64 400 + BitVec.ofNat 64 384; bv_omega
  rw [h₁, h₂]

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- What the frames' pushes write: the back chains and the return address. -/
theorem entered_mem (dn q : Nat) (s : State) :
    (entered s).mem =
      ((s.mem.writeW ((lay dn q s).B + BitVec.ofNat 64 352) s.sp).writeW ((lay dn q s).B + BitVec.ofNat 64 384)
        s.lr).writeW ((lay dn q s).B + BitVec.ofNat 64 96) (s.sp - 48) := by
  show ((s.mem.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 s.lr).write
    (s.sp - 48 - BitVec.ofNat 64 256) 8 (s.sp - 48) = _
  have h₁ : s.sp - 48 = (lay dn q s).B + BitVec.ofNat 64 352 := by
    show _ = s.sp - BitVec.ofNat 64 400 + BitVec.ofNat 64 352; bv_omega
  have h₂ : s.sp - 48 + 32 = (lay dn q s).B + BitVec.ofNat 64 384 := by
    show _ = s.sp - BitVec.ofNat 64 400 + BitVec.ofNat 64 384; bv_omega
  have h₃ : s.sp - 48 - BitVec.ofNat 64 256 = (lay dn q s).B + BitVec.ofNat 64 96 := by
    show _ = s.sp - BitVec.ofNat 64 400 + BitVec.ofNat 64 96; bv_omega
  rw [h₃, h₂, write8, write8, write8, ← h₁]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
