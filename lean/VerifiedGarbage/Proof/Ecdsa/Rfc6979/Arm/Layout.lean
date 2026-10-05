import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`) and the 240 bytes of stack below the stack pointer, from `B` up
(`Lay dn`): the 24 bytes the calls use (their frames and the 16 bytes of
HMAC's functions), then the frame of 216 bytes, from `B + 24`: `K` and `V`
(64 bytes each), `h` (48 bytes, of which `q` are used), a word unused, and our caller's `r4`–`r11` and `lr`. `Ctx` is
what holds between the frame's allocation and its release: the permissions,
`sp`, the registers that hold the pointers (`r4`–`r6`, `r8`, `r11`), our
caller's registers in the frame, and that memory changed only in `out`,
`scratch` and the stack. Code that writes only regions below the saved
registers (`Safe`) keeps it (`Ctx.keep`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm
open VG.Arm.FrameStack (addr_sub' sub_toNat')
open VG.Proof.X25519.Arm (Upd Mupd)

/-- The buffers, as the registers hold them, and the stack pointer on entry,
for a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) where
  out : BitVec 32
  d : BitVec 32
  dg : BitVec 32
  scr : BitVec 32
  sp : BitVec 32
  q : Nat

namespace Lay

variable {dn : Nat} (L : Lay dn)

/-- The lowest byte of the stack used. -/
abbrev B : Addr := State.addr L.sp - BitVec.ofNat 64 240
/-- The frame's base, as `sp` and `r8` hold it. -/
abbrev fp : BitVec 32 := L.sp - BitVec.ofNat 32 216

abbrev OUT : Region := ⟨State.addr L.out, 2 * L.q⟩
abbrev D : Region := ⟨State.addr L.d, L.q⟩
abbrev DG : Region := ⟨State.addr L.dg, dn⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 240⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 24, 216⟩
/-- The stack below the saved registers: the calls', `K`, `V`, `h` and the unused word. -/
abbrev LOW : Region := ⟨L.B, 204⟩

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
  no : L.out.toNat + 2 * L.q ≤ 2 ^ 32
  nd : L.d.toNat + L.q ≤ 2 ^ 32
  ng : L.dg.toNat + dn ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
  nB : 240 ≤ L.sp.toNat

end Lay

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn} (h : L.Ok)
include h

theorem B_toNat : L.B.toNat = L.sp.toNat - 240 := by
  have := h.nB; have := L.sp.isLt
  simp only [Lay.B, BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_addr]; omega

theorem B_fit : L.B.toNat + 240 ≤ 2 ^ 32 := by
  have := L.sp.isLt; rw [h.B_toNat]; omega

/-- `fp + o`, as an address: `B + 24 + o`. -/
theorem fpA {o : Nat} (ho : o < 216) :
    State.addr (L.fp + BitVec.ofNat 32 o) = L.B + BitVec.ofNat 64 (24 + o) := by
  have hn := h.nB
  have hfp : L.fp.toNat = L.sp.toNat - 216 := sub_toNat' (by omega)
  rw [addr_add (by rw [hfp]; have := L.sp.isLt; omega), Lay.fp, addr_sub' (by omega),
    Offset.sub_ofNat_eq _ (show 216 ≤ 240 by omega), Offset.add_add]

theorem fpA0 : State.addr L.fp = L.B + BitVec.ofNat 64 24 := by
  have := h.fpA (o := 0) (by omega)
  rwa [BitVec.add_zero] at this

theorem stk_scr {d n e k : Nat} (h₁ : d + n ≤ 240) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨State.addr L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_SCR {d n : Nat} (h₁ : d + n ≤ 240) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT {d n : Nat} (h₁ : d + n ≤ 240) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D {d n : Nat} (h₁ : d + n ≤ 240) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG {d n : Nat} (h₁ : d + n ≤ 240) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame. -/
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 240) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 24, 216⟩ :=
  ⟨d - 24, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below the saved registers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 204) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (Offset.sub_base _ h))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) :
    Safe L ⟨State.addr L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

/-- The saved registers are apart from every safe region. -/
theorem saved_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 204, 36⟩ r := by
  rcases hs with hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs

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

/-! ## Between the frame's allocation and its release -/

/-- The registers that hold the pointers between the calls. -/
abbrev ptrRegs : List Reg := [.r4, .r5, .r6, .r8, .r11]

/-- The state between the frame's allocation and its release: `g` are the
registers on entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG]
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  sp : t.sp = L.fp
  r4 : t.gpr .r4 = L.out
  r5 : t.gpr .r5 = L.d
  r6 : t.gpr .r6 = L.dg
  r8 : t.gpr .r8 = L.fp
  r11 : t.gpr .r11 = L.scr
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, t.mem.readW (L.B + BitVec.ofNat 64 (24 + p.2)) 32 = g p.1
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega) a (h a ha)⟩

theorem saved_off : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, 180 ≤ p.2 ∧ p.2 + 4 ≤ 216 := by decide

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `sp` and the registers that hold the
pointers, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hp : ∀ r ∈ ptrRegs, t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) : Ctx L g m₀ t' := by
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hp _ (by decide)).trans hc.r4,
    (hp _ (by decide)).trans hc.r5, (hp _ (by decide)).trans hc.r6, (hp _ (by decide)).trans hc.r8,
    (hp _ (by decide)).trans hc.r11, fun p hp' => ?_, hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame)⟩
  have ho := saved_off p hp'
  rw [hf.readW (r := ⟨L.B + BitVec.ofNat 64 204, 36⟩) (Offset.contains _ (by omega) (by omega) (by omega))
    (fun r hr => hL.saved_safe (hs r hr)) (by decide)]
  exact hc.saved p hp'

/-- An update of one register, not one that holds a pointer. -/
theorem upd (hc : Ctx L g m₀ t) {d : Reg} {v : BitVec 32} (u : Upd t t' d v) (hd : d ∉ ptrRegs) :
    Ctx L g m₀ t' :=
  ⟨u.rd.trans hc.rd, u.wr.trans hc.wr, u.sp.trans hc.sp,
    (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r4, (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r5,
    (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r6, (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r8,
    (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r11, fun p hp => by rw [u.mem]; exact hc.saved p hp,
    by rw [u.mem]; exact hc.frame⟩

/-- A byte of `d`, as on entry. -/
theorem d_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.q) :
    t.mem (State.addr L.d + BitVec.ofNat 64 i) = m₀ (State.addr L.d + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.D) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.od.symm
    · exact hL.dc
    · exact hL.kd.symm) (by show L.q ≤ 2 ^ 64; have := hL.nd; omega) hi

/-- A byte of `digest`, as on entry. -/
theorem dg_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < dn) :
    t.mem (State.addr L.dg + BitVec.ofNat 64 i) = m₀ (State.addr L.dg + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.DG) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.og.symm
    · exact hL.gc
    · exact hL.kg.symm) (by show dn ≤ 2 ^ 64; have := hL.ng; omega) hi

theorem inFr (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 240) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 240) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inScr (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (State.addr L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inScrW (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (State.addr L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inD (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (State.addr L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inDg (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (State.addr L.dg + BitVec.ofNat 64 o) n :=
  ⟨L.DG, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

/-- Regions within the buffers and the frame are permitted. -/
theorem covers (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl <;> simp

theorem coversW (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> simp

end Ctx

/-! ## The layout of a call -/

/-- The layout of a call from `s`, with a digest of `dn` bytes and scalars of `q`. -/
def lay (dn q : Nat) (s : State) : Lay dn := ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, s.sp, q⟩

theorem lay_ok {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcArm I).pre s) :
    (lay I.hashLen I.ecdsa.curve.len s).Ok := by
  obtain ⟨-, -, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp⟩ := h
  exact ⟨od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
