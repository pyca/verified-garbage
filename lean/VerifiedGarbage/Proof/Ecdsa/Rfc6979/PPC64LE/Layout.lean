module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Contract
public import VerifiedGarbage.Proof.HmacTable.PPC64LE
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
`scratch`, the table of HMAC) and the 736 bytes of stack below the stack
pointer on entry, from `B` up (`Lay dn`): the 96 bytes the calls use, then
the frame of 592 bytes from `B + 96` (the stack pointer of the body): its
back chain and header, `K` and `V` (64 bytes each, from `B + 128`), the
length of `T`, the number of candidates left, the pointers to `scratch`,
`digest`, `d` and `out`, `D`, `B` and the table's address (from `B + 272`),
then `h`, `X`, `core`'s digest and `T` (from `B + 328`); then the frame of
48 bytes holding our return address (at `B + 720`). `Ctx` is what holds
between the frames' pushes and pops: the permissions, `sp`, the
callee-saved registers, the return address and the pointers in the frames,
that memory changed only in `out`, `scratch` and the stack, the statics'
addresses, and what the table holds. Code that writes only regions apart
from the pointers and the return address (`Safe`) keeps it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (Fns)
open VG.Proof.HmacTable.PPC64LE (HVar TabOK TabMem)

/-- The buffers and the lowest byte of the stack used (`sp - 736` on
entry), for a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) where
  out : Addr
  d : Addr
  dg : Addr
  scr : Addr
  /-- The table of HMAC. -/
  tab : Addr
  B : Addr
  q : Nat
  /-- The hash function whose HMAC functions the table holds, and the
  functions an indirect call of a table's functions may reach. -/
  w : HVar
  f : Fns
  /-- The addresses of the statics. -/
  sy : String → Addr

namespace Lay

variable {dn : Nat} (L : Lay dn)

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The table of HMAC. -/
abbrev TAB : Region := ⟨L.tab, 48⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 736⟩
/-- The frame's local variable space, writable. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 128, 560⟩
/-- Our return address's place, writable. -/
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 720, 16⟩
/-- The stack below the frame's pointers: the calls', the back chain, `K`,
`V`, the length of `T` and the count. -/
abbrev LOW : Region := ⟨L.B, 272⟩
/-- The frame above its pointers: `h`, `X`, `core`'s digest and `T`. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 328, 360⟩

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
  nB : L.B.toNat + 736 ≤ 2 ^ 64
  /-- The table does not wrap around, and is apart from what the code writes. -/
  nt : L.tab.toNat + 48 ≤ 2 ^ 64
  tout : L.TAB.Disjoint L.OUT
  tsc : L.TAB.Disjoint L.SCR
  tstk : L.TAB.Disjoint L.STK

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame's local variable space. -/
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 688) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 128, 560⟩ :=
  ⟨d - 128, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch`, or the stack below or above the frame's pointers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 272) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Offset.sub_base _ h)))

theorem safe_high {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 328 ≤ d) (h₂ : d + n ≤ 688) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ h₂)))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

/-- A region of the frame below or above its pointers. -/
theorem safe_fr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 272 ∨ 328 ≤ d ∧ d + n ≤ 688) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ := by
  rcases h with h | ⟨h₁, h₂⟩
  · exact safe_low L h
  · exact safe_high L h₁ h₂

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 736) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 736) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 736) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 736) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 736) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

/-- The 96 bytes the calls use, apart from `scratch`. -/
theorem low_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 96⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ h₂)

/-- The frame's pointers are apart from every safe region. -/
theorem ptrs_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 272, 56⟩ r := by
  have := h.nB
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs
  · exact (Offset.disjoint _ (by omega) (by omega) (by omega)).sub_right hs

/-- Our return address is apart from every safe region. -/
theorem lr_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 720, 16⟩ r := by
  have := h.nB
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs
  · exact (Offset.disjoint _ (by omega) (by omega) (by omega)).sub_right hs

/-- The buffers that are only read are apart from every safe region. -/
theorem d_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.D.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.od.symm.sub_right hs
  · exact h.dc.sub_right hs
  · exact (h.kd.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs
  · exact (h.kd.symm.sub_right (Offset.sub_base _ (by omega))).sub_right hs

theorem dg_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.DG.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.og.symm.sub_right hs
  · exact h.gc.sub_right hs
  · exact (h.kg.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs
  · exact (h.kg.symm.sub_right (Offset.sub_base _ (by omega))).sub_right hs

/-- The table is apart from every safe region. -/
theorem tab_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.TAB.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.tout.sub_right hs
  · exact h.tsc.sub_right hs
  · exact (h.tstk.sub_right (Region.sub_prefix (by omega))).sub_right hs
  · exact (h.tstk.sub_right (Offset.sub_base _ (by omega))).sub_right hs

end Lay.Ok

/-! ## Between the frames' pushes and pops -/

/-- The state between the frames' pushes and pops: `g` are the registers on
entry, `lr` the return address, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.TAB]
  wr : t.wr = [L.FR, L.LR, L.OUT, L.SCR]
  sp : t.sp = L.B + BitVec.ofNat 64 96
  cs : ∀ r ∈ preserved, t.gpr r = g r
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 272) 64 = L.scr
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 280) 64 = L.dg
  pD : t.mem.readW (L.B + BitVec.ofNat 64 288) 64 = L.d
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 296) 64 = L.out
  /-- `D`, `B` and the table's address, above the pointers. -/
  pDl : t.mem.readW (L.B + BitVec.ofNat 64 304) 64 = BitVec.ofNat 64 L.w.H.D
  pBl : t.mem.readW (L.B + BitVec.ofNat 64 312) 64 = BitVec.ofNat 64 L.w.H.B
  pTab : t.mem.readW (L.B + BitVec.ofNat 64 320) 64 = L.tab
  lr : t.mem.readW (L.B + BitVec.ofNat 64 720) 64 = lr
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : t.syms = L.sy
  tabOk : TabOK L.w L.f L.sy
  tabMem : TabMem L.w L.sy L.tab m₀

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base L.B (by omega) a (h a ha)⟩

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `sp`, the callee-saved registers and
the statics' addresses, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g lr m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hcs : ∀ r ∈ preserved, t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) (hsy : t'.syms = t.syms) :
    Ctx L g lr m₀ t' := by
  have := hL.nB
  have keep : ∀ d, 272 ≤ d → d + 8 ≤ 328 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 272, 56⟩)
      (Offset.contains _ h₁ (by omega) (by omega)) (fun r hr => hL.ptrs_safe (hs r hr)) (by decide)
  have keepLr : t'.mem.readW (L.B + BitVec.ofNat 64 720) 64 = t.mem.readW (L.B + BitVec.ofNat 64 720) 64 :=
    hf.readW (r := ⟨L.B + BitVec.ofNat 64 720, 16⟩)
      (Offset.contains _ (Nat.le_refl _) (by omega) (by omega)) (fun r hr => hL.lr_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr => (hcs r hr).trans (hc.cs r hr),
    (keep 272 (by omega) (by omega)).trans hc.pScr, (keep 280 (by omega) (by omega)).trans hc.pDg,
    (keep 288 (by omega) (by omega)).trans hc.pD, (keep 296 (by omega) (by omega)).trans hc.pOut,
    (keep 304 (by omega) (by omega)).trans hc.pDl, (keep 312 (by omega) (by omega)).trans hc.pBl,
    (keep 320 (by omega) (by omega)).trans hc.pTab,
    keepLr.trans hc.lr, hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame), hsy.trans hc.sy, hc.tabOk,
    hc.tabMem⟩

/-- Code that writes only registers but the callee-saved ones. -/
theorem regs (hL : L.Ok) (hc : Ctx L g lr m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hsy : t'.syms = t.syms) :
    Ctx L g lr m₀ t' :=
  hc.keep hL hrd hwr hsp hg (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp) hsy

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

/-- The table's words, as on entry. -/
theorem tabWord (hL : L.Ok) (hc : Ctx L g lr m₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (L.tab + BitVec.ofNat 64 o) 64 = m₀.readW (L.tab + BitVec.ofNat 64 o) 64 :=
  hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.tout
    · exact hL.tsc
    · exact hL.tstk) (by decide)

theorem inFr (hc : Ctx L g lr m₀ t) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 688) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : Ctx L g lr m₀ t) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 688) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inScr (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inScrW (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inTab (hL : L.Ok) (hc : Ctx L g lr m₀ t) {o : Nat} (h : o + 8 ≤ 48) :
    InRegions (t.rd ++ t.wr) (L.tab + BitVec.ofNat 64 o) 8 :=
  ⟨L.TAB, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by have := hL.nt; omega)⟩

theorem inD (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 128) :
    InRegions (t.rd ++ t.wr) (L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inDg (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 128) :
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

/-- What the contract says of the table at `r8`: it holds `w`'s HMAC
functions, which an indirect call of `f`'s reaches, and its digest length
and HMAC's block size. -/
def tabFacts (w : HVar) (f : Fns) (s : State) : Prop :=
  TabOK w f s.syms ∧ TabMem w s.syms (s.gpr .r8) s.mem ∧
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q`, and the hash function `w`'s HMAC through the table, whose functions an
indirect call reaches among `f`'s. -/
def lay (dn q : Nat) (w : HVar) (f : Fns) (s : State) : Lay dn :=
  ⟨s.gpr .r3, s.gpr .r4, s.gpr .r5, s.gpr .r7, s.gpr .r8, s.sp - BitVec.ofNat 64 736, q, w, f, s.syms⟩

theorem lay_ok {I : Spec.Ecdsa.Rfc6979.Instance} {w : HVar} {f : Fns} {ns : List String} {s : State}
    (h : (rfcPPC I 736 (tabFacts w f) ns).pre s) :
    (lay I.hashLen I.ecdsa.curve.len w f s).Ok := by
  obtain ⟨-, -, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, nt, tout, tsc, tstk, -⟩ := h
  have nB : (lay I.hashLen I.ecdsa.curve.len w f s).B.toNat + 736 ≤ 2 ^ 64 := by
    show (s.sp - BitVec.ofNat 64 736).toNat + 736 ≤ 2 ^ 64
    change 736 ≤ s.sp.toNat at hsp
    rw [Offset.toNat_sub_ofNat s.sp _]
    omega
  exact ⟨od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nB, nt, tout, tsc, tstk.symm⟩

/-- The state after `mflr r0`. -/
def lrSaved (s : State) : State := s.write .r0 s.lr

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated Impl.Ecdsa.Rfc6979.PPC64LE.frameBytes (pushed .r0 (lrSaved s))

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl

@[simp] theorem entered_syms (s : State) : (entered s).syms = s.syms := rfl

theorem entered_gpr (s : State) {r : Reg} (hr : r ≠ .r0) : (entered s).gpr r = s.gpr r := by
  show (s.write .r0 s.lr).gpr r = _
  simp [State.write, hr]

theorem entered_sp (dn q : Nat) (w : HVar) (f : Fns) (s : State) :
    (entered s).sp = (lay dn q w f s).B + BitVec.ofNat 64 96 := by
  show s.sp - 48 - BitVec.ofNat 64 592 = s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 96
  bv_omega_using []

theorem entered_wr (dn q : Nat) (w : HVar) (f : Fns) (s : State) :
    (entered s).wr = (lay dn q w f s).FR :: (lay dn q w f s).LR :: s.wr := by
  show (⟨s.sp - 48 - BitVec.ofNat 64 592 + 32, 592 - 32⟩ : Region) :: ⟨s.sp - 48 + 32, 16⟩ :: s.wr =
    ⟨s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 128, 560⟩ ::
    ⟨s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 720, 16⟩ :: s.wr
  have h₁ : s.sp - 48 - BitVec.ofNat 64 592 + 32 = s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 128 := by
    bv_omega_using []
  have h₂ : s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 720 := by bv_omega_using []
  rw [h₁, h₂]

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- What the frames' pushes write: the back chains and the return address. -/
theorem entered_mem (dn q : Nat) (w : HVar) (f : Fns) (s : State) :
    (entered s).mem =
      ((s.mem.writeW ((lay dn q w f s).B + BitVec.ofNat 64 688) s.sp).writeW
        ((lay dn q w f s).B + BitVec.ofNat 64 720) s.lr).writeW ((lay dn q w f s).B + BitVec.ofNat 64 96)
        (s.sp - 48) := by
  show ((s.mem.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 s.lr).write
    (s.sp - 48 - BitVec.ofNat 64 592) 8 (s.sp - 48) =
      ((s.mem.writeW (s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 688) s.sp).writeW
        (s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 720) s.lr).writeW
        (s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 96) (s.sp - 48)
  have h₁ : s.sp - 48 = s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 688 := by bv_omega_using []
  have h₂ : s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 720 := by bv_omega_using []
  have h₃ : s.sp - 48 - BitVec.ofNat 64 592 = s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 96 := by
    bv_omega_using []
  rw [h₃, h₂, write8, write8, write8, ← h₁]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
