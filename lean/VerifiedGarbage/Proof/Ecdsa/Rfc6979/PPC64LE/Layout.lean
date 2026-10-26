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

/-- The bytes at the frame's top for a digest of `dn` bytes and scalars of
`q`: `extra`, wide if `dn < q`, else `h` there if `48 < q`. -/
def extraOf (dn q : Nat) : Nat :=
  Impl.Ecdsa.Rfc6979.PPC64LE.extra (!decide (dn < q) && decide (48 < q)) (decide (dn < q))

/-- The buffers and the lowest byte of the stack used (`sp - (400 + e)` on
entry, for `e` bytes at the frame's top), for a digest of `dn` bytes and
scalars of `q`. -/
structure Lay (dn : Nat) where
  out : Addr
  d : Addr
  dg : Addr
  scr : Addr
  B : Addr
  q : Nat

namespace Lay

variable {dn : Nat} (L : Lay dn)

/-- Whether scalars are longer than the digest: two `V`s make a candidate,
and the frame's top holds the digest for `core` and the candidate. -/
def wide : Bool := decide (dn < L.q)

/-- Whether `h` is at the frame's top: scalars of more than 48 bytes, unless
`wide`. -/
def hHigh : Bool := !L.wide && decide (48 < L.q)

/-- The bytes at the frame's top (`extra`). -/
def e : Nat := Impl.Ecdsa.Rfc6979.PPC64LE.extra L.hHigh L.wide

/-- Where `h` is in the frame. -/
def ho : Nat := if L.hHigh then Impl.Ecdsa.Rfc6979.PPC64LE.fX else Impl.Ecdsa.Rfc6979.PPC64LE.fH

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 400 + L.e⟩
/-- The frame's local variable space, writable. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 128, 224 + L.e⟩
/-- Our return address's place, writable. -/
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 (384 + L.e), 16⟩
/-- The frame's top, above its pointers (`extra`). -/
abbrev EXT : Region := ⟨L.B + BitVec.ofNat 64 352, L.e⟩
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
  nB : L.B.toNat + 400 + L.e ≤ 2 ^ 64

/-- Where `h` is: at the frame's `fH` (from `B + 256`, below the count) for
scalars of at most 48 bytes, or at its top (`fX`, from `B + 352`) within the
`e` bytes there, for scalars of at most 64. -/
def HOk : Prop := L.q ≤ 64 ∧ (L.ho = 160 ∧ L.q ≤ 48 ∨ L.ho = 256 ∧ L.q ≤ L.e)

/-- Where `h` is, as the steps on `K` and `V` need it: above them, within the
frame. -/
def HFar : Prop := 160 ≤ L.ho ∧ L.ho + L.q ≤ 304 + L.e

theorem e_le : L.e ≤ 144 := by
  simp only [e, Impl.Ecdsa.Rfc6979.PPC64LE.extra]; split <;> [omega; split <;> omega]

theorem e_mod : L.e % 16 = 0 := by
  simp only [e, Impl.Ecdsa.Rfc6979.PPC64LE.extra]; split <;> [omega; split <;> omega]

/-- The code is wide as the layout is. -/
theorem wide_eq {c : Impl.Ecdsa.Rfc6979.PPC64LE.Cfg} (hcl : c.len = L.q) (hcD : c.H.D = dn) :
    c.wide = L.wide := by
  unfold Impl.Ecdsa.Rfc6979.PPC64LE.Cfg.wide wide; rw [hcl, hcD]

theorem hHigh_eq {c : Impl.Ecdsa.Rfc6979.PPC64LE.Cfg} (hcl : c.len = L.q) (hcD : c.H.D = dn) :
    c.hHigh = L.hHigh := by
  unfold Impl.Ecdsa.Rfc6979.PPC64LE.Cfg.hHigh hHigh; rw [L.wide_eq hcl hcD, hcl]

/-- Where the code has `h`, as the layout has it. -/
theorem fHo_eq {c : Impl.Ecdsa.Rfc6979.PPC64LE.Cfg} (hcl : c.len = L.q) (hcD : c.H.D = dn) : c.fHo = L.ho := by
  unfold Impl.Ecdsa.Rfc6979.PPC64LE.Cfg.fHo ho; rw [L.hHigh_eq hcl hcD]

theorem HOk.far {L : Lay dn} (h : L.HOk) : L.HFar := by
  obtain ⟨-, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := h <;> exact ⟨by omega, by omega⟩

theorem hFar_wide (hw : L.wide = true) (hq : L.q ≤ 72) : L.HFar := by
  simp only [HFar, ho, e, hHigh, hw, Impl.Ecdsa.Rfc6979.PPC64LE.extra, Impl.Ecdsa.Rfc6979.PPC64LE.fH,
    Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
  omega

theorem hOk (h : L.q ≤ 64) (hw : L.wide = false) : L.HOk := by
  refine ⟨h, ?_⟩
  simp only [ho, e, hHigh, hw, Impl.Ecdsa.Rfc6979.PPC64LE.extra, Impl.Ecdsa.Rfc6979.PPC64LE.fX,
    Impl.Ecdsa.Rfc6979.PPC64LE.fH, decide_eq_true_eq, Bool.not_false, Bool.true_and, Bool.false_eq_true,
    ite_false]
  split <;> omega

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame's local variable space. -/
theorem within_fr (B : Addr) {e d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 352 + e) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 128, 224 + e⟩ :=
  ⟨d - 128, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch`, the stack below the frame's pointers or the frame's top. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.EXT

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 312) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Offset.sub_base _ h)))

theorem safe_ext {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 352 ≤ d) (h₂ : d + n ≤ 352 + L.e) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ h₂)))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

/-- `h`'s bytes are safe to write. -/
theorem safe_h {dn : Nat} (L : Lay dn) (hh : L.HOk) {d n : Nat} (h : d + n ≤ L.q) :
    Safe L ⟨L.B + BitVec.ofNat 64 (96 + L.ho + d), n⟩ := by
  obtain ⟨-, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := hh
  · exact safe_low L (by omega)
  · exact safe_ext L (by omega) (by omega)

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 400 + L.e) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 400 + L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 400 + L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 400 + L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 400 + L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

/-- The 96 bytes the calls use, apart from `scratch`. -/
theorem low_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 96⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ h₂)

/-- The frame's pointers are apart from every safe region. -/
theorem ptrs_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 312, 32⟩ r := by
  have := h.nB
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs
  · exact (Offset.disjoint _ (by omega) (by omega) (by omega)).sub_right hs

/-- Our return address is apart from every safe region. -/
theorem lr_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 (384 + L.e), 16⟩ r := by
  have := h.nB
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs
  · exact (Offset.disjoint _ (by omega) (by omega) (by omega)).sub_right hs

/-- The buffers that are only read are apart from every safe region. -/
theorem d_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.D.Disjoint r := by
  rcases hs with hs | hs | hs
  · exact h.od.symm.sub_right hs
  · exact h.dc.sub_right hs
  · rcases hs with hs | hs
    · exact (h.kd.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs
    · exact (h.kd.symm.sub_right (Offset.sub_base _ (by omega))).sub_right hs

theorem dg_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.DG.Disjoint r := by
  rcases hs with hs | hs | hs
  · exact h.og.symm.sub_right hs
  · exact h.gc.sub_right hs
  · rcases hs with hs | hs
    · exact (h.kg.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs
    · exact (h.kg.symm.sub_right (Offset.sub_base _ (by omega))).sub_right hs

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
  lr : t.mem.readW (L.B + BitVec.ofNat 64 (384 + L.e)) 64 = lr
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  ne : L.e ≤ 144

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base L.B (by omega) a (h a ha)⟩

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `sp` and the callee-saved registers,
and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g lr m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hcs : ∀ r ∈ preserved, t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) : Ctx L g lr m₀ t' := by
  have := hL.nB
  have := hc.ne
  have keep : ∀ d, 312 ≤ d → d + 8 ≤ 344 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 312, 32⟩)
      (Offset.contains _ h₁ (by omega) (by omega)) (fun r hr => hL.ptrs_safe (hs r hr)) (by decide)
  have keepLr : t'.mem.readW (L.B + BitVec.ofNat 64 (384 + L.e)) 64 =
      t.mem.readW (L.B + BitVec.ofNat 64 (384 + L.e)) 64 :=
    hf.readW (r := ⟨L.B + BitVec.ofNat 64 (384 + L.e), 16⟩)
      (Offset.contains _ (Nat.le_refl _) (by omega) (by omega)) (fun r hr => hL.lr_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr => (hcs r hr).trans (hc.cs r hr),
    (keep 312 (by omega) (by omega)).trans hc.pScr, (keep 320 (by omega) (by omega)).trans hc.pDg,
    (keep 328 (by omega) (by omega)).trans hc.pD, (keep 336 (by omega) (by omega)).trans hc.pOut,
    keepLr.trans hc.lr, hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame), hc.ne⟩

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

theorem inFr (hc : Ctx L g lr m₀ t) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 352 + L.e) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hc.ne; omega)⟩

theorem inFrW (hc : Ctx L g lr m₀ t) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 352 + L.e) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hc.ne; omega)⟩

theorem inScr (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inScrW (hc : Ctx L g lr m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

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

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q` and `e` bytes at the frame's top. -/
def lay (dn q : Nat) (s : State) : Lay dn :=
  ⟨s.gpr .r3, s.gpr .r4, s.gpr .r5, s.gpr .r6,
    s.sp - BitVec.ofNat 64 (400 + extraOf dn q), q⟩

theorem lay_ok {I : Spec.Ecdsa.Rfc6979.Instance} {s : State}
    (h : (rfcPPC I (400 + extraOf I.hashLen I.ecdsa.curve.len)).pre s) :
    (lay I.hashLen I.ecdsa.curve.len s).Ok := by
  obtain ⟨-, -, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp⟩ := h
  have nB : (lay I.hashLen I.ecdsa.curve.len s).B.toNat + 400 + (lay I.hashLen I.ecdsa.curve.len s).e ≤ 2 ^ 64 := by
    have hle := (lay I.hashLen I.ecdsa.curve.len s).e_le
    show (s.sp - BitVec.ofNat 64 (400 + (lay I.hashLen I.ecdsa.curve.len s).e)).toNat + 400 +
      (lay I.hashLen I.ecdsa.curve.len s).e ≤ 2 ^ 64
    change 400 + (lay I.hashLen I.ecdsa.curve.len s).e ≤ s.sp.toNat at hsp
    generalize (lay I.hashLen I.ecdsa.curve.len s).e = e at hle hsp ⊢
    rw [Offset.toNat_sub_ofNat s.sp _]
    omega
  exact ⟨od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nB⟩

/-- The state after `mflr r0`. -/
def lrSaved (s : State) : State := s.write .r0 s.lr

/-- The state in which the inner frame's body starts. -/
def entered (e : Nat) (s : State) : State := allocated (256 + e) (pushed .r0 (lrSaved s))

@[simp] theorem entered_rd (e : Nat) (s : State) : (entered e s).rd = s.rd := rfl

theorem entered_gpr (e : Nat) (s : State) {r : Reg} (hr : r ≠ .r0) : (entered e s).gpr r = s.gpr r := by
  show (s.write .r0 s.lr).gpr r = _
  simp [State.write, hr]

theorem entered_sp (dn q : Nat) (s : State) :
    (entered (lay dn q s).e s).sp = (lay dn q s).B + BitVec.ofNat 64 96 := by
  show s.sp - 48 - BitVec.ofNat 64 (256 + (lay dn q s).e) =
    s.sp - BitVec.ofNat 64 (400 + (lay dn q s).e) + BitVec.ofNat 64 96
  generalize (lay dn q s).e = e
  simp only [← BitVec.ofNat_add_ofNat]; generalize BitVec.ofNat 64 e = E; bv_omega_using []

theorem entered_wr (dn q : Nat) (s : State) :
    (entered (lay dn q s).e s).wr = (lay dn q s).FR :: (lay dn q s).LR :: s.wr := by
  show (⟨s.sp - 48 - BitVec.ofNat 64 (256 + (lay dn q s).e) + 32, 256 + (lay dn q s).e - 32⟩ : Region) ::
    ⟨s.sp - 48 + 32, 16⟩ :: s.wr =
    ⟨s.sp - BitVec.ofNat 64 (400 + (lay dn q s).e) + BitVec.ofNat 64 128, 224 + (lay dn q s).e⟩ ::
    ⟨s.sp - BitVec.ofNat 64 (400 + (lay dn q s).e) + BitVec.ofNat 64 (384 + (lay dn q s).e), 16⟩ :: s.wr
  generalize (lay dn q s).e = e
  have h₁ : s.sp - 48 - BitVec.ofNat 64 (256 + e) + 32 = s.sp - BitVec.ofNat 64 (400 + e) + BitVec.ofNat 64 128 := by
    simp only [← BitVec.ofNat_add_ofNat]; generalize BitVec.ofNat 64 e = E; bv_omega_using []
  have h₂ : s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 (400 + e) + BitVec.ofNat 64 (384 + e) := by
    simp only [← BitVec.ofNat_add_ofNat]; generalize BitVec.ofNat 64 e = E; bv_omega_using []
  rw [h₁, h₂, show 256 + e - 32 = 224 + e by omega]

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- What the frames' pushes write: the back chains and the return address. -/
theorem entered_mem (dn q : Nat) (s : State) :
    (entered (lay dn q s).e s).mem =
      ((s.mem.writeW ((lay dn q s).B + BitVec.ofNat 64 (352 + (lay dn q s).e)) s.sp).writeW
        ((lay dn q s).B + BitVec.ofNat 64 (384 + (lay dn q s).e)) s.lr).writeW ((lay dn q s).B + BitVec.ofNat 64 96)
        (s.sp - 48) := by
  show ((s.mem.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 s.lr).write
    (s.sp - 48 - BitVec.ofNat 64 (256 + (lay dn q s).e)) 8 (s.sp - 48) =
      ((s.mem.writeW (s.sp - BitVec.ofNat 64 (400 + (lay dn q s).e) + BitVec.ofNat 64 (352 + (lay dn q s).e))
        s.sp).writeW (s.sp - BitVec.ofNat 64 (400 + (lay dn q s).e) + BitVec.ofNat 64 (384 + (lay dn q s).e))
        s.lr).writeW (s.sp - BitVec.ofNat 64 (400 + (lay dn q s).e) + BitVec.ofNat 64 96) (s.sp - 48)
  generalize (lay dn q s).e = e
  have h₁ : s.sp - 48 = s.sp - BitVec.ofNat 64 (400 + e) + BitVec.ofNat 64 (352 + e) := by
    simp only [← BitVec.ofNat_add_ofNat]; generalize BitVec.ofNat 64 e = E; bv_omega_using []
  have h₂ : s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 (400 + e) + BitVec.ofNat 64 (384 + e) := by
    simp only [← BitVec.ofNat_add_ofNat]; generalize BitVec.ofNat 64 e = E; bv_omega_using []
  have h₃ : s.sp - 48 - BitVec.ofNat 64 (256 + e) = s.sp - BitVec.ofNat 64 (400 + e) + BitVec.ofNat 64 96 := by
    simp only [← BitVec.ofNat_add_ofNat]; generalize BitVec.ofNat 64 e = E; bv_omega_using []
  rw [h₃, h₂, write8, write8, write8, ← h₁]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
