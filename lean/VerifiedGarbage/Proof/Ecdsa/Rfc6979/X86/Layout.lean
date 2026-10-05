import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Contract

/-!
# Deterministic ECDSA on x86 (32-bit): where everything is

The function's arguments (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`, and `esp` on entry `E`) and the 272 bytes of stack below the
return address, from `B = E - 272` up (`Lay dn`): the 76 bytes the calls use
(a frame of at most six arguments, the return address, and the 48 bytes
HMAC's functions use below it), then the frame of 196 bytes, from `B + 76`
(`esp` in the body, `F`): `K` and `V` (64 bytes each), `h` (48 bytes, of
which `q` are used), the number of
candidates left, and our caller's `ebx`, `esi`, `edi` and `ebp`. Above it,
the return address and our arguments. `Ctx` is what holds between the
frame's allocation and release: the permissions, `esp`, the saved
registers, and that memory changed only in `out`, `scratch` and the stack.
Code that writes only regions below the saved registers (`Safe`) keeps it
(`Ctx.keep`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp

/-- The arguments (`out`, `d`, `digest`, `scratch`) and `esp` on entry, for
a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) where
  a0 : BitVec 32
  a1 : BitVec 32
  a2 : BitVec 32
  a3 : BitVec 32
  E : BitVec 32
  q : Nat

namespace Lay

variable {dn : Nat} (L : Lay dn)

abbrev out : Addr := L.a0.setWidth 64
abbrev d : Addr := L.a1.setWidth 64
abbrev dg : Addr := L.a2.setWidth 64
abbrev scr : Addr := L.a3.setWidth 64
/-- `esp` in the frame's body. -/
abbrev F : BitVec 32 := L.E - BitVec.ofNat 32 196
/-- The lowest byte of the stack used. -/
abbrev B : Addr := (L.E - BitVec.ofNat 32 272).setWidth 64

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 272⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 76, 196⟩
/-- The return address, and our arguments. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 272, 4⟩
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 276, 16⟩
/-- The stack below the saved registers: the calls', and `K`, `V`, `h` and the count. -/
abbrev LOW : Region := ⟨L.B, 256⟩

/-- What the contract says of where the buffers and the stack are (`d` and
`digest`, which are only read, may overlap). -/
structure Ok : Prop where
  od : L.OUT.Disjoint L.D
  og : L.OUT.Disjoint L.DG
  oc : L.OUT.Disjoint L.SCR
  dc : L.D.Disjoint L.SCR
  gc : L.DG.Disjoint L.SCR
  ao : L.ARGS.Disjoint L.OUT
  ac : L.ARGS.Disjoint L.SCR
  ro : L.RET.Disjoint L.OUT
  rc : L.RET.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  kd : L.STK.Disjoint L.D
  kg : L.STK.Disjoint L.DG
  kc : L.STK.Disjoint L.SCR
  no : L.a0.toNat + 2 * L.q ≤ 2 ^ 32
  nd : L.a1.toNat + L.q ≤ 2 ^ 32
  ng : L.a2.toNat + dn ≤ 2 ^ 32
  nc : L.a3.toNat + 8192 ≤ 2 ^ 32
  e272 : 272 ≤ L.E.toNat
  e20 : L.E.toNat + 20 ≤ 2 ^ 32

end Lay

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem B_eq (h : L.Ok) : L.B = L.E.setWidth 64 - BitVec.ofNat 64 272 := Taint.sub_setWidth h.e272

theorem nB (h : L.Ok) : L.B.toNat + 292 ≤ 2 ^ 64 := by
  have := h.e272; have := h.e20
  rw [show L.B.toNat = L.E.toNat - 272 by
    simp only [Lay.B, BitVec.toNat_setWidth]
    rw [sub_toNat (by omega)]; have := L.E.isLt; omega]
  omega

/-- `[F + o]`, for `o` in the frame or the arguments above it. -/
theorem addrF (h : L.Ok) {o : Nat} (ho : o < 216) : addr L.F o = L.B + BitVec.ofNat 64 (76 + o) := by
  have := h.e272; have := h.e20
  have hF : L.F.toNat = L.E.toNat - 196 := sub_toNat (by omega)
  rw [addr_eq (by rw [hF]; omega), Lay.F, Taint.sub_setWidth (by omega), h.B_eq,
    Offset.sub_ofNat_eq _ (show 196 ≤ 272 by omega), Offset.add_add]

theorem F64 (h : L.Ok) : L.F.setWidth 64 = L.B + BitVec.ofNat 64 76 := by
  have e := h.addrF (o := 0) (by omega)
  rwa [addr, BitVec.add_zero] at e

/-- The frame's 76 bytes below `F`, which the calls use. -/
theorem below_F (h : L.Ok) : below L.F 76 = ⟨L.B, 76⟩ := by
  have := h.e272
  show (⟨(L.F - BitVec.ofNat 32 76).setWidth 64, 76⟩ : Region) = _
  rw [Lay.F, show L.E - BitVec.ofNat 32 196 - BitVec.ofNat 32 76 = L.E - BitVec.ofNat 32 272 by
    rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]]

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 272) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 272) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 272) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 272) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 272) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 272) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame. -/
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 272) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 76, 196⟩ :=
  ⟨d - 76, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below the saved registers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 256) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (Offset.sub_base _ h))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

/-- Two adjacent ranges apart from `r`: so is their union. -/
theorem _root_.VG.Proof.Ecdsa.Rfc6979.X86.disjoint_join {p : Addr} {a b : Nat} {r : Region}
    (h₁ : Region.Disjoint ⟨p, a⟩ r)
    (h₂ : Region.Disjoint ⟨p + BitVec.ofNat 64 a, b⟩ r) : Region.Disjoint ⟨p, a + b⟩ r := by
  intro x hx
  simp only [Region.Contains] at hx
  rcases Nat.lt_or_ge (x - p).toNat a with hl | hl
  · exact h₁ x (by simp only [Region.Contains]; omega)
  · refine h₂ x ?_
    have ha : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    simp only [Region.Contains]
    rw [Offset.sub_add_eq, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ha]; exact hl), ha]
    omega

/-- The saved registers, the return address and our arguments are apart
from every safe region. -/
theorem top_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 256, 36⟩ r := by
  have nB := h.nB
  have j : ∀ {r : Region}, Region.Disjoint ⟨L.B + BitVec.ofNat 64 256, 16⟩ r → L.RET.Disjoint r →
      L.ARGS.Disjoint r → Region.Disjoint ⟨L.B + BitVec.ofNat 64 256, 36⟩ r := fun h₁ h₂ h₃ =>
    disjoint_join (a := 16) (b := 20) h₁ (by
      rw [Offset.add_add]
      exact disjoint_join (a := 4) (b := 16) h₂ (by rw [Offset.add_add]; exact h₃))
  rcases hs with hs | hs | hs
  · exact (j (h.stk_OUT (by omega)) h.ro h.ao).sub_right hs
  · exact (j (h.stk_SCR (by omega)) h.rc h.ac).sub_right hs
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

/-! ## Between the frame's allocation and release -/

/-- The state between the frame's allocation and release: `g` are the
registers on entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.ARGS]
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  esp : t.gpr .esp = L.F
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.X86.saved, t.mem.readW (L.B + BitVec.ofNat 64 (76 + p.2)) 32 = g p.1
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 276) 32 = L.a0
  pD : t.mem.readW (L.B + BitVec.ofNat 64 280) 32 = L.a1
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 284) 32 = L.a2
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 288) 32 = L.a3
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega) a (h a ha)⟩

theorem saved_off : ∀ p ∈ Impl.Ecdsa.Rfc6979.X86.saved, 180 ≤ p.2 ∧ p.2 + 4 ≤ 196 := by decide

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions and `esp`, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) :
    Ctx L g m₀ t' := by
  have nB := hL.nB
  have keep : ∀ d, 256 ≤ d → d + 4 ≤ 292 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 32 = t.mem.readW (L.B + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 256, 36⟩)
      (Offset.contains _ h₁ (by omega) (by omega)) (fun r hr => hL.top_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, fun p hp => by
    have := saved_off p hp
    rw [keep _ (by omega) (by omega)]
    exact hc.saved p hp, (keep 276 (by omega) (by omega)).trans hc.pOut,
    (keep 280 (by omega) (by omega)).trans hc.pD, (keep 284 (by omega) (by omega)).trans hc.pDg,
    (keep 288 (by omega) (by omega)).trans hc.pScr,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame)⟩

/-- Code that writes only registers but `esp`. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.gpr .esp = t.gpr .esp) : Ctx L g m₀ t' :=
  hc.keep hL hrd hwr hsp (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- A byte of `d`, as on entry. -/
theorem d_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.q) :
    t.mem (L.d + BitVec.ofNat 64 i) = m₀ (L.d + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.D) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.od.symm
    · exact hL.dc
    · exact hL.kd.symm) (by show L.q ≤ 2 ^ 64; have := hL.nd; omega) hi

/-- A byte of `digest`, as on entry. -/
theorem dg_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < dn) :
    t.mem (L.dg + BitVec.ofNat 64 i) = m₀ (L.dg + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.DG) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.og.symm
    · exact hL.gc
    · exact hL.kg.symm) (by show dn ≤ 2 ^ 64; have := hL.ng; omega) hi

theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₁ : 76 ≤ d) (h₂ : d + 4 ≤ 272) (hL : L.Ok) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 4 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 272) (hL : L.Ok) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

theorem inArgs (hc : Ctx L g m₀ t) {i : Nat} (hi : i < 4) (hL : L.Ok) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (276 + 4 * i)) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ (by omega) (by omega) (by have := hL.nB; omega)⟩

theorem inScr (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inScrW (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inD (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inDg (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.dg + BitVec.ofNat 64 o) n :=
  ⟨L.DG, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

/-- Regions within the buffers and the frame are permitted. -/
theorem covers (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.ARGS, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simpa using hR, hw⟩

theorem coversW (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.wr]; exact hR, hw⟩

end Ctx

/-! ## The frame's allocation -/

/-- The layout of a call from `s`, with a digest of `dn` bytes and scalars of `q`. -/
def lay (dn q : Nat) (s : State) : Lay dn := ⟨arg s 0, arg s 1, arg s 2, arg s 3, s.gpr .esp, q⟩

/-- Our arguments' slots. -/
theorem lay_ARGS {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (e272 : 272 ≤ (s.gpr .esp).toNat)
    (e20 : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) : (lay I.hashLen I.ecdsa.curve.len s).ARGS = ⟨argAddr s 0, 16⟩ := by
  have hB : (lay I.hashLen I.ecdsa.curve.len s).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 272 :=
    Taint.sub_setWidth e272
  simp only [Lay.ARGS, hB]
  congr 1
  show _ = (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s.gpr .esp) 4 from rfl,
    addr_eq (by omega), show (276 : Nat) = 272 + 4 from rfl, ← Offset.add_add, BitVec.sub_add_cancel]

theorem lay_ok {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcX86 I).pre s) : (lay I.hashLen I.ecdsa.curve.len s).Ok := by
  obtain ⟨e272, e20, -, -, od, og, oc, dc, gc, ao, ac, ro, rc, ko, kd, kg, kc, no, nd, ng, nc⟩ := h
  have hB : (lay I.hashLen I.ecdsa.curve.len s).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 272 :=
    Taint.sub_setWidth e272
  have eR : (lay I.hashLen I.ecdsa.curve.len s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
    simp only [Lay.RET, hB, BitVec.sub_add_cancel]
  have eA := lay_ARGS (I := I) e272 e20
  have eK : (lay I.hashLen I.ecdsa.curve.len s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 272, 272⟩ := by
    simp only [Lay.STK, hB]
  exact ⟨od, og, oc, dc, gc, eA ▸ ao, eA ▸ ac, eR ▸ ro, eR ▸ rc, eK ▸ ko, eK ▸ kd, eK ▸ kg, eK ▸ kc,
    no, nd, ng, nc, e272, e20⟩

/-- The state after the frame's allocation. -/
abbrev entered (s : State) : State := allocState Impl.Ecdsa.Rfc6979.X86.frameBytes s

theorem entered_esp (dn q : Nat) (s : State) : (entered s).gpr .esp = (lay dn q s).F := by
  simp only [entered, allocState_esp, Impl.Ecdsa.Rfc6979.X86.frameBytes]; rfl

theorem entered_wr {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcX86 I).pre s) :
    (entered s).wr = (lay I.hashLen I.ecdsa.curve.len s).FR :: s.wr := by
  simp only [entered, allocState_wr, Impl.Ecdsa.Rfc6979.X86.frameBytes]
  congr 1
  show (⟨(lay I.hashLen I.ecdsa.curve.len s).F.setWidth 64, 196⟩ : Region) = _
  rw [(lay_ok h).F64]

/-- The release of the frame. -/
def released (s₂ : State) : State :=
  { s₂.setReg .esp (s₂.gpr .esp + BitVec.ofNat 32 Impl.Ecdsa.Rfc6979.X86.frameBytes) with wr := s₂.wr.tail }

/-- The frame: its body, which never writes `esp`, runs from `entered s`,
and the frame's release leads to `released s₂`. -/
theorem WP.alloc {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : Impl.Ecdsa.Rfc6979.X86.frameBytes ≤ (s.gpr .esp).toNat) (hsp : NoSp body)
    (hb : WP isa body (entered s) fun s₂ => Q (released s₂)) :
    WP isa (.frame (.alloc Impl.Ecdsa.Rfc6979.X86.frameBytes) body (.free Impl.Ecdsa.Rfc6979.X86.frameBytes)) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := hb
  obtain ⟨-, hw⟩ := Exec.rdwr he
  have hp := Exec.gpr hsp he
  have hpush : isa.push (.alloc Impl.Ecdsa.Rfc6979.X86.frameBytes) s = some (entered s) := by
    simp only [isa, push]
    exact ite_eq_left ⟨by decide, by decide, by decide, hn⟩
  have hpop : isa.pop (.free Impl.Ecdsa.Rfc6979.X86.frameBytes) (entered s) s₂ = some (released s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, hp, hw, rfl⟩
  exact ⟨_, _, Exec.frame hpush he hpop, hq⟩

/-- Our caller's registers, saved: `Ctx` holds. -/
theorem save_ok {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcX86 I).pre s) {is : List Instr}
    {Q : State → Prop} (hQ : ∀ t, Ctx (lay I.hashLen I.ecdsa.curve.len s) s.gpr s.mem t → (∀ r, r ≠ .esp → t.gpr r = s.gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Ecdsa.Rfc6979.X86.Cfg.save ++ is)) (entered s) Q := by
  have hL := lay_ok h
  have nB := hL.nB
  have hesp : (entered s).gpr .esp = (lay I.hashLen I.ecdsa.curve.len s).F := entered_esp _ _ s
  have hw : ∀ o, o + 4 ≤ 196 → InRegions (entered s).wr (addr (lay I.hashLen I.ecdsa.curve.len s).F o) 4 := fun o ho =>
    ⟨(lay I.hashLen I.ecdsa.curve.len s).FR, by rw [entered_wr h]; simp, by
      rw [hL.addrF (by omega)]; exact Offset.contains _ (by omega) (by omega) (by omega)⟩
  have hg : ∀ r, r ≠ .esp → (entered s).gpr r = s.gpr r := fun r hr => allocState_gpr _ _ hr
  simp only [Impl.Ecdsa.Rfc6979.X86.Cfg.save, Impl.Ecdsa.Rfc6979.X86.saved, Impl.Ecdsa.Rfc6979.X86.fSave,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, Impl.Ecdsa.Rfc6979.X86.stk, Nat.reduceAdd]
  refine wp_stm hesp (hw 180 (by omega)) fun s₁ u₁ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len s).F) (by rw [u₁.gpr, hesp]) (by rw [u₁.wr]; exact hw 184 (by omega))
    fun s₂ u₂ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len s).F) (by rw [u₂.gpr, u₁.gpr, hesp])
    (by rw [u₂.wr, u₁.wr]; exact hw 188 (by omega)) fun s₃ u₃ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len s).F) (by rw [u₃.gpr, u₂.gpr, u₁.gpr, hesp])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw 192 (by omega)) fun s₄ u₄ => hQ s₄ ?_ fun r hr => ?_
  · have sep : ∀ x y, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 292 → y + 4 ≤ 292 →
        Mem.Sep ((lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 x) (32 / 8) ((lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 y) (32 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega) (by omega)
    have a : ∀ o, o < 216 → addr (lay I.hashLen I.ecdsa.curve.len s).F o = (lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 (76 + o) :=
      fun o ho => hL.addrF ho
    have m₄ : s₄.mem = (((s.mem.writeW ((lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 256) (s.gpr .ebx)).writeW
        ((lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 260) (s.gpr .esi)).writeW
        ((lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 264) (s.gpr .edi)).writeW
        ((lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 268) (s.gpr .ebp) := by
      simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr]
      rw [a 180 (by omega), a 184 (by omega), a 188 (by omega), a 192 (by omega),
        hg .ebx (by decide), hg .esi (by decide), hg .edi (by decide), hg .ebp (by decide)]
      rfl
    have pa : ∀ i, i < 4 → s₄.mem.readW ((lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 (276 + 4 * i)) 32 = arg s i :=
      fun i hi => by
        rw [m₄, Mem.readW_writeW_sep (sep _ 268 (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (sep _ 264 (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (sep _ 260 (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (sep _ 256 (by omega) (by omega) (by omega)) (by decide)]
        show _ = s.mem.readW (argAddr s i) 32
        congr 1
        show _ = addr (s.gpr .esp) (4 + 4 * i)
        rw [addr_eq (by have := h.2.1; omega), hL.B_eq, show 276 + 4 * i = 272 + (4 + 4 * i) by omega,
          ← Offset.add_add, BitVec.sub_add_cancel]
        rfl
    have ct : ∀ x, 256 ≤ x → x + 4 ≤ 272 →
        (lay I.hashLen I.ecdsa.curve.len s).STK.Contains ((lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 x) (32 / 8) :=
      fun x h₁ h₂ => Offset.contains_base _ (by omega) (by omega)
    refine ⟨by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]; show s.rd = _; rw [h.2.2.1, lay_ARGS h.1 h.2.1]; rfl,
      by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, entered_wr h, h.2.2.2.1]; rfl, by
        rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact hesp, fun p hp => ?_, pa 0 (by omega), pa 1 (by omega),
        pa 2 (by omega), pa 3 (by omega), ?_⟩
    · simp only [Impl.Ecdsa.Rfc6979.X86.saved, Impl.Ecdsa.Rfc6979.X86.fSave, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rw [m₄]
      rcases hp with rfl | rfl | rfl | rfl <;> dsimp only [Nat.reduceAdd]
      · rw [Mem.readW_writeW_sep (sep 256 268 (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (sep 256 264 (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (sep 256 260 (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (sep 260 268 (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (sep 260 264 (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (sep 264 268 (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_self32]
    · rw [m₄]
      exact (((Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _
        (ct 256 (by omega) (by omega))).writeW (by simp) _ (ct 260 (by omega) (by omega))).writeW (by simp) _
        (ct 264 (by omega) (by omega)) |>.writeW (by simp) _ (ct 268 (by omega) (by omega))
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact hg r hr

end VG.Proof.Ecdsa.Rfc6979.X86
