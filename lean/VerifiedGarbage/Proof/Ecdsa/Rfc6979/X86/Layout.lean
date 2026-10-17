module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Spec.Rc2

/-!
# Deterministic ECDSA on x86 (32-bit): where everything is

The function's arguments (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`digest_len`, `scratch`, `hash`, and `esp` on entry `E`) and the 536 bytes of
stack below the return address, from `B = E - 536` up (`Lay dn`): the 76
bytes the calls use (a frame of at most six arguments, the return address,
and the 48 bytes HMAC's functions use below it), then the frame of 460
bytes, from `B + 76` (`esp` in the body, `F`): `K` and `V` (64 bytes each),
the hash function's sizes (`B + 204`, eight words: `Lay.pv`), the offset and
count of the candidate's `V`s, the number of candidates left, our caller's
`ebx`, `esi`, `edi` and `ebp` (`B + 256`), `h` (`B + 272`), `X` (`B + 340`)
and the candidate (`B + 408`, 128 bytes). Above it, the return address and
our arguments. `Ctx0` is what holds between the frame's allocation and
release: the permissions, `esp`, the saved registers, our arguments, immutable
table contents and public symbol addresses, and that memory changed only in
`out`, `scratch` and the stack; `Ctx` adds the hash function's sizes, once
the code has stored them. Code that writes only regions apart from the saved
registers, the sizes and our arguments (`Safe`) keeps them (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp

/-- The arguments (`out`, `d`, `digest`, `scratch`, `digest_len`, `hash`),
`esp` on entry, and the sizes of the scalars and of the hash function, for a
digest of `dn` bytes. -/
structure Lay (dn : Nat) where
  a0 : BitVec 32
  a1 : BitVec 32
  a2 : BitVec 32
  a3 : BitVec 32
  dl : BitVec 32
  hs : BitVec 32
  E : BitVec 32
  q : Nat
  /-- The hash function's block size. -/
  Bk : Nat
  /-- The number of `V`s in a candidate. -/
  nb : Nat
  cs : List (String × List (BitVec 64))
  sy : String → BitVec 32

namespace Lay

variable {dn : Nat} (L : Lay dn)

/-- Argument `i`, as the code numbers them. -/
def a : Nat → BitVec 32
  | 0 => L.a0
  | 1 => L.a1
  | 2 => L.a2
  | 3 => L.dl
  | 4 => L.a3
  | _ => L.hs

/-- The hash function's sizes, as the frame holds them (`Cfg.sizes`). -/
def pv : Nat → BitVec 32
  | 0 => BitVec.ofNat 32 dn
  | 1 => BitVec.ofNat 32 L.Bk
  | 2 => BitVec.ofNat 32 (dn + 1)
  | 3 => BitVec.ofNat 32 (dn + 1 + 2 * L.q)
  | 4 => BitVec.ofNat 32 (L.Bk + dn)
  | 5 => BitVec.ofNat 32 (L.Bk + dn + 1)
  | 6 => BitVec.ofNat 32 (L.Bk + dn + 1 + 2 * L.q)
  | _ => BitVec.ofNat 32 L.nb

abbrev out : Addr := L.a0.setWidth 64
abbrev d : Addr := L.a1.setWidth 64
abbrev dg : Addr := L.a2.setWidth 64
abbrev scr : Addr := L.a3.setWidth 64
/-- `esp` in the frame's body. -/
abbrev F : BitVec 32 := L.E - BitVec.ofNat 32 460
/-- The lowest byte of the stack used. -/
abbrev B : Addr := (L.E - BitVec.ofNat 32 536).setWidth 64

abbrev TBLs : List Region := Abi.constRegions (fun n => (L.sy n).setWidth 64) L.cs

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 536⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 76, 460⟩
/-- The return address, and our arguments. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 536, 4⟩
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 540, 24⟩
/-- The stack the calls use, and `K` and `V`. -/
abbrev LOW : Region := ⟨L.B, 204⟩
/-- The offset and count of the candidate's `V`s, and the count of candidates. -/
abbrev CNT : Region := ⟨L.B + BitVec.ofNat 64 236, 20⟩
/-- `h`, `X` and the candidate. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 272, 264⟩

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
  e536 : 536 ≤ L.E.toNat
  e28 : L.E.toNat + 28 ≤ 2 ^ 32
  tbl : ∀ T ∈ L.TBLs, T.base.toNat + T.len ≤ 2 ^ 32 ∧
    T.Disjoint L.OUT ∧ T.Disjoint L.SCR ∧ T.Disjoint L.STK

end Lay

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem B_eq (h : L.Ok) : L.B = L.E.setWidth 64 - BitVec.ofNat 64 536 := Taint.sub_setWidth h.e536

theorem nB (h : L.Ok) : L.B.toNat + 564 ≤ 2 ^ 64 := by
  have := h.e536; have := h.e28
  rw [show L.B.toNat = L.E.toNat - 536 by
    simp only [Lay.B, BitVec.toNat_setWidth]
    rw [sub_toNat (by omega_arith)]; have := L.E.isLt; omega_arith]
  omega_arith

/-- `[F + o]`, for `o` in the frame or the arguments above it. -/
theorem addrF (h : L.Ok) {o : Nat} (ho : o < 488) : addr L.F o = L.B + BitVec.ofNat 64 (76 + o) := by
  have := h.e536; have := h.e28
  have hF : L.F.toNat = L.E.toNat - 460 := sub_toNat (by omega_arith)
  rw [addr_eq (by rw [hF]; omega_arith), Lay.F, Taint.sub_setWidth (by omega_arith), h.B_eq,
    Offset.sub_ofNat_eq _ (show 460 ≤ 536 by omega_arith), show 536 - 460 = 76 by omega_arith, Offset.add_add]

theorem F64 (h : L.Ok) : L.F.setWidth 64 = L.B + BitVec.ofNat 64 76 := by
  have e := h.addrF (o := 0) (by omega_arith)
  rwa [addr, BitVec.add_zero] at e

/-- The frame's 76 bytes below `F`, which the calls use. -/
theorem below_F (h : L.Ok) : below L.F 76 = ⟨L.B, 76⟩ := by
  have := h.e536
  show (⟨(L.F - BitVec.ofNat 32 76).setWidth 64, 76⟩ : Region) = _
  rw [Lay.F, show L.E - BitVec.ofNat 32 460 - BitVec.ofNat 32 76 = L.E - BitVec.ofNat 32 536 by
    rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]]

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 536) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 536) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 536) :
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
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 536) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 76, 460⟩ :=
  ⟨d - 76, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega_arith⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch`, or the stack apart from the hash function's sizes, the saved
registers and our arguments. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.CNT ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 204) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Offset.sub_base _ h)))

theorem safe_cnt {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 236 ≤ d) (h₂ : d + n ≤ 256) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (.inl (Offset.sub _ h₁ h₂))))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

theorem safe_high {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 272 ≤ d) (h₂ : d + n ≤ 536) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (.inr (Offset.sub _ h₁ h₂))))

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr (.inl fun x hx => hs x (h x hx)))),
    .inr (.inr (.inr (.inr fun x hx => hs x (h x hx))))]

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

/-- Two adjacent ranges apart from `r`: so is their union. -/
theorem _root_.VG.Proof.Ecdsa.Rfc6979.X86.disjoint_join {p : Addr} {a b : Nat} {r : Region}
    (h₁ : Region.Disjoint ⟨p, a⟩ r)
    (h₂ : Region.Disjoint ⟨p + BitVec.ofNat 64 a, b⟩ r) : Region.Disjoint ⟨p, a + b⟩ r := by
  intro x hx
  simp only [Region.Contains] at hx
  rcases Nat.lt_or_ge (x - p).toNat a with hl | hl
  · exact h₁ x (by simp only [Region.Contains]; omega_arith)
  · refine h₂ x ?_
    have ha : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
    simp only [Region.Contains]
    rw [Offset.sub_add_eq, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ha]; exact hl), ha]
    omega_arith

/-- A range of the stack apart from every safe region. -/
theorem kept_safe (h : L.Ok) {d n : Nat} (h₁ : 204 ≤ d) (h₂ : d + n ≤ 536)
    (hk : d + n ≤ 236 ∨ (256 ≤ d ∧ d + n ≤ 272)) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have nB := h.nB
  rcases hs with hs | hs | hs | hs | hs
  · exact (h.stk_OUT h₂).sub_right hs
  · exact (h.stk_SCR h₂).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- The return address and our arguments are apart from every safe region. -/
theorem top_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 536, 28⟩ r := by
  have nB := h.nB
  have j : ∀ {r : Region}, L.RET.Disjoint r → L.ARGS.Disjoint r →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 536, 28⟩ r := fun h₂ h₃ =>
    disjoint_join (a := 4) (b := 24) h₂ (by rw [Offset.add_add]; exact h₃)
  rcases hs with hs | hs | hs | hs | hs
  · exact (j h.ro h.ao).sub_right hs
  · exact (j h.rc h.ac).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- The buffers that are only read are apart from every safe region. -/
theorem d_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.D.Disjoint r := by
  rcases hs with hs | hs | hs | hs | hs
  · exact h.od.symm.sub_right hs
  · exact h.dc.sub_right hs
  · exact (h.kd.symm.sub_right (Region.sub_prefix (by omega_arith))).sub_right hs
  · exact (h.kd.symm.sub_right (Offset.sub_base _ (by omega_arith))).sub_right hs
  · exact (h.kd.symm.sub_right (Offset.sub_base _ (by omega_arith))).sub_right hs

theorem dg_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.DG.Disjoint r := by
  rcases hs with hs | hs | hs | hs | hs
  · exact h.og.symm.sub_right hs
  · exact h.gc.sub_right hs
  · exact (h.kg.symm.sub_right (Region.sub_prefix (by omega_arith))).sub_right hs
  · exact (h.kg.symm.sub_right (Offset.sub_base _ (by omega_arith))).sub_right hs
  · exact (h.kg.symm.sub_right (Offset.sub_base _ (by omega_arith))).sub_right hs

end Lay.Ok

/-! ## Between the frame's allocation and release -/

/-- The state between the frame's allocation and release: `g` are the
registers on entry, `m₀` the memory. -/
structure Ctx0 {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.ARGS] ++ L.TBLs
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  esp : t.gpr .esp = L.F
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.X86.saved, t.mem.readW (L.B + BitVec.ofNat 64 (76 + p.2)) 32 = g p.1
  args : ∀ i < 6, t.mem.readW (L.B + BitVec.ofNat 64 (540 + 4 * i)) 32 = L.a i
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : ∀ c ∈ L.cs, t.syms c.1 = L.sy c.1
  held : Abi.constsHeld m₀ (fun n => (L.sy n).setWidth 64) L.cs

/-- `Ctx0`, once the hash function's sizes are in the frame. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop
    extends Ctx0 L g m₀ t where
  prm : ∀ i < 8, t.mem.readW (L.B + BitVec.ofNat 64 (204 + 4 * i)) 32 = L.pv i

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega_arith) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base (p := L.B) (d := 236) (n := 20) (by omega_arith) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base (p := L.B) (d := 272) (n := 264) (by omega_arith) a (h a ha)⟩

theorem saved_off : ∀ p ∈ Impl.Ecdsa.Rfc6979.X86.saved, 180 ≤ p.2 ∧ p.2 + 4 ≤ 196 := by decide

namespace Ctx0

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions and `esp`, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx0 L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms) : Ctx0 L g m₀ t' := by
  have nB := hL.nB
  have keep : ∀ d, 256 ≤ d → d + 4 ≤ 272 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 32 = t.mem.readW (L.B + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 256, 16⟩)
      (Offset.contains _ h₁ (by omega_arith) (by omega_arith))
      (fun r hr => hL.kept_safe (by omega_arith) (by omega_arith) (.inr ⟨Nat.le_refl _, Nat.le_refl _⟩) (hs r hr)) (by decide)
  have keepA : ∀ d, 540 ≤ d → d + 4 ≤ 564 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 32 = t.mem.readW (L.B + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 536, 28⟩)
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)) (fun r hr => hL.top_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, fun p hp => by
    have := saved_off p hp
    rw [keep _ (by omega_arith) (by omega_arith)]
    exact hc.saved p hp, fun i hi => (keepA _ (by omega_arith) (by omega_arith)).trans (hc.args i hi),
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame),
    fun c hc' => by rw [hsy]; exact hc.sy c hc', hc.held⟩

/-- Code that keeps the permissions and `esp`, and writes only the hash
function's sizes. -/
theorem keepP (hL : L.Ok) (hc : Ctx0 L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) {ws : List Region} (hf : Frame ws t.mem t'.mem)
    (hs : ∀ r ∈ ws, Region.Sub r ⟨L.B + BitVec.ofNat 64 204, 32⟩) (hsy : t'.syms = t.syms) : Ctx0 L g m₀ t' := by
  have nB := hL.nB
  have keep : ∀ d, 256 ≤ d → d + 4 ≤ 272 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 32 = t.mem.readW (L.B + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 256, 16⟩)
      (Offset.contains _ h₁ (by omega_arith) (by omega_arith))
      (fun r hr => (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right (hs r hr)) (by decide)
  have keepA : ∀ d, 540 ≤ d → d + 4 ≤ 564 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 32 = t.mem.readW (L.B + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 536, 28⟩)
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      (fun r hr => (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, fun p hp => by
    have := saved_off p hp
    rw [keep _ (by omega_arith) (by omega_arith)]
    exact hc.saved p hp, fun i hi => (keepA _ (by omega_arith) (by omega_arith)).trans (hc.args i hi),
    hc.frame.trans (hf.sub fun r hr => ⟨L.STK, by simp, fun a ha =>
      Offset.sub_base (p := L.B) (d := 204) (n := 32) (by omega_arith) a (hs r hr a ha)⟩),
    fun c hc' => by rw [hsy]; exact hc.sy c hc', hc.held⟩

/-- Code that writes only registers but `esp`. -/
theorem regs (hL : L.Ok) (hc : Ctx0 L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsy : t'.syms = t.syms) : Ctx0 L g m₀ t' :=
  hc.keep hL hrd hwr hsp (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp) hsy

/-- A byte of `d`, as on entry. -/
theorem d_byte (hL : L.Ok) (hc : Ctx0 L g m₀ t) {i : Nat} (hi : i < L.q) :
    t.mem (L.d + BitVec.ofNat 64 i) = m₀ (L.d + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.D) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.od.symm
    · exact hL.dc
    · exact hL.kd.symm) (by show L.q ≤ 2 ^ 64; have := hL.nd; omega_arith) hi

/-- A byte of `digest`, as on entry. -/
theorem dg_byte (hL : L.Ok) (hc : Ctx0 L g m₀ t) {i : Nat} (hi : i < dn) :
    t.mem (L.dg + BitVec.ofNat 64 i) = m₀ (L.dg + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.DG) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.og.symm
    · exact hL.gc
    · exact hL.kg.symm) (by show dn ≤ 2 ^ 64; have := hL.ng; omega_arith) hi

theorem inFr (hc : Ctx0 L g m₀ t) {d : Nat} (h₁ : 76 ≤ d) (h₂ : d + 4 ≤ 536) (hL : L.Ok) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 4 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by have := hL.nB; omega_arith)⟩

theorem inFrW (hc : Ctx0 L g m₀ t) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 536) (hL : L.Ok) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by have := hL.nB; omega_arith)⟩

theorem inArgs (hc : Ctx0 L g m₀ t) {i : Nat} (hi : i < 6) (hL : L.Ok) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (540 + 4 * i)) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ (by omega_arith) (by omega_arith) (by have := hL.nB; omega_arith)⟩

theorem inScr (hc : Ctx0 L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inScrW (hc : Ctx0 L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inD (hc : Ctx0 L g m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 72) :
    InRegions (t.rd ++ t.wr) (L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inDg (hc : Ctx0 L g m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 72) :
    InRegions (t.rd ++ t.wr) (L.dg + BitVec.ofNat 64 o) n :=
  ⟨L.DG, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

/-- Regions within the buffers and the frame are permitted. -/
theorem covers (hc : Ctx0 L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.ARGS, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hR ⊢; rcases hR with h | h | h | h | h | h <;> simp [h], hw⟩

theorem coversW (hc : Ctx0 L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.wr]; exact hR, hw⟩

end Ctx0

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions and `esp`, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms) : Ctx L g m₀ t' :=
  have nB := hL.nB
  ⟨hc.toCtx0.keep hL hrd hwr hsp hf hs hsy, fun i hi => (hf.readW (r := ⟨L.B + BitVec.ofNat 64 204, 32⟩)
    (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun r hr => hL.kept_safe (by omega_arith) (by omega_arith) (.inl (by omega_arith)) (hs r hr)) (by decide)).trans
    (hc.prm i hi)⟩

/-- Code that writes only registers but `esp`. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsy : t'.syms = t.syms) : Ctx L g m₀ t' :=
  hc.keep hL hrd hwr hsp (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp) hsy

end Ctx

/-! ## The frame's allocation -/

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q` bytes, a hash function of `Bk`-byte blocks and `nb` `V`s to a candidate. -/
def lay (dn q Bk nb : Nat) (s : State) (cs : List (String × List (BitVec 64)) := []) : Lay dn :=
  ⟨arg s 0, arg s 1, arg s 2, arg s 4, arg s 3, arg s 5, s.gpr .esp, q, Bk, nb, cs,
    fun n => if n ∈ cs.map Prod.fst then s.syms n else 0⟩

theorem lay_sy (dn q Bk nb : Nat) (s : State) (cs : List (String × List (BitVec 64)))
    {c : String × List (BitVec 64)} (hc : c ∈ cs) : (lay dn q Bk nb s cs).sy c.1 = s.syms c.1 := by
  exact ite_eq_left (List.mem_map.mpr ⟨c, hc, rfl⟩)

theorem lay_tbls (dn q Bk nb : Nat) (s : State) (cs : List (String × List (BitVec 64))) :
    (lay dn q Bk nb s cs).TBLs = Abi.constRegions (fun n => (s.syms n).setWidth 64) cs := by
  apply List.map_congr_left
  intro c hc
  simp only [lay_sy dn q Bk nb s cs hc]

theorem lay_a (dn q Bk nb : Nat) (s : State) (cs : List (String × List (BitVec 64))) :
    ∀ i < 6, (lay dn q Bk nb s cs).a i = arg s i
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl

/-- Our arguments' slots. -/
theorem lay_ARGS {dn q Bk nb : Nat} {s : State} {cs : List (String × List (BitVec 64))}
    (e536 : 536 ≤ (s.gpr .esp).toNat) (e28 : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) :
    (lay dn q Bk nb s cs).ARGS = ⟨argAddr s 0, 24⟩ := by
  have hB : (lay dn q Bk nb s cs).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 536 := Taint.sub_setWidth e536
  show (⟨(lay dn q Bk nb s cs).B + BitVec.ofNat 64 540, 24⟩ : Region) = _
  rw [hB]
  refine congrArg (fun x => (⟨x, 24⟩ : Region)) ?_
  show _ = (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s.gpr .esp) 4 from rfl,
    addr_eq (by omega_arith), show (540 : Nat) = 536 + 4 by omega_arith, ← Offset.add_add, BitVec.sub_add_cancel]

/-- The layout of a call whose precondition holds. -/
abbrev layOf (I : Spec.Ecdsa.Rfc6979.Instance) (Bk nb : Nat) (s : State) (cs : List (String × List (BitVec 64))) :
    Lay I.hashLen := lay I.hashLen I.ecdsa.curve.len Bk nb s cs

theorem lay_ok {I : Spec.Ecdsa.Rfc6979.Instance} {k Bk nb : Nat} {s : State} {cs : List (String × List (BitVec 64))}
    (h : (rfcX86 I k 536 cs).pre s) : (layOf I Bk nb s cs).Ok := by
  obtain ⟨e536, e28, -, -, od, og, oc, dc, gc, ao, ac, ro, rc, ko, kd, kg, kc, no, nd, ng, nc, -, -, ht⟩ := h
  have hB : (layOf I Bk nb s cs).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 536 := Taint.sub_setWidth e536
  have eR : (layOf I Bk nb s cs).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
    show (⟨(layOf I Bk nb s cs).B + BitVec.ofNat 64 536, 4⟩ : Region) = _
    rw [hB, BitVec.sub_add_cancel]
  have eA := lay_ARGS (dn := I.hashLen) (q := I.ecdsa.curve.len) (Bk := Bk) (nb := nb) (cs := cs) e536 e28
  have eK : (layOf I Bk nb s cs).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 536, 536⟩ := by
    show (⟨(layOf I Bk nb s cs).B, 536⟩ : Region) = _
    rw [hB]
  refine ⟨od, og, oc, dc, gc, eA ▸ ao, eA ▸ ac, eR ▸ ro, eR ▸ rc, eK ▸ ko, eK ▸ kd, eK ▸ kg, eK ▸ kc,
    no, nd, ng, nc, e536, e28, ?_⟩
  intro T hT
  rw [lay_tbls] at hT
  have hh := ht.2 T hT
  exact ⟨hh.1, hh.2 _ (by simp [Lay.OUT, Lay.out, lay]), hh.2 _ (by simp [Lay.SCR, Lay.scr, lay]), by rw [eK]; exact hh.2 _ (by simp)⟩

/-- The state after the frame's allocation. -/
abbrev entered (s : State) : State := allocState 460 s

theorem entered_esp (dn q Bk nb : Nat) (s : State) (cs : List (String × List (BitVec 64)) := []) :
    (entered s).gpr .esp = (lay dn q Bk nb s cs).F := by
  simp only [entered, allocState_esp]; rfl

theorem entered_wr {I : Spec.Ecdsa.Rfc6979.Instance} {k Bk nb : Nat} {s : State} {cs : List (String × List (BitVec 64))}
    (h : (rfcX86 I k 536 cs).pre s) :
    (entered s).wr = (layOf I Bk nb s cs).FR :: s.wr := by
  simp only [entered, allocState_wr]
  congr 1
  show (⟨(layOf I Bk nb s cs).F.setWidth 64, 460⟩ : Region) = _
  rw [(lay_ok (Bk := Bk) (nb := nb) h).F64]

/-- The release of the frame. -/
def released (s₂ : State) : State :=
  { s₂.setReg .esp (s₂.gpr .esp + BitVec.ofNat 32 460) with wr := s₂.wr.tail }

/-- The frame: its body, which never writes `esp`, runs from `entered s`,
and the frame's release leads to `released s₂`. -/
theorem WP.alloc {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : 460 ≤ (s.gpr .esp).toNat) (hsp : NoSp body)
    (hb : WP isa body (entered s) fun s₂ => Q (released s₂)) :
    WP isa (.frame (.alloc 460) body (.free 460)) s Q := by
  obtain ⟨t, s₂, he', hq⟩ := hb
  obtain ⟨-, hw⟩ := Exec.rdwr he'
  have hp := Exec.gpr hsp he'
  have hpush : isa.push (.alloc 460) s = some (entered s) := by
    simp only [isa, push]
    exact ite_eq_left ⟨by omega_arith, by omega_arith, trivial, hn⟩
  have hpop : isa.pop (.free 460) (entered s) s₂ = some (released s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by omega_arith, by omega_arith, trivial, hp, hw, rfl⟩
  exact ⟨_, _, Exec.frame hpush he' hpop, hq⟩

/-- Our caller's registers, saved: `Ctx0` holds. -/
theorem save_ok {I : Spec.Ecdsa.Rfc6979.Instance} {k Bk nb : Nat} {s : State} {cs : List (String × List (BitVec 64))}
    (h : (rfcX86 I k 536 cs).pre s) {is : List Instr}
    {Q : State → Prop} (hQ : ∀ t, Ctx0 (layOf I Bk nb s cs) s.gpr s.mem t → (∀ r, r ≠ .esp → t.gpr r = s.gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Ecdsa.Rfc6979.X86.save ++ is)) (entered s) Q := by
  have hL := lay_ok (Bk := Bk) (nb := nb) h
  have nB := hL.nB
  have hesp : (entered s).gpr .esp = (layOf I Bk nb s cs).F := entered_esp _ _ _ _ s cs
  have hw : ∀ o, o + 4 ≤ 460 → InRegions (entered s).wr (addr (layOf I Bk nb s cs).F o) 4 := fun o ho =>
    ⟨(layOf I Bk nb s cs).FR, by rw [entered_wr (Bk := Bk) (nb := nb) h]; simp, by
      rw [hL.addrF (by omega_arith)]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
  have hg : ∀ r, r ≠ .esp → (entered s).gpr r = s.gpr r := fun r hr => allocState_gpr _ _ hr
  simp only [Impl.Ecdsa.Rfc6979.X86.save, Impl.Ecdsa.Rfc6979.X86.saved, Impl.Ecdsa.Rfc6979.X86.fSave,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, Impl.Ecdsa.Rfc6979.X86.stk, Nat.reduceAdd]
  refine wp_stm hesp (hw 180 (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_stm (B := (layOf I Bk nb s cs).F) (by rw [u₁.gpr, hesp]) (by rw [u₁.wr]; exact hw 184 (by omega_arith))
    fun s₂ u₂ => ?_
  refine wp_stm (B := (layOf I Bk nb s cs).F) (by rw [u₂.gpr, u₁.gpr, hesp])
    (by rw [u₂.wr, u₁.wr]; exact hw 188 (by omega_arith)) fun s₃ u₃ => ?_
  refine wp_stm (B := (layOf I Bk nb s cs).F) (by rw [u₃.gpr, u₂.gpr, u₁.gpr, hesp])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw 192 (by omega_arith)) fun s₄ u₄ => hQ s₄ ?_ fun r hr => ?_
  · have sep : ∀ x y, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 564 → y + 4 ≤ 564 →
        Mem.Sep ((layOf I Bk nb s cs).B + BitVec.ofNat 64 x) (32 / 8) ((layOf I Bk nb s cs).B + BitVec.ofNat 64 y) (32 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega_arith) (by omega_arith)
    have a : ∀ o, o < 488 → addr (layOf I Bk nb s cs).F o = (layOf I Bk nb s cs).B + BitVec.ofNat 64 (76 + o) :=
      fun o ho => hL.addrF ho
    have m₄ : s₄.mem = (((s.mem.writeW ((layOf I Bk nb s cs).B + BitVec.ofNat 64 256) (s.gpr .ebx)).writeW
        ((layOf I Bk nb s cs).B + BitVec.ofNat 64 260) (s.gpr .esi)).writeW
        ((layOf I Bk nb s cs).B + BitVec.ofNat 64 264) (s.gpr .edi)).writeW
        ((layOf I Bk nb s cs).B + BitVec.ofNat 64 268) (s.gpr .ebp) := by
      simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr]
      rw [a 180 (by omega_arith), a 184 (by omega_arith), a 188 (by omega_arith), a 192 (by omega_arith),
        hg .ebx (by decide), hg .esi (by decide), hg .edi (by decide), hg .ebp (by decide)]
      rfl
    have pa : ∀ i < 6, s₄.mem.readW ((layOf I Bk nb s cs).B + BitVec.ofNat 64 (540 + 4 * i)) 32 = arg s i :=
      fun i hi => by
        rw [m₄, Mem.readW_writeW_sep (sep (540 + 4 * i) 268 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_sep (sep (540 + 4 * i) 264 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_sep (sep (540 + 4 * i) 260 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_sep (sep (540 + 4 * i) 256 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        show _ = s.mem.readW (argAddr s i) 32
        congr 1
        show _ = addr (s.gpr .esp) (4 + 4 * i)
        rw [addr_eq (by have := h.2.1; omega_arith), hL.B_eq, show 540 + 4 * i = 536 + (4 + 4 * i) by omega_arith,
          ← Offset.add_add, BitVec.sub_add_cancel]
        rfl
    have ct : ∀ x, 256 ≤ x → x + 4 ≤ 272 →
        (layOf I Bk nb s cs).STK.Contains ((layOf I Bk nb s cs).B + BitVec.ofNat 64 x) (32 / 8) :=
      fun x h₁ h₂ => Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine ⟨by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]; show s.rd = _; rw [h.2.2.1, lay_ARGS h.1 h.2.1, lay_tbls]; rfl,
      by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, entered_wr (Bk := Bk) (nb := nb) h, h.2.2.2.1]; rfl, by
        rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact hesp, fun p hp => ?_,
        fun i hi => (pa i hi).trans (lay_a _ _ _ _ s cs i hi).symm, ?_, ?_, ?_⟩
    · simp only [Impl.Ecdsa.Rfc6979.X86.saved, Impl.Ecdsa.Rfc6979.X86.fSave, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rw [m₄]
      rcases hp with rfl | rfl | rfl | rfl <;> dsimp only [Nat.reduceAdd]
      · rw [Mem.readW_writeW_sep (sep 256 268 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_sep (sep 256 264 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_sep (sep 256 260 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (sep 260 268 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_sep (sep 260 264 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (sep 264 268 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_self32]
    · rw [m₄]
      exact (((Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _
        (ct 256 (by omega_arith) (by omega_arith))).writeW (by simp) _ (ct 260 (by omega_arith) (by omega_arith))).writeW (by simp) _
        (ct 264 (by omega_arith) (by omega_arith)) |>.writeW (by simp) _ (ct 268 (by omega_arith) (by omega_arith))
    · intro c hc
      change c ∈ cs at hc
      rw [u₄.syms, u₃.syms, u₂.syms, u₁.syms, lay_sy I.hashLen I.ecdsa.curve.len Bk nb s cs hc]
      rfl
    · have ht := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      intro c hc
      change c ∈ cs at hc
      simpa only [lay_sy I.hashLen I.ecdsa.curve.len Bk nb s cs hc] using ht.1 c hc
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact hg r hr

end VG.Proof.Ecdsa.Rfc6979.X86
