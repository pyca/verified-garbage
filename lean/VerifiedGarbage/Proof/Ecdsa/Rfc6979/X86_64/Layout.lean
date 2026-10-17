module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Contract
import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on x86-64: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`) and the `248 + 8 e` bytes of stack below its return address
(`e = 38`), from `A = B - 8` up (`Lay dn`): the 32 bytes the calls use (a
call's return address, and the 24 bytes HMAC's functions use below theirs),
from `A`, then the
frame of `27 + e` words, from `B + 24`: `K` and `V` (64 bytes each), the
candidate's offset, the number of candidates left, the pointers to
`scratch`, `digest`, `d` and `out`, `core`'s digest, `h` and the candidate
(`HIGH`, 280 bytes), and the hash function's block size `bs`, output length
`hl` and number `sel`. `Ctx` is what holds between the frame's push and pop:
the permissions, `rsp`, the callee-saved registers, the pointers and the
hash function's numbers in the frame, that memory changed only in `out`,
`scratch` and the stack, and where the tables of constants `core` reads are
(`TBLs`, the comb's). Code that writes only regions apart from the pointers
and those numbers (`Safe`) keeps it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- The buffers and the stack below the frame (`rsp - (240 + 8 e)` on entry,
8 bytes above the lowest byte of the stack used), for a digest of `dn` bytes
and scalars of `q`. -/
structure Lay (dn : Nat) where
  out : Addr
  d : Addr
  dg : Addr
  scr : Addr
  B : Addr
  q : Nat
  /-- The words above the frame's pointers. -/
  e : Nat
  he : e = 38
  /-- The hash function's number, output length and block size. -/
  sel : Nat
  hl : Nat
  bs : Nat
  /-- The tables of constants `core` reads, and their statics' addresses. -/
  cs : List (String × List (BitVec 64))
  sy : String → Addr

namespace Lay

variable {dn : Nat} (L : Lay dn)

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The lowest byte of the stack used. -/
def A : Addr := L.B - BitVec.ofNat 64 8
theorem B_eq : L.B = L.A + BitVec.ofNat 64 8 := (BitVec.sub_add_cancel _ _).symm
/-- An offset from `B`, as one from `A`. -/
theorem shift (d : Nat) : L.B + BitVec.ofNat 64 d = L.A + BitVec.ofNat 64 (8 + d) := by
  rw [L.B_eq, Offset.add_add]
/-- The stack used. -/
abbrev STK : Region := ⟨L.A, 248 + 8 * L.e⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 24, 216 + 8 * L.e⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 (240 + 8 * L.e), 8⟩
/-- The stack below the frame's pointers: the calls' and `K`, `V`, `h` and the count. -/
abbrev LOW : Region := ⟨L.A, 216⟩
/-- The stack the calls use. -/
abbrev CALLS : Region := ⟨L.A, 32⟩
/-- The frame above its pointers, below the hash function's numbers. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 240, 280⟩
/-- The tables of constants. -/
abbrev TBLs : List Region := Abi.constRegions L.sy L.cs

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
  ro : L.RET.Disjoint L.OUT
  rd : L.RET.Disjoint L.D
  rg : L.RET.Disjoint L.DG
  rc : L.RET.Disjoint L.SCR
  no : L.out.toNat + 2 * L.q ≤ 2 ^ 64
  nd : L.d.toNat + L.q ≤ 2 ^ 64
  ng : L.dg.toNat + dn ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  /-- The stack used does not wrap around. -/
  nb : L.A.toNat + (248 + 8 * L.e) ≤ 2 ^ 64
  /-- The tables do not wrap around, and are apart from what the code writes. -/
  tbl : ∀ T ∈ L.TBLs, T.base.toNat + T.len ≤ 2 ^ 64 ∧ T.Disjoint L.OUT ∧ T.Disjoint L.SCR ∧ T.Disjoint L.STK

/-- A region at an offset from `B`, apart from the stack below it. -/
theorem disjA {d n k : Nat} (h : k ≤ 8 + d) (hd : 8 + d + n ≤ 2 ^ 64) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.A, k⟩ := by
  rw [L.shift]; exact Offset.disjoint_base _ h hd

/-- A region at an offset from `B`, within the stack from `A`. -/
theorem subA {d n k : Nat} (h : 8 + d + n ≤ k) : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.A, k⟩ := by
  rw [L.shift]; exact Offset.sub_base _ (by omega)

/-- A region of the stack, at an offset from `B`. -/
theorem sub_stk {d n : Nat} (h : d + n ≤ 240 + 8 * L.e) : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK := by
  rw [L.shift]; exact Offset.sub_base _ (by omega)

end Lay

theorem constRegions_congr {f f' : String → Addr} {cs : List (String × List (BitVec 64))}
    (h : ∀ c ∈ cs, f c.1 = f' c.1) : Abi.constRegions f cs = Abi.constRegions f' cs :=
  List.map_congr_left fun c hc => by rw [h c hc]

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
theorem within_fr (B : Addr) {d n x : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 240 + x) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 24, 216 + x⟩ :=
  ⟨d - 24, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below or above the frame's pointers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 208) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (by rw [L.shift]; exact Offset.sub_base _ (by omega))))

theorem safe_calls {dn : Nat} (L : Lay dn) : Safe L L.CALLS :=
  .inr (.inr (.inl (Region.sub_prefix (by omega))))

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

theorem safe_high {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 240 ≤ d) (h₂ : d + n ≤ 520) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ h₂)))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

/-- The stack below the frame does not wrap around. -/
theorem nbB (h : L.Ok) : L.B.toNat + (240 + 8 * L.e) ≤ 2 ^ 64 := by
  have := h.nb
  rw [L.B_eq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (L.sub_stk h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (L.sub_stk h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (L.sub_stk h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (L.sub_stk h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (L.sub_stk h₁)

theorem stk_DG (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (L.sub_stk h₁)

theorem stk_d (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.d, L.q⟩ := h.stk_D h₁

/-- The frame's pointers are apart from every safe region. -/
theorem ptrs_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 208, 32⟩ r := by
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · rw [L.shift]; exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs
  · exact (Offset.disjoint _ (by omega) (by omega) (by omega)).sub_right hs

/-- The hash function's numbers in the frame are apart from every safe region. -/
theorem slots_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 520, 24⟩ r := by
  have := L.he
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · rw [L.shift]; exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs
  · exact (Offset.disjoint _ (by omega) (by omega) (by omega)).sub_right hs

/-- The buffers that are only read are apart from every safe region. -/
theorem d_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.D.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.od.symm.sub_right hs
  · exact h.dc.sub_right hs
  · exact (h.kd.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs
  · have := L.he
    exact (h.kd.symm.sub_right (L.sub_stk (by omega))).sub_right hs

theorem dg_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.DG.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.og.symm.sub_right hs
  · exact h.gc.sub_right hs
  · exact (h.kg.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs
  · have := L.he
    exact (h.kg.symm.sub_right (L.sub_stk (by omega))).sub_right hs

end Lay.Ok

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` are the registers on
entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG] ++ L.TBLs
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 24
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 208) 64 = L.scr
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 216) 64 = L.dg
  pD : t.mem.readW (L.B + BitVec.ofNat 64 224) 64 = L.d
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 232) 64 = L.out
  pBS : t.mem.readW (L.B + BitVec.ofNat 64 520) 64 = BitVec.ofNat 64 L.bs
  pHL : t.mem.readW (L.B + BitVec.ofNat 64 528) 64 = BitVec.ofNat 64 L.hl
  pSel : t.mem.readW (L.B + BitVec.ofNat 64 536) 64 = BitVec.ofNat 64 L.sel
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : ∀ c ∈ L.cs, t.syms c.1 = L.sy c.1
  held : Abi.constsHeld m₀ L.sy L.cs

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.A) (by omega) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => L.sub_stk (d := 240) (n := 280) (by have := L.he; omega) a (h a ha)⟩

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `rsp` and the callee-saved registers,
and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms) : Ctx L g m₀ t' := by
  have keep : ∀ d, 208 ≤ d → d + 8 ≤ 240 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 208, 32⟩)
      (Offset.contains _ h₁ (by omega) (by omega)) (fun r hr => hL.ptrs_safe (hs r hr)) (by decide)
  have keep' : ∀ d, 520 ≤ d → d + 8 ≤ 544 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 520, 24⟩)
      (Offset.contains _ h₁ (by omega) (by omega)) (fun r hr => hL.slots_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.rsp, fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'),
    (keep 208 (by omega) (by omega)).trans hc.pScr, (keep 216 (by omega) (by omega)).trans hc.pDg,
    (keep 224 (by omega) (by omega)).trans hc.pD, (keep 232 (by omega) (by omega)).trans hc.pOut,
    (keep' 520 (by omega) (by omega)).trans hc.pBS, (keep' 528 (by omega) (by omega)).trans hc.pHL,
    (keep' 536 (by omega) (by omega)).trans hc.pSel,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame), by rw [hsy]; exact hc.sy, hc.held⟩

/-- Code that writes only caller-saved registers. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
  hc.keep hL hrd hwr (hg .rsp (by decide)) (fun r hr _ => hg r hr) (ws := []) (by rw [hm]; exact Frame.refl _ _)
    (by simp) hsy

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

theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₁ : 24 ≤ d) (h₂ : d + 8 ≤ 240 + 8 * L.e) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  have := L.he
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 240 + 8 * L.e) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  have := L.he
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

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
theorem mem_regions {R : Region} (h : R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR]) :
    R ∈ [L.D, L.DG] ++ L.TBLs ++ [L.FR, L.OUT, L.SCR] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

theorem covers (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; exact mem_regions hR, hw⟩

theorem coversW (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.wr]; exact hR, hw⟩

end Ctx

/-! ## The frame -/

/-- The state after the frame's allocation of `n` bytes. -/
def allocd (n : Nat) (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp - BitVec.ofNat 64 n) with wr := ⟨s.gpr .rsp - BitVec.ofNat 64 n, n⟩ :: s.wr }

/-- The state after the frame's release of `n` bytes, from the state `s` its body ends in. -/
def freed (n : Nat) (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp + BitVec.ofNat 64 n) with wr := s.wr.tail }

theorem allocd_rsp (n : Nat) (s : State) : (allocd n s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 n :=
  show (s.setReg .rsp (s.gpr .rsp - BitVec.ofNat 64 n)).gpr .rsp = _ from RegUpd.gpr_setReg_self _ _ _
theorem allocd_gpr (n : Nat) (s : State) {r : Reg} (h : r ≠ .rsp) : (allocd n s).gpr r = s.gpr r :=
  RegUpd.gpr_setReg_of_ne _ _ h
theorem freed_gpr (n : Nat) (s : State) {r : Reg} (h : r ≠ .rsp) : (freed n s).gpr r = s.gpr r :=
  RegUpd.gpr_setReg_of_ne _ _ h
theorem freed_rsp (n : Nat) (s : State) : (freed n s).gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 n :=
  show (s.setReg .rsp (s.gpr .rsp + BitVec.ofNat 64 n)).gpr .rsp = _ from RegUpd.gpr_setReg_self _ _ _
@[simp] theorem freed_mem (n : Nat) (s : State) : (freed n s).mem = s.mem := rfl

theorem alloc_some {n : Nat} {s s₁ : State} (h : isa.push (.alloc n) s = some s₁) : s₁ = allocd n s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame of `n` bytes: its body runs from `allocd n s`, ends with `rsp` and
the writable regions as the allocation left them, and the release leads to
`freed n s₂`. -/
theorem WP.frameAlloc {n : Nat} {body : Prog isa} {s : State} {Q : State → Prop} (h₁ : 0 < n) (h₂ : n < 4096)
    (h₃ : n % 8 = 0) (hn : n ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocd n s) fun s₂ => s₂.gpr .rsp = (allocd n s).gpr .rsp ∧
      s₂.wr = (allocd n s).wr ∧ Q (freed n s₂)) :
    WP isa (.frame (.alloc n) body (.free n)) s Q := by
  obtain ⟨t, s₂, he, hsp, hw, hq⟩ := hb
  have hpush : isa.push (.alloc n) s = some (allocd n s) := by
    simp only [isa, push, h₁, h₂, h₃, hn, and_self, ite_true]; rfl
  have hpop : isa.pop (.free n) (allocd n s) s₂ = some (freed n s₂) := by
    simp only [isa, pop]
    refine ite_eq_left ⟨h₁, h₂, h₃, hsp, hw, ?_⟩
    rw [allocd_rsp]; rfl
  exact ⟨_, _, Exec.frame hpush he hpop, hq⟩

/-- Two runs of a frame of `n` bytes leak what its body does. -/
theorem RelCT.frameAlloc {n : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocd n s₁ ∧ b = allocd n s₂) body R) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := alloc_some p₁
      obtain rfl := alloc_some p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q`, the hash function `sel` of output length `hl` and block size `bs`, and
the tables `cs` (the statics' addresses, public, of those tables only). -/
def lay (dn q sel hl bs : Nat) (cs : List (String × List (BitVec 64))) (s : State) : Lay dn :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .r8, s.gpr .rsp - BitVec.ofNat 64 544, q, 38, rfl, sel, hl, bs, cs,
    fun n => if n ∈ cs.map Prod.fst then s.syms n else 0⟩

theorem lay_ret (dn q sel hl bs : Nat) (cs : List (String × List (BitVec 64))) (s : State) :
    (lay dn q sel hl bs cs s).B + BitVec.ofNat 64 (240 + 8 * 38) = s.gpr .rsp :=
  BitVec.sub_add_cancel _ _

theorem lay_sy (dn q sel hl bs : Nat) {cs : List (String × List (BitVec 64))} (s : State) :
    ∀ c ∈ cs, (lay dn q sel hl bs cs s).sy c.1 = s.syms c.1 := fun c hc => by
  simp only [lay, List.mem_map_of_mem (f := Prod.fst) hc, ite_true]

theorem lay_tbls (dn q sel hl bs : Nat) (cs : List (String × List (BitVec 64))) (s : State) :
    (lay dn q sel hl bs cs s).TBLs = Abi.constRegions (fun n => s.syms n) cs :=
  constRegions_congr (lay_sy dn q sel hl bs s)

theorem lay_ok {cs : List (String × List (BitVec 64))} {I : Spec.Ecdsa.Rfc6979.Instance} {k : Nat}
    (sel hl bs : Nat) {s : State} (h : (rfcX86_64 cs I k 552).pre s) :
    (lay I.hashLen I.ecdsa.curve.len sel hl bs cs s).Ok := by
  obtain ⟨-, hsp, -, -, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, -, ht⟩ := h
  have e' : (lay I.hashLen I.ecdsa.curve.len sel hl bs cs s).RET = ⟨s.gpr .rsp, 8⟩ := by
    show (⟨_ + BitVec.ofNat 64 (240 + 8 * 38), 8⟩ : Region) = _; rw [lay_ret]
  have eA : (lay I.hashLen I.ecdsa.curve.len sel hl bs cs s).A = s.gpr .rsp - BitVec.ofNat 64 552 :=
    Offset.sub_sub_ofNat _ 544 8
  have eK : (lay I.hashLen I.ecdsa.curve.len sel hl bs cs s).STK = ⟨s.gpr .rsp - BitVec.ofNat 64 552, 552⟩ := by
    show (⟨_, 248 + 8 * 38⟩ : Region) = _; rw [eA]
  refine ⟨od, og, oc, dc, gc, eK ▸ ko, eK ▸ kd, eK ▸ kg, eK ▸ kc, e' ▸ ro, e' ▸ rd, e' ▸ rg, e' ▸ rc, no, nd, ng, nc,
    ?_, ?_⟩
  · show (lay I.hashLen I.ecdsa.curve.len sel hl bs cs s).A.toNat + (248 + 8 * 38) ≤ 2 ^ 64
    rw [eA, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
    have := (s.gpr .rsp).isLt
    omega
  · intro T hT
    rw [lay_tbls] at hT
    obtain ⟨hn, hd⟩ := ht T hT
    exact ⟨hn, hd _ (List.mem_cons_self ..), hd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      eK ▸ hd _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))⟩

theorem frame_base (sp : Addr) :
    sp - BitVec.ofNat 64 520 = sp - BitVec.ofNat 64 544 + BitVec.ofNat 64 24 := by
  rw [show 520 = 544 - 24 by omega, ← Offset.ofNat_sub_ofNat (by omega), Offset.sub_sub_eq]

/-- A word of the frame, after a store to another. -/
theorem rd_other {m : Mem} {B : Addr} {x y : Nat} (v : BitVec 64) (h : x + 8 ≤ y ∨ y + 8 ≤ x) (hx : x + 8 ≤ 1024)
    (hy : y + 8 ≤ 1024) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 64 = m.readW (B + BitVec.ofNat 64 x) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

/-- The state before the frame's push, from the call's `s`: `scratch` in
`rcx`, and the hash function's number, output length and block size in `rax`,
`r10` and `r11`. -/
structure Entered (s : State) (sel hl bs : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : s'.mem = s.mem
  syms : s'.syms = s.syms
  rsp : s'.gpr .rsp = s.gpr .rsp
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rdi : s'.gpr .rdi = s.gpr .rdi
  rsi : s'.gpr .rsi = s.gpr .rsi
  rdx : s'.gpr .rdx = s.gpr .rdx
  rcx : s'.gpr .rcx = s.gpr .r8
  rax : s'.gpr .rax = BitVec.ofNat 64 sel
  r10 : s'.gpr .r10 = BitVec.ofNat 64 hl
  r11 : s'.gpr .r11 = BitVec.ofNat 64 bs

end VG.Proof.Ecdsa.Rfc6979.X86_64
