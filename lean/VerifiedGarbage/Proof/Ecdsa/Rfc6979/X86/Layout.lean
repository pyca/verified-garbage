module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Contract
public import VerifiedGarbage.Proof.HmacTable.X86
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on x86 (32-bit): where everything is

The function's arguments (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`digest_len`, `scratch`, the table `hmac` of 24 bytes, and `esp` on entry
`E`) and the 588 bytes of stack below the return address, from
`B = E - 588` up (`Lay dn`): the 76 bytes the calls use (a frame of at most
six arguments, the return address, and the 48 bytes HMAC's functions use
below it), then the frame of 512 bytes, from `B + 76` (`esp` in the body,
`F`): `K` and `V` (64 bytes each), our caller's `ebx`, `esi`, `edi` and
`ebp`, `D` and `B`, and above them (`HIGH`) the length of `T`, the number of
candidates left, `h`, `X`, `core`'s digest and `T`. Above it, the return
address and our arguments. `Ctx` is what holds between the frame's entry
(`entry`, `tabDB`) and its release: the permissions, `esp`, the saved
registers, `D` and `B`, our arguments, immutable table contents and public
symbol addresses, what the table holds and which functions an indirect call
of it reaches, and that memory changed only in `out`, `scratch` and the
stack. Code that writes only regions apart from the saved registers, `D`
and `B` (`Safe`) keeps it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp
open VG.Impl.Ecdsa.Rfc6979.X86 (Fns)
open VG.Proof.HmacTable.X86 (TabOK TabMem)

/-- The arguments (`out`, `d`, `digest`, `digest_len`, `scratch`, `hmac`)
and `esp` on entry, for a digest of `dn` bytes and scalars of `q`, the
tables of constants `core` reads and their statics' addresses, the hash
function's functions whose table `hmac` is, the functions an indirect call
of a table's functions may reach, and the addresses of the table's
functions. -/
structure Lay (dn : Nat) where
  a0 : BitVec 32
  a1 : BitVec 32
  a2 : BitVec 32
  a3 : BitVec 32
  sc : BitVec 32
  tb : BitVec 32
  E : BitVec 32
  q : Nat
  cs : List (String × List (BitVec 64))
  sy : String → BitVec 32
  H : Impl.Pbkdf2.Whole.X86.Fns
  f : Fns
  fa : String → BitVec 32

namespace Lay

variable {dn : Nat} (L : Lay dn)

/-- Argument `i` of the layout. -/
def a : Nat → BitVec 32
  | 0 => L.a0
  | 1 => L.a1
  | 2 => L.a2
  | 3 => L.a3
  | 4 => L.sc
  | _ => L.tb

abbrev out : Addr := L.a0.setWidth 64
abbrev d : Addr := L.a1.setWidth 64
abbrev dg : Addr := L.a2.setWidth 64
abbrev scr : Addr := L.sc.setWidth 64
abbrev tab : Addr := L.tb.setWidth 64
/-- `esp` in the frame's body. -/
abbrev F : BitVec 32 := L.E - BitVec.ofNat 32 512
/-- The lowest byte of the stack used. -/
abbrev B : Addr := (L.E - BitVec.ofNat 32 588).setWidth 64

abbrev TBLs : List Region := Abi.constRegions (fun n => (L.sy n).setWidth 64) L.cs

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The table of HMAC. -/
abbrev TAB : Region := ⟨L.tab, 24⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 588⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 76, 512⟩
/-- The return address, and our arguments. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 588, 4⟩
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 592, 24⟩
/-- The stack below the saved registers: the calls', and `K` and `V`. -/
abbrev LOW : Region := ⟨L.B, 204⟩
/-- The frame above `D` and `B`. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 228, 360⟩

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
  nc : L.sc.toNat + 8192 ≤ 2 ^ 32
  e588 : 588 ≤ L.E.toNat
  e28 : L.E.toNat + 28 ≤ 2 ^ 32
  tbl : ∀ T ∈ L.TBLs, T.base.toNat + T.len ≤ 2 ^ 32 ∧
    T.Disjoint L.OUT ∧ T.Disjoint L.SCR ∧ T.Disjoint L.STK
  /-- The table does not wrap around, and is apart from what the code writes. -/
  nt : L.tb.toNat + 24 ≤ 2 ^ 32
  to : L.TAB.Disjoint L.OUT
  tc : L.TAB.Disjoint L.SCR
  tk : L.TAB.Disjoint L.STK
  ta : L.TAB.Disjoint L.ARGS

end Lay

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem B_eq (h : L.Ok) : L.B = L.E.setWidth 64 - BitVec.ofNat 64 588 := Taint.sub_setWidth h.e588

theorem BN (h : L.Ok) : L.B.toNat = L.E.toNat - 588 := by
  have := h.e588
  simp only [Lay.B, BitVec.toNat_setWidth]
  rw [sub_toNat (by omega_arith)]; have := L.E.isLt; omega_arith

theorem nB (h : L.Ok) : L.B.toNat + 616 ≤ 2 ^ 64 := by
  have := h.e588; have := h.e28; rw [h.BN]; omega_arith

/-- `[F + o]`, for `o` in the frame or the arguments above it. -/
theorem addrF (h : L.Ok) {o : Nat} (ho : o < 540) : addr L.F o = L.B + BitVec.ofNat 64 (76 + o) := by
  have := h.e588; have := h.e28
  have hF : L.F.toNat = L.E.toNat - 512 := sub_toNat (by omega_arith)
  rw [addr_eq (by rw [hF]; omega_arith), Lay.F, Taint.sub_setWidth (by omega_arith), h.B_eq,
    Offset.sub_ofNat_eq _ (show 512 ≤ 588 by omega_arith), show 588 - 512 = 76 by omega_arith, Offset.add_add]

theorem F64 (h : L.Ok) : L.F.setWidth 64 = L.B + BitVec.ofNat 64 76 := by
  have e := h.addrF (o := 0) (by omega_arith)
  rwa [addr, BitVec.add_zero] at e

/-- The frame's 76 bytes below `F`, which the calls use. -/
theorem below_F (_h : L.Ok) : below L.F 76 = ⟨L.B, 76⟩ := by
  show (⟨(L.F - BitVec.ofNat 32 76).setWidth 64, 76⟩ : Region) = _
  rw [Lay.F, show L.E - BitVec.ofNat 32 512 - BitVec.ofNat 32 76 = L.E - BitVec.ofNat 32 588 by
    rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]]

theorem FN (h : L.Ok) : L.F.toNat = L.E.toNat - 512 := sub_toNat (by have := h.e588; omega_arith)

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 588) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 588) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 588) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 588) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame. -/
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 588) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 76, 512⟩ :=
  ⟨d - 76, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega_arith⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below the saved registers or above `B`. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 204) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Offset.sub_base _ h)))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

theorem safe_high {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 228 ≤ d) (h₂ : d + n ≤ 588) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ (by omega_arith))))

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

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

/-- The saved registers, `D` and `B` are apart from every safe region. -/
theorem saved_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 204, 24⟩ r := by
  have nB := h.nB
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega_arith)).sub_right hs
  · exact (h.stk_SCR (by omega_arith)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- The return address and our arguments are apart from every safe region. -/
theorem top_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 588, 28⟩ r := by
  have nB := h.nB
  have j : ∀ {r : Region}, L.RET.Disjoint r → L.ARGS.Disjoint r →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 588, 28⟩ r := fun h₂ h₃ =>
    disjoint_join (a := 4) (b := 24) h₂ (by rw [Offset.add_add]; exact h₃)
  rcases hs with hs | hs | hs | hs
  · exact (j h.ro h.ao).sub_right hs
  · exact (j h.rc h.ac).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

end Lay.Ok

/-! ## Between the frame's entry and release -/

/-- The state between the frame's entry and release: `g` are the registers
on entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.TAB] ++ L.TBLs
  wr : t.wr = [L.FR, L.OUT, L.SCR, L.ARGS]
  esp : t.gpr .esp = L.F
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.X86.saved, t.mem.readW (L.B + BitVec.ofNat 64 (76 + p.2)) 32 = g p.1
  pArg : ∀ i < 6, t.mem.readW (L.B + BitVec.ofNat 64 (592 + 4 * i)) 32 = L.a i
  /-- `D` and `B`, above the saved registers. -/
  pDl : t.mem.readW (L.B + BitVec.ofNat 64 220) 32 = BitVec.ofNat 32 L.H.H.D
  pBl : t.mem.readW (L.B + BitVec.ofNat 64 224) 32 = BitVec.ofNat 32 L.H.H.B
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : ∀ c ∈ L.cs, t.syms c.1 = L.sy c.1
  held : Abi.constsHeld m₀ (fun n => (L.sy n).setWidth 64) L.cs
  tabOk : TabOK L.H L.f t.syms
  tabMem : TabMem L.H t.syms L.tb m₀
  fsy : ∀ n ∈ [L.H.hiN, L.H.H.updN, L.H.hfN], t.syms n = L.fa n

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega_arith) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base (p := L.B) (d := 228) (n := 360) (by omega_arith) a (h a ha)⟩

theorem saved_off : ∀ p ∈ Impl.Ecdsa.Rfc6979.X86.saved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 144 := by decide

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions and `esp`, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms) : Ctx L g m₀ t' := by
  have nB := hL.nB
  have keep : ∀ d, 204 ≤ d → d + 4 ≤ 228 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 32 = t.mem.readW (L.B + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 204, 24⟩)
      (Offset.contains _ h₁ (by omega_arith) (by omega_arith)) (fun r hr => hL.saved_safe (hs r hr)) (by decide)
  have keepA : ∀ d, 592 ≤ d → d + 4 ≤ 616 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 32 = t.mem.readW (L.B + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 588, 28⟩)
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)) (fun r hr => hL.top_safe (hs r hr))
      (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, fun p hp => by
    have := saved_off p hp
    rw [keep _ (by omega_arith) (by omega_arith)]
    exact hc.saved p hp, fun i hi => (keepA _ (by omega_arith) (by omega_arith)).trans (hc.pArg i hi),
    (keep 220 (by omega_arith) (by omega_arith)).trans hc.pDl, (keep 224 (by omega_arith) (by omega_arith)).trans hc.pBl,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame),
    fun c hc' => by rw [hsy]; exact hc.sy c hc', hc.held, by rw [hsy]; exact hc.tabOk,
    by rw [hsy]; exact hc.tabMem, by rw [hsy]; exact hc.fsy⟩

/-- Code that writes only registers but `esp`. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsy : t'.syms = t.syms) : Ctx L g m₀ t' :=
  hc.keep hL hrd hwr hsp (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp) hsy

/-- A byte of `d`, as on entry. -/
theorem d_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.q) :
    t.mem (L.d + BitVec.ofNat 64 i) = m₀ (L.d + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.D) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.od.symm
    · exact hL.dc
    · exact hL.kd.symm) (by show L.q ≤ 2 ^ 64; have := hL.nd; omega_arith) hi

/-- A byte of `digest`, as on entry. -/
theorem dg_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < dn) :
    t.mem (L.dg + BitVec.ofNat 64 i) = m₀ (L.dg + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.DG) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.og.symm
    · exact hL.gc
    · exact hL.kg.symm) (by show dn ≤ 2 ^ 64; have := hL.ng; omega_arith) hi

/-- The table's words, as on entry. -/
theorem tabWord (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 4 ≤ 24) :
    t.mem.readW (addr L.tb o) 32 = m₀.readW (addr L.tb o) 32 := by
  rw [addr_eq (by have := hL.nt; omega_arith)]
  exact hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega_arith)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.to
    · exact hL.tc
    · exact hL.tk) (by decide)

theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₁ : 76 ≤ d) (h₂ : d + 4 ≤ 588) (hL : L.Ok) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 4 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by have := hL.nB; omega_arith)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 588) (hL : L.Ok) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by have := hL.nB; omega_arith)⟩

theorem inArgs (hc : Ctx L g m₀ t) {i : Nat} (hi : i < 6) (hL : L.Ok) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (592 + 4 * i)) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ (by omega_arith) (by omega_arith) (by have := hL.nB; omega_arith)⟩

theorem inScr (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inScrW (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inTab (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (h : o + 4 ≤ 24) :
    InRegions (t.rd ++ t.wr) (addr L.tb o) 4 :=
  ⟨L.TAB, by rw [hc.rd, hc.wr]; simp, by
    rw [addr_eq (by have := hL.nt; omega_arith)]
    exact Offset.contains_base _ h (by have := hL.nt; omega_arith)⟩

theorem inD (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inDg (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.dg + BitVec.ofNat 64 o) n :=
  ⟨L.DG, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

/-- Regions within the buffers and the frame are permitted. -/
theorem covers (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hR ⊢; rcases hR with h | h | h | h | h <;> simp [h], hw⟩

theorem coversW (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.wr]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢; rcases hR with h | h | h <;> simp [h], hw⟩

end Ctx

/-! ## The frame's entry -/

/-- What the contract says of the table, on entry: it holds `H`'s HMAC
functions, which an indirect call of `f`'s reaches, then its digest length
and HMAC's block size. -/
def tabFacts (H : Impl.Pbkdf2.Whole.X86.Fns) (f : Fns) (s : State) : Prop :=
  TabOK H f s.syms ∧ TabMem H s.syms (arg s 5) s.mem ∧
    s.mem.readW (addr (arg s 5) 16) 32 = BitVec.ofNat 32 H.H.D ∧
    s.mem.readW (addr (arg s 5) 20) 32 = BitVec.ofNat 32 H.H.B

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q`, the tables `cs` (the statics' addresses, public, of those tables only),
and the hash function `H`'s HMAC through the table, whose functions an
indirect call reaches among `f`'s. -/
def lay (dn q : Nat) (cs : List (String × List (BitVec 64))) (H : Impl.Pbkdf2.Whole.X86.Fns) (f : Fns)
    (s : State) : Lay dn :=
  ⟨arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, s.gpr .esp, q, cs,
    fun n => if n ∈ cs.map Prod.fst then s.syms n else 0, H, f,
    fun n => if n ∈ [H.hiN, H.H.updN, H.hfN] then s.syms n else 0⟩

section
variable {dn q : Nat} {cs : List (String × List (BitVec 64))} {H : Impl.Pbkdf2.Whole.X86.Fns} {f : Fns}

theorem lay_sy (s : State) {c : String × List (BitVec 64)} (hc : c ∈ cs) :
    (lay dn q cs H f s).sy c.1 = s.syms c.1 :=
  ite_eq_left (List.mem_map.mpr ⟨c, hc, rfl⟩)

theorem lay_tbls (s : State) :
    (lay dn q cs H f s).TBLs = Abi.constRegions (fun n => (s.syms n).setWidth 64) cs := by
  apply List.map_congr_left
  intro c hc
  show (⟨((lay dn q cs H f s).sy c.1).setWidth 64, _⟩ : Region) = _
  rw [lay_sy s (show c ∈ cs from hc)]

theorem lay_a (s : State) : ∀ i < 6, (lay dn q cs H f s).a i = arg s i
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

/-- The address of our argument `i`. -/
theorem lay_argAddr {s : State} (e588 : 588 ≤ (s.gpr .esp).toNat) (e28 : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    {i : Nat} (hi : i < 6) : argAddr s i = (lay dn q cs H f s).B + BitVec.ofNat 64 (592 + 4 * i) := by
  have hB : (lay dn q cs H f s).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588 := Taint.sub_setWidth e588
  rw [hB]
  show addr (s.gpr .esp) (4 + 4 * i) = _
  rw [addr_eq (by omega_arith), show 592 + 4 * i = 588 + (4 + 4 * i) by omega_arith,
    ← Offset.add_add ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588) 588 (4 + 4 * i), BitVec.sub_add_cancel]

/-- Our arguments' slots. -/
theorem lay_ARGS {s : State} (e588 : 588 ≤ (s.gpr .esp).toNat) (e28 : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) :
    (lay dn q cs H f s).ARGS = ⟨argAddr s 0, 24⟩ := by
  rw [lay_argAddr e588 e28 (by omega_arith)]

end

theorem lay_ok {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance}
    {H : Impl.Pbkdf2.Whole.X86.Fns} {f : Fns} {ns : List String} {s : State}
    (h : (rfcX86 cs I 588 (tabFacts H f) ns).pre s) : (lay I.hashLen I.ecdsa.curve.len cs H f s).Ok := by
  obtain ⟨e588, e28, -, -, od, og, oc, dc, gc, ao, ac, ro, rc, ko, kd, kg, kc, no, nd, ng, nc, ht, nt, tout, tsc,
    targ, -, tstk, -⟩ := h
  have hB : (lay I.hashLen I.ecdsa.curve.len cs H f s).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588 :=
    Taint.sub_setWidth e588
  have eR : (lay I.hashLen I.ecdsa.curve.len cs H f s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
    show (⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 588, 4⟩ : Region) = _
    rw [hB, BitVec.sub_add_cancel]
  have eA := lay_ARGS (dn := I.hashLen) (q := I.ecdsa.curve.len) (cs := cs) (H := H) (f := f) e588 e28
  have eK : (lay I.hashLen I.ecdsa.curve.len cs H f s).STK =
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩ := by
    show (⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B, 588⟩ : Region) = _
    rw [hB]
  refine ⟨od, og, oc, dc, gc, eA ▸ ao, eA ▸ ac, eR ▸ ro, eR ▸ rc, eK ▸ ko, eK ▸ kd, eK ▸ kg, eK ▸ kc,
    no, nd, ng, nc, e588, e28, ?_, nt, tout, tsc, eK ▸ tstk, eA ▸ targ⟩
  intro T hT
  rw [lay_tbls] at hT
  have hh := ht.2 T hT
  exact ⟨hh.1, hh.2 _ (by simp [Lay.OUT, Lay.out, lay]), hh.2 _ (by simp [Lay.SCR, Lay.scr, lay]),
    by rw [eK]; exact hh.2 _ (by simp)⟩

/-- The state after the frame's allocation. -/
abbrev entered (s : State) : State := allocState 512 s

theorem entered_esp (dn q : Nat) (cs : List (String × List (BitVec 64))) (H : Impl.Pbkdf2.Whole.X86.Fns)
    (f : Fns) (s : State) : (entered s).gpr .esp = (lay dn q cs H f s).F := by
  simp only [entered, allocState_esp]; rfl

theorem entered_wr {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance}
    {H : Impl.Pbkdf2.Whole.X86.Fns} {f : Fns} {ns : List String} {s : State}
    (h : (rfcX86 cs I 588 (tabFacts H f) ns).pre s) :
    (entered s).wr = (lay I.hashLen I.ecdsa.curve.len cs H f s).FR :: s.wr := by
  simp only [entered, allocState_wr]
  congr 1
  show (⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).F.setWidth 64, 512⟩ : Region) = _
  rw [(lay_ok h).F64]

/-- The release of the frame. -/
def released (s₂ : State) : State :=
  { s₂.setReg .esp (s₂.gpr .esp + BitVec.ofNat 32 512) with wr := s₂.wr.tail }

/-- The frame: its body, which never writes `esp`, runs from `entered s`,
and the frame's release leads to `released s₂`. -/
theorem WP.alloc {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : 512 ≤ (s.gpr .esp).toNat) (hsp : NoSp body)
    (hb : WP isa body (entered s) fun s₂ => Q (released s₂)) :
    WP isa (.frame (.alloc 512) body (.free 512)) s Q := by
  obtain ⟨t, s₂, he', hq⟩ := hb
  obtain ⟨-, hw⟩ := Exec.rdwr he'
  have hp := Exec.gpr hsp he'
  have hpush : isa.push (.alloc 512) s = some (entered s) := by
    simp only [isa, push]
    exact ite_eq_left ⟨by omega_arith, by omega_arith, by decide, hn⟩
  have hpop : isa.pop (.free 512) (entered s) s₂ = some (released s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by omega_arith, by omega_arith, by decide, hp, hw, rfl⟩
  exact ⟨_, _, Exec.frame hpush he' hpop, hq⟩

end VG.Proof.Ecdsa.Rfc6979.X86
