module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Contract
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfT
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on AArch64: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`) and the `256 + e` bytes of stack below the stack pointer, from `B`
up (`Lay dn E`): the 16 bytes the calls use (HMAC's functions' frames), then
the frame of `224 + e` bytes, from `B + 16`: `K` and `V` (64 bytes each), `h`
(48 bytes, of which `q` are used), the number of candidates left, the
pointers to `scratch`, `digest`, `d` and `out`, the table's address, and `e`
more bytes (`HIGH`, 272 if several `V`s make a candidate: `h`, the digest for
`core` and the candidate; 64 if `hHigh`: `h`, for 64-byte scalars); then the
frame holding our return address (`B + 240 + e`). The table of the hash
function holds the addresses of its streaming functions `G`, which an
indirect call of `f`'s reaches (`TabOK`, `TabMem`).
`Ctx` is what holds between the frames' pushes and pops: the permissions,
`sp`, the callee-saved registers, the return address and the pointers in the
frames, and that memory changed only in `out`, `scratch` and the stack. Code
that writes only regions apart from the pointers and the return address
(`Safe`) keeps it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.RsaOaep.AArch64.Table (TabOK TabMem)

/-- The buffers and the lowest byte of the stack used (`sp - 256` on entry),
for a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) (E : Impl.Ecdsa.AArch64.Cfg) where
  out : Addr
  d : Addr
  dg : Addr
  scr : Addr
  /-- The table of the hash function. -/
  tab : Addr
  B : Addr
  q : Nat
  /-- The comb's tables (the static `E.tsym`), which `core` reads. -/
  T : Addr
  /-- The bytes at the frame's top. -/
  e : Nat
  ew : e = 0 ∨ e = 64 ∨ e = 272
  /-- The hash function's streaming functions, which the table holds, and
  the functions an indirect call of a table's functions may reach. -/
  G : Stream
  f : Fns
  /-- The addresses of `G`'s functions, public. -/
  fa : String → Addr

theorem Lay.he {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : L.e ≤ 272 := by
  rcases L.ew with h | h | h <;> omega_arith

namespace Lay

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E)

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The table of the hash function. -/
abbrev TAB : Region := ⟨L.tab, 40⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 256 + L.e⟩
/-- The frames: our words, and our return address. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 224 + L.e⟩
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 (240 + L.e), 16⟩
/-- The stack below the frame's pointers: the calls' and `K`, `V`, `h` and the count. -/
abbrev LOW : Region := ⟨L.B, 200⟩
/-- The frame above the pointers and the table's address. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 240, L.e⟩
/-- The comb's tables. -/
abbrev TBL : Region := ⟨L.T, 8 * E.combWords.length⟩
abbrev tables : List Region := tableRegions E L.T

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
  nB : L.B.toNat + (256 + L.e) ≤ 2 ^ 64
  tOut : L.TBL.Disjoint L.OUT
  tScr : L.TBL.Disjoint L.SCR
  tStk : L.TBL.Disjoint L.STK
  nT : L.T.toNat + 8 * E.combWords.length ≤ 2 ^ 64
  /-- The table does not wrap around, and is apart from what the code writes. -/
  nt : L.tab.toNat + 40 ≤ 2 ^ 64
  to : L.TAB.Disjoint L.OUT
  tc : L.TAB.Disjoint L.SCR
  tk : L.TAB.Disjoint L.STK

end Lay

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
theorem within_fr (B : Addr) {d n x : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 240 + x) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 16, 224 + x⟩ :=
  ⟨d - 16, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega_arith⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below the frame's pointers or above them. -/
def Safe {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) {d n : Nat} (h : d + n ≤ 200) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Offset.sub_base _ h)))

theorem safe_high {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) {d n : Nat} (h₁ : 240 ≤ d)
    (h₂ : d + n ≤ 240 + L.e) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ h₂)))

theorem Safe.of_sub {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {r r' : Region} (hs : Safe L r')
    (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

theorem safe_scr {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 256 + L.e) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 256 + L.e) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 256 + L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 256 + L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 256 + L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 256 + L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

/-- The 16 bytes the calls use, apart from `scratch`. -/
theorem low_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base _ h₂)

/-- The frame's pointers are apart from every safe region. -/
theorem ptrs_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 200, 40⟩ r := by
  have := h.nB
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega_arith)).sub_right hs
  · exact (h.stk_SCR (by omega_arith)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- Our return address is apart from every safe region. -/
theorem lr_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 (240 + L.e), 16⟩ r := by
  have := h.nB
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega_arith)).sub_right hs
  · exact (h.stk_SCR (by omega_arith)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- The buffers that are only read are apart from every safe region. -/
theorem d_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.D.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.od.symm.sub_right hs
  · exact h.dc.sub_right hs
  · exact (h.kd.symm.sub_right (Region.sub_prefix (by omega_arith))).sub_right hs
  · exact (h.kd.symm.sub_right (Offset.sub_base _ (by omega_arith))).sub_right hs

/-- The table is apart from every safe region. -/
theorem tab_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.TAB.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.to.sub_right hs
  · exact h.tc.sub_right hs
  · exact (h.tk.sub_right (Region.sub_prefix (by omega_arith))).sub_right hs
  · exact (h.tk.sub_right (Offset.sub_base _ (by have := L.he; omega_arith))).sub_right hs

theorem dg_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.DG.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.og.symm.sub_right hs
  · exact h.gc.sub_right hs
  · exact (h.kg.symm.sub_right (Region.sub_prefix (by omega_arith))).sub_right hs
  · exact (h.kg.symm.sub_right (Offset.sub_base _ (by omega_arith))).sub_right hs

end Lay.Ok

/-! ## Between the frames' pushes and pops -/

/-- The state between the frames' pushes and pops: `g` are the registers on
entry, `m₀` the memory. -/
structure Ctx {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.TAB] ++ L.tables
  wr : t.wr = [L.FR, L.LR, L.OUT, L.SCR]
  sp : t.sp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 200) 64 = L.scr
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 208) 64 = L.dg
  pD : t.mem.readW (L.B + BitVec.ofNat 64 216) 64 = L.d
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 224) 64 = L.out
  pTab : t.mem.readW (L.B + BitVec.ofNat 64 232) 64 = L.tab
  lr : t.mem.readW (L.B + BitVec.ofNat 64 (240 + L.e)) 64 = g .x30
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : tableAddr E t.syms = L.T
  held : ∀ i < E.combWords.length,
    m₀.readW (L.T + BitVec.ofNat 64 (8 * i)) 64 = E.combWords.getD i 0
  tabOk : TabOK L.G L.f t.syms
  tabMem : TabMem L.G t.syms L.tab m₀
  fsy : ∀ n ∈ [L.G.initN, L.G.updN, L.G.finN], t.syms n = L.fa n

theorem Safe.sub_frame {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega_arith) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base (p := L.B) (d := 240) (n := L.e) (by omega_arith) a (h a ha)⟩

namespace Ctx

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `sp` and the callee-saved registers
but `x30`, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hcs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms) : Ctx L g m₀ t' := by
  have := hL.nB
  have := L.he
  have keep : ∀ d, 200 ≤ d → d + 8 ≤ 240 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 200, 40⟩)
      (Offset.contains _ h₁ (by omega_arith) (by omega_arith)) (fun r hr => hL.ptrs_safe (hs r hr)) (by decide)
  have keepLr : t'.mem.readW (L.B + BitVec.ofNat 64 (240 + L.e)) 64 =
      t.mem.readW (L.B + BitVec.ofNat 64 (240 + L.e)) 64 :=
    hf.readW (r := ⟨L.B + BitVec.ofNat 64 (240 + L.e), 16⟩)
      (Offset.contains _ (Nat.le_refl _) (by omega_arith) (by omega_arith)) (fun r hr => hL.lr_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'),
    (keep 200 (by omega_arith) (by omega_arith)).trans hc.pScr, (keep 208 (by omega_arith) (by omega_arith)).trans hc.pDg,
    (keep 216 (by omega_arith) (by omega_arith)).trans hc.pD, (keep 224 (by omega_arith) (by omega_arith)).trans hc.pOut,
    (keep 232 (by omega_arith) (by omega_arith)).trans hc.pTab, keepLr.trans hc.lr,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame), by rw [hsy]; exact hc.sy, hc.held,
    by rw [hsy]; exact hc.tabOk, by rw [hsy]; exact hc.tabMem, by rw [hsy]; exact hc.fsy⟩

/-- Code that writes only registers but the callee-saved ones. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) (hsy : t'.syms = t.syms) :
    Ctx L g m₀ t' :=
  hc.keep hL hrd hwr hsp hg (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp) hsy

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

theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 240 + L.e) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by have := L.he; omega_arith)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 240 + L.e) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by have := L.he; omega_arith)⟩

theorem inScr (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inScrW (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inTab (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (h : o + 8 ≤ 40) :
    InRegions (t.rd ++ t.wr) (L.tab + BitVec.ofNat 64 o) 8 :=
  ⟨L.TAB, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by have := hL.nt; omega_arith)⟩

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

/-! ## The layout of a call, and the frames' entry -/

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q`, `e` bytes at the frame's top, and the table's functions `G` and `f`. -/
def lay (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (e : Nat) (he : e = 0 ∨ e = 64 ∨ e = 272) (G : Stream) (f : Fns)
    (s : State) : Lay dn E :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x4, s.gpr .x5, s.sp - BitVec.ofNat 64 (256 + e), q, tableAddr E s.syms,
    e, he, G, f, fun n => if n ∈ [G.initN, G.updN, G.finN] then s.syms n else 0⟩

/-- What the contract says of the table at `x5`: it holds `G`'s functions,
which an indirect call of `f`'s reaches. -/
def tabFacts (G : Stream) (f : Fns) (s : State) : Prop := TabOK G f s.syms ∧ TabMem G s.syms (s.gpr .x5) s.mem

variable {e : Nat} {he : e = 0 ∨ e = 64 ∨ e = 272} {G : Stream} {f : Fns}

theorem lay_ok {E : Impl.Ecdsa.AArch64.Cfg} {I : Spec.Ecdsa.Rfc6979.Instance} {ns : List String} {s : State}
    (h : (rfcAArch64 E I (256 + e) (tabFacts G f) ns).pre s) :
    (lay I.hashLen I.ecdsa.curve.len E e he G f s).Ok := by
  obtain ⟨-, -, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, ⟨-, nT, hdw⟩, nt, tout, tsc, tstk, -⟩ := h
  have nB : (lay I.hashLen I.ecdsa.curve.len E e he G f s).B.toNat + (256 + e) ≤ 2 ^ 64 := by
    simp only [lay]
    rw [Offset.toNat_sub_ofNat s.sp (256 + e)]
    omega_arith
  have hk : (lay I.hashLen I.ecdsa.curve.len E e he G f s).STK = below s.sp (256 + e) := rfl
  exact ⟨od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nB, hdw _ (List.mem_cons_self ..),
    hdw _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
    hdw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))), nT, nt, tout, tsc,
    hk ▸ tstk⟩

/-- The state in which the inner frame's body starts. -/
def entered (e : Nat) (s : State) : State := allocated (224 + e) (pushed .x30 s)

@[simp] theorem entered_rd (e : Nat) (s : State) : (entered e s).rd = s.rd := rfl
@[simp] theorem entered_gpr (e : Nat) (s : State) : (entered e s).gpr = s.gpr := rfl
@[simp] theorem entered_syms (e : Nat) (s : State) : (entered e s).syms = s.syms := rfl

theorem entered_sp (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (s : State) :
    (entered e s).sp = (lay dn q E e he G f s).B + BitVec.ofNat 64 16 := by
  show s.sp - 16 - BitVec.ofNat 64 (224 + e) = s.sp - BitVec.ofNat 64 (256 + e) + BitVec.ofNat 64 16
  rcases he with rfl | rfl | rfl <;> bv_omega

theorem lr_slot (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (s : State) :
    s.sp - 16 = (lay dn q E e he G f s).B + BitVec.ofNat 64 (240 + (lay dn q E e he G f s).e) := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 (256 + e) + BitVec.ofNat 64 (240 + e)
  rcases he with rfl | rfl | rfl <;> bv_omega

theorem entered_wr (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (s : State) :
    (entered e s).wr = (lay dn q E e he G f s).FR :: (lay dn q E e he G f s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 (224 + e), 224 + e⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 (224 + e) = (lay dn q E e he G f s).B + BitVec.ofNat 64 16 from
    entered_sp dn q E s, lr_slot dn q E]
  rfl

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem entered_mem (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (s : State) :
    (entered e s).mem =
      s.mem.writeW ((lay dn q E e he G f s).B + BitVec.ofNat 64 (240 + (lay dn q E e he G f s).e)) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot dn q E (he := he) (G := G) (f := f), write8]

/-- Five words stored in the frame's pointers. -/
theorem five_ok (B : Addr) (m : Mem) (a b c d t : BitVec 64) :
    let m' := ((((m.writeW (B + BitVec.ofNat 64 224) a).writeW (B + BitVec.ofNat 64 216) b).writeW
      (B + BitVec.ofNat 64 208) c).writeW (B + BitVec.ofNat 64 200) d).writeW (B + BitVec.ofNat 64 232) t
    Frame [⟨B + BitVec.ofNat 64 200, 40⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 224) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 216) 64 = b ∧ m'.readW (B + BitVec.ofNat 64 208) 64 = c ∧
      m'.readW (B + BitVec.ofNat 64 200) 64 = d ∧ m'.readW (B + BitVec.ofNat 64 232) 64 = t := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 256 → y + 8 ≤ 256 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega_arith) (by omega_arith)
  have ct : ∀ x, 200 ≤ x → x + 8 ≤ 240 →
      (⟨B + BitVec.ofNat 64 200, 40⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega_arith) (by omega_arith)
  refine ⟨(((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 224 (by omega_arith) (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (ct 216 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
    (ct 208 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _ (ct 200 (by omega_arith) (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (ct 232 (by omega_arith) (by omega_arith)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (sep 224 232 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 224 200 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 224 208 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 224 216 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 216 232 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 216 200 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 216 208 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 208 232 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 208 200 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 200 232 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]

/-- The arguments saved in the frame: `Ctx` holds. -/
theorem entry_ok {E : Impl.Ecdsa.AArch64.Cfg} {I : Spec.Ecdsa.Rfc6979.Instance} {ns : List String} {s : State}
    (h : (rfcAArch64 E I (256 + e) (tabFacts G f) ns).pre s) :
    WP isa (.block Impl.Ecdsa.Rfc6979.AArch64.Cfg.saveArgs) (entered e s)
      (Ctx (lay I.hashLen I.ecdsa.curve.len E e he G f s) s.gpr s.mem) := by
  have hL := lay_ok (he := he) h
  have hnB := hL.nB
  have hw : ∀ d, 16 ≤ d → d + 8 ≤ 240 →
      InRegions (entered e s).wr ((lay I.hashLen I.ecdsa.curve.len E e he G f s).B + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => ⟨(lay I.hashLen I.ecdsa.curve.len E e he G f s).FR,
      by rw [entered_wr I.hashLen I.ecdsa.curve.len E (he := he) (G := G) (f := f)]; simp, Offset.contains _ h₁ (by omega_arith) (by omega_arith)⟩
  have w200 := hw 200 (by omega_arith) (by omega_arith)
  have w208 := hw 208 (by omega_arith) (by omega_arith)
  have w216 := hw 216 (by omega_arith) (by omega_arith)
  have w224 := hw 224 (by omega_arith) (by omega_arith)
  have w232 := hw 232 (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [Impl.Ecdsa.Rfc6979.AArch64.Cfg.saveArgs, Impl.Ecdsa.Rfc6979.AArch64.fOut,
    Impl.Ecdsa.Rfc6979.AArch64.fD, Impl.Ecdsa.Rfc6979.AArch64.fDigest, Impl.Ecdsa.Rfc6979.AArch64.fScratch,
    Impl.Ecdsa.Rfc6979.AArch64.fTab,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, State.read,
    Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, Option.bind_some, reduceCtorEq, ite_false, ite_true,
    entered_sp I.hashLen I.ecdsa.curve.len E (he := he) (G := G) (f := f),
    Offset.add_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, w200, w208, w216, w224,
    w232, write8, Option.some.injEq, exists_eq_left', BitVec.add_zero, entered_gpr]
  obtain ⟨fr, k224, k216, k208, k200, k232⟩ := five_ok (lay I.hashLen I.ecdsa.curve.len E e he G f s).B
    (entered e s).mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5)
  rw [entered_mem I.hashLen I.ecdsa.curve.len E (he := he) (G := G) (f := f)] at fr k224 k216 k208 k200 k232
  rw [entered_mem I.hashLen I.ecdsa.curve.len E (he := he) (G := G) (f := f)]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT, _, _, _, _, htf⟩ := h
  have hle := (lay I.hashLen I.ecdsa.curve.len E e he G f s).he
  refine ⟨?_, ?_, rfl, ?_, k200, k208, k216, k224, k232, ?_, ?_, rfl, hT.1, htf.1, htf.2, ?_⟩
  · simp only [entered_rd]; rw [h.1]; rfl
  · rw [entered_wr I.hashLen I.ecdsa.curve.len E (he := he) (G := G) (f := f), h.2.1]; rfl
  · intro r hr hr'
    rw [RegUpd.gpr_write_of_ne _ _ _ (by intro e; subst e; simp [preserved] at hr), entered_gpr]
  · rw [fr.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · refine Frame.trans (Frame.writeW (Frame.refl _ _) (r := (lay I.hashLen I.ecdsa.curve.len E e he G f s).STK) (by simp) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))) (Frame.sub fr fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(lay I.hashLen I.ecdsa.curve.len E e he G f s).STK, by simp, Offset.sub_base _ (by omega_arith)⟩
  · intro n hn
    exact (ite_eq_left_of_eq_true _ _ (eq_true (show n ∈ [G.initN, G.updN, G.finN] from hn))).symm

end VG.Proof.Ecdsa.Rfc6979.AArch64
