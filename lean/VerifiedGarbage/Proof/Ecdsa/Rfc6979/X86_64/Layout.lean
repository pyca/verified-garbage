module

public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.Mgf1.X86_64.Table
public import VerifiedGarbage.Proof.HmacTable.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on x86-64: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`) and the `240 + 8 e` bytes of stack below its return address, from
`B` up (`Lay dn`): the 24 bytes the calls use (a call's return address, and
the 16 bytes HMAC's functions use below theirs), then the frame of `27 + e`
words, from `B + 24`: `K` and `V` (64 bytes each), `h` (48 bytes, of which
`q` are used), the number of candidates left, the pointers to `scratch`,
`digest`, `d` and `out`, and `e` more words (`HIGH`, 18 if two `V`s make a
candidate: the digest for `core` and the candidate). `Ctx` is what holds
between the frame's push and pop: the permissions, `rsp`, the callee-saved
registers, the pointers in the frame, that memory changed only in `out`,
`scratch` and the stack, and where the tables of constants `core` reads are
(`TBLs`, the comb's). Code that writes only regions apart from the
pointers (`Safe`) keeps it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.HmacTable.X86_64 (TabOK TabMem)

/-- The buffers and the lowest byte of the stack used (`rsp - (240 + 8 e)` on
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
  /-- The words above the frame's pointers. -/
  e : Nat
  he : e = 48
  /-- The tables of constants `core` reads, and their statics' addresses. -/
  cs : List (String × List (BitVec 64))
  sy : String → Addr
  /-- The hash function's code, whose HMAC functions the table holds, and
  the functions an indirect call of a table's functions may reach. -/
  H : Hash
  f : Fns
  /-- The addresses of `H`'s HMAC functions, public. -/
  fa : String → Addr

namespace Lay

variable {dn : Nat} (L : Lay dn)

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The table of HMAC. -/
abbrev TAB : Region := ⟨L.tab, 48⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 248 + 8 * L.e⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 24, 224 + 8 * L.e⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 (248 + 8 * L.e), 8⟩
/-- The frame's slot of the table's address, its top word. -/
abbrev TS : Region := ⟨L.B + BitVec.ofNat 64 (240 + 8 * L.e), 8⟩
/-- The stack below the frame's pointers: the calls' and `K`, `V`, `h` and the count. -/
abbrev LOW : Region := ⟨L.B, 208⟩
/-- The frame above its pointers and the slots of `D` and `B`. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 256, 8 * L.e - 16⟩
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
  /-- The table does not wrap around, and is apart from what the code writes. -/
  nt : L.tab.toNat + 48 ≤ 2 ^ 64
  to : L.TAB.Disjoint L.OUT
  tc : L.TAB.Disjoint L.SCR
  tk : L.TAB.Disjoint L.STK
  /-- The stack used does not wrap around. -/
  nb : L.B.toNat + (248 + 8 * L.e) ≤ 2 ^ 64
  /-- The tables do not wrap around, and are apart from what the code writes. -/
  tbl : ∀ T ∈ L.TBLs, T.base.toNat + T.len ≤ 2 ^ 64 ∧ T.Disjoint L.OUT ∧ T.Disjoint L.SCR ∧ T.Disjoint L.STK

end Lay

theorem constRegions_congr {f f' : String → Addr} {cs : List (String × List (BitVec 64))}
    (h : ∀ c ∈ cs, f c.1 = f' c.1) : Abi.constRegions f cs = Abi.constRegions f' cs :=
  List.map_congr_left fun c hc => by rw [h c hc]

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame. -/
theorem within_fr (B : Addr) {d n x : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 248 + x) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 24, 224 + x⟩ :=
  ⟨d - 24, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega_arith⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below or above the frame's pointers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 208) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Offset.sub_base _ h)))

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

theorem safe_high {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 256 ≤ d) (h₂ : d + n ≤ 240 + 8 * L.e) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ (by have := L.he; omega_arith))))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_d (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.d, L.q⟩ := h.stk_D h₁

/-- The frame's pointers are apart from every safe region. -/
theorem ptrs_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 208, 32⟩ r := by
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega_arith)).sub_right hs
  · exact (h.stk_SCR (by omega_arith)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · have := L.he
    exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- The frame's slots of `D` and `B` are apart from every safe region. -/
theorem db_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 240, 16⟩ r := by
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by have := L.he; omega_arith)).sub_right hs
  · exact (h.stk_SCR (by have := L.he; omega_arith)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · have := L.he
    exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- The frame's slot of the table's address is apart from every safe region. -/
theorem ts_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.TS.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact (h.ko.sub_left (Offset.sub_base _ (by omega_arith))).sub_right hs
  · exact (h.kc.sub_left (Offset.sub_base _ (by omega_arith))).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by have := L.he; omega_arith)).sub_right hs
  · have := L.he
    exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

end Lay.Ok

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` are the registers on
entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.TAB] ++ L.TBLs
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 24
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 208) 64 = L.scr
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 216) 64 = L.dg
  pD : t.mem.readW (L.B + BitVec.ofNat 64 224) 64 = L.d
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 232) 64 = L.out
  pTab : t.mem.readW (L.B + BitVec.ofNat 64 (240 + 8 * L.e)) 64 = L.tab
  /-- `D` and `B`, above the pointers. -/
  pDl : t.mem.readW (L.B + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 L.H.D
  pBl : t.mem.readW (L.B + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 L.H.P.B
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : ∀ c ∈ L.cs, t.syms c.1 = L.sy c.1
  held : Abi.constsHeld m₀ L.sy L.cs
  tabOk : TabOK L.H L.f t.syms
  tabMem : TabMem L.H t.syms L.tab m₀
  fsy : ∀ n ∈ [L.H.hmacInitN, L.H.updN, L.H.hmacFinN], t.syms n = L.fa n

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega_arith) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base (p := L.B) (d := 256) (n := 8 * L.e - 16)
      (by have := L.he; omega_arith) a (h a ha)⟩

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
      (Offset.contains _ h₁ (by omega_arith) (by omega_arith)) (fun r hr => hL.ptrs_safe (hs r hr)) (by decide)
  have keepDB : ∀ d, 240 ≤ d → d + 8 ≤ 256 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 240, 16⟩)
      (Offset.contains _ h₁ (by omega_arith) (by have := hL.nb; have := L.he; omega_arith))
      (fun r hr => hL.db_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.rsp, fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'),
    (keep 208 (by omega_arith) (by omega_arith)).trans hc.pScr, (keep 216 (by omega_arith) (by omega_arith)).trans hc.pDg,
    (keep 224 (by omega_arith) (by omega_arith)).trans hc.pD, (keep 232 (by omega_arith) (by omega_arith)).trans hc.pOut,
    (hf.readW (r := L.TS) (Offset.contains _ (Nat.le_refl _) (by have := L.he; omega_arith) (by have := hL.nb; have := L.he; omega_arith))
      (fun r hr => hL.ts_safe (hs r hr)) (by decide)).trans hc.pTab,
    (keepDB 240 (by omega_arith) (by omega_arith)).trans hc.pDl, (keepDB 248 (by omega_arith) (by omega_arith)).trans hc.pBl,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame), by rw [hsy]; exact hc.sy, hc.held,
    by rw [hsy]; exact hc.tabOk, by rw [hsy]; exact hc.tabMem, by rw [hsy]; exact hc.fsy⟩

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

theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₁ : 24 ≤ d) (h₂ : d + 8 ≤ 248 + 8 * L.e) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  have := L.he
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by omega_arith)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 248 + 8 * L.e) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  have := L.he
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by omega_arith)⟩

theorem inScr (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inScrW (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inTab (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (h : o + 8 ≤ 48) :
    InRegions (t.rd ++ t.wr) (L.tab + BitVec.ofNat 64 o) 8 :=
  ⟨L.TAB, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by have := hL.nt; omega_arith)⟩

theorem inD (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inDg (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.dg + BitVec.ofNat 64 o) n :=
  ⟨L.DG, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

/-- Regions within the buffers and the frame are permitted. -/
theorem mem_regions {R : Region} (h : R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR]) :
    R ∈ [L.D, L.DG, L.TAB] ++ L.TBLs ++ [L.FR, L.OUT, L.SCR] := by
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

/-! ## The frame's push -/

/-- The registers the frame's push stores, with `e` words above the pointers:
the table's address, copies of `rax`, then `B` (`r11`) and `D` (`r10`) just
above the pointers. -/
abbrev pushRs (e : Nat) : List Reg :=
  .r9 :: ((List.replicate (e - 2) .rax ++ ([.r11, .r10] : List Reg)) ++ ([.rdi, .rsi, .rdx, .rcx] : List Reg) ++
    List.replicate 23 .rax)

theorem pushRs_length {e : Nat} (he : 2 ≤ e) : (pushRs e).length = 28 + e := by
  simp only [pushRs, List.length_cons, List.length_append, List.length_replicate, List.length_nil]; omega_arith

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q`, `e` words above the pointers, the tables `cs` (the statics' addresses,
public, of those tables only), and the hash function `H`'s HMAC through the
table, whose functions an indirect call reaches among `f`'s. -/
def lay (dn q e : Nat) (he : e = 48) (cs : List (String × List (BitVec 64))) (H : Hash) (f : Fns)
    (s : State) : Lay dn :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r9, s.gpr .rsp - BitVec.ofNat 64 (248 + 8 * e), q, e,
    he, cs, fun n => if n ∈ cs.map Prod.fst then s.syms n else 0, H, f,
    fun n => if n ∈ [H.hmacInitN, H.updN, H.hmacFinN] then s.syms n else 0⟩

/-- What the contract says of the table at `r9`, after the entry: it holds
`H`'s HMAC functions, which an indirect call of `f`'s reaches, and `r10` and
`r11` hold its digest length and HMAC's block size. -/
def tabFacts (H : Hash) (f : Fns) (s : State) : Prop :=
  TabOK H f s.syms ∧ TabMem H s.syms (s.gpr .r9) s.mem ∧ s.gpr .r10 = BitVec.ofNat 64 H.D ∧
    s.gpr .r11 = BitVec.ofNat 64 H.P.B

theorem lay_ret (dn q e : Nat) (he : e = 48) (cs : List (String × List (BitVec 64))) (H : Hash) (f : Fns)
    (s : State) :
    (lay dn q e he cs H f s).B + BitVec.ofNat 64 (248 + 8 * e) = s.gpr .rsp :=
  BitVec.sub_add_cancel _ _

theorem lay_sy (dn q e : Nat) (he : e = 48) {cs : List (String × List (BitVec 64))} {H : Hash} {f : Fns}
    (s : State) :
    ∀ c ∈ cs, (lay dn q e he cs H f s).sy c.1 = s.syms c.1 := fun c hc => by
  simp only [lay, List.mem_map_of_mem (f := Prod.fst) hc, ite_true]

theorem lay_tbls (dn q e : Nat) (he : e = 48) (cs : List (String × List (BitVec 64))) {H : Hash} {f : Fns}
    (s : State) :
    (lay dn q e he cs H f s).TBLs = Abi.constRegions (fun n => s.syms n) cs :=
  constRegions_congr (lay_sy dn q e he (H := H) (f := f) s)

theorem lay_ok {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance} {e : Nat}
    (he : e = 48) {H : Hash} {f : Fns} {ns : List String} {s : State}
    (h : (rfcX86_64 cs I (248 + 8 * e) (tabFacts H f) ns).pre s) :
    (lay I.hashLen I.ecdsa.curve.len e he cs H f s).Ok := by
  obtain ⟨hsp, -, -, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, ht, nt, tout, tsc, -,
    tstk, -⟩ := h
  have e' : (lay I.hashLen I.ecdsa.curve.len e he cs H f s).RET = ⟨s.gpr .rsp, 8⟩ := by
    show (⟨_ + BitVec.ofNat 64 (248 + 8 * e), 8⟩ : Region) = _; rw [lay_ret]
  refine ⟨od, og, oc, dc, gc, ko, kd, kg, kc, e' ▸ ro, e' ▸ rd, e' ▸ rg, e' ▸ rc, no, nd, ng, nc, nt, tout, tsc,
    tstk, ?_, ?_⟩
  · show (s.gpr .rsp - BitVec.ofNat 64 (248 + 8 * e)).toNat + (248 + 8 * e) ≤ 2 ^ 64
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]
    have := (s.gpr .rsp).isLt
    omega_arith
  · intro T hT
    rw [lay_tbls] at hT
    obtain ⟨hn, hd⟩ := ht.2 T hT
    exact ⟨hn, hd _ (List.mem_cons_self ..), hd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      hd _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))⟩

theorem push_base (sp : Addr) (e : Nat) :
    sp - BitVec.ofNat 64 (8 * (28 + e)) = sp - BitVec.ofNat 64 (248 + 8 * e) + BitVec.ofNat 64 24 := by
  rw [show 8 * (28 + e) = 248 + 8 * e - 24 by omega_arith, ← Offset.ofNat_sub_ofNat (by omega_arith), Offset.sub_sub_eq]

theorem push_slot (sp : Addr) (e j : Nat) (hj : j < 4) :
    sp - BitVec.ofNat 64 (8 * (1 + e + j + 1)) = sp - BitVec.ofNat 64 (248 + 8 * e) + BitVec.ofNat 64 (232 - 8 * j) := by
  rw [show 8 * (1 + e + j + 1) = 248 + 8 * e - (232 - 8 * j) by omega_arith, ← Offset.ofNat_sub_ofNat (by omega_arith),
    Offset.sub_sub_eq]

theorem push_top (sp : Addr) (e : Nat) :
    sp - BitVec.ofNat 64 (8 * (0 + 1)) = sp - BitVec.ofNat 64 (248 + 8 * e) + BitVec.ofNat 64 (240 + 8 * e) := by
  rw [show 8 * (0 + 1) = 248 + 8 * e - (240 + 8 * e) by omega_arith, ← Offset.ofNat_sub_ofNat (by omega_arith),
    Offset.sub_sub_eq]

/-- The places of `D` and `B`, the `j`th word just above the pointers. -/
theorem push_db (sp : Addr) (e j : Nat) (hj : j < 2) (he : 2 ≤ e) :
    sp - BitVec.ofNat 64 (8 * (e - j + 1)) = sp - BitVec.ofNat 64 (248 + 8 * e) + BitVec.ofNat 64 (240 + 8 * j) := by
  rw [show 8 * (e - j + 1) = 248 + 8 * e - (240 + 8 * j) by omega_arith, ← Offset.ofNat_sub_ofNat (by omega_arith),
    Offset.sub_sub_eq]

theorem push_ctx {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance} {e : Nat}
    (he : e = 48) {H : Hash} {f : Fns} {ns : List String} {s : State}
    (h : (rfcX86_64 cs I (248 + 8 * e) (tabFacts H f) ns).pre s) :
    Ctx (lay I.hashLen I.ecdsa.curve.len e he cs H f s) s.gpr s.mem (pushed (pushRs e) s) := by
  have he2 : 2 ≤ e := by omega_arith
  have hn : 8 * (pushRs e).length ≤ (s.gpr .rsp).toNat := by rw [pushRs_length he2]; have := h.1; omega_arith
  obtain ⟨hf, hw⟩ := pushRegs_mem s (pushRs e) (by simp [pushRs]) hn
  have hw' : ∀ j (hj : j < 4), (pushed (pushRs e) s).mem.readW
      ((lay I.hashLen I.ecdsa.curve.len e he cs H f s).B + BitVec.ofNat 64 (232 - 8 * j)) 64 =
        s.gpr ([Reg.rdi, .rsi, .rdx, .rcx][j]'hj) :=
    fun j hj => by
      have hj' : 1 + e + j < (pushRs e).length := by rw [pushRs_length he2]; omega_arith
      have hr : (pushRs e)[1 + e + j]'hj' = [Reg.rdi, .rsi, .rdx, .rcx][j]'hj := by
        simp only [pushRs, List.append_assoc, show 1 + e + j = (e + j) + 1 by omega_arith, List.getElem_cons_succ]
        rw [List.getElem_append_right (by simp <;> omega_arith)]
        simp only [List.length_replicate]
        rw [List.getElem_append_right (by simp <;> omega_arith)]
        simp only [List.length_cons, List.length_nil]
        rw [List.getElem_append_left (by simp <;> omega_arith)]
        congr 1; omega_arith
      rw [← hr, ← hw (1 + e + j) hj']; simp only [lay]; rw [push_slot _ e j hj]; rfl
  have hdb : ∀ j (hj : j < 2), (pushed (pushRs e) s).mem.readW
      ((lay I.hashLen I.ecdsa.curve.len e he cs H f s).B + BitVec.ofNat 64 (240 + 8 * j)) 64 =
        s.gpr ([Reg.r10, .r11][j]'hj) :=
    fun j hj => by
      have hj' : e - j < (pushRs e).length := by rw [pushRs_length he2]; omega_arith
      have hr : (pushRs e)[e - j]'hj' = [Reg.r10, .r11][j]'hj := by
        simp only [pushRs, List.append_assoc, show e - j = (e - 1 - j) + 1 by omega_arith, List.getElem_cons_succ]
        rw [List.getElem_append_right (by simp <;> omega_arith)]
        simp only [List.length_replicate]
        rw [List.getElem_append_left (by simp <;> omega_arith)]
        rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
        · simp only [show e - 1 - 0 - (e - 2) = 1 by omega_arith]; rfl
        · simp only [show e - 1 - 1 - (e - 2) = 0 by omega_arith]; rfl
      rw [← hr, ← hw (e - j) hj']; simp only [lay]; rw [push_db _ e j hj he2]; rfl
  have hwt : (pushed (pushRs e) s).mem.readW
      ((lay I.hashLen I.ecdsa.curve.len e he cs H f s).B + BitVec.ofNat 64 (240 + 8 * e)) 64 = s.gpr .r9 := by
    have := hw 0 (by rw [pushRs_length he2]; omega_arith)
    simp only [pushRs, List.getElem_cons_zero] at this
    rw [← this]; simp only [lay]; rw [push_top _ e]; rfl
  have ht := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htf : tabFacts H f s := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨by rw [pushed_rd, h.2.1, lay_tbls]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr,
    hw' 3 (by omega_arith), hw' 2 (by omega_arith), hw' 1 (by omega_arith), hw' 0 (by omega_arith), hwt,
    (hdb 0 (by omega_arith)).trans htf.2.2.1, (hdb 1 (by omega_arith)).trans htf.2.2.2, ?_,
    fun c hc => (congrFun (pushRegs_syms s _) c.1).trans
      (lay_sy I.hashLen I.ecdsa.curve.len e he (cs := cs) (H := H) (f := f) s c hc).symm,
    fun c hc i hi => ?_, ?_, ?_, ?_⟩
  · rw [pushed_wr, h.2.2.1, pushRs_length he2, push_base, show 8 * (28 + e) = 224 + 8 * e by omega_arith]; rfl
  · rw [pushed_rsp, pushRs_length he2, push_base]; rfl
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(lay I.hashLen I.ecdsa.curve.len e he cs H f s).STK, by simp, ?_⟩
    rw [pushRs_length he2, push_base]
    exact Offset.sub_base (n := 8 * (28 + e)) (k := 248 + 8 * e) _ (by omega_arith)
  · rw [lay_sy I.hashLen I.ecdsa.curve.len e he (cs := cs) (H := H) (f := f) s c hc]
    exact ht.1 c hc i hi
  · show TabOK H f (pushRegs s (pushRs e)).syms
    rw [pushRegs_syms]; exact htf.1
  · show TabMem H (pushRegs s (pushRs e)).syms (s.gpr .r9) s.mem
    rw [pushRegs_syms]; exact htf.2.1
  · intro n hn
    show (pushRegs s (pushRs e)).syms n = (if n ∈ [H.hmacInitN, H.updN, H.hmacFinN] then s.syms n else 0)
    have hn' : n ∈ [H.hmacInitN, H.updN, H.hmacFinN] := hn
    rw [pushRegs_syms, ite_eq_left_of_eq_true _ _ (eq_true hn')]

end VG.Proof.Ecdsa.Rfc6979.X86_64
