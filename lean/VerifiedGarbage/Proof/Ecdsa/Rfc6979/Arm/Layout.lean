module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm
import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.SymsInstr
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Contract
public import VerifiedGarbage.Proof.HmacTable.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# Deterministic ECDSA on 32-bit ARM: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`, the table `hmac` of 24 bytes, the 8 bytes of stack arguments
above the stack pointer) and the 536 bytes of stack below the stack
pointer, from `B` up (`Lay dn`): the 24 bytes the calls use (their frames
and the 16 bytes HMAC's functions use below theirs), then the frame of 512
bytes, from `B + 24`: `K`, `V`, `h`, `X`, `core`'s digest, `T` and its
length (`LOW`, with the calls' 24 bytes), then our caller's `r4`–`r11` and
`lr` and the pointer `digest` (`TOP`). `Ctx` is what holds between the
prologue and the frame's release: the permissions, `sp`, the registers that
hold the pointers (`r4`–`r6`, `r8`, `r11`), our caller's registers and
`digest` in the frame, that memory changed only in `out`, `scratch` and the
stack, where the tables of constants `core` reads are, and that the table
holds the hash function `F`'s HMAC functions, which an indirect call of
`f`'s reaches. Code that writes only regions apart from `TOP` (`Safe`) keeps
it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm
open VG.Arm.FrameStack (addr_sub' sub_toNat')
open VG.Proof.X25519.Arm (Upd Mupd)
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns)
open VG.Proof.HmacTable.Arm (TabOK TabMem tA)

/-- The stack the function uses: the frame and the calls' 24 bytes. -/
def stackT : Nat := 536

/-- The buffers, as the registers and stack arguments hold them, and the
stack pointer on entry, for a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) where
  out : BitVec 32
  d : BitVec 32
  dg : BitVec 32
  scr : BitVec 32
  /-- The table of HMAC. -/
  tab : BitVec 32
  sp : BitVec 32
  q : Nat
  /-- The tables of constants `core` reads, and their statics' addresses. -/
  cs : List (String × List (BitVec 64)) := []
  sy : String → BitVec 32 := fun _ => 0
  /-- The hash function's functions, which the table holds, and the
  functions an indirect call of a table's functions may reach. -/
  F : Impl.Pbkdf2.Whole.Arm.Fns
  f : Fns
  /-- The addresses of `F`'s HMAC functions, public. -/
  fa : String → BitVec 32

namespace Lay

variable {dn : Nat} (L : Lay dn)

/-- The lowest byte of the stack used. -/
abbrev B : Addr := State.addr L.sp - BitVec.ofNat 64 536
/-- The frame's base, as `sp` and `r8` hold it. -/
abbrev fp : BitVec 32 := L.sp - BitVec.ofNat 32 512

abbrev OUT : Region := ⟨State.addr L.out, 2 * L.q⟩
abbrev D : Region := ⟨State.addr L.d, L.q⟩
abbrev DG : Region := ⟨State.addr L.dg, dn⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
/-- The table of HMAC. -/
abbrev TAB : Region := ⟨State.addr L.tab, 24⟩
/-- The stack arguments. -/
abbrev ARGS : Region := ⟨State.addr L.sp, 8⟩
abbrev TBLs : List Region := Abi.constRegions (fun n => State.addr (L.sy n)) L.cs
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 536⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 24, 512⟩
/-- The stack below the saved registers: the calls', and the frame's buffers. -/
abbrev LOW : Region := ⟨L.B, 492⟩

/-- What the contract says of where the buffers and the stack are (`d` and
`digest`, which are only read, may overlap, and the table with them). -/
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
  /-- The table does not wrap around, and is apart from what the code writes. -/
  nt : L.tab.toNat + 24 ≤ 2 ^ 32
  to : L.TAB.Disjoint L.OUT
  tc : L.TAB.Disjoint L.SCR
  tk : L.TAB.Disjoint L.STK
  /-- The stack arguments are apart from what the code writes. -/
  ao : L.ARGS.Disjoint L.OUT
  ac : L.ARGS.Disjoint L.SCR
  nB : 536 ≤ L.sp.toNat
  na : L.sp.toNat + 8 ≤ 2 ^ 32
  tables : ∀ r∈L.TBLs,r.base.toNat+r.len≤2^32 ∧ (∀ w∈[L.OUT,L.SCR,L.STK],r.Disjoint w) ∧ r.base.toNat%64=0

end Lay

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn} (h : L.Ok)
include h

theorem B_toNat : L.B.toNat = L.sp.toNat - 536 := by
  have := h.nB; have := L.sp.isLt
  simp only [Lay.B, BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_addr]; omega

theorem B_fit : L.B.toNat + 536 ≤ 2 ^ 32 := by
  have := L.sp.isLt; have := h.nB; rw [h.B_toNat]; omega

omit h in
/-- The stack pointer on entry, from `B`. -/
theorem spA : State.addr L.sp = L.B + BitVec.ofNat 64 536 := by
  simp only [Lay.B, BitVec.sub_add_cancel]

/-- `fp + o`, as an address: `B + 24 + o`. -/
theorem fpA {o : Nat} (ho : o < 520) :
    State.addr (L.fp + BitVec.ofNat 32 o) = L.B + BitVec.ofNat 64 (24 + o) := by
  have hn := h.nB; have := L.sp.isLt
  have hfp : L.fp.toNat = L.sp.toNat - 512 := sub_toNat' (by omega)
  rw [addr_add (by rw [hfp]; have := h.na; omega), Lay.fp, addr_sub' (by omega),
    Offset.sub_ofNat_eq _ (show 512 ≤ 536 by omega), show 536 - 512 = 24 by omega, Offset.add_add]

theorem fpA0 : State.addr L.fp = L.B + BitVec.ofNat 64 24 := by
  have := h.fpA (o := 0) (by decide)
  rwa [BitVec.add_zero] at this

theorem stk_scr {d n e k : Nat} (h₁ : d + n ≤ 536) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨State.addr L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_SCR {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

theorem stk_TAB {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.TAB := (h.tk.sub_right (Offset.sub_base _ h₁)).symm

end Lay.Ok

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame. -/
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 536) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 24, 512⟩ :=
  ⟨d - 24, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below the saved registers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 492) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (Offset.sub_base _ h))

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr fun x hx => hs x (h x hx))]

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) :
    Safe L ⟨State.addr L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

/-- The saved registers and `digest` are apart from every safe region. -/
theorem top_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 492, 44⟩ r := by
  have := h.B_fit
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

theorem tab_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.TAB.Disjoint r := by
  rcases hs with hs | hs | hs
  · exact h.to.sub_right hs
  · exact h.tc.sub_right hs
  · exact (h.tk.sub_right (Region.sub_prefix (by omega))).sub_right hs

end Lay.Ok

/-! ## Between the prologue and the frame's release -/

/-- The registers that hold the pointers between the calls. -/
abbrev ptrRegs : List Reg := [.r4, .r5, .r6, .r8, .r11]

/-- The state between the prologue and the frame's release: `g` are the
registers on entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.TAB, L.ARGS] ++ L.TBLs
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  sp : t.sp = L.fp
  r4 : t.gpr .r4 = L.out
  r5 : t.gpr .r5 = L.d
  r6 : t.gpr .r6 = L.tab
  r8 : t.gpr .r8 = L.fp
  r11 : t.gpr .r11 = L.scr
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, t.mem.readW (L.B + BitVec.ofNat 64 (24 + p.2)) 32 = g p.1
  /-- The pointer `digest`, at the frame's top. -/
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 (24 + Impl.Ecdsa.Rfc6979.Arm.fDigest)) 32 = L.dg
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : ∀ c∈L.cs,t.syms c.1=L.sy c.1
  held : Abi.constsHeld m₀ (fun n => State.addr (L.sy n)) L.cs
  /-- The table: an indirect call reaches `F`'s functions, whose addresses
  it holds, then its digest length and HMAC's block size. -/
  tabOk : TabOK L.F L.f t.syms
  tabMem : TabMem L.F t.syms L.tab m₀
  tabD : m₀.readW (tA L.tab Impl.Ecdsa.Rfc6979.Arm.tD) 32 = BitVec.ofNat 32 L.F.H.D
  tabB : m₀.readW (tA L.tab Impl.Ecdsa.Rfc6979.Arm.tB) 32 = BitVec.ofNat 32 L.F.H.B
  fsy : ∀ n ∈ [L.F.hiN, L.F.H.updN, L.F.hfN], t.syms n = L.fa n

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega) a (h a ha)⟩

theorem saved_off : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, 468 ≤ p.2 ∧ p.2 + 4 ≤ 504 := by decide

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `sp` and the registers that hold the
pointers, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hp : ∀ r ∈ ptrRegs, t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) (hsy : t'.syms=t.syms) :
    Ctx L g m₀ t' := by
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hp _ (by decide)).trans hc.r4,
    (hp _ (by decide)).trans hc.r5, (hp _ (by decide)).trans hc.r6, (hp _ (by decide)).trans hc.r8,
    (hp _ (by decide)).trans hc.r11, fun p hp' => ?_, ?_, hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame),
    fun c hc' => by rw [hsy]; exact hc.sy c hc',hc.held, by rw [hsy]; exact hc.tabOk,
    by rw [hsy]; exact hc.tabMem, hc.tabD, hc.tabB, by rw [hsy]; exact hc.fsy⟩
  · have ho := saved_off p hp'
    rw [hf.readW (r := ⟨L.B + BitVec.ofNat 64 492, 44⟩) (Offset.contains _ (by omega) (by omega)
      (by have := hL.B_fit; omega)) (fun r hr => hL.top_safe (hs r hr)) (by decide)]
    exact hc.saved p hp'
  · rw [hf.readW (r := ⟨L.B + BitVec.ofNat 64 492, 44⟩) (Offset.contains _ (by decide) (by decide)
      (by have := hL.B_fit; omega)) (fun r hr => hL.top_safe (hs r hr)) (by decide)]
    exact hc.pDg

/-- An update of one register, not one that holds a pointer. -/
theorem upd (hc : Ctx L g m₀ t) {d : Reg} {v : BitVec 32} (u : UpdS t t' d v) (hd : d ∉ ptrRegs) :
    Ctx L g m₀ t' :=
  ⟨u.rd.trans hc.rd, u.wr.trans hc.wr, u.sp.trans hc.sp,
    (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r4, (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r5,
    (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r6, (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r8,
    (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r11, fun p hp => by rw [u.mem]; exact hc.saved p hp,
    by rw [u.mem]; exact hc.pDg, by rw [u.mem]; exact hc.frame,fun c hc' => by rw [u.syms]; exact hc.sy c hc',
    hc.held, by rw [u.syms]; exact hc.tabOk, by rw [u.syms]; exact hc.tabMem, hc.tabD, hc.tabB,
    by rw [u.syms]; exact hc.fsy⟩

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

/-- A word of the table, as on entry. -/
theorem tabWord (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 4 ≤ 24) :
    t.mem.readW (tA L.tab o) 32 = m₀.readW (tA L.tab o) 32 := by
  rw [tA, addr_add (by have := hL.nt; omega)]
  exact hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.to
      · exact hL.tc
      · exact hL.tk) (by decide)

theorem inFr (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 536) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 536) :
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

theorem inTab (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (h : o + 4 ≤ 24) :
    InRegions (t.rd ++ t.wr) (tA L.tab o) 4 := by
  rw [tA, addr_add (by have := hL.nt; omega)]
  exact ⟨L.TAB, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

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

end VG.Proof.Ecdsa.Rfc6979.Arm
