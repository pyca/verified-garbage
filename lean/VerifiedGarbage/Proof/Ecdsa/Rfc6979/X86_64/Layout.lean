module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Contract
public import VerifiedGarbage.Proof.HashFns.X86_64.Calls
public import VerifiedGarbage.Proof.Framework.X86_64.Funs

/-!
# Deterministic ECDSA on x86-64: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`) and the `240 + 8 e` bytes of stack below its return address, from
`B` up (`Lay dn`): the 24 bytes the calls use (a call's return address, and
the 8 bytes a streaming function uses below its own), then the frame of
`27 + e` words, from `B + 24`: `K` and `V` (64 bytes each), `h` (48 bytes,
of which `q` are used), the number of candidates left, the pointers to
`scratch`, `digest`, `d` and `out`, and `e` more words (21): the addresses of
the streaming `init`, `update` and `finalize` (`fi`, `fu`, `ff`), and 18
above them (`HIGH`: the digest for `core` and the candidate if the hash is
shorter than the scalars, or `h` for 64-byte scalars). `Ctx` is what holds
between the frame's push and pop: the permissions, `rsp`, the callee-saved
registers, the pointers and the addresses in the frame, that memory changed
only in `out`, `scratch` and the stack, where the tables of constants `core`
reads are (`TBLs`, the comb's), and that the state may call the streaming
functions: it keeps `World` of an entry like the anchor `E` (`Like`, the same
program and regions), in which they meet their contracts (`Fns`). Code that
writes only regions apart from the pointers and the addresses (`Safe`) keeps
it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- The streaming functions `T`, at the addresses `fi`, `fu` and `ff`, as the
contract of a function under `abi.withConsts cs` states them in its entry `e`
(`FnMeets`, as `HashFns.X86_64.C.Fns`), and the tables `cs` there
(`CallC.ConstsAt`), which the calls pass them too. -/
structure FnsK (cs : List (String × List (BitVec 64))) (e : State) (T : Spec.HashFns.Streaming)
    (fi fu ff : Addr) : Prop where
  init : FnMeets (abi.withConsts cs) (fun A n => Spec.HashFns.initContract T A n) 8 408 e fi
  upd : FnMeets (abi.withConsts cs) (fun A n => Spec.HashFns.updateContract T A n) 8 408 e fu
  fin : FnMeets (abi.withConsts cs) (fun A n => Spec.HashFns.finalizeContract T A n) 8 408 e ff
  consts : VG.X86_64.CallC.ConstsAt 408 e cs

/-- An entry state like the anchor's `E`: of the same program, with the same
regions and stack pointer. -/
structure Like (E e : State) : Prop where
  same : abi.sameWorld e E
  rd : e.rd = E.rd
  wr : e.wr = E.wr
  sp : e.gpr .rsp = E.gpr .rsp

/-- The buffers and the lowest byte of the stack used (`rsp - (240 + 8 e)` on
entry), for a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) where
  out : Addr
  d : Addr
  dg : Addr
  scr : Addr
  B : Addr
  q : Nat
  /-- The words above the frame's pointers. -/
  e : Nat
  he : e = 21
  /-- Further regions the function may read (which it does not). -/
  X : List Region
  /-- The tables of constants `core` reads, and their statics' addresses. -/
  cs : List (String × List (BitVec 64))
  sy : String → Addr
  /-- An entry of the program, the anchor of the runs' entries (`Like`). -/
  E : State
  /-- The streaming functions, and their addresses. -/
  T : Spec.HashFns.Streaming
  fi : Addr
  fu : Addr
  ff : Addr

namespace Lay

variable {dn : Nat} (L : Lay dn)

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 240 + 8 * L.e⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 24, 216 + 8 * L.e⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 (240 + 8 * L.e), 8⟩
/-- The stack below the frame's pointers: the calls' and `K`, `V`, `h` and the count. -/
abbrev LOW : Region := ⟨L.B, 208⟩
/-- The frame above its pointers and the streaming functions' addresses. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 264, 8 * L.e - 24⟩
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
  nb : L.B.toNat + (240 + 8 * L.e) ≤ 2 ^ 64
  /-- The tables do not wrap around, and are apart from what the code writes. -/
  tbl : ∀ T ∈ L.TBLs, T.base.toNat + T.len ≤ 2 ^ 64 ∧ T.Disjoint L.OUT ∧ T.Disjoint L.SCR ∧ T.Disjoint L.STK

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
`scratch` or the stack below the frame's pointers or above the streaming
functions' addresses. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 208) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Offset.sub_base _ h)))

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

theorem safe_high {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 264 ≤ d) (h₂ : d + n ≤ 240 + 8 * L.e) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ (by have := L.he; omega))))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

theorem stk_d (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.d, L.q⟩ := h.stk_D h₁

/-- The frame's pointers and the streaming functions' addresses are apart
from every safe region. -/
theorem ptrs_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 208, 56⟩ r := by
  have := L.he
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega) (by omega)).sub_right hs
  · have := L.he
    exact (Offset.disjoint _ (by omega) (by omega) (by omega)).sub_right hs

/-- The buffers that are only read are apart from every safe region. -/
theorem d_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.D.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.od.symm.sub_right hs
  · exact h.dc.sub_right hs
  · exact (h.kd.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs
  · have := L.he
    exact (h.kd.symm.sub_right (Offset.sub_base _ (by omega))).sub_right hs

theorem dg_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.DG.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact h.og.symm.sub_right hs
  · exact h.gc.sub_right hs
  · exact (h.kg.symm.sub_right (Region.sub_prefix (by omega))).sub_right hs
  · have := L.he
    exact (h.kg.symm.sub_right (Offset.sub_base _ (by omega))).sub_right hs

end Lay.Ok

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` are the registers on
entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG] ++ L.X ++ L.TBLs
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 24
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 208) 64 = L.scr
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 216) 64 = L.dg
  pD : t.mem.readW (L.B + BitVec.ofNat 64 224) 64 = L.d
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 232) 64 = L.out
  pFi : t.mem.readW (L.B + BitVec.ofNat 64 240) 64 = L.fi
  pFu : t.mem.readW (L.B + BitVec.ofNat 64 248) 64 = L.fu
  pFf : t.mem.readW (L.B + BitVec.ofNat 64 256) 64 = L.ff
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : ∀ c ∈ L.cs, t.syms c.1 = L.sy c.1
  held : Abi.constsHeld m₀ L.sy L.cs
  /-- The state keeps `World` of an entry like the anchor, in which the
  streaming functions meet their contracts. -/
  calls : ∃ e, World 408 e t ∧ FnsK L.cs e L.T L.fi L.fu L.ff ∧ Like L.E e ∧
    e.wr = [L.OUT, L.SCR] ∧ e.gpr .rsp = L.B + BitVec.ofNat 64 408

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base (p := L.B) (d := 264) (n := 8 * L.e - 24)
      (by have := L.he; omega) a (h a ha)⟩

/-- The 408 bytes of stack of an entry with the stack pointer `B + 408`, which the function's frame and calls use. -/
theorem stk_reserved {dn : Nat} (L : Lay dn) {e : State} (hsp : e.gpr .rsp = L.B + BitVec.ofNat 64 408) :
    L.STK ∈ abi.reserved 408 e := by
  have := L.he
  show (⟨L.B, 240 + 8 * L.e⟩ : Region) ∈ ⟨e.gpr .rsp, 8⟩ :: stackBelow (e.gpr .rsp) 408
  rw [hsp, show 240 + 8 * L.e = 408 by omega]
  exact List.mem_cons_of_mem _ (by simp [stackBelow, BitVec.add_sub_cancel])

/-- A safe region is an entry's own, for an entry whose writable regions
are `out` and `scratch` and whose stack is the stack used. -/
theorem owned_safe {dn : Nat} (L : Lay dn) {e : State} (hwr : e.wr = [L.OUT, L.SCR])
    (hsp : e.gpr .rsp = L.B + BitVec.ofNat 64 408) {ws : List Region} (hs : ∀ r ∈ ws, Safe L r) :
    Owned 408 e ws := fun r hr x hx => by
  obtain ⟨R, hR, hsub⟩ := (hs r hr).sub_frame
  refine ⟨R, ?_, hsub x hx⟩
  rw [hwr]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · simp
  · simp
  · exact List.mem_append_right _ (stk_reserved L hsp)

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `rsp` and the callee-saved registers,
and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms ∧ t'.funs = t.funs) : Ctx L g m₀ t' := by
  have keep : ∀ d, 208 ≤ d → d + 8 ≤ 264 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 208, 56⟩)
      (Offset.contains _ h₁ (by omega) (by omega)) (fun r hr => hL.ptrs_safe (hs r hr)) (by decide)
  obtain ⟨e, hW, hF, hl, hew, hes⟩ := hc.calls
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.rsp, fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'),
    (keep 208 (by omega) (by omega)).trans hc.pScr, (keep 216 (by omega) (by omega)).trans hc.pDg,
    (keep 224 (by omega) (by omega)).trans hc.pD, (keep 232 (by omega) (by omega)).trans hc.pOut,
    (keep 240 (by omega) (by omega)).trans hc.pFi, (keep 248 (by omega) (by omega)).trans hc.pFu,
    (keep 256 (by omega) (by omega)).trans hc.pFf,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame), by rw [hsy.1]; exact hc.sy, hc.held,
    ⟨e, hW.step hsy.2 hsy.1 hf (owned_safe L hew hes hs), hF, hl, hew, hes⟩⟩

/-- Code that writes only caller-saved registers. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsy : t'.syms = t.syms ∧ t'.funs = t.funs) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
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
    R ∈ [L.D, L.DG] ++ L.X ++ L.TBLs ++ [L.FR, L.OUT, L.SCR] := by
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

/-- The body's entry `s`, after `entry` and the choice of the hash
function's configuration, in a run from the function's entry `e`, which is
like the anchor `E`: the streaming functions `T`, at the addresses in `r9`,
`r10` and `r11`, meet their contracts in `e`, and `s` keeps `World` of it. -/
def BodyIn (cs : List (String × List (BitVec 64))) (T : Spec.HashFns.Streaming) (E s : State) : Prop :=
  ∃ e, World 408 e s ∧ FnsK cs e T (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧ Like E e ∧
    e.wr = s.wr ∧ e.gpr .rsp = s.gpr .rsp

open VG.Impl.Ecdsa.Rfc6979.X86_64 (Cfg)

theorem pushRs_length : Cfg.pushRs.length = 48 := rfl

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q`, the tables `cs` (the statics' addresses, public, of those tables only),
the anchor `E` and the streaming functions `T`, at the addresses in `r9`,
`r10` and `r11`. -/
def lay (dn q : Nat) (cs : List (String × List (BitVec 64))) (E : State) (T : Spec.HashFns.Streaming)
    (s : State) (X : List Region := []) : Lay dn :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .rsp - BitVec.ofNat 64 408, q, 21, rfl, X, cs,
    fun n => if n ∈ cs.map Prod.fst then s.syms n else 0, E, T, s.gpr .r9, s.gpr .r10, s.gpr .r11⟩

variable {dn q : Nat} {cs : List (String × List (BitVec 64))} {E : State} {T : Spec.HashFns.Streaming}
  {X : List Region}

theorem lay_ret (s : State) : (lay dn q cs E T s X).B + BitVec.ofNat 64 (240 + 8 * 21) = s.gpr .rsp :=
  BitVec.sub_add_cancel _ _

theorem lay_sy (s : State) : ∀ c ∈ cs, (lay dn q cs E T s X).sy c.1 = s.syms c.1 := fun c hc => by
  simp only [lay, List.mem_map_of_mem (f := Prod.fst) hc, ite_true]

theorem lay_tbls (s : State) : (lay dn q cs E T s X).TBLs = Abi.constRegions (fun n => s.syms n) cs :=
  constRegions_congr (lay_sy s)

theorem lay_ok {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcX86_64 cs I 408 X).pre s) :
    (lay I.hashLen I.ecdsa.curve.len cs E T s X).Ok := by
  obtain ⟨hsp, -, -, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, -, ht⟩ := h
  have e' : (lay I.hashLen I.ecdsa.curve.len cs E T s X).RET = ⟨s.gpr .rsp, 8⟩ := by
    show (⟨_ + BitVec.ofNat 64 (240 + 8 * 21), 8⟩ : Region) = _; rw [lay_ret]
  refine ⟨od, og, oc, dc, gc, ko, kd, kg, kc, e' ▸ ro, e' ▸ rd, e' ▸ rg, e' ▸ rc, no, nd, ng, nc, ?_, ?_⟩
  · show (s.gpr .rsp - BitVec.ofNat 64 408).toNat + (240 + 8 * 21) ≤ 2 ^ 64
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
    have := (s.gpr .rsp).isLt
    omega
  · intro T hT
    rw [lay_tbls] at hT
    obtain ⟨hn, hd⟩ := ht T hT
    exact ⟨hn, hd _ (List.mem_cons_self ..), hd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      hd _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))⟩

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 48) = sp - BitVec.ofNat 64 408 + BitVec.ofNat 64 24 := by
  rw [show 8 * 48 = 408 - 24 by rfl, ← Offset.ofNat_sub_ofNat (by decide), Offset.sub_sub_eq]

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 7) :
    sp - BitVec.ofNat 64 (8 * (18 + j + 1)) = sp - BitVec.ofNat 64 408 + BitVec.ofNat 64 (256 - 8 * j) := by
  rw [show 8 * (18 + j + 1) = 408 - (256 - 8 * j) by omega, ← Offset.ofNat_sub_ofNat (by omega),
    Offset.sub_sub_eq]

theorem push_ctx {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcX86_64 cs I 408 X).pre s)
    (hb : BodyIn cs T E s) :
    Ctx (lay I.hashLen I.ecdsa.curve.len cs E T s X) s.gpr s.mem (pushed Cfg.pushRs s) := by
  have hn : 8 * Cfg.pushRs.length ≤ (s.gpr .rsp).toNat := by rw [pushRs_length]; have := h.1; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s Cfg.pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 7), (pushed Cfg.pushRs s).mem.readW
      ((lay I.hashLen I.ecdsa.curve.len cs E T s X).B + BitVec.ofNat 64 (256 - 8 * j)) 64 =
        s.gpr ([Reg.r11, .r10, .r9, .rdi, .rsi, .rdx, .rcx][j]'hj) :=
    fun j hj => by
      have hj' : 18 + j < Cfg.pushRs.length := by rw [pushRs_length]; omega
      have hr : Cfg.pushRs[18 + j]'hj' = [Reg.r11, .r10, .r9, .rdi, .rsi, .rdx, .rcx][j]'hj := by
        simp only [Cfg.pushRs, Cfg.extra, List.append_assoc]
        rw [List.getElem_append_right (by simp <;> omega)]
        simp only [List.length_replicate, Nat.add_sub_cancel_left]
        rw [List.getElem_append_left (by simp <;> omega)]
      rw [← hr, ← hw (18 + j) hj']; simp only [lay]; rw [push_slot _ j hj]; rfl
  have ht := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * Cfg.pushRs.length), 8 * Cfg.pushRs.length⟩
      (lay I.hashLen I.ecdsa.curve.len cs E T s X).STK := by
    rw [pushRs_length, push_base]
    exact Offset.sub_base (n := 8 * 48) (k := 240 + 8 * 21) _ (by omega)
  obtain ⟨e, hW, hF, hl, hew, hes⟩ := hb
  have hwr : s.wr = [⟨s.gpr .rdi, 2 * I.ecdsa.curve.len⟩, ⟨s.gpr .rcx, 8192⟩] := h.2.2.1
  have hfs : Frame [(lay I.hashLen I.ecdsa.curve.len cs E T s X).STK] s.mem (pushed Cfg.pushRs s).mem :=
    hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, hst⟩
  have hes' : e.gpr .rsp = (lay I.hashLen I.ecdsa.curve.len cs E T s X).B + BitVec.ofNat 64 408 :=
    hes.trans (lay_ret s).symm
  refine ⟨by rw [pushed_rd, h.2.1, lay_tbls]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr,
    hw' 6 (by omega), hw' 5 (by omega), hw' 4 (by omega), hw' 3 (by omega), hw' 2 (by omega),
    hw' 1 (by omega), hw' 0 (by omega), hfs.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩,
    fun c hc => (congrFun (pushRegs_syms s Cfg.pushRs) c.1).trans
      (lay_sy (dn := I.hashLen) (q := I.ecdsa.curve.len) (cs := cs) (E := E) (T := T) (X := X) s c hc).symm,
    fun c hc i hi => ?_, ⟨e, hW.step (pushRegs_funs s _) (pushRegs_syms s _) hfs fun r hr x hx => ?_,
      hF, hl, hew.trans hwr, hes'⟩⟩
  · rw [pushed_wr, hwr, pushRs_length, push_base]; rfl
  · rw [pushed_rsp, pushRs_length, push_base]; rfl
  · rw [lay_sy (dn := I.hashLen) (q := I.ecdsa.curve.len) (cs := cs) (E := E) (T := T) (X := X) s c hc]
    exact ht c hc i hi
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_right _ (stk_reserved _ hes'), hx⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
