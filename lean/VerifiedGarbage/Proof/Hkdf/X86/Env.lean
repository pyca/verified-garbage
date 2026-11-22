module

public import VerifiedGarbage.Proof.HmacTable.X86
public import VerifiedGarbage.Impl.Hkdf.X86
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# HKDF on x86 (32-bit): where everything is, between a frame's entry and release

The three functions share a shape (`Impl/Hkdf/X86.lean`): a frame of `FB`
bytes, whose first 16 hold our caller's `ebx`, `esi`, `edi` and `ebp`,
below which the calls use `cb` bytes; our `NA` arguments above it and the
return address, one of them (`ti`) the table `hmac`; and one buffer they
write (`W`). `Lay` is what of a call is public: `esp` on entry (`E`), the
arguments, the regions on entry and the addresses of the table's functions;
every place in the stack is at an offset of the lowest byte used, `B`
(`E - (FB + cb)`): the calls' bytes (`CALLS`), the frame (`FR`, from `F`,
`esp` in the body), the return address (`RET`) and the arguments (`ARGS`).

`Ctx` is what holds between the frame's entry and its release, for the
variant `K.w` of the table's hash function and the functions an indirect
call of the table may reach (`K.f`): the permissions, `esp`, the saved
registers, that memory changed only in `W` and the stack, and what the
arguments, the table and the symbols were on entry. Code that keeps the
permissions and `esp` and writes only `W`, the frame above the saved
registers or the calls' bytes (`Safe`) keeps it (`Ctx.keep`). `Upd` is code
that sets one register; the lemmas after it are those of each kind of
instruction the code has.
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86

open VG VG.X86 VG.X86.Wp
open VG.Impl.Ecdsa.Rfc6979.X86 (Fns)
open VG.Proof.HmacTable.X86 (HVar TabOK TabMem)

/-- A frame's shape: its size, the bytes below it the calls use, the number
of arguments, and which is the table. -/
structure Sh where
  FB : Nat
  cb : Nat
  NA : Nat
  ti : Nat

/-- A call's public data, for a frame of the shape `S`: `esp` on entry, the
arguments, the buffer the function writes, the regions on entry, and the
addresses of the table's functions. -/
structure Lay (S : Sh) where
  E : BitVec 32
  a : Nat → BitVec 32
  W : Region
  rd : List Region
  wr : List Region
  fa : String → BitVec 32

namespace Lay

variable {S : Sh} (L : Lay S)

/-- The stack used below the return address. -/
abbrev N : Nat := S.FB + S.cb
theorem N_eq : L.N = S.FB + S.cb := rfl
/-- `esp` in the frame's body. -/
abbrev F : BitVec 32 := L.E - BitVec.ofNat 32 S.FB
/-- The lowest byte of the stack used. -/
abbrev B : Addr := (L.E - BitVec.ofNat 32 L.N).setWidth 64
/-- The table. -/
abbrev tb : BitVec 32 := L.a S.ti

abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 S.cb, S.FB⟩
abbrev CALLS : Region := ⟨L.B, S.cb⟩
abbrev STK : Region := ⟨L.B, L.N⟩
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 L.N, 4⟩
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 (L.N + 4), 4 * S.NA⟩
abbrev TAB : Region := ⟨L.tb.setWidth 64, 24⟩
/-- The frame above the saved registers. -/
abbrev HI : Region := ⟨L.B + BitVec.ofNat 64 (S.cb + 16), S.FB - 16⟩
/-- The saved registers. -/
abbrev SV : Region := ⟨L.B + BitVec.ofNat 64 S.cb, 16⟩

/-- What the contracts say of where the buffers and the stack are, and what
the frame's shape needs. -/
structure Ok : Prop where
  e0 : L.N ≤ L.E.toNat
  e1 : L.E.toNat + 4 + 4 * S.NA ≤ 2 ^ 32
  s0 : 16 ≤ S.FB
  s1 : S.FB < 4096
  s2 : S.FB % 4 = 0
  ti : S.ti < S.NA
  c76 : 76 ≤ S.cb
  nW : L.W.base.toNat + L.W.len ≤ 2 ^ 32
  kW : L.STK.Disjoint L.W
  rW : L.RET.Disjoint L.W
  aW : L.ARGS.Disjoint L.W
  nt : L.tb.toNat + 24 ≤ 2 ^ 32
  tW : L.TAB.Disjoint L.W
  tK : L.TAB.Disjoint L.STK
  tRd : L.TAB ∈ L.rd
  aWr : L.ARGS ∈ L.wr
  wWr : L.W ∈ L.wr

end Lay

namespace Lay.Ok

variable {S : Sh} {L : Lay S} (h : L.Ok)
include h

theorem BN : L.B.toNat = L.E.toNat - L.N := by
  have := h.e0; have := L.N_eq
  simp only [Lay.B, BitVec.toNat_setWidth]
  rw [sub_toNat (by omega_arith)]; have := L.E.isLt; omega_arith

theorem nB : L.B.toNat + L.N + 4 + 4 * S.NA ≤ 2 ^ 32 := by
  have := L.N_eq; have := h.e0; have := h.e1; rw [h.BN]; omega_arith

theorem FN : L.F.toNat = L.E.toNat - S.FB := sub_toNat (by have := h.e0; have := L.N_eq; omega_arith)

theorem B_eq : L.B = L.E.setWidth 64 - BitVec.ofNat 64 L.N := Taint.sub_setWidth h.e0

/-- `[F + o]`, for `o` in the frame or the arguments above it. -/
theorem addrF {o : Nat} (ho : o ≤ S.FB + 4 * S.NA) : addr L.F o = L.B + BitVec.ofNat 64 (S.cb + o) := by
  have := h.e0; have := h.e1; have := L.N_eq
  rw [addr_eq (by rw [h.FN]; omega_arith), Lay.F, Taint.sub_setWidth (by omega_arith), h.B_eq,
    Offset.sub_ofNat_eq _ (show S.FB ≤ L.N by omega_arith), show L.N - S.FB = S.cb by omega_arith, Offset.add_add]

theorem F64 : L.F.setWidth 64 = L.B + BitVec.ofNat 64 S.cb := by
  have e := h.addrF (o := 0) (by omega_arith)
  rwa [addr, BitVec.add_zero, Nat.add_zero] at e

/-- The address of argument `i`. -/
theorem addrE (i : Nat) (hi : i < S.NA) : addr L.E (4 + 4 * i) = L.B + BitVec.ofNat 64 (L.N + 4 + 4 * i) := by
  have := h.e0; have := h.e1; have := L.N_eq
  rw [addr_eq (by omega_arith), h.B_eq, show L.N + 4 + 4 * i = L.N + (4 + 4 * i) by omega_arith,
    ← Offset.add_add (L.E.setWidth 64 - BitVec.ofNat 64 L.N) L.N (4 + 4 * i), BitVec.sub_add_cancel]

/-- The `n` bytes below `F`, for `n` up to `cb`: among the calls'. -/
theorem below_F {n : Nat} (hn : n ≤ S.cb) : Region.Sub (below L.F n) L.CALLS := by
  have := h.e0; have := L.N_eq
  show Region.Sub ⟨(L.F - BitVec.ofNat 32 n).setWidth 64, n⟩ _
  rw [Taint.sub_setWidth (by rw [h.FN]; omega_arith), h.F64,
    Offset.sub_ofNat_eq (L.B + BitVec.ofNat 64 S.cb) hn, BitVec.add_sub_cancel]
  exact Offset.sub_base _ (by omega_arith)

theorem below_F_eq : below L.F S.cb = L.CALLS := by
  have := h.e0; have := L.N_eq
  show (⟨(L.F - BitVec.ofNat 32 S.cb).setWidth 64, S.cb⟩ : Region) = ⟨L.B, S.cb⟩
  rw [Taint.sub_setWidth (by rw [h.FN]; omega_arith), h.F64, BitVec.add_sub_cancel]

/-- The frame. -/
theorem FR_eq : below L.E S.FB = L.FR := by
  show (⟨L.F.setWidth 64, S.FB⟩ : Region) = _
  rw [h.F64]

/-- Regions at offsets of `B`. -/
theorem disj {d n e k : Nat} (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ L.N + 4 + 4 * S.NA)
    (he : e + k ≤ L.N + 4 + 4 * S.NA) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.B + BitVec.ofNat 64 e, k⟩ := by
  have := h.nB
  exact Offset.disjoint _ hs (by omega_arith) (by omega_arith)

omit h in
theorem sub {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) :
    Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.B + BitVec.ofNat 64 e, k⟩ := Offset.sub _ h₁ h₂

omit h in
theorem subK {d n : Nat} (h₂ : d + n ≤ L.N) : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK :=
  Offset.sub_base _ h₂

omit h in
/-- The calls' bytes, the frame, and the stack used. -/
theorem calls_stk : Region.Sub L.CALLS L.STK := Region.sub_prefix (by have := L.N_eq; omega_arith)

omit h in
theorem fr_stk : Region.Sub L.FR L.STK := Offset.sub_base _ (by have := L.N_eq; omega_arith)

theorem hi_stk : Region.Sub L.HI L.STK := Offset.sub_base _ (by have := h.s0; have := L.N_eq; omega_arith)

/-- A range of the stack used, and `W`. -/
theorem kW' {d n : Nat} (h₂ : d + n ≤ L.N) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.W :=
  h.kW.sub_left (Offset.sub_base _ h₂)

theorem calls_W : L.CALLS.Disjoint L.W := h.kW.sub_left (Region.sub_prefix (by have := L.N_eq; omega_arith))

/-- The words of the table are readable. -/
theorem inTab {t : State} (hrd : t.rd = L.rd) {o : Nat} (ho : o + 4 ≤ 24) :
    InRegions (t.rd ++ t.wr) (addr L.tb o) 4 :=
  ⟨L.TAB, List.mem_append_left _ (by rw [hrd]; exact h.tRd), by
    rw [addr_eq (by have := h.nt; omega_arith)]
    exact Offset.contains_base _ ho (by have := h.nt; omega_arith)⟩

end Lay.Ok

/-! ## Between the frame's entry and release -/

/-- The variant of the table's hash function, and the functions an indirect
call of a table's functions may reach. -/
structure Hk where
  w : HVar
  f : Fns

/-- The state between the frame's entry and release: `g` are the registers
on entry, `m₀` the memory and `y` the symbols' addresses. -/
structure Ctx {S : Sh} (K : Hk) (L : Lay S) (g : Reg → BitVec 32) (m₀ : Mem) (y : String → BitVec 32) (t : State) :
    Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.FR :: L.wr
  esp : t.gpr .esp = L.F
  saved : Spill.Saved t.mem (addr L.F) g Impl.Hkdf.X86.saved
  frame : Frame [L.W, L.STK] m₀ t.mem
  syms : t.syms = y
  args : ∀ i < S.NA, m₀.readW (L.B + BitVec.ofNat 64 (L.N + 4 + 4 * i)) 32 = L.a i
  tabOk : TabOK K.w.F K.f y
  tabMem : TabMem K.w.F y L.tb m₀
  tabD : m₀.readW (addr L.tb 16) 32 = BitVec.ofNat 32 K.w.F.H.D
  tabB : m₀.readW (addr L.tb 20) 32 = BitVec.ofNat 32 K.w.F.H.B
  fsy : ∀ n ∈ [K.w.F.hiAnyN, K.w.F.H.updN, K.w.F.hfN], y n = L.fa n

/-- A region the code may write without disturbing `Ctx`: within `W`, the
frame above the saved registers, or the calls' bytes. -/
def Safe {S : Sh} (L : Lay S) (r : Region) : Prop := Region.Sub r L.W ∨ Region.Sub r L.HI ∨ Region.Sub r L.CALLS

theorem Safe.of_sub {S : Sh} {L : Lay S} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr fun x hx => hs x (h x hx))]

theorem saved_in : ∀ p ∈ Impl.Hkdf.X86.saved, p.2 + 4 ≤ 16 := by decide

section
variable {S : Sh} {L : Lay S} (hL : L.Ok)
include hL

/-- The saved registers are apart from every safe region. -/
theorem Lay.Ok.sv_safe {r : Region} (hs : Safe L r) : Region.Disjoint L.SV r := by
  have := hL.s0; have := hL.nB; have := L.N_eq
  rcases hs with hs | hs | hs
  · exact (hL.kW' (by omega_arith)).sub_right hs
  · exact (hL.disj (.inl (Nat.le_refl _)) (by omega_arith) (by omega_arith)).sub_right hs
  · exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)).sub_right hs

theorem Safe.sub_frame {r : Region} (hs : Safe L r) : ∃ R ∈ [L.W, L.STK], Region.Sub r R := by
  rcases hs with hs | hs | hs
  · exact ⟨_, by simp, hs⟩
  · exact ⟨L.STK, by simp, fun x hx => hL.hi_stk x (hs x hx)⟩
  · exact ⟨L.STK, by simp, fun x hx => Lay.Ok.calls_stk x (hs x hx)⟩

/-- The slot of a saved register. -/
theorem sv_contains {p : Reg × Nat} (hp : p ∈ Impl.Hkdf.X86.saved) : L.SV.Contains (addr L.F p.2) 4 := by
  have := saved_in p hp; have := hL.nB; have := hL.s0; have := L.N_eq
  rw [hL.addrF (by omega_arith)]
  exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

end

namespace Ctx

variable {S : Sh} {K : Hk} {L : Lay S} {g : Reg → BitVec 32} {m₀ : Mem} {y : String → BitVec 32} {t t' : State}

/-- Code that keeps the permissions and `esp`, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx K L g m₀ y t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms) : Ctx K L g m₀ y t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp,
    hc.saved.of_frame hf (fun _ hp => sv_contains hL hp) (fun r hr => hL.sv_safe (hs r hr)),
    hc.frame.trans (hf.sub fun r hr => Safe.sub_frame hL (hs r hr)), hsy.trans hc.syms, hc.args, hc.tabOk,
    hc.tabMem, hc.tabD, hc.tabB, hc.fsy⟩

/-- Code that writes only registers but `esp`. -/
theorem regs (hL : L.Ok) (hc : Ctx K L g m₀ y t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsy : t'.syms = t.syms) : Ctx K L g m₀ y t' :=
  hc.keep hL hrd hwr hsp (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp) hsy

/-- The bytes of a region apart from `W` and the stack used are as on entry. -/
theorem bytes (hc : Ctx K L g m₀ y t) {R : Region} (hW : R.Disjoint L.W) (hK : R.Disjoint L.STK)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  hc.frame.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hW
    · exact hK) hR hi

/-- A word of a region apart from `W` and the stack used is as on entry. -/
theorem word (hc : Ctx K L g m₀ y t) {R : Region} (hW : R.Disjoint L.W) (hK : R.Disjoint L.STK) {a : Addr}
    (ha : R.Contains a 4) : t.mem.readW a 32 = m₀.readW a 32 :=
  hc.frame.readW ha (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hW
    · exact hK) (by decide)

/-- Argument `i`, as on entry. -/
theorem arg (hL : L.Ok) (hc : Ctx K L g m₀ y t) {i : Nat} (hi : i < S.NA) :
    t.mem.readW (L.B + BitVec.ofNat 64 (L.N + 4 + 4 * i)) 32 = L.a i := by
  have := hL.nB; have := L.N_eq
  rw [hc.word (R := L.ARGS) hL.aW (Offset.disjoint_base L.B (k := L.N) (d := L.N + 4) (n := 4 * S.NA)
      (by omega_arith) (by omega_arith))
    (Offset.contains L.B (e := L.N + 4) (k := 4 * S.NA) (by omega_arith) (by omega_arith) (by omega_arith))]
  exact hc.args i hi

/-- The table's words, as on entry. -/
theorem tabWord (hL : L.Ok) (hc : Ctx K L g m₀ y t) {o : Nat} (ho : o + 4 ≤ 24) :
    t.mem.readW (addr L.tb o) 32 = m₀.readW (addr L.tb o) 32 := by
  rw [addr_eq (by have := hL.nt; omega_arith)]
  exact hc.word hL.tW hL.tK (Offset.contains_base _ ho (by have := hL.nt; omega_arith))

/-- A part of the frame is readable and writable. -/
theorem inFrW (hL : L.Ok) (hc : Ctx K L g m₀ y t) {o n : Nat} (h : o + n ≤ S.FB) :
    InRegions t.wr (L.B + BitVec.ofNat 64 (S.cb + o)) n :=
  ⟨L.FR, by rw [hc.wr]; exact List.mem_cons_self, Offset.contains _ (by omega_arith) (by omega_arith)
    (by have := hL.nB; have := L.N_eq; omega_arith)⟩

theorem inFr (hL : L.Ok) (hc : Ctx K L g m₀ y t) {o n : Nat} (h : o + n ≤ S.FB) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (S.cb + o)) n :=
  let ⟨r, hr, hc'⟩ := hc.inFrW hL h
  ⟨r, List.mem_append_right _ hr, hc'⟩

/-- An argument is readable. -/
theorem inArg (hL : L.Ok) (hc : Ctx K L g m₀ y t) {i : Nat} (hi : i < S.NA) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (L.N + 4 + 4 * i)) 4 :=
  ⟨L.ARGS, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_of_mem _ hL.aWr),
    Offset.contains _ (by have := L.N_eq; omega_arith) (by omega_arith) (by have := hL.nB; have := L.N_eq; omega_arith)⟩

end Ctx

/-! ## Code that sets one register -/

/-- `u'` is `u` with only the register `d` (not `esp`, and the flags)
changed, to `v`. -/
structure Upd {S : Sh} (K : Hk) (L : Lay S) (g : Reg → BitVec 32) (m₀ : Mem) (y : String → BitVec 32) (u : State) (d : Reg)
    (v : BitVec 32) (u' : State) : Prop where
  ctx : Ctx K L g m₀ y u'
  mem : u'.mem = u.mem
  val : u'.gpr d = v
  keep : ∀ r, r ≠ d → u'.gpr r = u.gpr r
  syms : u'.syms = u.syms

variable {S : Sh} {K : Hk} {L : Lay S} {g : Reg → BitVec 32} {m₀ : Mem} {y : String → BitVec 32}

theorem Upd.of_wp {u u' : State} {d : Reg} {v : BitVec 32} (hL : L.Ok) (hc : Ctx K L g m₀ y u) (hd : d ≠ .esp)
    (h : VG.X86.Wp.Upd u u' d v) : Upd K L g m₀ y u d v u' :=
  ⟨hc.regs hL h.rd h.wr h.mem (h.other .esp (Ne.symm hd)) h.syms, h.mem, h.gpr, h.other, h.syms⟩

theorem Upd.trans {u u' u'' : State} {d : Reg} {v w : BitVec 32} (hL : L.Ok) (hd : d ≠ .esp)
    (h₁ : VG.X86.Wp.Upd u u' d v) (h₂ : VG.X86.Wp.Upd u' u'' d w) (hc : Ctx K L g m₀ y u) :
    Upd K L g m₀ y u d w u'' :=
  ⟨hc.regs hL (h₂.rd.trans h₁.rd) (h₂.wr.trans h₁.wr) (h₂.mem.trans h₁.mem)
      ((h₂.other .esp (Ne.symm hd)).trans (h₁.other .esp (Ne.symm hd))) (h₂.syms.trans h₁.syms),
    h₂.mem.trans h₁.mem, h₂.gpr, fun r hr => (h₂.other r hr).trans (h₁.other r hr), h₂.syms.trans h₁.syms⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, src`. -/
theorem wp_movS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, VG.X86.Wp.Upd s t d v → WP isa (.block is) t Q) :
    WP isa (.block (.mov d src :: is)) s Q :=
  cons (s' := s.setReg d v) (by simp only [exec, h, Option.map_some]) (k _ (VG.X86.Wp.Upd.setReg _ _ _))

/-- `add d, src`. -/
theorem wp_addS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, VG.X86.Wp.Upd s t d (s.gpr d + v) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (VG.X86.Wp.Upd.flags _ _ _ _ _ _))

end

section
variable (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {d : Reg} (hd : d ≠ .esp)
include hL hc hd

/-- `d ← esp + o`, an address in the frame. -/
theorem fr_ok (o : Nat) :
    WP isa (.block (Impl.Hkdf.X86.fr d o)) u (Upd K L g m₀ y u d (L.F + BitVec.ofNat 32 o)) := by
  refine wp_mov fun _ v₁ => wp_addi fun u₂ v₂ => WP.block_nil ?_
  rw [v₁.gpr, hc.esp] at v₂
  exact Upd.trans hL hd v₁ v₂ hc

/-- `d ← v`. -/
theorem movi_ok (v : BitVec 32) : WP isa (.block [.mov d (.imm v)]) u (Upd K L g m₀ y u d v) :=
  wp_movi fun _ v₁ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-- `d ← r`. -/
theorem movr_ok (r : Reg) : WP isa (.block [.mov d (.reg r)]) u (Upd K L g m₀ y u d (u.gpr r)) :=
  wp_mov fun _ v₁ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-- `d ← d + v`. -/
theorem addI_ok (v : BitVec 32) : WP isa (.block [.alu .add d (.imm v)]) u (Upd K L g m₀ y u d (u.gpr d + v)) :=
  wp_addi fun _ v₁ => WP.block_nil (Upd.of_wp hL hc hd v₁)

omit hd in
/-- `argM` reads argument `i`. -/
theorem readArg {i : Nat} (hi : i < S.NA) : readSrc u (Impl.Hkdf.X86.argM S.FB i) = some (L.a i) := by
  have e : addr L.F (S.FB + 4 + 4 * i) = L.B + BitVec.ofNat 64 (L.N + 4 + 4 * i) := by
    have := L.N_eq
    rw [hL.addrF (by omega_arith), show S.cb + (S.FB + 4 + 4 * i) = L.N + 4 + 4 * i by omega_arith]
  rw [Impl.Hkdf.X86.argM, Impl.Hkdf.X86.sp, readSrc_mem hc.esp (by rw [e]; exact hc.inArg hL hi), e, hc.arg hL hi]

/-- `d ← argument i`. -/
theorem arg_ok {i : Nat} (hi : i < S.NA) :
    WP isa (.block [.mov d (Impl.Hkdf.X86.argM S.FB i)]) u (Upd K L g m₀ y u d (L.a i)) :=
  wp_movS (readArg hL hc hi) fun _ v₁ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-- `d ← d + argument i`. -/
theorem addA_ok {i : Nat} (hi : i < S.NA) :
    WP isa (.block [.alu .add d (Impl.Hkdf.X86.argM S.FB i)]) u (Upd K L g m₀ y u d (u.gpr d + L.a i)) :=
  wp_addS (readArg hL hc hi) fun _ v₁ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-- `d ← [esp + o]`, a word of the frame. -/
theorem ldF_ok {o : Nat} (ho : o + 4 ≤ S.FB) :
    WP isa (.block [.mov d (.mem (Impl.Hkdf.X86.sp o))]) u
      (Upd K L g m₀ y u d (u.mem.readW (L.B + BitVec.ofNat 64 (S.cb + o)) 32)) := by
  obtain e := hL.addrF (o := o) (by omega_arith)
  refine wp_ldm hc.esp (by rw [e]; exact hc.inFr hL ho) fun u' v => WP.block_nil ?_
  rw [e] at v
  exact Upd.of_wp hL hc hd v

/-- `d ← d + [esp + o]`, a word of the frame. -/
theorem addF_ok {o : Nat} (ho : o + 4 ≤ S.FB) :
    WP isa (.block [.alu .add d (.mem (Impl.Hkdf.X86.sp o))]) u
      (Upd K L g m₀ y u d (u.gpr d + u.mem.readW (L.B + BitVec.ofNat 64 (S.cb + o)) 32)) := by
  obtain e := hL.addrF (o := o) (by omega_arith)
  refine wp_addm hc.esp (by rw [e]; exact hc.inFr hL ho) fun u' v => WP.block_nil ?_
  rw [e] at v
  exact Upd.of_wp hL hc hd v

end

/-- `[esp + o] ← r`, a word of the frame above the saved registers. -/
theorem stF_ok (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) (r : Reg) {o : Nat} (h₁ : 16 ≤ o)
    (ho : o + 4 ≤ S.FB) :
    WP isa (.block [.store (Impl.Hkdf.X86.sp o) r]) u fun u' => Ctx K L g m₀ y u' ∧
      u'.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (S.cb + o)) (u.gpr r) ∧ u'.gpr = u.gpr ∧ u'.syms = u.syms := by
  obtain e := hL.addrF (o := o) (by omega_arith)
  refine wp_stm hc.esp (by rw [e]; exact hc.inFrW hL ho) fun u' v => WP.block_nil ?_
  rw [e] at v
  refine ⟨hc.keep hL v.rd v.wr (by rw [v.gpr]) (ws := [⟨L.B + BitVec.ofNat 64 (S.cb + o), 4⟩]) ?_ ?_ v.syms,
    v.mem, v.gpr, v.syms⟩
  · rw [v.mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  · intro q hq
    simp only [List.mem_singleton] at hq; subst hq
    exact .inr (.inl (Lay.Ok.sub (by omega_arith) (by have := hL.s0; omega_arith)))

end VG.Proof.Hkdf.X86
