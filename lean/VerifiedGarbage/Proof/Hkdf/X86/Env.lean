module

public import VerifiedGarbage.Proof.HmacTable.X86
public import VerifiedGarbage.Impl.Hkdf.X86
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyCT
public import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Hkdf.X86
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

/-- The stack used below the return address. -/
abbrev Sh.N (S : Sh) : Nat := S.FB + S.cb
theorem Sh.N_eq (S : Sh) : S.N = S.FB + S.cb := rfl

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

/-- `esp` in the frame's body. -/
abbrev F : BitVec 32 := L.E - BitVec.ofNat 32 S.FB
/-- The lowest byte of the stack used. -/
abbrev B : Addr := (L.E - BitVec.ofNat 32 S.N).setWidth 64
/-- The table. -/
abbrev tb : BitVec 32 := L.a S.ti

abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 S.cb, S.FB⟩
abbrev CALLS : Region := ⟨L.B, S.cb⟩
abbrev STK : Region := ⟨L.B, S.N⟩
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 S.N, 4⟩
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 (S.N + 4), 4 * S.NA⟩
abbrev TAB : Region := ⟨L.tb.setWidth 64, 24⟩
/-- The frame above the saved registers. -/
abbrev HI : Region := ⟨L.B + BitVec.ofNat 64 (S.cb + 16), S.FB - 16⟩
/-- The saved registers. -/
abbrev SV : Region := ⟨L.B + BitVec.ofNat 64 S.cb, 16⟩

/-- What the contracts say of where the buffers and the stack are, and what
the frame's shape needs. -/
structure Ok : Prop where
  e0 : S.N ≤ L.E.toNat
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

theorem BN : L.B.toNat = L.E.toNat - S.N := by
  have := h.e0; have := S.N_eq
  simp only [Lay.B, BitVec.toNat_setWidth]
  rw [sub_toNat (by omega_arith)]; have := L.E.isLt; omega_arith

theorem nB : L.B.toNat + S.N + 4 + 4 * S.NA ≤ 2 ^ 32 := by
  have := S.N_eq; have := h.e0; have := h.e1; rw [h.BN]; omega_arith

theorem FN : L.F.toNat = L.E.toNat - S.FB := sub_toNat (by have := h.e0; have := S.N_eq; omega_arith)

theorem B_eq : L.B = L.E.setWidth 64 - BitVec.ofNat 64 S.N := Taint.sub_setWidth h.e0

/-- `[F + o]`, for `o` in the frame or the arguments above it. -/
theorem addrF {o : Nat} (ho : o ≤ S.FB + 4 * S.NA) : addr L.F o = L.B + BitVec.ofNat 64 (S.cb + o) := by
  have := h.e0; have := h.e1; have := S.N_eq
  rw [addr_eq (by rw [h.FN]; omega_arith), Lay.F, Taint.sub_setWidth (by omega_arith), h.B_eq,
    Offset.sub_ofNat_eq _ (show S.FB ≤ S.N by omega_arith), show S.N - S.FB = S.cb by omega_arith, Offset.add_add]

theorem F64 : L.F.setWidth 64 = L.B + BitVec.ofNat 64 S.cb := by
  have e := h.addrF (o := 0) (by omega_arith)
  rwa [addr, BitVec.add_zero, Nat.add_zero] at e

/-- The address of argument `i`. -/
theorem addrE (i : Nat) (hi : i < S.NA) : addr L.E (4 + 4 * i) = L.B + BitVec.ofNat 64 (S.N + 4 + 4 * i) := by
  have := h.e0; have := h.e1; have := S.N_eq
  rw [addr_eq (by omega_arith), h.B_eq, show S.N + 4 + 4 * i = S.N + (4 + 4 * i) by omega_arith,
    ← Offset.add_add (L.E.setWidth 64 - BitVec.ofNat 64 S.N) S.N (4 + 4 * i), BitVec.sub_add_cancel]

/-- The `n` bytes below `F`, for `n` up to `cb`: among the calls'. -/
theorem below_F {n : Nat} (hn : n ≤ S.cb) : Region.Sub (below L.F n) L.CALLS := by
  have := h.e0; have := S.N_eq
  show Region.Sub ⟨(L.F - BitVec.ofNat 32 n).setWidth 64, n⟩ _
  rw [Taint.sub_setWidth (by rw [h.FN]; omega_arith), h.F64,
    Offset.sub_ofNat_eq (L.B + BitVec.ofNat 64 S.cb) hn, BitVec.add_sub_cancel]
  exact Offset.sub_base _ (by omega_arith)

theorem below_F_eq : below L.F S.cb = L.CALLS := by
  have := h.e0; have := S.N_eq
  show (⟨(L.F - BitVec.ofNat 32 S.cb).setWidth 64, S.cb⟩ : Region) = ⟨L.B, S.cb⟩
  rw [Taint.sub_setWidth (by rw [h.FN]; omega_arith), h.F64, BitVec.add_sub_cancel]

/-- The frame. -/
theorem FR_eq : below L.E S.FB = L.FR := by
  show (⟨L.F.setWidth 64, S.FB⟩ : Region) = _
  rw [h.F64]

/-- Regions at offsets of `B`. -/
theorem disj {d n e k : Nat} (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ S.N + 4 + 4 * S.NA)
    (he : e + k ≤ S.N + 4 + 4 * S.NA) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.B + BitVec.ofNat 64 e, k⟩ := by
  have := h.nB
  exact Offset.disjoint _ hs (by omega_arith) (by omega_arith)

omit h in
theorem sub {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) :
    Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.B + BitVec.ofNat 64 e, k⟩ := Offset.sub _ h₁ h₂

omit h in
theorem subK {d n : Nat} (h₂ : d + n ≤ S.N) : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK :=
  Offset.sub_base _ h₂

omit h in
/-- The calls' bytes, the frame, and the stack used. -/
theorem calls_stk : Region.Sub L.CALLS L.STK := Region.sub_prefix (by have := S.N_eq; omega_arith)

omit h in
theorem fr_stk : Region.Sub L.FR L.STK := Offset.sub_base _ (by have := S.N_eq; omega_arith)

theorem hi_stk : Region.Sub L.HI L.STK := Offset.sub_base _ (by have := h.s0; have := S.N_eq; omega_arith)

/-- A range of the stack used, and `W`. -/
theorem kW' {d n : Nat} (h₂ : d + n ≤ S.N) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.W :=
  h.kW.sub_left (Offset.sub_base _ h₂)

theorem calls_W : L.CALLS.Disjoint L.W := h.kW.sub_left (Region.sub_prefix (by have := S.N_eq; omega_arith))

/-- The words of the table are readable. -/
theorem inTab {t : State} (hrd : t.rd = L.rd) {o : Nat} (ho : o + 4 ≤ 24) :
    InRegions (t.rd ++ t.wr) (addr L.tb o) 4 :=
  ⟨L.TAB, List.mem_append_left _ (by rw [hrd]; exact h.tRd), by
    rw [addr_eq (by have := h.nt; omega_arith)]
    exact Offset.contains_base _ ho (by have := h.nt; omega_arith)⟩

/-! ## Parts of the frame, as the code computes their addresses -/

theorem frv {o : Nat} (ho : o ≤ S.FB + 4 * S.NA) :
    (L.F + BitVec.ofNat 32 o).setWidth 64 = L.B + BitVec.ofNat 64 (S.cb + o) := h.addrF ho

theorem frN {o : Nat} (ho : o ≤ S.FB + 4 * S.NA) : (L.F + BitVec.ofNat 32 o).toNat = L.F.toNat + o := by
  have := h.e0; have := h.e1; have := S.N_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), h.FN,
    Nat.mod_eq_of_lt (by omega_arith)]

/-- A part of the frame, at an offset of the frame's base. -/
theorem frBase {o : Nat} (ho : o ≤ S.FB) :
    (L.F + BitVec.ofNat 32 o).setWidth 64 = L.FR.base + BitVec.ofNat 64 o := by
  rw [h.frv (by omega_arith), Offset.add_add]

/-- Two parts of the frame that do not overlap. -/
theorem fr_disj {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o) (h₁ : o + n ≤ S.FB) (h₂ : o' + n' ≤ S.FB) :
    Region.Disjoint ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ ⟨(L.F + BitVec.ofNat 32 o').setWidth 64, n'⟩ := by
  have := S.N_eq
  rw [h.frv (by omega_arith), h.frv (by omega_arith)]
  exact h.disj (by omega_arith) (by omega_arith) (by omega_arith)

/-- A part of the frame, within the stack used. -/
theorem fr_sub {o n : Nat} (h₁ : o + n ≤ S.FB) :
    Region.Sub ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ L.STK := by
  have := S.N_eq
  rw [h.frv (by omega_arith)]; exact Offset.sub_base _ (by omega_arith)

/-- A part of the frame above the saved registers. -/
theorem fr_hi {o n : Nat} (h₀ : 16 ≤ o) (h₁ : o + n ≤ S.FB) :
    Region.Sub ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ L.HI := by
  rw [h.frv (by omega_arith)]; exact Offset.sub _ (by omega_arith) (by omega_arith)

/-- The calls' bytes, and a part of the frame. -/
theorem calls_fr {o n : Nat} (h₁ : o + n ≤ S.FB) :
    Region.Disjoint L.CALLS ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ := by
  have := S.N_eq; have := h.nB
  rw [h.frv (by omega_arith)]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)

/-- A part of the frame, and `W`. -/
theorem fr_W {o n : Nat} (h₁ : o + n ≤ S.FB) : Region.Disjoint ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ L.W :=
  h.kW.sub_left (h.fr_sub h₁)

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
  args : ∀ i < S.NA, m₀.readW (L.B + BitVec.ofNat 64 (S.N + 4 + 4 * i)) 32 = L.a i
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
  have := hL.s0; have := hL.nB; have := S.N_eq
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
  have := saved_in p hp; have := hL.nB; have := hL.s0; have := S.N_eq
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
    t.mem.readW (L.B + BitVec.ofNat 64 (S.N + 4 + 4 * i)) 32 = L.a i := by
  have := hL.nB; have := S.N_eq
  rw [hc.word (R := L.ARGS) hL.aW (Offset.disjoint_base L.B (k := S.N) (d := S.N + 4) (n := 4 * S.NA)
      (by omega_arith) (by omega_arith))
    (Offset.contains L.B (e := S.N + 4) (k := 4 * S.NA) (by omega_arith) (by omega_arith) (by omega_arith))]
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
    (by have := hL.nB; have := S.N_eq; omega_arith)⟩

theorem inFr (hL : L.Ok) (hc : Ctx K L g m₀ y t) {o n : Nat} (h : o + n ≤ S.FB) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (S.cb + o)) n :=
  let ⟨r, hr, hc'⟩ := hc.inFrW hL h
  ⟨r, List.mem_append_right _ hr, hc'⟩

/-- An argument is readable. -/
theorem inArg (hL : L.Ok) (hc : Ctx K L g m₀ y t) {i : Nat} (hi : i < S.NA) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (S.N + 4 + 4 * i)) 4 :=
  ⟨L.ARGS, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_of_mem _ hL.aWr),
    Offset.contains _ (by have := S.N_eq; omega_arith) (by omega_arith) (by have := hL.nB; have := S.N_eq; omega_arith)⟩

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
  have e : addr L.F (S.FB + 4 + 4 * i) = L.B + BitVec.ofNat 64 (S.N + 4 + 4 * i) := by
    have := S.N_eq
    rw [hL.addrF (by omega_arith), show S.cb + (S.FB + 4 + 4 * i) = S.N + 4 + 4 * i by omega_arith]
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

/-- `d ← [r + o]`, a word of the table, which `r` holds. -/
theorem tabld_ok (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {d r : Reg} (hd : d ≠ .esp)
    (hr : u.gpr r = L.tb) {o : Nat} (ho : o + 4 ≤ 24) :
    WP isa (.block [.mov d (.mem (Impl.Pbkdf2.Stream.X86.at_ r o))]) u
      (Upd K L g m₀ y u d (m₀.readW (addr L.tb o) 32)) :=
  wp_ldm hr (hL.inTab hc.rd ho) fun _ v => WP.block_nil (by
    rw [hc.tabWord hL ho] at v; exact Upd.of_wp hL hc hd v)

/-- `d ← d + r`. -/
theorem addR_ok (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {d : Reg} (hd : d ≠ .esp) (r : Reg) :
    WP isa (.block [.alu .add d (.reg r)]) u (Upd K L g m₀ y u d (u.gpr d + u.gpr r)) :=
  wp_add fun _ v₁ _ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-- `d ← d - r`, and ZF. -/
theorem subR_ok (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {d : Reg} (hd : d ≠ .esp) (r : Reg) :
    WP isa (.block [.alu .sub d (.reg r)]) u fun u' => Upd K L g m₀ y u d (u.gpr d - u.gpr r) u' :=
  wp_sub fun _ v₁ _ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-- `test d, d`: ZF, whether `d` is zero. -/
theorem test_ok (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) (d : Reg) :
    WP isa (.block [.alu .test d (.reg d)]) u fun u' => Ctx K L g m₀ y u' ∧ u'.gpr = u.gpr ∧ u'.mem = u.mem ∧
      u'.syms = u.syms ∧ u'.zf = some (u.gpr d == 0) :=
  wp_test fun u' f hz => WP.block_nil ⟨hc.regs hL f.rd f.wr f.mem (by rw [f.gpr]) f.syms, f.gpr, f.mem, f.syms,
    by rw [hz, BitVec.and_self]⟩

/-- `cmp d, r`: CF, whether `d < r`. -/
theorem cmp_ok (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) (d r : Reg) :
    WP isa (.block [.alu .cmp d (.reg r)]) u fun u' => Ctx K L g m₀ y u' ∧ u'.gpr = u.gpr ∧ u'.mem = u.mem ∧
      u'.syms = u.syms ∧ u'.cf = some (decide ((u.gpr d).toNat < (u.gpr r).toNat)) :=
  wp_cmp fun u' f hc' _ => WP.block_nil ⟨hc.regs hL f.rd f.wr f.mem (by rw [f.gpr]) f.syms, f.gpr, f.mem, f.syms,
    hc'⟩

/-- `[esp + o] ← r`, a byte of the frame above the saved registers. -/
theorem st8F_ok (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) (r : Reg8) {o : Nat} (h₁ : 16 ≤ o)
    (ho : o + 1 ≤ S.FB) :
    WP isa (.block [.store8 (Impl.Hkdf.X86.sp o) r]) u fun u' => Ctx K L g m₀ y u' ∧
      u'.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (S.cb + o)) ((u.gpr r.reg).setWidth 8) ∧ u'.gpr = u.gpr ∧
      u'.syms = u.syms := by
  obtain e := hL.addrF (o := o) (by omega_arith)
  have hin := hc.inFrW hL ho
  refine cons (s' := { u with mem := u.mem.writeW (L.B + BitVec.ofNat 64 (S.cb + o)) ((u.gpr r.reg).setWidth 8) })
    (by simp only [exec, State.store8, Impl.Hkdf.X86.sp, ea_mk, hc.esp, e, hin, ↓reduceIte]) (WP.block_nil ?_)
  refine ⟨hc.keep hL rfl rfl rfl (ws := [⟨L.B + BitVec.ofNat 64 (S.cb + o), 1⟩]) ?_ ?_ rfl, rfl, rfl, rfl⟩
  · exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  · intro q hq
    simp only [List.mem_singleton] at hq; subst hq
    exact .inr (.inl (Lay.Ok.sub (by omega_arith) (by have := hL.s0; omega_arith)))

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

/-! ## The frame's entry and release -/

/-- What the contract says of a call on entry, with the layout `L`. -/
structure Entry (K : Hk) (L : Lay S) (s : State) : Prop where
  esp : s.gpr .esp = L.E
  rd : s.rd = L.rd
  wr : s.wr = L.wr
  args : ∀ i < S.NA, arg s i = L.a i
  tabOk : TabOK K.w.F K.f s.syms
  tabMem : TabMem K.w.F s.syms L.tb s.mem
  tabD : s.mem.readW (addr L.tb 16) 32 = BitVec.ofNat 32 K.w.F.H.D
  tabB : s.mem.readW (addr L.tb 20) 32 = BitVec.ofNat 32 K.w.F.H.B
  fsy : ∀ n ∈ [K.w.F.hiAnyN, K.w.F.H.updN, K.w.F.hfN], s.syms n = L.fa n

theorem saved_fits : Spill.Fits 16 Impl.Hkdf.X86.saved := by decide

theorem saved_ne : ∀ p ∈ Impl.Hkdf.X86.saved, p.1 ≠ .esp := by decide

/-- Our caller's registers saved, and the table in `eax`: `Ctx`. -/
theorem entry_ok (hL : L.Ok) {s : State} (he : Entry K L s) :
    WP isa (.block (Impl.Hkdf.X86.entry S.FB S.ti)) (allocFrame S.FB s)
      fun t => Ctx K L s.gpr s.mem s.syms t ∧ t.gpr .eax = L.tb := by
  have hesp : (allocFrame S.FB s).gpr .esp = L.F := by rw [allocFrame_esp, he.esp]
  have hwr : (allocFrame S.FB s).wr = L.FR :: L.wr := by
    rw [allocFrame_wr, he.esp, he.wr]
    show (⟨L.F.setWidth 64, S.FB⟩ : Region) :: L.wr = _
    rw [hL.F64]
  have hF : L.F.toNat + 16 ≤ 2 ^ 32 := by have := hL.e1; have := hL.s0; rw [hL.FN]; omega_arith
  rw [Impl.Hkdf.X86.entry, show Impl.Hkdf.X86.saveRegs = Spill.saveCode .esp Impl.Hkdf.X86.saved from rfl]
  refine Spill.save_ok (b := .esp) Impl.Hkdf.X86.saved (fun p hp => ?_) fun t u => ?_
  · rw [hesp, hwr]
    exact ⟨L.FR, List.mem_cons_self, by
      have := saved_in p hp; have := hL.nB; have := S.N_eq; have := hL.s0
      rw [hL.addrF (by omega_arith)]
      exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
  have hc : Ctx K L s.gpr s.mem s.syms t :=
    { rd := by rw [u.rd, allocFrame_rd, he.rd]
      wr := by rw [u.wr, hwr]
      esp := by rw [u.gpr, hesp]
      saved := by
        rw [u.mem, allocFrame_mem, hesp]
        exact (Spill.saveMem_saved_addr s.mem _ saved_fits hF).congr (fun _ _ => rfl)
          fun p hp => allocFrame_gpr _ _ (saved_ne p hp)
      frame := by
        rw [u.mem, allocFrame_mem, hesp]
        exact Spill.saveMem_frame (R := L.STK) (by simp) _ _ _ _ fun p hp => by
          have := saved_in p hp; have := hL.nB; have := S.N_eq; have := hL.s0
          rw [hL.addrF (by omega_arith)]
          exact Offset.contains_base _ (by omega_arith) (by omega_arith)
      syms := by rw [u.syms]; rfl
      args := fun i hi => by rw [← hL.addrE i hi, ← he.esp, ← he.args i hi]; rfl
      tabOk := he.tabOk
      tabMem := he.tabMem
      tabD := he.tabD
      tabB := he.tabB
      fsy := he.fsy }
  exact WP.mono (arg_ok hL hc (d := .eax) (by decide) hL.ti) fun t' h => ⟨h.ctx, h.val⟩

/-- The frame: its body, which never writes `esp`, runs from the state after
the allocation, and ends in `Ctx` with our caller's registers restored; on
return, `abiPreserved` holds, and the memory is the body's but in the frame. -/
theorem frame_ok (hL : L.Ok) {s : State} (he : Entry K L s) {body : Prog isa} (hsp : NoSp body)
    {R : State → Prop}
    (hb : WP isa body (allocFrame S.FB s) fun u => Ctx K L s.gpr s.mem s.syms u ∧
      (∀ p ∈ Impl.Hkdf.X86.saved, u.gpr p.1 = s.gpr p.1) ∧ R u) :
    WP isa (.frame (.alloc S.FB) body (.free S.FB)) s fun s' => abiPreserved s s' ∧
      ∃ u, R u ∧ Frame [L.FR] u.mem s'.mem := by
  have := hL.e0; have := hL.s0; have := S.N_eq
  refine WP.frameAlloc (by omega_arith) hL.s1 hL.s2 (by rw [he.esp]; omega_arith) hsp
    (WP.mono hb fun u ⟨hc, hs, hr⟩ m v hm => ?_)
  rw [he.esp, hL.FR_eq] at hm
  refine ⟨⟨fun r hr => ?_, ?_⟩, u, hr, hm⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show ({ freed S.FB u with mem := m, unknowns := v } : State).gpr .ebx = u.gpr .ebx from
        freed_gpr S.FB u (q := .ebx) (by decide)]; exact hs (.ebx, 0) (by decide)
    · rw [show ({ freed S.FB u with mem := m, unknowns := v } : State).gpr .esi = u.gpr .esi from
        freed_gpr S.FB u (q := .esi) (by decide)]; exact hs (.esi, 4) (by decide)
    · rw [show ({ freed S.FB u with mem := m, unknowns := v } : State).gpr .edi = u.gpr .edi from
        freed_gpr S.FB u (q := .edi) (by decide)]; exact hs (.edi, 8) (by decide)
    · rw [show ({ freed S.FB u with mem := m, unknowns := v } : State).gpr .ebp = u.gpr .ebp from
        freed_gpr S.FB u (q := .ebp) (by decide)]; exact hs (.ebp, 12) (by decide)
    · show (freed S.FB u).gpr .esp = s.gpr .esp
      rw [freed_esp, hc.esp, he.esp, BitVec.sub_add_cancel]
  · have hret : (s.gpr .esp).setWidth 64 = L.B + BitVec.ofNat 64 S.N := by rw [he.esp, hL.B_eq, BitVec.sub_add_cancel]
    show m.readW _ 32 = _
    have hnb := hL.nB
    rw [hret, hm.readW (r := L.RET) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.disj (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
    refine hc.frame.readW (r := L.RET) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.rW
    · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)

/-- Our caller's registers back: `Ctx` kept, and the registers restored. -/
theorem restore_ok (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) :
    WP isa (.block Impl.Hkdf.X86.restoreRegs) u fun u' => Ctx K L g m₀ y u' ∧
      (∀ p ∈ Impl.Hkdf.X86.saved, u'.gpr p.1 = g p.1) ∧ u'.mem = u.mem := by
  rw [show Impl.Hkdf.X86.restoreRegs = Spill.restoreCode .esp Impl.Hkdf.X86.saved ++ [] from rfl]
  refine WP.mono_syms (Spill.restore_ok (b := .esp) Impl.Hkdf.X86.saved saved_ne (fun p hp => ?_)
    (by rw [hc.esp]; exact hc.saved) fun u' r => WP.block_nil r) fun u' r hsy => ?_
  · rw [hc.esp]
    have := saved_in p hp; have := hL.nB; have := S.N_eq; have := hL.s0
    rw [hL.addrF (by omega_arith)]
    exact hc.inFr hL (by omega_arith)
  · exact ⟨hc.regs hL r.rd r.wr r.mem (r.other _ (by decide)) hsy, r.gpr, r.mem⟩

/-! ## The indirect calls of the table's functions -/

section
variable {S : Sh} {K : Hk} {L : Lay S} {g : Reg → BitVec 32} {m₀ : Mem} {y : String → BitVec 32}

/-- The indirect call of the table's function `j`, at the address its word
`j` holds, of `n`, in a frame pushing `rs`: only `ebx` changes before the
frame. -/
theorem tcall_ok (hL : L.Ok) {t : State} (hc : Ctx K L g m₀ y t) {j : Nat} (hj : 4 * j + 4 ≤ 24)
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)} {rs : List Reg}
    (hw : m₀.readW (addr L.tb (4 * j)) 32 = y n)
    (hf : ts.find? (fun q => (y q.1).setWidth 64 == (y n).setWidth 64) = some (n, c))
    {Q : State → Prop}
    (h : ∀ t', Ctx K L g m₀ y t' → t'.mem = t.mem → (∀ r, r ≠ .ebx → t'.gpr r = t.gpr r) → t'.syms = t.syms →
      WP isa (.frame (.push rs) (.call n c) (.pop .eax rs.length)) t' Q) :
    WP isa (Impl.Hkdf.X86.tcall S.FB S.ti j ts rs) t Q := by
  unfold Impl.Hkdf.X86.tcall
  refine WP.seq (WP.mono (arg_ok hL hc (d := .ebx) (by decide) hL.ti) fun t₁ h₁ => ?_)
  refine WP.seq ?_
  have hb : t₁.gpr .ebx = L.tb := h₁.val
  refine wp_ldm hb (hL.inTab (h₁.ctx.rd) hj) fun t₂ v₂ => WP.block_nil ?_
  obtain u₂ := Upd.of_wp hL h₁.ctx (d := .ebx) (by decide) v₂
  obtain hsy : t₂.syms = t.syms := u₂.syms.trans h₁.syms
  obtain hm : t₂.mem = t.mem := u₂.mem.trans h₁.mem
  obtain hk : ∀ r, r ≠ .ebx → t₂.gpr r = t.gpr r := fun r hr => (u₂.keep r hr).trans (h₁.keep r hr)
  obtain hv : t₂.gpr .ebx = t.syms n := by rw [u₂.val, h₁.ctx.tabWord hL hj, hw, hc.syms]
  rw [← hc.syms] at hf
  refine WP.frame_icalls_of_call (fun u hp => ⟨_, rfl, ?_⟩) (h t₂ u₂.ctx hm hk hsy)
  obtain ⟨-, -, -, rfl⟩ := push_some hp
  show icallTarget isa (pushed rs t₂) (((pushed rs t₂).gpr .ebx).setWidth 64) ts = some (n, c)
  rw [pushed_gpr _ _ (by decide), hv, icallTarget_congr (s₂ := t) fun q _ => by
    show ((pushed rs t₂).syms q.1).setWidth 64 = (t.syms q.1).setWidth 64
    rw [show (pushed rs t₂).syms = t₂.syms from pushRegs_syms t₂ rs, hsy]]
  exact hf

/-! ## HMAC's functions -/

open VG.Proof.Pbkdf2.Whole.X86 (HfArgs hf_frame)
open VG.Proof.Pbkdf2.Whole.X86.Any (AnyArgs any_frame)
open VG.Proof.Pbkdf2.Stream.X86 (UpdArgs upd_frame)

/-- The bytes below `esp` a call uses, for `n` up to `cb`, are safe. -/
theorem safe_below (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {n : Nat} (hn : n ≤ S.cb) :
    Safe L (below (u.gpr .esp) n) := by
  rw [hc.esp]; exact .inr (.inr (hL.below_F hn))

/-- The bytes below `esp` a call uses, for `n` up to `cb`, are among the calls'. -/
theorem sub_below (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {n : Nat} (hn : n ≤ S.cb) :
    Region.Sub (below (u.gpr .esp) n) L.CALLS := by
  rw [hc.esp]; exact hL.below_F hn

/-- HMAC's `init` for a key of any length, through its contract: it keeps
`Ctx` and the callee-saved registers, changes only its states and working
space, which are safe, and the calls' bytes, and leaves the states of the
key. -/
theorem init_wp (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {inn out k sc : BitVec 32} {kl : Nat}
    (a : AnyArgs K.w.ok.hH.SH (K.w.F.W + K.w.F.H.S) u inn out k sc kl) (hcb : 100 ≤ S.cb)
    (hs : ∀ r ∈ [(⟨inn.setWidth 64, K.w.ok.hH.SH.stateBytes⟩ : Region), ⟨out.setWidth 64, K.w.ok.hH.SH.stateBytes⟩,
      ⟨sc.setWidth 64, (K.w.F.W + K.w.F.H.S) * 8⟩], Safe L r) :
    WP isa (.frame (.push Proof.Pbkdf2.Whole.X86.hi5) (.call K.w.F.hiAnyN K.w.F.hmacInitAny)
      (.pop .eax Proof.Pbkdf2.Whole.X86.hi5.length)) u fun u' => Ctx K L g m₀ y u' ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      Frame ([(⟨inn.setWidth 64, K.w.ok.hH.SH.stateBytes⟩ : Region), ⟨out.setWidth 64, K.w.ok.hH.SH.stateBytes⟩,
        ⟨sc.setWidth 64, (K.w.F.W + K.w.F.H.S) * 8⟩] ++ [L.CALLS]) u.mem u'.mem ∧
      K.w.ok.hH.SH.Repr u'.mem (inn.setWidth 64)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey K.w.ok.hH.SH.H (Spec.Sha256.bytesAt u.mem (k.setWidth 64) kl))
          Spec.Hmac.ipad) ∧
      K.w.ok.hH.SH.Repr u'.mem (out.setWidth 64)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey K.w.ok.hH.SH.H (Spec.Sha256.bytesAt u.mem (k.setWidth 64) kl))
          Spec.Hmac.opad) := by
  refine WP.of_syms (any_frame (fun m m' p q msg hb => K.w.ok.hH.repr m m' p q msg (fun i hi => hb i (by
      rw [K.w.ok.hH.hS]; exact hi))) K.w.any K.w.anySp K.w.anySU a fun v hrd hwr hcs hf hi ho => ?_)
  intro hsy
  have hb : Region.Sub (Proof.Pbkdf2.Whole.X86.Any.stk100 u) L.CALLS := sub_below hL hc hcb
  refine ⟨hc.keep hL hrd hwr (hcs .esp (by decide)) hf (fun r hr => ?_) hsy, hcs,
    hf.sub fun r hr => ?_, hi, ho⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact safe_below hL hc hcb
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.CALLS, by simp, hb⟩

/-- The streaming `update`, through its contract. -/
theorem upd_wp (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {st d sc c : BitVec 32} {len : Nat}
    (a : UpdArgs K.w.ok.hH u .esi .edi st d sc c len)
    (hs : ∀ r ∈ [(⟨st.setWidth 64, K.w.F.H.S⟩ : Region), ⟨sc.setWidth 64, K.w.ok.hH.Wb⟩], Safe L r) :
    WP isa (.frame (.push (Proof.Pbkdf2.Stream.X86.upd6 .esi .edi)) (.call K.w.F.H.updN K.w.F.H.updC)
      (.pop .eax (Proof.Pbkdf2.Stream.X86.upd6 .esi .edi).length)) u fun u' => Ctx K L g m₀ y u' ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      Frame ([(⟨st.setWidth 64, K.w.F.H.S⟩ : Region), ⟨sc.setWidth 64, K.w.ok.hH.Wb⟩] ++ [L.CALLS]) u.mem u'.mem ∧
      (∀ m, K.w.ok.hH.SH.Repr u.mem (st.setWidth 64) m → (0 : BitVec 32) ++ c = BitVec.ofNat 64 m.length →
        K.w.ok.hH.SH.Repr u'.mem (st.setWidth 64) (m ++ Spec.Sha256.bytesAt u.mem (d.setWidth 64) len)) := by
  refine WP.of_syms (upd_frame K.w.ok.hH a fun v af hr => ?_)
  intro hsy
  have hb : Region.Sub (Proof.Pbkdf2.Stream.X86.stk u) L.CALLS := sub_below hL hc (by have := hL.c76; omega_arith)
  refine ⟨hc.keep hL af.rd af.wr (af.cs .esp (by decide)) af.frame (fun r hr => ?_) hsy, af.cs,
    af.frame.sub fun r hr => ?_, hr⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact safe_below hL hc (by have := hL.c76; omega_arith)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.CALLS, by simp, hb⟩

/-- HMAC's `finalize`, through its contract. -/
theorem fin_wp (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {inn ou lo hi o sc : BitVec 32}
    (a : HfArgs K.w.ok.hH.SH K.w.ok.Wf u inn ou lo hi o sc)
    (hs : ∀ r ∈ [(⟨inn.setWidth 64, K.w.ok.hH.SH.stateBytes⟩ : Region), ⟨o.setWidth 64, K.w.ok.hH.SH.digestBytes⟩,
      ⟨sc.setWidth 64, K.w.ok.Wf * 8⟩], Safe L r) :
    WP isa (.frame (.push Proof.Pbkdf2.Whole.X86.hf6) (.call K.w.F.hfN K.w.F.hfC)
      (.pop .eax Proof.Pbkdf2.Whole.X86.hf6.length)) u fun u' => Ctx K L g m₀ y u' ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      Frame ([(⟨inn.setWidth 64, K.w.ok.hH.SH.stateBytes⟩ : Region), ⟨o.setWidth 64, K.w.ok.hH.SH.digestBytes⟩,
        ⟨sc.setWidth 64, K.w.ok.Wf * 8⟩] ++ [L.CALLS]) u.mem u'.mem ∧
      (∀ k0 text, k0.length = K.w.ok.hH.SH.H.blockSize → k0.length + text.length < 2 ^ 64 →
        K.w.ok.hH.SH.Repr u.mem (inn.setWidth 64) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text) →
        hi ++ lo = BitVec.ofNat 64 (K.w.ok.hH.SH.H.blockSize + text.length) →
        K.w.ok.hH.SH.Repr u.mem (ou.setWidth 64) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) →
        Spec.Sha256.bytesAt u'.mem (o.setWidth 64) K.w.ok.hH.SH.digestBytes =
          Spec.Hmac.hmacBlockKey K.w.ok.hH.SH.H k0 text) := by
  refine WP.of_syms (hf_frame (fun m m' p q msg hb => K.w.ok.hH.repr m m' p q msg (fun i hi => hb i (by
      rw [K.w.ok.hH.hS]; exact hi))) (by rw [K.w.ok.hH.hS]; have := K.w.ok.hH.hSB; omega_arith)
    K.w.ok.hf K.w.ok.hfSp K.w.ok.hfSU a fun v af hpost => ?_)
  intro hsy
  have hb : Region.Sub (Proof.Pbkdf2.Whole.X86.stk u) L.CALLS := sub_below hL hc hL.c76
  refine ⟨hc.keep hL af.rd af.wr (af.cs .esp (by decide)) af.frame (fun r hr => ?_) hsy, af.cs,
    af.frame.sub fun r hr => ?_, hpost⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact safe_below hL hc hL.c76
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.CALLS, by simp, hb⟩

/-! ## The byte loop -/

/-- The loop's `n > 0` bytes from `Sv` (in `esi`) to `Dv` (in `ebx`), apart,
the count in `ecx`, into a safe region: `Ctx` kept, the bytes copied, and
`ebx` past them. -/
theorem cp_ok (hL : L.Ok) {u : State} (hc : Ctx K L g m₀ y u) {Sv Dv : BitVec 32} {n : Nat} (hn : 0 < n)
    (hn32 : n < 2 ^ 32) (hS : Sv.toNat + n ≤ 2 ^ 32) (hD : Dv.toNat + n ≤ 2 ^ 32)
    (hr : InRegions (u.rd ++ u.wr) (Sv.setWidth 64) n) (hw : InRegions u.wr (Dv.setWidth 64) n)
    (hsep : Region.Disjoint ⟨Sv.setWidth 64, n⟩ ⟨Dv.setWidth 64, n⟩) (hsafe : Safe L ⟨Dv.setWidth 64, n⟩)
    (hsi : u.gpr .esi = Sv) (hbx : u.gpr .ebx = Dv) (hcx : u.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa Impl.Hkdf.X86.cpLoop u fun u' => Ctx K L g m₀ y u' ∧ Frame [⟨Dv.setWidth 64, n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (Dv.setWidth 64) n = Spec.Sha256.bytesAt u.mem (Sv.setWidth 64) n ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → r ≠ .ecx → u'.gpr r = u.gpr r) ∧
      u'.gpr .ebx = Dv + BitVec.ofNat 32 n := by
  refine WP.mono_syms (Proof.Bignum.X86.copyBytes_ok u
    (Proof.Bignum.X86.copyCtx_of_regions u Sv Dv hn32 hS hD hr hw hsep) hn hsi hbx hcx) fun u' I hsy => ?_
  have hf : Frame [⟨Dv.setWidth 64, n⟩] u.mem u'.mem := I.frame hD
  have hk := I.rest
  have hrest : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → r ≠ .ecx → u'.gpr r = u.gpr r := by
    intro r h₁ h₂ h₃ h₄
    refine hk.1 r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h) <;> contradiction
  refine ⟨hc.keep hL hk.2.1 hk.2.2 (hk.1 .esp (by decide)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsafe) hsy, hf, ?_, hrest, I.dest⟩
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have e := I.copied j hj
  rw [Proof.Bignum.X86.byteAddr_add (by omega_using [hD, hj]), Proof.Bignum.X86.byteAddr_add (by omega_using [hS, hj])] at e
  exact e

end

/-! ## Two runs -/

/-- What one run's piece needs and gives. -/
abbrev Pr (S : Sh) := Lay S → Mem → State → Prop

/-- What each of two runs has, between the frame's entry and its release. -/
structure Env2 (S : Sh) where
  L : Lay S
  g₁ : Reg → BitVec 32
  g₂ : Reg → BitVec 32
  m₁ : Mem
  m₂ : Mem
  y₁ : String → BitVec 32
  y₂ : String → BitVec 32

/-- Two runs with the layout and saved registers of `e`, each satisfying
`Ctx` and `Φ`. -/
def TwoAt (K : Hk) {S : Sh} (Φ : Pr S) (e : Env2 S) (a b : State) : Prop :=
  e.L.Ok ∧ Ctx K e.L e.g₁ e.m₁ e.y₁ a ∧ Ctx K e.L e.g₂ e.m₂ e.y₂ b ∧ Φ e.L e.m₁ a ∧ Φ e.L e.m₂ b

/-- Two runs with the same layout. -/
def Two (K : Hk) {S : Sh} (Φ : Pr S) (a b : State) : Prop := ∃ e, TwoAt K Φ e a b

section
variable {S : Sh} {K : Hk}

theorem two_exists {Φ : Pr S} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ e, RelCT isa (TwoAt K Φ e) c Q) : RelCT isa (Two K Φ) c Q :=
  VG.RelCT.exists_ h

theorem Two.mono {Φ Ψ : Pr S} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t) {a b : State}
    (ht : Two K Φ a b) : Two K Ψ a b :=
  let ⟨e, hL, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Pr S}
    (hct : RelCT isa (Two K Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay S) g m₀ y (t : State), L.Ok → Ctx K L g m₀ y t → Φ L m₀ t →
      WP isa c t fun t' => Ctx K L g m₀ y t' ∧ Ψ L m₀ t') :
    RelCT isa (Two K Φ) c (Two K Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂, y₁, y₂⟩, hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁'⟩ := hw L g₁ m₁ y₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂'⟩ := hw L g₂ m₂ y₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂, y₁, y₂⟩, hL, y₁'.1, y₂'.1, y₁'.2, y₂'.2⟩

/-- `two_wp`, for the runs with the layout and saved registers of `e`. -/
theorem two_wpAt {c : Prog isa} {Φ Ψ : Pr S} {e : Env2 S}
    (hct : RelCT isa (Two K Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay S) g m₀ y (t : State), L.Ok → Ctx K L g m₀ y t → Φ L m₀ t →
      WP isa c t fun t' => Ctx K L g m₀ y t' ∧ Ψ L m₀ t') :
    RelCT isa (TwoAt K Φ e) c (TwoAt K Ψ e) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ ⟨e, hp⟩ e₁ e₂
  obtain ⟨hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁'⟩ := hw e.L e.g₁ e.m₁ e.y₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂'⟩ := hw e.L e.g₂ e.m₂ e.y₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, hL, y₁'.1, y₂'.1, y₁'.2, y₂'.2⟩

/-- Registers that agree in two runs. -/
abbrev Agree (K : Hk) (Φ : Pr S) (rs : List Reg) : Prop :=
  ∀ (L : Lay S) (t₁ t₂ : State) g₁ g₂ m₁ m₂ y₁ y₂, Ctx K L g₁ m₁ y₁ t₁ → Ctx K L g₂ m₂ y₂ t₂ → Φ L m₁ t₁ →
    Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r

/-- The taint check of code whose addresses depend only on `rs`. -/
abbrev TaintOk (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (τr rs) c hc).isSome = true

/-- Code whose addresses depend only on the registers `rs`, which agree. -/
theorem two_prog {c : Prog isa} {Φ : Pr S} (rs : List Reg) (hrs : Agree K Φ rs) (h : TaintOk rs c) :
    RelCT isa (Two K Φ) c fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr rs)
    (fun _ _ ⟨_, _, c₁, c₂, f₁, f₂⟩ => agree_regs (hrs _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem espOnly {Φ : Pr S} : Agree K Φ [.esp] := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact c₁.esp.trans c₂.esp.symm

/-- What only `ebx` changing keeps. -/
def KeepsB (Φ : Pr S) : Prop :=
  ∀ L m₀ (t u : State), Φ L m₀ t → (∀ r, r ≠ .ebx → u.gpr r = t.gpr r) → u.mem = t.mem → u.syms = t.syms →
    Φ L m₀ u

/-- What an indirect call of `n` needs of the table in each run. -/
def TabFn (K : Hk) (S : Sh) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay S) g m₀ y (t : State), L.Ok → Ctx K L g m₀ y t →
    m₀.readW (addr L.tb (4 * j)) 32 = y n ∧
      ts.find? (fun q => (y q.1).setWidth 64 == (y n).setWidth 64) = some (n, c) ∧ y n = L.fa n

theorem tfn_init : TabFn K S 0 K.w.F.hiAnyN K.w.F.hmacInitAny K.f.init := fun _ _ _ _ _ _ hc =>
  ⟨hc.tabMem.1, hc.tabOk.i, hc.fsy _ (by simp)⟩

theorem tfn_upd : TabFn K S 1 K.w.F.H.updN K.w.F.H.updC K.f.upd := fun _ _ _ _ _ _ hc =>
  ⟨hc.tabMem.2.1, hc.tabOk.u, hc.fsy _ (by simp)⟩

theorem tfn_fin : TabFn K S 2 K.w.F.hfN K.w.F.hfC K.f.fin := fun _ _ _ _ _ _ hc =>
  ⟨hc.tabMem.2.2, hc.tabOk.f, hc.fsy _ (by simp)⟩

theorem tblk2_taint0 : TaintOk [.ebx] (.block [.mov .ebx (.mem (Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * 0)))]) :=
  ⟨_, by taint_decide⟩
theorem tblk2_taint1 : TaintOk [.ebx] (.block [.mov .ebx (.mem (Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * 1)))]) :=
  ⟨_, by taint_decide⟩
theorem tblk2_taint2 : TaintOk [.ebx] (.block [.mov .ebx (.mem (Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * 2)))]) :=
  ⟨_, by taint_decide⟩

/-- Two runs of the indirect call of the table's function `j`, pushing `rs`:
both of the same function. -/
theorem tcall_rel {Φ : Pr S} {j : Nat} (hj : 4 * j + 4 ≤ 24)
    (ht : TaintOk [.esp] (.block [.mov .ebx (Impl.Hkdf.X86.argM S.FB S.ti)]))
    (ht₂ : TaintOk [.ebx] (.block [.mov .ebx (.mem (Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * j)))])) {n : String}
    {c : Prog isa} {ts : List (String × Prog isa)} {rs : List Reg} (hn : TabFn K S j n c ts) (hΦ : KeepsB Φ)
    (hcall : RelCT isa (Two K Φ) (.frame (.push rs) (.call n c) (.pop .eax rs.length)) fun _ _ => True) :
    RelCT isa (Two K Φ) (Impl.Hkdf.X86.tcall S.FB S.ti j ts rs) fun _ _ => True := by
  unfold Impl.Hkdf.X86.tcall
  have s₁ : RelCT isa (Two K Φ) (.block [.mov .ebx (Impl.Hkdf.X86.argM S.FB S.ti)])
      (Two K fun L m₀ u => Φ L m₀ u ∧ u.gpr .ebx = L.tb) :=
    two_wp (two_prog [.esp] espOnly ht) fun L g m₀ y t hL hc hφ =>
      WP.mono (arg_ok hL hc (d := .ebx) (by decide) hL.ti) fun u h =>
        ⟨h.ctx, hΦ _ _ _ _ hφ h.keep h.mem h.syms, h.val⟩
  have s₂ : RelCT isa (Two K fun L m₀ u => Φ L m₀ u ∧ u.gpr .ebx = L.tb)
      (.block [.mov .ebx (.mem (Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * j)))])
      (Two K fun L m₀ u => Φ L m₀ u ∧ u.gpr .ebx = L.fa n ∧ u.syms n = L.fa n ∧
        ts.find? (fun q => (u.syms q.1).setWidth 64 == (u.syms n).setWidth 64) = some (n, c)) :=
    two_wp (two_prog [.ebx] (fun _ _ _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact f₁.2.trans f₂.2.symm) ht₂)
      fun L g m₀ y t hL hc ⟨hφ, hb⟩ => wp_ldm hb (hL.inTab hc.rd hj) fun u v => WP.block_nil (by
        have u₂ := Upd.of_wp hL hc (d := .ebx) (by decide) v
        obtain ⟨hw, hf, hfa⟩ := hn L g m₀ y t hL hc
        have hsy : u.syms = y := u₂.syms.trans hc.syms
        exact ⟨u₂.ctx, hΦ _ _ _ _ hφ u₂.keep u₂.mem u₂.syms, by rw [u₂.val, hc.tabWord hL hj, hw, hfa],
          by rw [hsy, hfa], by rw [hsy]; exact hf⟩)
  refine s₁.seq (s₂.seq ?_)
  cases ts with
  | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, f₁, _⟩ => by simp at f₁
  | cons q ts =>
    refine RelCT.frame_icalls_of_call (hcall.mono (fun _ _ => Two.mono fun _ _ _ h => h.1) fun _ _ h => h)
      fun s₁ s₂ ⟨e, _, c₁, c₂, f₁, f₂⟩ => ⟨?_, fun u₁ u₂ p₁ p₂ => ?_⟩
    · simp only [addrs, c₁.esp, c₂.esp]
    · obtain ⟨-, -, -, rfl⟩ := push_some p₁
      obtain ⟨-, -, -, rfl⟩ := push_some p₂
      refine ⟨(e.L.fa n).setWidth 64, by show some _ = _; rw [pushed_gpr _ _ (by decide), f₁.2.1],
        by show some _ = _; rw [pushed_gpr _ _ (by decide), f₂.2.1], ?_, ?_, rfl⟩
      · rw [← f₁.2.2.1, icallTarget_congr (s₂ := s₁) fun q _ => by
          show ((pushed rs s₁).syms q.1).setWidth 64 = (s₁.syms q.1).setWidth 64
          rw [show (pushed rs s₁).syms = s₁.syms from pushRegs_syms s₁ rs]]
        exact f₁.2.2.2
      · rw [← f₂.2.2.1, icallTarget_congr (s₂ := s₂) fun q _ => by
          show ((pushed rs s₂).syms q.1).setWidth 64 = (s₂.syms q.1).setWidth 64
          rw [show (pushed rs s₂).syms = s₂.syms from pushRegs_syms s₂ rs]]
        exact f₂.2.2.2

open VG.Proof.Pbkdf2.Whole.X86 (HfArgs hf_rel)
open VG.Proof.Pbkdf2.Whole.X86.Any (AnyArgs any_rel)
open VG.Proof.Pbkdf2.Stream.X86 (UpdArgs upd_rel)

/-- Two runs of HMAC's `init` for a key of any length, with arguments that are
functions of the layout. -/
theorem init_rel {Φ : Pr S} {inn out k sc : Lay S → BitVec 32} {kl : Lay S → Nat}
    (ha : ∀ (L : Lay S) g m₀ y u, L.Ok → Ctx K L g m₀ y u → Φ L m₀ u →
      AnyArgs K.w.ok.hH.SH (K.w.F.W + K.w.F.H.S) u (inn L) (out L) (k L) (sc L) (kl L)) :
    RelCT isa (Two K Φ) (.frame (.push Proof.Pbkdf2.Whole.X86.hi5) (.call K.w.F.hiAnyN K.w.F.hmacInitAny)
      (.pop .eax Proof.Pbkdf2.Whole.X86.hi5.length)) fun _ _ => True :=
  two_exists fun e => any_rel K.w.any (sp := e.L.F) fun _ _ ⟨hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨ha _ _ _ _ _ hL c₁ f₁, ha _ _ _ _ _ hL c₂ f₂, c₁.esp, c₂.esp⟩

/-- Two runs of the streaming `update`. -/
theorem upd_rel' {Φ : Pr S} {st d sc c : Lay S → BitVec 32} {len : Lay S → Nat}
    (ha : ∀ (L : Lay S) g m₀ y u, L.Ok → Ctx K L g m₀ y u → Φ L m₀ u →
      UpdArgs K.w.ok.hH u .esi .edi (st L) (d L) (sc L) (c L) (len L)) :
    RelCT isa (Two K Φ) (.frame (.push (Proof.Pbkdf2.Stream.X86.upd6 .esi .edi)) (.call K.w.F.H.updN K.w.F.H.updC)
      (.pop .eax (Proof.Pbkdf2.Stream.X86.upd6 .esi .edi).length)) fun _ _ => True :=
  two_exists fun e => upd_rel K.w.ok.hH (sp := e.L.F) fun _ _ ⟨hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨ha _ _ _ _ _ hL c₁ f₁, ha _ _ _ _ _ hL c₂ f₂, c₁.esp, c₂.esp⟩

/-- Two runs of HMAC's `finalize`. -/
theorem fin_rel {Φ : Pr S} {inn ou lo hi o sc : Lay S → BitVec 32}
    (ha : ∀ (L : Lay S) g m₀ y u, L.Ok → Ctx K L g m₀ y u → Φ L m₀ u →
      HfArgs K.w.ok.hH.SH K.w.ok.Wf u (inn L) (ou L) (lo L) (hi L) (o L) (sc L)) :
    RelCT isa (Two K Φ) (.frame (.push Proof.Pbkdf2.Whole.X86.hf6) (.call K.w.F.hfN K.w.F.hfC)
      (.pop .eax Proof.Pbkdf2.Whole.X86.hf6.length)) fun _ _ => True :=
  two_exists fun e => hf_rel K.w.ok.hf (sp := e.L.F) fun _ _ ⟨hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨ha _ _ _ _ _ hL c₁ f₁, ha _ _ _ _ _ hL c₂ f₂, c₁.esp, c₂.esp⟩

theorem cpLoop_taint : TaintOk [.esi, .ebx, .ecx] Impl.Hkdf.X86.cpLoop := ⟨_, by taint_decide⟩

/-- Two runs of the byte loop, from registers that agree. -/
theorem cp_rel {Φ : Pr S} (h : Agree K Φ [.esi, .ebx, .ecx]) :
    RelCT isa (Two K Φ) Impl.Hkdf.X86.cpLoop fun _ _ => True :=
  two_prog _ h cpLoop_taint

/-- Two runs from the states after the frame's allocation, of calls with the
same layout: our caller's registers saved and the table in `eax`, related by
`Two`. -/
theorem start_rel {L : Lay S} (hL : L.Ok) {P : Lay S → Prop} (hP : P L) {s₁ s₂ : State} (he₁ : Entry K L s₁)
    (he₂ : Entry K L s₂) (ht : TaintOk [.esp] (.block (Impl.Hkdf.X86.entry S.FB S.ti))) :
    RelCT isa (fun a b => a = allocFrame S.FB s₁ ∧ b = allocFrame S.FB s₂) (.block (Impl.Hkdf.X86.entry S.FB S.ti))
      (Two K fun (L' : Lay S) (_ : Mem) (u : State) => P L' ∧ u.gpr .eax = L'.tb) := by
  obtain ⟨_, ht⟩ := ht
  refine ((VG.RelCT.taint (A := taint) (τr [.esp]) (fun _ _ ⟨ea, eb⟩ => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr ea eb
      rw [allocFrame_esp, allocFrame_esp, he₁.esp, he₂.esp]) ht).wp
    (F₁ := fun t : State => Ctx K L s₁.gpr s₁.mem s₁.syms t ∧ t.gpr .eax = L.tb)
    (F₂ := fun t : State => Ctx K L s₂.gpr s₂.mem s₂.syms t ∧ t.gpr .eax = L.tb)
    fun _ _ ⟨ea, eb⟩ => by subst ea eb; exact ⟨entry_ok hL he₁, entry_ok hL he₂⟩).mono (fun _ _ h => h)
    fun a b h => by
      obtain ⟨_, ⟨c₁, x₁⟩, ⟨c₂, x₂⟩⟩ := h
      exact ⟨⟨L, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem, s₁.syms, s₂.syms⟩, hL, c₁, c₂, ⟨hP, x₁⟩, ⟨hP, x₂⟩⟩

end

end VG.Proof.Hkdf.X86
