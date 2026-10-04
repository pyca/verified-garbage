import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Contract

/-!
# Deterministic ECDSA on AArch64: where everything is

The function's buffers (`out`, `d`, `digest` of `dn` bytes, `scratch`) and
the 240 bytes of stack below the stack pointer, from `B` up (`Lay dn`): the
16 bytes the calls use (HMAC's functions' frames), then the frame of 208
bytes, from `B + 16`: `K` and `V` (64 bytes each), `h` (32 bytes), the
number of candidates left, and the pointers to `scratch`, `digest`, `d` and
`out`; then the frame holding our return address (`B + 224`). `Ctx` is what
holds between the frames' pushes and pops: the permissions, `sp`, the
callee-saved registers, the return address and the pointers in the frames,
and that memory changed only in `out`, `scratch` and the stack. Code that
writes only regions below the pointers (`Safe`) keeps it (`Ctx.keep`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

/-- The buffers and the lowest byte of the stack used (`sp - 240` on entry),
for a digest of `dn` bytes. -/
structure Lay (dn : Nat) where
  out : Addr
  d : Addr
  dg : Addr
  scr : Addr
  B : Addr

namespace Lay

variable {dn : Nat} (L : Lay dn)

abbrev OUT : Region := ⟨L.out, 64⟩
abbrev D : Region := ⟨L.d, 32⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 240⟩
/-- The frames: our words, and our return address. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 208⟩
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 224, 16⟩
/-- The stack below the frame's pointers: the calls' and `K`, `V`, `h` and the count. -/
abbrev LOW : Region := ⟨L.B, 184⟩

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
  no : L.out.toNat + 64 ≤ 2 ^ 64
  nd : L.d.toNat + 32 ≤ 2 ^ 64
  ng : L.dg.toNat + dn ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  nB : L.B.toNat + 240 ≤ 2 ^ 64

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
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 224) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 16, 208⟩ :=
  ⟨d - 16, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below the frame's pointers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 184) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (Offset.sub_base _ h))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 240) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 240) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_DG (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 240) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

/-- The 16 bytes the calls use, apart from `scratch`. -/
theorem low_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ h₂)

/-- The frames' pointers and our return address are apart from every safe region. -/
theorem ptrs_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 184, 56⟩ r := by
  rcases hs with hs | hs | hs
  · exact (h.stk_OUT (by omega)).sub_right hs
  · exact (h.stk_SCR (by omega)).sub_right hs
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

/-! ## Between the frames' pushes and pops -/

/-- The state between the frames' pushes and pops: `g` are the registers on
entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG]
  wr : t.wr = [L.FR, L.LR, L.OUT, L.SCR]
  sp : t.sp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 184) 64 = L.scr
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 192) 64 = L.dg
  pD : t.mem.readW (L.B + BitVec.ofNat 64 200) 64 = L.d
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 208) 64 = L.out
  lr : t.mem.readW (L.B + BitVec.ofNat 64 224) 64 = g .x30
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega) a (h a ha)⟩

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `sp` and the callee-saved registers
but `x30`, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hcs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) : Ctx L g m₀ t' := by
  have keep : ∀ d, 184 ≤ d → d + 8 ≤ 240 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 184, 56⟩)
      (Offset.contains _ h₁ (by omega) (by omega)) (fun r hr => hL.ptrs_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'),
    (keep 184 (by omega) (by omega)).trans hc.pScr, (keep 192 (by omega) (by omega)).trans hc.pDg,
    (keep 200 (by omega) (by omega)).trans hc.pD, (keep 208 (by omega) (by omega)).trans hc.pOut,
    (keep 224 (by omega) (by omega)).trans hc.lr,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame)⟩

/-- Code that writes only registers but the callee-saved ones. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
  hc.keep hL hrd hwr hsp hg (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- A byte of `d`, as on entry. -/
theorem d_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < 32) :
    t.mem (L.d + BitVec.ofNat 64 i) = m₀ (L.d + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.D) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.od.symm
    · exact hL.dc
    · exact hL.kd.symm) (by show (32 : Nat) ≤ 2 ^ 64; decide) hi

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

theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 224) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 224) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inScr (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inScrW (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inD (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 32) :
    InRegions (t.rd ++ t.wr) (L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inDg (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.dg + BitVec.ofNat 64 o) n :=
  ⟨L.DG, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

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

/-- The layout of a call from `s`, with a digest of `dn` bytes. -/
def lay (dn : Nat) (s : State) : Lay dn :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.sp - BitVec.ofNat 64 240⟩

theorem lay_top (dn : Nat) (s : State) : (lay dn s).B + BitVec.ofNat 64 240 = s.sp :=
  BitVec.sub_add_cancel _ _

theorem lay_ok {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcAArch64 I).pre s) :
    (lay I.hashLen s).Ok := by
  obtain ⟨-, -, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp⟩ := h
  have nB : (lay I.hashLen s).B.toNat + 240 ≤ 2 ^ 64 := by
    simp only [lay]
    rw [Offset.toNat_sub_ofNat s.sp 240]
    omega
  exact ⟨od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nB⟩

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated Impl.Ecdsa.Rfc6979.AArch64.frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl

theorem entered_sp (dn : Nat) (s : State) : (entered s).sp = (lay dn s).B + BitVec.ofNat 64 16 := by
  show s.sp - 16 - BitVec.ofNat 64 208 = s.sp - BitVec.ofNat 64 240 + BitVec.ofNat 64 16
  bv_omega

theorem lr_slot (dn : Nat) (s : State) : s.sp - 16 = (lay dn s).B + BitVec.ofNat 64 224 := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 240 + BitVec.ofNat 64 224
  bv_omega

theorem entered_wr (dn : Nat) (s : State) :
    (entered s).wr = (lay dn s).FR :: (lay dn s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 208, 208⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 208 = (lay dn s).B + BitVec.ofNat 64 16 from entered_sp dn s,
    lr_slot dn]

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem entered_mem (dn : Nat) (s : State) :
    (entered s).mem = s.mem.writeW ((lay dn s).B + BitVec.ofNat 64 224) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot dn, write8]

/-- Four words stored in the frame's pointers. -/
theorem four_ok (B : Addr) (m : Mem) (a b c d : BitVec 64) :
    let m' := (((m.writeW (B + BitVec.ofNat 64 208) a).writeW (B + BitVec.ofNat 64 200) b).writeW
      (B + BitVec.ofNat 64 192) c).writeW (B + BitVec.ofNat 64 184) d
    Frame [⟨B + BitVec.ofNat 64 184, 32⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 208) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 200) 64 = b ∧ m'.readW (B + BitVec.ofNat 64 192) 64 = c ∧
      m'.readW (B + BitVec.ofNat 64 184) 64 = d := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 240 → y + 8 ≤ 240 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega) (by omega)
  have ct : ∀ x, 184 ≤ x → x + 8 ≤ 216 →
      (⟨B + BitVec.ofNat 64 184, 32⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega) (by omega)
  refine ⟨((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 208 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 200 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 192 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (ct 184 (by omega) (by omega)),
    ?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (sep 208 184 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 208 192 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 208 200 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 200 184 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 200 192 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 192 184 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]

/-- The arguments saved in the frame: `Ctx` holds. -/
theorem entry_ok {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : (rfcAArch64 I).pre s) :
    WP isa (.block Impl.Ecdsa.Rfc6979.AArch64.Cfg.saveArgs) (entered s)
      (Ctx (lay I.hashLen s) s.gpr s.mem) := by
  have hL := lay_ok h
  have hnB := hL.nB
  have hw : ∀ d, 16 ≤ d → d + 8 ≤ 224 → InRegions (entered s).wr ((lay I.hashLen s).B + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => ⟨(lay I.hashLen s).FR, by rw [entered_wr I.hashLen]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  have w184 := hw 184 (by omega) (by omega)
  have w192 := hw 192 (by omega) (by omega)
  have w200 := hw 200 (by omega) (by omega)
  have w208 := hw 208 (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Impl.Ecdsa.Rfc6979.AArch64.Cfg.saveArgs, Impl.Ecdsa.Rfc6979.AArch64.fOut,
    Impl.Ecdsa.Rfc6979.AArch64.fD, Impl.Ecdsa.Rfc6979.AArch64.fDigest, Impl.Ecdsa.Rfc6979.AArch64.fScratch,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, State.read,
    Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, Option.bind_some, reduceCtorEq, ite_false, ite_true, entered_sp I.hashLen,
    Offset.add_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, w184, w192, w200, w208,
    write8, Option.some.injEq, exists_eq_left', BitVec.add_zero, entered_gpr]
  obtain ⟨f, k208, k200, k192, k184⟩ := four_ok (lay I.hashLen s).B (entered s).mem (s.gpr .x0) (s.gpr .x1)
    (s.gpr .x2) (s.gpr .x3)
  rw [entered_mem I.hashLen] at f k208 k200 k192 k184
  rw [entered_mem I.hashLen]
  refine ⟨?_, ?_, rfl, ?_, k184, k192, k200, k208, ?_, ?_⟩
  · simp only [entered_rd]; rw [h.1]; rfl
  · rw [entered_wr I.hashLen, h.2.1]; rfl
  · intro r hr hr'
    rw [RegUpd.gpr_write_of_ne _ _ _ (by intro e; subst e; simp [preserved] at hr), entered_gpr]
  · rw [f.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · refine Frame.trans (Frame.writeW (Frame.refl _ _) (r := (lay I.hashLen s).STK) (by simp) _
      (Offset.contains_base _ (by omega) (by omega))) (Frame.sub f fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(lay I.hashLen s).STK, by simp, Offset.sub_base _ (by omega)⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64
