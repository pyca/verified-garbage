import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Callee
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, AArch64: the function

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
allocates its frame of 16 bytes, at `B + 2576` with `B` the base of the 2592
bytes of stack below the stack pointer (`sp = B + 2592`), keeps our return
address at `B + 2584` and `tag`, the call's stack argument, at `B + 2576`
(`entry_ok`), gathers the slices to `dst` (`gather_wp`), and calls
`vg_aes_gcm_seal` on them in place (`sealSpec_pre`, `sealSpec_post`); the
call keeps our frame, so the return address comes back from it
(`sealGather_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen)
open VG.Proof.AesGcm.AArch64 (bytesAt_frame blockAt_frame covers_of_mem covers_cons covers_append covers_prefix)

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- The key context, through a frame of regions apart from it. -/
theorem ctx_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 256⟩ : Region).Disjoint r) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : ctxCiph m' K R = ctxCiph m K R ∧ ctxH m' K = ctxH m K := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_⟩
  · simp only [ctxCiph]
    rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]
  · simp only [ctxH]
    exact blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub_base K (show 240 + 16 ≤ 256 by decide))

/-- The bytes written at `q` are there. -/
theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₂, ite_true]
    simp [List.getD_eq_getElem?_getD, h₂]

/-- The entry, in the frame at `P`: our return address at `P + 8`, the
stack argument at `P + 32` (`tag`) at `P`, and the one at `P + 16` (`dst`)
in `x11`. -/
theorem entry_ok (a : State) {P : Addr} (hsp : a.sp = P)
    (w₈ : InRegions a.wr (P + BitVec.ofNat 64 8) 8) (w₀ : InRegions a.wr P 8)
    (r₃₂ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 32) 8)
    (r₁₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 16) 8) :
    WP isa (.block entry) a fun e =>
      e.mem = (a.mem.write (P + BitVec.ofNat 64 8) 8 (a.gpr .x30)).write P 8
        ((a.mem.write (P + BitVec.ofNat 64 8) 8 (a.gpr .x30)).read (P + BitVec.ofNat 64 32) 8) ∧
      e.gpr .x11 = e.mem.read (P + BitVec.ofNat 64 16) 8 ∧
      (∀ r, r ≠ .x11 → r ≠ .x16 → r ≠ .x17 → e.gpr r = a.gpr r) ∧ e.sp = a.sp ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  subst hsp
  have e₀ : a.sp + BitVec.ofNat 64 0 = a.sp := BitVec.add_zero _
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [entry, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write, sp_write, Option.bind_some,
      Option.map_some, BitVec.setWidth_eq, e₀, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul,
      Nat.reduceMod, and_self, w₈, w₀, r₃₂, r₁₆]; rfl, rfl⟩ fun e he => ?_
  subst he
  exact ⟨rfl, by simp [State.write], fun r h₁ h₂ h₃ => by simp [State.write, h₁, h₂, h₃], rfl, rfl, rfl⟩

/-- `ldrSp t k`: the doubleword at `sp + k` into `t`. -/
theorem ldrSp_ok (a : State) {t : Reg} {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (r : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.ldrSp t k]) a fun e => e.gpr t = a.mem.read (a.sp + BitVec.ofNat 64 k) 8 ∧
      (∀ r, r ≠ t → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.sp = a.sp ∧ e.rd = a.rd ∧ e.wr = a.wr ∧ e.v = a.v := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Option.map_some,
      BitVec.setWidth_eq, hk, r, and_self, ite_true]; rfl, rfl⟩ fun e he => ?_
  subst he
  exact ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl, rfl⟩

/-- `callArgs`: the stack arguments at `sp + 16` and `sp + 24` into `x6` and `x7`. -/
theorem callArgs_ok (a : State) (r₁₆ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 16) 8)
    (r₂₄ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 24) 8) :
    WP isa (.block callArgs) a fun e => e.gpr .x6 = a.mem.read (a.sp + BitVec.ofNat 64 16) 8 ∧
      e.gpr .x7 = a.mem.read (a.sp + BitVec.ofNat 64 24) 8 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.sp = a.sp ∧ e.rd = a.rd ∧
      e.wr = a.wr ∧ e.v = a.v := by
  show WP isa (.block ([Instr.ldrSp .x6 16] ++ [Instr.ldrSp .x7 24])) a _
  refine WP.block_append (WP.mono (ldrSp_ok (t := .x6) a (by decide) r₁₆) fun e ⟨g₆, g, m, sp, rd, wr, v⟩ => ?_)
  refine WP.mono (ldrSp_ok (t := .x7) e (by decide) (by rw [rd, wr, sp]; exact r₂₄))
    fun e' ⟨g₇, g', m', sp', rd', wr', v'⟩ => ?_
  refine ⟨by rw [g' _ (by decide), g₆], by rw [g₇, m, sp], fun r h₁ h₂ => by rw [g' r h₂, g r h₁], by rw [m', m],
    by rw [sp', sp], by rw [rd', rd], by rw [wr', wr], by rw [v', v]⟩

/-- The `n` bytes at `p + d` are within the `k` bytes at `p + e`. -/
theorem contains_off (p : Addr) {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) (hd : d - e < 2 ^ 64) :
    (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := by
  rw [show p + BitVec.ofNat 64 d = p + BitVec.ofNat 64 e + BitVec.ofNat 64 (d - e) by
    rw [Offset.add_ofNat_add_ofNat, Nat.add_sub_cancel' h₁]]
  exact Offset.contains_base _ (by omega) hd

theorem stackArgAddr_eq (s : State) {B : Addr} (hB : s.sp = B + BitVec.ofNat 64 2592) (i : Nat) :
    stackArgAddr s i = B + BitVec.ofNat 64 (2592 + 8 * i) := by
  rw [stackArgAddr, hB, Offset.add_ofNat_add_ofNat]

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 2592 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 2592

/-- The frame. -/
abbrev FR : Region := ⟨Bs s + BitVec.ofNat 64 2576, 16⟩

/-- The memory after the entry: the return address at `Bs + 2584` and `tag` at `Bs + 2576`. -/
abbrev eMem : Mem :=
  (s.mem.write (Bs s + BitVec.ofNat 64 2584) 8 (s.gpr .x30)).write (Bs s + BitVec.ofNat 64 2576) 8 (Tg s)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gMem : Mem := writeBytes (eMem s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_aes_gcm_seal` reads and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s, ⟨Bs s + BitVec.ofNat 64 2576, 8⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 2592
  hBn : (Bs s).toNat + 2616 ≤ 2 ^ 64
  bk : (⟨Bs s, 2592⟩ : Region).Disjoint (kR s)
  bn : (⟨Bs s, 2592⟩ : Region).Disjoint (nR s)
  ba : (⟨Bs s, 2592⟩ : Region).Disjoint (aR s)
  bds : (⟨Bs s, 2592⟩ : Region).Disjoint (dsR s)
  bl : ∀ r ∈ lsR s, (⟨Bs s, 2592⟩ : Region).Disjoint r
  bd : (⟨Bs s, 2592⟩ : Region).Disjoint (dR s)
  bt : (⟨Bs s, 2592⟩ : Region).Disjoint (tgR s)
  hargR : argR s = ⟨Bs s + BitVec.ofNat 64 2592, 24⟩
  w₁ : 2592 ≤ s.sp.toNat
  hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14
  hgl : gl s (Cnt s) = L s
  ods : (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩ := hs
  have hB : s.sp = Bs s + BitVec.ofNat 64 2592 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 2616 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega
  exact ⟨⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩, hB, hBn, bk, bn, ba, bds, bl, bd, bt,
    by simp only [argR, stackArgAddr_eq s hB, Nat.mul_zero, Nat.add_zero], w₁, hR, hgl, ods⟩

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2592) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 2592⟩ :=
  Offset.sub_base _ h'

theorem frame_eMem (s : State) : Frame [FR s] s.mem (eMem s) :=
  ((Frame.refl _ _).write (List.mem_singleton_self _) _
    (contains_off _ (by decide) (by decide) (by decide))).write (List.mem_singleton_self _) _
    (by simp [Region.Contains])

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hA (i : Nat) : stackArgAddr s i = Bs s + BitVec.ofNat 64 (2592 + 8 * i) := stackArgAddr_eq s h.hB i

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

theorem inArg (d : Nat) (h₁ : 2592 ≤ d) (h₂ : d + 8 ≤ 2616) (rs : List Region) :
    InRegions (s.rd ++ rs) (Bs s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_append_left _ h.argIn, by rw [h.hargR]; exact contains_off _ h₁ (by omega) (by omega)⟩

theorem sa (i : Nat) : s.mem.read (Bs s + BitVec.ofNat 64 (2592 + 8 * i)) 8 = stackArg s i := by
  rw [← h.hA]; rfl

theorem sep (d e : Nat) (h₁ : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2616) (he : e + 8 ≤ 2616) :
    Mem.Sep (Bs s + BitVec.ofNat 64 d) 8 (Bs s + BitVec.ofNat 64 e) 8 :=
  Offset.sep _ h₁ (by have := h.hBn; omega) (by have := h.hBn; omega)

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 2592⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  frame_eMem s x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 2576 16 (by decide) x hc)

theorem eArg (i : Nat) (hi : i < 3) : (eMem s).read (Bs s + BitVec.ofNat 64 (2592 + 8 * i)) 8 = stackArg s i := by
  rw [Mem.read_write_sep (h.sep _ 2576 (by omega) (by omega) (by decide)) (by decide),
    Mem.read_write_sep (h.sep _ 2584 (by omega) (by omega) (by decide)) (by decide)]
  exact h.sa i

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eMem s x := by
  intro r hr x hx
  refine (keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bl r hr).symm

theorem hpt : gathered 64 (eMem s) (Src s) (Cnt s) = pt s (Cnt s) := Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gMem : Frame [dR s] (eMem s) (gMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

theorem gArg (i : Nat) (hi : i < 3) : (gMem s).read (Bs s + BitVec.ofNat 64 (2592 + 8 * i)) 8 = stackArg s i := by
  rw [← h.eArg i hi]
  refine Frame.read h.frame_gMem (contains_off _ (Nat.le_refl _) (Nat.le_refl _) (by omega)) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, darg, -⟩ := h.pre
  rw [h.hargR] at darg
  exact (darg.sub_right (Offset.sub _ (show 2592 ≤ 2592 + 8 * i by omega) (by omega))).symm

/-- A doubleword of the frame, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd' : d + 8 ≤ 2592) :
    (gMem s).read (Bs s + BitVec.ofNat 64 d) 8 = (eMem s).read (Bs s + BitVec.ofNat 64 d) 8 :=
  Frame.read h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.bd.symm.sub_right (stk_sub s d 8 hd') |>.symm) (by decide)

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  x11 : e.gpr .x11 = Dst s
  gpr : ∀ r, r ≠ .x11 → r ≠ .x16 → r ≠ .x17 → e.gpr r = s.gpr r
  sp : e.sp = Bs s + BitVec.ofNat 64 2576
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (e.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem allocated_sp {s : State} (h : Lay s) : (allocated 16 s).sp = Bs s + BitVec.ofNat 64 2576 := by
  show s.sp - BitVec.ofNat 64 16 = _
  rw [h.hB, add_ofNat_sub_ofNat _ (by decide)]

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 16 s) (Entered s) := by
  have asp := allocated_sp h
  have awr : (allocated 16 s).wr = FR s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 16, 16⟩ :: s.wr : List Region) = _
    rw [show s.sp - BitVec.ofNat 64 16 = _ from asp]
  refine WP.mono (WP.preservedV (entry_ok (allocated 16 s) asp
      ⟨_, by rw [awr]; exact List.mem_cons_self .., Offset.contains_base _ (by decide) (by decide)⟩
      ⟨_, by rw [awr]; exact List.mem_cons_self .., by simp [Region.Contains]⟩
      (by rw [Offset.add_ofNat_add_ofNat]; exact h.inArg 2608 (by decide) (by decide) _)
      (by rw [Offset.add_ofNat_add_ofNat]; exact h.inArg 2592 (by decide) (by decide) _)) (by lit_decide))
    fun e ⟨⟨me, x11e, ge, spe, rde, wre⟩, ve⟩ => ?_
  simp only [Offset.add_ofNat_add_ofNat, Nat.reduceAdd] at me x11e
  change e.mem = (s.mem.write _ 8 (s.gpr .x30)).write _ 8 ((s.mem.write _ 8 (s.gpr .x30)).read _ 8) at me
  rw [Mem.read_write_sep (h.sep 2608 2584 (by decide) (by decide) (by decide)) (by decide), h.sa 2] at me
  refine ⟨me, ?_, ge, by rw [spe, asp], rde, by rw [wre, awr], ve⟩
  rw [x11e, me]
  exact h.eArg 0 (by decide)

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { x6 := he.gpr _ (by decide) (by decide) (by decide)
          x7 := by rw [he.gpr _ (by decide) (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
          x11 := he.x11
          hcnt := (s.gpr .x7).isLt
          dw := ods
          lt := (stackArg s 1).isLt
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl
          dsr := covers_of_mem (List.mem_append_left _ (by rw [he.rd]; show dsR s ∈ s.rd; rw [rd]; simp))
          lsr := fun r hr => covers_of_mem (List.mem_append_left _ (by
            rw [hls] at hr; rw [he.rd]; show r ∈ s.rd; rw [rd]; simp [hr]))
          dw' := covers_of_mem (by rw [he.wr, wr]; simp)
          dsd := dsd
          lsd := fun r hr => (lsdt r (by rw [hls] at hr; exact hr)).1 }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gMem s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .x11 → r ≠ .x16 → r ≠ .x17 → g.gpr r = s.gpr r
  sp : g.sp = Bs s + BitVec.ofNat 64 2576
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (g.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) : WP isa gather e (Gathered s) := by
  refine WP.mono (WP.preservedV (gather_wp e (gatherPre_of h he)) (by lit_decide)) fun g ⟨⟨mg, kg⟩, vg⟩ => ?_
  rw [he.mem, h.hpt] at mg
  exact ⟨mg, fun r hg h₁₁ h₁₆ h₁₇ => (kg.gpr r hg).trans (he.gpr r h₁₁ h₁₆ h₁₇), kg.sp.trans he.sp,
    kg.rd.trans he.rd, kg.wr.trans he.wr, fun r hr => (vg r hr).trans (he.v r hr)⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gMem s
  x6 : c.gpr .x6 = Dst s
  x7 : c.gpr .x7 = stackArg s 1
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → r ∉ gatherRegs → r ≠ .x11 → r ≠ .x16 → r ≠ .x17 → c.gpr r = s.gpr r
  sp : c.sp = Bs s + BitVec.ofNat 64 2576
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (c.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa (.block callArgs) g (Ready s) := by
  refine WP.mono (callArgs_ok g
      (by rw [hg.sp, Offset.add_ofNat_add_ofNat, hg.rd, hg.wr]; exact h.inArg 2592 (by decide) (by decide) _)
      (by rw [hg.sp, Offset.add_ofNat_add_ofNat, hg.rd, hg.wr]; exact h.inArg 2600 (by decide) (by decide) _))
    fun c ⟨x6c, x7c, gc, mc, spc, rdc, wrc, vc⟩ => ?_
  rw [hg.sp, Offset.add_ofNat_add_ofNat, hg.mem] at x6c x7c
  exact ⟨mc.trans hg.mem, x6c.trans (h.gArg 0 (by decide)), x7c.trans (h.gArg 1 (by decide)),
    fun r h₆ h₇ hr h₁₁ h₁₆ h₁₇ => (gc r h₆ h₇).trans (hg.gpr r hr h₁₁ h₁₆ h₁₇), spc.trans hg.sp,
    rdc.trans hg.rd, wrc.trans hg.wr, fun r hr => by rw [vc]; exact hg.v r hr⟩

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) :
    c.callEntry.gpr .x0 = s.gpr .x0 ∧ c.callEntry.gpr .x1 = s.gpr .x1 ∧ c.callEntry.gpr .x2 = s.gpr .x2 ∧
      c.callEntry.gpr .x3 = s.gpr .x3 ∧ c.callEntry.gpr .x4 = s.gpr .x4 ∧ c.callEntry.gpr .x5 = s.gpr .x5 ∧
      c.callEntry.gpr .x6 = Dst s ∧ c.callEntry.gpr .x7 = stackArg s 1 := by
  have cg (r : Reg) (h₀ : r ∉ linkRegs) (h₆ : r ≠ .x6) (h₇ : r ≠ .x7) (hg : r ∉ gatherRegs) (h₁₁ : r ≠ .x11)
      (h₁₆ : r ≠ .x16) (h₁₇ : r ≠ .x17) : c.callEntry.gpr r = s.gpr r := by
    rw [c.callEntry_gpr h₀, hc.gpr r h₆ h₇ hg h₁₁ h₁₆ h₁₇]
  exact ⟨cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [c.callEntry_gpr (by decide), hc.x6], by rw [c.callEntry_gpr (by decide), hc.x7]⟩

/-- `tag`, the call's stack argument. -/
theorem Ready.stackArg0 {s c : State} (h : Lay s) (hc : Ready s c) (rd' wr' : List Region) :
    stackArg ((c.callEntry).withRegions rd' wr') 0 = Tg s := by
  have cTg : c.mem.read (Bs s + BitVec.ofNat 64 2576) 8 = Tg s := by
    rw [hc.mem, h.gFrame 2576 (by decide)]; exact read_write_self _ _ _
  rw [← cTg, ← hc.sp]; simp [stackArg, stackArgAddr, Mem.readW]

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩ := h.pre
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  have sa0 := hc.stackArg0 h
  have sad0 (rd' wr' : List Region) :
      stackArgAddr ((c.callEntry).withRegions rd' wr') 0 = Bs s + BitVec.ofNat 64 2576 := by
    simp [stackArgAddr, hc.sp]
  have hPn : (Bs s + BitVec.ofNat 64 2576).toNat = (Bs s).toNat + 2576 := by
    have := h.hBn
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c0, c1, c2, c3, c4, c5, c6, c7, sa0, sad0, hc.sp, BitVec.add_sub_cancel]
    have stkArg : (⟨Bs s, 2576⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 2576, 8⟩ := by
      have := Offset.disjoint (Bs s) (d := 0) (n := 2576) (e := 2576) (k := 8) (.inl (by decide)) (by decide)
        (by decide)
      rwa [BitVec.add_zero] at this
    refine ⟨trivial, trivial, kd, kt, nd, nt, ad, at_, dt, (h.bd.sub_left (stk_sub s 2576 8 (by decide))).symm,
      (h.bt.sub_left (stk_sub s 2576 8 (by decide))).symm, h.bk.sub_left (Region.sub_prefix (by decide)),
      h.bn.sub_left (Region.sub_prefix (by decide)), h.ba.sub_left (Region.sub_prefix (by decide)),
      h.bd.sub_left (Region.sub_prefix (by decide)), h.bt.sub_left (Region.sub_prefix (by decide)), stkArg,
      ok, on, oa, od, ot, by omega, by have := h.hBn; omega, hR⟩
  · have inRd {r : Region} (h' : r ∈ [kR s, nR s, aR s]) : Covers [r] (c.rd ++ c.wr) := by
      refine covers_of_mem (List.mem_append_left _ ?_)
      rw [hc.rd, rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl <;> simp
    have hfr : Covers [FR s] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..))
    have hw' {r : Region} (h' : r ∈ [dR s, tgR s]) : Covers [r] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr, wr]; exact List.mem_cons_of_mem _ h'))
    exact covers_append (covers_cons (inRd (r := kR s) (by simp)) (covers_cons (inRd (r := nR s) (by simp))
      (covers_cons (inRd (r := aR s) (by simp)) (covers_cons (covers_prefix hfr (by decide))
        Proof.AesGcm.AArch64.covers_nil))))
      (covers_cons (hw' (by simp)) (covers_cons (hw' (by simp)) Proof.AesGcm.AArch64.covers_nil))
  · rw [hc.wr, wr]
    exact covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp)) Proof.AesGcm.AArch64.covers_nil)

/-- After the call. -/
structure Called (s s' : State) : Prop where
  ra : s'.mem.read (Bs s + BitVec.ofNat 64 2584) 8 = s.gpr .x30
  out : encryptWith (ctxCiph (gMem s) (K s) (s.gpr .x1).toNat) (ctxH (gMem s) (K s)) 16
      (bytesAt (gMem s) (Nn s) (NL s)) (bytesAt (gMem s) (Dst s) (L s)) (bytesAt (gMem s) (Ad s) (AL s)) =
    (bytesAt s'.mem (Dst s) (L s), bytesAt s'.mem (Tg s) 16)
  gpr : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  sp : s'.sp = Bs s + BitVec.ofNat 64 2576
  rd : s'.rd = s.rd
  wr : s'.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem called_wp (F : SealFn) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call F.fn.name F.fn.code) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  have hdep := F.depth
  refine WP.callFV (name := F.fn.name) F.verified.1 (sealSpec_pre hcp) hcov hw
    (fun s' rd' wr' sp' fr' pres' presV' post' => ?_) (by omega)
  have hpost := sealSpec_post post' (by simp only [State.withRegions_gpr, c1]; exact h.hR)
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3, c4, c5, c6, c7,
    hc.stackArg0 h, hc.mem] at hpost
  have hpres : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x6 ∧ r ≠ .x7 ∧ r ∉ gatherRegs ∧ r ≠ .x11 ∧
      r ≠ .x16 ∧ r ≠ .x17 := by decide
  -- The return address, from the frame, which the call kept.
  have ra : s'.mem.read (Bs s + BitVec.ofNat 64 2584) 8 = s.gpr .x30 := by
    have e : c.mem.read (Bs s + BitVec.ofNat 64 2584) 8 = s.gpr .x30 := by
      rw [hc.mem, h.gFrame 2584 (by decide),
        Mem.read_write_sep (h.sep 2584 2576 (by decide) (by decide) (by decide)) (by decide)]
      exact read_write_self _ _ _
    rw [← e]
    refine Frame.read fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.bd.symm.sub_right (stk_sub s 2584 8 (by decide)) |>.symm
    · exact h.bt.symm.sub_right (stk_sub s 2584 8 (by decide)) |>.symm
    · simp only [below, hc.sp, add_ofNat_sub_ofNat _ (show 16 * F.fn.code.aarch64Depth ≤ 2576 by omega)]
      exact Offset.disjoint _ (.inr (by omega)) (by decide) (by have := h.hBn; omega)
  exact ⟨ra, hpost, fun r hr h30 => by
      obtain ⟨h₆, h₇, hg, h₁₁, h₁₆, h₁₇⟩ := hpres r hr h30
      rw [pres' r hr h30, hc.gpr r h₆ h₇ hg h₁₁ h₁₆ h₁₇],
    sp'.trans hc.sp, rd'.trans hc.rd, wr'.trans hc.wr, fun r hr => (presV' r hr).trans (hc.v r hr)⟩

/-- The return address back in `x30`, and the frame freed. -/
theorem ret_wp {s s' : State} (h : Lay s) (hc : Called s s') :
    WP isa (.block [.ldrSp .x30 8]) s' fun z => abiPreserved s (freed 16 z) ∧ gatherPost s (freed 16 z) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩ := h.pre
  refine WP.mono (ldrSp_ok (t := .x30) (k := 8) s' (by decide) ?_) fun z ⟨x30z, gz, mz, spz, rdz, wrz, vz⟩ => ?_
  · rw [hc.sp, hc.rd, hc.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), contains_off _ (by decide) (by decide) (by decide)⟩
  rw [hc.sp, Offset.add_ofNat_add_ofNat, hc.ra] at x30z
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · -- The callee-saved registers.
    show z.gpr r = s.gpr r
    by_cases h30 : r = .x30
    · subst h30; exact x30z
    · rw [gz r h30, hc.gpr r hr h30]
  · -- The stack pointer.
    show z.sp + BitVec.ofNat 64 16 = s.sp
    rw [spz, hc.sp, Offset.add_ofNat_add_ofNat, h.hB]
  · -- The callee-saved vector registers.
    show (z.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
    rw [vz]; exact hc.v r hr
  · -- The ciphertext and the tag.
    show encryptWith _ _ 16 _ _ _ = (bytesAt z.mem (Dst s) (L s), bytesAt z.mem (Tg s) 16)
    rw [mz]
    have hfc : Frame [FR s, dR s] s.mem (gMem s) :=
      ((frame_eMem s).mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
        (h.frame_gMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
    have apart {r : Region} (h₁ : (⟨Bs s, 2592⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right (stk_sub s 2576 16 (by decide))
      · exact h₂
    obtain ⟨hc', hh⟩ := ctx_frame hfc (apart h.bk kd) hR
    have hn : bytesAt (gMem s) (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
      bytesAt_frame hfc (apart h.bn nd) (by omega)
    have ha : bytesAt (gMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
      bytesAt_frame hfc (apart h.ba ad) (by omega)
    have hd : bytesAt (gMem s) (Dst s) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; exact (stackArg s 1).isLt)
    have := hc.out
    rw [hc', hh, hn, ha, hd] at this
    exact this

theorem sealGather_wp (F : SealFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGather F.fn) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.w₁; omega) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  refine WP.seq (WP.mono (called_wp F h hc) fun s' hs' => ?_)
  exact ret_wp h hs'

end VG.Proof.AesGcm.AArch64.Gather
