module

public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenSplit.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Fn
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenSplit.Contract
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM decryption out of place, in one pass, AArch64: the call

Untrusted: everything here is checked by Lean. `openToSplit f` (`Impl.AesGcm.AArch64.OpenTo`)
with `openTo 3`'s arguments, for a 12-byte nonce and at most 16 bytes of
additional data (`SPre`), and `f` an implementation of
`vg_aes_gcm_open_split_with_powers` with its contract with 2608 bytes of
stack (`SplitFn`).

With `B` the base of the 2656 bytes of stack below the stack pointer
(`sp = B + 2656`), it allocates its frame of 48 bytes at `P = B + 2608`: the
call's five stack arguments (`tag`, `tag_len`, `pw`, `src`, `len`) at `P`,
…, `P + 32`, and our return address at `P + 40` (`entered_wp`). It puts
`dst` in `x6`, calls the function (`called_wp`), which reads the ciphertext
at `src`, writes only `dst` and the stack below `P`, and keeps our frame,
and zeroes `dst` if it returned 0 (`after_ok`, as `openTo`'s).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.OpenTo

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.OpenTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Proof.AesGcm.AArch64 (bytesAt_frame covers_of_mem covers_cons covers_append covers_prefix covers_nil)
open VG.Proof.AesGcm.AArch64.Gather (add_ofNat_sub_ofNat contains_off ldrSp_ok)

/-- An implementation of `vg_aes_gcm_open_split_with_powers`, by its contract,
whose frames use at most its 2608 bytes of stack. -/
structure SplitFn where
  fn : Fn
  verified : Verified AArch64.target fn.code (OpenSplit.contract AArch64.abi 2608)
  depth : 16 * fn.code.aarch64Depth ≤ 2608

section
variable (s : State)

/-- The powers' buffer, our stack argument 4. -/
abbrev pR : Region := ⟨stackArg s 4, 128⟩
/-- The stack below the stack pointer, its base, and our frame. -/
abbrev stk2 : Region := ⟨s.sp - BitVec.ofNat 64 2656, 2656⟩
abbrev B2 : Addr := s.sp - BitVec.ofNat 64 2656
abbrev P2 : Addr := B2 s + BitVec.ofNat 64 2608
abbrev FR2 : Region := ⟨B2 s + BitVec.ofNat 64 2608, 48⟩

end

/-- What `openToSplit` needs: `openTo 3`'s layout, with 2656 bytes of stack
apart from the buffers, a 12-byte nonce and at most 16 bytes of additional
data. -/
structure SPre (s : State) : Prop where
  to : ToPre pwShape s
  w : 2656 ≤ s.sp.toNat
  bk : (stk2 s).Disjoint (kR s)
  bn : (stk2 s).Disjoint (nR s)
  ba : (stk2 s).Disjoint (aR s)
  bs : (stk2 s).Disjoint (sR s)
  bd : (stk2 s).Disjoint (dR s)
  bt : (stk2 s).Disjoint (tR s)
  bp : (stk2 s).Disjoint (pR s)
  barg : (stk2 s).Disjoint (argR s 3)
  nl : NL s = 12
  al : AL s ≤ 16

/-- The memory once the entry has stored our return address and the call's
five stack arguments. -/
def sMem (s : State) : Mem :=
  (((((s.mem.write (P2 s + BitVec.ofNat 64 40) 8 (s.gpr .x30)).write (P2 s + BitVec.ofNat 64 0) 8
    (stackArg s 2)).write (P2 s + BitVec.ofNat 64 8) 8 (stackArg s 3)).write (P2 s + BitVec.ofNat 64 16) 8
    (stackArg s 4)).write (P2 s + BitVec.ofNat 64 24) 8 (s.gpr .x6)).write (P2 s + BitVec.ofNat 64 32) 8
    (s.gpr .x7)

/-! ## The layout -/

/-- What `SPre` gives, with the stack below the stack pointer at `B2 s`. -/
structure SLay (s : State) : Prop where
  pre : SPre s
  hB : s.sp = B2 s + BitVec.ofNat 64 2656
  hBn : (B2 s).toNat + 2656 + 40 ≤ 2 ^ 64
  hargR : argR s 3 = ⟨B2 s + BitVec.ofNat 64 2656, 40⟩

theorem slay {s : State} (hs : SPre s) : SLay s := by
  have hB : s.sp = B2 s + BitVec.ofNat 64 2656 := (BitVec.sub_add_cancel s.sp _).symm
  have hBx : (B2 s).toNat + 2656 + 40 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (B2 s).isLt
    have := hs.w
    have := hs.to.w₂
    simp only [pwShape] at this
    omega_arith
  refine ⟨hs, hB, hBx, ?_⟩
  simp only [argR, stackArgAddr, hB, pwShape, Nat.mul_zero, BitVec.add_zero]

namespace SLay

variable {s : State} (h : SLay s)
include h

theorem sA (i : Nat) : stackArgAddr s i = B2 s + BitVec.ofNat 64 (2656 + 8 * i) := by
  rw [stackArgAddr, h.hB, Offset.add_ofNat_add_ofNat]

theorem argIn : argR s 3 ∈ s.rd := by rw [h.pre.to.rd]; simp [pwShape]

theorem inArg (d : Nat) (h₁ : 2656 ≤ d) (h₂ : d + 8 ≤ 2696) (rs : List Region) :
    InRegions (s.rd ++ rs) (B2 s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_append_left _ h.argIn, by
    rw [h.hargR]; exact contains_off _ h₁ (by omega_arith) (by have := h.hBn; omega_arith)⟩

theorem inFR (d : Nat) (h₁ : 2608 ≤ d) (h₂ : d + 8 ≤ 2656) (rs : List Region) :
    InRegions (FR2 s :: rs) (B2 s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., contains_off _ h₁ (by omega_arith) (by have := h.hBn; omega_arith)⟩

theorem sep (d e : Nat) (h₁ : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2696) (he : e + 8 ≤ 2696) :
    Mem.Sep (B2 s + BitVec.ofNat 64 d) 8 (B2 s + BitVec.ofNat 64 e) 8 :=
  Offset.sep _ h₁ (by have := h.hBn; omega_arith) (by have := h.hBn; omega_arith)

/-- Our stack argument `i`, read from `s.mem`. -/
theorem sa (i : Nat) : s.mem.read (B2 s + BitVec.ofNat 64 (2656 + 8 * i)) 8 = stackArg s i := by
  rw [← h.sA]; rfl

end SLay

/-- The entry writes only our frame. -/
theorem frame_sMem (s : State) : Frame [FR2 s] s.mem (sMem s) := by
  have c (d : Nat) (hd : d + 8 ≤ 48) : (FR2 s).Contains (P2 s + BitVec.ofNat 64 d) 8 := by
    show (FR2 s).Contains (B2 s + BitVec.ofNat 64 2608 + BitVec.ofNat 64 d) 8
    rw [Offset.add_ofNat_add_ofNat]
    exact contains_off _ (by omega_arith) (by omega_arith) (by omega_arith)
  unfold sMem
  exact ((((((Frame.refl _ _).write (List.mem_singleton_self _) _ (c 40 (by decide))).write
    (List.mem_singleton_self _) _ (c 0 (by decide))).write (List.mem_singleton_self _) _ (c 8 (by decide))).write
    (List.mem_singleton_self _) _ (c 16 (by decide))).write (List.mem_singleton_self _) _ (c 24 (by decide))).write
    (List.mem_singleton_self _) _ (c 32 (by decide))

/-! ## The entry -/

theorem splitEntry_eq : splitEntry = ([.addSp .x16 0, .str .x .x30 .x16 40] : List Instr) ++
    (([.ldrSp .x17 64, .str .x .x17 .x16 0] : List Instr) ++ (([.ldrSp .x17 72, .str .x .x17 .x16 8] : List Instr) ++
    (([.ldrSp .x17 80, .str .x .x17 .x16 16] : List Instr) ++
      ([.str .x .x6 .x16 24, .str .x .x7 .x16 32, .ldrSp .x6 48] : List Instr)))) := rfl

/-- The end of the entry: `x6` and `x7` at `x16 + 24` and `x16 + 32`, and
the doubleword at `sp + 48` in `x6`. -/
theorem tailS_ok (a : State) (w₂₄ : InRegions a.wr (a.gpr .x16 + BitVec.ofNat 64 24) 8)
    (w₃₂ : InRegions a.wr (a.gpr .x16 + BitVec.ofNat 64 32) 8)
    (r : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 48) 8) :
    WP isa (.block [.str .x .x6 .x16 24, .str .x .x7 .x16 32, .ldrSp .x6 48]) a fun e =>
      e.mem = (a.mem.write (a.gpr .x16 + BitVec.ofNat 64 24) 8 (a.gpr .x6)).write
        (a.gpr .x16 + BitVec.ofNat 64 32) 8 (a.gpr .x7) ∧
      e.gpr .x6 = ((a.mem.write (a.gpr .x16 + BitVec.ofNat 64 24) 8 (a.gpr .x6)).write
        (a.gpr .x16 + BitVec.ofNat 64 32) 8 (a.gpr .x7)).read (a.sp + BitVec.ofNat 64 48) 8 ∧
      (∀ r, r ≠ .x6 → e.gpr r = a.gpr r) ∧ e.sp = a.sp ∧ e.rd = a.rd ∧ e.wr = a.wr ∧ e.v = a.v := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write, sp_write, Option.bind_some,
      Option.map_some, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul,
      Nat.reduceMod, and_self, w₂₄, w₃₂, r]; rfl, rfl⟩ fun e he => ?_
  subst he
  exact ⟨by simp [State.write], by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

/-- After the entry. -/
structure SEntered (s e : State) : Prop where
  mem : e.mem = sMem s
  x6 : e.gpr .x6 = Dst s
  gpr : ∀ r, r ≠ .x6 → r ≠ .x16 → r ≠ .x17 → e.gpr r = s.gpr r
  sp : e.sp = P2 s
  rd : e.rd = s.rd
  wr : e.wr = FR2 s :: s.wr
  v : e.v = s.v

theorem sentered_wp {s : State} (h : SLay s) : WP isa (.block splitEntry) (allocated 48 s) (SEntered s) := by
  have asp : (allocated 48 s).sp = P2 s := by
    show s.sp - BitVec.ofNat 64 48 = _
    rw [h.hB, add_ofNat_sub_ofNat _ (by decide)]
  have awr : (allocated 48 s).wr = FR2 s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 48, 48⟩ :: s.wr : List Region) = _
    rw [show s.sp - BitVec.ofNat 64 48 = _ from asp]
  have hP (d : Nat) : P2 s + BitVec.ofNat 64 d = B2 s + BitVec.ofNat 64 (2608 + d) := Offset.add_ofNat_add_ofNat ..
  have fr : ∀ {m : Mem}, Frame [FR2 s] s.mem m → ∀ i, 2 ≤ i → i < 5 →
      m.read (B2 s + BitVec.ofNat 64 (2656 + 8 * i)) 8 = stackArg s i := fun hm i h₂ h₅ => by
    rw [← h.sa i]
    refine Frame.read hm (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by have := h.hBn; omega_arith)
  have cFR (d : Nat) (hd : d + 8 ≤ 48) : (FR2 s).Contains (P2 s + BitVec.ofNat 64 d) 8 := by
    rw [hP]; exact contains_off _ (by omega_arith) (by omega_arith) (by have := h.hBn; omega_arith)
  rw [splitEntry_eq, WP.block_append_iff]
  have w₄₀ : InRegions (allocated 48 s).wr ((allocated 48 s).sp + BitVec.ofNat 64 40) 8 := by
    rw [awr, asp, hP]; exact h.inFR _ (by decide) (by decide) _
  refine WP.mono (head_ok _ (k := 40) (by decide) (by decide) w₄₀) fun a ⟨ma, x16a, ga, spa, rda, wra, va⟩ => ?_
  rw [asp] at x16a spa
  rw [awr] at wra
  have f₀ : Frame [FR2 s] s.mem a.mem := by
    rw [ma, asp]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (cFR 40 (by decide))
  -- The three copies.
  have step (t : State) (i : Nat) (h₂ : 2 ≤ i) (h₅ : i < 5) (ft : Frame [FR2 s] s.mem t.mem)
      (x16t : t.gpr .x16 = P2 s) (spt : t.sp = P2 s) (rdt : t.rd = s.rd) (wrt : t.wr = FR2 s :: s.wr) :
      WP isa (.block [.ldrSp .x17 (48 + 16 + 8 * (i - 2)), .str .x .x17 .x16 (8 * (i - 2))]) t fun u =>
        u.mem = t.mem.write (P2 s + BitVec.ofNat 64 (8 * (i - 2))) 8 (stackArg s i) ∧
        (∀ r, r ≠ .x17 → u.gpr r = t.gpr r) ∧ u.sp = t.sp ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.v = t.v := by
    refine WP.mono (copyStep_ok t (o := 48 + 16 + 8 * (i - 2)) (k := 8 * (i - 2)) (by omega) (by omega) (by omega)
      (by omega) ?_ ?_) fun u ⟨mu, gu, spu, rdu, wru, vu⟩ => ⟨?_, gu, spu, rdu, wru, vu⟩
    · rw [spt, rdt, hP]; exact h.inArg _ (by omega_arith) (by omega_arith) _
    · rw [x16t, wrt]; exact ⟨_, List.mem_cons_self .., cFR _ (by omega)⟩
    · rw [mu, x16t, spt, hP (48 + 16 + 8 * (i - 2)), show 2608 + (48 + 16 + 8 * (i - 2)) = 2656 + 8 * i by omega,
        fr ft i h₂ h₅]
  rw [WP.block_append_iff]
  refine WP.mono (step a 2 (by decide) (by decide) f₀ x16a spa rda wra) fun b ⟨mb, gb, spb, rdb, wrb, vb⟩ => ?_
  have f₁ : Frame [FR2 s] s.mem b.mem := by
    rw [mb]; exact f₀.write (List.mem_singleton_self _) _ (cFR 0 (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (step b 3 (by decide) (by decide) f₁ (by rw [gb _ (by decide), x16a]) (spb.trans spa)
    (rdb.trans rda) (wrb.trans wra)) fun c ⟨mc, gc, spc, rdc, wrc, vc⟩ => ?_
  have f₂ : Frame [FR2 s] s.mem c.mem := by
    rw [mc]; exact f₁.write (List.mem_singleton_self _) _ (cFR 8 (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (step c 4 (by decide) (by decide) f₂ (by rw [gc _ (by decide), gb _ (by decide), x16a])
    (spc.trans (spb.trans spa)) (rdc.trans (rdb.trans rda)) (wrc.trans (wrb.trans wra)))
    fun d ⟨md, gd, spd, rdd, wrd, vd⟩ => ?_
  have x16d : d.gpr .x16 = P2 s := by rw [gd _ (by decide), gc _ (by decide), gb _ (by decide), x16a]
  have spd' : d.sp = P2 s := spd.trans (spc.trans (spb.trans spa))
  have rdd' : d.rd = s.rd := rdd.trans (rdc.trans (rdb.trans rda))
  have wrd' : d.wr = FR2 s :: s.wr := wrd.trans (wrc.trans (wrb.trans wra))
  have gd' : ∀ r, r ≠ .x16 → r ≠ .x17 → d.gpr r = s.gpr r := fun r h₁₆ h₁₇ => by
    rw [gd r h₁₇, gc r h₁₇, gb r h₁₇, ga r h₁₆]; rfl
  refine WP.mono (tailS_ok d (by rw [x16d, wrd']; exact ⟨_, List.mem_cons_self .., cFR 24 (by decide)⟩)
    (by rw [x16d, wrd']; exact ⟨_, List.mem_cons_self .., cFR 32 (by decide)⟩)
    (by rw [spd', rdd', hP]; exact h.inArg _ (by decide) (by decide) _)) fun e ⟨me, x6e, ge, spe, rde, wre, ve⟩ => ?_
  have hm : e.mem = sMem s := by
    rw [me, md, mc, mb, ma, x16d, asp, gd' .x6 (by decide) (by decide), gd' .x7 (by decide) (by decide)]
    rfl
  refine ⟨hm, ?_, fun r h₆ h₁₆ h₁₇ => by rw [ge r h₆, gd' r h₁₆ h₁₇], spe.trans spd', rde.trans rdd',
    wre.trans wrd', by rw [ve, vd, vc, vb, va]; rfl⟩
  rw [x6e, ← me, hm, spd', hP]
  show (sMem s).read (B2 s + BitVec.ofNat 64 (2656 + 8 * 0)) 8 = stackArg s 0
  rw [← h.sa 0]
  refine Frame.read (frame_sMem s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by have := h.hBn; omega_arith)

/-! ## The function called -/

theorem stackArgs_five' (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

/-- The precondition of `vg_aes_gcm_open_split_with_powers` with 2608 bytes of
stack, as the call lays it out. -/
def callSPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let dst : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let pw : Region := ⟨stackArg s 2, 128⟩
  let src : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
  let args : Region := ⟨stackArgAddr s 0, 40⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 2608, 2608⟩
  2608 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 64 ∧
    s.rd = [ctx, nonce, aad, tag, pw, src, args] ∧ s.wr = [dst] ∧
    ctx.Disjoint dst ∧ nonce.Disjoint dst ∧ aad.Disjoint dst ∧ dst.Disjoint tag ∧ dst.Disjoint pw ∧
    dst.Disjoint src ∧ dst.Disjoint args ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint dst ∧ stk.Disjoint tag ∧
    stk.Disjoint pw ∧ stk.Disjoint src ∧ stk.Disjoint args ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + 128 ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) ∧
    Spec.Gcm.Powers8Repr s.mem (stackArg s 2) (ctxH s.mem (s.gpr .x0)) ∧
    (stackArg s 4).toNat = (s.gpr .x7).toNat ∧ (s.gpr .x3).toNat = 12 ∧ (s.gpr .x5).toNat ≤ 16

theorem splitSpec_pre {s : State} (h : callSPre s) : (OpenSplit.contract AArch64.abi 2608).pre s := by
  sig_pre [OpenSplit.contract, OpenSplit.sig, OpenSplit.pre, AArch64.abi, AArch64.argRegs,
    stackArgs_five', List.append_eq, List.range, List.range.loop]
  sig_reduce [OpenSplit.contract, OpenSplit.sig, AArch64.abi, AArch64.argRegs, List.getD,
    List.range, List.range.loop]
  exact h

/-- `vg_aes_gcm_open`'s result on the ciphertext at the call's `src`. -/
abbrev callSRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

theorem splitSpec_post {s s' : State} (h : (OpenSplit.contract AArch64.abi 2608).post s s')
    (hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) :
    match callSRes s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 := by
  sig_post [OpenSplit.contract, OpenSplit.sig, OpenSplit.post, AArch64.abi, AArch64.argRegs,
    stackArgs_five', List.append_eq, List.range, List.range.loop] at h
  exact h hR

/-- The public data of a call: whether it succeeds. -/
def callSLeak (s : State) : List Nat :=
  if ¬((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) then []
  else [if (callSRes s).isSome = true then 1 else 0]

theorem splitSpec_pub {s₁ s₂ : State} (h : s₁.sp = s₂.sp ∧ callSLeak s₁ = callSLeak s₂ ∧
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧
    ∀ i < 5, stackArg s₁ i = stackArg s₂ i) :
    (OpenSplit.contract AArch64.abi 2608).pub s₁ s₂ := by
  sig_pub [OpenSplit.contract, OpenSplit.sig, OpenSplit.leak, AArch64.abi, AArch64.argRegs,
    stackArgs_five', List.append_eq, List.range, List.range.loop]
  sig_reduce [OpenSplit.contract, OpenSplit.sig, OpenSplit.leak, AArch64.abi, AArch64.argRegs,
    List.range, List.range.loop]
  obtain ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, a⟩ := h
  exact ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, a 0 (by decide), a 1 (by decide), a 2 (by decide),
    a 3 (by decide), a 4 (by decide)⟩

/-! ## The call -/

namespace SLay

variable {s : State} (h : SLay s)
include h

theorem rw_sep {d e : Nat} (h₁ : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2696) (he : e + 8 ≤ 2696) (m : Mem)
    (v : BitVec (8 * 8)) :
    (m.write (B2 s + BitVec.ofNat 64 e) 8 v).read (B2 s + BitVec.ofNat 64 d) 8 = m.read (B2 s + BitVec.ofNat 64 d) 8 :=
  Mem.read_write_sep (h.sep d e h₁ hd he) (by decide)

/-- What the entry stored in our frame. -/
theorem sMem_read :
    (sMem s).read (B2 s + BitVec.ofNat 64 2608) 8 = stackArg s 2 ∧
    (sMem s).read (B2 s + BitVec.ofNat 64 2616) 8 = stackArg s 3 ∧
    (sMem s).read (B2 s + BitVec.ofNat 64 2624) 8 = stackArg s 4 ∧
    (sMem s).read (B2 s + BitVec.ofNat 64 2632) 8 = s.gpr .x6 ∧
    (sMem s).read (B2 s + BitVec.ofNat 64 2640) 8 = s.gpr .x7 ∧
    (sMem s).read (B2 s + BitVec.ofNat 64 2648) 8 = s.gpr .x30 := by
  simp only [sMem, P2, Offset.add_ofNat_add_ofNat, Nat.reduceAdd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.rw_sep (d := 2608) (e := 2640) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2608) (e := 2632) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2608) (e := 2624) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2608) (e := 2616) (by decide) (by decide) (by decide), read_write_self]
  · rw [h.rw_sep (d := 2616) (e := 2640) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2616) (e := 2632) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2616) (e := 2624) (by decide) (by decide) (by decide), read_write_self]
  · rw [h.rw_sep (d := 2624) (e := 2640) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2624) (e := 2632) (by decide) (by decide) (by decide), read_write_self]
  · rw [h.rw_sep (d := 2632) (e := 2640) (by decide) (by decide) (by decide), read_write_self]
  · rw [read_write_self]
  · rw [h.rw_sep (d := 2648) (e := 2640) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2648) (e := 2632) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2648) (e := 2624) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2648) (e := 2616) (by decide) (by decide) (by decide),
      h.rw_sep (d := 2648) (e := 2608) (by decide) (by decide) (by decide), read_write_self]

end SLay

/-- The regions the call reads and writes, and its state. -/
abbrev rdS (s : State) : List Region := [kR s, nR s, aR s, tR s, pR s, sR s, ⟨P2 s, 40⟩]
abbrev wrS (s : State) : List Region := [dR s]
abbrev xSS (s e : State) : State := e.callEntry.withRegions (rdS s) (wrS s)

namespace SEntered

variable {s e : State} (h : SLay s) (he : SEntered s e)

include he in
/-- The registers at the call. -/
theorem callGpr :
    (xSS s e).gpr .x0 = s.gpr .x0 ∧ (xSS s e).gpr .x1 = s.gpr .x1 ∧ (xSS s e).gpr .x2 = s.gpr .x2 ∧
      (xSS s e).gpr .x3 = s.gpr .x3 ∧ (xSS s e).gpr .x4 = s.gpr .x4 ∧ (xSS s e).gpr .x5 = s.gpr .x5 ∧
      (xSS s e).gpr .x6 = Dst s ∧ (xSS s e).gpr .x7 = s.gpr .x7 := by
  have cg (r : Reg) (h₀ : r ∉ linkRegs) (h₆ : r ≠ .x6) (h₁₆ : r ≠ .x16) (h₁₇ : r ≠ .x17) :
      (xSS s e).gpr r = s.gpr r := by
    simp only [State.withRegions_gpr]; rw [e.callEntry_gpr h₀, he.gpr r h₆ h₁₆ h₁₇]
  exact ⟨cg _ (by decide) (by decide) (by decide) (by decide), cg _ (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide), cg _ (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide), cg _ (by decide) (by decide) (by decide) (by decide),
    by simp only [State.withRegions_gpr]; rw [e.callEntry_gpr (by decide), he.x6],
    cg _ (by decide) (by decide) (by decide) (by decide)⟩

include h he in
/-- The call's stack arguments: `tag`, `tag_len`, `pw`, `src` and `len`. -/
theorem stackArgs :
    stackArg (xSS s e) 0 = stackArg s 2 ∧ stackArg (xSS s e) 1 = stackArg s 3 ∧
      stackArg (xSS s e) 2 = stackArg s 4 ∧ stackArg (xSS s e) 3 = s.gpr .x6 ∧
      stackArg (xSS s e) 4 = s.gpr .x7 := by
  have r := h.sMem_read
  have a (i : Nat) : stackArg (xSS s e) i = (sMem s).read (B2 s + BitVec.ofNat 64 (2608 + 8 * i)) 8 := by
    simp only [stackArg, stackArgAddr, State.withRegions_sp, State.withRegions_mem, State.callEntry_sp,
      State.callEntry_mem, he.sp, he.mem, P2, Offset.add_ofNat_add_ofNat, Mem.readW, BitVec.setWidth_eq,
      Nat.reduceDiv]
  exact ⟨(a 0).trans r.1, (a 1).trans r.2.1, (a 2).trans r.2.2.1, (a 3).trans r.2.2.2.1, (a 4).trans r.2.2.2.2.1⟩

include he in
theorem sad0 : stackArgAddr (xSS s e) 0 = P2 s := by
  simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, he.sp, Nat.mul_zero, BitVec.add_zero]

include h in
theorem P2_toNat : (P2 s).toNat = (B2 s).toNat + 2608 := by
  have := h.hBn
  show (B2 s + BitVec.ofNat 64 2608).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

theorem P2_sub : P2 s - BitVec.ofNat 64 2608 = B2 s := by
  show B2 s + BitVec.ofNat 64 2608 - BitVec.ofNat 64 2608 = B2 s
  rw [add_ofNat_sub_ofNat _ (by decide), Nat.sub_self, BitVec.add_zero]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub2 (d n : Nat) (h' : d + n ≤ 2656) : (⟨B2 s + BitVec.ofNat 64 d, n⟩ : Region).Sub (stk2 s) := by
  show (⟨B2 s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨s.sp - BitVec.ofNat 64 2656, 2656⟩
  exact Offset.sub_base _ h'

/-- The regions apart from the stack below the stack pointer: apart from our frame. -/
theorem apart2 {r : Region} (h₁ : (stk2 s).Disjoint r) : ∀ r' ∈ [FR2 s], r.Disjoint r' := by
  intro r' hr'
  simp only [List.mem_singleton] at hr'; subst hr'
  exact h₁.symm.sub_right (stk_sub2 (s := s) 2608 48 (by decide))

include h he in
/-- What the call needs, and that it may read and write what it does. -/
theorem call : callSPre (xSS s e) ∧ Covers (rdS s ++ wrS s) (e.rd ++ e.wr) ∧ Covers (wrS s) e.wr := by
  have pre := h.pre
  have to := pre.to
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := he.callGpr
  obtain ⟨a0, a1, a2, a3, a4⟩ := he.stackArgs h
  have hPn := P2_toNat h
  have bsub (r : Region) (hr : (stk2 s).Disjoint r) : (⟨B2 s, 2608⟩ : Region).Disjoint r :=
    hr.sub_left (by
      have := stk_sub2 (s := s) 0 2608 (by decide)
      rwa [BitVec.add_zero] at this)
  have stkArg : (⟨B2 s, 2608⟩ : Region).Disjoint ⟨P2 s, 40⟩ := by
    have := Offset.disjoint (B2 s) (d := 0) (n := 2608) (e := 2608) (k := 40) (.inl (by decide)) (by decide)
      (by have := h.hBn; omega_arith)
    rwa [BitVec.add_zero] at this
  have argSub : (⟨P2 s, 40⟩ : Region).Sub (stk2 s) := stk_sub2 (s := s) 2608 40 (by decide)
  have dp : (dR s).Disjoint (pR s) := to.dx _ (by simp [pwShape, pwR, ourX])
  have op : (pR s).base.toNat + (pR s).len ≤ 2 ^ 64 := to.ox _ (by simp [pwShape, pwR, ourX])
  have bpX : pwShape.X s.mem (K s) (ourX s pwShape.n) := to.X
  have rep : Spec.Gcm.Powers8Repr (sMem s) (stackArg s 4) (ctxH (sMem s) (K s)) := by
    have := pwX_frame (frame_sMem s) (apart2 pre.bk)
      (fun x hx => by
        simp only [pwR, ourX, pwShape, List.map_cons, List.map_nil, List.mem_singleton, Nat.reduceSub,
          List.range_one] at hx
        subst hx; exact apart2 pre.bp)
      (fun x hx => by
        simp only [pwR, ourX, pwShape, List.map_cons, List.map_nil, List.mem_singleton, Nat.reduceSub,
          List.range_one] at hx
        subst hx; exact op) bpX
    exact this _ (by simp [pwShape, ourX])
  refine ⟨?_, ?_, ?_⟩
  · simp only [callSPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.withRegions_mem, State.callEntry_sp, State.callEntry_mem, c0, c1, c2, c3, c4, c5, c6, c7,
      a0, a1, a2, a3, a4, sad0 he, he.sp, P2_sub, he.mem]
    refine ⟨by omega, by have := h.hBn; omega, trivial, trivial, to.kd, to.nd, to.ad, to.dt, dp, to.sd.symm,
      (pre.bd.symm.sub_right argSub), bsub _ pre.bk, bsub _ pre.bn, bsub _ pre.ba, bsub _ pre.bd, bsub _ pre.bt,
      bsub _ pre.bp, bsub _ pre.bs, stkArg, to.ok, to.on, to.oa, to.od, to.ot, op, to.os, to.hR, rep, trivial,
      pre.nl, pre.al⟩
  · have inRd {r : Region} (h' : r ∈ s.rd) : Covers [r] (e.rd ++ e.wr) :=
      covers_of_mem (List.mem_append_left _ (by rw [he.rd]; exact h'))
    have hfr : Covers [FR2 s] (e.rd ++ e.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [he.wr]; exact List.mem_cons_self ..))
    have hw' : Covers [dR s] (e.rd ++ e.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [he.wr, to.wr]; simp))
    exact covers_append (covers_cons (inRd (r := kR s) (by rw [to.rd]; simp))
      (covers_cons (inRd (r := nR s) (by rw [to.rd]; simp))
      (covers_cons (inRd (r := aR s) (by rw [to.rd]; simp))
      (covers_cons (inRd (r := tR s) (by rw [to.rd]; simp))
      (covers_cons (inRd (r := pR s) (by rw [to.rd]; simp [pwShape, pwR, ourX]))
      (covers_cons (inRd (r := sR s) (by rw [to.rd]; simp))
      (covers_cons (covers_prefix hfr (by decide)) covers_nil)))))))
      (covers_cons hw' covers_nil)
  · rw [he.wr, to.wr]
    exact covers_cons (covers_of_mem (by simp)) covers_nil

include h he in
/-- The call's result is `res`. -/
theorem xres : callSRes (xSS s e) = res s := by
  have pre := h.pre
  have to := pre.to
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := he.callGpr
  obtain ⟨a0, a1, a2, a3, a4⟩ := he.stackArgs h
  have hf := frame_sMem s
  obtain ⟨hc, hh⟩ := Proof.AesGcm.ctx_frame hf (apart2 pre.bk) to.hR
  have hn : bytesAt (sMem s) (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
    bytesAt_frame hf (apart2 pre.bn) (by have := to.on; omega_arith)
  have ha : bytesAt (sMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
    bytesAt_frame hf (apart2 pre.ba) (by have := to.oa; omega_arith)
  have ht : bytesAt (sMem s) (Tg s) (TL s) = bytesAt s.mem (Tg s) (TL s) :=
    bytesAt_frame hf (apart2 pre.bt) (by have := to.ot; omega_arith)
  have hs : bytesAt (sMem s) (Src s) (L s) = bytesAt s.mem (Src s) (L s) :=
    bytesAt_frame hf (apart2 pre.bs) (by have := to.os; omega_arith)
  simp only [callSRes, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3, c4, c5,
    a0, a1, a2, a3, a4, he.mem]
  rw [hc, hh, hn, ha, ht, hs]

end SEntered

/-- After the call. -/
structure SCalled (s z : State) : Prop where
  fr : Frame [dR s, ⟨B2 s, 2608⟩] (sMem s) z.mem
  ra : z.mem.read (B2 s + BitVec.ofNat 64 2648) 8 = s.gpr .x30
  out : match res s with
    | some pt => (z.gpr .x0).setWidth 32 = 1 ∧ bytesAt z.mem (Dst s) (L s) = pt
    | none => (z.gpr .x0).setWidth 32 = 0
  gpr : ∀ r ∈ preserved, r ≠ .x30 → z.gpr r = s.gpr r
  sp : z.sp = P2 s
  rd : z.rd = s.rd
  wr : z.wr = FR2 s :: s.wr
  v : ∀ r ∈ preservedV, (z.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem scalled_wp (F : SplitFn) {s e : State} (h : SLay s) (he : SEntered s e) :
    WP isa (.call F.fn.name F.fn.code) e (SCalled s) := by
  obtain ⟨hcp, hcov, hw⟩ := he.call h
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := he.callGpr
  have hdep := F.depth
  refine WP.callFV (name := F.fn.name) F.verified.1 (splitSpec_pre hcp) hcov hw
    (fun s' rd' wr' sp' fr' pres' presV' post' => ?_) (by omega_arith)
  have hpost := splitSpec_post post' (by rw [c1]; exact h.pre.to.hR)
  rw [he.xres h] at hpost
  have hpres : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x6 ∧ r ≠ .x16 ∧ r ≠ .x17 := by decide
  have hP : P2 s = B2 s + BitVec.ofNat 64 2608 := rfl
  have bl : below e.sp (16 * F.fn.code.aarch64Depth) =
      ⟨B2 s + BitVec.ofNat 64 (2608 - 16 * F.fn.code.aarch64Depth), 16 * F.fn.code.aarch64Depth⟩ := by
    simp only [below, he.sp, hP, add_ofNat_sub_ofNat _ (show 16 * F.fn.code.aarch64Depth ≤ 2608 by omega_arith)]
  -- What the call wrote: `dst` and the stack below our frame.
  have frc : Frame [dR s, ⟨B2 s, 2608⟩] (sMem s) s'.mem := by
    rw [← he.mem]
    refine fr'.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dR s, by simp, fun _ h => h⟩
    · refine ⟨⟨B2 s, 2608⟩, by simp, ?_⟩
      rw [bl]
      exact Offset.sub_base _ (by omega_arith)
  -- The return address, from the frame, which the call kept.
  have ra : s'.mem.read (B2 s + BitVec.ofNat 64 2648) 8 = s.gpr .x30 := by
    rw [← h.sMem_read.2.2.2.2.2, ← he.mem]
    refine Frame.read fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (h.pre.bd.symm.sub_right (SEntered.stk_sub2 (s := s) 2648 8 (by decide))).symm
    · rw [bl]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega) (by have := h.hBn; omega_arith)
  refine ⟨frc, ra, ?_, fun r hr h30 => by
      obtain ⟨h₆, h₁₆, h₁₇⟩ := hpres r hr h30
      rw [pres' r hr h30, he.gpr r h₆ h₁₆ h₁₇],
    sp'.trans he.sp, rd'.trans he.rd, wr'.trans he.wr, fun r hr => by rw [presV' r hr, he.v]⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, c6, c7] at hpost
  exact hpost

/-! ## After the call -/

/-- `wipeArgs 5`: our stack arguments `dst` and `dst_len`, at `sp + 48` and
`sp + 56`, into `x9` and `x10`, and zero into `x11`. -/
theorem wipeArgs5_ok (a : State) (r₄₈ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 48) 8)
    (r₅₆ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 56) 8) :
    WP isa (.block (wipeArgs 5)) a fun e =>
      e.gpr .x9 = a.mem.read (a.sp + BitVec.ofNat 64 48) 8 ∧
      e.gpr .x10 = a.mem.read (a.sp + BitVec.ofNat 64 56) 8 ∧ e.gpr .x11 = 0 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.sp = a.sp ∧
      e.rd = a.rd ∧ e.wr = a.wr ∧ e.v = a.v := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [wipeArgs, frameBytes, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits,
      Size.bytes, Option.map_some, BitVec.setWidth_eq, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, r₄₈, r₅₆,
      and_self, ite_true, Nat.reduceLT, Nat.reduceMod, Option.bind_some, gpr_write, mem_write, rd_write, wr_write,
      sp_write]; rfl, rfl⟩ fun e he => ?_
  subst he
  refine ⟨by simp [State.write], by simp [State.write], by simp [State.write], fun r h₁ h₂ h₃ => by
    simp [State.write, h₁, h₂, h₃], rfl, rfl, rfl, rfl, rfl⟩

/-- Where the wipe leaves the state: what follows the call, with `dst` as
`toPost` has it. -/
structure SDone (s u : State) : Prop where
  post : toPost s u
  ra : u.mem.read (B2 s + BitVec.ofNat 64 2648) 8 = s.gpr .x30
  gpr : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s.gpr r
  sp : u.sp = P2 s
  rd : u.rd = s.rd
  wr : u.wr = FR2 s :: s.wr
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- Our stack argument `i < 2`, after the call. -/
theorem SCalled.arg {s z : State} (h : SLay s) (hz : SCalled s z) (i : Nat) (hi : i < 2) :
    z.mem.read (B2 s + BitVec.ofNat 64 (2656 + 8 * i)) 8 = stackArg s i := by
  have to := h.pre.to
  have e₀ : (sMem s).read (B2 s + BitVec.ofNat 64 (2656 + 8 * i)) 8 = stackArg s i := by
    rw [← h.sa i]
    refine Frame.read (frame_sMem s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by have := h.hBn; omega_arith)
  rw [← e₀]
  refine Frame.read hz.fr (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  have da : (dR s).Disjoint (argR s 3) := to.da
  rw [h.hargR] at da
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (da.sub_right (Offset.sub _ (show 2656 ≤ 2656 + 8 * i by omega_arith) (by omega_arith))).symm
  · have := Offset.disjoint (B2 s) (d := 2656 + 8 * i) (n := 8) (e := 0) (k := 2608) (.inr (by omega_arith))
      (by omega_arith) (by have := h.hBn; omega_arith)
    rwa [BitVec.add_zero] at this

theorem swipeArgs_wp {s z : State} (h : SLay s) (hz : SCalled s z) : WP isa (.block (wipeArgs 5)) z (WArgs s z) := by
  have to := h.pre.to
  have hP : P2 s = B2 s + BitVec.ofNat 64 2608 := rfl
  have inA (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 8 ≤ 64) :
      InRegions (z.rd ++ z.wr) (z.sp + BitVec.ofNat 64 d) 8 := by
    rw [hz.sp, hP, Offset.add_ofNat_add_ofNat, hz.rd]
    exact h.inArg (2608 + d) (by omega_arith) (by omega_arith) _
  refine WP.mono (wipeArgs5_ok z (inA 48 (by decide) (by decide)) (inA 56 (by decide) (by decide)))
    fun a ⟨x9a, x10a, x11a, ga, ma, spa, rda, wra, va⟩ => ?_
  rw [hz.sp, hP, Offset.add_ofNat_add_ofNat,
    show B2 s + BitVec.ofNat 64 (2608 + 48) = B2 s + BitVec.ofNat 64 (2656 + 8 * 0) from rfl,
    hz.arg h 0 (by decide)] at x9a
  rw [hz.sp, hP, Offset.add_ofNat_add_ofNat,
    show B2 s + BitVec.ofNat 64 (2608 + 56) = B2 s + BitVec.ofNat 64 (2656 + 8 * 1) from rfl,
    hz.arg h 1 (by decide)] at x10a
  have hL : stackArg s 1 = BitVec.ofNat 64 (L s) := by
    apply BitVec.eq_of_toNat_eq; rw [to.dl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s.gpr .x7).isLt]
  rw [hL] at x10a
  exact ⟨x9a, x10a, x11a, ga, ma, spa, rda, wra, va⟩

/-- When the call failed: `dst` zeroed. -/
theorem swipe_wp {s z : State} (h : SLay s) (hz : SCalled s z) (hres : res s = none) :
    WP isa (wipe 5) z (SDone s) := by
  have to := h.pre.to
  have x0 : (z.gpr .x0).setWidth 32 = 0 := by have := hz.out; rw [hres] at this; exact this
  unfold wipe
  refine WP.seq (WP.mono (swipeArgs_wp h hz) fun a ha => ?_)
  have hw : Covers [⟨Dst s, L s⟩] a.wr := by
    rw [ha.wr, hz.wr, to.wr]; exact covers_cons (covers_of_mem (by simp)) covers_nil
  refine WP.mono (wipeLoop_wp a (s.gpr .x7).isLt ha.x9 ha.x10 ha.x11 hw to.od)
    fun u ⟨pz, fu, gu, spu, rdu, wru, vu⟩ => ?_
  have g' : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → u.gpr r = z.gpr r := fun r a b c => by
    rw [gu r a b, ha.gpr r a b c]
  refine ⟨?_, ?_, fun r hr h30 => ?_, by rw [spu, ha.sp, hz.sp], by rw [rdu, ha.rd, hz.rd],
    by rw [wru, ha.wr, hz.wr], fun r hr => by rw [vu, ha.v]; exact hz.v r hr⟩
  · show match res s with | some pt => _ | none => _
    rw [hres]
    exact ⟨by rw [g' _ (by decide) (by decide) (by decide)]; exact x0, bytesAt_zeros pz⟩
  · rw [← hz.ra, ← ha.mem]
    refine Frame.read fu (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.pre.bd.symm.sub_right (SEntered.stk_sub2 (s := s) 2648 8 (by decide))).symm
  · have hp' : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by decide
    have := hp' r hr
    rw [g' r this.1 this.2.1 this.2.2]; exact hz.gpr r hr h30

/-- After the call: `dst` zeroed if it failed. -/
theorem safter_ok {s z : State} (h : SLay s) (hz : SCalled s z) : WP isa (after 5) z (SDone s) := by
  unfold after
  have hdone : res s ≠ none → SDone s z := fun hn => by
    obtain ⟨pt, hpt⟩ := Option.ne_none_iff_exists'.mp hn
    have o := hz.out
    rw [hpt] at o
    refine ⟨?_, hz.ra, hz.gpr, hz.sp, hz.rd, hz.wr, hz.v⟩
    show match res s with | some pt => _ | none => _
    rw [hpt]; exact o
  cases hr : res s with
  | none =>
    have x0 : (z.gpr .x0).setWidth 32 = 0 := by have := hz.out; rw [hr] at this; exact this
    exact WP.ite true (by show some (_ == _) = _; rw [show z.read .w .x0 = 0 from x0]; rfl)
      (fun _ => swipe_wp h hz hr) (fun h' => absurd h' (by decide))
  | some pt =>
    have x0 : (z.gpr .x0).setWidth 32 = 1 := by have := hz.out; rw [hr] at this; exact this.1
    exact WP.ite false (by show some (_ == _) = _; rw [show z.read .w .x0 = 1 from x0]; rfl)
      (fun h' => absurd h' (by decide)) (fun _ => WP.block_nil (hdone (by rw [hr]; simp)))

/-- Our return address back in `x30`, and the frame freed. -/
theorem sret_wp {s u : State} (h : SLay s) (hu : SDone s u) :
    WP isa (.block (ret 5)) u fun z => abiPreserved s (freed 48 z) ∧ toPost s (freed 48 z) := by
  have hP : P2 s = B2 s + BitVec.ofNat 64 2608 := rfl
  refine WP.mono (ldrSp_ok (t := .x30) (k := 40) u ⟨by decide, by decide⟩ ?_)
    fun z ⟨x30z, gz, mz, spz, rdz, wrz, vz⟩ => ?_
  · rw [hu.sp, hu.rd, hu.wr, hP, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
      contains_off _ (by decide) (by decide) (by have := h.hBn; omega_arith)⟩
  rw [hu.sp, hP, Offset.add_ofNat_add_ofNat, hu.ra] at x30z
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · show z.gpr r = s.gpr r
    by_cases h30 : r = .x30
    · subst h30; exact x30z
    · rw [gz r h30, hu.gpr r hr h30]
  · show z.sp + BitVec.ofNat 64 48 = s.sp
    rw [spz, hu.sp, hP, Offset.add_ofNat_add_ofNat, h.hB]
  · show (z.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
    rw [vz]; exact hu.v r hr
  · have p := hu.post
    show match res s with | some pt => _ | none => _
    revert p
    show (match res s with | some pt => _ | none => _) → _
    cases res s with
    | some pt => intro p; exact ⟨by show (z.gpr .x0).setWidth 32 = _; rw [gz _ (by decide)]; exact p.1,
        by show bytesAt z.mem _ _ = _; rw [mz]; exact p.2⟩
    | none => intro p; exact ⟨by show (z.gpr .x0).setWidth 32 = _; rw [gz _ (by decide)]; exact p.1,
        by show bytesAt z.mem _ _ = _; rw [mz]; exact p.2⟩

theorem openToSplit_wp (F : SplitFn) {s : State} (hs : SPre s) :
    WP isa (openToSplit F.fn) s fun z => abiPreserved s z ∧ toPost s z := by
  have h := slay hs
  unfold openToSplit
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hs.w; omega_arith) ?_
  refine WP.seq (WP.mono (sentered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (scalled_wp F h he) fun z hz => ?_)
  exact WP.seq (WP.mono (safter_ok h hz) fun u hu => sret_wp h hu)

/-! ## Constant time -/

open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint rel_ite ct_of)

/-- The call's public data, from the arguments. -/
theorem SEntered.leak {s e : State} (h : SLay s) (he : SEntered s e) : callSLeak (xSS s e) = toLeak s := by
  obtain ⟨-, c1, -, -, -, -, -, -⟩ := he.callGpr
  simp only [callSLeak, toLeak, he.xres h, State.withRegions_gpr, c1]

/-- Whether the call failed, from what it left. -/
theorem SCalled.zero {s z : State} (hz : SCalled s z) : ((z.gpr .x0).setWidth 32 == 0) = (res s).isNone := by
  have ho := hz.out
  revert ho
  cases res s with
  | some pt => intro ho; rw [ho.1]; rfl
  | none => intro ho; rw [ho]; rfl

theorem openToSplit_rel (F : SplitFn) {σ₁ σ₂ : State} (p₁ : SPre σ₁) (p₂ : SPre σ₂)
    (hq : toPub 3 σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (openToSplit F.fn) TT := by
  have h₁ := slay p₁
  have h₂ := slay p₂
  obtain ⟨qsp, ql, q0, q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  have a0 := qa 0 (by omega)
  have a2 := qa 2 (by omega)
  have a3 := qa 3 (by omega)
  have a4 := qa 4 (by omega)
  unfold openToSplit
  have hB : B2 σ₁ = B2 σ₂ := by simp only [B2, qsp]
  have hP : P2 σ₁ = P2 σ₂ := by simp only [P2, hB]
  have asp (σ : State) (h : SLay σ) : (allocated 48 σ).sp = P2 σ := by
    show σ.sp - BitVec.ofNat 64 48 = _
    rw [h.hB, add_ofNat_sub_ofNat _ (by decide)]
  refine (RelCT.alloc (P := Eq2 σ₁ σ₂) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocated 48 σ₁) (allocated 48 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (by rw [asp _ h₁, asp _ h₂, hP]) (by agree_tac []) ⟨_, by taint_decide⟩)
    (sentered_wp h₁) (sentered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdS σ₂ = rdS σ₁ := by
    simp only [rdS, kR, nR, aR, tR, pR, sR, K, Nn, NL, Ad, AL, Tg, TL, Src, L, q0, q2, q3, q4, q5, q6, q7, a2, a3,
      a4, hP]
  have hwr : wrS σ₂ = wrS σ₁ := by simp only [wrS, dR, Dst, L, a0, q7]
  obtain ⟨cp₁, cv₁, cw₁⟩ := he₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := he₂.call h₂
  have lk₁ := he₁.leak h₁
  have lk₂ := he₂.leak h₂
  have hx₂ : xSS σ₂ e₂ = e₂.callEntry.withRegions (rdS σ₁) (wrS σ₁) := by rw [← hrd, ← hwr]
  rw [hx₂] at cp₂ lk₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  obtain ⟨r0₁, r1₁, r2₁, r3₁, r4₁, r5₁, r6₁, r7₁⟩ := he₁.callGpr
  obtain ⟨r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, r7₂⟩ := he₂.callGpr
  obtain ⟨b0₁, b1₁, b2₁, b3₁, b4₁⟩ := he₁.stackArgs h₁
  obtain ⟨b0₂, b1₂, b2₂, b3₂, b4₂⟩ := he₂.stackArgs h₂
  rw [hx₂] at r0₂ r1₂ r2₂ r3₂ r4₂ r5₂ r6₂ r7₂ b0₂ b1₂ b2₂ b3₂ b4₂
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdS σ₁) (wrS σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨splitSpec_pre cp₁, splitSpec_pre cp₂, splitSpec_pub ⟨?_, by rw [lk₁, lk₂, ql], ?_⟩, cv₁, cw₁, cv₂,
        cw₂⟩
      · simp only [State.withRegions_sp, State.callEntry_sp, he₁.sp, he₂.sp, hP]
      · simp only [r0₁, r1₁, r2₁, r3₁, r4₁, r5₁, r6₁, r7₁, r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, r7₂, q0, q1, q2, q3,
          q4, q5, q7, Dst, a0, true_and]
        intro i hi
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl
        · rw [b0₁, b0₂, a2]
        · rw [b1₁, b1₂, a3]
        · rw [b2₁, b2₂, a4]
        · rw [b3₁, b3₂, q6]
        · rw [b4₁, b4₂, q7])
    (scalled_wp F h₁ he₁) (scalled_wp F h₂ he₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- After the call: the same branch in both runs.
  have hn : (res σ₁).isNone = (res σ₂).isNone := by
    simp only [toLeak, p₁.to.hR, p₂.to.hR, not_true_eq_false, ↓reduceIte, List.cons.injEq, and_true] at ql
    revert ql
    cases res σ₁ <;> cases res σ₂ <;> simp
  have ev₁ : isa.eval (.zero .w .x0) z₁ = some (res σ₁).isNone := by
    show some (_ == _) = _; rw [← hz₁.zero]; rfl
  have ev₂ : isa.eval (.zero .w .x0) z₂ = some (res σ₁).isNone := by
    show some (_ == _) = _; rw [hn, ← hz₂.zero]; rfl
  refine rel_seq (rel_ite ev₁ ev₂ (fun _ => ?_) fun _ => ?_) (safter_ok h₁ hz₁) (safter_ok h₂ hz₂)
    fun u₁ u₂ hu₁ hu₂ => ?_
  · -- `wipe`, from the same public arguments.
    refine rel_seq (rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by agree_tac []) ⟨_, by taint_decide⟩)
      (swipeArgs_wp h₁ hz₁) (swipeArgs_wp h₂ hz₂) fun w₁ w₂ hw₁ hw₂ => ?_
    exact rel_taint [.x9, .x10] (by rw [hw₁.sp, hw₂.sp, hz₁.sp, hz₂.sp, hP])
      (by agree_tac [hw₁.x9, hw₂.x9, hw₁.x10, hw₂.x10, Dst, L, a0, q7]) ⟨_, by taint_decide⟩
  · exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by agree_tac []) ⟨_, by taint_decide⟩
  -- The return address.
  exact rel_taint [] (by rw [hu₁.sp, hu₂.sp, hP]) (by agree_tac []) ⟨_, by taint_decide⟩


theorem openToSplit_ct (F : SplitFn) :
    ConstantTime isa SPre (toPub 3) (openToSplit F.fn) :=
  ct_of fun _ _ p₁ p₂ hq => openToSplit_rel F p₁ p₂ hq

/-! ## `vg_aes_gcm_open_to_with_powers`, choosing on entry -/

open VG.Proof.AesGcm.AArch64.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

/-- The shared contract with 2656 bytes of stack gives `ToPre` and the 2656
bytes apart from the buffers. -/
theorem toPre2656 {s : State} (h : (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2656).pre s) :
    ToPre pwShape s ∧ 2656 ≤ s.sp.toNat ∧ (stk2 s).Disjoint (kR s) ∧ (stk2 s).Disjoint (nR s) ∧
      (stk2 s).Disjoint (aR s) ∧ (stk2 s).Disjoint (sR s) ∧ (stk2 s).Disjoint (dR s) ∧
      (stk2 s).Disjoint (tR s) ∧ (stk2 s).Disjoint (pR s) ∧ (stk2 s).Disjoint (argR s 3) := by
  sig_pre [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig,
    Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToSig, Spec.Gcm.withPowersParam, Spec.Gcm.openToPre,
    AArch64.abi, AArch64.argRegs, stackArgs_five, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [filter_true', filter_false', filterMap_some', filterMap_none', List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.filterMap_cons, List.filterMap_nil,
    List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
    List.cons_append, List.singleton_append, Sig.descRegion, Function.comp_def, Bool.not_false,
    Bool.false_eq_true, ite_true, ite_false, List.filter_nil] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, nd, ad, sd, dt, dp, da⟩, bk, bn, ba, bs, bd, bt, bp, barg, ok, on, oa, os, od, ot, op,
    hR, dl, rep⟩ := h
  rw [dl] at wr kd nd ad sd dt dp da bd od
  have sb := Offset.sub_below s.sp (a := 2624) (n := 2624) (b := 2656) (m := 2656) (by omega) (by omega)
  exact ⟨⟨by omega, w₂, rd, wr, kd, nd, ad, sd, dt, by simpa [pwShape, pwR] using dp, da, bk.sub_left sb,
    bn.sub_left sb, ba.sub_left sb, bs.sub_left sb, bd.sub_left sb, bt.sub_left sb,
    by simpa [pwShape, pwR] using bp.sub_left sb, barg.sub_left sb, ok, on, oa, os, od, ot,
    by simpa [pwShape, pwR] using op, hR, dl, by simpa [pwShape, pwX] using rep⟩, w₁, bk, bn, ba, bs, bd, bt,
    by simpa [pwShape, pwR] using bp, barg⟩

theorem toPost2656 {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2656).post s s' := by
  sig_post [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig, Spec.Gcm.openToSig,
    Spec.Gcm.withPowersParam, Proof.AesGcm.openToWithPowersRoundsPost, Proof.AesGcm.openToRoundsPost,
    AArch64.abi, AArch64.argRegs, stackArgs_five, List.append_eq]
  exact fun _ => h

theorem toPub2656 {s₁ s₂ : State}
    (hp : (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2656).pub s₁ s₂) : toPub 3 s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig, Spec.Gcm.openToSig,
    Spec.Gcm.withPowersParam, Spec.Gcm.openToWithPowersLeak, Spec.Gcm.openToLeak,
    AArch64.abi, AArch64.argRegs, stackArgs_five, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, a0, a1, a2, a3, a4⟩ := hp
  refine ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, fun i hi => ?_⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

/-- A state satisfying the precondition with 2656 bytes of stack: `toSatPw`,
with a 12-byte nonce. -/
def toSatS : State :=
  { toSatPw with
    gpr := fun r => match r with
      | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 12 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
    rd := [⟨0x1000, 256⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0, 128⟩, ⟨0x9000, 40⟩] }

theorem toSatS_pre : ∃ s, (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2656).pre s ∧
    (s.gpr .x3).toNat = 12 ∧ (s.gpr .x5).toNat ≤ 16 := by
  refine ⟨toSatS, ?_, by decide, by decide⟩
  sig_pre [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig,
    Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToSig, Spec.Gcm.withPowersParam, Spec.Gcm.openToPre,
    AArch64.abi, AArch64.argRegs, stackArgs_five, List.append_eq, toSatS, toSatPw, toSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) fun _ _ => rfl

/-- The one-pass branch, against its contract. -/
def splitK : Contract isa where
  pre := SPre
  post := toPost
  pub := toPub 3

theorem openToSplit_verified (F : SplitFn) : Verified AArch64.target (openToSplit F.fn) splitK := by
  refine ⟨fun s hs => ?_, openToSplit_ct F, ?_⟩
  · obtain ⟨t, s', he, ha, hp⟩ := openToSplit_wp F hs
    exact ⟨t, s', he, ha, hp⟩
  · obtain ⟨s, hs, h12, h16⟩ := toSatS_pre
    obtain ⟨to, w, bk, bn, ba, bs, bd, bt, bp, barg⟩ := toPre2656 hs
    exact ⟨s, to, w, bk, bn, ba, bs, bd, bt, bp, barg, h12, h16⟩

/-- The copying branch, against `toK pwShape`. -/
theorem openToPw_verifiedK (F : OpenFn pwShape) : Verified AArch64.target (openTo 3 F.fn) (toK pwShape) := by
  refine ⟨fun s hs => openTo_correct F s hs, openTo_ct F, ?_⟩
  obtain ⟨s, hs⟩ := toSatPw_pre
  exact ⟨s, toPwPre_of_spec hs⟩

/-- `selSplit`'s flag: zero for a 12-byte nonce, less than 16 bytes of
additional data and from 768 bytes of text. -/
def selFlag (s : State) : BitVec 64 :=
  ((s.gpr .x5 >>> 4) ||| ((s.gpr .x7 - BitVec.ofNat 64 768) >>> 63)) ||| (s.gpr .x3 ^^^ BitVec.ofNat 64 12)

/-- What `selSplit` leaves of a state: all but `x9` and `x10`. -/
structure SelRan (s u : State) : Prop where
  g : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = s.gpr r
  sp : u.sp = s.sp
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  v : u.v = s.v

theorem sel_run (s : State) :
    ∃ u, execBlock isa selSplit s = some (u, []) ∧ SelRan s u ∧
      isa.eval (.zero .x .x10) u = some (selFlag s == 0) := by
  refine ⟨_, rfl, ⟨fun r h9 h10 => ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp [State.write, h9, h10]
  · simp [eval, State.write, State.read, selFlag, Size.bits]

theorem selFlag_ok {s : State} (h : (selFlag s == 0) = true) :
    (s.gpr .x3).toNat = 12 ∧ (s.gpr .x5).toNat ≤ 16 := by
  have h0 : selFlag s = 0#64 := beq_iff_eq.mp h
  unfold selFlag at h0
  obtain ⟨h1, h3⟩ := BitVec.or_eq_zero_iff.mp h0
  obtain ⟨h5, -⟩ := BitVec.or_eq_zero_iff.mp h1
  refine ⟨by rw [BitVec.xor_eq_zero_iff.mp h3]; rfl, ?_⟩
  have := congrArg BitVec.toNat h5
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at this
  omega

theorem openToSel_verified (F : OpenFn pwShape) (G : SplitFn) :
    Verified AArch64.target (openToSel F.fn G.fn) (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2656) := by
  have hp : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 := by decide
  have sat : ∃ s, (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2656).pre s :=
    let ⟨s, hs, _⟩ := toSatS_pre; ⟨s, hs⟩
  refine Verified.entryBranch (p := fun s => selFlag s == 0) (fun _ => []) (openToSplit_verified G)
    (openToPw_verifiedK F) (fun s hs => ?_) ?_ sat
  · obtain ⟨u, e, r, ev⟩ := sel_run s
    have abi : ∀ s', AArch64.target.abiPreserved u s' → AArch64.target.abiPreserved s s' := fun s' a =>
      ⟨fun x hx => by
        obtain ⟨h9, h10⟩ := hp x hx
        rw [a.1 x hx, r.g x h9 h10], by rw [a.2.1, r.sp], fun x hx => by rw [a.2.2 x hx, r.v]⟩
    have hu : (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2656).pre u := by
      sig_pre [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig,
        Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToSig, Spec.Gcm.withPowersParam, Spec.Gcm.openToPre,
        AArch64.abi, AArch64.argRegs, stackArgs_five, List.append_eq] at hs ⊢
      have sa (i : Nat) : stackArg u i = stackArg s i := by simp only [stackArg, stackArgAddr, r.mem, r.sp]
      have saa : stackArgAddr u 0 = stackArgAddr s 0 := by simp only [stackArgAddr, r.sp]
      rw [sa 0, sa 1, sa 2, sa 3, sa 4, saa, r.g .x0 (by decide) (by decide), r.g .x1 (by decide) (by decide), r.g .x2 (by decide) (by decide),
        r.g .x3 (by decide) (by decide), r.g .x4 (by decide) (by decide), r.g .x5 (by decide) (by decide),
        r.g .x6 (by decide) (by decide), r.g .x7 (by decide) (by decide), r.sp, r.mem, r.rd, r.wr]
      exact hs
    have hres : res u = res s := by
      simp only [res, K, R, Nn, NL, Ad, AL, Src, L, Tg, TL, stackArg, stackArgAddr, r.mem, r.sp,
        r.g .x0 (by decide) (by decide), r.g .x1 (by decide) (by decide), r.g .x2 (by decide) (by decide),
        r.g .x3 (by decide) (by decide), r.g .x4 (by decide) (by decide), r.g .x5 (by decide) (by decide),
        r.g .x6 (by decide) (by decide), r.g .x7 (by decide) (by decide)]
    have hpost : ∀ s', toPost u s' → toPost s s' := fun s' q => by
      unfold toPost at q ⊢
      rw [hres] at q
      simpa only [Dst, L, stackArg, stackArgAddr, r.mem, r.sp, r.g .x7 (by decide) (by decide)] using q
    obtain ⟨to, w, bk, bn, ba, bs, bd, bt, bp, barg⟩ := toPre2656 hu
    refine ⟨u, e, ev, fun hf => ⟨?_, fun s' a q => ⟨abi s' a, toPost2656 (hpost s' q)⟩⟩,
      fun _ => ⟨to, fun s' a q => ⟨abi s' a, toPost2656 (hpost s' q)⟩⟩⟩
    obtain ⟨h12, h16⟩ := selFlag_ok hf
    exact ⟨to, w, bk, bn, ba, bs, bd, bt, bp, barg,
      by show (u.gpr .x3).toNat = 12; rw [r.g .x3 (by decide) (by decide)]; exact h12,
      by show (u.gpr .x5).toNat ≤ 16; rw [r.g .x5 (by decide) (by decide)]; exact h16⟩
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, r, -⟩ := sel_run s
    obtain ⟨u₀', e₀', r', -⟩ := sel_run s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    obtain ⟨qsp, ql, q0, q1, q2, q3, q4, q5, q6, q7, qa⟩ := toPub2656 hq
    have pu : toPub 3 u₀ u₀' := by
      have g (r₀ : Reg) (h9 : r₀ ≠ .x9) (h10 : r₀ ≠ .x10) : u₀.gpr r₀ = s.gpr r₀ ∧ u₀'.gpr r₀ = s'.gpr r₀ :=
        ⟨r.g r₀ h9 h10, r'.g r₀ h9 h10⟩
      have sa (i : Nat) : stackArg u₀ i = stackArg s i ∧ stackArg u₀' i = stackArg s' i := by
        exact ⟨by simp only [stackArg, stackArgAddr, r.mem, r.sp], by simp only [stackArg, stackArgAddr, r'.mem, r'.sp]⟩
      refine ⟨by rw [r.sp, r'.sp, qsp], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
      · simp only [toLeak, res, K, R, Nn, NL, Ad, AL, Src, L, Tg, TL, (sa 0).1, (sa 0).2, (sa 1).1, (sa 1).2,
          (sa 2).1, (sa 2).2, (sa 3).1, (sa 3).2, r.mem, r'.mem, (g .x0 (by decide) (by decide)).1,
          (g .x0 (by decide) (by decide)).2, (g .x1 (by decide) (by decide)).1, (g .x1 (by decide) (by decide)).2,
          (g .x2 (by decide) (by decide)).1, (g .x2 (by decide) (by decide)).2, (g .x3 (by decide) (by decide)).1,
          (g .x3 (by decide) (by decide)).2, (g .x4 (by decide) (by decide)).1, (g .x4 (by decide) (by decide)).2,
          (g .x5 (by decide) (by decide)).1, (g .x5 (by decide) (by decide)).2, (g .x6 (by decide) (by decide)).1,
          (g .x6 (by decide) (by decide)).2, (g .x7 (by decide) (by decide)).1, (g .x7 (by decide) (by decide)).2]
        exact ql
      all_goals first
        | (rw [(g _ (by decide) (by decide)).1, (g _ (by decide) (by decide)).2]; assumption)
        | (rw [(sa i).1, (sa i).2]; exact qa i hi)
    refine ⟨rfl, ?_, fun _ => pu, fun _ => pu⟩
    simp only [selFlag, (r.g .x3 (by decide) (by decide)), (r.g .x5 (by decide) (by decide)),
      (r.g .x7 (by decide) (by decide)), (r'.g .x3 (by decide) (by decide)), (r'.g .x5 (by decide) (by decide)),
      (r'.g .x7 (by decide) (by decide)), q3, q5, q7]

end VG.Proof.AesGcm.AArch64.OpenTo
