module

public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Fn
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

theorem splitEntry_eq : splitEntry = [.addSp .x16 0, .str .x .x30 .x16 40] ++
    ([.ldrSp .x17 64, .str .x .x17 .x16 0] ++ ([.ldrSp .x17 72, .str .x .x17 .x16 8] ++
    ([.ldrSp .x17 80, .str .x .x17 .x16 16] ++ [.str .x .x6 .x16 24, .str .x .x7 .x16 32, .ldrSp .x6 48]))) := rfl

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

/-- When the call failed: `dst` zeroed. -/
theorem swipe_wp {s z : State} (h : SLay s) (hz : SCalled s z) (hres : res s = none) :
    WP isa (wipe 5) z (SDone s) := by
  have to := h.pre.to
  have hP : P2 s = B2 s + BitVec.ofNat 64 2608 := rfl
  have x0 : (z.gpr .x0).setWidth 32 = 0 := by have := hz.out; rw [hres] at this; exact this
  have inA (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 8 ≤ 64) :
      InRegions (z.rd ++ z.wr) (z.sp + BitVec.ofNat 64 d) 8 := by
    rw [hz.sp, hP, Offset.add_ofNat_add_ofNat, hz.rd]
    exact h.inArg (2608 + d) (by omega_arith) (by omega_arith) _
  unfold wipe
  refine WP.seq (WP.mono (wipeArgs5_ok z (inA 48 (by decide) (by decide)) (inA 56 (by decide) (by decide)))
    fun a ⟨x9a, x10a, x11a, ga, ma, spa, rda, wra, va⟩ => ?_)
  rw [hz.sp, hP, Offset.add_ofNat_add_ofNat,
    show B2 s + BitVec.ofNat 64 (2608 + 48) = B2 s + BitVec.ofNat 64 (2656 + 8 * 0) from rfl,
    hz.arg h 0 (by decide)] at x9a
  rw [hz.sp, hP, Offset.add_ofNat_add_ofNat,
    show B2 s + BitVec.ofNat 64 (2608 + 56) = B2 s + BitVec.ofNat 64 (2656 + 8 * 1) from rfl,
    hz.arg h 1 (by decide)] at x10a
  have hL : stackArg s 1 = BitVec.ofNat 64 (L s) := by
    apply BitVec.eq_of_toNat_eq; rw [to.dl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s.gpr .x7).isLt]
  rw [hL] at x10a
  have hw : Covers [⟨Dst s, L s⟩] a.wr := by
    rw [wra, hz.wr, to.wr]; exact covers_cons (covers_of_mem (by simp)) covers_nil
  refine WP.mono (wipeLoop_wp a (s.gpr .x7).isLt x9a x10a x11a hw to.od)
    fun u ⟨pz, fu, gu, spu, rdu, wru, vu⟩ => ?_
  have g' : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → u.gpr r = z.gpr r := fun r a b c => by
    rw [gu r a b, ga r a b c]
  refine ⟨?_, ?_, fun r hr h30 => ?_, by rw [spu, spa, hz.sp], by rw [rdu, rda, hz.rd],
    by rw [wru, wra, hz.wr], fun r hr => by rw [vu, va]; exact hz.v r hr⟩
  · show match res s with | some pt => _ | none => _
    rw [hres]
    exact ⟨by rw [g' _ (by decide) (by decide) (by decide)]; exact x0, bytesAt_zeros pz⟩
  · rw [← hz.ra, ← ma]
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

end VG.Proof.AesGcm.AArch64.OpenTo
