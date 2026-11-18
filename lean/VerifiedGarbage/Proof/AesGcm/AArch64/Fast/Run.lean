module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Front
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `AesGcm.AArch64.Fast.PadT`, which this module and modules that import it used -/

section

/-!
# AES-GCM on AArch64, the path for TLS records: the last bytes, from the end of the text

Untrusted: everything here is checked by Lean. `padMulT` absorbs the `x13`
bytes at `x12` padded to a block, as `padMul` does (`padMulT_ok`, with the
same result): by `padMul` for a text (of `x26` bytes) shorter than a block,
and otherwise by `Tail.padVec`, from the 16 bytes that end the text, moved
down into the padded block (`Tail.pad_vec`) in a register.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Impl.AesGcm.AArch64.Tail (idxName idxTable padVec shift)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes)

theorem syms_write' (s : State) (sz : Size) (r : Reg) (x : BitVec sz.bits) : (s.write sz r x).syms = s.syms := rfl
theorem syms_setV' (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).syms = s.syms := rfl
theorem idxTable_length' : idxTable.length = 4 := rfl

/-- The 16 bytes that end the last `m < 16` bytes of a readable text of `N`
bytes at `D₀` (`padMulT_ok`'s `hbig`). -/
theorem pad_big {rs : List Region} {D₀ P : Addr} {N m : Nat} (h : Covers [⟨D₀, N⟩] rs) (hN : N < 2 ^ 64)
    (hP : P = D₀ + BitVec.ofNat 64 (N - m)) (hm : m < 16) :
    16 ≤ N → m ≠ 0 → m < 16 ∧ ∃ E, E + BitVec.ofNat 64 (16 - m) = P ∧ InRegions rs E 16 := fun h16 _ =>
  ⟨hm, D₀ + BitVec.ofNat 64 (N - 16), by rw [hP, Offset.add_add]; congr 2; omega_using [hm, h16], in_off h (by omega_using [h16]) hN⟩

/-- `padVec`'s loads: the 16 bytes ending the `r` bytes at `x12`, moved down
into the padded block in `A`. -/
theorem padPre_run {E : Addr} {r : Nat} (hr : r < 16) {s : State}
    (h12 : s.gpr .x12 = E + BitVec.ofNat 64 (16 - r)) (h13 : s.gpr .x13 = BitVec.ofNat 64 r)
    (hE : InRegions (s.rd ++ s.wr) E 16) :
    ∃ s', runBlock isa (shift .x13 A .x11 ++ ([.ldrqTbl T .x11 16 idxName idxTable, .vop (.add .b16 T T A),
        .sub .x .x11 .x12 .x9, .ldrq A .x11 0, .vop (.tbl A A T)] : List Instr)) s = some s' ∧
      s'.v A = Tail.downV (s.mem.read E 16) r ∧ (∀ v, v ≠ A → v ≠ T → s'.v v = s.v v) ∧
      Others [.x9, .x11] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h16 : (BitVec.setWidth 64 (16#16) <<< 0 : BitVec 64) = BitVec.ofNat 64 16 := by decide
  have hsub : BitVec.ofNat 64 16 - BitVec.ofNat 64 r = BitVec.ofNat 64 (16 - r) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hr]) (by omega_using [hr])
  have hx11 : E + BitVec.ofNat 64 (16 - r) - BitVec.ofNat 64 (16 - r) = E := BitVec.add_sub_cancel _ _
  refine ⟨_, by
    simp only [shift, List.cons_append, List.nil_append]
    arun [h12, h13, h16, hsub, hx11, hE, VOp.eval, RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.wr_setV, RegUpd.rd_setV,
      RegUpd.sp_setV, RegUpd.rd_write, syms_write', syms_setV', idxTable_length', Nat.reduceDiv, RegUpd.v_write, BitVec.add_zero]
    , ?_⟩
  refine ⟨rfl, fun v h₁ h₂ => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [RegUpd.v_setV, RegUpd.v_write, h₁, h₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, RegUpd.gpr_setV, hr]

/-- `padMulT`: `padMul`'s result, for `n` bytes at `P` that, if the text (of
`N` bytes, in `x26`) is at least a block long and `n` is not zero, end 16
bytes at `E` the code may read. -/
theorem padMulT_ok (hM : MulKey) {Ctx St W SP : Addr} {H y : Block} {P : Addr} {n N : Nat} {s : State}
    (he : Env Ctx St W SP s) (hk : HKey H s)
    (hy : s.v Y = ext8 y y) (h12 : s.gpr .x12 = P) (h13 : s.gpr .x13 = BitVec.ofNat 64 n) (hn : n ≤ 16)
    (hP : Covers [⟨P, n⟩] (s.rd ++ s.wr)) (hPW : (⟨P, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 16⟩)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hbig : 16 ≤ N → n ≠ 0 → n < 16 ∧ ∃ E, E + BitVec.ofNat 64 (16 - n) = P ∧ InRegions (s.rd ++ s.wr) E 16) :
    WP isa Impl.AesGcm.AArch64.Fast.padMulT s fun s' =>
      s'.v Y = ext8 (padStep H y (bytesAt s.mem P n)) (padStep H y (bytesAt s.mem P n)) ∧ HKey H s' ∧
      Env Ctx St W SP s' ∧
      Others [.x9, .x11, .x12, .x13, .x14, .x15] s s' ∧ Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ [A, LO, MID, HI, T, Y] → s'.v r = s.v r) := by
  refine WP.ite (decide (n = 0)) (eval_zero h13 (by omega_using [hn])) (fun ht => ?_) (fun hf' => ?_)
  · have h0 : n = 0 := of_decide_eq_true ht
    subst h0
    exact WP.block_nil ⟨by rw [show bytesAt s.mem P 0 = [] from rfl]; exact hy, hk, he, fun _ _ => rfl,
      Frame.refl _ _, fun _ _ => rfl⟩
  have h0 : n ≠ 0 := of_decide_eq_false hf'
  obtain ⟨s₁, run₁, x9₁, r₁, v₁⟩ : ∃ s₁, runBlock isa [.lsr .x .x9 .x26 4] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 (N / 16) ∧ Regs [.x9] s s₁ ∧ s₁.v = s.v := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
    simp [gpr_write, h26, lsr_ofNat _ _ hN]
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => r₁.others r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) r₁.sp r₁.rd r₁.wr
  have hk₁ : HKey H s₁ := hk.of_v (by rw [v₁]) (by rw [v₁]) (by rw [v₁])
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (N / 16 = 0)) (eval_zero x9₁ (by omega_using [hN])) (fun _ => ?_) (fun hf => ?_)
  · refine WP.mono (padMul_ok hM (y := y) he₁ hk₁ (by rw [v₁]; exact hy) (by rw [r₁.others _ (by decide), h12])
      (by rw [r₁.others _ (by decide), h13]) hn (by rw [r₁.rd, r₁.wr]; exact hP) hPW)
      fun s' ⟨y', k', e', o', f', v'⟩ => ⟨by rw [y', r₁.mem], k', e', fun r hr => by
        rw [o' r hr, r₁.others r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.1)],
        by rw [← r₁.mem]; exact f', fun r hr => by rw [v' r hr, v₁]⟩
  have hbN : 16 ≤ N := by have := of_decide_eq_false hf; omega_using [this]
  obtain ⟨hn16, E, hE, hEr⟩ := hbig hbN h0
  obtain ⟨s₂, run₂, a₂, v₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := padPre_run (s := s₁) (E := E) hn16
    (by rw [r₁.others _ (by decide), h12, hE]) (by rw [r₁.others _ (by decide), h13])
    (by rw [r₁.rd, r₁.wr]; exact hEr)
  have vv : ∀ v, v ≠ A → v ≠ T → s₂.v v = s.v v := fun v h₁ h₂ => by rw [v₂ v h₁ h₂, v₁]
  have hk₂ : HKey H s₂ := hk.of_v (vv _ (by decide) (by decide)) (vv _ (by decide) (by decide))
    (vv _ (by decide) (by decide))
  have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  have hpv : padVec = (shift .x13 A .x11 ++ [.ldrqTbl T .x11 16 idxName idxTable, .vop (.add .b16 T T A),
      .sub .x .x11 .x12 .x9, .ldrq A .x11 0, .vop (.tbl A A T)]) ++
      (([.vop (.logic .eor A A Y)] : List Instr) ++ Impl.Gcm.AArch64.Pmull.mul Y A (sReg 1) (tReg 1)) := by
    simp [padVec]
  rw [hpv, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (eor_ok A A Y s₂) fun s₃ ⟨e₃, o₃⟩ => ?_
  have hk₃ : HKey H s₃ := hk₂.of_vonly o₃ (by decide) (by decide) (by decide)
  refine WP.mono (mulV_ok Y A (sReg 1) (tReg 1) s₃ free_A (sReg_free _) (tReg_free _) hk₃.sw hk₃.c)
    fun s₄ ⟨m₄, o₄⟩ => ⟨?_, hk₃.of_vonly o₄ (by decide) (by decide) (by decide),
      he₂.keep (fun r _ => by rw [o₄.gpr, o₃.gpr]) (by rw [o₄.sp, o₃.sp]) (by rw [o₄.rd, o₃.rd])
        (by rw [o₄.wr, o₃.wr]), fun r hr => ?_, ?_, fun r hr => ?_⟩
  · have hne : bytesAt s.mem P n ≠ [] := fun e => h0 (by simpa [length_bytesAt] using congrArg List.length e)
    have hY₂ : s₂.v Y = s.v Y := vv Y (by decide) (by decide)
    rw [m₄, e₃, a₂, hY₂, hy, r₁.mem, Tail.pad_vec _ _ (by omega_using [h0]) hn16, hE, rev64b_read, ← ext8_xor, hk₃.t, hM,
      BitVec.xor_comm, Tail.blockAt_padMem _ _ hn]
    simp only [padStep, hne, ↓reduceIte, length_bytesAt]
  · rw [o₄.gpr, o₃.gpr, g₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact ⟨hr.1, hr.2.1⟩),
      r₁.others r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.1)]
  · rw [o₄.mem, o₃.mem, m₂, r₁.mem]; exact Frame.refl _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₄.v r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]), o₃.v r (by simp [hr.1]),
      vv r hr.1 hr.2.2.2.2.1]

end VG.Proof.AesGcm.AArch64.Fast

end

end

/-!
# AES-GCM on AArch64, the path for TLS records: `run`

Untrusted: everything here is checked by Lean. After the entry of `seal`, for
a 12-byte nonce and at most 16 bytes of additional data, `runWithP` does
what `sealRest` does (`runWithP_ok`): `front` (`front_ok`), the text
encrypted as `sealRest` encrypts it (`cryptAl_ok`), its whole blocks absorbed
by one call of `vg_ghash` (`absSeg2_ok`, `absCall2_ok`), its last bytes and the lengths
block absorbed in registers (`padMul_ok`, `mulT_ok`), and the tag
(`tagSeg_ok`, `tagCall_ok`, `tagOut_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

/-- What `run` writes in the working space after the text: below `W + 128`,
`H'`, and the scratch space of the calls. -/
abbrev wsR (W : Addr) : List Region :=
  [⟨W, 128⟩, keyR W, ⟨W + BitVec.ofNat 64 512, 2048⟩]

theorem sub_low {W : Addr} {d k : Nat} (h : d + k ≤ 128) :
    ∃ r' ∈ wsR W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_self .., Offset.sub_base W h⟩

theorem sub_low' {W : Addr} {d e k : Nat} (h : d + e + k ≤ 128) :
    ∃ r' ∈ wsR W, Region.Sub ⟨W + BitVec.ofNat 64 d + BitVec.ofNat 64 e, k⟩ r' := by
  rw [add_ofNat_assoc]; exact sub_low h

theorem sub_scr {W : Addr} {k : Nat} (h : k ≤ 2048) :
    ∃ r' ∈ wsR W, Region.Sub ⟨W + BitVec.ofNat 64 512, k⟩ r' :=
  ⟨_, by simp, Region.sub_prefix h⟩

theorem saved_wsR {W : Addr} : ∀ r ∈ wsR W, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base W (by decide) (by decide)
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

/-- Apart from each of `rs` and each of `ex`. -/
theorem disj_ex {R : Region} {rs ex : List Region} (h : ∀ r ∈ rs, R.Disjoint r) (he : ∀ r ∈ ex, R.Disjoint r) :
    ∀ r ∈ rs ++ ex, R.Disjoint r :=
  fun r hr => (List.mem_append.mp hr).elim (h r) (he r)

/-- Apart from each region `absorb` writes and each of `ex`. -/
theorem disj_absEx {R : Region} {St W : Addr} {yo : Nat} {ex : List Region}
    (h : ∀ r ∈ absFrame St W yo, R.Disjoint r) (he : ∀ r ∈ ex, R.Disjoint r) :
    ∀ r ∈ absFrame St W yo ex, R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · exact h _ (by simp)
  · exact h _ (by simp)
  · exact h _ (by simp)
  · exact he r hr

/-- `runWith`, for a function `gh` that hashes the whole blocks as `vg_ghash`
does when called with `vg_ghash`'s arguments from a state with the regions
of `s`, whose memory differs from `s`'s only in the working space and the
text (`hgh`), and that may also write the regions `ex`, apart from the
working space, the text and the key context, and establish `I`, which what
the rest writes keeps (`hI`). -/
theorem runWithPX_ok (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) {w : Nat} {extra extraW : List Region} {s s₁ : State}
    {ex : List Region} {I : Mem → Prop}
    (hs : sealPreXW w extra s extraW)
    (hexW : ∀ r ∈ ex, (workR (stackArg s w)).Disjoint r)
    (hexD : ∀ r ∈ ex, (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨s.gpr .x0, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR (stackArg s w), ⟨stackArg s 0, 16⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region) →
      WP isa cl s' fun t => GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb t ex ∧ I t.mem)
    (h₁ : SealEntry w s s₁) (hx : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₁.gpr r = s.gpr r)
    (h12 : (s.gpr .x3).toNat = 12) (h16 : (s.gpr .x5).toNat ≤ 16) :
    WP isa (Impl.AesGcm.AArch64.Fast.runWithP v.callees cl) s₁ fun s' =>
      (GprAbi s s' ∧ sealAArch64.post s s') ∧ I s'.mem := by
  -- Facts are stated with `obtain`, not `have`: `have` keeps its proof in the context (a `let` nothing
  -- unfolds), and every `(by …)` in a term first instantiates and shares the whole context (`Term.runTactic`).
  obtain ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, x28₁, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩ := h₁
  obtain hx4 := hx .x4 (by simp)
  obtain hx5 := hx .x5 (by simp)
  obtain hx6 := hx .x6 (by simp)
  obtain hx7 := hx .x7 (by simp)
  obtain ⟨ol, tW, dtw, ddt⟩ := sealLay hs
  simp only [sealAArch64]
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  obtain h3 := ofNat_toNat' (s.gpr .x3)
  obtain h5 := ofNat_toNat' (s.gpr .x5)
  obtain h7 := ofNat_toNat' (s.gpr .x7)
  generalize hW : stackArg s w = W at *
  generalize hTg : stackArg s 0 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  subst h12
  obtain hRb : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRR]; exact hR
  obtain hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x7).isLt
  unfold Impl.AesGcm.AArch64.Fast.runWithP
  rw [← h5] at sl₂ hx5
  rw [← h7] at sl₄ hx7
  obtain sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  obtain kc := keep_of_sub (entryR_work W) (dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  obtain hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := blockAt_frame f₁ kc
  obtain hnon : DataOk (W + BitVec.ofNat 64 16) W s₁ Np 12 :=
    ⟨by rw [rd₁, wr₁]; exact nR, hnl ▸ (s.gpr .x3).isLt, wn, dnW.sub_right sub16, dnW⟩
  obtain haad : DataOk (W + BitVec.ofNat 64 16) W s₁ A al :=
    ⟨by rw [rd₁, wr₁]; exact aR, hal ▸ (s.gpr .x5).isLt, wa, daW.sub_right sub16, daW⟩
  obtain iv₁ : bytesAt s₁.mem Np 12 = bytesAt s.mem Np 12 :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) dnW) (by omega_arith)
  obtain a₁ : bytesAt s₁.mem A al = bytesAt s.mem A al :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) daW) (by omega_arith)
  obtain hJ : J0In Ctx (W + BitVec.ofNat 64 16) W s.sp s₁.gpr (ctxH s.mem Ctx) Np 12 s₁ :=
    ⟨he₁, fun _ _ => rfl, x23₁, by rw [x24₁, ← h3], by rw [x26₁, ← h3], x27₁, hnon, hH₁⟩
  refine WP.seq (WP.mono (front_ok L hMK hJ haad h16 hx4 hx5 hx6 hx7) fun s₂ h₂ => ?_)
  rw [iv₁, a₁] at h₂
  obtain slot₂ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' =>
    slot_kept h₂.frame (slots_frontFrame' L) h₁ h₂'
  have he₂ := h₂.env
  -- The text, from the first counter block.
  obtain ⟨s₃, run₃, x27₃, x24₃, x25₃, r₃⟩ : ∃ s₃, runBlock isa [mov .x27 .x23, mov .x24 .x26, imm .x25 0] s₂ =
      some s₃ ∧ s₃.gpr .x27 = D ∧ s₃.gpr .x24 = BitVec.ofNat 64 n ∧
      s₃.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x27, .x24, .x25] s₂ s₃ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h₂.x23], by simp [gpr_write, h₂.x26], by simp [gpr_write],
      ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ := he₂.of_regs r₃
  obtain hk₃ : Kept s₃.gpr s₃ := fun _ _ => rfl
  obtain x22₃ : s₃.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₃.others _ (by decide), h₂.x22, x22₁, ← hRR, ofNat_toNat']
  obtain x26₃ : s₃.gpr .x26 = BitVec.ofNat 64 n := by rw [r₃.others _ (by decide), h₂.x26]
  obtain x28₃ : s₃.gpr .x28 = Tg := by rw [r₃.others _ (by decide), h₂.x28, x28₁]
  obtain hdat₃ : DataW Ctx (W + BitVec.ofNat 64 16) W s₃ D n :=
    ⟨⟨covers_left (by rw [r₃.wr, h₂.wr, wr₁]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩,
      by rw [r₃.wr, h₂.wr, wr₁]; exact dW, dcd⟩
  obtain hCr : CrIn Ctx (W + BitVec.ofNat 64 16) W s.sp s₃.gpr R 0 D n s₃ :=
    ⟨he₃, hk₃, x22₃, hRb, by rw [r₃.others _ (by decide), h₂.x23], x24₃, x25₃, hdat₃, rfl⟩
  obtain cb₃ : blockAt s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np 12)) := by rw [r₃.mem]; exact h₂.cb
  generalize hJ0 : Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np 12) = J0 at cb₃
  refine WP.seq (WP.mono (WP.with_rdwr (cryptAlT_ok L v (icb := inc32 J0) hCr (by decide) x26₃ hnlt
      (tail_big hdat₃.wr hnlt (by simp) (Nat.zero_add n))))
    fun s₄ ⟨h₄, rd₄, wr₄⟩ => ?_)
  obtain hctr₃ : Ctr s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
      (ciphOf s₃.mem Ctx R) (inc32 J0) 0 := Proof.Gcm.ctr_zero _ _ _ _ cb₃
  obtain out₄ := h₄.out hctr₃
  have he₄ := h₄.env
  obtain dWK : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W D n, (keyR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (ddW.sub_right (Lay.wSub (by decide))).symm
    · exact (L.st_w (a := 48) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  obtain dWS : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W D n, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (ddW.sub_right (Lay.wSub (by decide))).symm
    · exact (L.st_w (a := 48) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  obtain slot₄ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' => by
    rw [slot_kept h₄.frame dWS h₁ h₂', r₃.mem, slot₂ d h₁ h₂']
  -- The whole blocks of the ciphertext, by `vg_ghash`.
  rw [WP.seq_iff, WP.block_append_iff]
  obtain ⟨s₅, run₅, x23₅, x24₅, r₅⟩ : ∃ s₅, runBlock isa [mov .x23 .x27, mov .x24 .x26] s₄ =
      some s₅ ∧ s₅.gpr .x23 = D ∧ s₅.gpr .x24 = BitVec.ofNat 64 n ∧ Regs [.x23, .x24] s₄ s₅ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h₄.kept .x27 (by decide), x27₃], by simp [gpr_write, h₄.kept .x26 (by decide), x26₃],
      ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain he₅ := he₄.of_regs r₅
  obtain hk₅ : Kept s₃.gpr s₅ := h₄.kept.of_others r₅.others
  obtain hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [r₅.mem, hH_crFrame L hdat₃ h₄.frame, r₃.mem, h₂.hH]
  obtain hdat₅ : DataOk (W + BitVec.ofNat 64 16) W s₅ D n :=
    hdat₃.ok.of_eq (by rw [r₅.rd, rd₄]) (by rw [r₅.wr, wr₄])
  generalize hx₁ : bytesAt s.mem A al ++ zeros (padLen (bytesAt s.mem A al).length) = x₁ at h₂
  obtain hx₁0 : x₁.length % 16 = 0 := by
    rw [← hx₁, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain hM : AbsMid Ctx (W + BitVec.ofNat 64 16) W s.sp s₃.gpr 16 (ctxH s.mem Ctx) x₁ D n 0 s₅.mem 0 s₅ :=
    ⟨he₅, hk₅, Nat.zero_le _, by rw [x23₅]; simp, by rw [x24₅, Nat.sub_zero],
      by rw [r₅.others _ (by decide), h₄.x25], hdat₅, hH₅, fun ha => by simpa [bytesAt] using ha,
      .inr (by omega_arith), Frame.refl _ _⟩
  refine WP.mono (WP.with_rdwr (absSeg2_ok L (.inr rfl) hM)) fun s₆ ⟨h₆, rd₆, wr₆⟩ => ?_
  obtain FW : Frame [workR W, ⟨D, n⟩] s.mem s₆.mem := by
    obtain e : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
        (∀ r ∈ rs, ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r') → Frame [workR W, ⟨D, n⟩] m m' :=
      fun h hs => h.sub hs
    obtain w : ∀ {r : Region}, Region.Sub r (workR W) → ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r' :=
      fun h => ⟨_, List.mem_cons_self .., h⟩
    obtain F1 := e f₁ fun r hr => w (entryR_work W r hr)
    obtain F2 := e h₂.frame fun r hr => w (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl <;> exact Lay.wSub (by decide))
    obtain F4 : Frame [workR W, ⟨D, n⟩] s₂.mem s₄.mem := by
      rw [← r₃.mem]
      refine e h₄.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
      · exact w (stW (by decide))
      · exact w (Lay.wSub (by decide))
    obtain F6 : Frame [workR W, ⟨D, n⟩] s₄.mem s₆.mem := by
      rw [← r₅.mem]
      refine e h₆.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact w (stW (by decide))
      · exact w (stW (by decide))
      · exact w (Lay.wSub (by decide))
    exact ((F1.trans F2).trans F4).trans F6
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, r₅.rd, rd₄, r₃.rd, h₂.rd, rd₁]
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, r₅.wr, wr₄, r₃.wr, h₂.wr, wr₁]
  obtain exW : ∀ {R : Region}, Region.Sub R (workR W) → ∀ r ∈ ex, R.Disjoint r :=
    fun hR r hr => (hexW r hr).sub_left hR
  refine WP.seq (WP.mono (WP.with_rdwr (absCall2WithX_ok L (.inr rfl)
      (fun r hr => (hexC r hr).sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
      (exW (stW (by decide))) h₆
      (hgh s₆ h₆.call (stW (by decide)) (Lay.wSub (by decide)) rd₆' wr₆' h₆.env.sp FW
        (Offset.sub_base D (by omega_arith)))))
    fun s₇ ⟨⟨⟨h₇, hlt₇⟩, I₇⟩, rd₇, wr₇⟩ => ?_)
  rw [Nat.zero_add, Nat.sub_zero] at h₇ hlt₇
  generalize hj : 16 * (n / 16) = j at h₇ hlt₇
  obtain hjn : j ≤ n := by omega_arith
  have he₇ := h₇.env
  obtain hab₅ : Absorbed s₅.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      (ctxH s.mem Ctx) x₁ := by
    refine ⟨?_, ?_⟩
    · rw [Proof.Gcm.whole_of_mod hx₁0, List.take_length, ← hx₁, ← h₂.y, r₅.mem,
        blockAt_frame h₄.frame (fun r hr => (acc_crFrame L hdat₃ r hr).sub_left (Region.sub_prefix (by decide))),
        r₃.mem]
    · rw [hx₁0, Proof.Gcm.whole_of_mod hx₁0, List.drop_length]; rfl
  obtain hY₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      ghash (ctxH s.mem Ctx) (blocks (x₁ ++ bytesAt s₅.mem D j)) :=
    (h₇.abs hab₅).whole_eq (by rw [List.length_append, length_bytesAt]; omega_arith)
  obtain key₇ : KeyAt (ctxH s.mem Ctx) s₇.mem W := by
    refine ((h₂.key.frame (rs := []) (by rw [← r₃.mem]; exact Frame.refl _ _) (by simp)).frame h₄.frame dWK).frame
      (by rw [← r₅.mem]; exact h₇.frame) fun r hr => ?_
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (a := 32) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact exW (Lay.wSub (by decide)) r hr
  -- `H'` again, `Y`, and the last bytes.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (reload_ok (H := ctxH s.mem Ctx) (by rw [he₇.x19]; exact he₇.perm.wR (by decide))
    (by rw [he₇.x19]; exact he₇.perm.wR (by decide)) (by rw [he₇.x19]) (by rw [he₇.x19]; exact key₇.2)
    key₇.1) fun s₈ ⟨hk₈, g₈, v₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  obtain he₈ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₈ := he₇.keep (fun r hr => g₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
  refine WP.mono (loadRev_ok Y .x20 16 s₈ (by decide) (by decide) (by rw [he₈.x20]; exact he₈.perm.stR (by decide)))
    fun s₉ ⟨l₉, o₉⟩ => ?_
  obtain he₉ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₉ := he₈.keep (fun r _ => by rw [o₉.gpr]) o₉.sp o₉.rd o₉.wr
  obtain ⟨s₁₀, run₁₀, x13₁₀, x12₁₀, r₁₀, v₁₀⟩ : ∃ s₁₀, runBlock isa [mov .x13 .x24, mov .x12 .x23] s₉ = some s₁₀ ∧
      s₁₀.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ s₁₀.gpr .x12 = D + BitVec.ofNat 64 j ∧
      Regs [.x13, .x12] s₉ s₁₀ ∧ s₁₀.v = s₉.v := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp [gpr_write, o₉.gpr, g₈ .x24 (by decide), h₇.x24]
    · simp [gpr_write, o₉.gpr, g₈ .x23 (by decide), h₇.x23]
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  obtain he₁₀ := he₉.of_regs r₁₀
  obtain hk₁₀ : HKey (ctxH s.mem Ctx) s₁₀ :=
    hk₈.of_v (by rw [v₁₀, o₉.v C (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)])
  obtain hy₁₀ : s₁₀.v Y = ext8 (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) := by
    rw [v₁₀, l₉, he₈.x20, m₈, rev64b_read]
  obtain rd₁₀ : s₁₀.rd = s₅.rd := by rw [r₁₀.rd, o₉.rd, rd₈, rd₇, rd₆]
  obtain wr₁₀ : s₁₀.wr = s₅.wr := by rw [r₁₀.wr, o₉.wr, wr₈, wr₇, wr₆]
  obtain hdj : DataOk (W + BitVec.ofNat 64 16) W s₁₀ (D + BitVec.ofNat 64 j) (n - j) :=
    (hdat₅.drop hjn).of_eq rd₁₀ wr₁₀
  obtain x26₁₀ : s₁₀.gpr .x26 = BitVec.ofNat 64 n := by
    rw [r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h₇.kept .x26 (by decide), x26₃]
  refine WP.seq (WP.mono (WP.with_rdwr (padMulT_ok hMK he₁₀ hk₁₀ hy₁₀ x12₁₀ x13₁₀ (by omega_arith) hdj.rd
    (hdj.w.sub_right (Lay.wSub (by decide))) x26₁₀ hnlt
    (pad_big (hdat₅.of_eq rd₁₀ wr₁₀).rd hnlt (by congr 2; omega_arith) (by omega_arith))))
    fun s₁₁ ⟨⟨y₁₁, hk₁₁, he₁₁, og₁₁, f₁₁, v₁₁⟩, rd₁₁, wr₁₁⟩ => ?_)
  -- The slots, so far.
  obtain m₁₀ : s₁₀.mem = s₇.mem := by rw [r₁₀.mem, o₉.mem, m₈]
  obtain slot₁₁ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₁₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' => by
    rw [slot_kept f₁₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)) h₁ h₂', m₁₀,
      slot_kept h₇.frame (disj_absEx (slots_absFrame L) (exW (Lay.wSub (by decide)))) h₁ h₂', r₅.mem,
      slot₄ d h₁ h₂']
  -- The lengths block.
  unfold Impl.AesGcm.AArch64.Fast.lensTag Impl.AesGcm.AArch64.Fast.lensTagAt
  rw [WP.seq_iff]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  obtain w₁ := he₁₁.perm.wW (show 96 + 8 ≤ 2560 by decide)
  obtain w₂ := he₁₁.perm.wW (show 104 + 8 ≤ 2560 by decide)
  obtain q₁ := he₁₁.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain x26₁₁ : s₁₁.gpr .x26 = BitVec.ofNat 64 n := by
    rw [og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h₇.kept .x26 (by decide), x26₃]
  obtain ⟨s₁₂, run₁₂, m₁₂, og₁₂, sp₁₂, rd₁₂, wr₁₂, v₁₂⟩ : ∃ s₁₂, runBlock isa
      [.ldr .x .x10 .x19 alenO, .lsl .x .x9 .x10 3, .rev .x9 .x9, .str .x .x9 .x19 tO, .lsl .x .x9 .x26 3,
        .rev .x9 .x9, .str .x .x9 .x19 (tO + 8)] s₁₁ = some s₁₂ ∧
      s₁₂.mem = (s₁₁.mem.writeW (W + BitVec.ofNat 64 96) (AArch64.rev64 (BitVec.ofNat 64 al <<< 3))).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (AArch64.rev64 (BitVec.ofNat 64 n <<< 3)) ∧
      Others [.x9, .x10] s₁₁ s₁₂ ∧ s₁₂.sp = s₁₁.sp ∧ s₁₂.rd = s₁₁.rd ∧ s₁₂.wr = s₁₁.wr ∧
      s₁₂.v = s₁₁.v := by
    obtain e₁ : s₁₁.mem.read (W + 224#64) 8 = BitVec.ofNat 64 al := by
      rw [show s₁₁.mem.read (W + 224#64) 8 = s₁₁.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl,
        slot₁₁ 224 (by decide) (by decide), sl₂]
    refine ⟨_, by arun [he₁₁.x19, q₁, w₁, w₂], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.mem_write, Mem.writeW, BitVec.setWidth_eq, add_ofNat_assoc, gpr_write, ite_true, ite_false,
      reduceCtorEq, e₁, x26₁₁]
  refine WP.of_runBlock ⟨s₁₂, run₁₂, ?_⟩
  obtain he₁₂ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₂ := he₁₁.keep (fun r hr => og₁₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁₂ rd₁₂ wr₁₂
  obtain fT₁₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s₁₁.mem s₁₂.mem := by rw [m₁₂]; exact Proof.Cmac.frame_store2 _ _ _
  obtain hT₁₂ : blockAt s₁₂.mem (s₁₂.gpr .x19 + BitVec.ofNat 64 tO) = ofBytes (lensBlock al n) := by
    rw [he₁₂.x19, show tO = 96 from rfl, blockAt, m₁₂, Proof.Cmac.bytesAt_store2, le8_lens, le8_lens,
      toNat_ofNat_of_lt (show al < 2 ^ 64 by omega_arith), toNat_ofNat_of_lt hnlt]
    rfl
  obtain hk₁₂ : HKey (ctxH s.mem Ctx) s₁₂ := hk₁₁.of_v (by rw [v₁₂]) (by rw [v₁₂]) (by rw [v₁₂])
  obtain y₁₂ : s₁₂.v Y = ext8 (padStep (ctxH s.mem Ctx) (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (bytesAt s₁₀.mem (D + BitVec.ofNat 64 j) (n - j)))
      (padStep (ctxH s.mem Ctx) (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (bytesAt s₁₀.mem (D + BitVec.ofNat 64 j) (n - j))) := by rw [v₁₂]; exact y₁₁
  rw [WP.block_append_iff]
  refine WP.mono (mulT_ok hMK hk₁₂ y₁₂ (by rw [he₁₂.x19]; exact he₁₂.perm.wR (by decide)))
    fun s₁₃ ⟨y₁₃, _, o₁₃⟩ => ?_
  rw [hT₁₂] at y₁₃
  rw [WP.block_append_iff]
  refine WP.mono (storeY_ok y₁₃ (by rw [o₁₃.gpr, o₁₃.wr, he₁₂.x20]; exact he₁₂.perm.stW (by decide)))
    fun s₁₄ ⟨m₁₄, b₁₄, o₁₄⟩ => ?_
  obtain g₁₄ : s₁₄.gpr = s₁₂.gpr := by rw [o₁₄.gpr]; exact o₁₃.gpr
  rw [show s₁₃.gpr .x20 = W + BitVec.ofNat 64 16 by rw [o₁₃.gpr, he₁₂.x20]] at b₁₄ m₁₄
  obtain he₁₄ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₄ :=
    he₁₂.keep (fun r _ => by rw [g₁₄]) (by rw [o₁₄.sp, o₁₃.sp]) (by rw [o₁₄.rd, o₁₃.rd]) (by rw [o₁₄.wr, o₁₃.wr])
  obtain fY₁₄ : Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩] s₁₂.mem s₁₄.mem := by
    rw [m₁₄, o₁₃.mem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  -- Everything the working space has had written since the text was encrypted.
  obtain F₇₁₄ : Frame (wsR W) s₇.mem s₁₄.mem := by
    refine (Frame.sub (by rw [← m₁₀]; exact f₁₁) fun r hr => ?_).trans
      ((fT₁₂.sub fun r hr => ?_).trans (fY₁₄.sub fun r hr => ?_))
    all_goals simp only [List.mem_singleton] at hr; subst hr
    · exact sub_low (by decide)
    · exact sub_low (by decide)
    · exact sub_low' (by decide)
  obtain exS : ∀ {r : Region}, (∃ r' ∈ wsR W, Region.Sub r r') → ∃ r' ∈ wsR W ++ ex, Region.Sub r r' :=
    fun ⟨r', h, hs⟩ => ⟨r', List.mem_append_left _ h, hs⟩
  obtain F₄₁₄ : Frame (wsR W ++ ex) s₄.mem s₁₄.mem := by
    refine (Frame.sub (by rw [← r₅.mem]; exact h₇.frame) fun r hr => ?_).trans
      (F₇₁₄.mono fun r hr => List.mem_append_left _ hr)
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact exS (sub_low' (by decide))
    · exact exS (sub_low' (by decide))
    · exact exS (sub_scr (by decide))
    · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩
  obtain slot₁₄ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₁₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' => by
    rw [slot_kept F₄₁₄ (disj_ex (rs := wsR W) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base W (by decide) (by decide)
        · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
        · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))
        (exW (Lay.wSub (by decide)))) h₁ h₂', slot₄ d h₁ h₂']
  obtain x22₁₄ : s₁₄.gpr .x22 = BitVec.ofNat 64 R := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr,
      g₈ _ (by decide), h₇.kept .x22 (by decide), x22₃]
  obtain x28₁₄ : s₁₄.gpr .x28 = Tg := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr,
      g₈ _ (by decide), h₇.kept .x28 (by decide), x28₃]
  refine WP.mono (WP.with_rdwr (tagSeg_ok L (o := 0) (.inl rfl) he₁₄ (fun _ _ => rfl : Kept s₁₄.gpr s₁₄) x22₁₄ hRb))
    fun s₁₆ ⟨h₁₆, rd₁₆, wr₁₆⟩ => ?_
  refine WP.seq (WP.mono (WP.with_rdwr (tagCall_ok L v (.inl rfl) h₁₆)) fun s₁₇ ⟨h₁₇, rd₁₇, wr₁₇⟩ => ?_)
  obtain wr₁₇' : s₁₇.wr = s.wr := by
    rw [wr₁₇, wr₁₆, o₁₄.wr, o₁₃.wr, wr₁₂, wr₁₁, wr₁₀, r₅.wr, wr₄, r₃.wr, h₂.wr, wr₁]
  refine WP.seq (WP.mono (tagOut_ok h₁₇.env.x19 (by rw [h₁₇.kept .x28 (by decide), x28₁₄])
    (covers_left h₁₇.env.perm.w) (by rw [wr₁₇']; exact tW) (dtw.sub_right (Region.sub_prefix (by decide))))
    fun s₁₈ ⟨out₁₈, f₁₈, og₁₈, sp₁₈, rd₁₈, wr₁₈⟩ => ?_)
  obtain he₁₈ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₈ := h₁₇.env.keep (fun r hr => og₁₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁₈ rd₁₈ wr₁₈
  -- The frames, from the entry.
  obtain hT₁₇ : ∀ r ∈ tagFrame (W + BitVec.ofNat 64 16) W 0, ∃ r' ∈ wsR W, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_low (by decide)
    · exact sub_low (by decide)
    · exact sub_low (by decide)
    · exact sub_scr (by decide)
  obtain F₁₅₁₇ : Frame (wsR W) s₁₄.mem s₁₇.mem := h₁₇.frame.sub hT₁₇
  obtain F₄₁₇ : Frame (wsR W ++ ex) s₄.mem s₁₇.mem :=
    F₄₁₄.trans (F₁₅₁₇.mono fun r hr => List.mem_append_left _ hr)
  obtain sv₁₈ : SavedAt s₁₈.mem W s := by
    obtain h₁ := sv₁.frame h₂.frame fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact saved_j0Frame L r hr
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    rw [← r₃.mem] at h₁
    obtain h₂' := (h₁.frame h₄.frame fun r hr => saved_bodyFrame L ddW r (mem_bc hr)).frame F₄₁₇
      (disj_ex saved_wsR (exW (Lay.wSub (by decide))))
    exact h₂'.frame f₁₈ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₁₈.x19 he₁₈.sp (covers_left he₁₈.perm.w) sv₁₈) fun s' ⟨ga, hm, _⟩ =>
    (fun hi hp => ⟨⟨ga, hp⟩, hi⟩) ?_ ?_
  · -- `I`, from the call on: the rest writes only the working space and the tag.
    rw [hm]
    refine hI I₇ (((F₇₁₄.trans F₁₅₁₇).sub fun r hr => ⟨workR W, List.mem_cons_self .., ?_⟩).trans
      (f₁₈.sub fun r hr => ⟨⟨Tg, 16⟩, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Region.sub_prefix (by decide)
    · exact Lay.wSub (by decide)
    · exact Lay.wSub (by decide)
  rw [hm]
  -- What the frames keep.
  obtain dWS₁ : ∀ r ∈ wsR W, (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ddW.sub_right (Region.sub_prefix (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
  obtain cWS : ∀ r ∈ wsR W, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dcW.sub_right (Region.sub_prefix (by decide))
    · exact dcW.sub_right (Lay.wSub (by decide))
    · exact dcW.sub_right (Lay.wSub (by decide))
  obtain dF : ∀ r ∈ frontFrame' (W + BitVec.ofNat 64 16) W, (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ddW.sub_right sub16
    all_goals exact ddW.sub_right (Lay.wSub (by decide))
  obtain cF : ∀ r ∈ frontFrame' (W + BitVec.ofNat 64 16) W, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact dcW.sub_right sub16
    all_goals exact dcW.sub_right (Lay.wSub (by decide))
  obtain hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [r₃.mem, bytesAt_frame h₂.frame dF (by omega_arith), bytesAt_frame f₁ (keep_of_sub (entryR_work W) ddW) (by omega_arith)]
  obtain hc₃ : ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [r₃.mem, ciph_frame h₂.frame cF hRb, ciph_frame f₁ (keep_of_sub (entryR_work W) dcW) hRb]
  obtain hc₁₅ : ciphOf s₁₄.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [ciph_frame F₄₁₄ (disj_ex cWS hexC) hRb, ciph_frame h₄.frame (ctx_crFrame L hdat₃) hRb, hc₃]
  obtain hC : xorKs (ciphOf s₃.mem Ctx R) (inc32 J0) 0 (bytesAt s₃.mem D n) =
      gctr (ctxCiph s.mem Ctx R) (inc32 J0) (bytesAt s.mem D n) := by
    rw [hc₃, hD₃, Proof.Gcm.gctr_eq]; rfl
  obtain hdata : bytesAt s₁₈.mem D n = gctr (ctxCiph s.mem Ctx R) (inc32 J0) (bytesAt s.mem D n) := by
    rw [bytesAt_frame f₁₈ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ddt) (by omega_arith),
      bytesAt_frame F₄₁₇ (disj_ex dWS₁ hexD) (by omega_arith), out₄, hC]
  obtain hc₅ : bytesAt s₅.mem D n = gctr (ctxCiph s.mem Ctx R) (inc32 J0) (bytesAt s.mem D n) := by
    rw [r₅.mem, out₄, hC]
  obtain ht₁₀ : bytesAt s₁₀.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt s₅.mem (D + BitVec.ofNat 64 j) (n - j) := by
    rw [m₁₀, bytesAt_frame h₇.frame (disj_absEx (data_absFrame (.inr rfl) (hdat₅.drop hjn))
      fun r hr => (hexD r hr).sub_left (Offset.sub_base D (by omega_arith))) (by omega_arith)]
  obtain hsplit : bytesAt s₅.mem D n = bytesAt s₅.mem D j ++ bytesAt s₅.mem (D + BitVec.ofNat 64 j) (n - j) := by
    rw [← bytesAt_add, Nat.add_sub_cancel' hjn]
  -- `J₀`, still at the state.
  obtain hJ₁₅ : blockAt s₁₄.mem (W + BitVec.ofNat 64 16) = J0 := by
    obtain j₂ : blockAt s₂.mem (W + BitVec.ofNat 64 16) = J0 := by rw [h₂.j0]; exact hJ0
    obtain e₄ : blockAt s₄.mem (W + BitVec.ofNat 64 16) = blockAt s₃.mem (W + BitVec.ofNat 64 16) :=
      blockAt_frame h₄.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (hdat₃.ok.st.symm).sub_left (Region.sub_prefix (by decide))
        · exact st0_disj L (by decide) (by decide)
        · exact st0_w L ⟨by decide, by decide⟩
    obtain e₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16) = blockAt s₅.mem (W + BitVec.ofNat 64 16) :=
      blockAt_frame h₇.frame fun r hr => by
        simp only [List.mem_cons] at hr
        rcases hr with rfl | rfl | rfl | hr
        · exact st0_disj L (by decide) (by decide)
        · exact st0_disj L (by decide) (by decide)
        · exact st0_w L ⟨by decide, by decide⟩
        · exact exW (Lay.wSub (by decide)) r hr
    obtain dT : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r :=
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact st0_w L ⟨by decide, by decide⟩
    rw [blockAt_frame fY₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact st0_disj L (by decide) (by decide)),
      blockAt_frame fT₁₂ dT, blockAt_frame f₁₁ dT, m₁₀, e₇, r₅.mem, e₄, r₃.mem, j₂]
  -- The tag.
  obtain hlen : (gctr (ctxCiph s.mem Ctx R) (inc32 J0) (bytesAt s.mem D n)).length = n := by
    rw [← hc₅, length_bytesAt]
  obtain htag : bytesAt s₁₈.mem Tg 16 = Spec.Gcm.toBytes (ghashFrom (ctxH s.mem Ctx)
      (ghash (ctxH s.mem Ctx) (blocks (Proof.Gcm.padded (bytesAt s.mem A al)
        (gctr (ctxCiph s.mem Ctx R) (inc32 J0) (bytesAt s.mem D n)))))
      [ofBytes (lensBlock (bytesAt s.mem A al).length (gctr (ctxCiph s.mem Ctx R) (inc32 J0) (bytesAt s.mem D n)).length)] ^^^
      ctxCiph s.mem Ctx R J0) := by
    rw [out₁₈, ← add_ofNat_zero W, h₁₇.out, b₁₄, hJ₁₅, hc₁₅, hY₇, ht₁₀, ← hx₁, ← hc₅, hsplit,
      ghash_padded _ _ _ _ (by rw [length_bytesAt]; omega_arith) (by rw [length_bytesAt]; omega_arith), length_bytesAt,
      List.length_append, length_bytesAt, length_bytesAt, Nat.add_sub_cancel' hjn]
    rfl
  rw [hdata, htag, Spec.Gcm.encryptWith, Proof.Gcm.fullTag_eq,
    List.take_of_length_le (by rw [Proof.Cmac.toBytes_length]), ← hJ0]

/-- `runWithPX_ok`, for a call that writes only what `vg_ghash` does. -/
theorem runWithP_ok (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) {w : Nat} {extra extraW : List Region} {s s₁ : State}
    (hs : sealPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (h₁ : SealEntry w s s₁) (hx : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₁.gpr r = s.gpr r)
    (h12 : (s.gpr .x3).toNat = 12) (h16 : (s.gpr .x5).toNat ≤ 16) :
    WP isa (Impl.AesGcm.AArch64.Fast.runWithP v.callees cl) s₁ fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  WP.mono (runWithPX_ok v cl hMK (ex := []) (I := fun _ => True) hs (by simp) (by simp) (by simp)
    (fun _ _ => trivial) (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf _ =>
      WP.mono (hgh s' hc sY sS hrd hwr hsp hf) fun _ g => ⟨g, trivial⟩) h₁ hx h12 h16) fun _ q => q.1

end VG.Proof.AesGcm.AArch64.Fast
