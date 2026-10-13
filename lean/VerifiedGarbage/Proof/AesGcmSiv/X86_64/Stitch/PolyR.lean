module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Polyval
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM-SIV: POLYVAL in registers, for short messages

Untrusted: everything here is checked by Lean. `Impl.AesGcmSiv.X86_64Stitch.polyvalR`
keeps `Y` in lane 0 of `ymm2` and takes one block at a time: `hmul_ok`, GHASH's
product of `Y ⊕ X` with `H`, from `H' = H · x⁻¹` in `xmm3` (`Pclmul.step1`),
lane by lane as the interleaved loop's loads (`accR_ok`). `H'` is the
authentication key at `W + 16` as it is, since GHASH's key at `W + 64` is its
product with `x` (`x_φ_key`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

set_option linter.unusedSimpArgs false

open VG VG.X86_64 VG.X86_64.RegUpd VG.Proof.Gcm.Poly
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.WriteBytes (writeBytes)
open VG.Impl.AesGcmSiv.X86_64 (zero16 bO yO akO aadO alenO dataO lenO)
open VG.Proof.Gcm.X86_64.Stitch (in_rdwr)
open VG.Proof.AesGcm.X86_64 (GcmImpl)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduce_ok const_ok)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes yframe_of_lanes)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.AesGcmSiv.X86_64Stitch (hmul hstep hrBody htail habsorb hlens polyvalR hsmall polyvalS)
open VG.Spec.Gcm (Block blockAt ghashFrom)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm.X86_64 (revMask)

theorem lane_restR3 : laneSseBlock (restR 0 .xmm3) = some (accR true .xmm3) := rfl

/-- Each lane's product, reduced, into that lane of `ymm2`. -/
theorem reduce2_lanes (s : State) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block (Impl.Gcm.X86_64.Vpclmul.reduce .xmm2)) s fun s' =>
      (∀ l < 2, s'.lane .xmm2 l = Gcm.X86_64.Pclmul.reduce (prod (s.proj l))) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s s' := by
  refine WP.mono (WP.lanes (ss := Impl.Gcm.X86_64.Pclmul.reduce .xmm2) rfl fun l hl =>
      reduce_ok .xmm2 (s.proj l) (by decide) (by decide) (by decide) (by decide) (by simpa using h1 l hl))
    fun s' ⟨hk, hq⟩ => ⟨fun l hl => by simpa using (hq l hl).1,
      yframe_of_lanes hk fun l hl r hr => (hq l hl).2.xmm r hr⟩

/-- `Y ← (Y ⊕ X) · H` in lane 0 of `ymm2`, `X` in `xmm7`, from any `H'` in
`xmm3` with `x · H' = H`. -/
theorem hmul_ok {H : Block} (s : State) (h1 : ∀ l < 2, s.lane .xmm1 l = poly)
    (hH : x * φ (s.lane .xmm3 0) = φ H) :
    WP isa (.block hmul) s fun s' =>
      s'.lane .xmm2 0 = Spec.Gcm.mul (s.lane .xmm2 0 ^^^ s.lane .xmm7 0) H ∧
      YFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s s' := by
  simp only [hmul, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s) fun s₁ ⟨p₁, F₁, _⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff,
    show ([.vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm2)] : List Instr) ++ Impl.Gcm.X86_64.Vpclmul.acc .xmm7 .xmm3 =
      restR 0 .xmm3 from rfl]
  refine WP.mono (WP.lanes lane_restR3 fun l _ =>
      accR_ok true .xmm3 (s₁.proj l) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₂ ⟨k₂, q₂⟩ => ?_
  have F₂ : YFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s₁ s₂ :=
    yframe_of_lanes k₂ fun l hl r hr => (q₂ l hl).2.xmm r hr
  have h1₂ : ∀ l < 2, s₂.lane .xmm1 l = poly := fun l hl => by
    rw [F₂.lane _ (by decide) l hl, F₁.lane _ (by decide) l hl, h1 l hl]
  refine WP.mono (reduce2_lanes s₂ h1₂) fun s₃ ⟨r₃, F₃⟩ => ⟨?_, ?_⟩
  · have e := (q₂ 0 (by decide)).1
    simp only [State.proj_xmm, ite_true] at e
    rw [r₃ 0 (by decide), e]
    have p0 : prod (s₁.proj 0) = Prod.zero := p₁ 0 (by decide)
    simp only [p0, F₁.lane .xmm2 (by decide) 0 (by decide), F₁.lane .xmm7 (by decide) 0 (by decide),
      F₁.lane .xmm3 (by decide) 0 (by decide)]
    exact Gcm.X86_64.Pclmul.step1 H _ _ _ hH
  · refine ⟨by rw [F₃.gpr, F₂.gpr, F₁.gpr], by rw [F₃.mem, F₂.mem, F₁.mem], by rw [F₃.rd, F₂.rd, F₁.rd],
      by rw [F₃.wr, F₂.wr, F₁.wr], fun r hr l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [F₃.lane r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]) l hl,
      F₂.lane r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]) l hl,
      F₁.lane r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1]) l hl]

/-- GHASH's key is the authentication key times `x`: so the authentication
key is `H'` for it. -/
theorem x_φ_key (K : Block) : x * φ K = φ (GcmSiv.Polyval.mulXG K) := by
  rw [GcmSiv.Polyval.mulXG, φ_shr1]

/-- A block of 16 bytes loaded as it is: POLYVAL's field element. -/
theorem readW128_ofBytes (m : Mem) (p : Addr) : m.readW p 128 = Spec.GcmSiv.ofBytes (bytesAt m p 16) := by
  rw [GcmSiv.ofBytes_bytesAt, readW128_q]

/-- What POLYVAL in registers keeps: the masks, and `H'` for `H`. -/
structure RRegs (H : Block) (t : State) : Prop where
  m0 : t.lane .xmm0 0 = revMask
  m1 : ∀ l < 2, t.lane .xmm1 l = poly
  h : x * φ (t.lane .xmm3 0) = φ H

theorem RRegs.of_yframe {H : Block} {rs : List XReg} {t t' : State} (R : RRegs H t) (F : YFrame rs t t')
    (h0 : .xmm0 ∉ rs) (h1 : .xmm1 ∉ rs) (h3 : .xmm3 ∉ rs) : RRegs H t' :=
  ⟨by rw [F.lane _ h0 0 (by decide)]; exact R.m0, fun l hl => by rw [F.lane _ h1 l hl]; exact R.m1 l hl,
    by rw [F.lane _ h3 0 (by decide)]; exact R.h⟩

/-- `hmul` of the block at `rsi`. -/
theorem hstep_ok {H : Block} (t : State) (R : RRegs H t)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rsi) 16) :
    WP isa (.block hstep) t fun t' =>
      t'.lane .xmm2 0 = Spec.Gcm.mul (t.lane .xmm2 0 ^^^ Spec.GcmSiv.ofBytes (bytesAt t.mem (t.gpr .rsi) 16)) H ∧
      RRegs H t' ∧ t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  let t₁ := t.setV .l128 .xmm7 (t.mem.readW (t.gpr .rsi) 128) 0
  rw [hstep, List.singleton_append, WP.block_cons_iff]
  refine ⟨t₁, ?_, ?_⟩
  · simp only [isa, exec, State.load128, VG.Proof.Gcm.X86_64.Pclmul.ea_at, BitVec.ofInt_natCast,
      BitVec.add_zero, hin, ite_true, Option.map_some, t₁]
  have keep : ∀ r, r ≠ .xmm7 → ∀ l < 2, t₁.lane r l = t.lane r l := fun r hr l _ => by
    simp [t₁, State.lane_setV128, hr]
  have R₁ : RRegs H t₁ := ⟨by rw [keep _ (by decide) 0 (by decide)]; exact R.m0,
    fun l hl => by rw [keep _ (by decide) l hl]; exact R.m1 l hl, by rw [keep _ (by decide) 0 (by decide)]; exact R.h⟩
  refine WP.mono (hmul_ok t₁ R₁.m1 R₁.h) fun t' ⟨y', F⟩ => ⟨?_, R₁.of_yframe F (by decide) (by decide) (by decide),
    F.gpr, F.mem, F.rd, F.wr⟩
  rw [y', keep _ (by decide) 0 (by decide), ← readW128_ofBytes]
  simp [t₁, State.lane_setV128]

/-! ## The byte loop keeps the vector registers -/

theorem copyStepV {s : State} {S D : Addr} {i : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa Proof.AesGcm.X86_64.copyBody s = some s' ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  have e₁ := Proof.AesGcm.X86_64.ea_idx s .rsi hs hi
  have e₂ := Proof.AesGcm.X86_64.ea_idx s .rdi hd hi
  refine ⟨?s', ?run, ?x, ?y⟩
  case run =>
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff,
      Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow,
      BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self,
      false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false,
      BitVec.reduceSignExtend, Proof.AesGcm.X86_64.copyBody, Impl.AesGcm.X86_64.srcB, Impl.AesGcm.X86_64.dstB,
      imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true,
      ite_false, e₁, e₂, r, w]
    rfl
  all_goals rfl

/-- `copyLoop_ok`, and the vector registers kept. -/
theorem copyLoopV_ok (s : State) {S D : Addr} {n : Nat} (h : Proof.AesGcm.X86_64.LoopPre s S D n) :
    WP isa Impl.AesGcm.X86_64.copyLoop s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (BitVec.ofNat 32 0)) :=
    ⟨_, by simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block Proof.AesGcm.X86_64.copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi) ?_ (n - 0) _
    ⟨0, rfl, h.pos, r10₁, by simp [bytesAt, VG.WriteBytes.writeBytes_nil, mem_setReg],
      fun r h₁ h₂ => by simp [gpr_setReg, h₂], rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr, x, y⟩
  have hsi : t.gpr .rsi = S := by rw [g _ (by decide) (by decide), h.rsi]
  have hdi : t.gpr .rdi = D := by rw [g _ (by decide) (by decide), h.rdi]
  have r' : InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 i) 1 := by
    rw [rd, wr]; exact Proof.AesGcm.X86_64.in_of_covers h.rd hi (by have := h.lt; omega)
  have w' : InRegions t.wr (D + BitVec.ofNat 64 i) 1 := by
    rw [wr]; exact Proof.AesGcm.X86_64.in_of_covers h.wr hi (by have := h.lt; omega)
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := Proof.AesGcm.X86_64.copyStep_ok t hsi hdi r10
    (by rw [g _ (by decide) (by decide), h.rcx]) r' w'
  obtain ⟨t'', run'', x'', y''⟩ := copyStepV hsi hdi r10 r' w'
  obtain rfl : t' = t'' := Option.some.inj (run'.symm.trans run'')
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem S i).length = i := by simp [bytesAt]
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, Proof.AesGcm.X86_64.src_kept h.disj hi h.lt _ hlen, Proof.AesGcm.X86_64.bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc s.mem D (bytesAt s.mem S i) _ (by rw [hlen]; have := h.lt; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', Proof.AesGcm.X86_64.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by have := h.lt; omega)
      (by have := h.lt; omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr], by rw [x'', x],
      by rw [y'', y]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [r10', Proof.AesGcm.X86_64.succ_ofNat], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [x'', x],
      by rw [y'', y]⟩

/-! ## Absorbing in registers -/

/-- The block the last bytes go through. -/
abbrev bR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 16⟩

/-- What absorbing `xs` in registers leaves, from `t`. -/
structure RPost (K W SP : Addr) (H : Block) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame [bR W] t.mem t'.mem
  regs : RRegs H t'
  y : t'.lane .xmm2 0 = ghashFrom H (t.lane .xmm2 0) xs

theorem RPost.trans {K W SP : Addr} {H : Block} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : RPost K W SP H xs t t₁) (h₂ : RPost K W SP H ys t₁ t₂) : RPost K W SP H (xs ++ ys) t t₂ :=
  ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame, h₂.regs, by
    rw [h₂.y, h₁.y, Proof.Gcm.ghashFrom_append]⟩

/-- `add rsi, 16; sub rbx, 1`. -/
theorem rnext_ok (s : State) :
    WP isa (.block [.alu .add .rsi (imm 16), .alu .sub .rbx (imm 1)]) s
      fun s' => s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rbx = s.gpr .rbx - 1 ∧
        s'.zf = some ((s.gpr .rbx - 1) == 0) ∧
        (∀ r, r ≠ .rsi → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (BitVec.ofNat 32 16) = 16 := by decide
  have e1 : BitVec.signExtend 64 (BitVec.ofNat 32 1) = 1 := by decide
  apply WP.of_runBlock
  simp only [imm, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The loop's state: `d` of the `b` blocks at `Q` absorbed. -/
structure LInv (K W SP : Addr) (H : Block) (Q : Addr) (b d : Nat) (t t' : State) : Prop where
  post : RPost K W SP H (elemsAt t.mem Q d) t t'
  rsi : t'.gpr .rsi = Q + BitVec.ofNat 64 (16 * d)
  rbx : t'.gpr .rbx = BitVec.ofNat 64 (b - d)
  rbp : t'.gpr .rbp = t.gpr .rbp
  mem : t'.mem = t.mem

/-- The `b` (at least 1) blocks at `Q`, one at a time. -/
theorem rloop_ok {K W SP : Addr} {H : Block} {t : State} (E : Env K W SP t) (R : RRegs H t)
    {Q : Addr} {b : Nat} (hb : 1 ≤ b) (hQ : Buf K W SP t Q (16 * b))
    (hsi : t.gpr .rsi = Q) (hbx : t.gpr .rbx = BitVec.ofNat 64 b) :
    WP isa (.loop (.block hrBody) .ne) t fun t' => LInv K W SP H Q b b t t' := by
  have hb64 : b < 2 ^ 64 := by have := hQ.lt; omega
  refine WP.loop (M := isa) (body := .block hrBody) (c := .ne)
    (fun (m : Nat) (t' : State) => ∃ d, m = b - d ∧ d < b ∧ LInv K W SP H Q b d t t') ?_ (b - 0) t
    ⟨0, rfl, hb, ⟨⟨E, rfl, rfl, Frame.refl _ _, R, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [hsi, Nat.mul_zero, BitVec.add_zero], by rw [hbx, Nat.sub_zero], rfl, rfl⟩⟩
  rintro m t' ⟨d, rfl, hd, I⟩
  have hin : InRegions (t'.rd ++ t'.wr) (t'.gpr .rsi) 16 := by
    rw [I.rsi, I.post.rd, I.post.wr]
    exact Proof.AesGcm.X86_64.in_off hQ.rd (by omega) hQ.lt
  rw [hrBody, WP.block_append_iff]
  refine WP.mono (hstep_ok t' I.post.regs hin) fun t₁ ⟨y₁, R₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (rnext_ok t₁) fun t₂ ⟨si₂, bx₂, zf₂, g₂, l₂, m₂, rd₂, wr₂⟩ => ?_
  have R₂ : RRegs H t₂ := ⟨by rw [l₂]; exact R₁.m0, fun l hl => by rw [l₂]; exact R₁.m1 l hl, by rw [l₂]; exact R₁.h⟩
  have gk : ∀ r, r ≠ .rsi → r ≠ .rbx → t₂.gpr r = t'.gpr r := fun r h₁ h₂ => by rw [g₂ r h₁ h₂, g₁]
  have I' : LInv K W SP H Q b (d + 1) t t₂ := by
    refine ⟨⟨I.post.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact gk _ (by decide) (by decide))
        (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]), by rw [rd₂, rd₁, I.post.rd], by rw [wr₂, wr₁, I.post.wr],
        by rw [m₂, m₁]; exact I.post.frame, R₂, ?_⟩, ?_, ?_, ?_, by rw [m₂, m₁, I.mem]⟩
    · rw [l₂, y₁, I.post.y, I.rsi, I.mem]
      simp only [elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil,
        Proof.Gcm.ghashFrom_append]
      rfl
    · rw [si₂, g₁, I.rsi, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat_assoc,
        show 16 * d + 16 = 16 * (d + 1) by omega]
    · rw [bx₂, g₁, I.rbx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
      congr 1
    · rw [gk _ (by decide) (by decide), I.rbp]
  have hz : t₂.zf = some (decide (b - (d + 1) = 0)) := by
    rw [zf₂, g₁, I.rbx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    congr 1; simp only [decide_eq_decide]; omega
  by_cases he : b - (d + 1) = 0
  · left
    have hdb : d + 1 = b := by omega
    exact ⟨by simp [eval, hz, he], hdb ▸ I'⟩
  · right
    exact ⟨by simp [eval, hz, he], b - (d + 1), by omega, d + 1, rfl, by omega, I'⟩

/-- The last `r` (1 to 15) bytes at `rsi`, padded with zeros at `W + 128`,
absorbed. -/
theorem rtail_ok {K W SP : Addr} (L : Lay K W SP) {H : Block} {t : State} (E : Env K W SP t) (R : RRegs H t)
    {P : Addr} {r : Nat} (hr1 : 1 ≤ r) (hr : r < 16) (hP : Buf K W SP t P r)
    (hsi : t.gpr .rsi = P) (hbp : t.gpr .rbp = BitVec.ofNat 64 r) :
    WP isa htail t
      (RPost K W SP H [Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have h15 := E.r15
  have hw := L.ww
  have w₀ := E.perm.wW (show 128 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 136 + 8 ≤ 3816 by decide)
  -- The block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, hdi₁, hcx₁, hg₁, hrd₁, hwr₁, hx₁, hy₁⟩ : ∃ t₁ : State,
      runBlock isa (zero16 bO ++ ptr .rdi .r15 bO ++ [.mov .rcx (.reg .rbp)]) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero2 t.mem (W + BitVec.ofNat 64 128) ∧ t₁.gpr .rdi = W + BitVec.ofNat 64 128 ∧
      t₁.gpr .rcx = BitVec.ofNat 64 r ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rcx → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧
      t₁.xmm = t.xmm ∧ t₁.ymmHi = t.ymmHi := by
    refine ⟨_, by srun [zero16, h15, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, Proof.Cmac.zero2, add_ofNat_assoc]
      rfl
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp]
    · intro r h₁ h₂ h₃; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, h₃, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have lp : Proof.AesGcm.X86_64.LoopPre t₁ P (W + BitVec.ofNat 64 128) r :=
    ⟨by rw [hg₁ _ (by decide) (by decide) (by decide), hsi], hdi₁, hcx₁, hr1, by omega,
      by rw [hrd₁, hwr₁]; exact hP.rd, by rw [hwr₁]; exact E.perm.wC (by omega),
      hP.w.sub_right (Lay.wSub (by omega))⟩
  refine WP.seq (WP.mono (copyLoopV_ok t₁ lp) fun t₂ ⟨hm₂, hg₂, hrd₂, hwr₂, hx₂, hy₂⟩ => ?_)
  -- The data is outside the zeroed block.
  have hd₁ : bytesAt t₁.mem P r = bytesAt t.mem P r := by
    rw [hm₁, Proof.Cmac.zero2]
    exact Proof.AesGcm.X86_64.bytesAt_frame
      (((Frame.refl [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region)] _).writeW (List.mem_singleton_self _) _
        (Offset.contains W (Nat.le_refl _) (by decide) (by omega))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide)))
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by omega)
  have hb₂ : bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := Proof.AesGcm.X86_64.length_bytesAt t.mem P r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega), hl]
  have h15₂ : t₂.gpr .r15 = W := by
    rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide), h15]
  -- What the pieces wrote.
  have fr₂ : Frame [bR W] t.mem t₂.mem := by
    have mB : (⟨W + BitVec.ofNat 64 128, 16⟩ : Region) ∈ [bR W] := List.mem_singleton_self _
    have f₁ : Frame [bR W] t.mem t₁.mem := by
      rw [hm₁, Proof.Cmac.zero2]
      exact ((Frame.refl _ _).writeW mB _ (Offset.contains W (Nat.le_refl _) (by decide) (by omega))).writeW mB _
        (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
    have f₂ : Frame [bR W] t₁.mem t₂.mem := by
      rw [hm₂]
      exact (Proof.AesGcm.X86_64.writeBytes_frame' _ (Proof.AesGcm.X86_64.length_bytesAt _ _ _)).sub
        fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, mB, Region.sub_prefix (by omega)⟩
    exact f₁.trans f₂
  -- The padded block absorbed.
  obtain ⟨t₃, run₃, si₃, hg₃, hm₃, hrd₃, hwr₃, hx₃, hy₃⟩ : ∃ t₃ : State,
      runBlock isa (ptr .rsi .r15 bO) t₂ = some t₃ ∧ t₃.gpr .rsi = W + BitVec.ofNat 64 128 ∧
      (∀ r, r ≠ .rsi → t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr ∧
      t₃.xmm = t₂.xmm ∧ t₃.ymmHi = t₂.ymmHi := by
    refine ⟨_, by srun [h15₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₂]
    · intro r h₁; simp only [gpr_arithFlags, gpr_setReg, h₁, ite_false]
    all_goals rfl
  have lk : ∀ q l, t₃.lane q l = t.lane q l := fun q l => by
    simp only [State.lane, hx₃, hy₃, hx₂, hy₂, hx₁, hy₁]
  have R₃ : RRegs H t₃ := ⟨by rw [lk]; exact R.m0, fun l hl => by rw [lk]; exact R.m1 l hl, by rw [lk]; exact R.h⟩
  have hin : InRegions (t₃.rd ++ t₃.wr) (t₃.gpr .rsi) 16 := by
    rw [si₃, hrd₃, hwr₃, hrd₂, hwr₂, hrd₁, hwr₁]
    exact E.perm.wR (show 128 + 16 ≤ 3816 by decide)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨t₃, run₃, WP.mono (hstep_ok t₃ R₃ hin) fun t₄ ⟨y₄, R₄, g₄, m₄, rd₄, wr₄⟩ => ?_⟩
  refine ⟨E.keep (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;>
        rw [g₄, hg₃ _ (by decide), hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide)])
      (by rw [rd₄, hrd₃, hrd₂, hrd₁]) (by rw [wr₄, hwr₃, hwr₂, hwr₁]),
    by rw [rd₄, hrd₃, hrd₂, hrd₁], by rw [wr₄, hwr₃, hwr₂, hwr₁], by rw [m₄, hm₃]; exact fr₂, R₄, ?_⟩
  rw [y₄, lk, si₃, hm₃, hb₂]
  rfl

theorem buf_bR {K W SP : Addr} {s : State} {Q : Addr} {k : Nat} (h : Buf K W SP s Q k) :
    ∀ r ∈ [bR W], (⟨Q, k⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact h.w.sub_right (Lay.wSub (by decide))

theorem RPost.of_eq {K W SP : Addr} {H : Block} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : RPost K W SP H xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr)
    (hy : t₁.lane .xmm2 0 = t.lane .xmm2 0) : RPost K W SP H xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, h.regs, by rw [h.y, hy]⟩

/-- The `rbp` bytes at `r12`, padded with zeros to whole blocks, absorbed in
registers. -/
theorem habsorb_ok {K W SP : Addr} (L : Lay K W SP) {H : Block} {t : State} (E : Env K W SP t) (R : RRegs H t)
    {Q : Addr} {n : Nat} (hQ : Buf K W SP t Q n) (h12 : t.gpr .r12 = Q) (hbp : t.gpr .rbp = BitVec.ofNat 64 n) :
    WP isa habsorb t (RPost K W SP H (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem Q n))) t) := by
  have hn := hQ.lt
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [Proof.AesGcm.X86_64.toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  obtain ⟨t₁, run₁, hbx₁, hbp₁, hsi₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁, hx₁, hy₁⟩ : ∃ t₁ : State,
      runBlock isa [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .mov .rsi (.reg .r12),
        .alu .test .rbx (.reg .rbx)] t = some t₁ ∧
      t₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₁.gpr .rsi = Q ∧
      t₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .rsi → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ t₁.xmm = t.xmm ∧ t₁.ymmHi = t.ymmHi := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp,
        Proof.AesGcm.X86_64.shr4 _ hn]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp, hand]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h12]
    · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
        reduceCtorEq, hbp, Proof.AesGcm.X86_64.shr4 _ hn]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]
    · intro r h₁ h₂ h₃; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have lk₁ : ∀ q l, t₁.lane q l = t.lane q l := fun q l => by simp only [State.lane, hx₁, hy₁]
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have R₁ : RRegs H t₁ := ⟨by rw [lk₁]; exact R.m0, fun l hl => by rw [lk₁]; exact R.m1 l hl, by rw [lk₁]; exact R.h⟩
  have hQ₁ := hQ.of_eq hrd₁ hwr₁
  -- The whole blocks.
  have hmid : WP isa (.ite .e (.block []) (.loop (.block hrBody) .ne)) t₁ fun t₂ =>
      RPost K W SP H (elemsAt t.mem Q (n / 16)) t₁ t₂ ∧ t₂.gpr .rsi = Q + BitVec.ofNat 64 (16 * (n / 16)) ∧
      t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₂.mem = t₁.mem := by
    refine WP.ite (decide (n / 16 = 0)) (eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : n / 16 = 0 := by simpa using ht
      refine WP.block_nil ⟨⟨E₁, rfl, rfl, Frame.refl _ _, R₁, by simp [h0, elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
        by rw [hsi₁, h0, Nat.mul_zero, BitVec.add_zero], hbp₁, rfl⟩
    · have h0 : n / 16 ≠ 0 := by simpa using hf
      refine WP.mono (rloop_ok E₁ R₁ (by omega) (hQ₁.take (by omega)) hsi₁ hbx₁) fun t₂ I => ?_
      have Ip := I.post
      rw [hm₁] at Ip
      exact ⟨Ip, I.rsi, I.rbp.trans hbp₁, I.mem⟩
  refine WP.seq (WP.mono hmid fun t₂ ⟨P₂, si₂, rbp₂, m₂⟩ => ?_)
  have P₂' := P₂.of_eq hm₁ hrd₁ hwr₁ (lk₁ _ _)
  obtain ⟨t₃, run₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃, hx₃, hy₃⟩ : ∃ t₃ : State,
      runBlock isa [.alu .test .rbp (.reg .rbp)] t₂ = some t₃ ∧
      t₃.zf = some (decide (n % 16 = 0)) ∧ (∀ r, t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr ∧ t₃.xmm = t₂.xmm ∧ t₃.ymmHi = t₂.ymmHi := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, rbp₂]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]
    · intro r; rfl
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have lk₃ : ∀ q l, t₃.lane q l = t₂.lane q l := fun q l => by simp only [State.lane, hx₃, hy₃]
  have P₃ : RPost K W SP H (elemsAt t.mem Q (n / 16)) t t₃ :=
    ⟨P₂'.env.keep (fun r _ => hg₃ r) hrd₃ hwr₃, hrd₃.trans P₂'.rd, hwr₃.trans P₂'.wr, hm₃ ▸ P₂'.frame,
      ⟨by rw [lk₃]; exact P₂'.regs.m0, fun l hl => by rw [lk₃]; exact P₂'.regs.m1 l hl,
        by rw [lk₃]; exact P₂'.regs.h⟩, by rw [lk₃, P₂'.y]⟩
  rw [elems_pad16_bytesAt]
  refine WP.ite (decide (n % 16 = 0)) (eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil P₃
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hP : Buf K W SP t₃ (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hQ.slice (by omega)).of_eq P₃.rd P₃.wr
    refine WP.mono (rtail_ok L P₃.env P₃.regs (by omega) (by omega) hP (by rw [hg₃, si₂]) (by rw [hg₃, rbp₂]))
      fun t₄ T => ?_
    have e := Proof.AesGcm.X86_64.bytesAt_frame P₃.frame (buf_bR (hQ.slice (a := 16 * (n / 16)) (k := n % 16)
      (by omega))) (by omega)
    rw [e] at T
    exact P₃.trans T

/-! ## The setup -/

/-- The constants, `H'` (the authentication key at `W + 16`), `Y = 0`, and the
additional data's address and length. -/
theorem rsetup_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) :
    WP isa (.block (Impl.AesGcmSiv.X86_64Stitch.hsetup ++
      ([.mov .r12 (.mem (Impl.AesGcm.X86_64.at_ .r15 aadO)), .mov .rbp (.mem (Impl.AesGcm.X86_64.at_ .r15 alenO))] :
        List Instr))) t fun t₁ =>
      RRegs (GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16))) t₁ ∧
      t₁.lane .xmm2 0 = 0 ∧ t₁.gpr .r12 = A ∧ t₁.gpr .rbp = BitVec.ofNat 64 al ∧
      (∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
  simp only [Impl.AesGcmSiv.X86_64Stitch.hsetup, List.append_assoc]
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ _ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₂ (by decide)) fun s₃ ⟨c₃, o₃⟩ => ?_
  have o := o₂.trans o₃
  have h15 : s₃.gpr .r15 = W := by rw [o.gpr _ (by decide)]; exact E.r15
  have rK : InRegions (s₃.rd ++ s₃.wr) (W + BitVec.ofNat 64 16) 16 := by
    rw [o.rd, o.wr]; exact E.perm.wR (show 16 + 16 ≤ 3816 by decide)
  have rA : InRegions (s₃.rd ++ s₃.wr) (W + BitVec.ofNat 64 216) 8 := by
    rw [o.rd, o.wr]; exact E.perm.wR (show 216 + 8 ≤ 3816 by decide)
  have rL : InRegions (s₃.rd ++ s₃.wr) (W + BitVec.ofNat 64 224) 8 := by
    rw [o.rd, o.wr]; exact E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have x0 : s₃.xmm .xmm0 = revMask := by rw [o₃.xmm _ (by decide), c₂, VG.Proof.Gcm.X86_64.Pclmul.rev_eq]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa,
    State.load128, VG.Proof.Gcm.X86_64.Pclmul.ea_at, h15, rK, VG.Proof.Gcm.X86_64.Vpclmul.getLsbD_one8, Option.map_some, Option.bind_some,
    readSrc, State.load64, State.ea, Impl.AesGcm.X86_64.at_, VG.Proof.AesGcm.X86_64.offset_nat, rA, rL,
    ite_true, Option.some.injEq, exists_eq_left', List.cons_append, List.nil_append, akO, aadO, alenO,
    Impl.Gcm.X86_64.Pclmul.at_, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr, State.setV_ea,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, Int.cast_ofNat_Int, BitVec.ofInt_ofNat, h15, rA, rL]
  have hm : s₃.mem = t.mem := o.mem
  have lr : ∀ (u : State) (q : Reg) (v : BitVec 64) (x : XReg) (l : Nat), (u.setReg q v).lane x l = u.lane x l :=
    fun _ _ _ _ _ => rfl
  refine ⟨⟨?_, fun l hl => ?_, ?_⟩, ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, by rw [hm], by rw [o.rd]; rfl,
    by rw [o.wr]; rfl⟩
  · simp only [lr, State.lane_setV128, State.lane_setV256, reduceCtorEq, ite_false]
    simpa only [State.lane, ite_true] using x0
  · simp only [lr, State.lane_setV128, State.lane_setV256, reduceCtorEq, ite_false, ite_true]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simpa [State.lane] using c₃
  · simp only [lr, State.lane_setV128, State.lane_setV256, reduceCtorEq, ite_false, ite_true]
    rw [hm, readW128_ofBytes, x_φ_key]
  · simp only [lr, State.lane_setV128, ite_true, VBinOp.sse, VG.Proof.Gcm.X86_64.Pclmul.eval_pxor,
      BitVec.xor_self]
    rfl
  · rw [hm, S.aad]
  · rw [hm, S.alen]
  · simp only [h₃, h₂, ite_false]
    rw [o.gpr r h₁]
    rfl

/-! ## The lengths -/

/-- `rax ← 8 · v`, from the slot at `W + o`. -/
theorem ld8_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {o v : Nat} (ho : o + 8 ≤ 3816)
    (hv : t.mem.readW (W + BitVec.ofNat 64 o) 64 = BitVec.ofNat 64 v) (hv' : v < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 o)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax)]) t fun t' =>
      t'.gpr .rax = BitVec.ofNat 64 (8 * v) ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧ t'.xmm = t.xmm ∧
      t'.ymmHi = t.ymmHi ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have r₀ := E.perm.wR ho
  apply WP.of_runBlock
  refine ⟨_, by srun [h15, r₀], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, hv, Proof.AesGcm.X86_64.times8_val,
      Proof.AesGcm.X86_64.toNat_ofNat_of_lt hv']
  · intro r hr; simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]
  all_goals rfl

/-- `vmovq x, rax`. -/
theorem vmovq_ok (x : XReg) (t : State) :
    WP isa (.block [.vop (.vmovq x .rax)]) t fun t' =>
      t'.lane x 0 = (0 : BitVec 64) ++ t.gpr .rax ∧ (∀ r, r ≠ x → ∀ l, t'.lane r l = t.lane r l) ∧
      t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  apply WP.of_runBlock
  refine ⟨_, rfl, ?_, fun r hr l => ?_, rfl, rfl, rfl, rfl⟩
  · simp [VOp.exec, State.lane_setV128]
  · simp [VOp.exec, State.lane_setV128, hr]

theorem punpcklqdq_zero (a b : BitVec 64) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ a) ((0 : BitVec 64) ++ b) = b ++ a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64 <;> simp [h] <;> omega

/-- The lengths block built in `xmm7`: `le64(8 · aad_len) ‖ le64(8 · len)`
as a little-endian number. -/
theorem rlensBlock_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {al n : Nat}
    (hal : t.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    WP isa (.block ([.mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .vop (.vmovq .xmm5 .rax),
      .mov .rax (.mem (at_ .r15 lenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .vop (.vmovq .xmm6 .rax), .vop (.vbin .vpunpcklqdq .l128 .xmm7 .xmm5 .xmm6)] :
        List Instr)) t fun t' =>
      t'.lane .xmm7 0 = Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n)) ∧
      (∀ r, r ≠ .xmm5 → r ≠ .xmm6 → r ≠ .xmm7 → ∀ l, t'.lane r l = t.lane r l) ∧
      (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  rw [show ([.mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .vop (.vmovq .xmm5 .rax),
      .mov .rax (.mem (at_ .r15 lenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .vop (.vmovq .xmm6 .rax), .vop (.vbin .vpunpcklqdq .l128 .xmm7 .xmm5 .xmm6)] :
        List Instr) =
      ([.mov .rax (.mem (at_ .r15 224)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax)] : List Instr) ++ [.vop (.vmovq .xmm5 .rax)] ++
      ([.mov .rax (.mem (at_ .r15 240)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax)] : List Instr) ++ [.vop (.vmovq .xmm6 .rax)] ++
      [.vop (.vbin .vpunpcklqdq .l128 .xmm7 .xmm5 .xmm6)] from rfl]
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ld8_ok E (show 224 + 8 ≤ 3816 by decide) hal hal') fun t₁ ⟨a₁, g₁, x₁, y₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (vmovq_ok .xmm5 t₁) fun t₂ ⟨v₂, l₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  have E₂ : Env K W SP t₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [g₂, g₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  refine WP.mono (ld8_ok E₂ (show 240 + 8 ≤ 3816 by decide) (by rw [m₂, m₁]; exact hn) hn')
    fun t₃ ⟨a₃, g₃, x₃, y₃, m₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (vmovq_ok .xmm6 t₃) fun t₄ ⟨v₄, l₄, g₄, m₄, rd₄, wr₄⟩ => ?_
  have lk₃ : ∀ r l, t₃.lane r l = t₂.lane r l := fun r l => by simp only [State.lane, x₃, y₃]
  have lk₁ : ∀ r l, t₁.lane r l = t.lane r l := fun r l => by simp only [State.lane, x₁, y₁]
  apply WP.of_runBlock
  refine ⟨_, rfl, ?_, fun r h5 h6 h7 l => ?_, fun r hr => ?_, m₄.trans (m₃.trans (m₂.trans m₁)),
    rd₄.trans (rd₃.trans (rd₂.trans rd₁)), wr₄.trans (wr₃.trans (wr₂.trans wr₁))⟩
  · have e5 : t₄.lane .xmm5 0 = (0 : BitVec 64) ++ BitVec.ofNat 64 (8 * al) := by
      rw [l₄ _ (by decide), lk₃, v₂, a₁]
    have e6 : t₄.lane .xmm6 0 = (0 : BitVec 64) ++ BitVec.ofNat 64 (8 * n) := by rw [v₄, a₃]
    simp only [VOp.exec, State.lane_setV128, ite_true, VBinOp.sse]
    rw [e5, e6, punpcklqdq_zero, GcmSiv.le64_le8, GcmSiv.le64_le8, GcmSiv.ofBytes_le8]
  · simp only [VOp.exec, State.lane_setV128, h7, ite_false]
    rw [l₄ r h6, lk₃, l₂ r h5, lk₁]
  · simp only [VOp.exec, State.setV_gpr]
    rw [g₄, g₃ r hr, g₂, g₁ r hr]

/-- The lengths block absorbed, and `Y` stored at `W + 80` in GHASH's order. -/
theorem rlens_ok {K W SP : Addr} (L : Lay K W SP) {H : Block} {t : State} (E : Env K W SP t) (R : RRegs H t)
    {al n : Nat} (hal : t.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    WP isa (.block hlens) t fun t' =>
      blockAt t'.mem (W + BitVec.ofNat 64 80) = Spec.Gcm.mul (t.lane .xmm2 0 ^^^
        Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))) H ∧
      Frame [⟨W + BitVec.ofNat 64 80, 16⟩] t.mem t'.mem ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hw := L.ww
  rw [hlens, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rlensBlock_ok E hal hn hal' hn') fun t₁ ⟨v₁, l₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have R₁ : RRegs H t₁ := ⟨by rw [l₁ _ (by decide) (by decide) (by decide)]; exact R.m0,
    fun l hl => by rw [l₁ _ (by decide) (by decide) (by decide)]; exact R.m1 l hl,
    by rw [l₁ _ (by decide) (by decide) (by decide)]; exact R.h⟩
  refine WP.mono (hmul_ok t₁ R₁.m1 R₁.h) fun t₂ ⟨y₂, F₂⟩ => ?_
  have m0 : t₂.xmm .xmm0 = revMask := by
    have := F₂.lane .xmm0 (by decide) 0 (by decide); simp only [State.lane, ite_true] at this
    rw [this]; simpa only [State.lane, ite_true] using R₁.m0
  have h15 : t₂.gpr .r15 = W := by rw [F₂.gpr, g₁ _ (by decide)]; exact E.r15
  have hin : InRegions t₂.wr (W + BitVec.ofNat 64 80) 16 := by
    rw [F₂.wr, wr₁]; exact E.perm.wW (show 80 + 16 ≤ 3816 by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, State.setV, State.store128_eq,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, VBinOp.sse, State.lane, ite_true, h15, BitVec.ofInt_natCast, yO, hin, m0,
    Option.some.injEq, exists_eq_left', Option.bind_some]
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · show blockAt (t₂.mem.writeW _ _) _ = _
    rw [VG.Proof.Gcm.X86_64.blockAt_store]
    have e := y₂; simp only [State.lane, ite_true] at e
    have v' : t₁.xmm .xmm7 = Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n)) := by
      simpa only [State.lane, ite_true] using v₁
    have y' : t₁.xmm .xmm2 = t.xmm .xmm2 := by
      simpa only [State.lane, ite_true] using l₁ .xmm2 (by decide) (by decide) (by decide) 0
    rw [e, v', y']
  · show Frame _ t.mem (t₂.mem.writeW _ _)
    rw [F₂.mem, m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · show t₂.gpr r = _
    rw [F₂.gpr, g₁ r hr]
  · show t₂.rd = _; rw [F₂.rd, rd₁]
  · show t₂.wr = _; rw [F₂.wr, wr₁]

/-! ## POLYVAL in registers -/

theorem frame_absR {W SP : Addr} {m m' : Mem} {rs : List Region} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, r ∈ absR W SP) : Frame (absR W SP) m m' :=
  h.mono hs

/-- `polyvalR`: POLYVAL of the padded additional data, the padded data and
the lengths block, in registers, and the tag input. -/
theorem polyvalR_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al)
    (hD : Buf K W SP t D n) (hN : Buf K W SP t N 12)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) :
    WP isa polyvalR t (PolyPost K W SP N A D al n t) := by
  have h15 := E.r15
  refine WP.seq (WP.mono (rsetup_ok E S) fun t₁ ⟨R₁, y₁, a₁, l₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) rd₁ wr₁
  refine WP.seq (WP.mono (habsorb_ok L E₁ R₁ (hA.of_eq rd₁ wr₁) a₁ l₁) fun t₂ P₂ => ?_)
  have fB : Frame [bR W] t.mem t₂.mem := m₁ ▸ P₂.frame
  have S₂ : Slots W R N A D al n t₂.mem := S.absR L (frame_absR fB (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp))
  have h15₂ : t₂.gpr .r15 = W := P₂.env.r15
  have rD := P₂.env.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rN := P₂.env.perm.wR (show 240 + 8 ≤ 3816 by decide)
  obtain ⟨t₃, run₃, d₃, n₃, g₃, m₃, rd₃, wr₃, x₃, y₃⟩ : ∃ t₃ : State,
      runBlock isa [.mov .r12 (.mem (Impl.AesGcm.X86_64.at_ .r15 dataO)),
        .mov .rbp (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO))] t₂ = some t₃ ∧
      t₃.gpr .r12 = D ∧ t₃.gpr .rbp = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → t₃.gpr r = t₂.gpr r) ∧
      t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr ∧ t₃.xmm = t₂.xmm ∧ t₃.ymmHi = t₂.ymmHi := by
    refine ⟨_, by srun [h15₂, rD, rN], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, S₂.data]
    · simp only [gpr_setReg, ite_true, S₂.len]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have lk₃ : ∀ q l, t₃.lane q l = t₂.lane q l := fun q l => by simp only [State.lane, x₃, y₃]
  have E₃ : Env K W SP t₃ := P₂.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
  have R₃ : RRegs _ t₃ := ⟨by rw [lk₃]; exact P₂.regs.m0, fun l hl => by rw [lk₃]; exact P₂.regs.m1 l hl,
    by rw [lk₃]; exact P₂.regs.h⟩
  have hD₃ : Buf K W SP t₃ D n := hD.of_eq (by rw [rd₃, P₂.rd, rd₁]) (by rw [wr₃, P₂.wr, wr₁])
  refine WP.seq (WP.mono (habsorb_ok L E₃ R₃ hD₃ d₃ n₃) fun t₄ P₄ => ?_)
  have S₄ : Slots W R N A D al n t₄.mem := S₂.absR L (frame_absR (m₃ ▸ P₄.frame) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp))
  rw [WP.block_append_iff]
  refine WP.mono (rlens_ok L P₄.env P₄.regs S₄.alen S₄.len hA.lt hD.lt) fun t₅ ⟨b₅, f₅, g₅, rd₅, wr₅⟩ => ?_
  have E₅ : Env K W SP t₅ := P₄.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide)) rd₅ wr₅
  have fr : Frame (absR W SP) t.mem t₅.mem := by
    refine ((frame_absR fB ?_).trans (frame_absR (m₃ ▸ P₄.frame) ?_)).trans (frame_absR f₅ ?_) <;>
      intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr <;> simp
  have hDb : bytesAt t₃.mem D n = bytesAt t.mem D n := by
    rw [m₃]; exact Proof.AesGcm.X86_64.bytesAt_frame fB (buf_bR hD) (by have := hD.lt; omega)
  refine polyPost_ok L S hN hG hY ⟨E₅, by rw [rd₅, P₄.rd, rd₃, P₂.rd, rd₁], by rw [wr₅, P₄.wr, wr₃, P₂.wr, wr₁],
    fr, ?_⟩
  rw [b₅, P₄.y, lk₃, P₂.y, y₁, hG, hY, hDb, m₁, Proof.Gcm.ghashFrom_append, Proof.Gcm.ghashFrom_append]
  rfl

/-- `polyvalS`'s test: whether the whole blocks number fewer than 10. -/
theorem smallCond_run {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (ha : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa hsmall t = some t₁ ∧
      t₁.cf = some (decide (al / 16 + n / 16 < 10)) ∧ (∀ r, r ≠ .rax → r ≠ .rdx → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ t₁.xmm = t.xmm ∧ t₁.ymmHi = t.ymmHi := by
  have h15 := E.r15
  have rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have rN := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sL := S.alen
  have sN := S.len
  refine ⟨_, by srun [hsmall, h15, rL, rN, sL, sN], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, gpr_arithFlags, gpr_setFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq,
      Proof.AesGcm.X86_64.shr4 _ ha, Proof.AesGcm.X86_64.shr4 _ hn, Proof.AesGcm.X86_64.ofNat_add_ofNat,
      Proof.AesGcm.X86_64.toNat_ofNat_of_lt (show al / 16 + n / 16 < 2 ^ 64 by omega)]
    rfl
  · intro r h₁ h₂; simp only [gpr_arithFlags, gpr_setFlags, gpr_setReg, h₁, h₂, ite_false]
  all_goals rfl

/-- `polyvalS`: POLYVAL and the tag input, in registers when the whole blocks
number fewer than 10, else as `polyval`. -/
theorem polyvalS_ok (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al)
    (hD : Buf K W SP t D n) (hN : Buf K W SP t N 12)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyvalS v.callees wide) t (PolyPost K W SP N A D al n t) := by
  obtain ⟨t₁, run₁, hcf₁, hg₁, hm₁, hrd₁, hwr₁, _, _⟩ := smallCond_run E S hA.lt hD.lt
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  have hS₁ : Slots W R N A D al n t₁.mem := hm₁ ▸ S
  have P : ∀ t' : State, PolyPost K W SP N A D al n t₁ t' → PolyPost K W SP N A D al n t t' := fun t' P =>
    ⟨P.env, P.rd.trans hrd₁, P.wr.trans hwr₁, hm₁ ▸ P.frame, by rw [← hm₁]; exact P.out⟩
  refine WP.ite (decide (al / 16 + n / 16 < 10)) (eval_b hcf₁) (fun _ => ?_) (fun _ => ?_)
  · exact WP.mono (polyvalR_ok L E₁ hS₁ (hA.of_eq hrd₁ hwr₁) (hD.of_eq hrd₁ hwr₁) (hN.of_eq hrd₁ hwr₁)
      (by rw [hm₁]; exact hG) (by rw [hm₁]; exact hY)) P
  · exact WP.mono (polyval_ok v wide L E₁ hS₁ (hA.of_eq hrd₁ hwr₁) (hD.of_eq hrd₁ hwr₁) (hN.of_eq hrd₁ hwr₁)
      (by rw [hm₁]; exact hG) (by rw [hm₁]; exact hY)) P

end VG.Proof.AesGcmSiv.X86_64.Stitch
