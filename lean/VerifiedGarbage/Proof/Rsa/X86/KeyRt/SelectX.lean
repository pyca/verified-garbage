module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Select3
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.X86.Sse

/-! # The key workspace's selections, sixteen bytes at a time

`selectLoopX_ok` and `select3LoopX_ok`: `selectLoopX` and `select3LoopX` do
what `CrtRt.selectLoop` and `select3Loop` do, for any positive count. The
mask is broadcast to every doubleword of `xmm7`; the `N / 4` 16-byte blocks,
if any, are selected with SSE2 (`CrtRt.chunks_ok`, and `chunks3_ok` for a
third array as the destination), and the last `N mod 4` words, if any, by the
scalar loop.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop selectLoop_ok)
open VG.Proof.Bignum.X86.CrtRt (sel128 chunks_ok count1 val32_shift wp_addXm wp_subXm wp_andZ)

section
variable {s : State} {is : List Instr} {Q : State → Prop}

/-- `shr d, n`, and ZF. -/
theorem wp_shrZ {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ t, Upd s t d (s.gpr d >>> n) → t.zf = some (s.gpr d >>> n == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _) rfl)

end

/-- The prologue: `eax = 4 N / 16` with ZF, the mask `ecx` in every doubleword of `xmm7`. -/
theorem prologue_ok {t₀ : State} {r : Reg} {N : Nat} (k : Bool)
    (hr4 : (t₀.gpr r).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask k) {Q : State → Prop}
    (hQ : ∀ t, (∀ r, r ≠ .eax → t.gpr r = t₀.gpr r) → t.mem = t₀.mem → t.rd = t₀.rd → t.wr = t₀.wr →
      (t.gpr .eax).toNat = N / 4 → t.zf = some (decide (N / 4 = 0)) →
      (∀ i < 4, dword (t.xmm .xmm7) i = cmask k) → Q t) :
    WP isa (.block [.mov .eax (.reg r), .shift .shr .eax 4, .xop (.movd .xmm7 .ecx),
      .xop (.pshufd .xmm7 .xmm7 0)]) t₀ Q := by
  refine wp_movS rfl fun s₁ u₁ _ => wp_shrZ (by decide) fun s₂ u₂ z₂ => ?_
  let s₃ := s₂.setXmm .xmm7 ((0 : BitVec 96) ++ s₂.gpr .ecx)
  let s₄ := s₃.setXmm .xmm7 (shufDwords (s₃.xmm .xmm7) 0)
  refine cons (s' := s₃) rfl (cons (s' := s₄) rfl (WP.block_nil ?_))
  have ea : (s₂.gpr .eax).toNat = N / 4 := by
    rw [u₂.gpr, u₁.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hr4]
    omega_arith
  refine hQ s₄ (fun r' h => by show s₂.gpr r' = _; rw [u₂.other _ h, u₁.other _ h])
    (by show s₂.mem = _; rw [u₂.mem, u₁.mem]) (by show s₂.rd = _; rw [u₂.rd, u₁.rd])
    (by show s₂.wr = _; rw [u₂.wr, u₁.wr]) ea ?_ ?_
  · show s₂.zf = _
    rw [z₂]
    congr 1
    by_cases e : N / 4 = 0
    · simp only [e, decide_true, beq_iff_eq]
      exact BitVec.eq_of_toNat_eq (by rw [← u₂.gpr, ea, e]; rfl)
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro z
      have := congrArg BitVec.toNat z
      rw [← u₂.gpr, ea] at this
      exact e (by simpa using this)
  · intro i hi
    show dword (shufDwords (s₃.xmm .xmm7) 0) i = _
    rw [show (0 : BitVec 8) = BitVec.ofNat 8 (0x55 * 0) from rfl, dword_shufDwords_bcast _ (by decide) hi]
    show dword ((0 : BitVec 96) ++ s₂.gpr .ecx) 0 = _
    rw [Sse2.dword_movd_0, u₂.other _ (by decide), u₁.other _ (by decide), hecx]

/-! ## Two arrays -/

/-- The blocks, if any: what `chunks_ok` gives, or nothing for fewer than four words. -/
theorem guarded_ok {t₁ : State} {W : Addr} {L x d N : Nat} (hw : Ws t₁ W L) {k : Bool}
    (hx : x + 4 * N ≤ L) (hd : d + 4 * N ≤ L) (hdx : d + 4 * N ≤ x ∨ x + 4 * N ≤ d)
    (pe : PtrAt t₁ W .ebp x) (pb : PtrAt t₁ W .ebx d) (ea : (t₁.gpr .eax).toNat = N / 4)
    (zf : t₁.zf = some (decide (N / 4 = 0)))
    (hv : ∀ i < 4, dword (t₁.xmm .xmm7) i = cmask k) :
    WP isa (.ite .ne (.loop (.block VG.Proof.Bignum.X86.CrtRt.chunk) .ne) (.block [])) t₁ fun u =>
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → u.gpr r = t₁.gpr r) ∧ u.rd = t₁.rd ∧ u.wr = t₁.wr ∧
      PtrAt u W .ebp (x + 16 * (N / 4)) ∧ PtrAt u W .ebx (d + 16 * (N / 4)) ∧
      Outside W d (16 * (N / 4)) t₁.mem u.mem ∧
      val32 u.mem W d (4 * (N / 4)) =
        if k then val32 t₁.mem W x (4 * (N / 4)) else val32 t₁.mem W d (4 * (N / 4)) := by
  by_cases e : N / 4 = 0
  · refine WP.ite false (by change t₁.zf.map (!·) = _; rw [zf, e]; rfl) (fun h => nomatch h)
      fun _ => WP.block_nil ?_
    rw [e]
    exact ⟨fun _ _ _ _ => rfl, rfl, rfl, by simpa using pe, by simpa using pb, Outside.refl _ _ _ _,
      by cases k <;> rfl⟩
  · refine WP.ite true (by change t₁.zf.map (!·) = _; rw [zf, decide_eq_false e]; rfl)
      (fun _ => chunks_ok hw (by omega_arith) hx hd hdx pe pb ea hv) fun h => nomatch h

/-- `selectLoopX` does what `CrtRt.selectLoop` does, for any count. -/
theorem selectLoopX_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x d N : Nat} (k : Bool)
    (hx : x + 4 * N ≤ L) (hd : d + 4 * N ≤ L) (hdx : d + 4 * N ≤ x ∨ x + 4 * N ≤ d)
    (hebp : PtrAt t₀ W .ebp x) (hebx : PtrAt t₀ W .ebx d)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask k) :
    WP isa selectLoopX t₀ fun u =>
      Outside W d (4 * N) t₀.mem u.mem ∧
        val32 u.mem W d N = (if k then val32 t₀.mem W x N else val32 t₀.mem W d N) ∧
        PtrAt u W .ebx (d + 4 * N) ∧ Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  unfold selectLoopX
  refine WP.seq (prologue_ok k hedi hecx fun s₄ g₄ m₄ r₄ w₄ ea₄ z₄ hv => ?_)
  have ws₄ : Ws s₄ W L := ⟨by rw [w₄]; exact hw.wr, hn⟩
  refine WP.seq (WP.mono (guarded_ok ws₄ (k := k) hx hd hdx
    (by rw [PtrAt, g₄ _ (by decide)]; exact hebp) (by rw [PtrAt, g₄ _ (by decide)]; exact hebx) ea₄ z₄ hv)
    fun t ⟨G, R, Wr, pe, pb, O, V⟩ => ?_)
  rw [m₄] at O V
  have gt : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → t.gpr r = t₀.gpr r := fun r h1 h2 h3 =>
    (G r h1 h2 h3).trans (g₄ r h1)
  have rdt : t.rd = t₀.rd := by rw [R, r₄]
  have wrt : t.wr = t₀.wr := by rw [Wr, w₄]
  refine WP.seq (wp_andZ rfl fun t₂ a₂ z₂ => WP.block_nil ?_)
  have e15 : (t.gpr .edi &&& 15).toNat = 4 * (N % 4) := by
    rw [BitVec.toNat_and, gt _ (by decide) (by decide) (by decide), hedi,
      show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega_arith
  have g₂ : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → r ≠ .edi → t₂.gpr r = t₀.gpr r := fun r h1 h2 h3 h4 =>
    (a₂.other _ h4).trans (gt r h1 h2 h3)
  have K₂ : Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ t₂ := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g₂ r hr.1 hr.2.1 hr.2.2.2.1 hr.2.2.2.2, by rw [a₂.rd, rdt], by rw [a₂.wr, wrt]⟩
  have pb₂ : PtrAt t₂ W .ebx (d + 16 * (N / 4)) := by rw [PtrAt, a₂.other _ (by decide)]; exact pb
  by_cases r4 : N % 4 = 0
  · have z : (t.gpr .edi &&& 15 == 0) = true := by
      rw [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by rw [e15, r4]; rfl)
    refine WP.ite false (by change t₂.zf.map (!·) = _; rw [z₂, z]; rfl) (fun e => nomatch e)
      fun _ => WP.block_nil ?_
    have e : 4 * (N / 4) = N := by omega_arith
    refine ⟨by rw [a₂.mem]; exact O.mono (Nat.le_refl _) (by omega_arith), by rw [a₂.mem, ← e]; exact V,
      by rw [show d + 4 * N = d + 16 * (N / 4) by omega_arith]; exact pb₂, K₂⟩
  · have z : (t.gpr .edi &&& 15 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have := congrArg BitVec.toNat h
      rw [e15] at this
      exact r4 (by simp at this; omega_arith)
    refine WP.ite true (by change t₂.zf.map (!·) = _; rw [z₂, z]; rfl) (fun _ => ?_) fun e => nomatch e
    have ws₂ : Ws t₂ W L := ⟨by rw [a₂.wr, wrt]; exact hw.wr, hn⟩
    refine WP.mono (selectLoop_ok ws₂ (x := x + 16 * (N / 4)) (d := d + 16 * (N / 4)) (N := N % 4) k
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by rw [PtrAt, a₂.other _ (by decide)]; exact pe) pb₂ (by rw [a₂.gpr]; exact e15)
      (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hecx))
      fun u ⟨O', V', P', K'⟩ => ?_
    rw [a₂.mem] at O' V'
    have hN4 : N = 4 * (N / 4) + N % 4 := by omega_arith
    refine ⟨?_, ?_, ?_, K₂.trans K'⟩
    · exact (O.mono (Nat.le_refl _) (by omega_arith)).trans (O'.mono (by omega_arith) (by omega_arith))
    · have Lo : val32 u.mem W d (4 * (N / 4)) = val32 t.mem W d (4 * (N / 4)) :=
        O'.val32 (.inl (by omega_arith)) (by omega_arith)
      have Xs : val32 t.mem W (x + 16 * (N / 4)) (N % 4) = val32 t₀.mem W (x + 16 * (N / 4)) (N % 4) :=
        O.val32 (by omega_arith) (by omega_arith)
      have Ds : val32 t.mem W (d + 16 * (N / 4)) (N % 4) = val32 t₀.mem W (d + 16 * (N / 4)) (N % 4) :=
        O.val32 (.inr (by omega_arith)) (by omega_arith)
      rw [hN4, val32_append, val32_append t₀.mem W x, val32_append t₀.mem W d,
        show d + 4 * (4 * (N / 4)) = d + 16 * (N / 4) by omega_arith,
        show x + 4 * (4 * (N / 4)) = x + 16 * (N / 4) by omega_arith, Lo, V, V', Xs, Ds]
      cases k <;> rfl
    · rw [show d + 4 * N = d + 16 * (N / 4) + 4 * (N % 4) by omega_arith]; exact P'

/-! ## Three arrays -/

/-- The loop's body with a third array as the destination: one 16-byte block. -/
abbrev chunk3 : List Instr :=
  [.movdquLoad .xmm0 (at_ .ebp 0), .movdquLoad .xmm1 (at_ .ebx 0),
    .xop (.bin .pxor .xmm1 .xmm0), .xop (.bin .pand .xmm1 .xmm7), .xop (.bin .pxor .xmm0 .xmm1),
    .movdquStore (at_ .edi 0) .xmm0, .alu .add .ebp (.imm 16), .alu .add .ebx (.imm 16),
    .alu .add .edi (.imm 16), .alu .sub .eax (.imm 1)]

/-- One block: `[edi]` the block at `ebx` where the mask is set, at `ebp` where it is clear. -/
theorem chunk3_ok {t : State} {W : Addr} {L x y d : Nat} (hw : Ws t W L) (hx : x + 16 ≤ L) (hy : y + 16 ≤ L)
    (hd : d + 16 ≤ L) (pe : PtrAt t W .ebp x) (pb : PtrAt t W .ebx y) (pi : PtrAt t W .edi d)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, u.mem = t.mem.writeW (off W d) (sel128 t.mem W y x (t.xmm .xmm7)) →
      u.gpr .ebp = t.gpr .ebp + 16 → u.gpr .ebx = t.gpr .ebx + 16 → u.gpr .edi = t.gpr .edi + 16 →
      u.gpr .eax = t.gpr .eax - 1 → u.zf = some (t.gpr .eax - 1 == 0) →
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → r ≠ .edi → u.gpr r = t.gpr r) → u.rd = t.rd → u.wr = t.wr →
      u.xmm .xmm7 = t.xmm .xmm7 → WP isa (.block is) u Q) :
    WP isa (.block (chunk3 ++ is)) t Q := by
  have eb : t.ea (at_ .ebx 0) = off W y := by simpa using ea_ptr hw pb (d := 0) (by omega_arith)
  have ep : t.ea (at_ .ebp 0) = off W x := by simpa using ea_ptr hw pe (d := 0) (by omega_arith)
  have ei : t.ea (at_ .edi 0) = off W d := by simpa using ea_ptr hw pi (d := 0) (by omega_arith)
  have rb : InRegions (t.rd ++ t.wr) (off W y) 16 := ws_read hw hy
  have rp : InRegions (t.rd ++ t.wr) (off W x) 16 := ws_read hw hx
  have wi : InRegions t.wr (off W d) 16 := ws_write hw hd
  let X := t.mem.readW (off W x) 128
  let Y := t.mem.readW (off W y) 128
  let s₁ := t.setXmm .xmm0 X
  let s₂ := s₁.setXmm .xmm1 Y
  let s₃ := s₂.setXmm .xmm1 (XBinOp.eval .pxor Y X)
  let s₄ := s₃.setXmm .xmm1 (XBinOp.eval .pand (XBinOp.eval .pxor Y X) (t.xmm .xmm7))
  let s₅ := s₄.setXmm .xmm0 (sel128 t.mem W y x (t.xmm .xmm7))
  let s₆ : State := { s₅ with mem := t.mem.writeW (off W d) (sel128 t.mem W y x (t.xmm .xmm7)) }
  simp only [List.cons_append]
  refine cons (s' := s₁) (by simp only [exec, ep, State.load128, rp, ite_true, Option.map_some]; rfl) ?_
  refine cons (s' := s₂) (by
    simp only [exec, show s₁.ea (at_ .ebx 0) = off W y from eb, State.load128,
      (show InRegions (s₁.rd ++ s₁.wr) (off W y) 16 from rb), ite_true, Option.map_some]; rfl) ?_
  refine cons (s' := s₃) rfl ?_
  refine cons (s' := s₄) rfl ?_
  refine cons (s' := s₅) rfl ?_
  refine cons (s' := s₆) (by
    simp only [exec, show s₅.ea (at_ .edi 0) = off W d from ei, State.store128,
      (show InRegions s₅.wr (off W d) 16 from wi), ite_true]; rfl) ?_
  refine wp_addXm rfl fun u₁ a₁ x₁ => wp_addXm rfl fun u₂ a₂ x₂ => wp_addXm rfl fun u₃ a₃ x₃ =>
    wp_subXm rfl fun u₄ a₄ z₄ x₄ => ?_
  refine k u₄ (by rw [a₄.mem, a₃.mem, a₂.mem, a₁.mem]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [a₄.other _ (by decide), a₃.other _ (by decide), a₂.other _ (by decide), a₁.gpr]; rfl
  · rw [a₄.other _ (by decide), a₃.other _ (by decide), a₂.gpr, a₁.other _ (by decide)]; rfl
  · rw [a₄.other _ (by decide), a₃.gpr, a₂.other _ (by decide), a₁.other _ (by decide)]; rfl
  · rw [a₄.gpr, a₃.other _ (by decide), a₂.other _ (by decide), a₁.other _ (by decide)]; rfl
  · rw [z₄, a₃.other _ (by decide), a₂.other _ (by decide), a₁.other _ (by decide)]; rfl
  · intro r h1 h2 h3 h4; rw [a₄.other _ h1, a₃.other _ h4, a₂.other _ h2, a₁.other _ h3]; rfl
  · rw [a₄.rd, a₃.rd, a₂.rd, a₁.rd]; rfl
  · rw [a₄.wr, a₃.wr, a₂.wr, a₁.wr]; rfl
  · rw [x₄, x₃, x₂, x₁]; rfl

/-- The block's doublewords are the selected words. -/
theorem chunk3_w32 {m : Mem} {W : Addr} {x y d : Nat} {v : BitVec 128} {k : Bool}
    (hv : ∀ i < 4, dword v i = cmask k) {i : Nat} (hi : i < 4) :
    w32 (m.writeW (off W d) (sel128 m W y x v)) W (d + 4 * i) =
      if k then w32 m W (y + 4 * i) else w32 m W (x + 4 * i) := by
  have e : ∀ z, off W (z + 4 * i) = off W z + BitVec.ofNat 64 (4 * i) := fun z => by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  simp only [w32, e, readW_writeW128 _ _ _ hi, sel128, dword_pxor, Lanes.dword_pand, dword_readW _ _ hi, hv i hi]
  rw [select_val]
  cases k <;> rfl

/-- The block's number. -/
theorem chunk3_val32 {m : Mem} {W : Addr} {x y d : Nat} {v : BitVec 128} {k : Bool}
    (hv : ∀ i < 4, dword v i = cmask k) :
    val32 (m.writeW (off W d) (sel128 m W y x v)) W d 4 =
      if k then val32 m W y 4 else val32 m W x 4 := by
  cases k
  · exact val32_shift fun j hj => by rw [chunk3_w32 hv hj]; rfl
  · exact val32_shift fun j hj => by rw [chunk3_w32 hv hj]; rfl

/-- The `N / 4` blocks. -/
theorem chunks3_ok {t₁ : State} {W : Addr} {L x y d N : Nat} (hw : Ws t₁ W L) {k : Bool}
    (hN : 4 ≤ N) (hx : x + 4 * N ≤ L) (hy : y + 4 * N ≤ L) (hd : d + 4 * N ≤ L)
    (hdx : d + 4 * N ≤ x ∨ x + 4 * N ≤ d) (hdy : d + 4 * N ≤ y ∨ y + 4 * N ≤ d)
    (pe : PtrAt t₁ W .ebp x) (pb : PtrAt t₁ W .ebx y) (pi : PtrAt t₁ W .edi d)
    (ea : (t₁.gpr .eax).toNat = N / 4) (hv : ∀ i < 4, dword (t₁.xmm .xmm7) i = cmask k) :
    WP isa (.loop (.block chunk3) .ne) t₁ fun u =>
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → r ≠ .edi → u.gpr r = t₁.gpr r) ∧ u.rd = t₁.rd ∧ u.wr = t₁.wr ∧
      PtrAt u W .ebp (x + 16 * (N / 4)) ∧ PtrAt u W .ebx (y + 16 * (N / 4)) ∧
      PtrAt u W .edi (d + 16 * (N / 4)) ∧ Outside W d (16 * (N / 4)) t₁.mem u.mem ∧
      val32 u.mem W d (4 * (N / 4)) =
        if k then val32 t₁.mem W y (4 * (N / 4)) else val32 t₁.mem W x (4 * (N / 4)) := by
  have hn := hw.nowrap
  refine WP.mono (countLoop (N := N / 4) (by omega_arith) (fun j t =>
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → r ≠ .edi → t.gpr r = t₁.gpr r) ∧ t.rd = t₁.rd ∧
      t.wr = t₁.wr ∧ PtrAt t W .ebp (x + 16 * j) ∧ PtrAt t W .ebx (y + 16 * j) ∧
      PtrAt t W .edi (d + 16 * j) ∧ (t.gpr .eax).toNat = N / 4 - j ∧
      t.xmm .xmm7 = t₁.xmm .xmm7 ∧ Outside W d (16 * j) t₁.mem t.mem ∧
      val32 t.mem W d (4 * j) = if k then val32 t₁.mem W y (4 * j) else val32 t₁.mem W x (4 * j)) ?_
    ⟨fun _ _ _ _ _ => rfl, rfl, rfl, by simpa using pe, by simpa using pb, by simpa using pi,
      by simpa using ea, rfl, Outside.refl _ _ _ _, by cases k <;> rfl⟩)
    fun u ⟨G, R, Wr, P, B, I, _, _, O, V⟩ => ⟨G, R, Wr, P, B, I, O, V⟩
  rintro j t hj ⟨G, R, Wr, pe', pb', pi', ea', x7, O, V⟩
  have ht : Ws t W L := ⟨by rw [Wr]; exact hw.wr, hn⟩
  have hv' : ∀ i < 4, dword (t.xmm .xmm7) i = cmask k := fun i hi => by rw [x7]; exact hv i hi
  rw [← List.append_nil chunk3]
  refine chunk3_ok ht (x := x + 16 * j) (y := y + 16 * j) (d := d + 16 * j) (by omega_arith) (by omega_arith)
    (by omega_arith) pe' pb' pi' fun u mu ebp ebx edi eax zf G' rd wr x7' => WP.block_nil ?_
  obtain ⟨c1, c2⟩ := count1 ea' hj
  have Ow := writeW128_out t.mem W (sel128 t.mem W (y + 16 * j) (x + 16 * j) (t.xmm .xmm7))
    (d := d + 16 * j) (by omega_arith)
  refine ⟨⟨fun r h1 h2 h3 h4 => (G' r h1 h2 h3 h4).trans (G r h1 h2 h3 h4), rd.trans R, wr.trans Wr,
    ?_, ?_, ?_, by rw [eax]; exact c1, x7'.trans x7, ?_, ?_⟩, by rw [zf, c2]⟩
  · rw [PtrAt, ebp, ptr_add pe', show (16 : BitVec 32).toNat = 16 from rfl,
      show x + 16 * j + 16 = x + 16 * (j + 1) by omega_arith]
  · rw [PtrAt, ebx, ptr_add pb', show (16 : BitVec 32).toNat = 16 from rfl,
      show y + 16 * j + 16 = y + 16 * (j + 1) by omega_arith]
  · rw [PtrAt, edi, ptr_add pi', show (16 : BitVec 32).toNat = 16 from rfl,
      show d + 16 * j + 16 = d + 16 * (j + 1) by omega_arith]
  · rw [mu]
    exact (O.mono (Nat.le_refl _) (by omega_arith)).trans (Ow.mono (by omega_arith) (by omega_arith))
  · have Xs : val32 t.mem W (x + 16 * j) 4 = val32 t₁.mem W (x + 16 * j) 4 := O.val32 (by omega_arith) (by omega_arith)
    have Ys : val32 t.mem W (y + 16 * j) 4 = val32 t₁.mem W (y + 16 * j) 4 := O.val32 (by omega_arith) (by omega_arith)
    have Lo : val32 (t.mem.writeW (off W (d + 16 * j)) (sel128 t.mem W (y + 16 * j) (x + 16 * j) (t.xmm .xmm7)))
        W d (4 * j) = val32 t.mem W d (4 * j) := Ow.val32 (.inl (by omega_arith)) (by omega_arith)
    have Hi := chunk3_val32 (m := t.mem) (W := W) (x := x + 16 * j) (y := y + 16 * j) (d := d + 16 * j) hv'
    rw [mu, show 4 * (j + 1) = 4 * j + 4 by omega_arith, val32_append, val32_append t₁.mem W x,
      val32_append t₁.mem W y, show d + 4 * (4 * j) = d + 16 * j by omega_arith,
      show x + 4 * (4 * j) = x + 16 * j by omega_arith, show y + 4 * (4 * j) = y + 16 * j by omega_arith, Lo, Hi, V, Xs, Ys]
    cases k <;> rfl

/-- `select3LoopX` does what `select3Loop` does, for any positive count. -/
theorem select3LoopX_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x y d N : Nat} (k : Bool)
    (hN : 0 < N) (hx : x + 4 * N ≤ L) (hy : y + 4 * N ≤ L) (hd : d + 4 * N ≤ L)
    (hdx : d + 4 * N ≤ x ∨ x + 4 * N ≤ d) (hdy : d + 4 * N ≤ y ∨ y + 4 * N ≤ d)
    (hebp : PtrAt t₀ W .ebp x) (hebx : PtrAt t₀ W .ebx y) (hedi : PtrAt t₀ W .edi d)
    (hedx : (t₀.gpr .edx).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask k) :
    WP isa select3LoopX t₀ fun u => Outside W d (4 * N) t₀.mem u.mem ∧
      val32 u.mem W d N = (if k then val32 t₀.mem W y N else val32 t₀.mem W x N) ∧
      Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  unfold select3LoopX
  refine WP.seq (prologue_ok k hedx hecx fun s₄ g₄ m₄ r₄ w₄ ea₄ z₄ hv => ?_)
  have ws₄ : Ws s₄ W L := ⟨by rw [w₄]; exact hw.wr, hn⟩
  -- The blocks, if any.
  have mid : WP isa (.ite .ne (.loop (.block chunk3) .ne) (.block [])) s₄ fun u =>
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → r ≠ .edi → u.gpr r = s₄.gpr r) ∧ u.rd = s₄.rd ∧
      u.wr = s₄.wr ∧ PtrAt u W .ebp (x + 16 * (N / 4)) ∧ PtrAt u W .ebx (y + 16 * (N / 4)) ∧
      PtrAt u W .edi (d + 16 * (N / 4)) ∧ Outside W d (16 * (N / 4)) s₄.mem u.mem ∧
      val32 u.mem W d (4 * (N / 4)) =
        if k then val32 s₄.mem W y (4 * (N / 4)) else val32 s₄.mem W x (4 * (N / 4)) := by
    have pe : PtrAt s₄ W .ebp x := by rw [PtrAt, g₄ _ (by decide)]; exact hebp
    have pb : PtrAt s₄ W .ebx y := by rw [PtrAt, g₄ _ (by decide)]; exact hebx
    have pi : PtrAt s₄ W .edi d := by rw [PtrAt, g₄ _ (by decide)]; exact hedi
    by_cases e : N / 4 = 0
    · refine WP.ite false (by change s₄.zf.map (!·) = _; rw [z₄, e]; rfl) (fun h => nomatch h)
        fun _ => WP.block_nil ?_
      rw [e]
      exact ⟨fun _ _ _ _ _ => rfl, rfl, rfl, by simpa using pe, by simpa using pb, by simpa using pi,
        Outside.refl _ _ _ _, by cases k <;> rfl⟩
    · refine WP.ite true (by change s₄.zf.map (!·) = _; rw [z₄, decide_eq_false e]; rfl)
        (fun _ => chunks3_ok ws₄ (by omega_arith) hx hy hd hdx hdy pe pb pi ea₄ hv) fun h => nomatch h
  refine WP.seq (WP.mono mid fun t ⟨G, R, Wr, pe, pb, pi, O, V⟩ => ?_)
  rw [m₄] at O V
  have gt : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → r ≠ .edi → t.gpr r = t₀.gpr r := fun r h1 h2 h3 h4 =>
    (G r h1 h2 h3 h4).trans (g₄ r h1)
  have rdt : t.rd = t₀.rd := by rw [R, r₄]
  have wrt : t.wr = t₀.wr := by rw [Wr, w₄]
  refine WP.seq (wp_andZ rfl fun t₂ a₂ z₂ => WP.block_nil ?_)
  have e15 : (t.gpr .edx &&& 15).toNat = 4 * (N % 4) := by
    rw [BitVec.toNat_and, gt _ (by decide) (by decide) (by decide) (by decide), hedx,
      show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega_arith
  have g₂ : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → r ≠ .edi → r ≠ .edx → t₂.gpr r = t₀.gpr r :=
    fun r h1 h2 h3 h4 h5 => (a₂.other _ h5).trans (gt r h1 h2 h3 h4)
  have K₂ : Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ t₂ := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g₂ r hr.1 hr.2.1 hr.2.2.2.1 hr.2.2.2.2 hr.2.2.1, by rw [a₂.rd, rdt], by rw [a₂.wr, wrt]⟩
  by_cases r4 : N % 4 = 0
  · have z : (t.gpr .edx &&& 15 == 0) = true := by
      rw [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by rw [e15, r4]; rfl)
    refine WP.ite false (by change t₂.zf.map (!·) = _; rw [z₂, z]; rfl) (fun e => nomatch e)
      fun _ => WP.block_nil ?_
    have e : 4 * (N / 4) = N := by omega_arith
    exact ⟨by rw [a₂.mem]; exact O.mono (Nat.le_refl _) (by omega_arith), by rw [a₂.mem, ← e]; exact V, K₂⟩
  · have z : (t.gpr .edx &&& 15 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have := congrArg BitVec.toNat h
      rw [e15] at this
      exact r4 (by simp at this; omega_arith)
    refine WP.ite true (by change t₂.zf.map (!·) = _; rw [z₂, z]; rfl) (fun _ => ?_) fun e => nomatch e
    have ws₂ : Ws t₂ W L := ⟨by rw [a₂.wr, wrt]; exact hw.wr, hn⟩
    refine WP.mono (select3Loop_ok ws₂ (x := x + 16 * (N / 4)) (y := y + 16 * (N / 4))
      (d := d + 16 * (N / 4)) (N := N % 4) k (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by rw [PtrAt, a₂.other _ (by decide)]; exact pe) (by rw [PtrAt, a₂.other _ (by decide)]; exact pb)
      (by rw [PtrAt, a₂.other _ (by decide)]; exact pi) (by rw [a₂.gpr]; exact e15)
      (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hecx))
      fun u ⟨O', V', K'⟩ => ?_
    rw [a₂.mem] at O' V'
    have hN4 : N = 4 * (N / 4) + N % 4 := by omega_arith
    refine ⟨?_, ?_, K₂.trans K'⟩
    · exact (O.mono (Nat.le_refl _) (by omega_arith)).trans (O'.mono (by omega_arith) (by omega_arith))
    · have Lo : val32 u.mem W d (4 * (N / 4)) = val32 t.mem W d (4 * (N / 4)) :=
        O'.val32 (.inl (by omega_arith)) (by omega_arith)
      have Xs : val32 t.mem W (x + 16 * (N / 4)) (N % 4) = val32 t₀.mem W (x + 16 * (N / 4)) (N % 4) :=
        O.val32 (by omega_arith) (by omega_arith)
      have Ys : val32 t.mem W (y + 16 * (N / 4)) (N % 4) = val32 t₀.mem W (y + 16 * (N / 4)) (N % 4) :=
        O.val32 (by omega_arith) (by omega_arith)
      rw [hN4, val32_append, val32_append t₀.mem W x, val32_append t₀.mem W y,
        show d + 4 * (4 * (N / 4)) = d + 16 * (N / 4) by omega_arith,
        show x + 4 * (4 * (N / 4)) = x + 16 * (N / 4) by omega_arith,
        show y + 4 * (4 * (N / 4)) = y + 16 * (N / 4) by omega_arith, Lo, V, V', Xs, Ys]
      cases k <;> rfl

end VG.Proof.Rsa.X86.KeyRt
