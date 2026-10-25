module

import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Spec.Rsa

/-! # The selection under a mask, sixteen bytes at a time

`selectLoopX` does what `selectLoop` does (`selectLoop_ok`), with SSE2:
the mask in every doubleword of `xmm7` (`maskX_ok`), each 16-byte block of
the destination replaced by `d ^ ((x ^ d) & mask)` (`chunk_ok`), whose
doublewords are the scalar loop's words (`chunk_w32`), over `N / 4` blocks
counted in `eax` (`chunks_ok`); the last `N mod 4` words by `selectLoop`
(`selectLoopX_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop selectLoop_ok)

section
variable {s : State} {is : List Instr} {Q : State → Prop}

/-- `add d, src`, keeping the XMM registers. -/
theorem wp_addXm {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d + v) → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `sub d, src`: ZF, keeping the XMM registers. -/
theorem wp_subXm {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d - v) → t.zf = some (s.gpr d - v == 0) → t.xmm = s.xmm →
      WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl rfl)

/-- `and d, src`: ZF. -/
theorem wp_andZ {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d &&& v) → t.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .and d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-- The loop's body: one 16-byte block. -/
abbrev chunk : List Instr :=
  [.movdquLoad .xmm0 (at_ .ebx 0), .movdquLoad .xmm1 (at_ .ebp 0),
    .xop (.bin .pxor .xmm1 .xmm0), .xop (.bin .pand .xmm1 .xmm7), .xop (.bin .pxor .xmm0 .xmm1),
    .movdquStore (at_ .ebx 0) .xmm0, .alu .add .ebp (.imm 16), .alu .add .ebx (.imm 16),
    .alu .sub .eax (.imm 1)]

/-- The block written: the destination's bytes `d` where the mask `v` is clear, the source's `x` where it is set. -/
def sel128 (m : Mem) (W : Addr) (x d : Nat) (v : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pxor (m.readW (off W d) 128)
    (XBinOp.eval .pand (XBinOp.eval .pxor (m.readW (off W x) 128) (m.readW (off W d) 128)) v)

/-- One block. -/
theorem chunk_ok {t : State} {W : Addr} {L x d : Nat} (hw : Ws t W L) (hx : x + 16 ≤ L) (hd : d + 16 ≤ L)
    (pe : PtrAt t W .ebp x) (pb : PtrAt t W .ebx d) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, u.mem = t.mem.writeW (off W d) (sel128 t.mem W x d (t.xmm .xmm7)) →
      u.gpr .ebp = t.gpr .ebp + 16 → u.gpr .ebx = t.gpr .ebx + 16 →
      u.gpr .eax = t.gpr .eax - 1 → u.zf = some (t.gpr .eax - 1 == 0) →
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → u.gpr r = t.gpr r) → u.rd = t.rd → u.wr = t.wr →
      u.xmm .xmm7 = t.xmm .xmm7 → WP isa (.block is) u Q) :
    WP isa (.block (chunk ++ is)) t Q := by
  have eb : t.ea (at_ .ebx 0) = off W d := by simpa using ea_ptr hw pb (d := 0) (by omega_arith)
  have ep : t.ea (at_ .ebp 0) = off W x := by simpa using ea_ptr hw pe (d := 0) (by omega_arith)
  have rb : InRegions (t.rd ++ t.wr) (off W d) 16 := ws_read hw hd
  have rp : InRegions (t.rd ++ t.wr) (off W x) 16 := ws_read hw hx
  have wb : InRegions t.wr (off W d) 16 := ws_write hw hd
  let D := t.mem.readW (off W d) 128
  let X := t.mem.readW (off W x) 128
  let s₁ := t.setXmm .xmm0 D
  let s₂ := s₁.setXmm .xmm1 X
  let s₃ := s₂.setXmm .xmm1 (XBinOp.eval .pxor X D)
  let s₄ := s₃.setXmm .xmm1 (XBinOp.eval .pand (XBinOp.eval .pxor X D) (t.xmm .xmm7))
  let s₅ := s₄.setXmm .xmm0 (sel128 t.mem W x d (t.xmm .xmm7))
  let s₆ : State := { s₅ with mem := t.mem.writeW (off W d) (sel128 t.mem W x d (t.xmm .xmm7)) }
  have x7 : s₄.xmm .xmm7 = t.xmm .xmm7 := rfl
  simp only [List.cons_append]
  refine cons (s' := s₁) (by simp only [exec, eb, State.load128, rb, ite_true, Option.map_some]; rfl) ?_
  refine cons (s' := s₂) (by
    simp only [exec, show s₁.ea (at_ .ebp 0) = off W x from ep, State.load128,
      (show InRegions (s₁.rd ++ s₁.wr) (off W x) 16 from rp), ite_true, Option.map_some]; rfl) ?_
  refine cons (s' := s₃) rfl ?_
  refine cons (s' := s₄) rfl ?_
  refine cons (s' := s₅) rfl ?_
  refine cons (s' := s₆) (by
    simp only [exec, show s₅.ea (at_ .ebx 0) = off W d from eb, State.store128,
      (show InRegions s₅.wr (off W d) 16 from wb), ite_true]; rfl) ?_
  refine wp_addXm rfl fun u₁ a₁ x₁ => wp_addXm rfl fun u₂ a₂ x₂ => wp_subXm rfl fun u₃ a₃ z₃ x₃ => ?_
  refine k u₃ (by rw [a₃.mem, a₂.mem, a₁.mem]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [a₃.other _ (by decide), a₂.other _ (by decide), a₁.gpr]; rfl
  · rw [a₃.other _ (by decide), a₂.gpr, a₁.other _ (by decide)]; rfl
  · rw [a₃.gpr, a₂.other _ (by decide), a₁.other _ (by decide)]; rfl
  · rw [z₃, a₂.other _ (by decide), a₁.other _ (by decide)]; rfl
  · intro r h1 h2 h3; rw [a₃.other _ h1, a₂.other _ h2, a₁.other _ h3]; rfl
  · rw [a₃.rd, a₂.rd, a₁.rd]; rfl
  · rw [a₃.wr, a₂.wr, a₁.wr]; rfl
  · rw [x₃, x₂, x₁]; rfl

/-- The block's doublewords are the selected words. -/
theorem chunk_w32 {m : Mem} {W : Addr} {x d : Nat} {v : BitVec 128} {k : Bool}
    (hv : ∀ i < 4, dword v i = cmask k) {i : Nat} (hi : i < 4) :
    w32 (m.writeW (off W d) (sel128 m W x d v)) W (d + 4 * i) =
      if k then w32 m W (x + 4 * i) else w32 m W (d + 4 * i) := by
  have e : ∀ y, off W (y + 4 * i) = off W y + BitVec.ofNat 64 (4 * i) := fun y => by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  simp only [w32, e, readW_writeW128 _ _ _ hi, sel128, dword_pxor, Lanes.dword_pand, dword_readW _ _ hi, hv i hi]
  rw [select_val]
  cases k <;> rfl

/-- Numbers of the same words. -/
theorem val32_shift {m m' : Mem} {W : Addr} : ∀ {n d y : Nat},
    (∀ j < n, w32 m' W (d + 4 * j) = w32 m W (y + 4 * j)) → val32 m' W d n = val32 m W y n
  | 0, _, _, _ => rfl
  | n + 1, d, y, h => by
    simp only [val32]
    rw [show w32 m' W d = w32 m W y by simpa using h 0 (by omega_arith),
      val32_shift (n := n) (d := d + 4) (y := y + 4) fun j hj => by
        have := h (j + 1) (by omega_arith)
        rwa [show d + 4 * (j + 1) = d + 4 + 4 * j by omega_arith, show y + 4 * (j + 1) = y + 4 + 4 * j by omega_arith] at this]

/-- The block's number. -/
theorem chunk_val32 {m : Mem} {W : Addr} {x d : Nat} {v : BitVec 128} {k : Bool}
    (hv : ∀ i < 4, dword v i = cmask k) :
    val32 (m.writeW (off W d) (sel128 m W x d v)) W d 4 =
      if k then val32 m W x 4 else val32 m W d 4 := by
  cases k
  · exact val32_shift fun j hj => by rw [chunk_w32 hv hj]; rfl
  · exact val32_shift fun j hj => by rw [chunk_w32 hv hj]; rfl

/-- The count down by one: ZF when it reaches zero. -/
theorem count1 {x : BitVec 32} {M j : Nat} (hx : x.toNat = M - j) (hj : j < M) :
    (x - 1).toNat = M - (j + 1) ∧ (x - 1 == 0) = decide (j + 1 = M) := by
  have h1 : (x - 1).toNat = M - (j + 1) := by
    rw [BitVec.toNat_sub, hx, show (1 : BitVec 32).toNat = 1 from rfl]
    have := x.isLt
    omega_arith
  refine ⟨h1, ?_⟩
  by_cases e : j + 1 = M
  · simp only [e, decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [h1, e, Nat.sub_self]; rfl)
  · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro z
    have := congrArg BitVec.toNat z
    rw [h1] at this
    exact e (by simp at this; omega_arith)

/-- The `N / 4` blocks. -/
theorem chunks_ok {t₁ : State} {W : Addr} {L x d N : Nat} (hw : Ws t₁ W L) {k : Bool}
    (hN : 4 ≤ N) (hx : x + 4 * N ≤ L) (hd : d + 4 * N ≤ L) (hdx : d + 4 * N ≤ x ∨ x + 4 * N ≤ d)
    (pe : PtrAt t₁ W .ebp x) (pb : PtrAt t₁ W .ebx d) (ea : (t₁.gpr .eax).toNat = N / 4)
    (hv : ∀ i < 4, dword (t₁.xmm .xmm7) i = cmask k) :
    WP isa (.loop (.block chunk) .ne) t₁ fun u =>
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → u.gpr r = t₁.gpr r) ∧ u.rd = t₁.rd ∧ u.wr = t₁.wr ∧
      PtrAt u W .ebp (x + 16 * (N / 4)) ∧ PtrAt u W .ebx (d + 16 * (N / 4)) ∧
      Outside W d (16 * (N / 4)) t₁.mem u.mem ∧
      val32 u.mem W d (4 * (N / 4)) =
        if k then val32 t₁.mem W x (4 * (N / 4)) else val32 t₁.mem W d (4 * (N / 4)) := by
  have hn := hw.nowrap
  refine WP.mono (countLoop (N := N / 4) (by omega_arith) (fun j t =>
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → t.gpr r = t₁.gpr r) ∧ t.rd = t₁.rd ∧ t.wr = t₁.wr ∧
      PtrAt t W .ebp (x + 16 * j) ∧ PtrAt t W .ebx (d + 16 * j) ∧ (t.gpr .eax).toNat = N / 4 - j ∧
      t.xmm .xmm7 = t₁.xmm .xmm7 ∧ Outside W d (16 * j) t₁.mem t.mem ∧
      val32 t.mem W d (4 * j) = if k then val32 t₁.mem W x (4 * j) else val32 t₁.mem W d (4 * j)) ?_
    ⟨fun _ _ _ _ => rfl, rfl, rfl, by simpa using pe, by simpa using pb, by simpa using ea, rfl,
      Outside.refl _ _ _ _, by cases k <;> rfl⟩)
    fun u ⟨G, R, Wr, P, B, _, _, O, V⟩ => ⟨G, R, Wr, P, B, O, V⟩
  rintro j t hj ⟨G, R, Wr, pe', pb', ea', x7, O, V⟩
  have ht : Ws t W L := ⟨by rw [Wr]; exact hw.wr, hn⟩
  have hv' : ∀ i < 4, dword (t.xmm .xmm7) i = cmask k := fun i hi => by rw [x7]; exact hv i hi
  rw [← List.append_nil chunk]
  refine chunk_ok ht (x := x + 16 * j) (d := d + 16 * j) (by omega_arith) (by omega_arith) pe' pb'
    fun u mu ebp ebx eax zf G' rd wr x7' => WP.block_nil ?_
  obtain ⟨c1, c2⟩ := count1 ea' hj
  have Ow := writeW128_out t.mem W (sel128 t.mem W (x + 16 * j) (d + 16 * j) (t.xmm .xmm7))
    (d := d + 16 * j) (by omega_arith)
  refine ⟨⟨fun r h1 h2 h3 => (G' r h1 h2 h3).trans (G r h1 h2 h3), rd.trans R, wr.trans Wr, ?_, ?_,
    by rw [eax]; exact c1, x7'.trans x7, ?_, ?_⟩, by rw [zf, c2]⟩
  · rw [PtrAt, ebp, ptr_add pe', show (16 : BitVec 32).toNat = 16 from rfl,
      show x + 16 * j + 16 = x + 16 * (j + 1) by omega_arith]
  · rw [PtrAt, ebx, ptr_add pb', show (16 : BitVec 32).toNat = 16 from rfl,
      show d + 16 * j + 16 = d + 16 * (j + 1) by omega_arith]
  · rw [mu]
    exact (O.mono (Nat.le_refl _) (by omega_arith)).trans (Ow.mono (by omega_arith) (by omega_arith))
  · have Xs : val32 t.mem W (x + 16 * j) 4 = val32 t₁.mem W (x + 16 * j) 4 := O.val32 (by omega_arith) (by omega_arith)
    have Ds : val32 t.mem W (d + 16 * j) 4 = val32 t₁.mem W (d + 16 * j) 4 := O.val32 (.inr (by omega_arith)) (by omega_arith)
    have Lo : val32 (t.mem.writeW (off W (d + 16 * j)) (sel128 t.mem W (x + 16 * j) (d + 16 * j) (t.xmm .xmm7)))
        W d (4 * j) = val32 t.mem W d (4 * j) := Ow.val32 (.inl (by omega_arith)) (by omega_arith)
    have Hi := chunk_val32 (m := t.mem) (W := W) (x := x + 16 * j) (d := d + 16 * j) hv'
    rw [mu, show 4 * (j + 1) = 4 * j + 4 by omega_arith, val32_append, val32_append t₁.mem W x,
      val32_append t₁.mem W d, show d + 4 * (4 * j) = d + 16 * j by omega_arith,
      show x + 4 * (4 * j) = x + 16 * j by omega_arith, Lo, Hi, V, Xs, Ds]
    cases k <;> rfl

/-- `selectLoopX` does what `selectLoop` does, for at least four words. -/
theorem selectLoopX_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x d N : Nat} (k : Bool)
    (hN : 4 ≤ N) (hx : x + 4 * N ≤ L) (hd : d + 4 * N ≤ L) (hdx : d + 4 * N ≤ x ∨ x + 4 * N ≤ d)
    (hebp : PtrAt t₀ W .ebp x) (hebx : PtrAt t₀ W .ebx d)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask k) :
    WP isa selectLoopX t₀ fun u =>
      Outside W d (4 * N) t₀.mem u.mem ∧
        val32 u.mem W d N = (if k then val32 t₀.mem W x N else val32 t₀.mem W d N) ∧
        PtrAt u W .ebx (d + 4 * N) ∧ Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  unfold selectLoopX
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => PublicRt.wp_shr (by decide) fun s₂ u₂ => ?_)
  let s₃ := s₂.setXmm .xmm7 ((0 : BitVec 96) ++ s₂.gpr .ecx)
  let s₄ := s₃.setXmm .xmm7 (shufDwords (s₃.xmm .xmm7) 0)
  refine cons (s' := s₃) rfl (cons (s' := s₄) rfl (WP.block_nil ?_))
  have g₄ : ∀ r, r ≠ .eax → s₄.gpr r = t₀.gpr r := fun r h => by
    show s₂.gpr r = _
    rw [u₂.other _ h, u₁.other _ h]
  have ws₄ : Ws s₄ W L := ⟨by show _ ∈ s₂.wr; rw [u₂.wr, u₁.wr]; exact hw.wr, hn⟩
  have ea₄ : (s₄.gpr .eax).toNat = N / 4 := by
    show (s₂.gpr .eax).toNat = _
    rw [u₂.gpr, u₁.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hedi]
    omega_arith
  have hv : ∀ i < 4, dword (s₄.xmm .xmm7) i = cmask k := fun i hi => by
    show dword (shufDwords (s₃.xmm .xmm7) 0) i = _
    rw [show (0 : BitVec 8) = BitVec.ofNat 8 (0x55 * 0) from rfl, dword_shufDwords_bcast _ (by decide) hi]
    show dword ((0 : BitVec 96) ++ s₂.gpr .ecx) 0 = _
    rw [Sse2.dword_movd_0, u₂.other _ (by decide), u₁.other _ (by decide), hecx]
  refine WP.seq (WP.mono (chunks_ok ws₄ (k := k) hN hx hd hdx
    (by rw [PtrAt, g₄ _ (by decide)]; exact hebp) (by rw [PtrAt, g₄ _ (by decide)]; exact hebx) ea₄ hv)
    fun t ⟨G, R, Wr, pe, pb, O, V⟩ => ?_)
  have m₄ : s₄.mem = t₀.mem := by show s₂.mem = _; rw [u₂.mem, u₁.mem]
  rw [m₄] at O V
  have gt : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ebp → t.gpr r = t₀.gpr r := fun r h1 h2 h3 =>
    (G r h1 h2 h3).trans (g₄ r h1)
  have rdt : t.rd = t₀.rd := by rw [R]; show s₂.rd = _; rw [u₂.rd, u₁.rd]
  have wrt : t.wr = t₀.wr := by rw [Wr]; show s₂.wr = _; rw [u₂.wr, u₁.wr]
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

end VG.Proof.Bignum.X86.CrtRt
