module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWWin
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Sub
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Sub
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

-- separate module: the digit step's multiply-subtract and copy-back, proven apart from the step so a change rebuilds only them

/-! # The square root by words on i686: a digit step's multiply-subtract and copy-back

`mulSubX`: `D`'s word `m` set to `q̂`, then `T = R - q̂ D` over the window's `L + 1` words, from
`R2Words.subBody` a word at a time from word 0 and `WordModRt.subTop` for the top word
(`mulSubX_ok`). `copyBackX`: `T`'s `L + 1` words back over the remainder's window
(`copyBackX_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)
open VG.Proof.Rsa.X86.WordRt (wq MLen)
open VG.Impl.Rsa.X86.RecoverRt (wid)
open VG.Impl.Rsa.X86.RecoverDetRt (sCt sqZ sqD sqT nl toE updX fixX mulSubX copyBackX hCnt)

variable {B : Addr} {Z len : Nat}

/-! ## `copyBackX` -/

/-- After words `0, …, j - 1` of `copyBackX`'s loop from `s`: `K` words from `to` (`ebp`) to
`xo` (`esi`). -/
structure CopyXI (s : State) (B : Addr) (to xo K j : Nat) (u : State) : Prop where
  bp : PtrAt u B .ebp (to + 4 * j)
  si : PtrAt u B .esi (xo + 4 * j)
  dx : u.gpr .edx = BitVec.ofNat 32 (4 * (K - j))
  keep : Keeps [.eax, .edx, .esi, .ebp] s u
  out : Outside B xo (4 * j) s.mem u.mem
  val : val32 u.mem B xo j = val32 s.mem B to j

theorem copyXStep_ok {s u : State} {bytes to xo K j : Nat} (ws : Ws s B bytes) (nw : B.toNat + bytes ≤ 2 ^ 32)
    (ht : to + 4 * K ≤ bytes) (hx : xo + 4 * K ≤ bytes) (sep : to + 4 * K ≤ xo ∨ xo + 4 * K ≤ to)
    (hj : j < K) (I : CopyXI s B to xo K j u) :
    WP isa (.block [.mov .eax (.mem (at_ .ebp 0)), .store (at_ .esi 0) .eax, .alu .add .ebp (.imm 4),
      .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) u fun u' =>
      u'.zf = some (decide (j + 1 = K)) ∧ CopyXI s B to xo K (j + 1) u' := by
  have wsu : Ws u B bytes := ws.of_wr I.keep.2.2
  refine wp_movS (readSrc_ptr wsu I.bp (d := 0) (by omega)) fun u₁ U₁ _ => ?_
  have ws₁ := wsu.of_wr U₁.wr
  have ps₁ : PtrAt u₁ B .esi (xo + 4 * j) := by rw [PtrAt, U₁.other _ (by decide)]; exact I.si
  refine wp_storeS (ea_ptr ws₁ ps₁ (d := 0) (by omega)) (ws_write ws₁ (by omega)) fun u₂ M₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_subZ rfl fun u₅ U₅ z₅ => WP.block_nil ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := K) (x := u.gpr .edx)
    (by rw [I.dx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  have dx₄ : u₄.gpr .edx = u.gpr .edx := by
    rw [U₄.other _ (by decide), U₃.other _ (by decide), M₂.gpr, U₁.other _ (by decide)]
  have m₅ : u₅.mem = u.mem.writeW (off B (xo + 4 * j)) (u.mem.readW (off B (to + 4 * j)) 32) := by
    rw [U₅.mem, U₄.mem, U₃.mem, M₂.mem, U₁.mem, U₁.gpr, Nat.add_zero, Nat.add_zero]
  have O := writeW32_outside u.mem B (d := xo + 4 * j) (u.mem.readW (off B (to + 4 * j)) 32) (by omega)
  rw [← m₅] at O
  refine ⟨by rw [z₅, dx₄, hc.2], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [PtrAt, U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, ptr_add (s := u₂) (x := to + 4 * j)
      (by rw [PtrAt, M₂.gpr, U₁.other _ (by decide)]; exact I.bp)]
    congr 2
  · rw [PtrAt, U₅.other _ (by decide), U₄.gpr, U₃.other _ (by decide), ptr_add (s := u₂) (x := xo + 4 * j)
      (by rw [PtrAt, M₂.gpr]; exact ps₁)]
    congr 2
  · apply BitVec.eq_of_toNat_eq
    rw [U₅.gpr, dx₄, hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact I.keep.trans (((U₁.keeps.mono (by decide)).trans (M₂.keeps _)).trans
      (((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))))
  · exact (I.out.mono (by omega) (by omega)).trans (O.mono (by omega) (by omega))
  · rw [val32_succ, val32_succ, O.val32 (.inl (by omega)) (by omega), I.val, m₅, w32_write_self]
    congr 2
    exact I.out.w32 (by omega) (by omega)

theorem copyXLoop_ok {s u : State} {bytes to xo K : Nat} (ws : Ws s B bytes) (nw : B.toNat + bytes ≤ 2 ^ 32)
    (ht : to + 4 * K ≤ bytes) (hx : xo + 4 * K ≤ bytes) (sep : to + 4 * K ≤ xo ∨ xo + 4 * K ≤ to)
    (hK : 0 < K) (I : CopyXI s B to xo K 0 u) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .store (at_ .esi 0) .eax, .alu .add .ebp (.imm 4),
      .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne) u fun v => CopyXI s B to xo K K v := by
  refine WP.loop (M := isa) (Q := fun v => CopyXI s B to xo K K v)
    (fun n v => ∃ j, n = K - j ∧ j < K ∧ CopyXI s B to xo K j v) ?_ _ u ⟨0, rfl, hK, I⟩
  rintro n v ⟨j, rfl, hj, J⟩
  refine WP.mono (copyXStep_ok ws nw ht hx sep hj J) fun v' ⟨z, J'⟩ => ?_
  by_cases e : j + 1 = K
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ J'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], K - (j + 1),
      by omega, j + 1, rfl, by omega, J'⟩

/-- The arrays the digit step uses, at the wide width. -/
theorem sq_arrs (w : Nat) : arr w sqZ = 160 + 20 * (4 * (w + 2)) ∧ arr w sqD = 160 + 7 * (4 * (w + 2)) ∧
    arr w sqT = 160 + 14 * (4 * (w + 2)) := ⟨rfl, rfl, rfl⟩

theorem copyBackX_ok {s : State} (h : RtWs wid s B Z len 22) {a j : Nat} (hm : MLen s B Z nl a)
    (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len) :
    WP isa copyBackX s fun t => RtWs wid t B Z len 22 ∧
      Outside B (arr (kw len) sqZ + 8 * (j - 1)) (4 * (wq a - (j - 1) + 3)) s.mem t.mem ∧
      val32 t.mem B (arr (kw len) sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) =
        val32 s.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) ∧
      Keeps [.eax, .ebx, .edx, .esi, .ebp] s t := by
  have nw := h.ws.workspace.nowrap
  have f21 := h.ws.arr_fit (j := 21) (by decide)
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  obtain ⟨ez, -, et⟩ := sq_arrs (kw len)
  simp only [S, arr, VG.Impl.Rsa.X86.Keys.hdr] at f21
  unfold copyBackX
  simp only [VG.Impl.Rsa.X86.Keys.seqs, List.append_assoc]
  refine WP.seq (winPtrs_ok h hm hC hj1 (by omega) fun u K mu ps _ pd _ => ?_)
  have h₁ := h.keep K (by decide) (by decide) (by rw [mu]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₁) h₁.lenLe h₁.edi (r := .ebp) (t := .eax) (j := sqT) (by decide) (by decide)
    (by rw [et]; omega) fun u₂ U₂ m₂ p₂ _ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => WP.block_nil ?_
  have K₃ : Keeps [.eax, .ebx, .edx, .esi, .ebp] s u₃ :=
    (K.mono (by decide)).trans ((U₂.mono (by decide)).trans (U₃.keeps.mono (by decide)))
  have m₃ : u₃.mem = s.mem := by rw [U₃.mem, m₂, mu]
  have I₀ : CopyXI u₃ B (arr (kw len) sqT) (arr (kw len) sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) 0 u₃ := by
    refine ⟨?_, ?_, ?_, Keeps.refl _ _, Outside.refl _ _ _ _, by simp [val32]⟩
    · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₃.other _ (by decide)]; exact p₂
    · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₃.other _ (by decide), U₂.1 _ (by decide)]; exact ps
    · apply BitVec.eq_of_toNat_eq
      have e4 : (4 : BitVec 32).toNat = 4 := rfl
      rw [U₃.gpr, BitVec.toNat_add, U₂.1 _ (by decide), pd, e4, BitVec.toNat_ofNat, Nat.sub_zero]
      have := hm.le
      simp only [wq] at hj hW ⊢
      omega
  refine WP.mono (copyXLoop_ok (h.rt.of_keeps K₃) nw (to := arr (kw len) sqT)
    (xo := arr (kw len) sqZ + 8 * (j - 1)) (K := wq a - (j - 1) + 3) (by simp only [et]; omega) (by simp only [ez]; omega) (by simp only [et, ez]; omega)
    (by omega) I₀) fun v I => ?_
  have O : Outside B (arr (kw len) sqZ + 8 * (j - 1)) (4 * (wq a - (j - 1) + 3)) s.mem v.mem := by
    have := I.out; rwa [m₃] at this
  refine ⟨h.keep (K₃.trans (I.keep.mono (by decide))) (by decide) (by decide)
      (O.mono (Nat.zero_le _) (by rw [ez]; omega)), O, ?_, K₃.trans (I.keep.mono (by decide))⟩
  have := I.val; rwa [m₃] at this

/-! ## `mulSubX` -/

/-- After words `0, …, j - 1` of `mulSubX`'s loop from `s`, for `q̂ = q` in `ecx`: the words
`T_j` of `t` (at `to`) and the carry in `t[j]`: `T_j + q D_j = R_j + 2^(32 j) t[j]`, for `D` at
`mo` and `R` at `xo`. -/
structure SubJ (s : State) (B : Addr) (mo xo to K q j : Nat) (v : State) : Prop where
  bx : PtrAt v B .ebx (mo + 4 * j)
  si : PtrAt v B .esi (xo + 4 * j)
  bp : PtrAt v B .ebp (to + 4 * j)
  di : v.gpr .edi = BitVec.ofNat 32 (4 * (K - j))
  cx : v.gpr .ecx = BitVec.ofNat 32 q
  qlt : q < 2 ^ 32
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s v
  out : Outside B to (4 * (j + 1)) s.mem v.mem
  val : val32 v.mem B to j + q * val32 s.mem B mo j = val32 s.mem B xo j + 2 ^ (32 * j) * w32 v.mem B (to + 4 * j)

theorem sub0_val {T q M Y G c t' d x c' : Nat} (hI : T + q * M = Y + G * c) (hv : t' + q * d + c = x + 2 ^ 32 * c') :
    T + G * t' + q * (M + G * d) = Y + G * x + G * 2 ^ 32 * c' := by
  have e := congrArg (G * ·) hv
  simp only [Nat.mul_add] at e
  grind

theorem subJStep_ok {s v : State} {bytes mo xo to K q j : Nat} (ws : Ws s B bytes) (nw : B.toNat + bytes ≤ 2 ^ 32)
    (gm : mo + 4 * K ≤ bytes) (gx : xo + 4 * (K + 1) ≤ bytes) (gt : to + 4 * (K + 1) ≤ bytes)
    (gmt : mo + 4 * K ≤ to ∨ to + 4 * (K + 1) ≤ mo) (gxt : xo + 4 * (K + 1) ≤ to ∨ to + 4 * (K + 1) ≤ xo)
    (hj : j < K) (I : SubJ s B mo xo to K q j v) :
    WP isa (.block VG.Impl.Bignum.X86.R2Words.subBody) v fun v' => v'.zf = some (decide (j + 1 = K)) ∧
      SubJ s B mo xo to K q (j + 1) v' := by
  have wsv : Ws v B bytes := ws.of_wr I.keep.2.2
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.subBody_ok wsv I.bx I.si I.bp (by omega) (by omega) (by omega)
    (by omega)) fun v' ⟨hv, O', pb', ps', pp', di', z', K'⟩ => ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := K) (x := v.gpr .edi)
    (by rw [I.di, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  refine ⟨by rw [z', hc.2], ⟨?_, ?_, ?_, ?_, ?_, I.qlt, I.keep.trans (K'.mono (by decide)), ?_, ?_⟩⟩
  · rw [show mo + 4 * (j + 1) = mo + 4 * j + 4 by omega]; exact pb'
  · rw [show xo + 4 * (j + 1) = xo + 4 * j + 4 by omega]; exact ps'
  · rw [show to + 4 * (j + 1) = to + 4 * j + 4 by omega]; exact pp'
  · apply BitVec.eq_of_toNat_eq
    rw [di', hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [K'.1 _ (by decide)]; exact I.cx
  · exact (I.out.mono (by omega) (by omega)).trans (O'.mono (by omega) (by omega))
  · have hA : w32 v.mem B (mo + 4 * j) = w32 s.mem B (mo + 4 * j) := I.out.w32 (by omega) (by omega)
    have hX : w32 v.mem B (xo + 4 * j) = w32 s.mem B (xo + 4 * j) := I.out.w32 (by omega) (by omega)
    have hT : val32 v'.mem B to j = val32 v.mem B to j := O'.val32 (.inl (by omega)) (by omega)
    have hq : (v.gpr .ecx).toNat = q := by rw [I.cx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt I.qlt]
    rw [hA, hX, hq] at hv
    rw [val32_succ, val32_succ, val32_succ, hT, show 32 * (j + 1) = 32 * j + 32 by omega, Nat.pow_add,
      show to + 4 * (j + 1) = to + 4 * j + 4 by omega]
    exact sub0_val I.val hv

theorem subJLoop_ok {s v : State} {bytes mo xo to K q : Nat} (ws : Ws s B bytes) (nw : B.toNat + bytes ≤ 2 ^ 32)
    (gm : mo + 4 * K ≤ bytes) (gx : xo + 4 * (K + 1) ≤ bytes) (gt : to + 4 * (K + 1) ≤ bytes)
    (gmt : mo + 4 * K ≤ to ∨ to + 4 * (K + 1) ≤ mo) (gxt : xo + 4 * (K + 1) ≤ to ∨ to + 4 * (K + 1) ≤ xo)
    (hK : 0 < K) (I : SubJ s B mo xo to K q 0 v) :
    WP isa (.loop (.block VG.Impl.Bignum.X86.R2Words.subBody) .ne) v fun v' => SubJ s B mo xo to K q K v' := by
  refine WP.loop (M := isa) (fun n v => ∃ j, n = K - j ∧ j < K ∧ SubJ s B mo xo to K q j v) ?_ _ v
    ⟨0, rfl, hK, I⟩
  rintro n v ⟨j, rfl, hj, I⟩
  refine WP.mono (subJStep_ok ws nw gm gx gt gmt gxt hj I) fun v' ⟨z, I'⟩ => ?_
  by_cases e : j + 1 = K
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], K - (j + 1),
      by omega, j + 1, rfl, by omega, I'⟩

theorem subTop_val {T q D R G c w' x b : Nat} (hI : T + q * D = R + G * c) (hv : w' + c = x + 2 ^ 32 * b) :
    T + G * w' + q * D = R + G * x + G * 2 ^ 32 * b := by
  have e := congrArg (G * ·) hv
  simp only [Nat.mul_add] at e
  grind

theorem oQ_slot : VG.Impl.Rsa.X86.WordModRt.oQ = 76 := rfl

theorem sq_geo {kw a j K Z : Nat} (f21 : 160 + 21 * (4 * (kw + 2)) + 4 * (kw + 2) ≤ Z) (hj1 : 1 ≤ j)
    (hj : j < a) (hW : a + 3 ≤ kw) (eK : a - (j - 1) + 2 = K) :
    160 + 7 * (4 * (kw + 2)) + 4 * (j - 1) + 4 * K ≤ 160 + 14 * (4 * (kw + 2)) ∧
    160 + 20 * (4 * (kw + 2)) + 8 * (j - 1) + 4 * (K + 1) ≤ Z ∧
    160 + 14 * (4 * (kw + 2)) + 4 * (K + 1) ≤ 160 + 20 * (4 * (kw + 2)) := by omega

/-- `mulSubX`'s first block: `D[m] := q`, `T[0] := 0`, the loop's pointers and count. -/
theorem mulSubXHead_ok {s : State} (h : RtWs wid s B Z len 22) {a j : Nat} (hm : MLen s B Z nl a)
    (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len) {q : Nat}
    (hq : slot s.mem B VG.Impl.Rsa.X86.WordModRt.oQ = q) :
    WP isa (.block (VG.Impl.Rsa.X86.RecoverDetRt.winPtrs ++
      (([.mov .ecx (.mem (sc VG.Impl.Rsa.X86.WordModRt.oQ)), .store (at_ .ebx 0) .ecx] : List Instr) ++
        (VG.Impl.Rsa.X86.KeyRt.arrPtr wid .ebp sqT .eax ++
          ([.mov .eax (.imm 0), .store (at_ .ebp 0) .eax, .mov .edi (.reg .edx)] : List Instr))))) s fun u =>
      SubJ u B (arr (kw len) sqD + 4 * (j - 1)) (arr (kw len) sqZ + 8 * (j - 1)) (arr (kw len) sqT)
        (wq a - (j - 1) + 2) q 0 u ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u ∧
      u.mem = (s.mem.writeW (off B (arr (kw len) sqD + 4 * (j - 1))) (BitVec.ofNat 32 q)).writeW
        (off B (arr (kw len) sqT)) (0 : BitVec 32) := by
  have nw := h.ws.workspace.nowrap
  have f21 := h.ws.arr_fit (j := 21) (by decide)
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  obtain ⟨ez, ed, et⟩ := sq_arrs (kw len)
  simp only [S, arr, VG.Impl.Rsa.X86.Keys.hdr] at f21
  have hqlt : q < 2 ^ 32 := hq ▸ (s.mem.readW _ 32).isLt
  refine winPtrs_ok h hm hC hj1 (by omega) fun u Ku mu ps pb pd _ => ?_
  have hu := h.keep Ku (by decide) (by decide) (by rw [mu]; exact Outside.refl _ _ _ _)
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readHdr hu.ws (d := VG.Impl.Rsa.X86.WordModRt.oQ) (by rw [oQ_slot]; decide))
    fun u₁ U₁ _ => ?_
  have cx₁ : u₁.gpr .ecx = BitVec.ofNat 32 q := by rw [U₁.gpr, mu, hq]
  have ws₁ : Ws u₁ B Z := h.rt.of_wr (U₁.wr.trans Ku.2.2)
  have pb₁ : PtrAt u₁ B .ebx (arr (kw len) sqD + 4 * (j - 1)) := by rw [PtrAt, U₁.other _ (by decide)]; exact pb
  refine wp_storeS (ea_ptr ws₁ pb₁ (d := 0) (by rw [ed]; omega)) (ws_write ws₁ (by rw [ed]; omega)) fun u₂ M₂ => ?_
  have m₂ : u₂.mem = s.mem.writeW (off B (arr (kw len) sqD + 4 * (j - 1))) (BitVec.ofNat 32 q) := by
    rw [M₂.mem, U₁.mem, mu, cx₁, Nat.add_zero]
  have OD : Outside B (arr (kw len) sqD + 4 * (j - 1)) 4 s.mem u₂.mem := by
    rw [m₂]; exact writeW32_outside _ B _ (by omega)
  have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .esi] s u₂ :=
    (Ku.mono (by decide)).trans ((U₁.keeps.mono (by decide)).trans (M₂.keeps _))
  have h₂ := h.keep K₂ (by decide) (by decide) (OD.mono (Nat.zero_le _) (by rw [ed]; omega))
  refine arrPtr_ok (lenSrc h₂) h₂.lenLe h₂.edi (r := .ebp) (t := .eax) (j := sqT) (by decide) (by decide)
    (by rw [et]; omega) fun u₃ U₃ m₃ p₃ _ => ?_
  refine wp_movS (v := 0) rfl fun u₄ U₄ _ => ?_
  have ws₄ : Ws u₄ B Z := h₂.rt.of_wr (U₄.wr.trans U₃.2.2)
  have pp₄ : PtrAt u₄ B .ebp (arr (kw len) sqT) := by rw [PtrAt, U₄.other _ (by decide)]; exact p₃
  refine wp_storeS (ea_ptr ws₄ pp₄ (d := 0) (by rw [et]; omega)) (ws_write ws₄ (by rw [et]; omega)) fun u₅ M₅ => ?_
  refine wp_movS rfl fun u₆ U₆ _ => WP.block_nil ?_
  have m₆ : u₆.mem = u₂.mem.writeW (off B (arr (kw len) sqT)) (0 : BitVec 32) := by
    rw [U₆.mem, M₅.mem, U₄.gpr, U₄.mem, m₃, Nat.add_zero]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hqlt, Keeps.refl _ _, Outside.refl _ _ _ _, ?_⟩,
    (K₂.mono (by decide)).trans ((U₃.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans
      ((M₅.keeps _).trans (U₆.keeps.mono (by decide))))), by rw [m₆, m₂]⟩
  · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide),
      U₃.1 _ (by decide), M₂.gpr]; exact pb₁
  · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide),
      U₃.1 _ (by decide), M₂.gpr, U₁.other _ (by decide)]; exact ps
  · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₆.other _ (by decide), M₅.gpr]; exact pp₄
  · apply BitVec.eq_of_toNat_eq
    have := hm.le
    rw [U₆.gpr, M₅.gpr, U₄.other _ (by decide), U₃.1 _ (by decide), M₂.gpr, U₁.other _ (by decide), pd,
      Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [wq] at hj ⊢; omega)]
  · rw [U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide), U₃.1 _ (by decide), M₂.gpr]; exact cx₁
  · rw [m₆, Nat.mul_zero, Nat.add_zero, w32_write_self]; simp [val32]

/-- `mulSubX`'s last block: `T`'s top word, `edi` back, and what the step leaves. -/
theorem mulSubXTail_ok {s u v : State} (h : RtWs wid s B Z len 22) {a j q : Nat}
    (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len) (hqlt : q < 2 ^ 32)
    (Ku : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u)
    (mu : u.mem = (s.mem.writeW (off B (arr (kw len) sqD + 4 * (j - 1))) (BitVec.ofNat 32 q)).writeW
        (off B (arr (kw len) sqT)) (0 : BitVec 32))
    (I : SubJ u B (arr (kw len) sqD + 4 * (j - 1)) (arr (kw len) sqZ + 8 * (j - 1)) (arr (kw len) sqT)
        (wq a - (j - 1) + 2) q (wq a - (j - 1) + 2) v) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.subTop wid)) v fun t => RtWs wid t B Z len 22 ∧ Keep B (kw len) [sqT, sqD] [] s.mem t.mem ∧
      (∀ i, i < kw len + 2 → i ≠ j - 1 →
        w32 t.mem B (arr (kw len) sqD + 4 * i) = w32 s.mem B (arr (kw len) sqD + 4 * i)) ∧
      w32 t.mem B (arr (kw len) sqD + 4 * (j - 1)) = q ∧
      (∃ b, b < 2 ∧ val32 t.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) +
          q * val32 t.mem B (arr (kw len) sqD + 4 * (j - 1)) (wq a - (j - 1) + 2) =
        val32 s.mem B (arr (kw len) sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) + 2 ^ (32 * (wq a - (j - 1) + 3)) * b) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have nw := h.ws.workspace.nowrap
  have f21 := h.ws.arr_fit (j := 21) (by decide)
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  obtain ⟨ez, ed, et⟩ := sq_arrs (kw len)
  simp only [S, arr, VG.Impl.Rsa.X86.Keys.hdr] at f21
  obtain ⟨K, eK⟩ : ∃ K, wq a - (j - 1) + 2 = K := ⟨_, rfl⟩
  have e3 : wq a - (j - 1) + 3 = K + 1 := by omega
  rw [e3, eK]
  rw [eK] at I
  obtain ⟨g1, g2, g3⟩ := sq_geo f21 hj1 hj hW eK
  rw [← ed, ← et] at g1
  rw [← ez] at g2
  rw [← et, ← ez] at g3
  have gd : arr (kw len) sqD + 4 * (kw len + 2) ≤ arr (kw len) sqT := by rw [ed, et]; omega
  have OD : Outside B (arr (kw len) sqD + 4 * (j - 1)) 4 s.mem
      (s.mem.writeW (off B (arr (kw len) sqD + 4 * (j - 1))) (BitVec.ofNat 32 q)) :=
    writeW32_outside _ B _ (by omega)
  have OT0 : Outside B (arr (kw len) sqT) 4 (s.mem.writeW (off B (arr (kw len) sqD + 4 * (j - 1))) (BitVec.ofNat 32 q))
      u.mem := by rw [mu]; exact writeW32_outside _ B _ (by omega)
  have Kv : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s v := Ku.trans I.keep
  have OT1 : Outside B (arr (kw len) sqT) (4 * (K + 1))
      (s.mem.writeW (off B (arr (kw len) sqD + 4 * (j - 1))) (BitVec.ofNat 32 q)) v.mem :=
    (OT0.mono (by omega) (by omega)).trans (I.out.mono (by omega) (by omega))
  have Ov : Outside B 0 Z s.mem v.mem := (OD.mono (Nat.zero_le _) (by omega)).trans (OT1.mono (Nat.zero_le _) (by omega))
  have ca := h.wsArg.keep Kv (by decide) Ov
  have wsv : Ws v B Z := h.rt.of_wr Kv.2.2
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.subTop_ok (L := wid) wsv I.si I.bp (by omega) (by omega) ca)
    fun t' ⟨b, hb, hv', hmt', hdi, K'⟩ => ?_
  have Otop := writeW32_outside v.mem B (d := arr (kw len) sqT + 4 * K)
    (BitVec.ofNat 32 (w32 t'.mem B (arr (kw len) sqT + 4 * K))) (by omega)
  rw [← hmt'] at Otop
  have OT : Outside B (arr (kw len) sqT) (4 * (K + 1))
      (s.mem.writeW (off B (arr (kw len) sqD + 4 * (j - 1))) (BitVec.ofNat 32 q)) t'.mem :=
    OT1.trans (Otop.mono (by omega) (by omega))
  have Oall : Outside B 0 Z s.mem t'.mem :=
    (OD.mono (Nat.zero_le _) (by omega)).trans (OT.mono (Nat.zero_le _) (by omega))
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t' :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .esi, .ebp])
      ((Kv.trans (K'.mono (by decide))).mono (by decide)) (hdi.trans h.edi_eq.symm)
  have hD : ∀ i, i < kw len + 2 → w32 t'.mem B (arr (kw len) sqD + 4 * i) =
      w32 (s.mem.writeW (off B (arr (kw len) sqD + 4 * (j - 1))) (BitVec.ofNat 32 q)) B (arr (kw len) sqD + 4 * i) :=
    fun i hi => OT.w32 (.inl (by omega)) (by omega)
  refine ⟨h.keep Kall (by decide) (by decide) Oall, ?_, fun i hi hne => ?_, ?_, ⟨b, hb, ?_⟩, Kall⟩
  · exact (Keep.of_arr (d := 4 * (j - 1)) OD (by simp only [S]; omega) (by simp)).trans
      (Keep.of_arr (d := 0) (by simpa using OT) (by simp only [S]; omega) (by simp))
  · rw [hD i hi]
    exact OD.w32 (by rcases Nat.lt_or_gt_of_ne hne with c | c <;> omega) (by omega)
  · rw [hD (j - 1) (by omega), w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]
  · have hDv : val32 t'.mem B (arr (kw len) sqD + 4 * (j - 1)) K = val32 u.mem B (arr (kw len) sqD + 4 * (j - 1)) K := by
      rw [OT.val32 (.inl (by omega)) (by omega), OT0.val32 (.inl (by omega)) (by omega)]
    have hR : val32 s.mem B (arr (kw len) sqZ + 8 * (j - 1)) (K + 1) =
        val32 u.mem B (arr (kw len) sqZ + 8 * (j - 1)) (K + 1) :=
      (val32_congr fun i hi => by
        rw [OT0.w32 (.inr (by omega)) (by omega), OD.w32 (.inr (by omega)) (by omega)]).symm
    have hx : w32 v.mem B (arr (kw len) sqZ + 8 * (j - 1) + 4 * K) = w32 u.mem B (arr (kw len) sqZ + 8 * (j - 1) + 4 * K) :=
      I.out.w32 (.inr (by omega)) (by omega)
    have hT : val32 t'.mem B (arr (kw len) sqT) K = val32 v.mem B (arr (kw len) sqT) K :=
      Otop.val32 (.inl (by omega)) (by omega)
    rw [hx] at hv'
    rw [hDv, hR, val32_succ, val32_succ, hT, show 32 * (K + 1) = 32 * K + 32 by omega, Nat.pow_add]
    exact subTop_val I.val hv'

theorem mulSubX_ok {s : State} (h : RtWs wid s B Z len 22) {a j : Nat} (hm : MLen s B Z nl a)
    (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len) {q : Nat}
    (hq : slot s.mem B VG.Impl.Rsa.X86.WordModRt.oQ = q) :
    WP isa mulSubX s fun t => RtWs wid t B Z len 22 ∧ Keep B (kw len) [sqT, sqD] [] s.mem t.mem ∧
      (∀ i, i < kw len + 2 → i ≠ j - 1 →
        w32 t.mem B (arr (kw len) sqD + 4 * i) = w32 s.mem B (arr (kw len) sqD + 4 * i)) ∧
      w32 t.mem B (arr (kw len) sqD + 4 * (j - 1)) = q ∧
      (∃ b, b < 2 ∧ val32 t.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) +
          q * val32 t.mem B (arr (kw len) sqD + 4 * (j - 1)) (wq a - (j - 1) + 2) =
        val32 s.mem B (arr (kw len) sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) + 2 ^ (32 * (wq a - (j - 1) + 3)) * b) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have nw := h.ws.workspace.nowrap
  have f21 := h.ws.arr_fit (j := 21) (by decide)
  obtain ⟨ez, ed, et⟩ := sq_arrs (kw len)
  simp only [S, arr, VG.Impl.Rsa.X86.Keys.hdr] at f21
  have hqlt : q < 2 ^ 32 := hq ▸ (s.mem.readW _ 32).isLt
  obtain ⟨g1, g2, g3⟩ := sq_geo f21 hj1 hj hW rfl
  rw [← ed, ← et] at g1
  rw [← ez] at g2
  rw [← et, ← ez] at g3
  unfold mulSubX
  simp only [VG.Impl.Rsa.X86.Keys.seqs, List.append_assoc]
  refine WP.seq (WP.mono (mulSubXHead_ok h hm hC hj1 hj hW hq) fun u ⟨I₀, Ku, mu⟩ => ?_)
  refine WP.seq (WP.mono (subJLoop_ok (h.rt.of_wr Ku.2.2) nw (by omega) g2 (by omega) (.inl g1)
    (.inr (by omega)) (by omega) I₀) fun v I => ?_)
  exact mulSubXTail_ok h hj1 hj hW hqlt Ku mu I

end VG.Proof.Rsa.X86.Recover
