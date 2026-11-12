module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Add
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega

/-! # Prime recovery's word moves on i686

`RecoverDetRt.moveH`: an array cleared, then the words of another copied into
it from word `c` on (`srcOff`, a shift down by `c` words) or to word `c` on
(`dstOff`, a shift up), `c` from the header word `sC4` (`4 c`). The copy's
step (`moveStep_ok`) counts `edx` down by bytes.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

variable {B : Addr}

/-- After words `0, …, j - 1` of a move of `K` words from `so` to `do'`. -/
structure MoveI (s : State) (B : Addr) (so do' K j : Nat) (u : State) : Prop where
  si : PtrAt u B .esi (so + 4 * j)
  bp : PtrAt u B .ebp (do' + 4 * j)
  dx : u.gpr .edx = BitVec.ofNat 32 (4 * (K - j))
  keep : Keeps [.eax, .edx, .esi, .ebp] s u
  out : Outside B do' (4 * j) s.mem u.mem
  val : val32 u.mem B do' j = val32 s.mem B so j

/-- A move's step: word `j` from `so` to `do'`. -/
theorem moveStep_ok {s u : State} {bytes so do' K j : Nat} (ws : Ws s B bytes) (nw : B.toNat + bytes ≤ 2 ^ 32)
    (hs : so + 4 * K ≤ bytes) (hd : do' + 4 * K ≤ bytes) (sep : so + 4 * K ≤ do' ∨ do' + 4 * K ≤ so)
    (hj : j < K) (I : MoveI s B so do' K j u) :
    WP isa (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) u fun u' =>
      u'.zf = some (decide (j + 1 = K)) ∧ MoveI s B so do' K (j + 1) u' := by
  have wsu : Ws u B bytes := ws.of_wr I.keep.2.2
  refine wp_movS (readSrc_ptr wsu I.si (d := 0) (by omega)) fun u₁ U₁ _ => ?_
  have ws₁ := wsu.of_wr U₁.wr
  have pp₁ : PtrAt u₁ B .ebp (do' + 4 * j) := by rw [PtrAt, U₁.other _ (by decide)]; exact I.bp
  refine wp_storeS (ea_ptr ws₁ pp₁ (d := 0) (by omega)) (ws_write ws₁ (by omega)) fun u₂ M₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_subZ rfl fun u₅ U₅ z₅ => WP.block_nil ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := K) (x := u.gpr .edx)
    (by rw [I.dx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  have dx₄ : u₄.gpr .edx = u.gpr .edx := by
    rw [U₄.other _ (by decide), U₃.other _ (by decide), M₂.gpr, U₁.other _ (by decide)]
  have m₅ : u₅.mem = u.mem.writeW (off B (do' + 4 * j)) (u.mem.readW (off B (so + 4 * j)) 32) := by
    rw [U₅.mem, U₄.mem, U₃.mem, M₂.mem, U₁.mem, U₁.gpr, Nat.add_zero, Nat.add_zero]
  have O := writeW32_outside u.mem B (d := do' + 4 * j) (u.mem.readW (off B (so + 4 * j)) 32) (by omega)
  rw [← m₅] at O
  refine ⟨by rw [z₅, dx₄, hc.2], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [PtrAt, U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, ptr_add (s := u₂) (x := so + 4 * j)
      (by rw [PtrAt, M₂.gpr, U₁.other _ (by decide)]; exact I.si)]
    congr 2
  · rw [PtrAt, U₅.other _ (by decide), U₄.gpr, U₃.other _ (by decide), ptr_add (s := u₂) (x := do' + 4 * j)
      (by rw [PtrAt, M₂.gpr]; exact pp₁)]
    congr 2
  · apply BitVec.eq_of_toNat_eq
    rw [U₅.gpr, dx₄, hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact I.keep.trans (((U₁.keeps.mono (by decide)).trans (M₂.keeps _)).trans
      (((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))))
  · exact (I.out.mono (by omega) (by omega)).trans (O.mono (by omega) (by omega))
  · rw [val32_succ, val32_succ, O.val32 (.inl (by omega)) (by omega), I.val, m₅, w32_write_self]
    congr 2
    exact I.out.w32 (by omega) (by omega)

/-- The move's loop: `K ≥ 1` words from `so` to `do'`. -/
theorem moveLoop_ok {s u : State} {bytes so do' K : Nat} (ws : Ws s B bytes) (nw : B.toNat + bytes ≤ 2 ^ 32)
    (hs : so + 4 * K ≤ bytes) (hd : do' + 4 * K ≤ bytes) (sep : so + 4 * K ≤ do' ∨ do' + 4 * K ≤ so)
    (hK : 0 < K) (I : MoveI s B so do' K 0 u) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne) u fun v => MoveI s B so do' K K v := by
  refine WP.loop (M := isa) (Q := fun v => MoveI s B so do' K K v)
    (fun n v => ∃ j, n = K - j ∧ j < K ∧ MoveI s B so do' K j v) ?_ _ u ⟨0, rfl, hK, I⟩
  rintro n v ⟨j, rfl, hj, J⟩
  refine WP.mono (moveStep_ok ws nw hs hd sep hj J) fun v' ⟨z, J'⟩ => ?_
  by_cases e : j + 1 = K
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ J'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], K - (j + 1),
      by omega, j + 1, rfl, by omega, J'⟩

/-- A number shifted down by `c` words: its words from `c` on. -/
theorem val32_down (m : Mem) (d c K : Nat) :
    val32 m B (d + 4 * c) K = val32 m B d (c + K) / 2 ^ (32 * c) := by
  rw [val32_append, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (val32_lt m B d c), Nat.zero_add]

/-- A number shifted up by `c` words, modulo `2^(32 (K + c))`: its low `K` words, `c` words up. -/
theorem val32_up (m : Mem) (d c K : Nat) :
    2 ^ (32 * c) * val32 m B d K = val32 m B d (K + c) * 2 ^ (32 * c) % 2 ^ (32 * (K + c)) := by
  rw [show 32 * (K + c) = 32 * K + 32 * c by omega, Nat.pow_add, Nat.mul_mod_mul_right, val32_append,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt m B d K), Nat.mul_comm]

/-- Words of a zero number are zero. -/
theorem val32_zero_split {m : Mem} {d a b : Nat} (h : val32 m B d (a + b) = 0) :
    val32 m B d a = 0 ∧ val32 m B (d + 4 * a) b = 0 := by
  rw [val32_append] at h
  have := Nat.two_pow_pos (32 * a)
  refine ⟨by omega, ?_⟩
  rcases Nat.eq_zero_of_add_eq_zero h with ⟨_, h2⟩
  exact (Nat.mul_eq_zero.mp h2).resolve_left (by omega)

open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc bytesB_ok zeroWide_ok)

/-- The header word of a word stage's size, read through any register writes. -/
theorem readSrc_sC4 {L : Lay} {s : State} {Z len N : Nat} (h : RtWs L s B Z len N) {c : Nat}
    (hC : slot s.mem B VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c) :
    readSrc s (.mem (sc VG.Impl.Rsa.X86.RecoverDetRt.sC4)) = some (BitVec.ofNat 32 (4 * c)) := by
  have := h.ws.hdr_le
  rw [readSrc_sc h.ws.workspace (by unfold VG.Impl.Rsa.X86.RecoverDetRt.sC4 VG.Impl.Rsa.X86.Keys.hdr at *; omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [← hC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- `moveH` down: `dst` (cleared, `W + 1` words) the words of `src` from word `c` on, `c` from
`sC4`. -/
theorem moveDown_ok {L : Lay} {s : State} {Z len N : Nat} (h : RtWs L s B Z len N) {src dst c : Nat}
    (hs : src < N) (hd : dst < N) (hsd : src ≠ dst) (hc : c < kw len)
    (hC : slot s.mem B VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.moveH L src dst true false) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) [dst] [] s.mem t.mem ∧
      val32 t.mem B (arr (kw len) dst) (kw len + 1) = num s.mem B (kw len) src / 2 ^ (32 * c) ∧
      Keeps [.eax, .ecx, .edx, .esi, .ebp] s t := by
  have nw := h.ws.workspace.nowrap
  have fs := h.ws.arr_fit hs
  have fd := h.ws.arr_fit hd
  have dj := VG.Proof.Rsa.X86.Keys.arr_disj (w := kw len) hsd
  have hh := h.ws.hdr_le
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fs fd dj
  unfold VG.Impl.Rsa.X86.RecoverDetRt.moveH
  simp only [VG.Impl.Rsa.X86.Keys.seqs, ite_true, Bool.false_eq_true, ite_false, List.append_nil, List.append_assoc]
  refine WP.seq (WP.mono (zeroWide_ok h hd) fun s₁ ⟨h₁, K₁, z₁, k₁⟩ => ?_)
  have C₁ : slot s₁.mem B VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c := by
    rw [K₁.slot (by unfold VG.Impl.Rsa.X86.RecoverDetRt.sC4 VG.Impl.Rsa.X86.Keys.hdr at *; omega) (by simp), hC]
  refine WP.seq ?_
  refine arrPtr_ok (lenSrc h₁) h₁.lenLe h₁.edi (r := .esi) (t := .edx) (j := src) (by decide) (by decide)
    (by omega) fun u₁ U₁ m₁ p₁ _ => ?_
  have h₁' := h₁.keep U₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sC4 h₁' (by rw [m₁]; exact C₁)) fun u₂ U₂ _ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => ?_
  have p₃ : PtrAt u₃ B .esi (arr (kw len) src + 4 * c) := by
    rw [PtrAt, U₃.gpr, U₂.other _ (by decide), ptr_add (s := u₁) (x := arr (kw len) src) p₁, U₂.gpr,
      BitVec.toNat_ofNat]
    omega
  have K₃ : Keeps [.esi, .edx] s₁ u₃ := (U₁.mono (by decide)).trans
    ((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide)))
  have m₃ : u₃.mem = s₁.mem := by rw [U₃.mem, U₂.mem, m₁]
  have h₃ := h₁.keep K₃ (by decide) (by decide) (by rw [m₃]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₃) h₃.lenLe h₃.edi (r := .ebp) (t := .edx) (j := dst) (by decide) (by decide)
    (by omega) fun u₄ U₄ m₄ p₄ _ => ?_
  have h₄ := h₃.keep U₄ (by decide) (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _)
  refine bytesB_ok (lenSrc h₄) h₄.lenLe fun u₅ U₅ m₅ e₅ => ?_
  have h₅ := h₄.keep U₅ (by decide) (by decide) (by rw [m₅]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sC4 h₅ (by rw [m₅, m₄, m₃]; exact C₁)) fun u₆ U₆ _ => ?_
  refine wp_subS (v := u₆.gpr .eax) rfl fun u₇ U₇ _ => WP.block_nil ?_
  have K₇ : Keeps [.eax, .edx, .esi, .ebp] s₁ u₇ := (K₃.mono (by decide)).trans ((U₄.mono (by decide)).trans
    ((U₅.mono (by decide)).trans ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide)))))
  have m₇ : u₇.mem = s₁.mem := by rw [U₇.mem, U₆.mem, m₅, m₄, m₃]
  have I₀ : MoveI s₁ B (arr (kw len) src + 4 * c) (arr (kw len) dst) (kw len - c) 0 u₇ := by
    refine ⟨?_, ?_, ?_, K₇, by rw [m₇]; exact Outside.refl _ _ _ _, by simp [val32]⟩
    · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₇.other _ (by decide), U₆.other _ (by decide),
        U₅.1 _ (by decide), U₄.1 _ (by decide)]
      exact p₃
    · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₇.other _ (by decide), U₆.other _ (by decide),
        U₅.1 _ (by decide)]
      exact p₄
    · apply BitVec.eq_of_toNat_eq
      rw [U₇.gpr, U₆.other _ (by decide), U₆.gpr, BitVec.toNat_sub, e₅, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
  refine WP.mono (moveLoop_ok h₁.rt nw (by omega) (by omega) (by omega) (by omega) I₀) fun v I => ?_
  have Os : Outside B (arr (kw len) dst) (4 * (kw len - c)) s₁.mem v.mem := I.out
  refine ⟨h₁.keep I.keep (by decide) (by decide) (Os.mono (by omega) (by omega)),
    K₁.trans (Keep.of_arr (d := 0) (by simpa using Os) (by simp only [S]; omega) (by simp)), ?_,
    ((k₁.mono (by decide) : Keeps [.eax, .ecx, .edx, .esi, .ebp] s s₁).trans (I.keep.mono (by decide)))⟩
  have src₁ : val32 s₁.mem B (arr (kw len) src) (kw len) = val32 s.mem B (arr (kw len) src) (kw len) :=
    K₁.num (by simp [Ne.symm hsd]) (by simp) (by simp only [S]; omega)
  have zs := val32_zero_split (a := kw len - c) (b := c + 1) (by rw [show kw len - c + (c + 1) = kw len + 1 by omega]; exact z₁)
  rw [show kw len + 1 = (kw len - c) + (c + 1) by omega, val32_append, I.val,
    Os.val32 (.inr (by omega)) (by omega), zs.2, Nat.mul_zero, Nat.add_zero,
    val32_down, show c + (kw len - c) = kw len by omega, src₁]

/-- `moveH` up: `dst` (cleared, `W + 1` words) the low words of `src` from word `c` on, `c` from
`sC4`. -/
theorem moveUp_ok {L : Lay} {s : State} {Z len N : Nat} (h : RtWs L s B Z len N) {src dst c : Nat}
    (hs : src < N) (hd : dst < N) (hsd : src ≠ dst) (hc : c < kw len)
    (hC : slot s.mem B VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.moveH L src dst false true) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) [dst] [] s.mem t.mem ∧
      val32 t.mem B (arr (kw len) dst) (kw len + 1) =
        num s.mem B (kw len) src * 2 ^ (32 * c) % 2 ^ (32 * kw len) ∧
      Keeps [.eax, .ecx, .edx, .esi, .ebp] s t := by
  have nw := h.ws.workspace.nowrap
  have fs := h.ws.arr_fit hs
  have fd := h.ws.arr_fit hd
  have dj := VG.Proof.Rsa.X86.Keys.arr_disj (w := kw len) hsd
  have hh := h.ws.hdr_le
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fs fd dj
  unfold VG.Impl.Rsa.X86.RecoverDetRt.moveH
  simp only [VG.Impl.Rsa.X86.Keys.seqs, ite_true, Bool.false_eq_true, ite_false, List.append_nil, List.append_assoc]
  refine WP.seq (WP.mono (zeroWide_ok h hd) fun s₁ ⟨h₁, K₁, z₁, k₁⟩ => ?_)
  have C₁ : slot s₁.mem B VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c := by
    rw [K₁.slot (by unfold VG.Impl.Rsa.X86.RecoverDetRt.sC4 VG.Impl.Rsa.X86.Keys.hdr at *; omega) (by simp), hC]
  refine WP.seq ?_
  refine arrPtr_ok (lenSrc h₁) h₁.lenLe h₁.edi (r := .esi) (t := .edx) (j := src) (by decide) (by decide)
    (by omega) fun u₁ U₁ m₁ p₁ _ => ?_
  have h₁' := h₁.keep U₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₁') h₁'.lenLe h₁'.edi (r := .ebp) (t := .edx) (j := dst) (by decide) (by decide)
    (by omega) fun u₂ U₂ m₂ p₂ _ => ?_
  have h₂ := h₁'.keep U₂ (by decide) (by decide) (by rw [m₂, m₁]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sC4 h₂ (by rw [m₂, m₁]; exact C₁)) fun u₃ U₃ _ => ?_
  refine wp_addS rfl fun u₄ U₄ _ => ?_
  have p₄ : PtrAt u₄ B .ebp (arr (kw len) dst + 4 * c) := by
    rw [PtrAt, U₄.gpr, U₃.other _ (by decide), ptr_add (s := u₂) (x := arr (kw len) dst) p₂, U₃.gpr,
      BitVec.toNat_ofNat]
    omega
  have K₄ : Keeps [.esi, .ebp, .edx] s₁ u₄ := (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))))
  have m₄ : u₄.mem = s₁.mem := by rw [U₄.mem, U₃.mem, m₂, m₁]
  have h₄ := h₁.keep K₄ (by decide) (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _)
  refine bytesB_ok (lenSrc h₄) h₄.lenLe fun u₅ U₅ m₅ e₅ => ?_
  have h₅ := h₄.keep U₅ (by decide) (by decide) (by rw [m₅]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sC4 h₅ (by rw [m₅, m₄]; exact C₁)) fun u₆ U₆ _ => ?_
  refine wp_subS (v := u₆.gpr .eax) rfl fun u₇ U₇ _ => WP.block_nil ?_
  have K₇ : Keeps [.eax, .edx, .esi, .ebp] s₁ u₇ := (K₄.mono (by decide)).trans
    ((U₅.mono (by decide)).trans ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide))))
  have m₇ : u₇.mem = s₁.mem := by rw [U₇.mem, U₆.mem, m₅, m₄]
  have p₁' : PtrAt u₄ B .esi (arr (kw len) src) := by
    rw [PtrAt, U₄.other _ (by decide), U₃.other _ (by decide), U₂.1 _ (by decide)]; exact p₁
  have I₀ : MoveI s₁ B (arr (kw len) src) (arr (kw len) dst + 4 * c) (kw len - c) 0 u₇ := by
    refine ⟨?_, ?_, ?_, K₇, by rw [m₇]; exact Outside.refl _ _ _ _, by simp [val32]⟩
    · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₇.other _ (by decide), U₆.other _ (by decide),
        U₅.1 _ (by decide)]
      exact p₁'
    · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₇.other _ (by decide), U₆.other _ (by decide),
        U₅.1 _ (by decide)]
      exact p₄
    · apply BitVec.eq_of_toNat_eq
      rw [U₇.gpr, U₆.other _ (by decide), U₆.gpr, BitVec.toNat_sub, e₅, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
  refine WP.mono (moveLoop_ok h₁.rt nw (by omega) (by omega) (by omega) (by omega) I₀) fun v I => ?_
  have Os : Outside B (arr (kw len) dst + 4 * c) (4 * (kw len - c)) s₁.mem v.mem := I.out
  refine ⟨h₁.keep I.keep (by decide) (by decide) (Os.mono (by omega) (by omega)),
    K₁.trans (Keep.of_arr (d := 4 * c) (by simpa using Os) (by simp only [S]; omega) (by simp)), ?_,
    ((k₁.mono (by decide) : Keeps [.eax, .ecx, .edx, .esi, .ebp] s s₁).trans (I.keep.mono (by decide)))⟩
  have src₁ : val32 s₁.mem B (arr (kw len) src) (kw len) = val32 s.mem B (arr (kw len) src) (kw len) :=
    K₁.num (by simp [Ne.symm hsd]) (by simp) (by simp only [S]; omega)
  have zs := val32_zero_split (a := c) (b := kw len - c + 1)
    (by rw [show c + (kw len - c + 1) = kw len + 1 by omega]; exact z₁)
  have zt := val32_zero_split (a := kw len - c) (b := 1) zs.2
  rw [show kw len + 1 = c + ((kw len - c) + 1) by omega, val32_append, val32_append, I.val,
    Os.val32 (.inl (by omega)) (by omega), Os.val32 (.inr (by omega)) (by omega), zs.1, zt.2,
    Nat.mul_zero, Nat.add_zero, Nat.zero_add, val32_up, show kw len - c + c = kw len by omega, src₁]

/-! ## The OR of low words -/

/-- A number's low `c` words, as its value mod `2^(32 c)`. -/
theorem val32_mod (m : Mem) (d c k : Nat) : val32 m B d (c + k) % 2 ^ (32 * c) = val32 m B d c := by
  rw [val32_append, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt m B d c)]

theorem or_zero_iff (x y : BitVec 32) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

theorem toNat_eq_zero_iff (v : BitVec 32) : v.toNat = 0 ↔ v = 0 :=
  ⟨fun e => BitVec.eq_of_toNat_eq (by rw [e]; rfl), fun e => by rw [e]; rfl⟩

/-- After words `0, …, j - 1` of `orLowH`'s loop. -/
structure OrI (s : State) (B : Addr) (a b c j : Nat) (u : State) : Prop where
  si : PtrAt u B .esi (a + 4 * j)
  bp : PtrAt u B .ebp (b + 4 * j)
  dx : (u.gpr .edx).toNat = 4 * (c - j)
  keep : Keeps [.ecx, .edx, .esi, .ebp] s u
  mem : u.mem = s.mem
  cx : u.gpr .ecx = 0 ↔ (val32 s.mem B a j = 0 ∧ val32 s.mem B b j = 0)

theorem orStep_ok {s u : State} {bytes a b c j : Nat} (ws : Ws s B bytes)
    (ha : a + 4 * c ≤ bytes) (hb : b + 4 * c ≤ bytes) (hj : j < c) (I : OrI s B a b c j u) :
    WP isa (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .or .ecx (.mem (at_ .ebp 0)), .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) u fun u' =>
      u'.zf = some (decide (j + 1 = c)) ∧ OrI s B a b c (j + 1) u' := by
  have wsu : Ws u B bytes := ws.of_wr I.keep.2.2
  refine wp_orS (readSrc_ptr wsu I.si (d := 0) (by omega)) fun u₁ U₁ => ?_
  have pp₁ : PtrAt u₁ B .ebp (b + 4 * j) := by rw [PtrAt, U₁.other _ (by decide)]; exact I.bp
  refine wp_orS (readSrc_ptr (wsu.of_wr U₁.wr) pp₁ (d := 0) (by omega)) fun u₂ U₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_subZ rfl fun u₅ U₅ z₅ => WP.block_nil ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := c) (x := u.gpr .edx) I.dx hj
  have dx₄ : u₄.gpr .edx = u.gpr .edx := by
    rw [U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide)]
  have m₁ : u₁.mem = s.mem := by rw [U₁.mem, I.mem]
  refine ⟨by rw [z₅, dx₄, hc.2], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [PtrAt, U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, ptr_add (s := u₂) (x := a + 4 * j)
      (by rw [PtrAt, U₂.other _ (by decide), U₁.other _ (by decide)]; exact I.si)]
    congr 2
  · rw [PtrAt, U₅.other _ (by decide), U₄.gpr, U₃.other _ (by decide), ptr_add (s := u₂) (x := b + 4 * j)
      (by rw [PtrAt, U₂.other _ (by decide)]; exact pp₁)]
    congr 2
  · rw [U₅.gpr, dx₄, hc.1]
  · exact I.keep.trans ((U₁.keeps.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans
      ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))))))
  · rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  · rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.gpr, U₁.gpr,
      or_zero_iff, or_zero_iff, I.cx, val32_succ, val32_succ, m₁, I.mem, Nat.add_zero, Nat.add_zero]
    have p := Nat.two_pow_pos (32 * j)
    rw [← toNat_eq_zero_iff (s.mem.readW (off B (a + 4 * j)) 32),
      ← toNat_eq_zero_iff (s.mem.readW (off B (b + 4 * j)) 32)]
    change (((_ ∧ _) ∧ w32 s.mem B (a + 4 * j) = 0) ∧ w32 s.mem B (b + 4 * j) = 0) ↔ _
    constructor
    · rintro ⟨⟨⟨x, y⟩, z⟩, v⟩
      exact ⟨by rw [x, z, Nat.mul_zero], by rw [y, v, Nat.mul_zero]⟩
    · rintro ⟨x, y⟩
      have x₂ : val32 s.mem B a j = 0 := by omega
      have x₁ : 2 ^ (32 * j) * w32 s.mem B (a + 4 * j) = 0 := by omega
      have y₂ : val32 s.mem B b j = 0 := by omega
      have y₁ : 2 ^ (32 * j) * w32 s.mem B (b + 4 * j) = 0 := by omega
      exact ⟨⟨⟨x₂, y₂⟩, (Nat.mul_eq_zero.mp x₁).resolve_left (by omega)⟩,
        (Nat.mul_eq_zero.mp y₁).resolve_left (by omega)⟩

/-- `orLowH`: `ecx` zero exactly where the low `c` words of `[a]` and `[b]` are (`4 c` in `sC4`). -/
theorem orLowH_ok {s : State} {Z len N : Nat} (h : RtWs VG.Impl.Rsa.X86.RecoverRt.nar s B Z len N)
    {a b c : Nat} (ha : a < N) (hb : b < N) (hc0 : 0 < c) (hc : c ≤ kw len)
    (hC : slot s.mem B VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.orLowH a b) s fun t => t.mem = s.mem ∧
      Keeps [.ecx, .edx, .esi, .ebp] s t ∧
      (t.gpr .ecx = 0 ↔ (num s.mem B (kw len) a % 2 ^ (32 * c) = 0 ∧ num s.mem B (kw len) b % 2 ^ (32 * c) = 0)) := by
  have nw := h.ws.workspace.nowrap
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fa fb
  unfold VG.Impl.Rsa.X86.RecoverDetRt.orLowH
  refine WP.seq ?_
  rw [List.append_assoc]
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .esi) (t := .edx) (j := a) (by decide) (by decide)
    (by omega) fun u₁ U₁ m₁ p₁ _ => ?_
  have h₁ := h.keep U₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₁) h₁.lenLe h₁.edi (r := .ebp) (t := .edx) (j := b) (by decide) (by decide)
    (by omega) fun u₂ U₂ m₂ p₂ _ => ?_
  have h₂ := h₁.keep U₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
  refine wp_movS (v := 0) rfl fun u₃ U₃ _ => ?_
  refine wp_movS (readSrc_sC4 (h₂.keep U₃.keeps (by decide) (by decide) (by rw [U₃.mem]; exact Outside.refl _ _ _ _))
    (by rw [U₃.mem, m₂, m₁]; exact hC)) fun u₄ U₄ _ => WP.block_nil ?_
  have I₀ : OrI s B (arr (kw len) a) (arr (kw len) b) c 0 u₄ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₄.other _ (by decide), U₃.other _ (by decide),
        U₂.1 _ (by decide)]
      exact p₁
    · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₄.other _ (by decide), U₃.other _ (by decide)]
      exact p₂
    · rw [U₄.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.sub_zero]
    · exact (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
        ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))))
    · rw [U₄.mem, U₃.mem, m₂, m₁]
    · rw [U₄.other _ (by decide), U₃.gpr]; simp [val32]
  refine WP.loop (M := isa) (fun n v => ∃ j, n = c - j ∧ j < c ∧ OrI s B (arr (kw len) a) (arr (kw len) b) c j v)
    ?_ (c - 0) u₄ ⟨0, rfl, hc0, I₀⟩
  rintro n v ⟨j, rfl, hj, J⟩
  refine WP.mono (orStep_ok h.rt (by omega) (by omega) hj J) fun v' ⟨z, J'⟩ => ?_
  by_cases e : j + 1 = c
  · refine .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], J'.mem, J'.keep, ?_⟩
    rw [J'.cx, e, num, num, show kw len = c + (kw len - c) by omega, val32_mod, val32_mod]
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], c - (j + 1),
      by omega, j + 1, rfl, by omega, J'⟩

end VG.Proof.Rsa.X86.Recover
