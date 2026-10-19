module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Fn
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Calls
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: a short copy, to `vg_aes_gcm_seal_split`

Untrusted: everything here is checked by Lean. What each block of the path
of a text whose slices after the first are fewer than `t` bytes does, from
the arguments kept in `work`: the test (`splitTest_wp`), the nonce and the
first slice kept, and the gathering's registers for the slices after it
(`splitEntry_ok`, `splitFirst_ok`, `splitKeep_ok`), what the gathering
needs (`splitGatherPre`) and leaves (`split_after`), and the arguments of
`vg_aes_gcm_seal_split` (`splitArgs_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (GatherPre GKeeps gatherRegs frame_of)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes
open VG.Spec.Gcm (gathered gatheredLen)

/-! ## The slices after the first -/

/-- `n + 1` descriptors list the slice of the first, then those of the `n`
after it. -/
theorem listed_zero (m : Mem) (p : Addr) (n : Nat) :
    Sig.listed 64 m .u8 p (n + 1) =
      ⟨(m.readW p 64).setWidth 64, (m.readW (p + BitVec.ofNat 64 8) 64).toNat * Elem.u8.size⟩ ::
        Sig.listed 64 m .u8 (p + BitVec.ofNat 64 16) n := by
  simp only [Sig.listed, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ => ?_⟩
  simp only [Function.comp]
  have e : p + BitVec.ofNat 64 ((i + 1) * (2 * (64 / 8))) =
      p + BitVec.ofNat 64 16 + BitVec.ofNat 64 (i * (2 * (64 / 8))) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [e]

theorem gathered_zero (m : Mem) (p : Addr) (n : Nat) :
    gathered 64 m p (n + 1) = bytesAt m (m.readW p 64) (m.readW (p + BitVec.ofNat 64 8) 64).toNat ++
      gathered 64 m (p + BitVec.ofNat 64 16) n := by
  simp [gathered, listed_zero, Elem.size]

theorem gatheredLen_zero (m : Mem) (p : Addr) (n : Nat) :
    gatheredLen 64 m p (n + 1) = (m.readW (p + BitVec.ofNat 64 8) 64).toNat +
      gatheredLen 64 m (p + BitVec.ofNat 64 16) n := by
  simp [gatheredLen, listed_zero, Elem.size]

section
variable (s : State)

/-- The slices skipped: the first, if any. -/
abbrev k0 : Nat := if Cnt s = 0 then 0 else 1
/-- The first slice's length (0 if there is none) and address (the descriptors' if none). -/
abbrev fl : Nat := gl s (k0 s)
abbrev fb : Addr := if Cnt s = 0 then Src s else sb s 0

theorem k0_le : k0 s ≤ Cnt s := by unfold k0; split <;> omega

/-- What the short path's threshold applies to: the text's length, or 0 if
its first slice holds all its whole blocks. -/
abbrev shortLen : Nat := if 16 * (L s / 16) ≤ fl s then 0 else L s

/-- What the choice between copying the text whole and sealing it from its
first slice applies to: 0 unless its first slice holds all its whole blocks,
and then that slice's length. -/
abbrev selLen : Nat := if fl s < 16 * (L s / 16) then 0 else fl s

theorem fl_eq : fl s = if Cnt s = 0 then 0 else sl s 0 := by
  unfold fl k0; split
  · exact gl_zero
  · rw [gl_succ, gl_zero, Nat.zero_add]

/-- The first slice's bytes. -/
theorem pt_k0 : pt s (k0 s) = bytesAt s.mem (fb s) (fl s) := by
  unfold fl fb k0; split
  · simp [pt, gathered, Sig.listed, gl_zero, bytesAt]
  · rw [pt_succ, gl_succ, gl_zero, Nat.zero_add]; simp [pt, gathered, Sig.listed]

/-- The text: the first slice, then those after it. -/
theorem pt_split : pt s (Cnt s) = pt s (k0 s) ++ gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) ∧
    gl s (Cnt s) = fl s + gatheredLen 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) := by
  unfold fl k0; split
  · next h => simp [pt, gl, h, gl_zero, gathered, gatheredLen, Sig.listed]
  · next h =>
    obtain ⟨n, hn⟩ : ∃ n, Cnt s = n + 1 := ⟨Cnt s - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]
    have e0 : pt s 0 = [] := by simp [pt, gathered, Sig.listed]
    have h0 : Src s + BitVec.ofNat 64 (16 * 0) = Src s := by simp
    refine ⟨?_, ?_⟩
    · show gathered 64 s.mem (Src s) (n + 1) = pt s (0 + 1) ++ _
      rw [gathered_zero, pt_succ, e0, List.nil_append, sb, sl, h0]
    · show gatheredLen 64 s.mem (Src s) (n + 1) = gl s (0 + 1) + _
      rw [gatheredLen_zero, gl_succ, gl_zero, Nat.zero_add, sl, h0]

/-- The slices after the first are slices of the text. -/
theorem listed_k0 : ∀ r ∈ Sig.listed 64 s.mem .u8 (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s), r ∈ lsR s := by
  intro r hr
  unfold k0 at hr; split at hr
  · simpa using hr
  · next h =>
    obtain ⟨n, hn⟩ : ∃ n, Cnt s = n + 1 := ⟨Cnt s - 1, by omega⟩
    simp only [lsR, hn, Nat.add_sub_cancel, Nat.mul_one] at hr ⊢
    rw [listed_zero]
    exact List.mem_cons_of_mem _ hr

end

/-- `n` descriptors list the first `k` (none or one) slices, then the rest. -/
theorem gathered_k (m : Mem) (p : Addr) {n k : Nat} (hk : k = 0 ∨ (k = 1 ∧ n ≠ 0)) :
    gathered 64 m p n = gathered 64 m p k ++ gathered 64 m (p + BitVec.ofNat 64 (16 * k)) (n - k) := by
  rcases hk with rfl | ⟨rfl, hn⟩
  · simp [gathered, Sig.listed]
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [gathered_zero, Nat.add_sub_cancel, show (1 : Nat) = 0 + 1 from rfl, gathered_zero]
    simp [gathered, Sig.listed]

/-- `k0`, for `gathered_k`. -/
theorem k0_cases (s : State) : k0 s = 0 ∨ (k0 s = 1 ∧ Cnt s ≠ 0) := by
  unfold k0; split <;> simp_all

/-! ## The test -/

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

theorem fl_le : fl s ≤ L s := gl_le hp (k0_le s)

/-- `work` in `r11`, no first slice yet, and `ZF` if there is no slice. -/
theorem splitT1_ok {st : State} (h : Base s (AL s) 0 st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 48)), .mov32 .r10 (imm 0), .mov .rax (.mem (at_ .r11 gLeft)),
      .alu .test .rax (.reg .rax)]) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.gpr .r10 = 0 ∧ st'.zf = some (decide (Cnt s = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  have r₈ := h.slot hp (d := 64) (by decide)
  have hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  have hz := and_self_beq hC
  have hleft : st.mem.readW (W s + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 (Cnt s) := by
    rw [h.kept.left, Nat.sub_zero]
  apply WP.of_runBlock
  refine ⟨_, by simp only [gLeft]; xrun [a₅, e₅, r₈, hleft], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, imm]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, hz]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The first slice's length into `r10`. -/
theorem splitT2_ok (hc : Cnt s ≠ 0) {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s) :
    WP isa (.block [.mov .r10 (.mem (at_ .r11 gDesc)), .mov .r10 (.mem (at_ .r10 8))]) st fun st' =>
      st'.gpr .r10 = BitVec.ofNat 64 (fl s) ∧ (∀ r, r ≠ .r10 → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  have r₇ := h.slot hp (d := 56) (by decide)
  have d₈ := desc_in hp h (i := 0) (by omega) (d := 8) (by decide)
  have v₈ := sl_eq hp h.frame (i := 0) (by omega)
  have hd : st.mem.readW (W s + BitVec.ofNat 64 56) 64 = Src s + BitVec.ofNat 64 (16 * 0) := h.kept.desc
  have hfl : fl s = sl s 0 := by rw [fl_eq]; simp [hc]
  apply WP.of_runBlock
  refine ⟨_, by simp only [gDesc]; xrun [h11, r₇, hd, d₈, v₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hfl, v₈]
  · intro r a; simp [gpr_setReg, a]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- What follows the first slice is short below any threshold of the short path. -/
theorem sub_lt_of_shortLen {t : Nat} (ht : t < 2 ^ 31) (h : shortLen s < t) : L s - fl s < 2 ^ 63 := by
  have := fl_le hp
  unfold shortLen at h; split at h <;> omega

/-- `CF` if the text is shorter than `t`, or its first slice holds all its
whole blocks. -/
theorem splitT3_ok {t : Nat} (ht : t < 2 ^ 31) {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s)
    (h10 : st.gpr .r10 = BitVec.ofNat 64 (fl s)) :
    WP isa (.block [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4,
        .alu .cmp .r10 (.reg .rax), .mov .rax (.mem (at_ .r11 gLen)), .mov32 .r10 (imm 0), .cmov .ae .rax (.reg .r10),
        .alu .cmp .rax (imm t)]) st
      fun st' => st'.cf = some (decide (shortLen s < t)) ∧ (∀ r, r ≠ .rax → r ≠ .r10 → st'.gpr r = st.gpr r) ∧
        st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have r₅ := h.slot hp (d := 40) (by decide)
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hfl := fl_le hp
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  have it := imm_eq ht
  have r16 := round16 hL
  have m₁ : fl s % 18446744073709551616 = fl s := Nat.mod_eq_of_lt (by omega)
  have m₂ : L s % 18446744073709551616 = L s := Nat.mod_eq_of_lt (by omega)
  have m₃ : t % 18446744073709551616 = t := Nat.mod_eq_of_lt (by omega)
  have m₄ : 16 * (L s / 16) % 18446744073709551616 = 16 * (L s / 16) := Nat.mod_eq_of_lt (by omega)
  have l₁ := toNat_ofNat_of_lt (show fl s < 2 ^ 64 by omega)
  have l₂ := toNat_ofNat_of_lt (show 16 * (L s / 16) < 2 ^ 64 by omega)
  have l₃ := toNat_ofNat_of_lt (show t < 2 ^ 64 by omega)
  apply WP.of_runBlock
  by_cases h₁ : 16 * (L s / 16) ≤ fl s
  · have h₁' : ¬fl s < 16 * (L s / 16) := by omega
    refine ⟨_, by simp only [gLen]; xrun [h11, h10, r₅, hlen, it, r16, execCmov, eval, l₁, l₂, l₃, m₁, m₂, m₃, m₄, h₁',
      decide_false, Bool.not_false, Option.map_some], ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (intro r a b; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, m₁, m₂, m₄, h₁, h₁'])
        | (simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
            wr_setReg, wr_setFlags, m₁, m₂, m₄, h₁, h₁']; done)
        | (simp [shortLen, h₁, h₁', BitVec.toNat_ofNat, m₁, m₂, m₃, m₄] <;> omega)
  · have h₁' : fl s < 16 * (L s / 16) := by omega
    refine ⟨_, by simp only [gLen]; xrun [h11, h10, r₅, hlen, it, r16, execCmov, eval, l₁, l₂, l₃, m₁, m₂, m₃, m₄, h₁',
      decide_true, Bool.not_true, Bool.false_eq_true, Option.map_some], ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (intro r a b; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, m₁, m₂, m₄, h₁, h₁'])
        | (simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
            wr_setReg, wr_setFlags, m₁, m₂, m₄, h₁, h₁']; done)
        | (simp [shortLen, h₁, h₁', BitVec.toNat_ofNat, m₁, m₂, m₃, m₄] <;> omega)

/-- After the first block of the test. -/
def G1 (s st : State) : Prop :=
  E2 s st ∧ st.gpr .r11 = W s ∧ st.gpr .r10 = 0 ∧ st.zf = some (decide (Cnt s = 0))

/-- Before the comparison. -/
def G2 (s st : State) : Prop := E2 s st ∧ st.gpr .r11 = W s ∧ st.gpr .r10 = BitVec.ofNat 64 (fl s)

theorem w_splitT1 {st : State} (h : E2 s st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 48)), .mov32 .r10 (imm 0), .mov .rax (.mem (at_ .r11 gLeft)),
      .alu .test .rax (.reg .rax)]) st (G1 s) := by
  obtain ⟨B, di, si, dx, cx⟩ := h
  refine WP.mono (splitT1_ok hp B) fun s₁ ⟨r11₁, r10₁, zf₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have cs₁ : ∀ r ∈ calleeSaved, s₁.gpr r = st.gpr r := fun r hr => g₁ r
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
    (by intro e; subst e; simp [calleeSaved] at hr)
  exact ⟨⟨B.regs m₁ cs₁ rd₁ wr₁, by rw [g₁ _ (by decide) (by decide) (by decide), di],
    by rw [g₁ _ (by decide) (by decide) (by decide), si], by rw [g₁ _ (by decide) (by decide) (by decide), dx],
    by rw [g₁ _ (by decide) (by decide) (by decide), cx]⟩, r11₁, r10₁, zf₁⟩

omit hp in
theorem w_splitT2z (hc : Cnt s = 0) {st : State} (h : G1 s st) : G2 s st :=
  ⟨h.1, h.2.1, by rw [h.2.2.1, fl_eq]; simp [hc]⟩

theorem w_splitT2 (hc : Cnt s ≠ 0) {st : State} (h : G1 s st) :
    WP isa (.block [.mov .r10 (.mem (at_ .r11 gDesc)), .mov .r10 (.mem (at_ .r10 8))]) st (G2 s) := by
  obtain ⟨⟨B, di, si, dx, cx⟩, r11, -, -⟩ := h
  refine WP.mono (splitT2_ok hp hc B r11) fun s₂ ⟨r10₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  have cs₂ : ∀ r ∈ calleeSaved, s₂.gpr r = st.gpr r := fun r hr => g₂ r
    (by intro e; subst e; simp [calleeSaved] at hr)
  exact ⟨⟨B.regs m₂ cs₂ rd₂ wr₂, by rw [g₂ _ (by decide), di], by rw [g₂ _ (by decide), si],
    by rw [g₂ _ (by decide), dx], by rw [g₂ _ (by decide), cx]⟩, by rw [g₂ _ (by decide), r11], r10₂⟩

theorem w_splitT3 {t : Nat} (ht : t < 2 ^ 31) {st : State} (h : G2 s st) :
    WP isa (.block [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4,
        .alu .cmp .r10 (.reg .rax), .mov .rax (.mem (at_ .r11 gLen)), .mov32 .r10 (imm 0), .cmov .ae .rax (.reg .r10),
        .alu .cmp .rax (imm t)]) st
      fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (shortLen s < t)) := by
  obtain ⟨⟨B, di, si, dx, cx⟩, r11, r10⟩ := h
  refine WP.mono (splitT3_ok hp ht B r11 r10) fun s₃ ⟨cf₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = st.gpr r := fun r hr => g₃ r
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
  exact ⟨⟨B.regs m₃ cs₃ rd₃ wr₃, by rw [g₃ _ (by decide) (by decide), di], by rw [g₃ _ (by decide) (by decide), si],
    by rw [g₃ _ (by decide) (by decide), dx], by rw [g₃ _ (by decide) (by decide), cx]⟩,
    by rw [g₃ _ (by decide) (by decide), r11], cf₃⟩

/-- The first slice's length, if there is one. -/
theorem w_splitIte {st : State} (h : G1 s st) :
    WP isa (.ite .e (.block []) (.block [.mov .r10 (.mem (at_ .r11 gDesc)), .mov .r10 (.mem (at_ .r10 8))])) st
      (G2 s) :=
  WP.ite (decide (Cnt s = 0)) (by simp only [eval, h.2.2.2]) (fun e => WP.block_nil (w_splitT2z (by simpa using e) h))
    (fun e => w_splitT2 hp (by simpa using e) h)

/-- The lengths, then `last`. -/
theorem lenTest_wp {last : List Instr} {P : State → Prop} (h₃ : ∀ st, G2 s st → WP isa (.block last) st P)
    {st : State} (h : E2 s st) : WP isa (lenTest last) st P := by
  unfold lenTest
  exact WP.seq (WP.mono (w_splitT1 hp h) fun s₁ G =>
    WP.seq (WP.mono (w_splitIte hp G) fun s₂ G₂ => h₃ s₂ G₂))

/-- `work` in `r11`, and `CF` if the text is shorter than `q`. -/
theorem quickT_ok {q : Nat} (hq : q < 2 ^ 31) {st : State} (h : Base s (AL s) 0 st) :
    WP isa (.block (quickTest q)) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.cf = some (decide (L s < q)) ∧
      (∀ r, r ≠ .rax → r ≠ .r11 → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  have r₅ := h.slot hp (d := 40) (by decide)
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  have it := imm_eq hq
  have m₂ : L s % 18446744073709551616 = L s := Nat.mod_eq_of_lt (by omega)
  have m₃ : q % 18446744073709551616 = q := Nat.mod_eq_of_lt (by omega)
  have l₂ := toNat_ofNat_of_lt hL
  have l₃ := toNat_ofNat_of_lt (show q < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [quickTest, gLen]; xrun [a₅, e₅, r₅, hlen, it], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [BitVec.toNat_ofNat, m₂, m₃, l₂, l₃]
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

theorem w_quick {q : Nat} (hq : q < 2 ^ 31) {st : State} (h : E2 s st) :
    WP isa (.block (quickTest q)) st fun st' =>
      E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (L s < q)) := by
  obtain ⟨B, di, si, dx, cx⟩ := h
  refine WP.mono (quickT_ok hp hq B) fun s₁ ⟨r11₁, cf₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have cs₁ : ∀ r ∈ calleeSaved, s₁.gpr r = st.gpr r := fun r hr => g₁ r
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
  exact ⟨⟨B.regs m₁ cs₁ rd₁ wr₁, by rw [g₁ _ (by decide) (by decide), di], by rw [g₁ _ (by decide) (by decide), si],
    by rw [g₁ _ (by decide) (by decide), dx], by rw [g₁ _ (by decide) (by decide), cx]⟩, r11₁, cf₁⟩

/-- The length alone if the text is shorter than `q`, which decides `b`;
otherwise the lengths, then `last`. -/
theorem lenTestQ_wp {q : Nat} (hq : q < 2 ^ 31) {last : List Instr} {b : Bool} (hb : L s < q → b = true)
    (h₃ : ∀ st, G2 s st → WP isa (.block last) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some b)
    {st : State} (h : E2 s st) :
    WP isa (lenTestQ q last) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some b := by
  unfold lenTestQ
  refine WP.seq (WP.mono (w_quick hp hq h) fun s₁ ⟨E, r11, cf⟩ => ?_)
  refine WP.ite (decide (L s < q)) (by simp only [eval, cf]) (fun e => WP.block_nil ⟨E, r11, ?_⟩)
    (fun _ => lenTest_wp hp h₃ E)
  rw [cf, e, hb (by simpa using e)]

/-- The test of the texts the short path takes. -/
theorem splitTest_wp {t : Nat} (ht : t < 2 ^ 31) {st : State} (h : E2 s st) :
    WP isa (splitTest t) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (shortLen s < t)) :=
  lenTestQ_wp hp ht (fun e => by unfold shortLen; split <;> simp <;> omega) (fun _ G => w_splitT3 hp ht G) h

/-- `CF` unless the first slice holds all the whole blocks and at least `ts`
bytes. -/
theorem selT3_ok {ts : Nat} (hts : ts < 2 ^ 31) {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s)
    (h10 : st.gpr .r10 = BitVec.ofNat 64 (fl s)) :
    WP isa (.block (selLast ts)) st
      fun st' => st'.cf = some (decide (selLen s < ts)) ∧
        (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → st'.gpr r = st.gpr r) ∧
        st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have r₅ := h.slot hp (d := 40) (by decide)
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hfl := fl_le hp
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  have it := imm_eq hts
  have r16 := round16 hL
  have m₁ : fl s % 18446744073709551616 = fl s := Nat.mod_eq_of_lt (by omega)
  have m₃ : ts % 18446744073709551616 = ts := Nat.mod_eq_of_lt (by omega)
  have m₄ : 16 * (L s / 16) % 18446744073709551616 = 16 * (L s / 16) := Nat.mod_eq_of_lt (by omega)
  have l₁ := toNat_ofNat_of_lt (show fl s < 2 ^ 64 by omega)
  have l₂ := toNat_ofNat_of_lt (show 16 * (L s / 16) < 2 ^ 64 by omega)
  have l₃ := toNat_ofNat_of_lt (show ts < 2 ^ 64 by omega)
  apply WP.of_runBlock
  by_cases h₁ : fl s < 16 * (L s / 16)
  · refine ⟨_, by simp only [selLast, gLen]; xrun [h11, h10, r₅, hlen, it, r16, execCmov, eval, l₁, l₂, l₃, m₁, m₃,
      m₄, h₁, decide_true, Option.map_some], ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (intro r a b c; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, c, m₁, m₄, h₁])
        | (simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
            wr_setReg, wr_setFlags, m₁, m₄, h₁]; done)
        | (simp [selLen, h₁, BitVec.toNat_ofNat, m₁, m₃, m₄] <;> omega)
  · refine ⟨_, by simp only [selLast, gLen]; xrun [h11, h10, r₅, hlen, it, r16, execCmov, eval, l₁, l₂, l₃, m₁, m₃,
      m₄, h₁, decide_false, Bool.false_eq_true, Option.map_some], ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (intro r a b c; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, c, m₁, m₄, h₁])
        | (simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
            wr_setReg, wr_setFlags, m₁, m₄, h₁]; done)
        | (simp [selLen, h₁, BitVec.toNat_ofNat, m₁, m₃, m₄] <;> omega)

theorem w_selT3 {ts : Nat} (hts : ts < 2 ^ 31) {st : State} (h : G2 s st) :
    WP isa (.block (selLast ts)) st
      fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (selLen s < ts)) := by
  obtain ⟨⟨B, di, si, dx, cx⟩, r11, r10⟩ := h
  refine WP.mono (selT3_ok hp hts B r11 r10) fun s₃ ⟨cf₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = st.gpr r := fun r hr => g₃ r
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
    (by intro e; subst e; simp [calleeSaved] at hr)
  have g : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r11], s₃.gpr r = st.gpr r := fun r hr => g₃ r
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  exact ⟨⟨B.regs m₃ cs₃ rd₃ wr₃, by rw [g _ (by simp), di], by rw [g _ (by simp), si], by rw [g _ (by simp), dx],
    by rw [g _ (by simp), cx]⟩, by rw [g _ (by simp), r11], cf₃⟩

/-- The choice, on the short path, between copying the text whole and
sealing it from its first slice. -/
theorem selTest_wp {ts : Nat} (hts : ts < 2 ^ 31) {st : State} (h : E2 s st) :
    WP isa (selTest ts) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (selLen s < ts)) :=
  lenTest_wp hp (fun _ G => w_selT3 hp hts G) h

/-- A text on the short path that is not sealed from its first slice is
shorter than the threshold. -/
theorem lt_of_sel {t ts : Nat} (htt : ts + 16 ≤ t) (h₁ : shortLen s < t) (h₂ : selLen s < ts) :
    L s < t := by
  have := fl_le hp
  unfold shortLen at h₁; unfold selLen at h₂
  split at h₁ <;> split at h₂ <;> omega

/-- A text sealed from its first slice has fewer than 16 bytes after it. -/
theorem sub_lt_of_sel {ts : Nat} (hts : 1 ≤ ts) (h : ¬selLen s < ts) : L s - fl s < 2 ^ 63 := by
  have := fl_le hp
  unfold selLen at h; split at h <;> omega

end

/-! ## The nonce and the first slice kept -/

/-- `CBase`, with the first slice's address and length kept in the
streaming state's slots after the nonce. -/
structure PBase (s : State) (st : State) : Prop extends CBase s st where
  first : st.mem.readW (St s + BitVec.ofNat 64 16) 64 = fb s
  firstLen : st.mem.readW (St s + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (fl s)

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The nonce and its length kept, the slices in `r9`, `dst` in `rdi`, the
first descriptor in `r10`, an empty first slice in `rax` and `rcx`, and `ZF`
if there is no slice. -/
theorem splitEntry_ok {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s) (hsi : st.gpr .rsi = Nn s)
    (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (.block splitEntry) st fun st' =>
      st'.gpr .r9 = BitVec.ofNat 64 (Cnt s) ∧ st'.gpr .rdi = Dst s ∧ st'.gpr .r10 = Src s ∧ st'.gpr .rax = Src s ∧
      st'.gpr .rcx = 0 ∧ st'.zf = some (decide (Cnt s = 0)) ∧ st'.gpr .r11 = W s ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ CBase s st' := by
  have hw := hp.w_w
  have r₈ := h.slot hp (d := 64) (by decide)
  have r₄ := h.slot hp (d := 32) (by decide)
  have r₇ := h.slot hp (d := 56) (by decide)
  have hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  have hz := and_self_beq hC
  have w : ∀ d, d + 8 ≤ 184 → InRegions st.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d hd => by
    rw [h.wr]; exact w_in hp (by omega)
  have hleft : st.mem.readW (W s + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 (Cnt s) := by
    rw [h.kept.left, Nat.sub_zero]
  have hdesc : st.mem.readW (W s + BitVec.ofNat 64 56) 64 = Src s := by
    rw [h.kept.desc]; simp
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [splitEntry, gState, gLeft, gDst, gDesc]
    xrun [h11, hsi, hdx, w 104 (by decide), w 112 (by decide), r₈, r₄, r₇, h.kept.dst, hleft, hdesc,
      readW_writeW_off], ?_⟩
  have cs : ∀ d, 104 ≤ d → d + 8 ≤ 184 → (stR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => by
    have e : W s + BitVec.ofNat 64 d = St s + BitVec.ofNat 64 (d - 104) := by
      rw [St, BitVec.add_assoc, ofNat_add_ofNat]; congr 2; omega
    rw [e]; exact Offset.contains_base _ (by omega) (by omega)
  have fS : Frame [stR s] st.mem
      ((st.mem.writeW (W s + BitVec.ofNat 64 104) (Nn s)).writeW (W s + BitVec.ofNat 64 112) (s.gpr .rcx)) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 104 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 112 (by decide) (by decide))
  refine ⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags],
    by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags, imm],
    by simp [gpr_setReg, gpr_arithFlags, imm], by simp only [zf_arithFlags, gpr_setReg, ite_true, hz, reduceCtorEq,
      ↓reduceIte], by simp [gpr_setReg, gpr_arithFlags, h11], fun r hr => ?_,
    ⟨⟨?_, fun r hr => ?_, by simp [rd_arithFlags, rd_setReg, h.rd], by simp [wr_arithFlags, wr_setReg, h.wr], ?_, ?_⟩,
      ?_, ?_⟩⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, h.rsp]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags] <;>
      exact h.saved _ (by decide)
  · simp only [mem_setReg, mem_arithFlags]
    exact h.kept.frame fS fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kpR_stR
  · simp only [mem_setReg, mem_arithFlags]
    exact h.frame.trans (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wkR s, by simp, stR_sub⟩)
  · simp (disch := decide) only [mem_setReg, mem_arithFlags, St, readW_writeW_off, Mem.readW_writeW_self64]
  · simp (disch := decide) only [mem_setReg, mem_arithFlags, St, Offset.add_add, readW_writeW_off,
      Mem.readW_writeW_self64]

/-- What the gathering of the slices after the first needs in registers,
and the first slice in `rax` and `rcx`. -/
def FirstRegs (s st : State) : Prop :=
  st.gpr .rax = fb s ∧ st.gpr .rcx = BitVec.ofNat 64 (fl s) ∧ st.gpr .r9 = BitVec.ofNat 64 (Cnt s - k0 s) ∧
    st.gpr .r10 = Src s + BitVec.ofNat 64 (16 * k0 s) ∧ st.gpr .rdi = Dst s + BitVec.ofNat 64 (fl s) ∧
    st.gpr .r11 = W s

/-- The first slice, and past it. -/
theorem splitFirst_ok (hc : Cnt s ≠ 0) {st : State} (h : Base s (AL s) 0 st)
    (h9 : st.gpr .r9 = BitVec.ofNat 64 (Cnt s)) (hdi : st.gpr .rdi = Dst s) (h10 : st.gpr .r10 = Src s)
    (h11 : st.gpr .r11 = W s) :
    WP isa (.block splitFirst) st fun st' => FirstRegs s st' ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧
      st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  have d₀ := desc_in hp h (i := 0) (by omega) (d := 0) (by decide)
  have d₈ := desc_in hp h (i := 0) (by omega) (d := 8) (by decide)
  have v₀ : st.mem.readW (Src s + BitVec.ofNat 64 (16 * 0) + BitVec.ofNat 64 0) 64 = sb s 0 := by
    simpa using sb_eq hp h.frame (i := 0) (by omega)
  have v₈ := sl_eq hp h.frame (i := 0) (by omega)
  have e0 : Src s + BitVec.ofNat 64 (16 * 0) = Src s := by simp
  rw [e0] at d₀ d₈ v₀ v₈
  have hk : k0 s = 1 := by simp [k0, hc]
  have hfl : fl s = sl s 0 := by rw [fl_eq]; simp [hc]
  have hfb : fb s = sb s 0 := by simp [fb, hc]
  have hsub : BitVec.ofNat 64 (Cnt s) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (Cnt s - 1) :=
    ofNat_sub (by omega) hC
  have i16 := imm_eq (n := 16) (by decide)
  have i1 := imm_eq (n := 1) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [splitFirst, imm]; xrun [h10, d₀, d₈, v₀, v₈, i16, i1], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, hfb]
  · simp [gpr_setReg, gpr_arithFlags, hfl]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h9, hk, imm, i1, ← hsub]
  · simp [gpr_setReg, gpr_arithFlags, h10, hk, imm, i16]
  · simp [gpr_setReg, gpr_arithFlags, hdi, hfl]
  · simp [gpr_setReg, gpr_arithFlags, h11]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The entry of the path, and the first slice if there is one. -/
theorem splitHead_wp {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s) (hsi : st.gpr .rsi = Nn s)
    (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (.seq (.block splitEntry) (.ite .e (.block []) (.block splitFirst))) st fun st' =>
      FirstRegs s st' ∧ CBase s st' := by
  refine WP.seq (WP.mono (splitEntry_ok hp h h11 hsi hdx) fun s₁ ⟨r9, di, r10, ax, cx, zf, r11, cs, C⟩ => ?_)
  refine WP.ite (decide (Cnt s = 0)) (by simp only [eval, zf]) (fun e => ?_) (fun e => ?_)
  · have hc : Cnt s = 0 := by simpa using e
    refine WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, r11⟩, C⟩
    · rw [ax]; simp [fb, hc]
    · rw [cx, fl_eq]; simp [hc]
    · rw [r9]; simp [k0, hc]
    · rw [r10]; simp [k0, hc]
    · rw [di, fl_eq]; simp [hc]
  · have hc : Cnt s ≠ 0 := by simpa using e
    refine WP.mono (splitFirst_ok hp hc C.toBase r9 di r10 r11) fun s₂ ⟨F, cs₂, m₂, rd₂, wr₂⟩ => ⟨F, ?_⟩
    exact ⟨C.toBase.regs m₂ cs₂ rd₂ wr₂, by rw [m₂]; exact C.nonce, by rw [m₂]; exact C.nonceLen⟩

/-- The first slice kept, and the next descriptor in `r11`. -/
theorem splitKeep_ok {st : State} (F : FirstRegs s st) (C : CBase s st) :
    WP isa (.block splitKeep) st fun st' => PBase s st' ∧ st'.gpr .r9 = BitVec.ofNat 64 (Cnt s - k0 s) ∧
      st'.gpr .rdi = Dst s + BitVec.ofNat 64 (fl s) ∧ st'.gpr .r11 = Src s + BitVec.ofNat 64 (16 * k0 s) ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) := by
  obtain ⟨ax, cx, r9, r10, di, r11⟩ := F
  have hw := hp.w_w
  have w : ∀ d, d + 8 ≤ 184 → InRegions st.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d hd => by
    rw [C.wr]; exact w_in hp (by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [splitKeep, gState]; xrun [r11, ax, cx, r10, w 120 (by decide), w 128 (by decide)], ?_⟩
  have cs : ∀ d, 104 ≤ d → d + 8 ≤ 184 → (stR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => by
    have e : W s + BitVec.ofNat 64 d = St s + BitVec.ofNat 64 (d - 104) := by
      rw [St, BitVec.add_assoc, ofNat_add_ofNat]; congr 2; omega
    rw [e]; exact Offset.contains_base _ (by omega) (by omega)
  have fS : Frame [stR s] st.mem
      ((st.mem.writeW (W s + BitVec.ofNat 64 120) (fb s)).writeW (W s + BitVec.ofNat 64 128)
        (BitVec.ofNat 64 (fl s))) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 120 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 128 (by decide) (by decide))
  have eS : ∀ d, St s + BitVec.ofNat 64 d = W s + BitVec.ofNat 64 (104 + d) := fun d => by
    rw [St, BitVec.add_assoc, ofNat_add_ofNat]
  refine ⟨⟨⟨⟨?_, fun r hr => ?_, by simp [rd_setReg, C.rd], by simp [wr_setReg, C.wr], ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩,
    by simp [gpr_setReg, r9], by simp [gpr_setReg, di], by simp [gpr_setReg, r10], fun r hr => ?_⟩
  · simp [gpr_setReg, C.rsp]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg] <;> exact C.saved _ (by decide)
  · simp only [mem_setReg]
    exact C.kept.frame fS fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kpR_stR
  · simp only [mem_setReg]
    exact C.frame.trans (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wkR s, by simp, stR_sub⟩)
  · simp only [mem_setReg]
    rw [show St s = W s + BitVec.ofNat 64 104 from rfl, readW_writeW_off _ (by decide) (by decide) (by decide),
      readW_writeW_off _ (by decide) (by decide) (by decide)]
    exact C.nonce
  · simp only [mem_setReg]
    rw [eS, readW_writeW_off _ (by decide) (by decide) (by decide),
      readW_writeW_off _ (by decide) (by decide) (by decide), ← eS]
    exact C.nonceLen
  · simp only [mem_setReg]
    rw [eS, readW_writeW_off _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_setReg]
    rw [eS, Mem.readW_writeW_self64]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

omit hp in
/-- The descriptors of the slices after the first are descriptors of the text. -/
theorem dsK_sub : Region.Sub ⟨Src s + BitVec.ofNat 64 (16 * k0 s), (Cnt s - k0 s) * 16⟩ (dsR s) := by
  have := k0_le s
  exact Offset.sub_base _ (by rw [Nat.sub_mul]; omega)

/-- The output after the first slice. -/
theorem dK_sub : Region.Sub ⟨Dst s + BitVec.ofNat 64 (fl s), L s - fl s⟩ (dR s) := by
  have := fl_le hp
  exact Offset.sub_base _ (by omega)

/-- The slices after the first, through a frame of the regions written and
the stack. -/
theorem listedK_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) :
    Sig.listed 64 m .u8 (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) =
      Sig.listed 64 s.mem .u8 (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) :=
  Sig.listed_congr 64 .u8 _ _ fun a ha => hf a fun r hr hc => ds_apart hp r hr a
    ((dsK_sub (s := s)) a (by simpa [Sig.descRegion] using ha)) hc

/-- Their bytes, through such a frame. -/
theorem gatheredK_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) :
    gathered 64 m (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) =
      gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) := by
  have e₁ := gathered_k m (Src s) (k0_cases s)
  have e₂ := gathered_k s.mem (Src s) (k0_cases s)
  rw [pt_eq hp hf (Nat.le_refl _)] at e₁
  rw [pt_eq hp hf (k0_le s)] at e₁
  exact List.append_cancel_left (e₁.symm.trans e₂)

/-- What the gathering of the slices after the first needs, after `splitKeep`. -/
theorem splitGatherPre {st : State} (hL : L s - fl s < 2 ^ 63) (h : Base s (AL s) 0 st)
    (h9 : st.gpr .r9 = BitVec.ofNat 64 (Cnt s - k0 s)) (hdi : st.gpr .rdi = Dst s + BitVec.ofNat 64 (fl s))
    (h11 : st.gpr .r11 = Src s + BitVec.ofNat 64 (16 * k0 s)) :
    GatherPre st (Src s + BitVec.ofNat 64 (16 * k0 s)) (Dst s + BitVec.ofNat 64 (fl s)) (Cnt s - k0 s)
      (L s - fl s) := by
  have hl := listedK_eq hp h.frame
  have hk := k0_le s
  have hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  have hL' : L s < 2 ^ 64 := (stackArg s 3).isLt
  have ws := hp.w_ds
  have hfl := fl_le hp
  have hdw : (Src s + BitVec.ofNat 64 (16 * k0 s)).toNat + (Cnt s - k0 s) * 16 ≤ 2 ^ 64 := by
    by_cases hz : Cnt s - k0 s = 0
    · rw [hz]; have := (Src s + BitVec.ofNat 64 (16 * k0 s)).isLt; omega
    · have : (Src s + BitVec.ofNat 64 (16 * k0 s)).toNat = (Src s).toNat + 16 * k0 s := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k0 s) (by omega),
          Nat.mod_eq_of_lt (by omega)]
      rw [this, Nat.sub_mul]; omega
  have cD : Covers [dsR s] (st.rd ++ st.wr) := by
    rw [h.rd, h.wr]; exact covers_left' (covers_of_mem (by rw [hp.rd]; simp))
  have cO : Covers [dR s] st.wr := by rw [h.wr, hp.wr]; exact covers_of_mem (by simp)
  refine ⟨h11, h9, hdi, by omega, hdw, hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gatheredLen, hl, ← gatheredLen, ← hp.glen]
    have := (pt_split s).2
    simp only [gl] at this ⊢
    omega
  · refine Covers.trans (Covers.of_sub fun r hr => ?_) cD
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dsR s, List.mem_singleton_self _, 16 * k0 s, rfl, by simp only [dsR]; rw [Nat.sub_mul]; omega⟩
  · rw [hl]
    intro r hr
    rw [h.rd, h.wr]
    exact covers_left' (covers_of_mem (by rw [hp.rd]; simp [listed_k0 s r hr]))
  · exact covers_off cO (by omega) (by omega)
  · exact (hp.ds_d.sub_left ((dsK_sub (s := s)))).sub_right (dK_sub hp)
  · rw [hl]; exact fun r hr => (hp.ls r (listed_k0 s r hr)).1.sub_right (dK_sub hp)

/-- `PBase`, with the slices after the first gathered in the output after it. -/
structure SPBase (s : State) (st : State) : Prop extends PBase s st where
  out : bytesAt st.mem (Dst s + BitVec.ofNat 64 (fl s)) (L s - fl s) =
    gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s)

/-- After the gathering: the slices after the first in the output after it,
and the rest as it was. -/
theorem split_after {st st' : State} (h : PBase s st)
    (hm : st'.mem = WriteBytes.writeBytes st.mem (Dst s + BitVec.ofNat 64 (fl s))
      (gathered 64 st.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s))) (hk : GKeeps st st') :
    SPBase s st' := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hg := gatheredK_eq hp h.frame
  have hlen : (gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s)).length = L s - fl s := by
    rw [Proof.Gcm.length_gathered]
    have := (pt_split s).2
    have := hp.glen
    simp only [gl] at *
    omega
  rw [hg] at hm
  have fD : Frame [⟨Dst s + BitVec.ofNat 64 (fl s), L s - fl s⟩] st.mem st'.mem := frame_of hm (by rw [hlen])
  have ns : ∀ r ∉ gatherRegs, st'.gpr r = st.gpr r := hk.gpr
  have sd : (stR s).Disjoint ⟨Dst s + BitVec.ofNat 64 (fl s), L s - fl s⟩ :=
    (hp.d_w.symm.sub_left stR_sub).sub_right (dK_sub hp)
  have hcs : ∀ r ∈ calleeSaved, r ∉ gatherRegs := by decide
  have dS : ∀ d, d + 8 ≤ 80 → (stR s).Contains (St s + BitVec.ofNat 64 d) (64 / 8) := fun d hd =>
    Offset.contains_base (St s) (d := d) (n := 8) (k := 80) hd (by omega)
  have dS1 : ∀ r ∈ [(⟨Dst s + BitVec.ofNat 64 (fl s), L s - fl s⟩ : Region)], (stR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sd
  have rS : ∀ d, d + 8 ≤ 80 → st'.mem.readW (St s + BitVec.ofNat 64 d) 64 = st.mem.readW (St s + BitVec.ofNat 64 d) 64 :=
    fun d hd => fD.readW (dS d hd) dS1 (by decide)
  have e0 : St s + BitVec.ofNat 64 0 = St s := BitVec.add_zero _
  refine ⟨⟨⟨⟨by rw [ns .rsp (by decide), h.rsp], fun r hr => by rw [ns r (hcs r hr), h.saved r hr],
    hk.rd.trans h.rd, hk.wr.trans h.wr, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact h.kept.frame fD fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hp.d_w.symm.sub_left kpR_sub).sub_right (dK_sub hp)
  · exact h.frame.trans (fD.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, dK_sub hp⟩)
  · have := rS 0 (by decide); rw [e0] at this; rw [this]; exact h.nonce
  · rw [rS 8 (by decide)]; exact h.nonceLen
  · rw [rS 16 (by decide)]; exact h.first
  · rw [rS 24 (by decide)]; exact h.firstLen
  · rw [hm, ← hlen]; exact bytesAt_writeBytes_self _ _ _ (by omega)

/-- The arguments of `vg_aes_gcm_seal_split(ctx, rounds, nonce, nonce_len,
aad, aad_len, src, src_len, dst, len, tag)` but `ctx` and `rounds`, with
`tag`, `len`, `dst`, `src_len` and `src` to push. -/
theorem splitArgs_ok {st : State} (h : SPBase s st) :
    WP isa (.block splitArgs) st fun st' =>
      st'.gpr .rdx = Nn s ∧ st'.gpr .rcx = s.gpr .rcx ∧ st'.gpr .r8 = Ad s ∧ st'.gpr .r9 = AL s ∧
      st'.gpr .rax = Tg s ∧ st'.gpr .r10 = stackArg s 3 ∧ st'.gpr .rdi = BitVec.ofNat 64 (fl s) ∧
      st'.gpr .rsi = fb s ∧ st'.gpr .r11 = Dst s ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧
      st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have B := h.toBase
  obtain ⟨a₅, e₅⟩ := B.w hp
  have r₂ := B.slot hp (d := 16) (by decide)
  have r₃ := B.slot hp (d := 24) (by decide)
  have r₄ := B.slot hp (d := 32) (by decide)
  have r₅ := B.slot hp (d := 40) (by decide)
  have r₆ := B.slot hp (d := 48) (by decide)
  have r₁₃ := B.slot hp (d := 104) (by decide)
  have r₁₄ := B.slot hp (d := 112) (by decide)
  have r₁₅ := B.slot hp (d := 120) (by decide)
  have r₁₆ := B.slot hp (d := 128) (by decide)
  have n₀ : st.mem.readW (W s + BitVec.ofNat 64 104) 64 = Nn s := h.nonce
  have n₁ : st.mem.readW (W s + BitVec.ofNat 64 112) 64 = s.gpr .rcx := by
    rw [← h.nonceLen, St, Offset.add_add]
  have n₂ : st.mem.readW (W s + BitVec.ofNat 64 120) 64 = fb s := by
    rw [← h.first, St, Offset.add_add]
  have n₃ : st.mem.readW (W s + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 (fl s) := by
    rw [← h.firstLen, St, Offset.add_add]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [splitArgs, gState, gAad, gAlen, gTag, gLen, gDst]
    xrun [a₅, e₅, r₂, r₃, r₄, r₅, r₆, r₁₃, r₁₄, r₁₅, r₁₆, n₀, n₁, n₂, n₃, B.kept.aad,
      B.kept.alen, B.kept.tag, B.kept.len, B.kept.dst], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

end

end VG.Proof.AesGcm.X86_64.Gather
