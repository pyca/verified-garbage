module

import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LastSel
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplit
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# ChaCha20 keystream XOR with the data's first bytes from another buffer on x86-64 with AVX-512: the function

The entry (`C`, the copy of the bytes of `src` from `C` on to `dst`, and the
loop's registers), the last bytes after the loop (by a call of
`vg_chacha20_xor_avx512` in place when fewer than 513 are left, as `C` is
then at most where they start, `tailCall_ok`; else by `last16Sel_ok`), and
the postcondition.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Split

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (add_ofNat)
open VG.WriteBytes (writeBytes writeBytes_frame)
open VG.Proof.AesGcm.X86_64.Short (CopyPre)

/-! ## `C` -/

/-- `C`: `src_len` rounded down to a multiple of 64, and, if fewer than 513
bytes follow the whole 1024-byte passes, at most `len` rounded down to a
multiple of 1024. -/
def Cof (s₀ : State) : Nat :=
  if sL s₀ - 1024 * (sL s₀ / 1024) < 513 then min (64 * (sS s₀ / 64)) (1024 * (sL s₀ / 1024))
  else 64 * (sS s₀ / 64)

theorem Cof_ok {s₀ : State} (hp : APre s₀) : COk s₀ (Cof s₀) := by
  have := hp.le
  unfold Cof; constructor <;> split <;> omega_arith

theorem shr_shl10 (r : Nat) (hr : r < 2 ^ 64) :
    BitVec.ofNat 64 r >>> 10 <<< 10 = BitVec.ofNat 64 (1024 * (r / 1024)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hr]
  omega_arith

theorem entryA_ok (s₀ : State) :
    WP isa (.block [.mov .rax (.reg .r8), .shift .shr .rax 10, .shift .shl .rax 10,
      .mov .r10 (.reg .rdx), .shift .shr .r10 6, .shift .shl .r10 6,
      .mov .r11 (.reg .r8), .alu .sub .r11 (.reg .rax), .alu .cmp .r11 (.imm 513)]) s₀ fun s =>
      s.gpr .rax = BitVec.ofNat 64 (1024 * (sL s₀ / 1024)) ∧
      s.gpr .r10 = BitVec.ofNat 64 (64 * (sS s₀ / 64)) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r) ∧
      s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      s.cf = some (decide (sL s₀ - 1024 * (sL s₀ / 1024) < 513)) := by
  have hL := sL_lt s₀
  have hS := sS_lt s₀
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift, arithFlags,
    State.setReg, State.setFlags, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
    reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self]
  have e8 : s₀.gpr .r8 = BitVec.ofNat 64 (sL s₀) := by simp [sL]
  have e2 : s₀.gpr .rdx = BitVec.ofNat 64 (sS s₀) := by simp [sS]
  have se : BitVec.signExtend 64 (513 : BitVec 32) = 513 := by decide
  rw [e8, e2, shr_shl10 _ hL, Avx512Last.shr_shl _ hS, se]
  refine ⟨rfl, rfl, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial, trivial, trivial, ?_⟩
  have e : (BitVec.ofNat 64 (sL s₀) - BitVec.ofNat 64 (1024 * (sL s₀ / 1024))).toNat =
      sL s₀ - 1024 * (sL s₀ / 1024) := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt hL,
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith), BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL,
      Nat.mod_eq_of_lt (by omega_arith)]
  rw [e]; rfl

theorem entryC_ok (s₀ : State) :
    WP isa entryC s₀ fun s => s.gpr .r10 = BitVec.ofNat 64 (Cof s₀) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r) ∧
      s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hL := sL_lt s₀
  have hS := sS_lt s₀
  refine WP.seq (WP.mono (entryA_ok s₀) fun s₁ ⟨rax₁, r10₁, g₁, m₁, rd₁, wr₁, c₁⟩ => ?_)
  refine WP.ite (decide (sL s₀ - 1024 * (sL s₀ / 1024) < 513)) (by simp [eval, c₁]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execCmov, eval, arithFlags,
      State.setReg, State.setFlags, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
      rax₁, r10₁]
    have ea : (BitVec.ofNat 64 (64 * (sS s₀ / 64))).toNat = 64 * (sS s₀ / 64) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    have eb : (BitVec.ofNat 64 (1024 * (sL s₀ / 1024))).toNat = 1024 * (sL s₀ / 1024) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    simp only [ea, eb]
    by_cases hab : 64 * (sS s₀ / 64) < 1024 * (sL s₀ / 1024)
    · simp only [hab, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, fun r h1 h2 h3 => g₁ r h1 h2 h3, m₁, rd₁, wr₁⟩
      rw [r10₁]; simp only [Cof, hb, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt hab)]
    · simp only [hab, decide_false, Bool.not_false, ↓reduceIte]
      refine ⟨?_, fun r h1 h2 h3 => by simp only [h2, ↓reduceIte]; exact g₁ r h1 h2 h3, m₁, rd₁, wr₁⟩
      simp only [Cof, hb, ↓reduceIte, Nat.min_eq_right (by omega_arith : 1024 * (sL s₀ / 1024) ≤ 64 * (sS s₀ / 64))]
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (M := isa) ⟨by rw [r10₁]; simp only [Cof, hb, ↓reduceIte], g₁, m₁, rd₁, wr₁⟩

theorem Cof_gap {s₀ : State} (hp : APre s₀) : sS s₀ - Cof s₀ < 1024 := by
  have := hp.le
  unfold Cof; split <;> omega_arith

theorem Cof_le {s₀ : State} (h : sL s₀ - 1024 * (sL s₀ / 1024) < 513) :
    Cof s₀ ≤ 1024 * (sL s₀ / 1024) := by
  unfold Cof; rw [ite_eq_left h]; omega_arith

/-! ## The copy -/

theorem bytesAt_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem copyArgs_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : C ≤ sS s₀) {s : State}
    (hg : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r) (hr10 : s.gpr .r10 = BitVec.ofNat 64 C)
    (hwr : s.wr = s₀.wr) :
    WP isa (.block copyArgs) s fun s' =>
      s'.gpr .r11 = sst s₀ ∧ s'.gpr .rdi = sdp s₀ + BitVec.ofNat 64 C ∧
      s'.gpr .rsi = ssp s₀ + BitVec.ofNat 64 C ∧ s'.gpr .rcx = BitVec.ofNat 64 (sS s₀ - C) ∧
      s'.gpr .rdx = BitVec.ofNat 64 C ∧ s'.gpr .r9 = sbp s₀ ∧ s'.gpr .rbx = s₀.gpr .r8 ∧
      (∀ r ∈ calleeSaved, r ≠ .rbx → s'.gpr r = s₀.gpr r) ∧
      s'.mem = s.mem.writeW (sbp s₀) (s₀.gpr .rbx) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hS := sS_lt s₀
  have hea : s.ea (at_ .r9 0) = sbp s₀ := by
    simp only [State.ea, at_, hg .r9 (by decide) (by decide) (by decide)]
    rw [show BitVec.ofInt 64 ((0 : Nat) : Int) = 0#64 by decide, BitVec.add_zero]
  have hin : InRegions s.wr (s.ea (at_ .r9 0)) 8 := by
    rw [hea, hwr, hp.wr]; exact ⟨bufR s₀, by simp, by simp [Region.Contains]⟩
  apply WP.of_runBlock
  simp only [copyArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.store64, hin, ite_true, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
    State.setReg, State.setFlags]
  simp only [reduceCtorEq, ↓reduceIte, hea]
  have g : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r := hg
  rw [g .rdi (by decide) (by decide) (by decide), g .rcx (by decide) (by decide) (by decide),
    g .rsi (by decide) (by decide) (by decide), g .rdx (by decide) (by decide) (by decide),
    g .r9 (by decide) (by decide) (by decide), g .r8 (by decide) (by decide) (by decide),
    g .rbx (by decide) (by decide) (by decide), hr10]
  have e2 : s₀.gpr .rdx = BitVec.ofNat 64 (sS s₀) := by simp [sS]
  refine ⟨rfl, rfl, rfl, by rw [e2]; bv_omega, rfl, rfl, rfl, fun r hr hb => ?_, rfl, trivial, trivial⟩
  obtain ⟨a, b, c, d, e⟩ := calleeSaved_ne hr
  have f : r ≠ .rcx ∧ r ≠ .rdi ∧ r ≠ .r11 := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [b, c, f.1, f.2.1, f.2.2, hb]
  exact g r a e f.2.2

theorem loopArgs_ok {s₀ : State} (hp : APre s₀) {C : Nat} {s : State}
    (hr11 : s.gpr .r11 = sst s₀) (hrdi : s.gpr .rdi = sdp s₀ + BitVec.ofNat 64 C)
    (hrsi : s.gpr .rsi = ssp s₀ + BitVec.ofNat 64 C) (hrdx : s.gpr .rdx = BitVec.ofNat 64 C)
    (hr9 : s.gpr .r9 = sbp s₀) (hrbx : s.gpr .rbx = s₀.gpr .r8)
    (hsave : s.mem.readW (sbp s₀) 64 = s₀.gpr .rbx) (hwr : s.wr = s₀.wr) :
    WP isa (.block loopArgs) s fun s' =>
      s'.gpr .rdi = sst s₀ ∧ s'.gpr .rsi = sdp s₀ ∧ s'.gpr .rdx = s₀.gpr .r8 ∧ s'.gpr .rcx = sbp s₀ ∧
      s'.gpr .r8 = ssp s₀ ∧ s'.gpr .r10 = BitVec.ofNat 64 C ∧ s'.gpr .r9 = sbp s₀ ∧
      s'.gpr .rbx = s₀.gpr .rbx ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → r ≠ .rbx →
        s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hea : s.ea (at_ .r9 0) = sbp s₀ := by
    simp only [State.ea, at_, hr9]
    rw [show BitVec.ofInt 64 ((0 : Nat) : Int) = 0#64 by decide, BitVec.add_zero]
  have hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .r9 0)) 8 := by
    rw [hea, hwr, hp.wr]; exact ⟨bufR s₀, by simp, by simp [Region.Contains]⟩
  apply WP.of_runBlock
  simp only [loopArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.load64, hin, ite_true, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
    State.setReg, State.setFlags]
  simp only [reduceCtorEq, ↓reduceIte, hea, hsave]
  rw [hr11, hrdi, hrsi, hrdx, hr9, hrbx]
  and_intros
  all_goals first
    | trivial | rfl | exact BitVec.add_sub_cancel _ _
    | (intro r h1 h2 h3 h4 h5 h6 h7 h8; simp only [h1, h2, h3, h4, h5, h6, h7, h8, ite_false])

/-! ## The postcondition -/

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

theorem bytesAt_getElem (m : Mem) (p : Addr) (n i : Nat) (h : i < (bytesAt m p n).length) :
    (bytesAt m p n)[i] = m (p + BitVec.ofNat 64 i) := by simp [bytesAt]

theorem bytes_vmem {s₀ : State} (hp : APre s₀) :
    bytesAt (vmem s₀) (sdp s₀) (sL s₀) =
      bytesAt s₀.mem (ssp s₀) (sS s₀) ++ (bytesAt s₀.mem (sdp s₀) (sL s₀)).drop (sS s₀) := by
  have hSL := hp.le
  apply List.ext_getElem
  · simp only [bytesAt_length, List.length_append, List.length_drop]; omega_arith
  · intro i h₁ h₂
    have hi : i < sL s₀ := by rwa [bytesAt_length] at h₁
    rw [bytesAt_getElem, vmem_dst s₀ hi, List.getElem_append]
    unfold I
    by_cases hs : i < sS s₀
    · rw [ite_eq_left hs, dite_eq_left (by rw [bytesAt_length]; exact hs), bytesAt_getElem]
    · rw [ite_eq_right hs, dite_eq_right (by rw [bytesAt_length]; exact hs), List.getElem_drop, bytesAt_getElem,
        bytesAt_length, Nat.add_sub_cancel' (by omega_arith)]

theorem post_of_V {s₀ : State} (hp : APre s₀) {s' : State}
    (h : gprPreserved (V s₀) s' ∧ Avx2.xorAvx2X86_64.post (V s₀) s') :
    gprPreserved s₀ s' ∧ xorSplitX86_64.post s₀ s' := by
  obtain ⟨⟨hk, hr⟩, hpost⟩ := h
  refine ⟨⟨fun r hr' => (hk r hr').trans (V_keep s₀ hr'), ?_⟩, ?_⟩
  · rw [V_rsp, V_mem] at hr
    rw [hr]
    exact ((vmem_frame s₀).readW (r := sret s₀) (a := s₀.gpr .rsp) (w := 64) (Region.contains_self _ _)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_d) (by decide)).symm
  · simp only [Avx2.xorAvx2X86_64, xorX86_64, V_rsi, V_rdx, V_rdi, V_mem] at hpost
    simp only [xorSplitX86_64]
    have e : stateAt (vmem s₀) (sst s₀) = stateAt s₀.mem (sst s₀) := V_S0 hp
    rw [hpost, bytes_vmem hp, e]

/-! ## The prologue -/

/-- The bytes of `dst` from `C` on after the copy: the input's. -/
theorem copied_byte {s₀ : State} (hp : APre s₀) {C : Nat} (hC : C ≤ sS s₀) {m : Mem}
    (hm : ∀ k < sS s₀, m (ssp s₀ + BitVec.ofNat 64 k) = s₀.mem (ssp s₀ + BitVec.ofNat 64 k))
    (hd : ∀ k < sL s₀, sS s₀ ≤ k → m (sdp s₀ + BitVec.ofNat 64 k) = s₀.mem (sdp s₀ + BitVec.ofNat 64 k))
    {k : Nat} (hk : k < sL s₀) (hck : C ≤ k) :
    writeBytes m (sdp s₀ + BitVec.ofNat 64 C) (bytesAt m (ssp s₀ + BitVec.ofNat 64 C) (sS s₀ - C))
      (sdp s₀ + BitVec.ofNat 64 k) = I s₀ k := by
  have hL := sL_lt s₀
  have hw := hp.wrap_d
  have e : (sdp s₀ + BitVec.ofNat 64 k - (sdp s₀ + BitVec.ofNat 64 C)).toNat = k - C := by
    rw [show sdp s₀ + BitVec.ofNat 64 k - (sdp s₀ + BitVec.ofNat 64 C) = BitVec.ofNat 64 (k - C) by
      bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  simp only [writeBytes, e, bytesAt_length]
  unfold I
  by_cases hs : k < sS s₀
  · rw [ite_eq_left (by omega_arith), ite_eq_left hs, bytesAt_getD' _ _ (by omega_arith), add_ofNat,
      Nat.add_sub_cancel' hck, hm k hs]
  · rw [ite_eq_right (by omega_arith), ite_eq_right hs, hd k hk (by omega_arith)]

theorem prologue_ok {s₀ : State} (hp : APre s₀) {Q : State → Prop} {rest : Prog isa}
    (hk : ∀ s, SInv s₀ (Cof s₀) 0 s → s.cf = some (decide (sL s₀ < 1024)) → WP isa rest s Q) :
    WP isa (.seq entryC (.seq (.block copyArgs) (.seq (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes .z64)
      (.seq (.block (loopArgs ++ Impl.ChaCha20.X86_64.Avx512Tail.consts ++ consts ++
        ([.alu .cmp .rdx (.imm 1024)] : List Instr))) rest)))) s₀ Q := by
  have hL := sL_lt s₀
  have hS := sS_lt s₀
  have hSL := hp.le
  have hCo := Cof_ok hp
  have hgap := Cof_gap hp
  have hws := hp.wrap_s
  have hwd := hp.wrap_d
  generalize hCd : Cof s₀ = C at hCo hgap hk
  have hCS := hCo.le
  refine WP.seq (WP.mono (entryC_ok s₀) fun s₁ ⟨r10₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hCd] at r10₁
  refine WP.seq (WP.mono (copyArgs_ok hp hCS g₁ r10₁ wr₁)
    fun s₂ ⟨r11₂, rdi₂, rsi₂, rcx₂, rdx₂, r9₂, rbx₂, keep₂, m₂, rd₂, wr₂⟩ => ?_)
  have cp : CopyPre s₂ (ssp s₀ + BitVec.ofNat 64 C) (sdp s₀ + BitVec.ofNat 64 C) (sS s₀ - C) :=
    ⟨rsi₂, rdi₂, rcx₂, by omega_arith,
      by rw [rd₂, rd₁, hp.rd]
         exact Covers.left (Covers.of_sub fun r hr => by
           simp only [List.mem_singleton] at hr; subst hr
           exact ⟨srR s₀, by simp, C, rfl, by simp only; omega_arith⟩),
      by rw [wr₂, wr₁, hp.wr]
         exact Covers.of_sub fun r hr => by
           simp only [List.mem_singleton] at hr; subst hr
           exact ⟨sdR s₀, by simp, C, rfl, by simp only; omega_arith⟩,
      (hp.s_d.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))⟩
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.X86_64.Gather.copyBytes_ok cp .z64) fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_)
  replace m₃ : s₃.mem = writeBytes s₂.mem (sdp s₀ + BitVec.ofNat 64 C)
      (bytesAt s₂.mem (ssp s₀ + BitVec.ofNat 64 C) (sS s₀ - C)) := m₃
  have gk₃ : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s₃.gpr r = s₂.gpr r := g₃
  -- The memory so far.
  have FW : Frame [⟨sdp s₀ + BitVec.ofNat 64 C, sS s₀ - C⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have FB : Frame [bufR s₀] s₀.mem s₂.mem := by
    rw [m₂, m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simp [Region.Contains])
  have dsub : Region.Sub ⟨sdp s₀ + BitVec.ofNat 64 C, sS s₀ - C⟩ (sdR s₀) := Offset.sub_base _ (by omega_arith)
  have F₃ : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem s₃.mem :=
    (FB.mono (by simp)).trans (FW.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨sdR s₀, by simp, dsub⟩)
  have hlen : s₃.mem.readW (sbp s₀) 64 = s₀.gpr .rbx := by
    rw [FW.readW (r := ⟨sbp s₀, 8⟩) (Region.contains_self _ _) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact (hp.d_b.symm.sub_left (Region.sub_prefix (by omega_arith))).sub_right dsub) (by decide), m₂,
      Mem.readW_writeW_self64]
  rw [Avx512.tconsts_eq, Avx512.consts_eq]
  refine WP.seq (WP.block_append (WP.block_append (WP.block_append (WP.mono (loopArgs_ok hp (C := C)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact r11₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact rdi₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact rsi₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact rdx₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact r9₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact rbx₂) hlen (wr₃.trans (wr₂.trans wr₁)))
    fun s₄ ⟨rdi₄, rsi₄, rdx₄, rcx₄, r8₄, r10₄, r9₄, rbx₄, g₄, m₄, rd₄, wr₄⟩ =>
      WP.mono (Avx2.pairs_ok Avx512.tPairs Avx512.tPairs_le (buf := sbp s₀) (s := s₄) rcx₄
        (by rw [wr₄, wr₃, wr₂, wr₁, hp.wr]; simp))
      fun s₅ ⟨m₅, g₅, rd₅, wr₅⟩ =>
        WP.mono (Avx2.pairs_ok Avx512.incPairs Avx512.incPairs_le (buf := sbp s₀) (s := s₅)
          (by rw [g₅ _ (by decide)]; exact rcx₄) (by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hp.wr]; simp))
        fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => WP.mono (Avx512.cmp_ok s₆) fun s₇ ⟨g₇, m₇, rd₇, wr₇, cf₇⟩ => ?_))))
  have gp : ∀ r, r ≠ .rax → s₇.gpr r = s₄.gpr r := fun r h => by rw [g₇, g₆ r h, g₅ r h]
  have mm : s₇.mem = Avx2.storeAll (sbp s₀) Avx512.incPairs (Avx2.storeAll (sbp s₀) Avx512.tPairs s₃.mem) := by
    rw [m₇, m₆, m₅, m₄]
  have FS : Frame [bufR s₀] s₃.mem s₇.mem := by
    rw [mm]
    exact (Avx2.storeAll_frame (List.mem_singleton_self _) _ Avx512.tPairs_le _).trans
      (Avx2.storeAll_frame (List.mem_singleton_self _) _ Avx512.incPairs_le _)
  have Fx : Frame [sdR s₀, bufR s₀] s₀.mem s₇.mem :=
    ((FB.mono (by simp)).trans (FW.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨sdR s₀, by simp, dsub⟩)).trans (FS.mono (by simp))
  have nb : ∀ k < sL s₀, ¬ (bufR s₀).Contains (sdp s₀ + BitVec.ofNat 64 k) 1 := fun k hk hc =>
    hp.d_b _ (Avx2.in_dR (s₀ := V s₀) hk) hc
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 (1024 * 0) = a := fun a => by
    rw [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  refine hk s₇ ⟨by rw [gp _ (by decide)]; exact rdi₄, by rw [gp _ (by decide)]; exact rcx₄,
    by rw [gp _ (by decide), rsi₄, e0], by rw [gp _ (by decide), rdx₄, Nat.mul_zero, Nat.sub_zero]; simp [sL],
    by rw [gp _ (by decide), r8₄, e0], by rw [gp _ (by decide), r10₄, Nat.mul_zero, Nat.sub_zero], by omega_arith,
    fun r hr => ?_, by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁], ?_,
    fun k hk => absurd hk (by omega_arith), fun k hk _ hck => ?_, by rw [mm]; exact Avx512.incs_mem _ _,
    by rw [mm]; exact Avx512.tincs_mem _ _, (Fx.mono (by simp))⟩ ?_
  · by_cases hb : r = .rbx
    · subst hb; rw [gp _ (by decide)]; exact rbx₄
    obtain ⟨a, b, c, d, e⟩ := calleeSaved_ne hr
    have f : r ≠ .rcx ∧ r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gp r a, g₄ r a f.2 b c f.1 d e hb, gk₃ r a d e]
    exact keep₂ r hr hb
  · rw [Nat.mul_zero, ctr_zero]
    exact Xor.stateAt_frame Fx (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.st_d
      · exact hp.st_b)
  · rw [FS _ (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact nb k hk), m₃]
    exact copied_byte hp hCS (fun k hk => by
        rw [m₂, m₁]
        exact (Frame.refl [bufR s₀] _).writeW (List.mem_singleton_self _) _ (by simp [Region.Contains]) _
          (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
              exact fun hc => hp.s_b _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc))
      (fun k hk _ => by
        rw [m₂, m₁]
        exact (Frame.refl [bufR s₀] _).writeW (List.mem_singleton_self _) _ (by simp [Region.Contains]) _
          (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact nb k hk))
      hk hck
  · rw [cf₇, g₆ .rdx (by decide), g₅ .rdx (by decide), rdx₄]

/-! ## The last bytes -/

theorem SInv.of_eq {s₀ : State} {C t : Nat} {s s' : State} (h : SInv s₀ C t s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SInv s₀ C t s' :=
  ⟨by rw [hg]; exact h.rdi, by rw [hg]; exact h.rcx, by rw [hg]; exact h.rsi, by rw [hg]; exact h.rdx,
    by rw [hg]; exact h.r8, by rw [hg]; exact h.r10, h.le, fun r hr => by rw [hg]; exact h.keep r hr,
    hrd.trans h.rd, hwr.trans h.wr, by rw [hm]; exact h.cnt, fun k hk => by rw [hm]; exact h.done k hk,
    fun k hk h₁ h₂ => by rw [hm]; exact h.todo k hk h₁ h₂, by rw [hm]; exact h.incs, by rw [hm]; exact h.tincs,
    by rw [hm]; exact h.frame⟩

/-! ## Fewer than 513 bytes left: the call -/

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by lit_omega) (by lit_omega))

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A call of the implementation `v` of `vg_chacha20_xor`, with 24 bytes of stack below `rsp`:
8 for its return address, 16 for its calls. -/
theorem xor_call (v : XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hd := v.depth_le
  have h8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) := below_sub (by lit_omega) (by lit_omega)
  have hk := v.stack_le
  have hk' : Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack, v.stack⟩ (below (s.gpr .rsp) 24) := by
    rw [show s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack = s.gpr .rsp - BitVec.ofNat 64 (8 + v.stack) by
      rw [BitVec.sub_sub, BitVec.ofNat_add]; rfl]
    exact Offset.sub_below _ (by lit_omega) (by lit_omega)
  have hpre : (xorStack v.stack).pre (s.callEntry.withRegions [] [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) := by
    simp only [xorStack, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hsS.sub_left h8, hsD.sub_left h8, hsB.sub_left h8,
      hsS.sub_left hk', hsD.sub_left hk', hsB.sub_left hk', hwrap⟩
  refine WP.call (k := xorStack v.stack) v.ok v.nosp (by lit_omega) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost, _⟩
  have hf' : Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem := by
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (s.gpr .rsp) 24, by simp, below_sub (by lit_omega) (by lit_omega)⟩
  refine hQ s' hrd hwr hcs hf' ?_
  simp only [xorX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
  rw [hpost, bytesAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsD.sub_left h8).symm) (by lit_omega),
    Xor.stateAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsS.sub_left h8).symm)]

/-- The output, pointwise the input XORed with `ks`. -/
theorem bytesAt_xor {m m' : Mem} {D : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : ∀ k < n, m' (D + BitVec.ofNat 64 k) = m (D + BitVec.ofNat 64 k) ^^^ ks.getD k 0) :
    bytesAt m' D n = List.zipWith (· ^^^ ·) (bytesAt m D n) ks := by
  apply List.ext_getElem
  · simp [bytesAt, hks]
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [h k h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_arith), Option.getD_some]

theorem ret_stk24 (s₀ : State) : (sret s₀).Disjoint (sstk s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 24) (d := 24) (n := 8) (k := 24) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem tailCall_ok {s₀ : State} (hp : APre s₀) {C t : Nat} (hC : C ≤ 1024 * t) (ht : sL s₀ - 1024 * t < 1024)
    {s : State} (h : SInv s₀ C t s) :
    WP isa (.call "vg_chacha20_xor_avx512" xor) s fun s' => gprPreserved s₀ s' ∧ xorSplitX86_64.post s₀ s' := by
  have hL := sL_lt s₀
  have hle := h.le
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.keep .rsp (by simp [calleeSaved])
  have hw' : 1024 * t + (sL s₀ - 1024 * t) ≤ sL s₀ := by omega_arith
  have sD : Region.Sub ⟨sdp s₀ + BitVec.ofNat 64 (1024 * t), sL s₀ - 1024 * t⟩ (sdR s₀) :=
    Offset.sub_base _ hw'
  show WP isa (.call XorImpl.avx512.callee.name XorImpl.avx512.callee.code) s _
  refine xor_call XorImpl.avx512 h.rdi h.rsi h.rdx h.rcx (by omega_arith) (hp.st_d.sub_right sD) hp.st_b (hp.d_b.sub_left sD)
    (by have := hp.wrap_d; bv_omega) (by rw [hsp]; exact hp.stk_st) (by rw [hsp]; exact hp.stk_d.sub_right sD)
    (by rw [hsp]; exact hp.stk_b)
    (by
      rw [h.rd, h.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega_arith⟩
      · exact ⟨sdR s₀, by simp, 1024 * t, rfl, hw'⟩
      · exact ⟨bufR s₀, by simp, 0, by simp, show 0 + 320 ≤ 320 by omega_arith⟩)
    (by
      rw [h.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega_arith⟩
      · exact ⟨sdR s₀, by simp, 1024 * t, rfl, hw'⟩
      · exact ⟨bufR s₀, by simp, 0, by simp, show 0 + 320 ≤ 320 by omega_arith⟩)
    fun s' _ _ hcs hf hpost => ?_
  rw [hsp] at hf
  refine post_of_V hp ⟨⟨fun r hr => by rw [hcs r hr, h.keep r hr, V_keep s₀ hr], ?_⟩, ?_⟩
  · show s'.mem.readW (s₀.gpr .rsp) 64 = (vmem s₀).readW (s₀.gpr .rsp) 64
    refine (hf.readW (r := sret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_d.sub_right sD
      · exact hp.ret_b
      · exact ret_stk24 s₀
    · refine (h.frame.readW (r := sret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st
        · exact hp.ret_d
        · exact hp.ret_b
      · exact ((vmem_frame s₀).readW (r := sret s₀) (a := s₀.gpr .rsp) (w := 64) (Region.contains_self _ _)
          (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_d) (by decide))
  · show bytesAt s'.mem (sdp s₀) (sL s₀) =
      List.zipWith (· ^^^ ·) (bytesAt (vmem s₀) (sdp s₀) (sL s₀)) (keystream (Avx2.S0 (V s₀)) (sL s₀))
    rw [V_S0 hp]
    refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
    rw [vmem_dst s₀ hk]
    by_cases hk' : k < 1024 * t
    · have n_w : ¬ (⟨sdp s₀ + BitVec.ofNat 64 (1024 * t), sL s₀ - 1024 * t⟩ : Region).Contains
          (sdp s₀ + BitVec.ofNat 64 k) 1 := by
        simp only [Region.Contains]; bv_omega
      rw [hf _ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact fun hc => hp.st_d _ hc (Avx2.in_dR (s₀ := V s₀) hk)
          · exact n_w
          · exact fun hc => hp.d_b _ (Avx2.in_dR (s₀ := V s₀) hk) hc
          · exact fun hc => hp.stk_d _ hc (Avx2.in_dR (s₀ := V s₀) hk)), h.done k hk']
    · have ea : sdp s₀ + BitVec.ofNat 64 k =
          sdp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) := by
        rw [add_ofNat, Nat.add_sub_cancel' (by omega_arith)]
      have x := Avx2.bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 1024 * t) (by omega_arith)
      rw [← ea, h.cnt, keystream_getD _ (by omega_arith), Avx2.ctr_ctr] at x
      rw [x, h.todo k hk (by omega_arith) (by omega_arith), keystream_getD _ hk,
        show 16 * t + (k - 1024 * t) / 64 = k / 64 by omega_arith, show (k - 1024 * t) % 64 = k % 64 by omega_arith]

theorem rest_ok {s₀ : State} (hp : APre s₀) {t : Nat} (ht : sL s₀ - 1024 * t < 1024) {s : State}
    (h : SInv s₀ (Cof s₀) t s) :
    WP isa (.seq (.block [.alu .cmp .rdx (.imm 513)]) (.ite .b (.call "vg_chacha20_xor_avx512" xor) last16Sel)) s
      fun s' => gprPreserved s₀ s' ∧ xorSplitX86_64.post s₀ s' := by
  have hL := sL_lt s₀
  have hle := h.le
  refine WP.seq (WP.mono (Avx512.cmp513_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁, c₁⟩ => ?_)
  have h₁ := h.of_eq g₁ m₁ rd₁ wr₁
  have hr : (s.gpr .rdx).toNat = sL s₀ - 1024 * t := by rw [h.rdx, toNat_ofNat_lt (by omega_arith)]
  refine WP.ite (decide (sL s₀ - 1024 * t < 513)) (by simp [eval, c₁, hr]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    have hC : Cof s₀ ≤ 1024 * t := by
      have := Cof_le (s₀ := s₀) (by omega_arith); omega_arith
    exact tailCall_ok hp hC ht h₁
  · simp only [decide_eq_false_iff_not] at hs
    exact WP.mono (last16Sel_ok hp (Cof_ok hp) (by omega_arith) ht h₁) fun s' ⟨hpost, _⟩ => post_of_V hp hpost

/-! ## The whole function -/

theorem xorSplit_eq : xorSplit =
    .seq entryC (.seq (.block copyArgs) (.seq (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes .z64)
    (.seq (.block (loopArgs ++ Impl.ChaCha20.X86_64.Avx512Tail.consts ++ consts ++
      ([.alu .cmp .rdx (.imm 1024)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop bodySel .ae))
    (.seq (.block [.alu .cmp .rdx (.imm 513)]) (.ite .b (.call "vg_chacha20_xor_avx512" xor) last16Sel)))))) := rfl

theorem correct {s₀ : State} (hp : APre s₀) :
    WP isa xorSplit s₀ fun s' => gprPreserved s₀ s' ∧ xorSplitX86_64.post s₀ s' := by
  rw [xorSplit_eq]
  refine prologue_ok hp fun s₁ h₁ hc => ?_
  exact WP.seq (WP.mono (loop_ok hp (Cof_ok hp) h₁ hc) fun s₂ ⟨t, ht, h₂⟩ => rest_ok hp ht h₂)

end VG.Proof.ChaCha20.X86_64.Avx512Split
