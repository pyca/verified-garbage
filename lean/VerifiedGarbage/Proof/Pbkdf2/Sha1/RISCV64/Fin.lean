module

public import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Pro
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Hmac.Common

/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the epilogue, and correctness

Untrusted: everything here is checked by Lean. The epilogue writes `T`'s
words to `t`, big-endian, which is the digest of the final `T`
(`out_ok`), and restores our caller's registers (`fin_ok`). `correct`: the
entry block, the prologue, the loop and the epilogue meet the iteration's
contract (`iterK`), since the digest of the final `T` on words is PBKDF2's
(`Sha1Words.iterate_digest`, `Md.iterate_hmac`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.ByteLoad (beBytes storeBE_ok)
open VG.WriteBytes (writeBytes)
open VG.Impl.Words.RISCV64 (storeBE)
open VG.Proof.Hmac.Common (writeBytes_at writeBytes_other)
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes Entry key up tp scr nn sc scR keyR uR tR sc_al sc_sub iterK)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word wordBytes)
open VG.Proof.Sha1 (md)
open VG.Proof.Pbkdf2.Sha1Words (beWords wIter digest_eq digest_beWords iterate_digest)

theorem shr_byte (x : BitVec 64) (s : Nat) : (x >>> s).setWidth 8 = x.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, hi]

theorem setWidth_byte (w : Word) {s : Nat} (h : s + 8 ≤ 32) :
    (w.setWidth 64).extractLsb' s 8 = w.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show s + i < 32 by omega, show s + i < 64 by omega]

/-- A word, as `storeBE 4` stores it. -/
theorem beBytes_word (w : Word) : beBytes 4 (w.setWidth 64) = wordBytes w := by
  simp only [beBytes, shr_byte]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp (disch := decide) only [List.map_cons, List.map_nil, Nat.reduceMul, Nat.reduceSub, setWidth_byte,
    wordBytes]

/-- Byte `4k + i` of a digest. -/
theorem digest_getD (x : HashValue) {k i : Nat} (hk : k < 5) (hi : i < 4) :
    (md.digest x).getD (4 * k + i) 0 = (wordBytes x[k]!).getD i 0 := by
  rw [digest_eq, getElem!_pos x k hk]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
  simp [wordBytes]

theorem digest_length (x : HashValue) : (md.digest x).length = 20 := md.digest_length x

/-! ## `T` to `t` -/

/-- The first `k` words of `T` written to `t`, from the state `s₁` before. -/
structure OI (s₀ s₁ : State) (y : HashValue) (k : Nat) (s : State) : Prop where
  bytes : ∀ j < 20, s.mem (tp s₀ + BitVec.ofNat 64 j) =
    if j < 4 * k then (md.digest y).getD j 0 else s₁.mem (tp s₀ + BitVec.ofNat 64 j)
  frame : Frame [tR it s₀] s₁.mem s.mem
  gpr : ∀ r, r ≠ T1 → r ≠ KR → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

/-- The frame's words, which the writes to `t` keep. -/
theorem fw_tR {m m' : Mem} (hf : Frame [tR it s₀] m m') {d : Nat} (hd : d + 4 ≤ 164) : fw s₀ m' d = fw s₀ m d :=
  hf.readW (r := scR Wi s₀) (fc hz hd) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.symm) (by decide)

theorem out_ok (s₁ : State) (y : HashValue) (hb : s₁.gpr B = sc s₀) (htp : s₁.gpr TP = tp s₀)
    (hy : ∀ k < 5, fw s₀ s₁.mem (tO + 4 * k) = y[k]!) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range 5).flatMap fun k => ([.load .w T1 B (tO + 4 * k)] : List Instr) ++ storeBE 4 T1 KR TP (4 * k)))
      s₁ (OI s₀ s₁ y 5) := by
  refine wp_range_flatMap (M := isa) (OI s₀ s₁ y) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨fun j _ => by simp, Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  have hb' : s.gpr B = sc s₀ := by rw [h.gpr _ (by decide) (by decide), hb]
  have htp' : s.gpr TP = tp s₀ := by rw [h.gpr _ (by decide) (by decide), htp]
  have rd' : s.rd = s₀.rd := h.rd.trans hrd
  have wr' : s.wr = s₀.wr := h.wr.trans hwr
  rw [List.singleton_append]
  refine wp_lw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega) (by rw [hb'])
    (fal s₀ (by simp only [tO]; omega)) (frd hp hz rd' wr' (by simp only [tO]; omega)) fun s₂ u₂ => ?_
  have hv : s₂.gpr T1 = (y[k]!).setWidth 64 := by
    have e := fw_tR hp hz h.frame (d := tO + 4 * k) (by simp only [tO]; omega)
    have e' := hy k hk
    simp only [fw] at e e'
    rw [u₂.gpr, e, e']
  have tp₂ : s₂.gpr TP = tp s₀ := by rw [u₂.other _ (by decide), htp']
  refine WP.mono (storeBE_ok (s := s₂) (v := T1) (tmp := KR) (n := TP) (off := 4 * k) (w := 4) (by decide)
    (by decide) (by decide) (by decide) (by omega) fun j hj => ?_) fun s₃ e₃ => ?_
  · rw [u₂.wr, wr', hp.wr, tp₂]
    exact ⟨tR it s₀, by simp, Offset.contains_base _ (by simp only [it]; omega) (by omega)⟩
  subst e₃
  have m₃ : (({ s₂ with mem := writeBytes s₂.mem (s₂.gpr TP + BitVec.ofNat 64 (4 * k)) (beBytes 4 (s₂.gpr T1)) } :
      State).write KR (s₂.gpr T1)).mem = writeBytes s.mem (tp s₀ + BitVec.ofNat 64 (4 * k)) (wordBytes y[k]!) := by
    rw [RegUpd.mem_write]; show writeBytes _ _ _ = _; rw [u₂.mem, tp₂, hv, beBytes_word]
  have wl : (wordBytes y[k]!).length = 4 := rfl
  refine ⟨fun j hj => ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [m₃]
    by_cases hin : 4 * k ≤ j ∧ j < 4 * k + 4
    · obtain ⟨i, rfl⟩ : ∃ i, j = 4 * k + i := ⟨j - 4 * k, by omega⟩
      rw [← Offset.add_add, writeBytes_at _ _ _ (by rw [wl]; omega) (by rw [wl]; decide),
        digest_getD y hk (by omega)]
      simp only [show 4 * k + i < 4 * (k + 1) by omega, ↓reduceIte]
    · rw [writeBytes_other _ _ _ (by
        rw [wl, Offset.lt_iff _ _ (by omega), Mem.sub_ofNat_toNat _ (by omega)]; exact hin), h.bytes j hj]
      by_cases hjk : j < 4 * k
      · simp only [hjk, show j < 4 * (k + 1) by omega, ↓reduceIte]
      · simp only [hjk, show ¬ j < 4 * (k + 1) by omega, ↓reduceIte]
  · rw [m₃]
    exact h.frame.trans (VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [wl]; exact Offset.contains_base _ (by simp only [it]; omega) (by omega)))
  · rw [RegUpd.gpr_write_of_ne _ _ h2]
    show s₂.gpr r = _
    rw [u₂.other _ h1, h.gpr r h1 h2]
  · rw [RegUpd.rd_write]; show s₂.rd = _; rw [u₂.rd, h.rd]
  · rw [RegUpd.wr_write]; show s₂.wr = _; rw [u₂.wr, h.wr]
  · rw [RegUpd.sp_write]; show s₂.sp = _; rw [u₂.sp, h.sp]

omit hp hz in
theorem finish_eq : finish = ((List.range 5).flatMap fun k => ([.load .w T1 B (tO + 4 * k)] : List Instr) ++
    storeBE 4 T1 KR TP (4 * k)) ++ Spill.restoreCode B saved := rfl

theorem fin_ok {R : HashValue} {s : State} (h : LI Wi s₀ R 0 s) :
    WP isa (.block finish) s fun s' => abiPreserved s₀ s' ∧ Spec.Sha256.bytesAt s'.mem (tp s₀) 20 = md.digest R := by
  obtain ⟨x, y, hx, hy, hR⟩ := h.xy
  have hyR : y = R := hR
  subst hyR
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (out_ok hp hz s y h.b h.tp hy h.rd h.wr) fun s₁ h₁ => ?_
  have b₁ : s₁.gpr B = sc s₀ := by rw [h₁.gpr _ (by decide) (by decide), h.b]
  have sv₁ : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem :=
    h.saved.frame h₁.frame fun q hq r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.symm.sub_left (sc_sub (by have := hz.fits; have := saved_bound q hq; simp only [it] at *; omega))
  refine WP.mono (Spill.restore_wp (b := B) (l := saved) (B := sc s₀) sc_al b₁ (by decide) (by decide)
    (fun q hq => frd hp hz (h₁.rd.trans h.rd) (h₁.wr.trans h.wr) (by have := saved_bound q hq; omega)) sv₁)
    fun s₂ r₂ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · exact r₂.gpr_of (.inl (by revert r; decide))
  · rw [r₂.sp, h₁.sp, h.sp]
  · exact r₂.gpr_of (.inl (by decide))
  · rw [r₂.mem]
    apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, digest_length])
    intro j h₁' h₂'
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range] at h₁'
    simp only [Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range]
    rw [h₁.bytes j h₁']
    simp only [show j < 4 * 5 by omega, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂',
      Option.getD_some]

end

theorem entry_eq : entry = Impl.Pbkdf2.RISCV64.It.entry := rfl

/-- `iterate` meets the iteration's contract, for SHA-1's link to the specification. -/
theorem correct {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
    (hl : md.Link Spec.Hmac.sha1S Spec.Sha1.H0 20) :
    WP isa iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterK Spec.Hmac.sha1S Wi).post s₀ s' := by
  unfold iterate main
  refine WP.seq (WP.mono (by rw [entry_eq]; exact Proof.Pbkdf2.RISCV64.entry_ok s₀) fun e he => ?_)
  refine WP.seq (WP.mono (pro_ok hp hz he) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz (Proof.Pbkdf2.RISCV64.nn_lt s₀) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (fin_ok hp hz h₂) fun s' ⟨ha, hb⟩ => ⟨ha, ?_⟩
  intro k0 hk hi ho
  have hD : Spec.Hmac.sha1S.digestBytes = 20 := rfl
  rw [hD]
  rw [MdStream.Md.iterate_hmac hl hk hi ho _ (by simp [Spec.Sha256.bytesAt]),
    ← digest_beWords s₀.mem (s₀.gpr .a1), ← digest_beWords s₀.mem (s₀.gpr .a3),
    iterate_digest (md.stateAt s₀.mem (s₀.gpr .a0))
      (md.stateAt s₀.mem (s₀.gpr .a0 + BitVec.ofNat 64 Spec.Hmac.sha1S.stateBytes))]
  exact hb

end VG.Proof.Pbkdf2.Sha1.RISCV64
