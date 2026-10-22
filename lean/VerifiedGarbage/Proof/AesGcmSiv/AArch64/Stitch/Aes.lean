module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Aes
public import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Stitch
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: the counter mode

Untrusted: everything here is checked by Lean. `aesPart_ok`: `aesPart nr o`
(`Impl.AesGcmSiv.AArch64.Stitch`) leaves in `v0`–`v7` the eight data blocks
at `x9 + o` XORed with the cipher of the counter blocks `cvec s k j`: the
counter block at `x19 + 96` with its first word replaced by that word plus
`k + j` (`w10` being that word plus `k`), as RFC 8452 §4 increments it. The
rounds are AES-GCM's (`Proof.Gcm.AArch64.Stitch`), with the keys at `x21`;
only the counter blocks differ.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (K P breg rnd lastRnd)
open VG.Proof.Gcm.AArch64.Stitch (breg_inj breg_ne_K breg_ne_P aesV breg_mem RI rnd8_ok aese8_ok fin8_ok fr_setV
  fr_widen)
open VG.Proof.Aes.AArch64.Aese (st KeyIs rnds round_st last_st keyIs_readW getD_st exec_ldrq
  vbyte_xor vbyte_readW setV_v_self setV_v_of_ne setV_setV Fr exec_addImm_w sw32)
open VG.Spec.Aes (roundKey cipher addRoundKey)
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV v_write gpr_write_self
  gpr_write_of_ne mem_write rd_write wr_write sp_write)

/-! ## What the part needs -/

section
variable (s : State)

abbrev cbA : Addr := s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO
/-- The counter block's first word, as a little-endian number. -/
abbrev c0 : BitVec 32 := s.mem.readW (cbA s) 32
end

/-- `aesPart nr o` can run from `s`, the counter in `w10` being the
counter block's plus `k`. -/
structure APre (nr o k : Nat) (s : State) : Prop where
  rounds : nr = 10 ∨ nr = 12 ∨ nr = 14
  o_le : o ≤ 128
  keys : ∀ r ≤ nr, InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 16
  ctr : InRegions (s.rd ++ s.wr) (cbA s) 16
  data : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16
  x10 : s.read .w .x10 = c0 s + BitVec.ofNat 32 k

/-- The key schedule of `nr` rounds at `x21`. -/
abbrev sch (nr : Nat) (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x21) (16 * (nr + 1))

/-- The counter block `k + j`, as `ctr1` builds it. -/
abbrev cvec (s : State) (k j : Nat) : BitVec 128 :=
  setLane (s.mem.readW (cbA s) 128) 32 0 (c0 s + BitVec.ofNat 32 k + BitVec.ofNat 32 j)

/-- What it leaves: the blocks, and only `x10`, `x12` and `aesV` written. -/
structure APost (nr o k : Nat) (s s' : State) : Prop where
  out : ∀ j < 8, ∀ t < 16, vbyte (s'.v (breg j)) t =
    (cipher nr (sch nr s) (st (cvec s k j))).getD t 0 ^^^
      s.mem (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) + BitVec.ofNat 64 t)
  x10 : s'.read .w .x10 = c0 s + BitVec.ofNat 32 (k + 8)
  fr : Fr [.x10, .x12] aesV s s'

/-! ## The counter blocks -/

/-- `ctr1 j`: counter block `k + j` into `breg j`. -/
theorem ctr1_ok (j : Nat) (hj : j < 8) (s : State) (hin : InRegions (s.rd ++ s.wr) (cbA s) 16) :
    WP isa (.block (ctr1 j)) s fun s' =>
      s'.v (breg j) = setLane (s.mem.readW (cbA s) 128) 32 0 (s.read .w .x10 + BitVec.ofNat 32 j) ∧
        Fr [.x12] [breg j] s s' := by
  rw [ctr1, WP.block_cons_iff]
  refine ⟨_, exec_addImm_w (by omega), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrq (off := Impl.AesGcmSiv.AArch64.cbO) (by decide) hin, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp [State.setV, State.write, State.read]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]

theorem ctrs_ok {nr o k : Nat} {s : State} (hp : APre nr o k s) :
    WP isa (.block ((List.range 8).flatMap ctr1)) s fun s' =>
      (∀ j < 8, s'.v (breg j) = cvec s k j) ∧ Fr [.x12] aesV s s' := by
  refine wp_range_flatMap (M := isa) (fun i s' => (∀ j < i, s'.v (breg j) = cvec s k j) ∧
      Fr [.x12] aesV s s') (fun i s₁ hi ⟨e₁, f₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega), Fr.refl _ _ _⟩
  refine WP.mono (ctr1_ok i hi s₁ (by rw [f₁.rd, f₁.wr, cbA, f₁.gpr _ (by decide)]; exact hp.ctr))
    fun s' ⟨e, f⟩ => ⟨fun j hj => ?_, f₁.trans (f.mono (fun r h => h)
      (fun r h => by simp only [List.mem_singleton] at h; subst h; exact breg_mem i))⟩
  by_cases hji : j = i
  · subst hji
    have hx := hp.x10
    simp only [State.read] at hx
    rw [e, f₁.mem]
    simp only [cbA, State.read, f₁.gpr _ (by decide : Reg.x19 ∉ [Reg.x12]),
      f₁.gpr _ (by decide : Reg.x10 ∉ [Reg.x12])]
    rw [hx]
  · rw [f.v _ (by simp only [List.mem_singleton]; exact fun h => hji (breg_inj j (by omega) i hi h)),
      e₁ j (by omega)]

/-! ## The rounds -/

/-- Round key `r` into `v30`, and the eight states through the round. -/
theorem rnd_ok {nr o k : Nat} {s₀ : State} (hp : APre nr o k s₀) {x : Nat → Spec.Aes.State} {r : Nat}
    (hr : r + 1 ≤ nr) {s : State} (hf : Fr [.x12] aesV s₀ s) (hI : RI (sch nr s₀) x r s) :
    WP isa (.block (rnd r)) s fun s' => RI (sch nr s₀) x (r + 1) s' ∧ Fr [.x12] aesV s₀ s' := by
  have hR := hp.rounds
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [hf.rd, hf.wr, hf.gpr _ (by decide)]; exact hp.keys r (by omega)
  rw [rnd, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega) hin, ?_⟩
  have hk : KeyIs ((s.setV K (s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 128)).v K)
      (roundKey (sch nr s₀) r) := by
    rw [setV_v_self, hf.mem, hf.gpr _ (by decide)]
    exact keyIs_readW _ _ (by omega)
  have hI' : RI (sch nr s₀) x r (s.setV K (s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 128)) :=
    fun j hj => by rw [setV_v_of_ne _ _ (breg_ne_K j)]; exact hI j hj
  exact WP.mono (rnd8_ok hk hI') fun s' ⟨e, f, _⟩ =>
    ⟨e, (hf.trans (fr_setV _ _ (by decide))).trans (fr_widen f _)⟩

theorem rnds_ok {nr o k : Nat} {s₀ : State} (hp : APre nr o k s₀) {x : Nat → Spec.Aes.State} {s : State}
    (hf : Fr [.x12] aesV s₀ s) (hI : RI (sch nr s₀) x 0 s) :
    ∀ n, n + 1 ≤ nr → WP isa (.block ((List.range n).flatMap rnd)) s fun s' =>
      RI (sch nr s₀) x n s' ∧ Fr [.x12] aesV s₀ s' := by
  intro n hn
  refine wp_range_flatMap (M := isa) (fun r s' => RI (sch nr s₀) x r s' ∧ Fr [.x12] aesV s₀ s')
    (fun r s₁ hr ⟨e₁, f₁⟩ => rnd_ok hp (by omega) f₁ e₁) n (Nat.le_refl _) s ⟨hI, hf⟩

/-! ## The part -/

theorem aesPart_ok {nr o k : Nat} {s : State} (hp : APre nr o k s) (ho16 : o % 16 = 0) :
    WP isa (.block (aesPart nr o)) s (APost nr o k s) := by
  have hR := hp.rounds
  unfold aesPart
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ctrs_ok hp) fun s₁ ⟨e₁, f₁⟩ => ?_
  -- The counter blocks, as AES states.
  let x : Nat → Spec.Aes.State := fun j => st (cvec s k j)
  have hI₁ : RI (sch nr s) x 0 s₁ := fun j hj => by rw [e₁ j hj]; rfl
  refine WP.mono (rnds_ok hp f₁ hI₁ (nr - 1) (by omega)) fun s₂ ⟨e₂, f₂⟩ => ?_
  -- The last round.
  have g₂ : s₂.gpr .x21 = s.gpr .x21 := f₂.gpr _ (by decide)
  have hin : ∀ r ≤ nr, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x21 + BitVec.ofNat 64 (16 * r)) 16 :=
    fun r hr => by rw [f₂.rd, f₂.wr, g₂]; exact hp.keys r hr
  unfold lastRnd
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega) (hin (nr - 1) (by omega)), ?_⟩
  generalize hK₁ : s₂.mem.readW (s₂.gpr .x21 + BitVec.ofNat 64 (16 * (nr - 1))) 128 = K₁
  refine WP.mono (aese8_ok _) fun s₃ ⟨e₃, f₃, _⟩ => ?_
  rw [WP.block_cons_iff]
  have hin₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x21 + BitVec.ofNat 64 (16 * nr)) 16 := by
    rw [f₃.rd, f₃.wr, f₃.gpr _ (by decide), rd_setV, wr_setV, gpr_setV]
    exact hin nr (Nat.le_refl _)
  refine ⟨_, exec_ldrq (by omega) hin₃, ?_⟩
  generalize hK₂ : s₃.mem.readW (s₃.gpr .x21 + BitVec.ofNat 64 (16 * nr)) 128 = K₂
  have g₃ : ∀ r, s₃.gpr r = s₂.gpr r := fun r => by rw [f₃.gpr r (by simp)]; rfl
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, mem_setV, f₂.mem]
  have hin₄ : ∀ j < 8, InRegions ((s₃.setV K K₂).rd ++ (s₃.setV K K₂).wr)
      ((s₃.setV K K₂).gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16 := fun j hj => by
    rw [rd_setV, wr_setV, gpr_setV, f₃.rd, f₃.wr, g₃, rd_setV, wr_setV, f₂.rd,
      f₂.wr, f₂.gpr _ (by decide)]
    exact hp.data j hj
  refine WP.mono (fin8_ok hp.o_le _ hin₄ ho16) fun s₄ ⟨e₄, f₄⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_w (imm := 8) (by decide), WP.block_nil ?_⟩
  -- The keys, and the last round of each block.
  have hk₁ : KeyIs K₁ (roundKey (sch nr s) (nr - 1)) := by
    rw [← hK₁, f₂.mem, g₂]; exact keyIs_readW _ _ (by omega)
  have hk₂ : KeyIs K₂ (roundKey (sch nr s) nr) := by
    rw [← hK₂, m₃, g₃, g₂]; exact keyIs_readW _ _ (by omega)
  have g₉ : s₃.gpr .x9 = s.gpr .x9 := by rw [g₃, f₂.gpr _ (by decide)]
  refine ⟨fun j hj t ht => ?_, ?_, ?_⟩
  · rw [v_write, e₄ j hj, v_setV_of_ne _ _ (breg_ne_K j), e₃ j hj, v_setV_of_ne _ _ (breg_ne_K j),
      v_setV_self, v_setV_self, mem_setV, gpr_setV, m₃, g₉,
      show ∀ A M C : BitVec 128, A ^^^ M ^^^ C = (A ^^^ C) ^^^ M from fun A M C => by ac_rfl, vbyte_xor,
      vbyte_readW _ _ ht, ← getD_st _ ht, last_st hk₁ hk₂ (e₂ j hj)]
  · have hx := hp.x10
    have g₁₀ : s₄.gpr .x10 = s.gpr .x10 := by
      rw [f₄.gpr _ (by simp), gpr_setV, g₃, f₂.gpr _ (by decide)]
    simp only [State.read] at hx ⊢
    rw [gpr_write_self, sw32, g₁₀, hx, BitVec.add_assoc, ← BitVec.ofNat_add]
  · have f₄' : Fr [] aesV s₃ s₄ := (fr_setV _ _ (by decide)).trans f₄
    have f₃' : Fr [] aesV s₂ s₃ := (fr_setV _ _ (by decide)).trans f₃
    refine ((f₂.trans (fr_widen (f₃'.trans f₄') _)).mono (fun r h => List.mem_cons_of_mem _ h)
      (fun _ h => h)).trans ⟨fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact gpr_write_of_ne _ _ _ hr.1

end VG.Proof.AesGcmSiv.AArch64.Stitch
