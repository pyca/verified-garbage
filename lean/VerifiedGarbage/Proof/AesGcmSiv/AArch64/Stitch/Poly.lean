module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Framework.AArch64.InterleaveFootprints
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
public import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Stitch

/-! ### `AesGcmSiv.AArch64.Stitch.Loops`, which this module and modules that import it used -/

section

/-! ### `AesGcmSiv.AArch64.Stitch.Steps`, which this module and modules that import it used -/

section

/-! ### `AesGcmSiv.AArch64.Stitch.Aes`, which only this module used -/

section

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: the counter mode

Untrusted: everything here is checked by Lean. `aesPart_ok`: `aesPart nr o`
(`Impl.AesGcmSiv.AArch64.Stitch`) leaves in `v0`–`v7` the eight data blocks
at `x9 + o` XORed with the cipher of the counter blocks `cvec s k j`: the
counter block at `x19 + 96` with its first word replaced by that word plus
`k + j` (`w10` being that word plus `k`), as RFC 8452 §4 increments it. The
rounds are AES-GCM's (`Proof.Gcm.AArch64.Stitch`), with the keys at `x15`;
only the counter blocks differ.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (K P breg)
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
  keys : ∀ r ≤ nr, InRegions (s.rd ++ s.wr) (s.gpr .x15 + BitVec.ofNat 64 (16 * r)) 16
  ctr : InRegions (s.rd ++ s.wr) (cbA s) 16
  data : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16
  x10 : s.read .w .x10 = c0 s + BitVec.ofNat 32 k

/-- The key schedule of `nr` rounds at `x15`. -/
abbrev sch (nr : Nat) (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x15) (16 * (nr + 1))

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
  refine ⟨_, exec_addImm_w (by omega_arith), ?_⟩
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
    ⟨fun _ h => absurd h (by omega_arith), Fr.refl _ _ _⟩
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
  · rw [f.v _ (by simp only [List.mem_singleton]; exact fun h => hji (breg_inj j (by omega_arith) i hi h)),
      e₁ j (by omega_arith)]

/-! ## The rounds -/

/-- Round key `r` into `v30`, and the eight states through the round. -/
theorem rnd_ok {nr o k : Nat} {s₀ : State} (hp : APre nr o k s₀) {x : Nat → Spec.Aes.State} {r : Nat}
    (hr : r + 1 ≤ nr) {s : State} (hf : Fr [.x12] aesV s₀ s) (hI : RI (sch nr s₀) x r s) :
    WP isa (.block (rnd r)) s fun s' => RI (sch nr s₀) x (r + 1) s' ∧ Fr [.x12] aesV s₀ s' := by
  have hR := hp.rounds
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x15 + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [hf.rd, hf.wr, hf.gpr _ (by decide)]; exact hp.keys r (by omega_arith)
  rw [rnd, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega_arith) hin, ?_⟩
  have hk : KeyIs ((s.setV K (s.mem.readW (s.gpr .x15 + BitVec.ofNat 64 (16 * r)) 128)).v K)
      (roundKey (sch nr s₀) r) := by
    rw [setV_v_self, hf.mem, hf.gpr _ (by decide)]
    exact keyIs_readW _ _ (by omega_arith)
  have hI' : RI (sch nr s₀) x r (s.setV K (s.mem.readW (s.gpr .x15 + BitVec.ofNat 64 (16 * r)) 128)) :=
    fun j hj => by rw [setV_v_of_ne _ _ (breg_ne_K j)]; exact hI j hj
  exact WP.mono (rnd8_ok hk hI') fun s' ⟨e, f, _⟩ =>
    ⟨e, (hf.trans (fr_setV _ _ (by decide))).trans (fr_widen f _)⟩

theorem rnds_ok {nr o k : Nat} {s₀ : State} (hp : APre nr o k s₀) {x : Nat → Spec.Aes.State} {s : State}
    (hf : Fr [.x12] aesV s₀ s) (hI : RI (sch nr s₀) x 0 s) :
    ∀ n, n + 1 ≤ nr → WP isa (.block ((List.range n).flatMap rnd)) s fun s' =>
      RI (sch nr s₀) x n s' ∧ Fr [.x12] aesV s₀ s' := by
  intro n hn
  refine wp_range_flatMap (M := isa) (fun r s' => RI (sch nr s₀) x r s' ∧ Fr [.x12] aesV s₀ s')
    (fun r s₁ hr ⟨e₁, f₁⟩ => rnd_ok hp (by omega_arith) f₁ e₁) n (Nat.le_refl _) s ⟨hI, hf⟩

/-! ## The last round's sums -/

theorem eor2_run (j o : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16)
    (ho : o + 16 * j < 65536) (ho' : (o + 16 * j) % 16 = 0) :
    runBlock isa (.ldrq P .x9 (o + 16 * j) :: xor3 false (breg j) (breg j) P K) s =
      some ((s.setV P (s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128)).setV (breg j)
        (s.v (breg j) ^^^ s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K)) := by
  rw [runBlock_cons, exec_ldrq ⟨ho', ho⟩ hin, runStep_some]
  simp only [xor3, Bool.false_eq_true, ite_false, runBlock_cons, runStep_some, runBlock_nil, isa, exec,
    VOp.eval, Option.map_some]
  rw [setV_v_self, setV_v_of_ne _ _ (breg_ne_P j), setV_v_of_ne _ _ (breg_ne_K j).symm,
    setV_v_of_ne _ _ (by decide : K ≠ P), setV_v_self, setV_setV]

/-- `Proof.Gcm.AArch64.Stitch.fin8_ok`, with the sums by `xor3 e3`. -/
theorem fin8x_ok (e3 : Bool) {o : Nat} (ho : o ≤ 128) (s : State)
    (hin : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16)
    (ho16 : o % 16 = 0) :
    WP isa (.block ((List.range 8).flatMap fun j => .ldrq P .x9 (o + 16 * j) :: xor3 e3 (breg j) (breg j) P K))
      s fun s' =>
      (∀ j < 8, s'.v (breg j) = s.v (breg j) ^^^ s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K) ∧
      Fr [] aesV s s' := by
  cases e3
  case true => exact fin8_ok ho s hin ho16
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s' =>
      (∀ j < i, s'.v (breg j) = s.v (breg j) ^^^ s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K) ∧
      (∀ j, i ≤ j → j < 8 → s'.v (breg j) = s.v (breg j)) ∧ Fr [] aesV s s' ∧ s'.v K = s.v K)
    (fun i s₁ hi ⟨e₁, u₁, f₁, k₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Fr.refl _ _ _, rfl⟩)
    fun s' ⟨e, _, f, _⟩ => ⟨e, f⟩
  have hin₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x9 + BitVec.ofNat 64 (o + 16 * i)) 16 := by
    rw [f₁.rd, f₁.wr, f₁.gpr _ (by decide)]; exact hin i hi
  refine WP.of_runBlock ⟨_, eor2_run i o s₁ hin₁ (by omega_arith) (by omega_arith), ?_⟩
  have hne : ∀ j, j < 8 → j ≠ i → breg j ≠ breg i := fun j hj hji h => hji (breg_inj j hj i hi h)
  refine ⟨fun j hj => ?_, fun j hj hj8 => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji; rw [setV_v_self, u₁ j (Nat.le_refl _) hi, k₁, f₁.mem, f₁.gpr _ (by decide)]
    · rw [setV_v_of_ne _ _ (hne j (by omega_arith) hji), setV_v_of_ne _ _ (breg_ne_P j)]; exact e₁ j (by omega_arith)
  · rw [setV_v_of_ne _ _ (hne j hj8 (by omega_arith)), setV_v_of_ne _ _ (breg_ne_P j), u₁ j (by omega_arith) hj8]
  · refine f₁.trans ⟨fun _ _ => rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    rw [setV_v_of_ne _ _ fun h => hr (by rw [h]; exact breg_mem i), setV_v_of_ne _ _ fun h => hr (by rw [h]; decide)]
  · rw [setV_v_of_ne _ _ (breg_ne_K i).symm, setV_v_of_ne _ _ (by decide : K ≠ P), k₁]

/-! ## The part -/

theorem aesPart_ok (e3 : Bool) {nr o k : Nat} {s : State} (hp : APre nr o k s) (ho16 : o % 16 = 0) :
    WP isa (.block (aesPart e3 nr o)) s (APost nr o k s) := by
  have hR := hp.rounds
  unfold aesPart
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ctrs_ok hp) fun s₁ ⟨e₁, f₁⟩ => ?_
  -- The counter blocks, as AES states.
  let x : Nat → Spec.Aes.State := fun j => st (cvec s k j)
  have hI₁ : RI (sch nr s) x 0 s₁ := fun j hj => by rw [e₁ j hj]; rfl
  refine WP.mono (rnds_ok hp f₁ hI₁ (nr - 1) (by omega_arith)) fun s₂ ⟨e₂, f₂⟩ => ?_
  -- The last round.
  have g₂ : s₂.gpr .x15 = s.gpr .x15 := f₂.gpr _ (by decide)
  have hin : ∀ r ≤ nr, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x15 + BitVec.ofNat 64 (16 * r)) 16 :=
    fun r hr => by rw [f₂.rd, f₂.wr, g₂]; exact hp.keys r hr
  unfold lastRnd
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega_arith) (hin (nr - 1) (by omega_arith)), ?_⟩
  generalize hK₁ : s₂.mem.readW (s₂.gpr .x15 + BitVec.ofNat 64 (16 * (nr - 1))) 128 = K₁
  refine WP.mono (aese8_ok _) fun s₃ ⟨e₃, f₃, _⟩ => ?_
  rw [WP.block_cons_iff]
  have hin₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x15 + BitVec.ofNat 64 (16 * nr)) 16 := by
    rw [f₃.rd, f₃.wr, f₃.gpr _ (by decide), rd_setV, wr_setV, gpr_setV]
    exact hin nr (Nat.le_refl _)
  refine ⟨_, exec_ldrq (by omega_arith) hin₃, ?_⟩
  generalize hK₂ : s₃.mem.readW (s₃.gpr .x15 + BitVec.ofNat 64 (16 * nr)) 128 = K₂
  have g₃ : ∀ r, s₃.gpr r = s₂.gpr r := fun r => by rw [f₃.gpr r (by simp)]; rfl
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, mem_setV, f₂.mem]
  have hin₄ : ∀ j < 8, InRegions ((s₃.setV K K₂).rd ++ (s₃.setV K K₂).wr)
      ((s₃.setV K K₂).gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16 := fun j hj => by
    rw [rd_setV, wr_setV, gpr_setV, f₃.rd, f₃.wr, g₃, rd_setV, wr_setV, f₂.rd,
      f₂.wr, f₂.gpr _ (by decide)]
    exact hp.data j hj
  refine WP.mono (fin8x_ok e3 hp.o_le _ hin₄ ho16) fun s₄ ⟨e₄, f₄⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_w (imm := 8) (by decide), WP.block_nil ?_⟩
  -- The keys, and the last round of each block.
  have hk₁ : KeyIs K₁ (roundKey (sch nr s) (nr - 1)) := by
    rw [← hK₁, f₂.mem, g₂]; exact keyIs_readW _ _ (by omega_arith)
  have hk₂ : KeyIs K₂ (roundKey (sch nr s) nr) := by
    rw [← hK₂, m₃, g₃, g₂]; exact keyIs_readW _ _ (by omega_arith)
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

end

end

/-! ### `AesGcmSiv.AArch64.Stitch.Gh`, which only this module used -/

section

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: POLYVAL's instructions

Untrusted: everything here is checked by Lean. `ghPart_ok`: `ghPart`
(`Impl.AesGcmSiv.AArch64.Stitch`) leaves in `Y` (`v16`) the `gh8V` of `Y`, the
eight blocks at `x9` with their halves swapped (`blkV`), and the powers and
keys of the table at `x19 + tblO`, as AES-GCM's `ghPart` does with the blocks
as it loads them (`Proof.Gcm.AArch64.Stitch.ghPart_ok`): only the loads
(`ld`) and the table's place differ, and the products, their sums and the
reduction are the same instructions.
-/

@[expose] public section

local notation "vdword" => VG.Proof.Gcm.Clmul.vdword
local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64
open VG.Proof.Gcm.AArch64.Pmull (Prod ext8 VOnly v_setV gpr_setV mem_setV rd_setV wr_setV sp_setV
  exec_pmull0 exec_pmull1 exec_eor exec_ext8 vdword_append_0 vdword_append_1)
open VG.Proof.Gcm.AArch64.Stitch (prodS kpair fix gh8V ghV pairV exec_trn trn_sum vdword_ofVDwords0
  vdword_ofVDwords1 addY_ok addFirst_ok addNext_ok reduce_ok exec_eor3)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (Y C HI LO MID A₁ A₂ S₁ S₂ KP T U X₁ X₂ pa pk pb pl addFirst)

/-- Block `j` of the eight at `x9`, its halves swapped. -/
def blkV (s : State) (j : Nat) : BitVec 128 :=
  ext8 (s.mem.read (s.gpr .x9 + BitVec.ofNat 64 (16 * j)) 16) (s.mem.read (s.gpr .x9 + BitVec.ofNat 64 (16 * j)) 16)

/-- The table's value at `x19 + o`. -/
def tblV (s : State) (o : Nat) : BitVec 128 := s.mem.read (s.gpr .x19 + BitVec.ofNat 64 o) 16

/-- A block loaded, its halves swapped. -/
theorem ld_ok (d : VReg) (j : Nat) (s : State) (hj : j < 8)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block (ld d j)) s fun s' => s'.v d = blkV s j ∧ VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil,
    Proof.Gcm.AArch64.Pmull.exec_ldrq (Nat.mul_mod_right 16 j) (by omega_using [hj]) hin, exec_ext8,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [v_setV, ite_true, blkV]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [v_setV, hr, ite_false]

/-- The rest of a pair: the keys loaded, the sums of the blocks' halves
packed, and the six products. -/
theorem pairTail_ok (p k l : Nat) (s : State) (hk : sOff k % 16 = 0 ∧ sOff k < 4096 * 16)
    (hl : sOff l % 16 = 0 ∧ sOff l < 4096 * 16) (hp : kOff p % 16 = 0 ∧ kOff p < 4096 * 16)
    (hink : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (sOff k)) 16)
    (hinl : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (sOff l)) 16)
    (hinp : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (kOff p)) 16) :
    WP isa (.block [.ldrq S₁ .x19 (sOff k), .ldrq S₂ .x19 (sOff l), .ldrq KP .x19 (kOff p),
      .vop (.perm .trn1 .d2 T A₁ A₂), .vop (.perm .trn2 .d2 U A₁ A₂), .vop (.logic .eor T T U),
      .vop (.pmull false X₁ A₁ S₁), .vop (.pmull true A₁ A₁ S₁),
      .vop (.pmull false X₂ A₂ S₂), .vop (.pmull true A₂ A₂ S₂),
      .vop (.pmull false U T KP), .vop (.pmull true T T KP)]) s fun s' =>
      s'.v X₁ = polyMul (vdword (s.v A₁) 0) (vdword (tblV s (sOff k)) 0) ∧
      s'.v A₁ = polyMul (vdword (s.v A₁) 1) (vdword (tblV s (sOff k)) 1) ∧
      s'.v X₂ = polyMul (vdword (s.v A₂) 0) (vdword (tblV s (sOff l)) 0) ∧
      s'.v A₂ = polyMul (vdword (s.v A₂) 1) (vdword (tblV s (sOff l)) 1) ∧
      s'.v U = polyMul (vdword (s.v A₁) 0 ^^^ vdword (s.v A₁) 1) (vdword (tblV s (kOff p)) 0) ∧
      s'.v T = polyMul (vdword (s.v A₂) 0 ^^^ vdword (s.v A₂) 1) (vdword (tblV s (kOff p)) 1) ∧
      VOnly [S₁, S₂, KP, T, U, X₁, A₁, X₂, A₂] s s' := by
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_ldrq hk.1 hk.2 hink, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_ldrq hl.1 hl.2 (by simpa only [gpr_setV, rd_setV, wr_setV] using hinl), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_ldrq hp.1 hp.2 (by simpa only [gpr_setV, rd_setV, wr_setV] using hinp), ?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_trn, exec_eor, exec_pmull0, exec_pmull1,
    Option.some.injEq, exists_eq_left', v_setV, gpr_setV, mem_setV, ite_true, ite_false, reduceCtorEq, tblV,
    trn_sum, vdword_ofVDwords0, vdword_ofVDwords1]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, by simp only [gpr_setV],
    by simp only [mem_setV], by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-- The table's offsets. -/
theorem sOff_ok (k : Nat) (hk : k ≤ 8) : sOff k % 16 = 0 ∧ sOff k < 4096 * 16 := by
  unfold sOff tblO Impl.AesGcmSiv.AArch64.revO; omega_using [hk]
theorem kOff_ok (p : Nat) (hp : p < 4) : kOff p % 16 = 0 ∧ kOff p < 4096 * 16 := by
  unfold kOff tblO Impl.AesGcmSiv.AArch64.revO; omega_using [hp]

/-- What `ghPart` reads. -/
structure GhIn (s : State) : Prop where
  blk : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (16 * j)) 16
  sw : ∀ k, 1 ≤ k → k ≤ 8 → InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (sOff k)) 16
  key : ∀ p < 4, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (kOff p)) 16

theorem GhIn.of {s s' : State} (h : GhIn s) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    GhIn s' :=
  ⟨fun j hj => by rw [hg, hrd, hwr]; exact h.blk j hj, fun k a b => by rw [hg, hrd, hwr]; exact h.sw k a b,
    fun p hp => by rw [hg, hrd, hwr]; exact h.key p hp⟩

/-- Pair `p` of blocks `a` and `b`, by the powers `k` and `l`. -/
theorem pair_ok (p a k b l : Nat) (y : Bool) (s : State) (hin : GhIn s) (hp : p < 4) (ha : a < 8)
    (hb : b < 8) (hk : 1 ≤ k ∧ k ≤ 8) (hl : 1 ≤ l ∧ l ≤ 8) :
    WP isa (.block (pair p a k b l y)) s fun s' =>
      s'.v X₁ = polyMul (vdword (blkV s a) 0) (vdword (tblV s (sOff k)) 0) ∧
      s'.v A₁ = polyMul (vdword (blkV s a) 1) (vdword (tblV s (sOff k)) 1) ∧
      s'.v X₂ = polyMul (vdword (blkV s b ^^^ (if y then s.v Y else 0)) 0) (vdword (tblV s (sOff l)) 0) ∧
      s'.v A₂ = polyMul (vdword (blkV s b ^^^ (if y then s.v Y else 0)) 1) (vdword (tblV s (sOff l)) 1) ∧
      s'.v U = polyMul (vdword (blkV s a) 0 ^^^ vdword (blkV s a) 1) (vdword (tblV s (kOff p)) 0) ∧
      s'.v T = polyMul (vdword (blkV s b ^^^ (if y then s.v Y else 0)) 0 ^^^
        vdword (blkV s b ^^^ (if y then s.v Y else 0)) 1) (vdword (tblV s (kOff p)) 1) ∧
      VOnly [A₁, A₂, S₁, S₂, KP, T, U, X₁, X₂] s s' := by
  unfold pair
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok A₁ a s ha (hin.blk a ha)) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok A₂ b s₁ hb (by rw [o₁.rd, o₁.wr, o₁.gpr]; exact hin.blk b hb)) fun s₂ ⟨l₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addY_ok y s₂) fun s₃ ⟨e₃, o₃⟩ => ?_
  have o₁₃ := o₁.trans (o₂.trans o₃)
  have hin₃ := hin.of o₁₃.gpr o₁₃.rd o₁₃.wr
  refine WP.mono (pairTail_ok p k l s₃ (sOff_ok k hk.2) (sOff_ok l hl.2) (kOff_ok p hp)
    (hin₃.sw k hk.1 hk.2) (hin₃.sw l hl.1 hl.2) (hin₃.key p hp))
    fun s' ⟨h1, h2, h3, h4, h5, h6, o⟩ => ?_
  have hA₁ : s₃.v A₁ = blkV s a := by
    rw [o₃.v A₁ (by decide), o₂.v A₁ (by decide), l₁]
  have hA₂ : s₃.v A₂ = blkV s b ^^^ (if y then s.v Y else 0) := by
    rw [e₃, l₂, o₂.v Y (by decide), o₁.v Y (by decide)]
    simp only [blkV, o₁.mem, o₁.gpr]
  have ht : ∀ o, tblV s₃ o = tblV s o := fun o => by simp only [tblV, o₁₃.mem, o₁₃.gpr]
  rw [hA₁] at h1 h2 h5
  rw [hA₂] at h3 h4 h6
  simp only [ht] at h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6, (o₁₃.trans o).weaken⟩

/-! ## The sums -/

/-- A pair's products added, as `Proof.Gcm.AArch64.Stitch.addNext_ok`. -/
theorem addNext3_ok (e3 : Bool) (s : State) :
    WP isa (.block (addNext3 e3)) s fun s' =>
      prodS s' = ⟨s.v LO ^^^ s.v A₁ ^^^ s.v A₂, s.v MID ^^^ s.v U ^^^ s.v T, s.v HI ^^^ s.v X₁ ^^^ s.v X₂⟩ ∧
        VOnly [HI, LO, MID] s s' := by
  cases e3
  · apply WP.of_runBlock
    simp only [addNext3, xor3, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec_eor, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
      by simp only [wr_setV], by simp only [sp_setV]⟩⟩
    · simp only [prodS, v_setV, ite_true, ite_false, reduceCtorEq]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]
  · exact addNext_ok s

/-- The reduction, as `Proof.Gcm.AArch64.Stitch.reduce_ok`. -/
theorem reduce3_ok (e3 : Bool) (s : State)
    (hc : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) :
    WP isa (.block (reduce3 e3)) s fun s' =>
      s'.v Y = Proof.Gcm.AArch64.Pmull.reduce (fix (prodS s)) ∧ VOnly [T, U, MID, HI, Y] s s' := by
  cases e3
  · have hc0 : vdword (ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) 0 =
      Impl.Gcm.AArch64.Pmull.poly := vdword_append_0 _ _
    apply WP.of_runBlock
    simp only [reduce3, xor3, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec_pmull0, exec_ext8, exec_eor, Option.some.injEq, exists_eq_left', v_setV,
      ite_true, ite_false, reduceCtorEq, hc]
    refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
      by simp only [wr_setV], by simp only [sp_setV]⟩⟩
    · simp only [hc0, Proof.Gcm.AArch64.Pmull.reduce, fix, prodS]
      have e : s.v MID ^^^ (ext8 (s.v LO) (s.v LO) ^^^ s.v LO ^^^ s.v HI) ^^^
          polyMul (vdword (s.v LO) 0) Impl.Gcm.AArch64.Pmull.poly =
          s.v MID ^^^ s.v HI ^^^ s.v LO ^^^ ext8 (s.v LO) (s.v LO) ^^^
            polyMul (vdword (s.v LO) 0) Impl.Gcm.AArch64.Pmull.poly := by
        ac_rfl
      rw [e]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  · exact reduce_ok s hc

/-! ## The part -/

/-- The products of pair `p`, added to `pv`. -/
def pairP (s : State) (pv : Prod) (p : Nat) : Prod :=
  kpair pv (blkV s (pa p)) (tblV s (sOff (pk p))) (blkV s (pb p) ^^^ (if p = 3 then s.v Y else 0))
    (tblV s (sOff (pl p))) (tblV s (kOff p))

theorem pairAdd_ok (e3 : Bool) (p : Nat) (hp : p < 4) (first : Bool) (s₀ s : State) (hin : GhIn s₀)
    (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hy : s.v Y = s₀.v Y) :
    WP isa (.block (pair p (pa p) (pk p) (pb p) (pl p) (decide (p = 3)) ++ (if first then addFirst else addNext3 e3)))
      s fun s' => prodS s' = pairP s₀ (if first then ⟨0, 0, 0⟩ else prodS s) p ∧ VOnly pairV s s' := by
  have hin' := hin.of hg hrd hwr
  rw [WP.block_append_iff]
  have hpa : pa p < 8 := by unfold pa; split <;> omega_using []
  have hpb : pb p < 8 := by unfold pb; split <;> omega_using []
  have hpk : 1 ≤ pk p ∧ pk p ≤ 8 := by unfold pk; split <;> omega_using []
  have hpl : 1 ≤ pl p ∧ pl p ≤ 8 := by unfold pl; split <;> omega_using []
  refine WP.mono (pair_ok p (pa p) (pk p) (pb p) (pl p) (decide (p = 3)) s hin' hp hpa hpb hpk hpl)
    fun s₁ ⟨h1, h2, h3, h4, h5, h6, o₁⟩ => ?_
  have eb : ∀ j, blkV s j = blkV s₀ j := fun j => by simp only [blkV, hm, hg]
  have et : ∀ o, tblV s o = tblV s₀ o := fun o => by simp only [tblV, hm, hg]
  cases first
  · refine WP.mono (addNext3_ok e3 s₁) fun s' ⟨e, o⟩ => ⟨?_, (o₁.trans o).weaken⟩
    rw [e, h1, h2, h3, h4, h5, h6, o₁.v LO (by decide), o₁.v MID (by decide), o₁.v HI (by decide)]
    simp only [pairP, kpair, Proof.Gcm.AArch64.Stitch.kadd, prodS, decide_eq_true_eq, hy, eb, et,
      Bool.false_eq_true, ite_false]
  · refine WP.mono (addFirst_ok s₁) fun s' ⟨e, o⟩ => ⟨?_, (o₁.trans o).weaken⟩
    rw [e, h1, h2, h3, h4, h5, h6]
    simp only [pairP, kpair, Proof.Gcm.AArch64.Stitch.kadd, BitVec.ofNat_eq_ofNat, BitVec.zero_xor, ite_true,
      decide_eq_true_eq, hy, eb, et]

theorem ghPart_eq (e3 : Bool) : ghPart e3 =
    (pair 0 (pa 0) (pk 0) (pb 0) (pl 0) (decide (0 = 3)) ++ (if true then addFirst else addNext3 e3)) ++
    ((pair 1 (pa 1) (pk 1) (pb 1) (pl 1) (decide (1 = 3)) ++ (if false then addFirst else addNext3 e3)) ++
    ((pair 2 (pa 2) (pk 2) (pb 2) (pl 2) (decide (2 = 3)) ++ (if false then addFirst else addNext3 e3)) ++
    ((pair 3 (pa 3) (pk 3) (pb 3) (pl 3) (decide (3 = 3)) ++ (if false then addFirst else addNext3 e3)) ++
    reduce3 e3))) := by
  simp only [ghPart, List.append_assoc]; rfl

theorem ghPart_ok (e3 : Bool) (s : State) (hin : GhIn s)
    (hc : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) :
    WP isa (.block (ghPart e3)) s fun s' =>
      s'.v Y = gh8V (s.v Y) (blkV s) (fun k => tblV s (sOff k)) (fun p => tblV s (kOff p)) ∧
        VOnly ghV s s' := by
  rw [ghPart_eq e3, WP.block_append_iff]
  refine WP.mono (pairAdd_ok e3 0 (by decide) true s s hin rfl rfl rfl rfl rfl) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairAdd_ok e3 1 (by decide) false s s₁ hin o₁.gpr o₁.mem o₁.rd o₁.wr (o₁.v Y (by decide)))
    fun s₂ ⟨p₂, o₂⟩ => ?_
  have O₂ := (o₁.trans o₂).weaken (rs' := pairV)
  rw [WP.block_append_iff]
  refine WP.mono (pairAdd_ok e3 2 (by decide) false s s₂ hin O₂.gpr O₂.mem O₂.rd O₂.wr (O₂.v Y (by decide)))
    fun s₃ ⟨p₃, o₃⟩ => ?_
  have O₃ := (O₂.trans o₃).weaken (rs' := pairV)
  rw [WP.block_append_iff]
  refine WP.mono (pairAdd_ok e3 3 (by decide) false s s₃ hin O₃.gpr O₃.mem O₃.rd O₃.wr (O₃.v Y (by decide)))
    fun s₄ ⟨p₄, o₄⟩ => ?_
  have O₄ := (O₃.trans o₄).weaken (rs' := pairV)
  refine WP.mono (reduce3_ok e3 s₄ (by rw [O₄.v C (by decide), hc])) fun s' ⟨e, o⟩ => ⟨?_, (O₄.trans o).weaken⟩
  rw [e, p₄, p₃, p₂, p₁]
  simp only [ite_true, Bool.false_eq_true, ite_false, gh8V, pairP]

end VG.Proof.AesGcmSiv.AArch64.Stitch

end

end


/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: one batch

Untrusted: everything here is checked by Lean. The loops of
`Impl.AesGcmSiv.AArch64.Stitch` run on the data at `D`, `nb` batches of
eight blocks, with the working space `W` in `x19` and the encryption key's
schedule `K` in `x15`, from the memory `m₀` (`Ctx`), which holds the counter
block at `W + 96` and the table of keys of `H` at `W + tblO` (`KPre`).
`aesStep` is the counter mode of a batch (the blocks of the keystream `ks`,
RFC 8452's counter blocks), `stores_ok` the eight blocks it computes
stored, and `ghStep` GHASH of a batch (POLYVAL's blocks, as numbers).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq st)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly pp)
open VG.Proof.Gcm.AArch64.Stitch (aesV gh8V kpack Gh8Ok read_eq_readW range_map_add ghashFrom_append gh8V_congr
  dataInv_store1)
open VG.Spec.Gcm (Block ghashFrom)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (breg Y C pk pl stores)

/-- What the loops run on. -/
structure Ctx where
  /-- The working space (`x19`). -/
  W : Addr
  /-- The encryption key's schedule (`x15`). -/
  K : Addr
  /-- The data. -/
  D : Addr
  /-- The rounds. -/
  nr : Nat
  /-- The batches of eight blocks. -/
  nb : Nat
  /-- GHASH's key, of which the table holds the powers. -/
  H : Block
  /-- The memory before the loops. -/
  m₀ : Mem
  rd : List Region
  wr : List Region

namespace Ctx
variable (σ : Ctx)

abbrev dR : Region := ⟨σ.D, 128 * σ.nb⟩
abbrev kR : Region := ⟨σ.K, 16 * (σ.nr + 1)⟩
abbrev cR : Region := ⟨σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO, 16⟩
abbrev tR : Region := ⟨σ.W + BitVec.ofNat 64 tblO, 192⟩
/-- The key schedule, and the counter block's first word. -/
abbrev sch : List Byte := Spec.Aes.bytesAt σ.m₀ σ.K (16 * (σ.nr + 1))
abbrev c0 : BitVec 32 := σ.m₀.readW (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) 32
/-- Counter block `q`, and the keystream, byte by byte. -/
abbrev cv (q : Nat) : BitVec 128 :=
  setLane (σ.m₀.readW (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) 128) 32 0 (σ.c0 + BitVec.ofNat 32 q)
abbrev ks (i : Nat) : Byte := (Spec.Aes.cipher σ.nr σ.sch (st (σ.cv (i / 16)))).getD (i % 16) 0
/-- Block `i` of the data as it was, as a number, and decrypted. -/
abbrev blockO (i : Nat) : Block := σ.m₀.readW (σ.D + BitVec.ofNat 64 (16 * i)) 128

end Ctx

/-- The table of keys of `H` at `W + tblO` (as AES-GCM's,
`Proof.Gcm.AArch64.Stitch.TblOk`). -/
structure TblOk (m : Mem) (W : Addr) (H : Block) : Prop where
  sw : ∀ k, 1 ≤ k → k ≤ 8 → m.readW (W + BitVec.ofNat 64 (sOff k)) 128 = ext8 (pp H k) (pp H k)
  key : ∀ p < 4, m.readW (W + BitVec.ofNat 64 (kOff p)) 128 = kpack H (pk p) (pl p)

/-- What the counter mode of the loops needs of the context. -/
structure KPreC (σ : Ctx) : Prop where
  rounds : σ.nr = 10 ∨ σ.nr = 12 ∨ σ.nr = 14
  nb1 : 1 ≤ σ.nb
  n16 : 128 * σ.nb < 2 ^ 64
  k_in : InRegions (σ.rd ++ σ.wr) σ.K (16 * (σ.nr + 1))
  c_in : InRegions (σ.rd ++ σ.wr) (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) 16
  d_in : InRegions σ.wr σ.D (128 * σ.nb)
  d_k : σ.dR.Disjoint σ.kR
  d_c : σ.dR.Disjoint σ.cR
  wrap_c : σ.W.toNat + Impl.AesGcmSiv.AArch64.cbO + 16 ≤ 2 ^ 64
  wrap_k : σ.K.toNat + 16 * (σ.nr + 1) ≤ 2 ^ 64

/-- What the loops need of the context, with the table of keys. -/
structure KPre (σ : Ctx) : Prop extends KPreC σ where
  t_in : InRegions (σ.rd ++ σ.wr) (σ.W + BitVec.ofNat 64 tblO) 192
  d_t : σ.dR.Disjoint σ.tR
  wrap_t : σ.W.toNat + tblO + 192 ≤ 2 ^ 64
  tbl : TblOk σ.m₀ σ.W σ.H

namespace KPreC
variable {σ : Ctx} (hp : KPreC σ)
include hp

theorem k_frame {m : Mem} (hf : Frame [σ.dR] σ.m₀ m) : Spec.Aes.bytesAt m σ.K (16 * (σ.nr + 1)) = σ.sch :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.d_k.symm) (by have := hp.wrap_k; omega_arith)

theorem c_frame {m : Mem} (hf : Frame [σ.dR] σ.m₀ m) {w : Nat} (hw : w = 32 ∨ w = 128) :
    m.readW (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) w =
      σ.m₀.readW (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) w := by
  rcases hw with rfl | rfl
  · exact hf.readW (r := σ.cR) (by simp [Region.Contains])
      (by simp only [List.mem_singleton, forall_eq]; exact hp.d_c.symm) (by decide)
  · exact hf.readW (r := σ.cR) (by simp [Region.Contains])
      (by simp only [List.mem_singleton, forall_eq]; exact hp.d_c.symm) (by decide)

end KPreC

namespace KPre
variable {σ : Ctx} (hp : KPre σ)
include hp

theorem t_frame {m : Mem} (hf : Frame [σ.dR] σ.m₀ m) {o : Nat} (ho : o + 16 ≤ 192) :
    m.readW (σ.W + BitVec.ofNat 64 tblO + BitVec.ofNat 64 o) 128 =
      σ.m₀.readW (σ.W + BitVec.ofNat 64 tblO + BitVec.ofNat 64 o) 128 :=
  hf.readW (r := σ.tR) (Offset.contains_base _ (by omega_arith) (by have := hp.wrap_t; omega_arith))
    (by simp only [List.mem_singleton, forall_eq]; exact hp.d_t.symm) (by decide)

end KPre

theorem inRegions_app {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem Ctx.ks_eq (σ : Ctx) (q : Nat) {t : Nat} (ht : t < 16) :
    σ.ks (16 * q + t) = (Spec.Aes.cipher σ.nr σ.sch (st (σ.cv q))).getD t 0 := by
  simp only [Ctx.ks]
  rw [show (16 * q + t) / 16 = q by omega_arith, show (16 * q + t) % 16 = t by omega_arith]

/-! ## Storing a batch -/

/-- The eight blocks of batch `c` stored at `x9 + o`. -/
theorem stores_ok {σ : Ctx} (hp : KPreC σ) {c o : Nat} (hc : c < σ.nb) (ho : o ≤ 128) (ho16 : o % 16 = 0)
    (u : State) (hx9 : u.gpr .x9 + BitVec.ofNat 64 o = σ.D + BitVec.ofNat 64 (128 * c))
    (hdata : DataInv σ.m₀ u.mem σ.D (8 * σ.nb) (8 * c) σ.ks) (hwr : u.wr = σ.wr)
    (hv : ∀ j < 8, ∀ t < 16, vbyte (u.v (breg j)) t =
      σ.ks (16 * (8 * c + j) + t) ^^^ σ.m₀ (σ.D + BitVec.ofNat 64 (16 * (8 * c + j) + t))) :
    WP isa (.block (stores o)) u fun u' =>
      DataInv σ.m₀ u'.mem σ.D (8 * σ.nb) (8 * (c + 1)) σ.ks ∧ Frame [σ.dR] u.mem u'.mem ∧
        u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := hp.n16
  refine WP.mono (wp_range_flatMap (M := isa) (fun j u' =>
      DataInv σ.m₀ u'.mem σ.D (8 * σ.nb) (8 * c + j) σ.ks ∧ Frame [σ.dR] u.mem u'.mem ∧
        u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr)
    (fun j u₁ hj ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_) 8 (Nat.le_refl _) u
    ⟨hdata, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩) fun u' ⟨d, f, g, v, sp, rd, wr⟩ =>
      ⟨by rw [show 8 * (c + 1) = 8 * c + 8 by omega_arith]; exact d, f, g, v, sp, rd, wr⟩
  have ha : u₁.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * c + j)) := by
    rw [g₁, ← Offset.add_add, hx9, Offset.add_add_eq _ (show 128 * c + 16 * j = 16 * (8 * c + j) by omega_arith)]
  have hw : InRegions u₁.wr (u₁.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16 := by
    rw [ha, wr₁, hwr]
    exact CallLay.inRegions_sub hp.d_in (by omega_arith) (by omega_arith)
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (by omega_arith) hw, WP.block_nil ?_⟩
  rw [ha]
  have hst := dataInv_store1 (v := u₁.v (breg j)) (by omega_arith) (by omega_arith) d₁ fun t ht => by
    rw [v₁, hv j hj t ht]
  refine ⟨hst.1, f₁.trans ?_, g₁, v₁, sp₁, rd₁, wr₁⟩
  exact hst.2.sub fun r hr => ⟨σ.dR, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega_arith)⟩

/-! ## Counter mode -/

/-- Counter mode of batch `c`, from the data at `x9 + o`. -/
theorem aesStep (e3 : Bool) {σ : Ctx} (hp : KPreC σ) {c o : Nat} {s : State} (hc : c < σ.nb) (ho' : o ≤ 128) (ho16 : o % 16 = 0)
    (hx9 : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * c + j)))
    (hx10 : s.read .w .x10 = σ.c0 + BitVec.ofNat 32 (8 * c))
    (hx19 : s.gpr .x19 = σ.W) (hx15 : s.gpr .x15 = σ.K) (hrdwr : s.rd ++ s.wr = σ.rd ++ σ.wr)
    (hf : Frame [σ.dR] σ.m₀ s.mem) (hdata : DataInv σ.m₀ s.mem σ.D (8 * σ.nb) (8 * c) σ.ks) :
    WP isa (.block (aesPart e3 σ.nr o)) s fun t =>
      (∀ j < 8, ∀ tt < 16, vbyte (t.v (breg j)) tt =
        σ.ks (16 * (8 * c + j) + tt) ^^^ σ.m₀ (σ.D + BitVec.ofNat 64 (16 * (8 * c + j) + tt))) ∧
      t.read .w .x10 = σ.c0 + BitVec.ofNat 32 (8 * (c + 1)) ∧ Fr [.x10, .x12] aesV s t := by
  have hn := hp.n16
  have hR := hp.rounds
  have hc0 : c0 s = σ.c0 := by rw [c0, cbA, hx19, hp.c_frame hf (.inl rfl)]
  have hA : APre σ.nr o (8 * c) s := {
    rounds := hR
    o_le := ho'
    keys := fun r hr => by
      rw [hrdwr, hx15]; exact CallLay.inRegions_sub hp.k_in (by omega_arith) (by omega_arith)
    ctr := by rw [hrdwr, cbA, hx19]; exact hp.c_in
    data := fun j hj => by
      rw [hrdwr, hx9]
      exact inRegions_app (CallLay.inRegions_sub (off := 16 * (8 * c + j)) (l := 16) (n := 128 * σ.nb) hp.d_in (by omega_arith) (by omega_arith))
    x10 := by rw [hx10, hc0] }
  refine WP.mono (aesPart_ok e3 hA ho16) fun t ⟨out, x10, fr⟩ => ⟨fun j hj tt htt => ?_, ?_, fr⟩
  · rw [out j hj tt htt, sch, hx15, hp.k_frame hf, hx9, Offset.add_add, hdata _ (by omega_arith),
      ite_eq_right (by omega_arith), show ∀ b : Byte, b ^^^ 0 = b from fun _ => BitVec.xor_zero]
    have hcv : cvec s (8 * c) j = σ.cv (8 * c + j) := by
      simp only [cvec, Ctx.cv]
      rw [cbA, hx19, hp.c_frame hf (.inr rfl), ← hc0, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [hcv, σ.ks_eq _ htt]
  · rw [x10, hc0, show 8 * c + 8 = 8 * (c + 1) by omega_arith]

/-! ## POLYVAL -/

/-- GHASH from `y`, by `H`, of the first `n` blocks of `hb`. -/
abbrev yh (H y : Block) (hb : Nat → Block) (n : Nat) : Block := ghashFrom H y ((List.range n).map hb)

/-- GHASH of the eight blocks at `x9`, the blocks `hb (8 h + j)` as numbers. -/
theorem ghStep (e3 : Bool) {σ : Ctx} (hp : KPre σ) (gh : Gh8Ok) {y : Block} {hb : Nat → Block} {h : Nat} {t : State}
    (hy : t.v Y = ext8 (yh σ.H y hb (8 * h)) (yh σ.H y hb (8 * h)))
    (hc : t.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly)
    (hx9 : t.gpr .x9 = σ.D + BitVec.ofNat 64 (128 * h)) (hh : h < σ.nb)
    (hx19 : t.gpr .x19 = σ.W) (hrdwr : t.rd ++ t.wr = σ.rd ++ σ.wr)
    (hf : Frame [σ.dR] σ.m₀ t.mem)
    (hb' : ∀ j < 8, t.mem.readW (σ.D + BitVec.ofNat 64 (16 * (8 * h + j))) 128 = hb (8 * h + j)) :
    WP isa (.block (ghPart e3)) t fun u =>
      u.v Y = ext8 (yh σ.H y hb (8 * (h + 1))) (yh σ.H y hb (8 * (h + 1))) ∧ VOnly Proof.Gcm.AArch64.Stitch.ghV t u := by
  have hn := hp.n16
  have ha : ∀ j, t.gpr .x9 + BitVec.ofNat 64 (16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * h + j)) :=
    fun j => by rw [hx9, Offset.add_add_eq _ (show 128 * h + 16 * j = 16 * (8 * h + j) by omega_arith)]
  have ht : ∀ o, o + 16 ≤ 192 → t.gpr .x19 + BitVec.ofNat 64 (tblO + o) =
      σ.W + BitVec.ofNat 64 tblO + BitVec.ofNat 64 o := fun o _ => by rw [hx19, Offset.add_add]
  have hin : GhIn t := {
    blk := fun j hj => by
      rw [hrdwr, ha]
      exact inRegions_app (CallLay.inRegions_sub (off := 16 * (8 * h + j)) (l := 16) (n := 128 * σ.nb) hp.d_in (by omega_arith) (by omega_arith))
    sw := fun k hk1 hk8 => by
      rw [hrdwr, show sOff k = tblO + 16 * (k - 1) from rfl, ht _ (by omega_arith)]
      exact CallLay.inRegions_sub hp.t_in (by omega_arith) (by omega_arith)
    key := fun p hp' => by
      rw [hrdwr, show kOff p = tblO + (128 + 16 * p) by unfold kOff; omega_arith, ht _ (by omega_arith)]
      exact CallLay.inRegions_sub hp.t_in (by omega_arith) (by omega_arith) }
  refine WP.mono (ghPart_ok e3 t hin hc) fun u ⟨e, o⟩ => ⟨?_, o⟩
  rw [e, hy, gh8V_congr rfl (b' := fun j => ext8 (hb (8 * h + j)) (hb (8 * h + j)))
    (S' := fun k => ext8 (pp σ.H k) (pp σ.H k))
    (KP' := fun p => kpack σ.H (pk p) (pl p))
    (fun j hj => by rw [blkV, ha, read_eq_readW, hb' j hj])
    (fun k hk1 hk8 => by
      rw [tblV, read_eq_readW, show sOff k = tblO + 16 * (k - 1) from rfl, ht _ (by omega_arith), hp.t_frame hf (by omega_arith),
        Offset.add_add, show tblO + 16 * (k - 1) = sOff k from rfl]
      exact hp.tbl.sw k hk1 hk8)
    (fun p hp' => by
      rw [tblV, read_eq_readW, show kOff p = tblO + (128 + 16 * p) by unfold kOff; omega_arith, ht _ (by omega_arith),
        hp.t_frame hf (by omega_arith), Offset.add_add, show tblO + (128 + 16 * p) = kOff p by unfold kOff; omega_arith]
      exact hp.tbl.key p hp'), gh, yh, yh, show 8 * (h + 1) = 8 * h + 8 by omega_arith, range_map_add hb (8 * h),
    ghashFrom_append]

/-! ## The pointer and the count -/

theorem adv_ok {D : Addr} {nb : Nat} {u : State} {h c : Nat} (hc : c < nb)
    (hx9 : u.gpr .x9 = D + BitVec.ofNat 64 (128 * h))
    (hx11 : u.gpr .x11 = BitVec.ofNat 64 (nb - c)) :
    WP isa (.block adv) u fun u' =>
      u'.gpr .x9 = D + BitVec.ofNat 64 (128 * (h + 1)) ∧
      u'.gpr .x11 = BitVec.ofNat 64 (nb - (c + 1)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x11 → u'.gpr r = u.gpr r) ∧ u'.v = u.v ∧ u'.mem = u.mem ∧
      u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  rw [adv, WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨?_, ?_, fun r h9 h11 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, BitVec.setWidth_eq, hx9]
    rw [Offset.add_add_eq _ (show 128 * h + 128 = 128 * (h + 1) by omega_arith)]
  · rw [gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, BitVec.setWidth_eq, gpr_write_of_ne _ _ _ (show Reg.x11 ≠ Reg.x9 by decide), hx11]
    rw [Offset.ofNat_sub_ofNat (by omega_arith), show nb - c - 1 = nb - (c + 1) by omega_arith]
  · rw [gpr_write_of_ne _ _ _ h11, gpr_write_of_ne _ _ _ h9]

end VG.Proof.AesGcmSiv.AArch64.Stitch

end

end

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: the loops

Untrusted: everything here is checked by Lean. From a context `σ` meeting
`KPre`:

* `ghLoop_ok`: `ghLoop` leaves in `Y` GHASH of the `8 nb` blocks of the data
  (as numbers, POLYVAL's blocks) from the `Y` it starts from, and writes no
  memory;
* `ctrLoop_ok`: `ctrLoop nr` XORs the data with the keystream (`DataInv`);
* `openLoop_ok`: `openLoop nr` does both, GHASH of the data as XORed
  (`blockC`, the blocks of `mDec`): batch `i + 1` XORed while batch `i` is
  hashed, woven (`parts_ok`, the parts independent, checked once).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq eval_zero eval_nonzero)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok fuse_flatten flatten_singles ghV)
open VG.Spec.Gcm (Block ghashFrom)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (breg Y C stores byRounds)

/-! ## The data XORed with the keystream -/

namespace Ctx
variable (σ : Ctx)

/-- The memory with the data XORed with the keystream. -/
def mDec : Mem := fun a =>
  σ.m₀ a ^^^ (if (a - σ.D).toNat < 16 * (8 * σ.nb) then σ.ks (a - σ.D).toNat else 0)

/-- Block `i` of the data XORed, as a number. -/
abbrev blockC (i : Nat) : Block := σ.mDec.readW (σ.D + BitVec.ofNat 64 (16 * i)) 128

end Ctx

theorem readW_of_dataInv {σ : Ctx} (hn : 128 * σ.nb < 2 ^ 64) {m : Mem} {k : Nat}
    (h : DataInv σ.m₀ m σ.D (8 * σ.nb) k σ.ks) {i : Nat} (hi : i < k) (hk : k ≤ 8 * σ.nb) :
    m.readW (σ.D + BitVec.ofNat 64 (16 * i)) 128 = σ.blockC i := by
  refine Mem.readW_congr fun t ht => ?_
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (by omega_arith), Ctx.mDec, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), ite_eq_left (by omega_arith)]

/-! ## The number of rounds -/

theorem byRounds_ok {nr : Nat} (hR : nr = 10 ∨ nr = 12 ∨ nr = 14) {f : Nat → Prog isa} {P Q : State → Prop}
    {s : State} (hx22 : s.gpr .x22 = BitVec.ofNat 64 nr)
    (hst : ∀ s', (∀ r, r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) → s'.v = s.v → s'.mem = s.mem →
      s'.sp = s.sp → s'.rd = s.rd → s'.wr = s.wr → P s')
    (hf : ∀ s, P s → WP isa (f nr) s Q) :
    WP isa (byRounds f) s Q := by
  rw [byRounds, WP.seq_iff, WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 12) (by decide), WP.block_nil ?_⟩
  have hP' := hst ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
      ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12))
    (fun r h13 h14 => by rw [gpr_write_of_ne _ _ _ h14, gpr_write_of_ne _ _ _ h13]) rfl rfl rfl rfl rfl
  have e13 : ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
      ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12)).gpr .x13 =
      BitVec.ofNat 64 (nr - 10) := by
    simp only [gpr_write_of_ne _ _ _ (show Reg.x13 ≠ Reg.x14 by decide), gpr_write_self, State.read,
      BitVec.setWidth_eq, hx22, Size.bits]
    rw [Offset.ofNat_sub_ofNat (by omega_arith)]
  refine WP.ite _ (eval_zero e13 (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h10 : nr = 10 := by simp only [decide_eq_true_eq] at h; omega_arith
    have e := hf _ hP'
    rw [h10] at e; exact e
  · have hge : 12 ≤ nr := by simp only [decide_eq_false_iff_not] at h; omega_arith
    have e14 : ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
        ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12)).gpr .x14 =
        BitVec.ofNat 64 (nr - 12) := by
      simp only [gpr_write_self, State.read, BitVec.setWidth_eq,
        gpr_write_of_ne _ _ _ (show Reg.x22 ≠ Reg.x13 by decide), hx22, Size.bits]
      rw [Offset.ofNat_sub_ofNat (by omega_arith)]
    refine WP.ite _ (eval_zero e14 (by omega_arith)) (fun h' => ?_) (fun h' => ?_)
    · have h12 : nr = 12 := by simp only [decide_eq_true_eq] at h'; omega_arith
      have e := hf _ hP'
      rw [h12] at e; exact e
    · have h14 : nr = 14 := by simp only [decide_eq_false_iff_not] at h'; omega_arith
      have e := hf _ hP'
      rw [h14] at e; exact e

/-! ## POLYVAL of the batches -/

/-- After `h` batches hashed, from `s₀`. -/
structure GInv (σ : Ctx) (y : Block) (s₀ : State) (h : Nat) (s : State) : Prop where
  le : h ≤ σ.nb
  x9 : s.gpr .x9 = σ.D + BitVec.ofNat 64 (128 * h)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (σ.nb - h)
  gpr : ∀ r, r ≠ .x9 → r ≠ .x11 → s.gpr r = s₀.gpr r
  y : s.v Y = ext8 (yh σ.H y σ.blockO (8 * h)) (yh σ.H y σ.blockO (8 * h))
  cr : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly
  mem : s.mem = σ.m₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ghLoop_ok (e3 : Bool) {σ : Ctx} (hp : KPre σ) (gh : Gh8Ok) {y : Block} {s₀ : State}
    (hx19 : s₀.gpr .x19 = σ.W) (hrdwr : s₀.rd ++ s₀.wr = σ.rd ++ σ.wr) (hI : GInv σ y s₀ 0 s₀) :
    WP isa (ghLoop e3) s₀ (GInv σ y s₀ σ.nb) := by
  have hn := hp.n16
  have h1 := hp.nb1
  let I : Nat → State → Prop := fun m s => ∃ h, m = σ.nb - h ∧ h < σ.nb ∧ GInv σ y s₀ h s
  have hstep : ∀ m s, I m s → WP isa (.block (ghPart e3 ++ adv)) s (fun s' =>
      (AArch64.eval (.nonzero .x .x11) s' = some false ∧ GInv σ y s₀ σ.nb s') ∨
      (AArch64.eval (.nonzero .x .x11) s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨h, rfl, hh, hI⟩
    rw [WP.block_append_iff]
    refine WP.mono (ghStep e3 hp gh (y := y) (hb := σ.blockO) (h := h) hI.y hI.cr hI.x9 hh
      (by rw [hI.gpr _ (by decide) (by decide), hx19]) (by rw [hI.rd, hI.wr, hrdwr])
      (by rw [hI.mem]; exact Frame.refl _ _) (fun j hj => by rw [hI.mem])) fun u ⟨hy, ou⟩ => ?_
    refine WP.mono (adv_ok (D := σ.D) (h := h) hh (by rw [ou.gpr, hI.x9]) (by rw [ou.gpr, hI.x11]))
      fun u' ⟨x9', x11', g', v', m', sp', rd', wr'⟩ => ?_
    have hI' : GInv σ y s₀ (h + 1) u' := {
      le := by omega_arith
      x9 := x9'
      x11 := by rw [x11', show σ.nb - (h + 1) = σ.nb - (h + 1) from rfl]
      gpr := fun r h9 h11 => by rw [g' r h9 h11, ou.gpr, hI.gpr r h9 h11]
      y := by rw [v', hy]
      cr := by rw [v', ou.v C (by decide), hI.cr]
      mem := by rw [m', ou.mem, hI.mem]
      sp := by rw [sp', ou.sp, hI.sp]
      rd := by rw [rd', ou.rd, hI.rd]
      wr := by rw [wr', ou.wr, hI.wr] }
    rw [eval_nonzero hI'.x11 (by omega_arith)]
    by_cases hl : σ.nb - (h + 1) = 0
    · have e : h + 1 = σ.nb := by omega_arith
      exact .inl ⟨by simp [hl], by rw [← e]; exact hI'⟩
    · exact .inr ⟨by simp [hl], σ.nb - (h + 1), by omega_arith, h + 1, rfl, by omega_arith, hI'⟩
  exact WP.loop (M := isa) I hstep _ _ ⟨0, rfl, by omega_arith, hI⟩

/-! ## Counter mode of the batches -/

/-- The registers the counter-mode loops write. -/
abbrev kRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

/-- After `c` batches XORed, from `s₀`, with `x9` at batch `p`. -/
structure CInv (σ : Ctx) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ σ.nb
  x9 : s.gpr .x9 = σ.D + BitVec.ofNat 64 (128 * p)
  x10 : s.read .w .x10 = σ.c0 + BitVec.ofNat 32 (8 * c)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (σ.nb - c)
  gpr : ∀ r, r ∉ kRegs → s.gpr r = s₀.gpr r
  data : DataInv σ.m₀ s.mem σ.D (8 * σ.nb) (8 * c) σ.ks
  frame : Frame [σ.dR] σ.m₀ s.mem
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem CInv.of_x1314 {σ : Ctx} {s₀ : State} {c p : Nat} {s s' : State} (hI : CInv σ s₀ c p s)
    (hg : ∀ r, r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : CInv σ s₀ c p s' where
  le := hI.le
  x9 := by rw [hg _ (by decide) (by decide), hI.x9]
  x10 := by simp only [State.read]; rw [hg _ (by decide) (by decide)]; exact hI.x10
  x11 := by rw [hg _ (by decide) (by decide), hI.x11]
  gpr r hr := by rw [hg r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])), hI.gpr r hr]
  data := by rw [hm]; exact hI.data
  frame := by rw [hm]; exact hI.frame
  sp := by rw [hsp, hI.sp]
  rd := by rw [hrd, hI.rd]
  wr := by rw [hwr, hI.wr]

theorem ctrLoop_ok (e3 : Bool) {σ : Ctx} (hp : KPreC σ) {s₀ : State}
    (hx19 : s₀.gpr .x19 = σ.W) (hx15 : s₀.gpr .x15 = σ.K) (hrdwr : s₀.rd ++ s₀.wr = σ.rd ++ σ.wr)
    (hwr : s₀.wr = σ.wr) {s : State} (hI : CInv σ s₀ 0 0 s) :
    WP isa (ctrLoop e3 σ.nr) s (CInv σ s₀ σ.nb σ.nb) := by
  have hn := hp.n16
  have h1 := hp.nb1
  let I : Nat → State → Prop := fun m s => ∃ c, m = σ.nb - c ∧ c < σ.nb ∧ CInv σ s₀ c c s
  have hstep : ∀ m s, I m s → WP isa (.block (aesPart e3 σ.nr 0 ++ stores 0 ++ adv)) s (fun s' =>
      (AArch64.eval (.nonzero .x .x11) s' = some false ∧ CInv σ s₀ σ.nb σ.nb s') ∨
      (AArch64.eval (.nonzero .x .x11) s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨c, rfl, hc, hI⟩
    rw [List.append_assoc, WP.block_append_iff]
    have hx9 : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (0 + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * c + j)) :=
      fun j => by rw [hI.x9, Offset.add_add_eq _ (show 128 * c + (0 + 16 * j) = 16 * (8 * c + j) by omega_arith)]
    refine WP.mono (aesStep e3 hp hc (by decide) (by decide) hx9 hI.x10 (by rw [hI.gpr _ (by decide), hx19])
      (by rw [hI.gpr _ (by decide), hx15]) (by rw [hI.rd, hI.wr, hrdwr]) hI.frame hI.data)
      fun t ⟨hv, x10t, frt⟩ => ?_
    have gt : ∀ r, r ≠ .x10 → r ≠ .x12 → t.gpr r = s.gpr r := fun r h1 h2 => frt.gpr r (by simp [h1, h2])
    rw [WP.block_append_iff]
    refine WP.mono (stores_ok hp hc (by decide) (by decide) t
      (by rw [gt _ (by decide) (by decide), hI.x9, BitVec.add_zero]) (by rw [frt.mem]; exact hI.data)
      (by rw [frt.wr, hI.wr, hwr]) hv) fun u ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
    refine WP.mono (adv_ok (D := σ.D) (h := c) hc (by rw [g₁, gt _ (by decide) (by decide), hI.x9])
      (by rw [g₁, gt _ (by decide) (by decide), hI.x11])) fun u' ⟨x9', x11', g', v', m', sp', rd', wr'⟩ => ?_
    have gall : ∀ r, r ≠ .x9 → r ≠ .x11 → u'.gpr r = t.gpr r := fun r h9 h11 => by rw [g' r h9 h11, g₁]
    have hI' : CInv σ s₀ (c + 1) (c + 1) u' := {
      le := by omega_arith
      x9 := x9'
      x10 := by
        simp only [State.read] at x10t ⊢
        rw [gall _ (by decide) (by decide)]; exact x10t
      x11 := x11'
      gpr := fun r hr => by
        simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [gall r hr.1 hr.2.2.1, gt r hr.2.1 hr.2.2.2.1, hI.gpr r (by simp [kRegs, hr.1, hr.2.1, hr.2.2.1,
          hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
      data := by rw [m']; exact d₁
      frame := by
        rw [m']
        have : s.mem = t.mem := frt.mem.symm
        exact hI.frame.trans (this ▸ f₁)
      sp := by rw [sp', sp₁, frt.sp, hI.sp]
      rd := by rw [rd', rd₁, frt.rd, hI.rd]
      wr := by rw [wr', wr₁, frt.wr, hI.wr] }
    rw [eval_nonzero hI'.x11 (by omega_arith)]
    by_cases hl : σ.nb - (c + 1) = 0
    · have e : c + 1 = σ.nb := by omega_arith
      exact .inl ⟨by simp [hl], by rw [← e]; exact hI'⟩
    · exact .inr ⟨by simp [hl], σ.nb - (c + 1), by omega_arith, c + 1, rfl, by omega_arith, hI'⟩
  exact WP.loop (M := isa) I hstep _ _ ⟨0, rfl, by omega_arith, hI⟩

/-! ## `open`'s loop -/

/-- The footprints of the parts' code; neither stores, so the base register
does not matter. -/
abbrev fps : VG.Interleave.Footprints isa := VG.AArch64.Interleave.footprints .x0

theorem parts_check : ∀ e3 : Bool, ∀ nr ∈ [10, 12, 14],
    ((fps.blockFp (aesPart e3 nr 128)).bind fun A => (fps.blockFp (ghPart e3)).map fun B => fps.indep A B) = some true := by
  decide +kernel

/-- The parts, woven, run as `aesPart` and then `ghPart`. -/
theorem parts_ok (e3 : Bool) {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {s : State}
    {Q : State → Prop} (h : WP isa (.block (aesPart e3 nr 128)) s fun t => WP isa (.block (ghPart e3)) t Q) :
    WP isa (.block (parts e3 nr 128)) s Q := by
  unfold parts
  refine VG.Interleave.WP.weaveG (P := fps.Inv) ?_ trivial ?_
  · rw [fuse_flatten, flatten_singles]
    exact fps.indeps_of_check (parts_check e3 nr (by rcases hnr with rfl | rfl | rfl <;> decide))
  · rw [fuse_flatten, flatten_singles]; exact h

/-- After `c` batches XORed and `h` hashed, from `s₀`: `x9` at batch `h`. -/
structure OInv (σ : Ctx) (y : Block) (s₀ : State) (c h : Nat) (s : State) : Prop where
  ci : CInv σ s₀ c h s
  y : s.v Y = ext8 (yh σ.H y σ.blockC (8 * h)) (yh σ.H y σ.blockC (8 * h))
  cr : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly

section
variable {σ : Ctx} (hp : KPre σ) (gh : Gh8Ok) {y : Block} {s₀ : State}
    (hx19 : s₀.gpr .x19 = σ.W) (hx15 : s₀.gpr .x15 = σ.K) (hrdwr : s₀.rd ++ s₀.wr = σ.rd ++ σ.wr)
    (hwr : s₀.wr = σ.wr)
include hp gh hx19 hx15 hrdwr hwr

/-- One iteration of `open`'s loop: batch `h + 1` XORed while batch `h` is
hashed, then stored. -/
theorem openBody_ok (e3 : Bool) {h : Nat} (hh : h + 1 < σ.nb) {s : State} (hI : OInv σ y s₀ (h + 1) h s) :
    WP isa (.block (parts e3 σ.nr 128 ++ stores 128 ++ adv)) s (OInv σ y s₀ (h + 2) (h + 1)) := by
  have hn := hp.n16
  have hct : ∀ j < 8, s.mem.readW (σ.D + BitVec.ofNat 64 (16 * (8 * h + j))) 128 = σ.blockC (8 * h + j) :=
    fun j hj => readW_of_dataInv hn hI.ci.data (by omega_arith) (by have := hI.ci.le; omega_arith)
  rw [List.append_assoc, WP.block_append_iff]
  refine parts_ok e3 hp.rounds ?_
  have hx9 : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (128 + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * (h + 1) + j)) :=
    fun j => by rw [hI.ci.x9, Offset.add_add_eq _ (show 128 * h + (128 + 16 * j) = 16 * (8 * (h + 1) + j) by omega_arith)]
  refine WP.mono (aesStep e3 hp.toKPreC hh (by decide) (by decide) hx9 hI.ci.x10 (by rw [hI.ci.gpr _ (by decide), hx19])
    (by rw [hI.ci.gpr _ (by decide), hx15]) (by rw [hI.ci.rd, hI.ci.wr, hrdwr]) hI.ci.frame hI.ci.data)
    fun t ⟨hv, x10t, frt⟩ => ?_
  have gt : ∀ r, r ≠ .x10 → r ≠ .x12 → t.gpr r = s.gpr r := fun r h1 h2 => frt.gpr r (by simp [h1, h2])
  refine WP.mono (ghStep e3 hp gh (y := y) (hb := σ.blockC) (h := h) (t := t) (by rw [frt.v _ (by decide), hI.y])
    (by rw [frt.v _ (by decide), hI.cr]) (by rw [gt _ (by decide) (by decide), hI.ci.x9]) (by omega_arith)
    (by rw [gt _ (by decide) (by decide), hI.ci.gpr _ (by decide), hx19])
    (by rw [frt.rd, frt.wr, hI.ci.rd, hI.ci.wr, hrdwr]) (by rw [frt.mem]; exact hI.ci.frame)
    (fun j hj => by rw [frt.mem]; exact hct j hj)) fun u ⟨hy, ou⟩ => ?_
  rw [WP.block_append_iff]
  have gu : ∀ r, r ≠ .x10 → r ≠ .x12 → u.gpr r = s.gpr r := fun r h1 h2 => by rw [ou.gpr, gt r h1 h2]
  refine WP.mono (stores_ok hp.toKPreC hh (by decide) (by decide) u (by rw [gu _ (by decide) (by decide), hI.ci.x9,
      Offset.add_add_eq _ (show 128 * h + 128 = 128 * (h + 1) by omega_arith)]) (by rw [ou.mem, frt.mem]; exact hI.ci.data)
    (by rw [ou.wr, frt.wr, hI.ci.wr, hwr])
    (fun j hj tt htt => by rw [ou.v _ (by unfold breg; split <;> decide)]; exact hv j hj tt htt))
    fun u₁ ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (adv_ok (D := σ.D) (h := h) (c := h + 1) hh (by rw [g₁, gu _ (by decide) (by decide), hI.ci.x9])
    (by rw [g₁, gu _ (by decide) (by decide), hI.ci.x11])) fun u' ⟨x9', x11', g', v', m', sp', rd', wr'⟩ => ?_
  have gall : ∀ r, r ≠ .x9 → r ≠ .x11 → u'.gpr r = u.gpr r := fun r h9 h11 => by rw [g' r h9 h11, g₁]
  refine ⟨⟨by omega_arith, x9', ?_, by rw [x11'], fun r hr => ?_, by rw [m']; exact d₁, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [State.read] at x10t ⊢
    rw [gall _ (by decide) (by decide), ou.gpr]; exact x10t
  · simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gall r hr.1 hr.2.2.1, gu r hr.2.1 hr.2.2.2.1, hI.ci.gpr r (by simp [kRegs, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  · rw [m']
    have : s.mem = u.mem := by rw [ou.mem, frt.mem]
    exact hI.ci.frame.trans (this ▸ f₁)
  · rw [sp', sp₁, ou.sp, frt.sp, hI.ci.sp]
  · rw [rd', rd₁, ou.rd, frt.rd, hI.ci.rd]
  · rw [wr', wr₁, ou.wr, frt.wr, hI.ci.wr]
  · rw [v', v₁, hy]
  · rw [v', v₁, ou.v C (by decide), frt.v C (by decide), hI.cr]

theorem openLoop_ok (e3 : Bool) {s : State} (hI : CInv σ s₀ 0 0 s)
    (hy : s.v Y = ext8 y y) (hc : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) :
    WP isa (openLoop e3 σ.nr) s (OInv σ y s₀ σ.nb σ.nb) := by
  have hn := hp.n16
  have h1 := hp.nb1
  unfold openLoop
  refine WP.seq ?_
  -- The first batch.
  rw [WP.block_append_iff, WP.block_append_iff]
  have hx9₀ : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (0 + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * 0 + j)) :=
    fun j => by rw [hI.x9, Offset.add_add_eq _ (show 128 * 0 + (0 + 16 * j) = 16 * (8 * 0 + j) by omega_arith)]
  refine WP.mono (aesStep e3 hp.toKPreC (c := 0) h1 (by decide) (by decide) hx9₀ hI.x10 (by rw [hI.gpr _ (by decide), hx19])
    (by rw [hI.gpr _ (by decide), hx15]) (by rw [hI.rd, hI.wr, hrdwr]) hI.frame hI.data)
    fun t ⟨hv, x10t, frt⟩ => ?_
  have gt : ∀ r, r ≠ .x10 → r ≠ .x12 → t.gpr r = s.gpr r := fun r h1 h2 => frt.gpr r (by simp [h1, h2])
  refine WP.mono (stores_ok hp.toKPreC (c := 0) (by omega_arith) (by decide) (by decide) t
    (by rw [gt _ (by decide) (by decide), hI.x9]; exact BitVec.add_zero _) (by rw [frt.mem]; exact hI.data)
    (by rw [frt.wr, hI.wr, hwr]) hv) fun u ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hI₁ : OInv σ y s₀ 1 0 (u.write .x .x11 (u.read .x .x11 - BitVec.ofNat 64 1)) := {
    ci := {
      le := h1
      x9 := by rw [gpr_write_of_ne _ _ _ (by decide), g₁, gt _ (by decide) (by decide), hI.x9]
      x10 := by
        simp only [State.read] at x10t ⊢
        rw [gpr_write_of_ne _ _ _ (by decide), g₁]; exact x10t
      x11 := by
        simp only [gpr_write_self, State.read, BitVec.setWidth_eq]
        rw [g₁, gt .x11 (by decide) (by decide), hI.x11, Nat.sub_zero, Offset.ofNat_sub_ofNat (by omega_arith)]
      gpr := fun r hr => by
        simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [gpr_write_of_ne _ _ _ hr.2.2.1, g₁, gt r hr.2.1 hr.2.2.2.1, hI.gpr r (by simp [kRegs, hr.1, hr.2.1,
          hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
      data := by rw [mem_write]; exact d₁
      frame := by rw [mem_write]; exact hI.frame.trans (frt.mem ▸ f₁)
      sp := by rw [sp_write, sp₁, frt.sp, hI.sp]
      rd := by rw [rd_write, rd₁, frt.rd, hI.rd]
      wr := by rw [wr_write, wr₁, frt.wr, hI.wr] }
    y := by rw [v_write, v₁, frt.v _ (by decide), hy]; rfl
    cr := by rw [v_write, v₁, frt.v _ (by decide), hc] }
  -- The loop, then the last batch hashed.
  refine WP.seq (WP.mono (Q := OInv σ y s₀ σ.nb (σ.nb - 1)) ?_ fun s₂ hI₂ => ?_)
  · refine WP.ite (decide (σ.nb - 1 = 0)) (eval_zero hI₁.ci.x11 (by omega_arith)) (fun h => ?_) (fun h => ?_)
    · have : σ.nb = 1 := by simp at h; omega_arith
      exact WP.block_nil (by rw [this]; exact hI₁)
    · let I : Nat → State → Prop := fun m s => ∃ h, m = σ.nb - (h + 1) ∧ h + 1 < σ.nb ∧ OInv σ y s₀ (h + 1) h s
      have hstep : ∀ m s, I m s → WP isa (.block (parts e3 σ.nr 128 ++ stores 128 ++ adv)) s (fun s' =>
          (AArch64.eval (.nonzero .x .x11) s' = some false ∧ OInv σ y s₀ σ.nb (σ.nb - 1) s') ∨
          (AArch64.eval (.nonzero .x .x11) s' = some true ∧ ∃ m' < m, I m' s')) := by
        rintro m s ⟨h, rfl, hh, hI⟩
        refine WP.mono (openBody_ok hp gh hx19 hx15 hrdwr hwr e3 hh hI) fun s' hI' => ?_
        rw [eval_nonzero hI'.ci.x11 (by omega_arith)]
        by_cases hl : σ.nb - (h + 2) = 0
        · have e : h + 2 = σ.nb := by omega_arith
          exact .inl ⟨by simp [hl], by rw [← e, show h + 2 - 1 = h + 1 by omega_arith]; exact hI'⟩
        · exact .inr ⟨by simp [hl], σ.nb - (h + 2), by omega_arith, h + 1, rfl, by omega_arith, hI'⟩
      exact WP.loop (M := isa) I hstep _ _ ⟨0, rfl, by simp at h; omega_arith, hI₁⟩
  · rw [WP.block_append_iff]
    have hct : ∀ j < 8, s₂.mem.readW (σ.D + BitVec.ofNat 64 (16 * (8 * (σ.nb - 1) + j))) 128 =
        σ.blockC (8 * (σ.nb - 1) + j) :=
      fun j hj => readW_of_dataInv hn hI₂.ci.data (by omega_arith) (by omega_arith)
    refine WP.mono (ghStep e3 hp gh (y := y) (hb := σ.blockC) (h := σ.nb - 1) hI₂.y hI₂.cr hI₂.ci.x9 (by omega_arith)
      (by rw [hI₂.ci.gpr _ (by decide), hx19]) (by rw [hI₂.ci.rd, hI₂.ci.wr, hrdwr]) hI₂.ci.frame hct)
      fun u ⟨hy, ou⟩ => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, exec_addImm_x (imm := 128) (by decide), WP.block_nil ?_⟩
    have e : σ.nb - 1 + 1 = σ.nb := by omega_arith
    exact {
      ci := {
        le := Nat.le_refl _
        x9 := by
          simp only [gpr_write_self, State.read, BitVec.setWidth_eq, ou.gpr, hI₂.ci.x9]
          rw [Offset.add_add_eq _ (show 128 * (σ.nb - 1) + 128 = 128 * σ.nb by omega_arith)]
        x10 := by
          simp only [State.read, gpr_write_of_ne _ _ _ (show Reg.x10 ≠ Reg.x9 by decide), ou.gpr]; exact hI₂.ci.x10
        x11 := by rw [gpr_write_of_ne _ _ _ (by decide), ou.gpr, hI₂.ci.x11]
        gpr := fun r hr => by
          rw [gpr_write_of_ne _ _ _ (fun h => hr (by simp [h, kRegs])), ou.gpr, hI₂.ci.gpr r hr]
        data := by rw [mem_write, ou.mem]; exact hI₂.ci.data
        frame := by rw [mem_write, ou.mem]; exact hI₂.ci.frame
        sp := by rw [sp_write, ou.sp, hI₂.ci.sp]
        rd := by rw [rd_write, ou.rd, hI₂.ci.rd]
        wr := by rw [wr_write, ou.wr, hI₂.ci.wr] }
      y := by rw [v_write, hy, e]
      cr := by rw [v_write, ou.v C (by decide), hI₂.cr] }

end

end VG.Proof.AesGcmSiv.AArch64.Stitch

end

end

/-! ### `AesGcmSiv.AArch64.Stitch.Tbl`, which only this module used -/

section

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: the table of keys

Untrusted: everything here is checked by Lean. `tblBuild_ok`: `tblBuild`
(`Impl.AesGcmSiv.AArch64.Stitch`) leaves the table of keys of GHASH's key `H`
(at `W + 64`) at `W + tblO` (`TblOk`): `H'` computed from `H` as
`vg_ghash_aes`'s prologue computes it (`keyV`), the powers by its `powers`
(`Proof.AesGcm.AArch64.Stitch.powers_ok`), from `PrepPow` (the algebra's
one fact, a hypothesis here), and stored as AES-GCM's table is, at another
place in `W`.
-/

@[expose] public section

local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly pp PrepPow keyV mulV_ok swap_ok consts_ok loadRev_ok rev64b_read
  ext8_ext8 tReg_free sReg_free free_A ne_tReg ne_sReg tReg_ne_sReg)
open VG.Proof.AesGcm.AArch64.Stitch (PInv PT powers_ok powV readW_write_self readW_write_sep kv_ok kpack_eq
  pkl_range tReg_nlow sReg_nlow)
open VG.Proof.Gcm.AArch64.Stitch (kpack)
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C tReg sReg poly)
open VG.Impl.AesGcmSiv.AArch64.Stitch (tblO sOff kOff tblBuild)
open VG.Impl.Gcm.AArch64.Stitch (pk pl)
open VG.Spec.Gcm (Block blockAt)

/-! ## `H'` -/

/-- `Pmull.consts_ok`, with the stack pointer kept. -/
theorem consts_ok' (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.consts) s fun s' =>
      s'.v C = ofVDwords poly poly ∧ s'.v (tReg 2) = Proof.Gcm.AArch64.Pmull.xInv2 ∧
      s'.v (sReg 2) = ext8 Proof.Gcm.AArch64.Pmull.xInv2 Proof.Gcm.AArch64.Pmull.xInv2 ∧
      (∀ r, r ≠ C → r ≠ tReg 2 → r ≠ sReg 2 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.consts, tReg, sReg, runBlock_cons, runStep_some, runBlock_nil,
    Proof.Gcm.AArch64.Pmull.exec_movz_x (show 16 * 3 < 64 by decide),
    Proof.Gcm.AArch64.Pmull.exec_movz_x (show 16 * 0 < 64 by decide),
    Proof.Gcm.AArch64.Pmull.exec_dup_d2, Proof.Gcm.AArch64.Pmull.exec_ins_d2 (show 0 < 2 by decide),
    Proof.Gcm.AArch64.Pmull.exec_ins_d2 (show 1 < 2 by decide),
    Proof.Gcm.AArch64.Pmull.v_setV, gpr_setV, VG.AArch64.RegUpd.v_write, Proof.Gcm.AArch64.Pmull.gpr_write_x,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', Proof.Gcm.AArch64.Pmull.setLane_pair,
    mem_setV, rd_setV, wr_setV, sp_setV, VG.AArch64.RegUpd.mem_write, VG.AArch64.RegUpd.rd_write,
    VG.AArch64.RegUpd.wr_write, VG.AArch64.RegUpd.sp_write, and_true]
  refine ⟨by decide, by decide, by rw [Proof.Gcm.AArch64.Pmull.ext8_eq]; decide, fun r hc ht hs => ?_,
    fun r h5 h6 h7 => ?_⟩
  · simp only [hc, ht, hs, ite_false]
  · simp only [h5, h6, h7, ite_false]

/-- `H` loaded from `x19 + 64`, the constants, and `H'`. -/
theorem hPrime_ok (hP : PrepPow) {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO) 16) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadRev A .x19 Impl.AesGcmSiv.AArch64.hO ++
        Impl.Gcm.AArch64.Pmull.consts ++ Impl.Gcm.AArch64.Pmull.mul (sReg 1) A (sReg 2) (tReg 2) ++
        ([.vop (.ext (tReg 1) (sReg 1) (sReg 1) 8)] : List Instr))) s fun s' =>
      PInv (blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO)) 1 s' ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadRev_ok A .x19 _ s (by decide) (by decide) hin) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok' s₁) fun s₂ ⟨c₂, t₂, w₂, kv₂, kg₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulV_ok (sReg 1) A (sReg 2) (tReg 2) s₂ free_A (sReg_free _) (tReg_free _)
    (by rw [w₂, t₂]) c₂) fun s₃ ⟨m₃, o₃⟩ => ?_
  refine WP.mono (swap_ok (tReg 1) (sReg 1) s₃) fun s₄ ⟨w₄, o₄⟩ => ?_
  have hA₂ : s₂.v A = s₁.v A := kv₂ A (by decide) (ne_tReg 2) (ne_sReg 2)
  have hm : s₃.v (sReg 1) = ext8 (keyV (blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO)))
      (keyV (blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO))) := by
    rw [m₃, hA₂, l₁, t₂, rev64b_read, keyV, ext8_ext8]
  have s₁' : s₄.v (sReg 1) = s₃.v (sReg 1) := o₄.v _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun e => tReg_ne_sReg _ _ e.symm)
  refine ⟨⟨?_, fun k hk hk1 => ?_, fun k hk hk1 => ?_⟩, fun r h5 h6 h7 => ?_, ?_, ?_, ?_, ?_⟩
  · have h : C ∉ [LO, MID, HI, T, sReg 1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, by decide, by decide, ne_sReg 1⟩
    rw [o₄.v C (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ne_tReg 1), o₃.v C h, c₂]
  · obtain rfl : k = 1 := by omega_using [hk, hk1]
    rw [w₄, hm, ext8_ext8, hP.key]
  · obtain rfl : k = 1 := by omega_using [hk, hk1]
    rw [s₁', hm, hP.key]
  · rw [o₄.gpr, o₃.gpr, kg₂ r h5 h6 h7, o₁.gpr]
  · rw [o₄.mem, o₃.mem, m₂, o₁.mem]
  · rw [o₄.sp, o₃.sp, sp₂, o₁.sp]
  · rw [o₄.rd, o₃.rd, rd₂, o₁.rd]
  · rw [o₄.wr, o₃.wr, wr₂, o₁.wr]

/-! ## The table -/

/-- Where the table is. -/
abbrev tblR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 tblO, 192⟩

theorem sOff_eq (k : Nat) : sOff (k + 1) = tblO + 16 * k := by unfold sOff; omega_using []

theorem kOff_eq (p : Nat) : kOff p = tblO + 128 + 16 * p := by unfold kOff; omega_using []

theorem tblO_eq : tblO = 480 := rfl

/-- A store into the table. -/
theorem st_ok (t : VReg) {d : Nat} (hd : tblO ≤ d) (hd' : d + 16 ≤ tblO + 192) (h16 : d % 16 = 0) {s : State}
    (hw : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 tblO) 192) :
    WP isa (.block [.strq t .x19 d]) s fun s' =>
      s' = { s with mem := s.mem.write (s.gpr .x19 + BitVec.ofNat 64 d) 16 (s.v t) } ∧
      Frame [tblR (s.gpr .x19)] s.mem s'.mem := by
  have hin : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 16 := by
    have := CallLay.inRegions_sub (off := d - tblO) (l := 16) hw (by omega_using [hd']) (by decide)
    rwa [Offset.add_add, show tblO + (d - tblO) = d by omega_using [hd]] at this
  refine WP.block_cons_iff.mpr ⟨_, Proof.Gcm.AArch64.Pmull.exec_strq h16 (by rw [tblO_eq] at hd'; omega_using [hd']) hin,
    WP.block_nil ⟨rfl, ?_⟩⟩
  exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Offset.contains _ hd (by omega_using [hd']) (by decide))

/-- The table's first `n` powers and `q` pairs of keys stored. -/
structure TS (s₀ : State) (H : Block) (n q : Nat) (s : State) : Prop where
  v : ∀ r, r ∉ [VReg.v2, .v3, .v4] → s.v r = s₀.v r
  gpr : s.gpr = s₀.gpr
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [tblR (s₀.gpr .x19)] s₀.mem s.mem
  sw : ∀ k < n, s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (sOff (k + 1))) 128 = ext8 (pp H (k + 1)) (pp H (k + 1))
  key : ∀ p < q, s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (kOff p)) 128 = kpack H (pk p) (pl p)

/-- The powers stored. -/
theorem sws_ok {s₀ : State} {H : Block} (hI : PT H 8 s₀)
    (hw : InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 tblO) 192) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k => [.strq (sReg (k + 1)) .x19 (sOff (k + 1))]))
      s₀ (TS s₀ H n 0) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, nofun, nofun⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun s h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have e := sOff_eq n
    refine WP.mono (st_ok (s := s) (sReg (n + 1)) (d := sOff (n + 1)) (by omega_using [e]) (by omega_using [hn, e])
      (by rw [e, tblO_eq]; omega_using []) (by rw [h.wr, h.gpr]; exact hw)) fun s' ⟨hs', f'⟩ => ?_
    subst hs'
    refine ⟨h.v, h.gpr, h.sp, h.rd, h.wr, h.frame.trans (h.gpr ▸ f'), fun k hk => ?_, nofun⟩
    dsimp only
    rw [h.gpr]
    rcases (by omega_using [hk] : k = n ∨ k < n) with rfl | hk'
    · rw [readW_write_self, h.v _ (sReg_nlow _), hI.sw _ (by omega_using []) (by omega_using [hn])]
    · rw [readW_write_sep (by rw [sOff_eq, sOff_eq]; omega_using [hk']) (by rw [sOff_eq, tblO_eq]; omega_using [hn, hk])
        (by rw [tblO_eq] at e; omega_using [hn, e]), h.sw k hk']

/-- A pair of keys stored. -/
theorem key_ok {s₀ : State} {H : Block} (hI : PT H 8 s₀)
    (hw : InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 tblO) 192) {q : Nat} (hq : q < 4) {s : State}
    (h : TS s₀ H 8 q s) :
    WP isa (.block [.vop (.logic .eor .v2 (sReg (pk q)) (tReg (pk q))),
      .vop (.logic .eor .v3 (sReg (pl q)) (tReg (pl q))),
      .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (kOff q)]) s (TS s₀ H 8 (q + 1)) := by
  obtain ⟨k1, k8, l1, l8⟩ := pkl_range q hq
  have e := kOff_eq q
  rw [show ∀ a b c d : Instr, [a, b, c, d] = [a, b, c] ++ [d] from fun _ _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (kv_ok (pk q) (pl q) s) fun s₃ ⟨v4, v₃, g₃, m₃, sp₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (st_ok .v4 (d := kOff q) (by omega_using [e]) (by omega_using [hq, e]) (by rw [e, tblO_eq]; omega_using [])
    (by rw [wr₃, g₃, h.wr, h.gpr]; exact hw)) fun s' ⟨hs', f'⟩ => ?_
  subst hs'
  refine ⟨fun r hr => by dsimp only; rw [v₃ r hr, h.v r hr], by dsimp only; rw [g₃, h.gpr],
    by dsimp only; rw [sp₃, h.sp], by dsimp only; rw [rd₃, h.rd], by dsimp only; rw [wr₃, h.wr],
    h.frame.trans (by rw [← m₃]; rw [show tblR (s₃.gpr .x19) = tblR (s₀.gpr .x19) by rw [g₃, h.gpr]] at f'; exact f'),
    fun k hk => ?_, fun p hp => ?_⟩
  · dsimp only
    rw [g₃, m₃, h.gpr, readW_write_sep (by rw [sOff_eq, kOff_eq]; omega_using [hk]) (by rw [sOff_eq, tblO_eq]; omega_using [hk])
      (by rw [tblO_eq] at e; omega_using [hq, e]), h.sw k hk]
  · dsimp only
    rw [g₃, m₃, h.gpr]
    rcases (by omega_using [hp] : p = q ∨ p < q) with rfl | hp'
    · rw [readW_write_self, v4, h.v _ (sReg_nlow _), h.v _ (tReg_nlow _), h.v _ (sReg_nlow _),
        h.v _ (tReg_nlow _), hI.sw _ k1 k8, hI.t _ k1 k8, hI.sw _ l1 l8, hI.t _ l1 l8, kpack_eq]
      rfl
    · rw [readW_write_sep (by rw [kOff_eq, kOff_eq]; omega_using [hp']) (by rw [kOff_eq, tblO_eq]; omega_using [hq, hp])
        (by rw [tblO_eq] at e; omega_using [hq, e]), h.key p hp']

/-- The table stores. -/
abbrev tblStores : List Instr :=
  (List.range 8).flatMap (fun k => [.strq (sReg (k + 1)) .x19 (sOff (k + 1))]) ++
  (List.range 4).flatMap fun p =>
    [.vop (.logic .eor .v2 (sReg (pk p)) (tReg (pk p))),
     .vop (.logic .eor .v3 (sReg (pl p)) (tReg (pl p))),
     .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (kOff p)]

/-- The table of keys: the powers with their halves swapped, and the pairs' keys. -/
theorem tbl_ok {s₀ : State} {H : Block} (hI : PT H 8 s₀)
    (hw : InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 tblO) 192) :
    WP isa (.block tblStores) s₀ (TS s₀ H 8 4) := by
  have ks : ∀ q ≤ 4, ∀ s, TS s₀ H 8 0 s → WP isa (.block ((List.range q).flatMap fun p =>
      [.vop (.logic .eor .v2 (sReg (pk p)) (tReg (pk p))), .vop (.logic .eor .v3 (sReg (pl p)) (tReg (pl p))),
       .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (kOff p)])) s (TS s₀ H 8 q) := by
    intro q hq s h
    induction q with
    | zero => exact WP.block_nil ⟨h.v, h.gpr, h.sp, h.rd, h.wr, h.frame, h.sw, nofun⟩
    | succ q ih =>
      rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
      refine WP.mono (ih (by omega_using [hq])) fun s' h' => ?_
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact key_ok hI hw (by omega_using [hq]) h'
  rw [tblStores, WP.block_append_iff]
  exact WP.mono (sws_ok hI hw 8 (Nat.le_refl _)) fun s h => ks 4 (by decide) s h

theorem TS.tblOk {s₀ s : State} {H : Block} (h : TS s₀ H 8 4 s) : TblOk s.mem (s₀.gpr .x19) H :=
  ⟨fun k hk hk8 => by
    have := h.sw (k - 1) (by omega_using [hk8])
    rwa [show k - 1 + 1 = k by omega_using [hk]] at this, h.key⟩

/-- `tblBuild`: the table of keys of `H` (at `x19 + 64`), and only `x5`–`x7`,
the vector registers and the table written. -/
theorem tblBuild_ok (hP : PrepPow) {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO) 16)
    (hw : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 tblO) 192) :
    WP isa (.block tblBuild) s fun s' =>
      TblOk s'.mem (s.gpr .x19) (blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.hO)) ∧
      Frame [tblR (s.gpr .x19)] s.mem s'.mem ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  rw [show tblBuild = (Impl.Gcm.AArch64.Pmull.loadRev A .x19 Impl.AesGcmSiv.AArch64.hO ++
        Impl.Gcm.AArch64.Pmull.consts ++ Impl.Gcm.AArch64.Pmull.mul (sReg 1) A (sReg 2) (tReg 2) ++
        ([.vop (.ext (tReg 1) (sReg 1) (sReg 1) 8)] : List Instr)) ++ Impl.Gcm.AArch64.Pmull.powers ++ tblStores
      by simp only [tblBuild, tblStores, List.append_assoc], WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hPrime_ok hP hin) fun s₁ ⟨p₁, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (powers_ok hP p₁) fun s₂ ⟨p₂, o₂⟩ => ?_
  have g₂ : s₂.gpr .x19 = s.gpr .x19 := by rw [o₂.gpr, g₁ _ (by decide) (by decide) (by decide)]
  refine WP.mono (tbl_ok p₂.pt (by rw [o₂.wr, wr₁, g₂]; exact hw)) fun s₃ h₃ => ?_
  refine ⟨?_, ?_, fun r h5 h6 h7 => ?_, ?_, ?_, ?_⟩
  · have := h₃.tblOk; rwa [g₂] at this
  · have f := h₃.frame
    rw [g₂, o₂.mem, m₁] at f; exact f
  · rw [h₃.gpr, o₂.gpr, g₁ r h5 h6 h7]
  · rw [h₃.sp, o₂.sp, sp₁]
  · rw [h₃.rd, o₂.rd, rd₁]
  · rw [h₃.wr, o₂.wr, wr₁]

end VG.Proof.AesGcmSiv.AArch64.Stitch

end

end


/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: POLYVAL of the data

Untrusted: everything here is checked by Lean. `polyData_ok`: `polyData`
(`Impl.AesGcmSiv.AArch64.Stitch`) absorbs the data padded with zeros, as
`absorb` does (`Proof.AesGcmSiv.AArch64.absorb_ok`): its batches by
`ghLoop`, from the table of keys `tblBuild` writes (`polyBatch_ok`), the
rest by `absorb`; and `polyval_ok` is `Proof.AesGcmSiv.AArch64.polyval_ok`
with it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs Absorbed AbsPost absR absorbR absorbR_buf absR_sub
  elemsAt absorb_ok lens_ok tagIn_ok tagInMem tagInMem_frame tagInMem_bytes polyR PolyPost absorbR_H)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl Others covers_left lsr_ofNat eval_zero add_ofNat_assoc length_bytesAt)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly PrepPow rev64b_read blockAt_store ext8_ext8)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (Y C)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-! ## Words -/

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega_arith)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by omega_arith)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega_arith
      have e2 : (i - 8) % 8 = i % 8 := by omega_arith
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega_arith

/-- 16 bytes as two doublewords. -/
theorem readW128_q (m : Mem) (a : Addr) : m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Mem.readW, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  rw [getLsbD_read _ 16 a i (by omega_arith)]
  by_cases h : i < 64
  · simp only [h, decide_true, Bool.cond_true, BitVec.getLsbD_setWidth]
    rw [getLsbD_read _ 8 a i (by omega_arith)]
    simp [hi, h]
  · simp only [h, decide_false, Bool.cond_false, BitVec.getLsbD_setWidth]
    rw [getLsbD_read _ 8 _ (i - 64) (by omega_arith), Offset.add_add, show 8 + (i - 64) / 8 = i / 8 by omega_arith,
      show (i - 64) % 8 = i % 8 by omega_arith]
    simp [hi, h, show i - 64 < 64 by omega_arith]

/-- 16 bytes as a number. -/
theorem ofBytes_readW (m : Mem) (a : Addr) : Spec.GcmSiv.ofBytes (bytesAt m a 16) = m.readW a 128 := by
  rw [GcmSiv.ofBytes_bytesAt, readW128_q]

/-! ## The setup and the end of `ghLoop` -/

/-- `batches` and `ghSetup`: the data's pointer and batches, the reduction
constant and `Y` as loaded. -/
theorem ghPre_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    WP isa (.block (batches ++ ghSetup)) s fun s' =>
      s'.gpr .x9 = p.D + BitVec.ofNat 64 (128 * 0) ∧ s'.gpr .x11 = BitVec.ofNat 64 (p.n / 128 - 0) ∧
      s'.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly ∧
      s'.v Y = ext8 (blockAt s.mem (p.W + BitVec.ofNat 64 80)) (blockAt s.mem (p.W + BitVec.ofNat 64 80)) ∧
      Others [.x9, .x11, .x12] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hWn := L.hWn
  have hy : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 80) 16 := by
    rw [E.x19]; exact E.perm.wR (by decide)
  simp only [batches, ghSetup, List.cons_append, List.nil_append]
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 7) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_movz_x (imm := 0xc200) (hw := 3) (by decide) _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_dup_d2 C .x12 _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_ldrq (t := Y) (off := 80) (by decide) (by decide)
    (by simpa only [gpr_setV, rd_setV, wr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x11 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide), rd_write, wr_write] using hy), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_rev64b Y Y _, WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_setV, gpr_write, reduceCtorEq, ite_false, ite_true, State.read, BitVec.setWidth_eq, E.x25,
      Nat.mul_zero, BitVec.add_zero]
  · simp only [gpr_setV, gpr_write, reduceCtorEq, ite_false, ite_true, State.read, BitVec.setWidth_eq, E.x26,
      Nat.sub_zero]
    rw [lsr_ofNat _ _ L.n_lt]
  · simp only [v_write, v_setV_of_ne _ _ (show C ≠ Y by decide), v_setV_self, gpr_write_self]
    rfl
  · simp only [v_write, v_setV_self, mem_setV, mem_write, gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x11 by decide), gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide),
      E.x19]
    rw [rev64b_read]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setV, gpr_write_of_ne _ _ _ hr.1, gpr_write_of_ne _ _ _ hr.2.1, gpr_write_of_ne _ _ _ hr.2.2]

/-- `ghFinish`: `Y` stored back to `W + 80`. -/
theorem ghFinish_ok {p : Prm} {s : State} (hx19 : s.gpr .x19 = p.W)
    (hw : InRegions s.wr (p.W + BitVec.ofNat 64 80) 16) :
    WP isa (.block ghFinish) s fun s' =>
      blockAt s'.mem (p.W + BitVec.ofNat 64 80) = ext8 (s.v Y) (s.v Y) ∧
      Frame [⟨p.W + BitVec.ofNat 64 80, 16⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  rw [ghFinish, WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_rev64b Y Y _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_strq (t := Y) (off := 80) (by decide) (by decide)
    (by simpa only [wr_setV, gpr_setV, hx19] using hw), WP.block_nil ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · show blockAt ((s.setV Y _).mem.write ((s.setV Y _).gpr .x19 + BitVec.ofNat 64 80) 16 ((s.setV Y _).v Y)) _ = _
    rw [gpr_setV, v_setV_self, mem_setV, hx19, blockAt_store]
  · show Frame _ s.mem ((s.setV Y _).mem.write ((s.setV Y _).gpr .x19 + BitVec.ofNat 64 80) 16 _)
    rw [gpr_setV, mem_setV, hx19]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The batches -/

theorem elemsAt_eq {m m' : Mem} {D : Addr} {k : Nat}
    (h : ∀ i < k, m'.readW (D + BitVec.ofNat 64 (16 * i)) 128 = m.readW (D + BitVec.ofNat 64 (16 * i)) 128) :
    (List.range k).map (fun i => m'.readW (D + BitVec.ofNat 64 (16 * i)) 128) = elemsAt m D k := by
  refine List.map_congr_left fun i hi => ?_
  rw [h i (List.mem_range.mp hi), ofBytes_readW]

/-- The batches of the data hashed by `ghLoop`, from the table of keys. -/
theorem polyBatch_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hnb : 1 ≤ p.n / 128) :
    WP isa (.seq (.block (tblBuild ++ batches ++ ghSetup)) (.seq (ghLoop e3) (.block ghFinish))) t
      (Absorbed p (absR p.W) (elemsAt t.mem p.D (8 * (p.n / 128))) t) := by
  obtain hWn := L.hWn
  have hn := L.n_lt
  have hww := L.ww
  rw [List.append_assoc, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (tblBuild_ok hP (by rw [E.x19]; exact E.perm.wR (by decide)) (by rw [E.x19]; exact E.perm.wW (by decide)))
    fun s₁ ⟨tok₁, f₁, g₁, sp₁, rd₁, wr₁⟩ => ?_
  have E₁ : Env p s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)) sp₁ rd₁ wr₁
  refine WP.mono (ghPre_ok L E₁) fun s₂ ⟨x9₂, x11₂, c₂, y₂, o₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  rw [E.x19] at tok₁ f₁
  -- The context of the loop.
  let σ : Ctx := ⟨p.W, p.W + BitVec.ofNat 64 240, p.D, p.R, p.n / 128, blockAt t.mem (p.W + BitVec.ofNat 64 64),
    s₂.mem, t.rd, t.wr⟩
  have hd₁ : Frame [tblR p.W] t.mem s₂.mem := by rw [m₂]; exact f₁
  have dT : (⟨p.D, p.n⟩ : Region).Disjoint (tblR p.W) := L.d_w' (by decide)
  have hp : KPre σ := {
    rounds := by rcases L.rounds with h | h <;> simp [σ, h]
    nb1 := hnb
    n16 := by show 128 * (p.n / 128) < 2 ^ 64; omega_arith
    k_in := by
      show InRegions (t.rd ++ t.wr) (p.W + BitVec.ofNat 64 240) (16 * (p.R + 1))
      exact E.perm.wR (by rcases L.rounds with h | h <;> rw [h] <;> decide)
    c_in := E.perm.wR (by decide)
    d_in := by
      show InRegions t.wr p.D (128 * (p.n / 128))
      exact E.perm.d _ _ ⟨⟨p.D, p.n⟩, List.mem_singleton_self _, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_arith⟩
    t_in := E.perm.wR (by decide)
    d_k := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 240, 16 * (p.R + 1)⟩
      exact (L.d_w' (d := 240) (k := 16 * (p.R + 1)) (by rcases L.rounds with h | h <;> rw [h] <;> decide)).sub_left
        (Region.sub_prefix (by omega_arith))
    d_c := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega_arith))
    d_t := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega_arith))
    wrap_t := by show p.W.toNat + 480 + 192 ≤ 2 ^ 64; omega_arith
    wrap_c := by show p.W.toNat + 96 + 16 ≤ 2 ^ 64; omega_arith
    wrap_k := by
      show (p.W + BitVec.ofNat 64 240).toNat + 16 * (p.R + 1) ≤ 2 ^ 64
      rw [L.toNat_W (by omega)]; rcases L.rounds with h | h <;> rw [h] <;> omega_arith
    tbl := by show TblOk s₂.mem p.W _; rw [m₂]; exact tok₁ }
  have hI : GInv σ (blockAt t.mem (p.W + BitVec.ofNat 64 80)) s₂ 0 s₂ := {
    le := Nat.zero_le _
    x9 := x9₂
    x11 := x11₂
    gpr := fun _ _ _ => rfl
    y := by
      rw [y₂, yh, Nat.mul_zero, List.range_zero, List.map_nil]
      have e : blockAt s₁.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) :=
        Proof.AesGcm.AArch64.blockAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact L.w_w (.inl (by decide)) (by decide) (by decide))
      rw [e]; rfl
    cr := c₂
    mem := rfl
    sp := rfl
    rd := rfl
    wr := rfl }
  have x19₂ : s₂.gpr .x19 = p.W := by rw [o₂ _ (by decide), E₁.x19]
  refine WP.seq (WP.mono (ghLoop_ok e3 hp gh x19₂ (by rw [rd₂, wr₂, rd₁, wr₁]) hI) fun s₃ G => ?_)
  refine WP.mono (ghFinish_ok (p := p) (s := s₃) (by rw [G.gpr _ (by decide) (by decide), x19₂])
    (by rw [G.wr, wr₂, wr₁]; exact E.perm.wW (by decide))) fun s₄ ⟨b₄, f₄, g₄, sp₄, rd₄, wr₄⟩ => ?_
  refine ⟨E₁.keep (fun r hr => ?_) (by rw [sp₄, G.sp, sp₂]) (by rw [rd₄, G.rd, rd₂])
    (by rw [wr₄, G.wr, wr₂]), by rw [rd₄, G.rd, rd₂, rd₁], by rw [wr₄, G.wr, wr₂, wr₁], ?_, ?_⟩
  · simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g₄, G.gpr r (by rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
      (by rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide),
      o₂ r (by rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)]
  · have f₁' : Frame (absR p.W) t.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨p.W + BitVec.ofNat 64 480, 1280⟩, by simp [absR], Region.sub_prefix (by decide)⟩
    have f₄' : Frame (absR p.W) s₃.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp [absR], fun _ h => h⟩
    have e₃ : s₃.mem = s₁.mem := by rw [G.mem, ← m₂]
    exact f₁'.trans (e₃ ▸ f₄')
  · rw [b₄, G.y, ext8_ext8, yh]
    have e : blockAt s₁.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) :=
      Proof.AesGcm.AArch64.blockAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by decide)) (by decide) (by decide))
    refine congrArg _ (elemsAt_eq fun i hi => ?_)
    have hσ : σ.nb = p.n / 128 := rfl
    show s₂.mem.readW _ 128 = _
    rw [m₂]
    exact f₁.readW (r := ⟨p.D, p.n⟩) (Offset.contains_base p.D (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dT) (by decide)

theorem pad16_append {a b : List Byte} (ha : a.length % 16 = 0) :
    Spec.GcmSiv.pad16 (a ++ b) = a ++ Spec.GcmSiv.pad16 b := by
  simp only [Spec.GcmSiv.pad16, List.length_append, List.append_assoc]
  congr 3; omega_arith

/-- The elements of the data padded: those of its batches, then those of
the rest padded. -/
theorem elems_split (m : Mem) (D : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m D n)) =
      elemsAt m D (8 * (n / 128)) ++
        Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m (D + BitVec.ofNat 64 (128 * (n / 128))) (n - 128 * (n / 128)))) := by
  have e := Proof.Cmac.bytesAt_add m D (128 * (n / 128)) (n - 128 * (n / 128))
  rw [show 128 * (n / 128) + (n - 128 * (n / 128)) = n by omega_arith] at e
  rw [e, pad16_append (by rw [length_bytesAt]; omega_arith),
    GcmSiv.elems_append (by rw [length_bytesAt]; omega_arith),
    show 128 * (n / 128) = 16 * (8 * (n / 128)) by omega_arith, GcmSiv.elems_bytesAt]

/-- The start of `ifBatch`: `x9` the number of batches. -/
theorem batchHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.block [.lsr .x .x9 .x26 7]) t fun t₁ => t₁.gpr .x9 = BitVec.ofNat 64 (p.n / 128) ∧
      Env p t₁ ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
  WP.run ⟨_, by grun [], rfl⟩ fun t₁ ht₁ => by
    subst ht₁
    refine ⟨by simp [gpr_write, E.x26, lsr_ofNat _ _ L.n_lt], E.write (by decide) _, rfl, rfl, rfl⟩

/-- `rest`: the data past its batches. -/
theorem rest_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.block rest) t fun t₁ =>
      t₁.gpr .x27 = p.D + BitVec.ofNat 64 (128 * (p.n / 128)) ∧
      t₁.gpr .x28 = BitVec.ofNat 64 (p.n - 128 * (p.n / 128)) ∧
      Env p t₁ ∧ Others [.x9, .x27, .x28] t t₁ ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
  WP.run ⟨_, by simp only [rest]; grun [], rfl⟩ fun t₁ ht₁ => by
    subst ht₁
    have hl : (BitVec.ofNat 64 p.n >>> 7) <<< 7 = BitVec.ofNat 64 (128 * (p.n / 128)) := by
      rw [lsr_ofNat _ _ L.n_lt, Proof.AesGcmSiv.AArch64.ofNat_lsl]; congr 1; omega_arith
    refine ⟨by simp [gpr_write, E.x25, E.x26, hl], ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, E.x26, hl, Proof.AesGcm.AArch64.ofNat_sub (show 128 * (p.n / 128) ≤ p.n by omega_arith) L.n_lt]
    · exact ((((E.write (by decide) _).write (by decide) _).write (by decide) _).write (by decide) _)

/-- The batches, if the data has one. -/
theorem polyBatches_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (ifBatch (.seq (.block (tblBuild ++ batches ++ ghSetup)) (.seq (ghLoop e3) (.block ghFinish)))) t
      (Absorbed p (absR p.W) (elemsAt t.mem p.D (8 * (p.n / 128))) t) := by
  obtain hWn := L.hWn
  have hn := L.n_lt
  unfold ifBatch
  refine WP.seq (WP.mono (batchHead_ok L E) fun t₁ ⟨x9₁, E₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.ite (decide (p.n / 128 = 0)) (eval_zero x9₁ (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h0 : p.n / 128 = 0 := by simpa using h
    refine WP.block_nil ⟨E₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_⟩
    rw [h0, m₁]; simp [elemsAt, ghashFrom]
  · have h1 : 1 ≤ p.n / 128 := by simp at h; omega_arith
    exact WP.mono (polyBatch_ok hP gh e3 L E₁ h1) fun t₂ A => by rw [m₁] at A; exact A.of_eq m₁ rd₁ wr₁

/-- `polyData`: the data padded absorbed. -/
theorem polyData_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (polyData e3 v.callees) t (AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem p.D p.n))) t) := by
  obtain hWn := L.hWn
  have hn := L.n_lt
  unfold polyData ifBatch
  -- The batches.
  have hb := polyBatches_ok hP gh e3 L E
  refine WP.seq (WP.mono hb fun t₂ A => ?_)
  -- The rest.
  refine WP.seq (WP.mono (rest_ok L A.env) fun t₃ ⟨x27₃, x28₃, E₃, o₃, m₃, rd₃, wr₃⟩ => ?_)
  have hc : Covers [⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩] (t₃.rd ++ t₃.wr) := by
    rw [rd₃, wr₃, A.rd, A.wr]
    exact covers_left (Proof.AesGcm.AArch64.covers_off E.perm.d (by omega_arith) hn)
  have dW : (⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W, p.Wn⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega_arith))
  refine WP.mono (absorb_ok v L E₃ hc (by omega_arith) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * (p.n / 128)) (by omega_arith)]
      have := L.dw; have := Nat.mod_le (p.D.toNat + 128 * (p.n / 128)) (2 ^ 64); omega_arith)
    dW x27₃ x28₃) fun t₄ P₄ => ?_
  have e : bytesAt t₃.mem (p.D + BitVec.ofNat 64 (128 * (p.n / 128))) (p.n - 128 * (p.n / 128)) =
      bytesAt t.mem (p.D + BitVec.ofNat 64 (128 * (p.n / 128))) (p.n - 128 * (p.n / 128)) := by
    rw [m₃]
    exact Proof.AesGcm.AArch64.bytesAt_frame A.frame (fun r hr => dW.sub_right (by
      simp only [absR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Proof.AesGcmSiv.AArch64.Lay.wSub (by omega))) (by omega_arith)
  rw [e] at P₄
  rw [elems_split]
  exact AbsPost.trans L (A.sub (absR_sub p.W)) (P₄.of_eq m₃ rd₃ wr₃)

/-- `polyval` with `polyData` (`Proof.AesGcmSiv.AArch64.polyval_ok`). -/
theorem polyval_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hG : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80) = 0) :
    WP isa (Impl.AesGcmSiv.AArch64.Stitch.polyval e3 v.callees) t (PolyPost p t) := by
  obtain hWn := L.hWn
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok v L ((E.write (by decide) _).write (by decide) _) (by simp only [rd_write, wr_write]; exact E.perm.aad) L.al_lt L.aw L.a_w
    (by simp [gpr_write, E.x23]) (by simp [gpr_write, E.x24])) fun t₂ P₂ => ?_)
  simp only [mem_write] at P₂
  have P₂' := P₂.of_eq (t := t) rfl rfl rfl
  -- The data.
  refine WP.seq (WP.mono (polyData_ok hP gh e3 v L P₂.env) fun t₄ P₄ => ?_)
  rw [Proof.AesGcm.AArch64.bytesAt_frame P₂.frame (absorbR_buf L.d_w) (by have := L.n_lt; omega_arith)] at P₄
  have P₂₄ := AbsPost.trans L P₂' P₄
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  have P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := tagIn_ok P₂₅.env
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.keep (fun q hq => ho₆ q (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆,
    by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₆]
    exact (tagInMem_frame _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega_arith
    have nN : bytesAt t₅.mem p.N 12 = bytesAt t.mem p.N 12 :=
      Proof.AesGcm.AArch64.bytesAt_frame P₂₅.frame (absorbR_buf L.n_w) (by decide)
    rw [hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]
    simp only [mem_write]

end VG.Proof.AesGcmSiv.AArch64.Stitch
