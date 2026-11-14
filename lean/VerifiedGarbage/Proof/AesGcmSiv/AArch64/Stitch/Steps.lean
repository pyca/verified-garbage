module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Aes
public import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Stitch
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.GhBits
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Base
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
