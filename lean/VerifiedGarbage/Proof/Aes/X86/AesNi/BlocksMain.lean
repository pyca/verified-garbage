module

public import VerifiedGarbage.Proof.Aes.Rounds
import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
public import VerifiedGarbage.Proof.Aes.X86.BlocksContract
meta import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
meta import VerifiedGarbage.Proof.Aes.X86.BlocksContract

/-! ### `Aes.X86.AesNi.Blocks`, which this module and modules that import it used -/

section

/-!
# AES-NI on x86 (32-bit): encryption and decryption of whole blocks

The loops are proven once for any transformation `f` of a list of block
registers that computes `F` on each, given what it needs of the state
(`KP`, which the loops keep): `aes` and `aesDec`. After `c` blocks, the
first `c` data blocks hold `F` of the original ones (`Inv`); the turn of
six blocks and the groups of three, two and one of the blocks left are the
same code for different lists of registers (`blocks_ok`). `encrypt_correct` and `decrypt_correct` add the prologue,
which saves `esi` and `edi` in the scratch buffer and loads the arguments,
the round keys through `aesimc` for decryption, and the epilogue.
-/

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ aes aesDec regs6 regs3 regs2 regs1 loadData storeData blocksGroup blocks6
  blocks3 blocksBit blocksTail
  blocksPrologue blocksCmp blocksRestore imcKeys)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 in_rd
  addr_add part_contains part_sub_reg reg_contains in_reg)
open VG.X86.Wp (Upd Fupd wp_addi wp_subi wp_cmpi wp_test wp_ldm wp_stm toNat_ofNat_lt ofNat_beq_zero)

namespace Ecb

section
variable (s₀ : State)

/-- Block `k` of the data, and where it starts. -/
abbrev bAddr (k : Nat) : Addr := (bDatP s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)
abbrev orig (k : Nat) : Spec.Aes.State := Spec.Aes.stateAt s₀.mem (bAddr s₀ k)
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem ((bSchP s₀).setWidth 64) (16 * (bRounds s₀ + 1))

end

/-- What a transformation of the block registers needs of the state is kept
by writing data blocks and moving `esi` and `edi`. -/
def Stable (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s s', KP s → (∀ r, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
    Frame [bDatR s₀] s.mem s'.mem → KP s'

/-- The lists of block registers of the loops: a turn's six, and the three,
the two and the one of the blocks left. -/
def Lanes (rs : List XReg) : Prop := rs = regs6 ∨ rs = regs3 ∨ rs = regs2 ∨ rs = regs1

/-- `f` computes `F` on each block register, for each list of registers. -/
def BlkOk (f : List XReg → Prog isa) (F : Spec.Aes.State → Spec.Aes.State) (KP : State → Prop) :
    Prop :=
  ∀ rs, Lanes rs → ∀ s, KP s →
    WP isa (f rs) s fun s' => (∀ b ∈ rs, st (s'.xmm b) = F (st (s.xmm b))) ∧ XFrame (.xmm6 :: rs) s s'

/-- After `c` blocks, with `esi` at block `p` and `edi` the number of blocks
from block `q` on; the other registers are `g`, and only the data has
changed since `m₁`. -/
structure Inv (KP : State → Prop) (F : Spec.Aes.State → Spec.Aes.State) (s₀ : State) (g : Reg → BitVec 32)
    (m₁ : Mem) (c p q : Nat) (s : State) : Prop where
  le : c ≤ bN s₀
  kp : KP s
  gpr : ∀ r, r ≠ .esi → r ≠ .edi → s.gpr r = g r
  esi : s.gpr .esi = bDatP s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (bN s₀ - q)
  frame : Frame [bDatR s₀] m₁ s.mem
  blocks : ∀ k < bN s₀,
    Spec.Aes.stateAt s.mem (bAddr s₀ k) = if k < c then F (orig s₀ k) else orig s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem regs_nodup (rs : List XReg) (h : Lanes rs) : rs.Nodup ∧ .xmm6 ∉ rs := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem regs_len (rs : List XReg) (h : Lanes rs) : 0 < rs.length ∧ rs.length ≤ 6 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- Whether a count under 3 has the bit 2 or 1: what `test edi, 2` and
`test edi, 1` give. -/
theorem bit_lt : ∀ r < 3, (BitVec.ofNat 32 r &&& BitVec.ofNat 32 2 == 0) = decide (r < 2) ∧
    (BitVec.ofNat 32 r &&& BitVec.ofNat 32 1 == 0) = decide (r % 2 < 1) := by decide

/-- `test d, v` -/
private theorem wp_testi {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Fupd s s' → s'.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.imm v) :: is)) s Q :=
  VG.X86.Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

section Loops

variable {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
  {s₀ : State} {g : Reg → BitVec 32} {m₁ : Mem} (hp : BPre s₀) (hst : Stable KP s₀) (hf : BlkOk f F KP)
include hp hst hf

/-- The loads, `f` and the stores, for the blocks `c … c + N - 1` (`N` the
number of registers). -/
theorem blocks_ok (rs : List XReg) (hrs : Lanes rs) (tail : List Instr)
    {Q : State → Prop} {c q : Nat} (hc : c + rs.length ≤ bN s₀) {s : State} (hI : Inv KP F s₀ g m₁ c c q s)
    (hQ : ∀ s', Inv KP F s₀ g m₁ (c + rs.length) c q s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (loadData .esi rs 0)) (.seq (f rs) (.block (storeData .esi rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, h6⟩ := regs_nodup rs hrs
  have hw := hp.fD
  have hlen := (regs_len rs hrs).1
  have haddr : ∀ k, c + k < bN s₀ →
      addr (s.gpr .esi) (16 * (0 + k)) = bAddr s₀ (c + k) := fun k hk => by
    rw [hI.esi, addr_add, addr_eq (by omega_using [hw, hk]), show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega_using []]
  have hout : ∀ k, c + k < bN s₀ → InRegions s.wr (bAddr s₀ (c + k)) 16 := fun k hk =>
    ⟨bDatR s₀, by rw [hI.wr, hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega_using [hk]) (by omega_using [hw, hk])⟩
  refine WP.seq (WP.mono (loadData_ok .esi rs 0 s hnd fun k hk => by
      rw [haddr k (by omega_using [hc, hk])]; exact in_rd (hout k (by omega_using [hc, hk]))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have hkp₁ : KP s₁ := hst s s₁ hI.kp (fun r _ _ => by rw [g₁]) rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (hf rs hrs s₁ hkp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have ek : ∀ k (h : k < rs.length), st (s₂.xmm rs[k]) = F (orig s₀ (c + k)) := fun k h => by
    rw [e₂ _ (List.getElem_mem h), e₁ k h, haddr k (by omega_using [hc, h]), hI.blocks _ (by omega_using [hc, h])]
    simp only [show ¬ c + k < c by omega_using [], ite_false]
  have hesi₂ : s₂.gpr .esi = s.gpr .esi := by rw [f₂.gpr, g₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeData_ok .esi rs 0 s₂ (fun k hk => by
      rw [hesi₂, haddr k (by omega_using [hc, hk]), f₂.wr, wr₁]; exact hout k (by omega_using [hc, hk]))
      (by rw [hesi₂, hI.esi, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc, hw, hlen]),
        Nat.mod_eq_of_lt (by omega_using [hc, hw, hlen])]; omega_using [hc, hw]))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, _⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, m₁]
  rw [hm₂, hesi₂, show 16 * 0 = 16 * (0 + 0) by rfl, haddr 0 (by omega_using [hc, hlen]), Nat.add_zero] at fr₃
  rw [hesi₂] at b₃
  have fr₃' : Frame [bDatR s₀] s.mem s₃.mem :=
    fr₃.sub fun r hr => ⟨bDatR s₀, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by omega_using [hc])⟩
  have g₃' : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, g₁]
  refine ⟨Nat.le_trans (by omega_using []) hc, hst s s₃ hI.kp (fun r _ _ => g₃' r) (by rw [rd₃, f₂.rd, rd₁])
    (by rw [wr₃, f₂.wr, wr₁]) fr₃', fun r h1 h2 => by rw [g₃', hI.gpr r h1 h2],
    by rw [g₃', hI.esi], by rw [g₃', hI.edi], hI.frame.trans fr₃', ?_,
    by rw [rd₃, f₂.rd, rd₁, hI.rd], by rw [wr₃, f₂.wr, wr₁, hI.wr]⟩
  intro k hk
  have out : ¬ (c ≤ k ∧ k < c + rs.length) →
      Spec.Aes.stateAt s₃.mem (bAddr s₀ k) = Spec.Aes.stateAt s.mem (bAddr s₀ k) :=
    fun hn => by
      rw [stateAt_eq, stateAt_eq]
      exact congrArg st <| fr₃.readW (r := ⟨bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_using [hn]) (by omega_using [hw, hk]) (by omega_using [hc, hw])) (by decide)
  by_cases hlo : k < c
  · rw [out (by omega_using [hlo]), hI.blocks k hk]
    simp only [hlo, show k < c + rs.length by omega_using [hlo], ite_true]
  · by_cases hhi : k < c + rs.length
    · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega_using [hlo]⟩
      have hj : j < rs.length := by omega_using [hhi]
      rw [← haddr j (by omega_using [hk]), b₃ j hj, ek j hj]
      simp only [hhi, ite_true]
    · rw [out (by omega_using [hhi]), hI.blocks k hk]
      simp only [hlo, hhi, ite_false]

omit hf in
/-- `add esi, 16 m; sub edi, m`, after `m` more blocks. -/
theorem advance_ok {rest : List Instr} {c m : Nat} (hc : c + m ≤ bN s₀) {s : State}
    (hI : Inv KP F s₀ g m₁ (c + m) c c s) {Q : State → Prop}
    (hQ : ∀ s', Inv KP F s₀ g m₁ (c + m) (c + m) (c + m) s' →
      s'.zf = some (decide (bN s₀ - (c + m) = 0)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .add .esi (.imm (BitVec.ofNat 32 (16 * m))) :: .alu .sub .edi
      (.imm (BitVec.ofNat 32 m)) :: rest)) s Q := by
  have hw := hp.fD
  refine wp_addi fun s₁ u₁ => wp_subi fun s₂ u₂ _ hz => hQ s₂ ?_ ?_
  · have g₂ : ∀ r, r ≠ .esi → r ≠ .edi → s₂.gpr r = s.gpr r := fun r h1 h2 => by
      rw [u₂.other r h2, u₁.other r h1]
    refine ⟨hI.le, hst s s₂ hI.kp g₂ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _), fun r h1 h2 => by rw [g₂ r h1 h2, hI.gpr r h1 h2],
      ?_, ?_, by rw [u₂.mem, u₁.mem]; exact hI.frame, by rw [u₂.mem, u₁.mem]; exact hI.blocks,
      by rw [u₂.rd, u₁.rd, hI.rd], by rw [u₂.wr, u₁.wr, hI.wr]⟩
    · rw [u₂.other _ (by decide), u₁.gpr, hI.esi, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega_using []
    · rw [u₂.gpr, u₁.other _ (by decide), hI.edi]
      have : bN s₀ < 2 ^ 32 := by omega_using [hw]
      bv_omega
  · have hn : bN s₀ < 2 ^ 32 := by omega_using [hw]
    have e : BitVec.ofNat 32 (bN s₀ - c) - BitVec.ofNat 32 m = BitVec.ofNat 32 (bN s₀ - (c + m)) := by
      bv_omega
    rw [hz, u₁.other _ (by decide), hI.edi, e, ofNat_beq_zero (by omega_using [hw])]

omit hp hf in
/-- `Inv` is kept by changing the flags. -/
theorem Inv.fupd {c p q : Nat} {s s' : State} (hI : Inv KP F s₀ g m₁ c p q s) (ug : s'.gpr = s.gpr)
    (um : s'.mem = s.mem) (urd : s'.rd = s.rd) (uwr : s'.wr = s.wr) : Inv KP F s₀ g m₁ c p q s' :=
  { hI with
    kp := hst _ _ hI.kp (fun r _ _ => by rw [ug]) urd uwr (by rw [um]; exact Frame.refl _ _)
    gpr := fun r h1 h2 => by rw [ug, hI.gpr r h1 h2]
    esi := by rw [ug, hI.esi]
    edi := by rw [ug, hI.edi]
    frame := by rw [um]; exact hI.frame
    blocks := by rw [um]; exact hI.blocks
    rd := by rw [urd, hI.rd]
    wr := by rw [uwr, hI.wr] }

omit hp hf in
/-- `add esi, 16 m`, after `m` more blocks: `edi` is as it was. -/
theorem skip_ok {c m q : Nat} {s : State} (hI : Inv KP F s₀ g m₁ (c + m) c q s) :
    WP isa (.block [.alu .add .esi (.imm (BitVec.ofNat 32 (16 * m)))]) s (Inv KP F s₀ g m₁ (c + m) (c + m) q) := by
  refine wp_addi fun s₁ u₁ => WP.block_nil ?_
  exact { hI with
    kp := hst _ _ hI.kp (fun r h1 _ => u₁.other r h1) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _)
    gpr := fun r h1 h2 => by rw [u₁.other r h1, hI.gpr r h1 h2]
    esi := by
      rw [u₁.gpr, hI.esi, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega_using []
    edi := by rw [u₁.other _ (by decide), hI.edi]
    frame := by rw [u₁.mem]; exact hI.frame
    blocks := by rw [u₁.mem]; exact hI.blocks
    rd := by rw [u₁.rd, hI.rd]
    wr := by rw [u₁.wr, hI.wr] }

/-- The turn of six blocks. -/
theorem body6_ok {c : Nat} (hc : c + 6 ≤ bN s₀) {s : State} (hI : Inv KP F s₀ g m₁ c c c s) :
    WP isa (blocks6 f) s fun s' => Inv KP F s₀ g m₁ (c + 6) (c + 6) (c + 6) s' ∧
      s'.cf = some (decide (bN s₀ - (c + 6) < 6)) := by
  have hw := hp.fD
  refine blocks_ok hp hst hf regs6 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  refine advance_ok hp hst (m := 6) hc hI₁ fun s₂ hI₂ _ => ?_
  refine wp_cmpi fun s₃ u₃ hcf _ => WP.block_nil ⟨hI₂.fupd hst u₃.gpr u₃.mem u₃.rd u₃.wr, ?_⟩
  rw [hcf, hI₂.edi, toNat_ofNat_lt (by omega_using [hw])]; rfl

/-- The three blocks, if three are left. -/
theorem three_ok {c : Nat} {s : State} (hI : Inv KP F s₀ g m₁ c c c s) (hlt : bN s₀ - c < 6) :
    WP isa (blocks3 f) s fun s' => ∃ c', bN s₀ - c' < 3 ∧ Inv KP F s₀ g m₁ c' c' c' s' := by
  have hw := hp.fD
  have hle := hI.le
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => Inv KP F s₀ g m₁ c c c s₁ ∧ s₁.cf = some (decide (bN s₀ - c < 3)))
    (wp_cmpi fun s₁ u₁ hcf _ => WP.block_nil ⟨hI.fupd hst u₁.gpr u₁.mem u₁.rd u₁.wr, ?_⟩) fun s₁ ⟨hI₁, hcf₁⟩ => ?_)
  · rw [hcf, hI.edi, toNat_ofNat_lt (by omega_using [hw])]; rfl
  refine WP.ite (decide (bN s₀ - c < 3)) (by simp [eval, hcf₁]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨c, by simpa using h, hI₁⟩
  · obtain hc : c + 3 ≤ bN s₀ := by simp at h; omega_using [h, hle]
    refine blocks_ok hp hst hf regs3 (.inr (.inl rfl)) _ hc hI₁ fun s₂ hI₂ => ?_
    exact advance_ok hp hst (m := 3) (rest := []) hc hI₂ fun s₃ hI₃ _ =>
      WP.block_nil ⟨c + 3, by omega_using [hlt], hI₃⟩

omit hp hf in
/-- `test edi, v`: ZF from the count of blocks from block `q` on. -/
theorem bit_ok {c q : Nat} (v : BitVec 32) {s : State} (hI : Inv KP F s₀ g m₁ c c q s) :
    WP isa (.block [.alu .test .edi (.imm v)]) s fun s' =>
      Inv KP F s₀ g m₁ c c q s' ∧ s'.zf = some (BitVec.ofNat 32 (bN s₀ - q) &&& v == 0) :=
  wp_testi fun s' u hz => WP.block_nil ⟨hI.fupd hst u.gpr u.mem u.rd u.wr, by rw [hz, hI.edi]⟩

/-- A group of the blocks left after block `c`: taken if the count from
block `q` on has the group's bit, which is set when the blocks left are
at least the group's. -/
theorem group_ok (rs : List XReg) (hrs : Lanes rs) (rest : List Instr) {Q : State → Prop} {c q : Nat}
    {s : State} (hI : Inv KP F s₀ g m₁ c c q s)
    (hbit : (BitVec.ofNat 32 (bN s₀ - q) &&& BitVec.ofNat 32 rs.length == 0) = decide (bN s₀ - c < rs.length))
    (hskip : bN s₀ - c < rs.length → ∀ s', Inv KP F s₀ g m₁ c c q s' → Q s')
    (hrun : c + rs.length ≤ bN s₀ → ∀ s', Inv KP F s₀ g m₁ (c + rs.length) c q s' → WP isa (.block rest) s' Q) :
    WP isa (blocksBit f rs rest) s Q := by
  have hle := hI.le
  refine WP.seq (WP.mono (bit_ok hst _ hI) fun s₁ ⟨hI₁, hzf⟩ => ?_)
  rw [hbit] at hzf
  refine WP.ite (decide (bN s₀ - c < rs.length)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (hskip (by simpa using h) _ hI₁)
  · obtain hc : c + rs.length ≤ bN s₀ := by simp at h; omega_using [h, hle]
    exact blocks_ok hp hst hf rs hrs _ hc hI₁ (hrun hc)

/-- The blocks left after `c₀`, six at a time and then three, two and
one. -/
theorem tail_ok {c₀ : Nat} {s₁ : State} (hI₁ : Inv KP F s₀ g m₁ c₀ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (bN s₀ - c₀ < 6))) :
    WP isa (blocksTail f) s₁ fun s => ∃ p q, Inv KP F s₀ g m₁ (bN s₀) p q s := by
  refine WP.seq (WP.mono (Q := fun s => ∃ c, bN s₀ - c < 6 ∧ Inv KP F s₀ g m₁ c c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (bN s₀ - c₀ < 6)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I6 : Nat → State → Prop := fun m s => ∃ c, m = bN s₀ - c ∧ c + 6 ≤ bN s₀ ∧ Inv KP F s₀ g m₁ c c c s
      have hstep : ∀ m s, I6 m s → WP isa (blocks6 f) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, bN s₀ - c < 6 ∧ Inv KP F s₀ g m₁ c c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I6 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body6_ok hp hst hf hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : bN s₀ - (c + 6) < 6
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 6, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], bN s₀ - (c + 6), by omega_using [hc], c + 6, rfl, by omega_using [hlt], hI'⟩
      exact WP.loop (M := isa) I6 hstep (bN s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega_using [h], hI₁⟩
  refine WP.seq (WP.mono (three_ok hp hst hf hI₂ hc) fun s₃ ⟨q, hq, hI₃⟩ => ?_)
  -- The blocks left, fewer than three, as `edi` has them from here on: their bits 2 and 1.
  obtain ⟨b2, b1⟩ := bit_lt (bN s₀ - q) hq
  have hle := hI₃.le
  refine WP.seq (WP.mono (Q := fun s => ∃ c, bN s₀ - c = (bN s₀ - q) % 2 ∧ Inv KP F s₀ g m₁ c c q s)
    (group_ok hp hst hf regs2 (.inr (.inr (.inl rfl))) _ hI₃ (by rw [show regs2.length = 2 from rfl, b2])
      (fun h s' hI' => ⟨q, by rw [show regs2.length = 2 from rfl] at h; omega_using [h], hI'⟩)
      (fun h s' hI' => WP.mono (skip_ok hst (m := 2) hI') fun s'' hI'' =>
        ⟨q + 2, by rw [show regs2.length = 2 from rfl] at h; omega_using [h, hq], hI''⟩))
    fun s₄ ⟨c₄, e₄, hI₄⟩ => ?_)
  refine group_ok hp hst hf regs1 (.inr (.inr (.inr rfl))) _ hI₄ (by rw [show regs1.length = 1 from rfl, b1, e₄])
    (fun h s' hI' => ?_) (fun h s' hI' => WP.block_nil ?_)
  · obtain e : c₄ = bN s₀ := by
      have := hI'.le; rw [show regs1.length = 1 from rfl] at h; omega_using [this, h]
    exact ⟨c₄, q, e ▸ hI'⟩
  · obtain e : c₄ + regs1.length = bN s₀ := by
      rw [show regs1.length = 1 from rfl] at h ⊢; omega_using [h, e₄]
    exact ⟨c₄, q, e ▸ hI'⟩

end Loops

end Ecb

end VG.Proof.Aes.X86.AesNi

end

end

/-!
# AES-NI on x86 (32-bit): `vg_aes_encrypt_blocks_aesni` and `vg_aes_decrypt_blocks_aesni`

`encryptBlocks_verified` and `decryptBlocks_verified` prove
`Impl.Aes.X86.AesNi.encryptBlocks` and `decryptBlocks` against the contracts
of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, through the
per-target contract of the bitsliced implementation (`Proof.Aes.blocksX86`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ argOp aes aesDec blocksPrologue blocksCmp blocksRestore blocksTail imcKeys
  encryptBlocks decryptBlocks)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 in_rd
  addr_add part_contains part_sub_reg part_sub reg_contains in_reg rd_wr_ne blocksτ₀ blocks_agree₀)
open VG.X86.Wp (wp_ldm wp_stm wp_cmpi toNat_ofNat_lt)
open VG.Proof.Aes.X86.AesNi.Ecb

namespace Ecb

/-! ## The prologue -/

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  eax : s.gpr .eax = bSchP s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = bScrP s₀
  esi : s.gpr .esi = bDatP s₀
  edi : s.gpr .edi = arg s₀ 3
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr (bScrP s₀) 0, 8⟩] s₀.mem s.mem
  savedEsi : s.mem.readW (addr (bScrP s₀) 0) 32 = s₀.gpr .esi
  savedEdi : s.mem.readW (addr (bScrP s₀) 4) 32 = s₀.gpr .edi

theorem prologue_ok {s₀ : State} (hp : BPre s₀) : WP isa (.block blocksPrologue) s₀ (P1 s₀) := by
  obtain fB := hp.fB; have fSp := hp.fSp
  let B := bScrP s₀
  let E := s₀.gpr .esp
  obtain hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain hrA : bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain argC : ∀ i < 5, (bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide)
  obtain argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨bArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  obtain hm : (⟨addr B 0, 8⟩ : Region) ∈ [⟨addr B 0, 8⟩] := List.mem_singleton_self _
  obtain dA : ∀ r ∈ [(⟨addr B 0, 8⟩ : Region)], (bArgR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.aB.sub_right (part_sub_reg fB (by omega_arith))
  refine wp_ldm (B := E) (o := 20) rfl (argIn _ rfl 4 (by omega_arith)) fun s₁ u₁ => ?_
  obtain e₁ : s₁.gpr .edx = B := by rw [u₁.gpr]; rfl
  refine wp_stm (B := B) (o := 0) e₁ (by rw [u₁.wr]; exact in_reg hwB fB (by omega_arith) (by decide)) fun s₂ u₂ => ?_
  refine wp_stm (B := B) (o := 4) ((congrFun u₂.gpr _).trans e₁)
    (by rw [u₂.wr, u₁.wr]; exact in_reg hwB fB (by omega_arith) (by decide))
    fun s₃ u₃ => ?_
  obtain esp₃ : s₃.gpr .esp = E := by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain f₃ : Frame [⟨addr B 0, 8⟩] s₀.mem s₃.mem := by
    rw [u₃.mem, u₂.mem, u₁.mem]
    exact ((Frame.refl _ _).writeW hm _ (part_contains fB (by omega_arith) (by omega_arith) (by omega_arith) (by decide))).writeW
      hm _ (part_contains fB (by omega_arith) (by omega_arith) (by omega_arith) (by decide))
  obtain a₃ : ∀ i < 5, s₃.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    f₃.readW (argC i hi) dA (by decide)
  refine wp_ldm (B := E) (o := 4) esp₃ (argIn _ rd₃ 0 (by omega_arith)) fun s₄ u₄ => ?_
  refine wp_ldm (B := E) (o := 8) (by rw [u₄.other _ (by decide)]; exact esp₃)
    (by rw [u₄.rd, u₄.wr]; exact argIn _ rd₃ 1 (by omega_arith)) fun s₅ u₅ => ?_
  refine wp_ldm (B := E) (o := 12) (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact esp₃)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact argIn _ rd₃ 2 (by omega_arith)) fun s₆ u₆ => ?_
  refine wp_ldm (B := E) (o := 16)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide)]; exact esp₃)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact argIn _ rd₃ 3 (by omega_arith)) fun s₇ u₇ =>
    WP.block_nil ?_
  obtain m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain esi₀ : s₂.mem.readW (addr B 0) 32 = s₀.gpr .esi := by
    rw [u₂.mem, u₁.other _ (by decide), Mem.readW_writeW_self32]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃], by rw [m₇]; exact f₃, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    exact a₃ 0 (by omega_arith)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem]
    exact a₃ 1 (by omega_arith)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr]; exact e₁
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem]
    exact a₃ 2 (by omega_arith)
  · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem]
    exact a₃ 3 (by omega_arith)
  · rw [u₇.other r h5, u₆.other r h4, u₅.other r h2, u₄.other r h1, u₃.gpr, u₂.gpr, u₁.other r h3]
  · rw [m₇, u₃.mem, rd_wr_ne fB _ _ (N := 2048) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact esi₀
  · rw [m₇, u₃.mem, u₂.gpr, u₁.other _ (by decide), Mem.readW_writeW_self32]

/-! ## What the transformations need -/

theorem sch_frame {s₀ : State} (hp : BPre s₀) {m : Mem} (hf : Frame [bDatR s₀, bScrR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m ((bSchP s₀).setWidth 64) (16 * (bRounds s₀ + 1)) = sch s₀ := by
  obtain hn : 16 * (bRounds s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨(bSchP s₀).setWidth 64, 16 * (bRounds s₀ + 1)⟩) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dSD.sub_left (Region.sub_prefix hn)
    · exact hp.dSB.sub_left (Region.sub_prefix hn)) (by change 16 * (bRounds s₀ + 1) ≤ 2 ^ 64; omega_arith) hi

/-- The readable round keys and their standard byte representation. -/
theorem keys_of {s₀ s : State} (hp : BPre s₀) (heax : s.gpr .eax = bSchP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hf : Frame [bDatR s₀, bScrR s₀] s₀.mem s.mem) :
    Keys (bRounds s₀) (sch s₀) s := by
  obtain hnr : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  obtain he : ∀ j ≤ bRounds s₀, s.ea (at_ .eax (16 * j)) =
      (bSchP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j) := by
    intro j hj
    rw [ea_at, heax]
    exact addr_eq (by have h := hp.fS; omega_arith)
  refine ⟨hnr, fun j hj => ?_, fun j hj => ?_⟩
  · rw [he j hj, hrd, hwr]
    exact ⟨bSchR s₀, by simp [hp.rd], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [he j hj, ← sch_frame hp hf]
    obtain h := byte_roundKey s.mem ((bSchP s₀).setWidth 64) (L := 16 * (bRounds s₀ + 1)) (j := j) (by omega_arith)
    rw [ofInt_natCast] at h
    exact h

/-- What encryption needs, from `s₀`. -/
def KPe (s₀ : State) (s : State) : Prop :=
  Keys (bRounds s₀) (sch s₀) s ∧ s.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) ∧ s.gpr .eax = bSchP s₀

/-- What decryption needs, from `s₀`. -/
def KPd (s₀ : State) (s : State) : Prop :=
  DKeys (bRounds s₀) (sch s₀) s ∧ s.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) ∧ s.gpr .eax = bSchP s₀ ∧
    s.gpr .edx = bScrP s₀

theorem keys_stable {nr : Nat} {w : List Byte} {s₀ s s' : State} (hp : BPre s₀) (hK : Keys nr w s)
    (hle : 16 * nr + 16 ≤ 240) (heax : s.gpr .eax = bSchP s₀)
    (hg : s'.gpr .eax = s.gpr .eax) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [bDatR s₀] s.mem s'.mem) : Keys nr w s' := by
  obtain he : ∀ j ≤ nr, s'.ea (at_ .eax (16 * j)) = s.ea (at_ .eax (16 * j)) := fun j _ => by
    rw [ea_at, ea_at, hg]
  refine ⟨hK.le, fun j hj => by rw [he j hj, hrd, hwr]; exact hK.keys j hj, fun j hj i hi => ?_⟩
  rw [he j hj, ← hK.bytes j hj i hi, ea_at, heax,
    hf.readW (r := ⟨addr (bSchP s₀) (16 * j), 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.dSD.sub_left (part_sub_reg hp.fS (by omega_arith))).symm.symm) (by decide)]

theorem kpe_stable {s₀ : State} (hp : BPre s₀) : Stable (KPe s₀) s₀ := fun s s' ⟨hK, hc, ha⟩ hg hrd hwr hf => by
  obtain hnr : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  exact ⟨keys_stable hp hK (by omega_arith) ha (hg _ (by decide) (by decide)) hrd hwr hf,
    by rw [hg _ (by decide) (by decide), hc], by rw [hg _ (by decide) (by decide), ha]⟩

theorem kpd_stable {s₀ : State} (hp : BPre s₀) : Stable (KPd s₀) s₀ :=
  fun s s' ⟨hK, hc, ha, hd⟩ hg hrd hwr hf => by
  obtain hnr : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  have fB := hp.fB
  obtain hedx : s'.gpr .edx = s.gpr .edx := hg _ (by decide) (by decide)
  obtain he : ∀ o, s'.ea (at_ .edx o) = s.ea (at_ .edx o) := fun o => by rw [ea_at, ea_at, hedx]
  obtain hm : ∀ o, 16 ≤ o → o + 16 ≤ 240 →
      s'.mem.readW (s.ea (at_ .edx o)) 128 = s.mem.readW (s.ea (at_ .edx o)) 128 := fun o h1 h2 => by
    rw [ea_at, hd]
    exact hf.readW (r := ⟨addr (bScrP s₀) o, 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.dDB.sub_right (part_sub_reg fB (by omega_arith))).symm) (by decide)
  refine ⟨⟨keys_stable hp hK.keys (by omega_arith) ha (hg _ (by decide) (by decide)) hrd hwr hf,
    fun j h1 h2 => ?_, ?_⟩, by rw [hg _ (by decide) (by decide), hc], by rw [hg _ (by decide) (by decide), ha],
    by rw [hedx, hd]⟩
  · obtain ⟨hin, hst⟩ := hK.imc j h1 h2
    exact ⟨by rw [he, hrd, hwr]; exact hin, by rw [he, hm _ (by omega_arith) (by omega_arith)]; exact hst⟩
  · obtain ⟨hin, hb⟩ := hK.last
    exact ⟨by rw [he, hrd, hwr]; exact hin, by rw [he, hm _ (by omega_arith) (by omega_arith)]; exact hb⟩

theorem aes_blkOk {s₀ : State} (hp : BPre s₀) :
    BlkOk aes (Spec.Aes.cipher (bRounds s₀) (sch s₀)) (KPe s₀) :=
  fun rs hrs s ⟨hK, hc, _⟩ => by
    obtain ⟨hnd, h6⟩ := regs_nodup rs hrs
    exact aes_ok rs hnd h6 hp.rounds s hK hc

theorem aesDec_blkOk {s₀ : State} (hp : BPre s₀) :
    BlkOk aesDec (Spec.Aes.invCipher (bRounds s₀) (sch s₀)) (KPd s₀) :=
  fun rs hrs s ⟨hK, hc, _, _⟩ => by
    obtain ⟨hnd, h6⟩ := regs_nodup rs hrs
    exact aesDec_ok rs hnd h6 hp.rounds s hK hc

/-! ## The epilogue -/

/-- From the state after the loops, the restore and the postcondition. -/
theorem finish_ok {F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
    {s₀ s₁ s : State} (hp : BPre s₀) (h₁ : P1 s₀ s₁) {m₁ : Mem}
    (hm₁ : Frame [⟨addr (bScrP s₀) 16, 224⟩] s₁.mem m₁) {p q : Nat}
    (hI : Inv KP (F (bRounds s₀) (sch s₀)) s₀ s₁.gpr m₁ (bN s₀) p q s) :
    WP isa (.block blocksRestore) s fun s' =>
      abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 F).post s₀ s' ∧
        Frame [bDatR s₀, ⟨addr (bScrP s₀) 0, 240⟩] s₀.mem s'.mem := by
  have fB := hp.fB
  obtain hscr : reg32 (bScrP s₀) 2048 ∈ s.rd ++ s.wr := by
    rw [hI.rd, hI.wr, hp.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  obtain hedx : s.gpr .edx = bScrP s₀ := by rw [hI.gpr _ (by decide) (by decide), h₁.edx]
  -- The scratch buffer's first eight bytes are as the prologue left them.
  obtain hsv : ∀ o, o + 4 ≤ 8 → s.mem.readW (addr (bScrP s₀) o) 32 = s₁.mem.readW (addr (bScrP s₀) o) 32 :=
    fun o ho => by
      rw [hI.frame.readW (r := ⟨addr (bScrP s₀) o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dDB.sub_right (part_sub_reg fB (by omega_arith))).symm) (by decide)]
      exact hm₁.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj fB (by omega_arith) (by omega_arith) (.inl (by omega_arith))) (by decide)
  refine wp_ldm (B := bScrP s₀) (o := 0) hedx (in_reg hscr fB (by omega_arith) (by decide)) fun s₂ u₂ => ?_
  refine wp_ldm (B := bScrP s₀) (o := 4) (by rw [u₂.other _ (by decide)]; exact hedx)
    (by rw [u₂.rd, u₂.wr]; exact in_reg hscr fB (by omega_arith) (by decide)) fun s₃ u₃ => WP.block_nil ?_
  obtain hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  -- Everything written since the entry: the scratch buffer and the data.
  obtain G : Frame [bDatR s₀, bScrR s₀] s₀.mem s₃.mem := by
    rw [hm₃]
    refine (h₁.frame.sub fun r hr => ⟨bScrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega_arith)⟩).trans
      ((hm₁.sub fun r hr => ⟨bScrR s₀, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega_arith)⟩).trans
      (hI.frame.mono fun r hr => by simp at hr; simp [hr]))
  -- Of the scratch buffer, only the first 240 bytes.
  obtain G' : Frame [bDatR s₀, ⟨addr (bScrP s₀) 0, 240⟩] s₀.mem s₃.mem := by
    rw [hm₃]
    refine (h₁.frame.sub fun r hr => ⟨⟨addr (bScrP s₀) 0, 240⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_sub fB (by omega_arith) (by omega_arith) (by omega_arith)⟩).trans
      ((hm₁.sub fun r hr => ⟨⟨addr (bScrP s₀) 0, 240⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_sub fB (by omega_arith) (by omega_arith) (by omega_arith)⟩).trans
      (hI.frame.mono fun r hr => by simp at hr; simp [hr]))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, G'⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), hI.gpr _ (by decide) (by decide),
        h₁.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [u₃.other _ (by decide), u₂.gpr, hsv 0 (by omega_arith), h₁.savedEsi]
    · rw [u₃.gpr, u₂.mem, hsv 4 (by omega_arith), h₁.savedEdi]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), hI.gpr _ (by decide) (by decide),
        h₁.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), hI.gpr _ (by decide) (by decide),
        h₁.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · refine G.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.rD
    · exact hp.rB
  · show Spec.Aes.statesAt s₃.mem ((bDatP s₀).setWidth 64) (bN s₀) = _
    rw [hm₃]
    simp only [Spec.Aes.statesAt, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    obtain hk := List.mem_range.mp hk
    have := hI.blocks k hk
    simp only [hk, ite_true] at this
    exact this

/-! ## The two functions -/

theorem dkeys_congr {nr : Nat} {w : List Byte} {s s' : State} (h : DKeys nr w s)
    (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    DKeys nr w s' := by
  obtain he : ∀ m, s'.ea m = s.ea m := fun m => by simp only [State.ea, hg]
  exact ⟨⟨h.keys.le, fun j hj => by rw [he, hrd, hwr]; exact h.keys.keys j hj,
      fun j hj => by rw [he, hm]; exact h.keys.bytes j hj⟩,
    fun j h1 h2 => by rw [he, hrd, hwr, hm]; exact h.imc j h1 h2,
    by rw [he, hrd, hwr, hm]; exact h.last⟩

theorem decrypt_correct {s₀ : State} (hp : BPre s₀) :
    WP isa decryptBlocks s₀ fun s' =>
      abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s₀ s' ∧
        Frame [bDatR s₀, ⟨addr (bScrP s₀) 0, 240⟩] s₀.mem s'.mem := by
  obtain fD := hp.fD; have fB := hp.fB
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  obtain hf₁ : Frame [bDatR s₀, bScrR s₀] s₀.mem s₁.mem := h₁.frame.sub fun r hr => ⟨bScrR s₀, by simp, by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega_arith)⟩
  obtain hs : ImcSetup s₁ :=
    { sch := by rw [h₁.eax, h₁.rd, hp.rd]; exact List.mem_append_left _ (List.mem_cons_self ..)
      scr := by rw [h₁.edx, h₁.wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      fitS := by rw [h₁.eax]; exact hp.fS
      fitB := by rw [h₁.edx]; exact fB
      sep := by rw [h₁.eax, h₁.edx]; exact hp.dSB }
  obtain hK₁ : Keys (bRounds s₀) (sch s₀) s₁ := keys_of hp h₁.eax h₁.rd h₁.wr hf₁
  obtain hc₁ : s₁.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) := by
    rw [h₁.ecx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (imcKeys_ok hs hp.rounds hc₁) fun s₂ hd₂ => ?_)
  obtain hK₂ := dKeys_of_imc hs hK₁ hd₂
  obtain ⟨S, hI₂, -, -⟩ := hd₂
  obtain hm₂ : Frame [⟨addr (bScrP s₀) 16, 224⟩] s₁.mem s₂.mem := by rw [← h₁.edx]; exact hI₂.frame
  refine WP.seq (wp_cmpi fun s₃ u₃ hcf _ => WP.block_nil ?_)
  obtain hI₃ : Inv (KPd s₀) (Spec.Aes.invCipher (bRounds s₀) (sch s₀)) s₀ s₁.gpr s₂.mem 0 0 0 s₃ :=
    { le := Nat.zero_le _
      kp := ⟨dkeys_congr hK₂ u₃.gpr u₃.mem u₃.rd u₃.wr,
        by rw [u₃.gpr, hI₂.gpr, hc₁], by rw [u₃.gpr, hI₂.gpr, h₁.eax], by rw [u₃.gpr, hI₂.gpr, h₁.edx]⟩
      gpr := fun r _ _ => by rw [u₃.gpr, hI₂.gpr]
      esi := by rw [u₃.gpr, hI₂.gpr, h₁.esi]; simp
      edi := by rw [u₃.gpr, hI₂.gpr, h₁.edi]; simp [bN]
      frame := by rw [u₃.mem]; exact Frame.refl _ _
      blocks := fun k hk => by
        simp only [Nat.not_lt_zero, ite_false, orig]
        rw [u₃.mem, stateAt_eq, stateAt_eq]
        obtain G : Frame [bScrR s₀] s₀.mem s₂.mem :=
          (h₁.frame.sub fun r hr => ⟨bScrR s₀, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega_arith)⟩).trans
          (hm₂.sub fun r hr => ⟨bScrR s₀, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega_arith)⟩)
        exact congrArg st <| G.readW (r := ⟨bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hp.dDB.sub_left (Offset.sub_base _ (by omega_arith))) (by decide)
      rd := by rw [u₃.rd, hI₂.rd, h₁.rd]
      wr := by rw [u₃.wr, hI₂.wr, h₁.wr] }
  obtain hcf' : s₃.cf = some (decide (bN s₀ - 0 < 6)) := by
    rw [hcf, hI₂.gpr, h₁.edi, Nat.sub_zero]; rfl
  refine WP.seq (WP.mono (tail_ok hp (kpd_stable hp) (aesDec_blkOk hp) hI₃ hcf') fun s ⟨_, _, hI⟩ => ?_)
  exact finish_ok (KP := KPd s₀) hp h₁ hm₂ hI

end Ecb

/-! ## Encryption

`vg_aes_encrypt_blocks_aesni` keeps the data's address in `edx`, and after
each group of blocks counts the blocks done into `ecx`, from `edx` and the
data's address, compares them with `n`, and reloads `rounds` (`encTest`):
it changes only `eax`, `ecx` and `edx` of the registers, and only the data
in memory. -/

namespace Enc

open VG.Impl.Aes.X86.AesNi (encTest encGroup encBlocks encOnce encPrologue regs6 regs3 regs2 regs1)
open VG.X86.Wp (Upd wp_mov wp_shr wp_addi wp_sub wp_cmp wp_ldm cons readSrc_mem)
open VG.Proof.Aes.X86.AesNi.Ecb (bAddr orig sch Lanes regs_nodup regs_len keys_of keys_stable)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `sub d, [b + o]` -/
private theorem wp_subm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d - s.mem.readW (addr B o) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [reduceExec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

/-- `cmp d, [b + o]`: CF is `d < [b + o]` (unsigned). -/
private theorem wp_cmpm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - s.mem.readW (addr B o) 32)
      (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat))
      (subOverflow (s.gpr d) (s.mem.readW (addr B o) 32) (s.gpr d - s.mem.readW (addr B o) 32)))
    (by simp [reduceExec, execAlu, readSrc_mem hb hin]) (k _ rfl rfl rfl rfl rfl)

/-- `mov d, [b + o]`, which keeps CF. -/
private theorem wp_ldm' {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.mem.readW (addr B o) 32) → s'.cf = s.cf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp [reduceExec, readSrc_mem hb hin]) (k _ (Upd.setReg _ _ _) rfl)

end

/-- `16 n` fits in 32 bits: the data, which does not wrap, is apart from the
arguments. -/
theorem n16 {s₀ : State} (hp : BPre s₀) : 16 * bN s₀ < 2 ^ 32 := by
  have fD := hp.fD
  have fSp := hp.fSp
  refine Nat.lt_of_not_le fun hc => hp.aD (argAddr s₀ 0) (by simp [Region.Contains]) ?_
  obtain h0 : (bDatP s₀).toNat = 0 := by omega_using [fD, hc]
  obtain e0 : (bDatP s₀).setWidth 64 = 0 := BitVec.eq_of_toNat_eq (by simp [h0])
  obtain hA : (argAddr s₀ 0).toNat < 2 ^ 32 := by
    simp only [argAddr, BitVec.toNat_setWidth]; omega_using []
  show (argAddr s₀ 0 - (bDatP s₀).setWidth 64).toNat + 1 ≤ 16 * bN s₀
  obtain e1 : argAddr s₀ 0 - (bDatP s₀).setWidth 64 = argAddr s₀ 0 := by rw [e0]; simp
  rw [e1]
  omega_using [hc, hA]

theorem shr16 {c : Nat} (h : 16 * c < 2 ^ 32) : BitVec.ofNat 32 (16 * c) >>> 4 = BitVec.ofNat 32 c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_using [h])]
  omega_using []

/-- After `c` blocks, with `edx` at block `c` (`ecx` aside): only `eax`,
`ecx` and `edx` and the data have changed. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ bN s₀
  keys : Keys (bRounds s₀) (sch s₀) s
  eax : s.gpr .eax = bSchP s₀
  edx : s.gpr .edx = bDatP s₀ + BitVec.ofNat 32 (16 * c)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  frame : Frame [bDatR s₀] s₀.mem s.mem
  blocks : ∀ k < bN s₀, Spec.Aes.stateAt s.mem (bAddr s₀ k) =
    if k < c then Spec.Aes.cipher (bRounds s₀) (sch s₀) (orig s₀ k) else orig s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem rounds_le : 16 * bRounds s₀ + 16 ≤ 240 := by
  rcases hp.rounds with h | h | h <;> omega_arith

/-- `Inv` is kept by changing `ecx` and the flags, and `eax` to the schedule
again. -/
theorem Inv.of_ecx {c : Nat} {s s' : State} (hI : Inv s₀ c s)
    (hg : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) (ha : s'.gpr .eax = bSchP s₀)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ c s' := by
  exact { hI with
    keys := keys_stable hp hI.keys (rounds_le hp) hI.eax (by rw [ha, hI.eax]) hrd hwr
      (by rw [hm]; exact Frame.refl _ _)
    eax := ha
    edx := by rw [hg _ (by decide) (by decide), hI.edx]
    keep := fun r h1 h2 h3 => by rw [hg r h1 h2, hI.keep r h1 h2 h3]
    frame := by rw [hm]; exact hI.frame
    blocks := by rw [hm]; exact hI.blocks
    rd := by rw [hrd, hI.rd]
    wr := by rw [hwr, hI.wr] }

/-- The argument words, which are read only, are apart from the data. -/
theorem arg_read {s : State} (hrd : s.rd = s₀.rd) (hf : Frame [bDatR s₀] s₀.mem s.mem) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i := by
  have fSp := hp.fSp
  obtain argC : (bArgR s₀).Contains (addr (s₀.gpr .esp) (4 + 4 * i)) 4 := by
    show (⟨addr (s₀.gpr .esp) 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide)
  refine ⟨⟨bArgR s₀, List.mem_append_left _ (by rw [hrd, hp.rd]; simp), argC⟩, ?_⟩
  exact hf.readW argC (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.aD) (by decide)

/-- `encTest k` after `c` blocks: CF is `c + k < n`, and `ecx` holds `rounds`. -/
theorem test_ok {c k : Nat} (hk : k ≤ 5) {s : State} (hI : Inv s₀ c s) :
    WP isa (.block (encTest k)) s fun s' => Inv s₀ c s' ∧
      s'.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) ∧ s'.cf = some (decide (c + k < bN s₀)) := by
  obtain h16 := n16 hp
  have hle := hI.le
  obtain hesp : s.gpr .esp = s₀.gpr .esp := hI.keep _ (by decide) (by decide) (by decide)
  obtain ⟨in0, rd0⟩ := arg_read hp hI.rd hI.frame (i := 0) (by decide)
  obtain ⟨in1, rd1⟩ := arg_read hp hI.rd hI.frame (i := 1) (by decide)
  obtain ⟨in2, rd2⟩ := arg_read hp hI.rd hI.frame (i := 2) (by decide)
  obtain ⟨in3, rd3⟩ := arg_read hp hI.rd hI.frame (i := 3) (by decide)
  refine wp_ldm (B := s₀.gpr .esp) (o := 12) hesp in2 fun s₁ u₁ => ?_
  refine wp_mov fun s₂ u₂ => ?_
  refine wp_sub fun s₃ u₃ _ => ?_
  refine wp_shr (n := 4) (by decide) fun s₄ u₄ _ => ?_
  refine wp_addi fun s₅ u₅ => ?_
  obtain esp₅ : s₅.gpr .esp = s₀.gpr .esp := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hesp]
  obtain rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_ldm (B := s₀.gpr .esp) (o := 16) esp₅ (by rw [rd₅, wr₅]; exact in3) fun s₆ u₆ => ?_
  refine wp_cmp fun s₇ u₇ hcf _ => ?_
  refine wp_ldm' (B := s₀.gpr .esp) (o := 8) (by rw [u₇.gpr, u₆.other _ (by decide), esp₅])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, rd₅, wr₅]; exact in1) fun s₈ u₈ hcf₈ => ?_
  refine wp_ldm' (B := s₀.gpr .esp) (o := 4) (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), esp₅])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, rd₅, wr₅]; exact in0) fun s₉ u₉ hcf₉ => WP.block_nil ?_
  obtain m₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
  obtain e₃ : s₃.gpr .ecx = BitVec.ofNat 32 (16 * c) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.other _ (by decide), rd2, hI.edx,
      BitVec.add_comm, BitVec.add_sub_cancel]
  obtain e₅ : s₅.gpr .ecx = BitVec.ofNat 32 (c + k) := by
    rw [u₅.gpr, u₄.gpr, e₃, shr16 (by omega_using [h16, hle]), BitVec.ofNat_add]
  obtain e₆ : s₆.gpr .eax = arg s₀ 3 := by rw [u₆.gpr, m₅, rd3]
  refine ⟨Inv.of_ecx hp hI (fun r h1 h2 => ?_) ?_ (by rw [m₉]) (by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅])
      (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]), ?_, ?_⟩
  · rw [u₉.other r h1, u₈.other r h2, u₇.gpr, u₆.other r h1, u₅.other r h2, u₄.other r h2, u₃.other r h2,
      u₂.other r h2, u₁.other r h1]
  · rw [u₉.gpr, u₈.mem, u₇.mem, u₆.mem, m₅, rd0]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.mem, u₆.mem, m₅, rd1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hcf₉, hcf₈, hcf, u₆.other _ (by decide), e₅, e₆, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk, h16, hle])]

/-- `rs.length` blocks from block `c`. -/
theorem group_ok (rs : List XReg) (hrs : Lanes rs) {c : Nat}
    (hc : c + rs.length ≤ bN s₀) {s : State} (hI : Inv s₀ c s)
    (hecx : s.gpr .ecx = BitVec.ofNat 32 (bRounds s₀)) :
    WP isa (encGroup rs) s fun s' => Inv s₀ (c + rs.length) s' ∧
      s'.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) := by
  obtain ⟨hnd, h6⟩ := regs_nodup rs hrs
  have hw := hp.fD
  obtain hlen := (regs_len rs hrs).1
  obtain haddr : ∀ j, c + j < bN s₀ → addr (s.gpr .edx) (16 * (0 + j)) = bAddr s₀ (c + j) := fun j hj => by
    rw [hI.edx, addr_add, addr_eq (by omega_using [hw, hj]), show 16 * c + 16 * (0 + j) = 16 * (c + j) by omega_using []]
  obtain hout : ∀ j, c + j < bN s₀ → InRegions s.wr (bAddr s₀ (c + j)) 16 := fun j hj =>
    ⟨bDatR s₀, by rw [hI.wr, hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega_using [hj]) (by omega_using [hw, hj])⟩
  unfold encGroup
  refine WP.seq (WP.mono (loadData_ok .edx rs 0 s hnd fun j hj => by
      rw [haddr j (by omega_using [hc, hj])]; exact in_rd (hout j (by omega_using [hc, hj]))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  obtain hK₁ : Keys (bRounds s₀) (sch s₀) s₁ := keys_stable hp hI.keys (rounds_le hp) hI.eax (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (aes_ok rs hnd h6 hp.rounds s₁ hK₁ (by rw [g₁, hecx])) fun s₂ ⟨e₂, f₂⟩ => ?_)
  obtain ek : ∀ j (h : j < rs.length), st (s₂.xmm rs[j]) =
      Spec.Aes.cipher (bRounds s₀) (sch s₀) (orig s₀ (c + j)) := fun j h => by
    rw [e₂ _ (List.getElem_mem h), e₁ j h, haddr j (by omega_using [hc, h]), hI.blocks _ (by omega_using [hc, h])]
    simp only [show ¬ c + j < c by omega_using [], ite_false]
  obtain hedx₂ : s₂.gpr .edx = s.gpr .edx := by rw [f₂.gpr, g₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeData_ok .edx rs 0 s₂ (fun j hj => by
      rw [hedx₂, haddr j (by omega_using [hc, hj]), f₂.wr, wr₁]; exact hout j (by omega_using [hc, hj]))
      (by rw [hedx₂, hI.edx, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc, hw, hlen]),
        Nat.mod_eq_of_lt (by omega_using [hc, hw, hlen])]; omega_using [hc, hw]))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, _⟩ => ?_
  obtain hm₂ : s₂.mem = s.mem := by rw [f₂.mem, m₁]
  rw [hm₂, hedx₂, show 16 * 0 = 16 * (0 + 0) by rfl, haddr 0 (by omega_using [hc, hlen]), Nat.add_zero] at fr₃
  rw [hedx₂] at b₃
  obtain fr₃' : Frame [bDatR s₀] s.mem s₃.mem :=
    fr₃.sub fun r hr => ⟨bDatR s₀, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by omega_using [hc])⟩
  obtain g₃' : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, g₁]
  obtain blocks₃ : ∀ k < bN s₀, Spec.Aes.stateAt s₃.mem (bAddr s₀ k) =
      if k < c + rs.length then Spec.Aes.cipher (bRounds s₀) (sch s₀) (orig s₀ k) else orig s₀ k := by
    intro k hk
    obtain out : ¬ (c ≤ k ∧ k < c + rs.length) →
        Spec.Aes.stateAt s₃.mem (bAddr s₀ k) = Spec.Aes.stateAt s.mem (bAddr s₀ k) :=
      fun hn => by
        rw [stateAt_eq, stateAt_eq]
        exact congrArg st <| fr₃.readW (r := ⟨bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_using [hn]) (by omega_using [hw, hk]) (by omega_using [hc, hw])) (by decide)
    by_cases hlo : k < c
    · rw [out (by omega_using [hlo]), hI.blocks k hk]
      simp only [hlo, show k < c + rs.length by omega_using [hlo], ite_true]
    · by_cases hhi : k < c + rs.length
      · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega_using [hlo]⟩
        obtain hj : j < rs.length := by omega_using [hhi]
        rw [← haddr j (by omega_using [hk]), b₃ j hj, ek j hj]
        simp only [hhi, ite_true]
      · rw [out (by omega_using [hhi]), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]
  refine wp_addi fun s₄ u₄ => WP.block_nil ⟨?_, by rw [u₄.other _ (by decide), g₃', hecx]⟩
  exact
    { le := hc
      keys := keys_stable hp hI.keys (rounds_le hp) hI.eax (by rw [u₄.other _ (by decide), g₃'])
        (by rw [u₄.rd, rd₃, f₂.rd, rd₁]) (by rw [u₄.wr, wr₃, f₂.wr, wr₁]) (by rw [u₄.mem]; exact fr₃')
      eax := by rw [u₄.other _ (by decide), g₃', hI.eax]
      edx := by
        rw [u₄.gpr, g₃', hI.edx, BitVec.add_assoc, ← BitVec.ofNat_add,
          show 16 * c + 16 * rs.length = 16 * (c + rs.length) by omega_using []]
      keep := fun r h1 h2 h3 => by rw [u₄.other r h3, g₃', hI.keep r h1 h2 h3]
      frame := by rw [u₄.mem]; exact hI.frame.trans fr₃'
      blocks := by rw [u₄.mem]; exact blocks₃
      rd := by rw [u₄.rd, rd₃, f₂.rd, rd₁, hI.rd]
      wr := by rw [u₄.wr, wr₃, f₂.wr, wr₁, hI.wr] }

/-- The turns of six blocks while six are left, after `encTest 5` at block
`c₀`. -/
theorem loop_ok {c₀ : Nat} {s : State} (hI : Inv s₀ c₀ s) (hecx : s.gpr .ecx = BitVec.ofNat 32 (bRounds s₀))
    (hcf : s.cf = some (decide (c₀ + 5 < bN s₀))) :
    WP isa (.ite .ae (.block []) (.loop encBlocks .b)) s fun s' =>
      ∃ c, bN s₀ < c + 6 ∧ Inv s₀ c s' ∧ s'.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) := by
  refine WP.ite (!decide (c₀ + 5 < bN s₀)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨c₀, by simp at h; omega_using [h], hI, hecx⟩
  · let I : Nat → State → Prop := fun m s => ∃ c, m = bN s₀ - c ∧ c + 6 ≤ bN s₀ ∧ Inv s₀ c s ∧
      s.gpr .ecx = BitVec.ofNat 32 (bRounds s₀)
    obtain hstep : ∀ m s, I m s → WP isa encBlocks s (fun s' =>
        (eval .b s' = some false ∧ ∃ c, bN s₀ < c + 6 ∧ Inv s₀ c s' ∧
          s'.gpr .ecx = BitVec.ofNat 32 (bRounds s₀)) ∨
        (eval .b s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨c, rfl, hc, hI, he⟩
      refine WP.seq (WP.mono (group_ok hp regs6 (.inl rfl) hc hI he) fun s₁ ⟨hI₁, _⟩ => ?_)
      refine WP.mono (test_ok hp (k := 5) (by decide) hI₁) fun s' ⟨hI', he', hcf'⟩ => ?_
      rw [show regs6.length = 6 from rfl] at hI' hcf'
      by_cases hlt : c + 6 + 5 < bN s₀
      · exact .inr ⟨by simp [eval, hcf', hlt], bN s₀ - (c + 6), by omega_using [hc], c + 6, rfl,
          by omega_using [hlt], hI', he'⟩
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 6, by omega_using [hlt], hI', he'⟩
    exact WP.loop (M := isa) I hstep (bN s₀ - c₀) s ⟨c₀, rfl, by simp at h; omega_using [h], hI, hecx⟩

/-- A group of the blocks left after block `c`, fewer than twice its
length: taken if that many are left. -/
theorem once_ok (rs : List XReg) (hrs : Lanes rs) {c : Nat} {s : State} (hI : Inv s₀ c s)
    (hlt : bN s₀ < c + 2 * rs.length) :
    WP isa (encOnce rs) s fun s' =>
      ∃ c', bN s₀ < c' + rs.length ∧ Inv s₀ c' s' := by
  obtain ⟨hpos, h6⟩ := regs_len rs hrs
  refine WP.seq (WP.mono (test_ok hp (k := rs.length - 1) (by omega_using [h6]) hI) fun s₁ ⟨hI₁, he₁, hcf₁⟩ => ?_)
  refine WP.ite (!decide (c + (rs.length - 1) < bN s₀)) (by simp [eval, hcf₁]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨c, by simp at h; omega_using [h, hpos], hI₁⟩
  · obtain hc : c + rs.length ≤ bN s₀ := by simp at h; omega_using [h, hpos]
    exact WP.mono (group_ok hp rs hrs hc hI₁ he₁) fun s' ⟨hI', _⟩ => ⟨c + rs.length, by omega_using [hlt], hI'⟩

theorem encrypt_correct :
    WP isa Impl.Aes.X86.AesNi.encryptBlocks s₀ fun s' => abiPreserved s₀ s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.cipher).post s₀ s' ∧ Frame [bDatR s₀] s₀.mem s'.mem := by
  have fD := hp.fD
  obtain ⟨in0, rd0⟩ := arg_read hp (s := s₀) rfl (Frame.refl _ _) (i := 0) (by decide)
  obtain ⟨in2, rd2⟩ := arg_read hp (s := s₀) rfl (Frame.refl _ _) (i := 2) (by decide)
  refine WP.seq ?_
  rw [encPrologue, WP.block_append_iff]
  refine wp_ldm (B := s₀.gpr .esp) (o := 4) rfl in0 fun s₁ u₁ => ?_
  refine wp_ldm (B := s₀.gpr .esp) (o := 12) (u₁.other _ (by decide)) (by rw [u₁.rd, u₁.wr]; exact in2)
    fun s₂ u₂ => WP.block_nil ?_
  obtain hm₂ : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
  obtain hI₂ : Inv s₀ 0 s₂ :=
    { le := Nat.zero_le _
      keys := keys_of hp (by rw [u₂.other _ (by decide), u₁.gpr, rd0]) (by rw [u₂.rd, u₁.rd])
        (by rw [u₂.wr, u₁.wr]) (by rw [hm₂]; exact Frame.refl _ _)
      eax := by rw [u₂.other _ (by decide), u₁.gpr, rd0]
      edx := by rw [u₂.gpr, u₁.mem, rd2]; simp
      keep := fun r h1 _ h3 => by rw [u₂.other r h3, u₁.other r h1]
      frame := by rw [hm₂]; exact Frame.refl _ _
      blocks := fun k _ => by simp only [Nat.not_lt_zero, ite_false, orig, hm₂]
      rd := by rw [u₂.rd, u₁.rd]
      wr := by rw [u₂.wr, u₁.wr] }
  refine WP.mono (test_ok hp (k := 5) (by decide) hI₂) fun s₃ ⟨hI₃, he₃, hcf₃⟩ => ?_
  refine WP.seq (WP.mono (loop_ok hp hI₃ he₃ hcf₃) fun s₄ ⟨c, hc, hI₄, _⟩ => ?_)
  refine WP.seq (WP.mono (once_ok hp regs3 (.inr (.inl rfl)) hI₄ (by rw [show regs3.length = 3 from rfl]; omega_using [hc]))
    fun s₅ ⟨c₅, hc₅, hI₅⟩ => ?_)
  rw [show regs3.length = 3 from rfl] at hc₅
  refine WP.seq (WP.mono (once_ok hp regs2 (.inr (.inr (.inl rfl))) hI₅ (by rw [show regs2.length = 2 from rfl]; omega_using [hc₅]))
    fun s₆ ⟨c₆, hc₆, hI₆⟩ => ?_)
  rw [show regs2.length = 2 from rfl] at hc₆
  refine WP.mono (once_ok hp regs1 (.inr (.inr (.inr rfl))) hI₆ (by rw [show regs1.length = 1 from rfl]; omega_using [hc₆]))
    fun s' ⟨c', hc', hI'⟩ => ?_
  obtain e : c' = bN s₀ := by
    have := hI'.le; rw [show regs1.length = 1 from rfl] at hc'; omega_using [this, hc']
  obtain hI'' : Inv s₀ (bN s₀) s' := e ▸ hI'
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, hI''.frame⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hI''.keep _ (by decide) (by decide) (by decide)
  · exact hI''.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.rD) (by decide)
  · show Spec.Aes.statesAt s'.mem ((bDatP s₀).setWidth 64) (bN s₀) = _
    simp only [Spec.Aes.statesAt, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    obtain hk := List.mem_range.mp hk
    have := hI''.blocks k hk
    simp only [hk, ite_true] at this
    exact this

end

end Enc

end VG.Proof.Aes.X86.AesNi

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86
open VG.Proof.Aes.X86 (BPre blocksτ₀ blocks_agree₀ blocksSat)

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.cipher).post s s' :=
  (Enc.encrypt_correct (BPre.of hs)).imp fun _ ⟨s', he, h, h', _⟩ => ⟨s', he, h, h'⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s s' :=
  (Ecb.decrypt_correct (BPre.of hs)).imp fun _ ⟨s', he, h, h', _⟩ => ⟨s', he, h, h'⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.cipher).pub Impl.Aes.X86.AesNi.encryptBlocks :=
  VG.Taint.constantTime (A := sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub Impl.Aes.X86.AesNi.decryptBlocks :=
  VG.Taint.constantTime (A := sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem encryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.AesNi.encryptBlocks (Proof.Aes.encryptBlocksRoundsContract X86.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct
    (by
      obtain a0 : arg blocksSat 0 = 0x1000 := by decide
      obtain a1 : arg blocksSat 1 = 10 := by decide
      obtain a2 : arg blocksSat 2 = 0x3000 := by decide
      obtain a3 : arg blocksSat 3 = 0 := by decide
      obtain a4 : arg blocksSat 4 = 0x4000 := by decide
      obtain e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

theorem decryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.AesNi.decryptBlocks (Proof.Aes.decryptBlocksRoundsContract X86.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct
    (by
      obtain a0 : arg blocksSat 0 = 0x1000 := by decide
      obtain a1 : arg blocksSat 1 = 10 := by decide
      obtain a2 : arg blocksSat 2 = 0x3000 := by decide
      obtain a3 : arg blocksSat 3 = 0 := by decide
      obtain a4 : arg blocksSat 4 = 0x4000 := by decide
      obtain e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)


/-- `vg_aes_encrypt_blocks_aesni` writes no byte of `scratch`. -/
theorem encryptBlocks_unwritten (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s)
    (t : List Leak) (s' : State) (he : Exec isa Impl.Aes.X86.AesNi.encryptBlocks s t s') :
    ∀ i, 0 ≤ i → i < 2048 →
      s'.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) := by
  obtain hp := BPre.of hs
  have fB := hp.fB
  obtain ⟨t', s'', he', -, -, hf⟩ := Enc.encrypt_correct hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  intro i _ hi
  refine hf _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.dDB _ hc (Offset.contains_base _ (by omega_arith) (by omega_arith))

/-- `vg_aes_decrypt_blocks_aesni` writes only the first 240 bytes of
`scratch`. -/
theorem decryptBlocks_unwritten (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s)
    (t : List Leak) (s' : State) (he : Exec isa Impl.Aes.X86.AesNi.decryptBlocks s t s') :
    ∀ i, 240 ≤ i → i < 2048 →
      s'.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) := by
  obtain hp := BPre.of hs
  have fB := hp.fB
  obtain ⟨t', s'', he', -, -, hf⟩ := Ecb.decrypt_correct hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  intro i h1 hi
  refine hf _ fun r hr hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.dDB _ hc (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · simp only [Region.Contains, addr_zero, BitVec.add_comm ((arg s 4).setWidth 64), BitVec.add_sub_cancel,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [hi])] at hc
    omega_using [h1, hc]

end VG.Proof.Aes.X86.AesNi
