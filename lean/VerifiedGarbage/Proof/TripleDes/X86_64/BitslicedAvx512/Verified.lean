module

public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Pass
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Passes
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Batch
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Ecb
import VerifiedGarbage.Proof.TripleDes.X86_64.SaveRegs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Ecb
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.TripleDes.Bitslice.Layout
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.Sbox

/-! ### `TripleDes.X86_64.BitslicedAvx512.Ecb`, which only this module used -/

section

/-! ### `TripleDes.X86_64.BitslicedAvx512.Wide`, which only this module used -/

section

/-! ### `TripleDes.X86_64.BitslicedAvx512.Batch`, which only this module used -/

section

/-! ### `TripleDes.X86_64.BitslicedAvx512.Passes`, which only this module used -/

section

/-!
# The three AVX-512 passes

The loop of passes, counted down from 3 in `r11`, does to the state words
what three DES passes do (`chain`), with the components and directions of
TDEA, in every lane.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx512 VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (passW pairs swapW)
open VG.Proof.TripleDes.X86_64.Bitsliced (chain keyAt passA passD passComp passIdx_lt passAddr_eq
  keyAt_pass cnt_sub pairs_keys_congr pairs_congr swapW_congr)

/-- The key words of the passes are apart from the scratch buffer and the state. -/
theorem passKeys_apart {s : State} {S : Addr} (hS : ∀ i < 48, Apart s (S + BitVec.ofNat 64 (8 * i)))
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {r : Nat} (hr : r < 16) :
    Apart s (passA d p S + BitVec.ofNat 64 r * passD d p) := by
  simp only [passA, passD]
  rw [BitVec.add_assoc, passAddr_eq d p hp.1 hp.2 r hr]
  exact hS _ (passIdx_lt d p hp.1 hp.2 r hr)

structure PassesInv (d : Direction) (s₀ : State) (p : Nat) (s : State) : Prop where
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ p
  le : p ≤ 3
  words : ∀ x < 64, words s x = chain d (scheduleAt s₀.mem (s₀.gpr .rdi)) (3 - p) (words s₀) x
  count : s.gpr .r11 = BitVec.ofNat 64 p
  gpr : ∀ r, PassRegs r → s.gpr r = s₀.gpr r
  frame : Frame [spillR s₀, stateR s₀] s₀.mem s.mem

structure PassesPost (d : Direction) (s₀ s : State) : Prop where
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, words s x = chain d (scheduleAt s₀.mem (s₀.gpr .rdi)) 3 (words s₀) x
  gpr : ∀ r, PassRegs r → s.gpr r = s₀.gpr r
  frame : Frame [spillR s₀, stateR s₀] s₀.mem s.mem

theorem passes_ok (d : Direction) {s₀ : State}
    (hS : ∀ i < 48, Apart s₀ (s₀.gpr .rdi + BitVec.ofNat 64 (8 * i)))
    (p₀ : Nat) (s₁ : State) (hs₁ : PassesInv d s₀ p₀ s₁) :
    WP isa (.loop (pass d) .ne) s₁ (PassesPost d s₀) := by
  refine WP.loop (M := isa) (PassesInv d s₀) ?_ p₀ s₁ hs₁
  intro p s hs
  let S := s₀.gpr .rdi
  have g : ∀ r, PassRegs r → s.gpr r = s₀.gpr r := hs.gpr
  obtain hS' : s.gpr .rdi = S := g _ (by simp [PassRegs])
  obtain hc := g .rcx (by simp [PassRegs])
  obtain hsi := g .rsi (by simp [PassRegs])
  obtain hp : 1 ≤ p ∧ p ≤ 3 := ⟨hs.pos, hs.le⟩
  obtain hk : ∀ r < 16, Apart s (passA d p (s.gpr .rdi) + BitVec.ofNat 64 r * passD d p) := by
    intro r hr
    rw [hS']
    exact (passKeys_apart hS d hp hr).congr hc hsi hs.rd hs.wr
  apply WP.mono (pass_ok d hp hs.room hs.count hk)
  intro s' q
  obtain keys : ∀ r < 16, keyAt s.mem (passA d p (s.gpr .rdi)) (passD d p) r =
      VG.Proof.TripleDes.roundKey (componentSchedule (scheduleAt s₀.mem S) (passComp d p).1)
        (passComp d p).2 r := by
    intro r hr
    obtain e := (passKeys_apart hS d hp hr).readW hs.frame
    simp only [keyAt, hS']
    rw [e, ← keyAt_pass s₀.mem S d hp hr]; rfl
  obtain words' : ∀ x < 64, words s' x = chain d (scheduleAt s₀.mem S) (3 - p + 1) (words s₀) x := by
    intro x hx
    rw [q.words x hx, pairs_keys_congr 8 (fun r hr => keys r (by omega_using [hr]))]
    simp only [chain, show 3 - (3 - p) = p by omega_using [hp]]
    exact swapW_congr (pairs_congr _ 8 hs.words) x hx
  obtain gpr' : ∀ r, PassRegs r → s'.gpr r = s₀.gpr r := fun r hr => (q.gpr r hr).trans (g r hr)
  obtain frame' : Frame [spillR s₀, stateR s₀] s₀.mem s'.mem := by
    have := q.frame
    rw [show spillR s = spillR s₀ by simp only [spillR, hc],
      show stateR s = stateR s₀ by simp only [stateR, hsi]] at this
    exact hs.frame.trans this
  obtain cntv : s.gpr .r11 - 1 = BitVec.ofNat 64 (p - 1) := by rw [hs.count]; exact cnt_sub p hs.pos
  by_cases h1 : p = 1
  · subst h1
    left
    refine ⟨?_, q.room, q.rd.trans hs.rd, q.wr.trans hs.wr, words', gpr', frame'⟩
    show s'.zf.map (!·) = some false
    rw [q.zf, cntv]; rfl
  · right
    refine ⟨?_, p - 1, by omega_using [hp], ⟨q.room, q.rd.trans hs.rd, q.wr.trans hs.wr, by omega_using [hp, h1],
      by omega_using [hp], ?_, ?_, gpr', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [q.zf, cntv]
      have : (BitVec.ofNat 64 (p - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega_using [hp])] at this
        omega_using [hp, h1, this]
      rw [this]; rfl
    · rw [show 3 - (p - 1) = 3 - p + 1 by omega_using [hp]]; exact words'
    · rw [q.count, cntv]

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

end

end


/-!
# An AVX-512 batch

A batch of 512 blocks, in place: each quadword lane `q` of the 64 state
words (the 4096 bytes at `rsi`) is transposed, so that lane `64 q + i` of
the words is IP of block `8 i + q`; the three passes run; the lanes are
transposed back, and each block becomes its TDEA encryption or decryption
(`batch_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx512
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW ipLane_bit)
open VG.Proof.TripleDes.X86_64.Bitsliced (chain chain_lane blockOut blockOut_cores ipLane_congr wAt
  readW_bit blockAt_of_readW)

/-! ## Quadword lanes as blocks -/

theorem qw_readW (m : Mem) (a : Addr) {q : Nat} (hq : q < 8) :
    qw (m.readW a 512) q = m.readW (a + BitVec.ofNat 64 q * 8) 64 := by
  obtain e := readW_extract m a (w := 512) (k := 8 * q) (n := 8) (by omega_using [hq])
  rw [show 8 * (8 * q) = 64 * q by omega_using [], show 8 * 8 = 64 by rfl] at e
  rw [qw, e]
  congr 2
  rw [BitVec.mul_comm, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_mul_ofNat]

/-- Quadword `q` of state word `i` is block `8 i + q`. -/
theorem laneW_eq (s : State) {q i : Nat} (hq : q < 8) :
    laneW s q i = s.mem.readW (wAt (s.gpr .rsi) (8 * i + q)) 64 := by
  simp only [laneW, words, zAddr]
  rw [qw_readW _ _ hq, BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  obtain e : ∀ a b : Nat, a = b → s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 a) 64 =
      s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 b) 64 := fun a b h => by rw [h]
  exact e _ _ (by omega_using [])

/-- Lane `64 q + i` of 512-bit words is lane `i` of their quadwords `q`. -/
theorem ipLane_qw {W : Nat → BitVec 512} {q i : Nat} (hi : i < 64) :
    ipLane W (64 * q + i) = ipLane (fun j => qw (W j) q) i := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [ipLane_bit _ _ ht, ipLane_bit _ _ ht, getLsbD_qw _ hi]

/-! ## The batch -/

/-- What a batch needs: the scratch buffer and the 512 blocks' state words,
and the schedule's words, readable and apart from both. -/
structure BatchPre (s : State) : Prop where
  room : Room s
  sched : ∀ i < 48, Apart s (s.gpr .rdi + BitVec.ofNat 64 (8 * i))
  schedSep : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint (stateR s)

structure BatchPost (d : Direction) (s s' : State) : Prop where
  out : ∀ b < 512, blockAt s'.mem (wAt (s.gpr .rsi) b) =
    blockOut (scheduleAt s.mem (s.gpr .rdi)) d (blockAt s.mem (wAt (s.gpr .rsi) b))
  rsi : s'.gpr .rsi = s.gpr .rsi + 4096
  rdx : s'.gpr .rdx = s.gpr .rdx - 512
  cf : s'.cf = some (decide ((s.gpr .rdx - 512).toNat < 512))
  gpr : ∀ r, PassRegs r → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [spillR s, stateR s] s.mem s'.mem

theorem frame_into {rs : List Region} {m m' : Mem} {r : Region} (h : Frame [r] m m') (hr : r ∈ rs) :
    Frame rs m m' :=
  h.mono fun r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr

theorem batch_ok (d : Direction) {s : State} (h : BatchPre s) : WP isa (batch d) s (BatchPost d s) := by
  let S := s.gpr .rdi
  let D := s.gpr .rsi
  rw [batch]
  -- the transposition, and the count of passes
  refine WP.seq (WP.mono (transpose_ok h.room.state) fun s₁ ⟨w₁, g₁, rd₁, wr₁, f₁⟩ => ?_)
  apply WP.seq
  let s₂ := s₁.setReg .r11 ((3 : BitVec 32).signExtend 64)
  refine WP.of_runBlock ⟨s₂, (by rw [runBlock_cons]; rfl), ?_⟩
  obtain g₂ : ∀ r, r ≠ .rbx → r ≠ .r11 → s₂.gpr r = s.gpr r := by
    intro r a b
    simp [s₂, gpr_setReg, b, g₁ r a b]
  obtain m₂ : s₂.mem = s₁.mem := by simp [s₂, mem_setReg]
  obtain rd₂ : s₂.rd = s.rd := by simp [s₂, rd_setReg, rd₁]
  obtain wr₂ : s₂.wr = s.wr := by simp [s₂, wr_setReg, wr₁]
  obtain c₂ := g₂ .rcx (by decide) (by decide)
  obtain si₂ := g₂ .rsi (by decide) (by decide)
  obtain di₂ := g₂ .rdi (by decide) (by decide)
  obtain h₂ : Room s₂ := h.room.congr c₂ si₂ wr₂
  obtain words₂ : ∀ j, words s₂ j = words s₁ j := fun j => by
    simp only [words, m₂, si₂, g₁ .rsi (by decide) (by decide)]
  obtain scr₂ : spillR s₂ = spillR s := by simp only [spillR, c₂]
  obtain st₂ : stateR s₂ = stateR s := by simp only [stateR, si₂]
  obtain f₂ : Frame [spillR s, stateR s] s.mem s₂.mem := by
    rw [m₂]; exact frame_into f₁ (List.mem_cons_of_mem _ List.mem_cons_self)
  -- the passes
  apply WP.seq
  obtain hS₂ : ∀ i < 48, Apart s₂ (s₂.gpr .rdi + BitVec.ofNat 64 (8 * i)) := by
    intro i hi; rw [di₂]; exact (h.sched i hi).congr c₂ si₂ rd₂ wr₂
  obtain inv : PassesInv d s₂ 3 s₂ :=
    ⟨h₂, rfl, rfl, by decide, by decide, fun _ _ => rfl, by simp [s₂, gpr_setReg],
      fun _ _ => rfl, Frame.refl _ _⟩
  apply WP.mono (passes_ok d hS₂ 3 s₂ inv)
  intro s₃ q₃
  obtain g₃ : ∀ r, PassRegs r → s₃.gpr r = s.gpr r := by
    intro r hr; rw [q₃.gpr r hr, g₂ r hr.2.1 hr.2.2.2.2.2.1]
  obtain si₃ := g₃ .rsi (by simp [PassRegs])
  obtain c₃ := g₃ .rcx (by simp [PassRegs])
  obtain rdx₃ := g₃ .rdx (by simp [PassRegs])
  -- the transposition back, and the next batch
  refine WP.seq (WP.mono (transpose_ok q₃.room.state) fun s₄ ⟨w₄, g₄, rd₄, wr₄, f₄⟩ => ?_)
  obtain si₄ : s₄.gpr .rsi = D := (g₄ .rsi (by decide) (by decide)).trans si₃
  obtain rdx₄ : s₄.gpr .rdx = s.gpr .rdx := (g₄ .rdx (by decide) (by decide)).trans rdx₃
  let u₁ := (arithFlags s₄ (s₄.gpr .rsi + (4096 : BitVec 32).signExtend 64)
    (decide (2 ^ 64 ≤ (s₄.gpr .rsi).toNat + ((4096 : BitVec 32).signExtend 64).toNat))
    (addOverflow (s₄.gpr .rsi) ((4096 : BitVec 32).signExtend 64)
      (s₄.gpr .rsi + (4096 : BitVec 32).signExtend 64))).setReg .rsi
    (s₄.gpr .rsi + (4096 : BitVec 32).signExtend 64)
  let v := u₁.gpr .rdx - (512 : BitVec 32).signExtend 64
  let u₂ := (arithFlags u₁ v (decide ((u₁.gpr .rdx).toNat < ((512 : BitVec 32).signExtend 64).toNat))
    (subOverflow (u₁.gpr .rdx) ((512 : BitVec 32).signExtend 64) v)).setReg .rdx v
  let s₅ := cmpState u₂ .rdx 512
  refine WP.of_runBlock ⟨s₅, (by
    rw [runBlock_cons, show exec (.alu .add .rsi (.imm 4096)) s₄ = some u₁ from rfl, runStep_some,
      runBlock_cons, show exec (.alu .sub .rdx (.imm 512)) u₁ = some u₂ from rfl, runStep_some,
      cmp_run]), ?_⟩
  obtain m₅ : s₅.mem = s₄.mem := by simp [s₅, cmpState, u₂, u₁, mem_setReg, mem_arithFlags]
  obtain g₅ : ∀ r, r ≠ .rsi → r ≠ .rdx → s₅.gpr r = s₄.gpr r := by
    intro r a b; simp [s₅, cmpState, u₂, u₁, gpr_setReg, a, b]
  obtain rdx₅ : s₅.gpr .rdx = s.gpr .rdx - 512 := by
    simp [s₅, cmpState, u₂, u₁, gpr_setReg, v, rdx₄]
  -- every block of the batch
  obtain K₂ : scheduleAt s₂.mem (s₂.gpr .rdi) = scheduleAt s.mem S := by
    rw [di₂, m₂]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.schedSep
  refine ⟨fun b hb => ?_, ?_, rdx₅, ?_, fun r hr a c => ?_, ?_, ?_, ?_⟩
  · have hq : b % 8 < 8 := Nat.mod_lt _ (by decide)
    obtain hi : b / 8 < 64 := by omega_using [hb]
    obtain eb : 8 * (b / 8) + b % 8 = b := Nat.div_add_mod b 8
    -- lane 64 q + i before the passes: IP of the block
    obtain lane₂ : ipLane (words s₂) (64 * (b % 8) + b / 8) =
        permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [ipLane_qw hi]
      obtain e : ∀ j < 64, qw (words s₂ j) (b % 8) = transposeW (laneW s (b % 8)) j := by
        intro j hj; rw [words₂]; exact w₁ _ hq j hj
      rw [ipLane_congr e]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hi fun j hj => ?_
      rw [laneW_eq s hq, eb]
      exact readW_bit s.mem (wAt D b) hj
    -- the block's word at the end
    obtain word₅ : s₅.mem.readW (wAt D b) 64 = transposeW (laneW s₃ (b % 8)) (b / 8) := by
      rw [m₅, ← w₄ _ hq _ hi, laneW_eq s₄ hq, si₄, eb]
    rw [blockOut_cores, ← K₂]
    apply blockAt_of_readW
    intro j hj
    rw [word₅, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj]
    obtain e₃ : ipLane (laneW s₃ (b % 8)) (b / 8) = ipLane (words s₃) (64 * (b % 8) + b / 8) :=
      (ipLane_qw hi).symm
    rw [e₃, ipLane_congr q₃.words, chain_lane d _ _ (by omega_using [hb]), lane₂]
    rfl
  · simp [s₅, cmpState, u₂, u₁, gpr_setReg, si₄]; rfl
  · have u₂d : u₂.gpr .rdx = s.gpr .rdx - 512 := by
      simp [u₂, u₁, gpr_setReg, v, rdx₄]
    simp only [s₅, cmpState, cf_arithFlags, u₂d,
      show ((512 : BitVec 32).signExtend 64).toNat = 512 by decide]
  · rw [g₅ r a c, g₄ r hr.2.1 hr.2.2.2.2.2.1, g₃ r hr]
  · simp [s₅, cmpState, u₂, u₁, rd_setReg, rd_arithFlags, rd₄, q₃.rd, rd₂]
  · simp [s₅, cmpState, u₂, u₁, wr_setReg, wr_arithFlags, wr₄, q₃.wr, wr₂]
  · have a := q₃.frame
    rw [scr₂, st₂] at a
    obtain b : Frame [spillR s, stateR s] s₃.mem s₄.mem := by
      rw [show stateR s₃ = stateR s by simp only [stateR, si₃]] at f₄
      exact frame_into f₄ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [m₅]
    exact (f₂.trans a).trans b

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

end

end


/-!
# Batches of 512 blocks

While at least 512 blocks are left, the AVX-512 code runs a batch on the next
512 (`wide_ok`): of the `n` blocks, the first `n - n % 512` become their
encryption or decryption, and `rsi` and `rdx` then point at and count the
`n % 512` left. `rbx`, `r12` and `r13`, the callee-saved registers the
batches use, are saved in the scratch buffer and restored.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx512
open VG.Spec.TripleDes
open VG.Proof.TripleDes.X86_64.Bitsliced (blockOut wAt wAt_wAt blockAt_frame toNat_ofNat_of_le)
open VG.Proof.TripleDes.X86_64 (store3_run load3_run)

/-- A region disjoint from a nonempty one does not cover the whole address space. -/
theorem len_lt_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h2 : 0 < r₂.len) : r₁.len < 2 ^ 64 := by
  by_contra hc
  refine h r₂.base ?_ ?_
  · simp only [Region.Contains]; have := (r₂.base - r₁.base).isLt; omega_arith
  · simp only [Region.Contains, BitVec.sub_self]; simp; omega_arith

/-- What the batches may assume of the state they start in: the scratch
buffer and the `n` blocks of data writable (at offset `o` of a writable
region), the schedule readable, apart from each other. -/
structure WideEnv (s : State) : Prop where
  scratch : scratchR s ∈ s.wr
  data : ∃ r ∈ s.wr, ∃ o : Nat, s.gpr .rsi = r.base + BitVec.ofNat 64 o ∧
    o + 8 * (s.gpr .rdx).toNat ≤ r.len ∧ r.len < 2 ^ 64
  keyIn : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * i)) 8
  dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint (scratchR s)
  keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint (scratchR s)
  keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64

theorem WideEnv.len {s : State} (E : WideEnv s) : 8 * (s.gpr .rdx).toNat < 2 ^ 64 :=
  len_lt_of_disjoint E.dataBuf (by simp [scratchR])

/-- The registers the batches change, but for `rsi` and `rdx`. -/
def WideRegs (r : Reg) : Prop := PassRegs r ∧ r ≠ .rsi ∧ r ≠ .rdx

/-- `m` blocks left, a multiple of 512 fewer than `n`, and at least 512. -/
structure WideInv (d : Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  ge : 512 ≤ m
  le : m ≤ n
  mod : m % 512 = n % 512
  rdx : s.gpr .rdx = BitVec.ofNat 64 m
  rsi : s.gpr .rsi = wAt (s₀.gpr .rsi) (n - m)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, blockAt s.mem (wAt (s₀.gpr .rsi) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .rdi)) d (blockAt s₀.mem (wAt (s₀.gpr .rsi) b))
  frame : Frame [spillR s₀, ⟨s₀.gpr .rsi, 8 * (n - m)⟩] s₀.mem s.mem

structure WideLoopPost (d : Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  rdx : s.gpr .rdx = BitVec.ofNat 64 (n % 512)
  rsi : s.gpr .rsi = wAt (s₀.gpr .rsi) (n - n % 512)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - n % 512, blockAt s.mem (wAt (s₀.gpr .rsi) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .rdi)) d (blockAt s₀.mem (wAt (s₀.gpr .rsi) b))
  frame : Frame [spillR s₀, ⟨s₀.gpr .rsi, 8 * (n - n % 512)⟩] s₀.mem s.mem

theorem WideInv.batchPre {d : Direction} {s₀ : State} {n m : Nat} (E : WideEnv s₀)
    (hn : (s₀.gpr .rdx).toNat = n) {s : State} (h : WideInv d s₀ n m s) : BatchPre s := by
  have hl := E.len
  have hfit := E.fit
  have g : ∀ r, WideRegs r → s.gpr r = s₀.gpr r := h.gpr
  obtain hc := g .rcx (by simp [WideRegs, PassRegs])
  obtain hdi := g .rdi (by simp [WideRegs, PassRegs])
  obtain scr : scratchR s = scratchR s₀ := by simp only [scratchR, hc]
  have hge := h.ge
  have hle := h.le
  obtain st : Region.Sub (stateR s) ⟨s₀.gpr .rsi, 8 * n⟩ := by
    simp only [stateR, h.rsi, wAt]
    exact Offset.sub_base _ (by omega_arith)
  obtain dataB : (⟨s₀.gpr .rsi, 8 * n⟩ : Region).Disjoint (scratchR s₀) := hn ▸ E.dataBuf
  refine ⟨⟨by rw [scr, h.wr]; exact E.scratch, ?_, ?_⟩, fun i hi => ⟨?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨r, hr, o, hb, hor, hrl⟩ := E.data
    rw [hn] at hor
    refine Ok.of_off (off := o + 8 * (n - m)) (by rw [h.wr]; exact hr) ?_ ?_ hrl
    · show s.gpr .rsi = _
      rw [h.rsi, wAt, hb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · show o + 8 * (n - m) + 64 * 64 ≤ r.len; omega_arith
  · rw [scr]; exact dataB.sub_left st
  · rw [hdi, h.rd, h.wr]; exact E.keyIn i hi
  · rw [hdi, scr]; exact E.keyBuf.sub_left (Offset.sub_base _ (by omega_arith))
  · rw [hdi]
    exact (E.keyData.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (hn ▸ st)
  · rw [hdi]; exact E.keyData.sub_right (hn ▸ st)

theorem loop_ok (d : Direction) {s₀ : State} (E : WideEnv s₀) {n : Nat}
    (hn : (s₀.gpr .rdx).toNat = n) (m : Nat) (s : State) (hs : WideInv d s₀ n m s) :
    WP isa (.loop (batch d) .ae) s (WideLoopPost d s₀ n) := by
  refine WP.loop (M := isa) (WideInv d s₀ n) ?_ m s hs
  intro m s h
  have hl := E.len
  have hge := h.ge
  have hle := h.le
  apply WP.mono (batch_ok d (h.batchPre E hn))
  intro s' q
  let D := s₀.gpr .rsi
  let S := s₀.gpr .rdi
  have g : ∀ r, WideRegs r → s.gpr r = s₀.gpr r := h.gpr
  obtain hc := g .rcx (by simp [WideRegs, PassRegs])
  obtain hdi := g .rdi (by simp [WideRegs, PassRegs])
  obtain spl : spillR s = spillR s₀ := by simp only [spillR, hc]
  obtain hm : (s.gpr .rdx).toNat = m := by rw [h.rdx]; exact toNat_ofNat_of_le hle (by omega_arith)
  -- the memory written so far
  obtain frame' : Frame [spillR s₀, ⟨D, 8 * (n - (m - 512))⟩] s₀.mem s'.mem := by
    obtain f₁ : Frame [spillR s₀, ⟨D, 8 * (n - (m - 512))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨spillR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 8 * (n - (m - 512))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Region.sub_prefix (by omega_arith)⟩
    obtain f₂ : Frame [spillR s₀, ⟨D, 8 * (n - (m - 512))⟩] s.mem s'.mem := q.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨spillR s₀, List.mem_cons_self, by rw [spl]; exact fun _ h => h⟩
      · refine ⟨⟨D, 8 * (n - (m - 512))⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
        simp only [stateR, h.rsi, wAt]
        exact Offset.sub_base _ (by omega_arith)
    exact f₁.trans f₂
  obtain dataB : (⟨D, 8 * n⟩ : Region).Disjoint (scratchR s₀) := hn ▸ E.dataBuf
  obtain done' : ∀ b < n - (m - 512), blockAt s'.mem (wAt D b) =
      blockOut (scheduleAt s₀.mem S) d (blockAt s₀.mem (wAt D b)) := by
    intro b hb
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame q.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [spl]
        exact (dataB.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (spill_sub s₀)
      · simp only [stateR, h.rsi, wAt]
        exact Offset.disjoint D (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega_arith⟩
      obtain e := q.out j (by omega_arith)
      rw [h.rsi, wAt_wAt, hdi] at e
      rw [e]
      obtain hK : scheduleAt s.mem S = scheduleAt s₀.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact E.keyBuf.sub_right (spill_sub s₀)
          · exact (hn ▸ E.keyData).sub_right (Region.sub_prefix (by omega_arith))
      obtain hB : blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (dataB.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (spill_sub s₀)
          · exact Offset.disjoint_base D (by omega_arith) (by omega_arith)
      rw [hK, hB]
  obtain rdx' : s'.gpr .rdx = BitVec.ofNat 64 (m - 512) := by
    rw [q.rdx, h.rdx, show (512 : BitVec 64) = BitVec.ofNat 64 512 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge]
  obtain rsi' : s'.gpr .rsi = wAt D (n - (m - 512)) := by
    rw [q.rsi, h.rsi, show (4096 : BitVec 64) = BitVec.ofNat 64 (8 * 512) from rfl, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    obtain e : ∀ a b : Nat, a = b → D + BitVec.ofNat 64 a = D + BitVec.ofNat 64 b := fun a b h => by rw [h]
    exact e _ _ (by omega_arith)
  obtain gpr' : ∀ r, WideRegs r → s'.gpr r = s₀.gpr r := fun r hr =>
    (q.gpr r hr.1 hr.2.1 hr.2.2).trans (g r hr)
  obtain cf' : s'.cf = some (decide (m - 512 < 512)) := by
    rw [q.cf, h.rdx, show (512 : BitVec 64) = BitVec.ofNat 64 512 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge, toNat_ofNat_of_le (n := n) (by omega_arith) (by omega_arith)]
  by_cases hend : m - 512 < 512
  · left
    obtain e : m - 512 = n % 512 := by have := h.mod; omega_arith
    refine ⟨by show s'.cf.map (!·) = some false; rw [cf']; simp [hend],
      by rw [rdx', e], by rw [rsi', e], gpr', q.rd.trans h.rd, q.wr.trans h.wr,
      by rw [← e]; exact done', by rw [← e]; exact frame'⟩
  · right
    refine ⟨by show s'.cf.map (!·) = some true; rw [cf']; simp [hend], m - 512, by omega_arith,
      ⟨by omega_arith, by omega_arith, by have := h.mod; omega_arith, rdx', rsi', gpr', q.rd.trans h.rd,
        q.wr.trans h.wr, done', frame'⟩⟩

/-! ## The whole phase -/

structure WidePost (d : Direction) (s s' : State) : Prop where
  rdx : s'.gpr .rdx = BitVec.ofNat 64 ((s.gpr .rdx).toNat % 512)
  rsi : s'.gpr .rsi = wAt (s.gpr .rsi) ((s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 512)
  gpr : ∀ r, WideRegs r → s'.gpr r = s.gpr r
  rbx : s'.gpr .rbx = s.gpr .rbx
  r12 : s'.gpr .r12 = s.gpr .r12
  r13 : s'.gpr .r13 = s.gpr .r13
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  done : ∀ b < (s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 512, blockAt s'.mem (wAt (s.gpr .rsi) b) =
    blockOut (scheduleAt s.mem (s.gpr .rdi)) d (blockAt s.mem (wAt (s.gpr .rsi) b))
  frame : Frame [scratchR s, ⟨s.gpr .rsi, 8 * ((s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 512)⟩]
    s.mem s'.mem

/-- Where `rbx`, `r12` and `r13` are saved: the last 24 bytes of the scratch buffer. -/
def saveR (s : State) : Region := ⟨s.gpr .rcx + BitVec.ofNat 64 1000, 24⟩

theorem save_sub (s : State) : Region.Sub (saveR s) (scratchR s) := Offset.sub_base _ (by decide)

theorem save_spill (s : State) : (saveR s).Disjoint (spillR s) :=
  Offset.disjoint_base _ (by decide) (by decide)

/-- Save slot `k` (`rbx`, `r12`, `r13` at 1016, 1008, 1000). -/
theorem save_in (s : State) {d : Nat} (h1 : 1000 ≤ d) (h2 : d + 8 ≤ 1024) :
    (saveR s).Contains (s.gpr .rcx + BitVec.ofNat 64 d) 8 := Offset.contains _ h1 (by omega_arith) (by decide)

theorem save_wr {s : State} (h : scratchR s ∈ s.wr) {d : Nat} (h1 : 1000 ≤ d) (h2 : d + 8 ≤ 1024) :
    InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 d) 8 :=
  ⟨_, h, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem save_sep (p : Addr) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 1024) (he : e + 8 ≤ 1024) :
    Mem.Sep (p + BitVec.ofNat 64 d) (64 / 8) (p + BitVec.ofNat 64 e) (64 / 8) :=
  Offset.sep p h (by omega_arith) (by omega_arith)

theorem wide_ok (d : Direction) {s : State} (E : WideEnv s) : WP isa (wide d) s (WidePost d s) := by
  let n := (s.gpr .rdx).toNat
  have hl := E.len
  rw [wide]
  apply WP.seq
  let s₁ := cmpState s .rdx 512
  refine WP.of_runBlock ⟨s₁, cmp_run s .rdx 512, ?_⟩
  obtain cf₁ : isa.eval .b s₁ = some (decide (n < 512)) := by
    show s₁.cf = _
    simp only [s₁, cmpState, cf_arithFlags, show ((512 : BitVec 32).signExtend 64).toNat = 512 by decide]
    rfl
  apply WP.ite (decide (n < 512)) cf₁
  · intro hlt
    obtain hlt' : n < 512 := by simpa using hlt
    apply WP.block_nil
    obtain e : n % 512 = n := Nat.mod_eq_of_lt hlt'
    refine ⟨?_, ?_, fun r _ => by simp [s₁, cmpState], by simp [s₁, cmpState], by simp [s₁, cmpState],
      by simp [s₁, cmpState], by simp [s₁, cmpState, rd_arithFlags], by simp [s₁, cmpState, wr_arithFlags],
      fun b hb => by simp only [n] at e; omega_arith, ?_⟩
    · simp only [s₁, cmpState, gpr_arithFlags]
      rw [show (s.gpr .rdx).toNat % 512 = (s.gpr .rdx).toNat from e]; simp
    · simp only [s₁, cmpState, gpr_arithFlags]
      rw [show (s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 512 = 0 by simp only [n] at e; omega_arith]
      simp [wAt]
    · simp only [s₁, cmpState, mem_arithFlags]; exact Frame.refl _ _
  · intro hge
    obtain hge' : 512 ≤ n := by simp at hge; omega_arith
    -- save rbx, r12 and r13
    apply WP.seq
    obtain g₁ : s₁.gpr = s.gpr := by simp [s₁, cmpState]
    obtain wr₁ : s₁.wr = s.wr := by simp [s₁, cmpState, wr_arithFlags]
    let C := s.gpr .rcx
    let a₁ := C + BitVec.ofNat 64 1016
    let a₂ := C + BitVec.ofNat 64 1008
    let a₃ := C + BitVec.ofNat 64 1000
    obtain ea₁ : s₁.ea rbxSave = a₁ := by simp only [State.ea, rbxSave, g₁]; rfl
    obtain ea₂ : s₁.ea r12Save = a₂ := by simp only [State.ea, r12Save, g₁]; rfl
    obtain ea₃ : s₁.ea r13Save = a₃ := by simp only [State.ea, r13Save, g₁]; rfl
    obtain hw : ∀ d, 1000 ≤ d → d + 8 ≤ 1024 → InRegions s₁.wr (C + BitVec.ofNat 64 d) 8 :=
      fun d h1 h2 => by rw [wr₁]; exact save_wr E.scratch h1 h2
    let m₂ := ((s₁.mem.writeW a₁ (s.gpr .rbx)).writeW a₂ (s.gpr .r12)).writeW a₃ (s.gpr .r13)
    let s₂ : State := { s₁ with mem := m₂ }
    refine WP.of_runBlock ⟨s₂, ?_, ?_⟩
    · rw [store3_run (by rw [ea₁]; exact hw 1016 (by decide) (by decide))
        (by rw [ea₂]; exact hw 1008 (by decide) (by decide)) (by rw [ea₃]; exact hw 1000 (by decide) (by decide))]
      simp only [s₂, m₂, ea₁, ea₂, ea₃, g₁]
    have g₂ : s₂.gpr = s.gpr := g₁
    obtain rd₂ : s₂.rd = s.rd := by simp [s₂, s₁, cmpState, rd_arithFlags]
    have wr₂ : s₂.wr = s.wr := wr₁
    obtain f₂ : Frame [saveR s] s.mem s₂.mem := by
      simp only [s₂, m₂, s₁, cmpState, mem_arithFlags]
      exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (save_in s (d := 1016) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (save_in s (d := 1008) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (save_in s (d := 1000) (by decide) (by decide))
    obtain sv₁ : s₂.mem.readW a₁ 64 = s.gpr .rbx := by
      simp only [s₂, m₂]
      rw [Mem.readW_writeW_sep (save_sep C (Or.inr (by decide)) (by decide) (by decide)) (by omega_arith),
        Mem.readW_writeW_sep (save_sep C (Or.inr (by decide)) (by decide) (by decide)) (by omega_arith)]
      exact Mem.readW_writeW_self _ _ 8 _ (by decide)
    obtain sv₂ : s₂.mem.readW a₂ 64 = s.gpr .r12 := by
      simp only [s₂, m₂]
      rw [Mem.readW_writeW_sep (save_sep C (Or.inr (by decide)) (by decide) (by decide)) (by omega_arith)]
      exact Mem.readW_writeW_self _ _ 8 _ (by decide)
    obtain sv₃ : s₂.mem.readW a₃ 64 = s.gpr .r13 := by
      simp only [s₂, m₂]
      exact Mem.readW_writeW_self _ _ 8 _ (by decide)
    obtain E₂ : WideEnv s₂ := by
      obtain sc : scratchR s₂ = scratchR s := by simp only [scratchR, g₂]
      refine ⟨by rw [sc, wr₂]; exact E.scratch, by rw [g₂, wr₂]; exact E.data,
        by rw [g₂, rd₂, wr₂]; exact E.keyIn, by rw [g₂, sc]; exact E.dataBuf,
        by rw [g₂, sc]; exact E.keyBuf, by rw [g₂]; exact E.keyData, by rw [g₂]; exact E.fit⟩
    apply WP.seq
    obtain hn₂ : (s₂.gpr .rdx).toNat = n := by rw [g₂]
    obtain I : WideInv d s₂ n n s₂ := ⟨hge', Nat.le_refl _, rfl, by rw [g₂]; simp [n], by simp [wAt],
      fun _ _ => rfl, rfl, rfl, fun b hb => by omega_arith, by rw [Nat.sub_self]; exact Frame.refl _ _⟩
    apply WP.mono (loop_ok d E₂ hn₂ n s₂ I)
    intro s₃ p₃
    -- restore rbx, r12 and r13
    obtain c₃ : s₃.gpr .rcx = s.gpr .rcx := (p₃.gpr .rcx (by simp [WideRegs, PassRegs])).trans (by rw [g₂])
    obtain keep : ∀ d, 1000 ≤ d → d + 8 ≤ 1024 →
        s₃.mem.readW (C + BitVec.ofNat 64 d) 64 = s₂.mem.readW (C + BitVec.ofNat 64 d) 64 := by
      intro d h1 h2
      refine p₃.frame.readW (r := saveR s) (save_in s h1 h2) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [spillR, g₂]; exact save_spill s
      · rw [g₂]
        exact (E.dataBuf.sub_left (Region.sub_prefix (by omega_arith))).symm.sub_left (save_sub s)
    obtain hld : ∀ t : State, t.gpr .rcx = C → t.rd = s.rd → t.wr = s.wr → ∀ d, 1000 ≤ d → d + 8 ≤ 1024 →
        InRegions (t.rd ++ t.wr) (C + BitVec.ofNat 64 d) 8 := fun t _ _ hw d h1 h2 => by
      rw [hw]; exact (save_wr E.scratch h1 h2).elim fun r ⟨hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩
    let s₄ := ((s₃.setReg .rbx (s.gpr .rbx)).setReg .r12 (s.gpr .r12)).setReg .r13 (s.gpr .r13)
    let s₅ := VOp.vzeroupper.exec s₄
    obtain wr₃ : s₃.wr = s.wr := by rw [p₃.wr, wr₂]
    obtain rd₃ : s₃.rd = s.rd := by rw [p₃.rd, rd₂]
    refine WP.of_runBlock ⟨s₅, ?_, ?_⟩
    · have e₁ : s₃.ea rbxSave = a₁ := by simp only [State.ea, rbxSave, c₃]; rfl
      obtain e₂ : s₃.ea r12Save = a₂ := by simp only [State.ea, r12Save, c₃]; rfl
      obtain e₃ : s₃.ea r13Save = a₃ := by simp only [State.ea, r13Save, c₃]; rfl
      rw [load3_run (v₁ := s.gpr .rbx) (v₂ := s.gpr .r12) (v₃ := s.gpr .r13)
        (by rw [e₁]; exact hld s₃ c₃ rd₃ wr₃ 1016 (by decide) (by decide))
        (by rw [e₂]; exact hld s₃ c₃ rd₃ wr₃ 1008 (by decide) (by decide))
        (by rw [e₃]; exact hld s₃ c₃ rd₃ wr₃ 1000 (by decide) (by decide))
        (by rw [e₁, keep 1016 (by decide) (by decide)]; exact sv₁)
        (by rw [e₂, keep 1008 (by decide) (by decide)]; exact sv₂)
        (by rw [e₃, keep 1000 (by decide) (by decide)]; exact sv₃)
        (by simp only [State.ea, r12Save, gpr_setReg_of_ne _ _ (show Reg.rcx ≠ .rbx by decide)])
        (by simp only [State.ea, r13Save, gpr_setReg_of_ne _ _ (show Reg.rcx ≠ .rbx by decide),
          gpr_setReg_of_ne _ _ (show Reg.rcx ≠ .r12 by decide)]), runBlock_cons]
      rfl
    obtain g₅ : ∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → s₅.gpr r = s₃.gpr r := by
      intro r h1 h2 h3; simp [s₅, s₄, gpr_setReg, h1, h2, h3]
    obtain hm : s₅.mem = s₃.mem := by simp [s₅, s₄, mem_setReg]
    refine ⟨by rw [g₅ _ (by decide) (by decide) (by decide), p₃.rdx],
      by rw [g₅ _ (by decide) (by decide) (by decide), p₃.rsi, g₂],
      fun r hr => by
        have h' := hr
        simp only [WideRegs, PassRegs] at h'
        rw [g₅ r h'.1.2.1 h'.1.2.2.2.2.2.2.1 h'.1.2.2.2.2.2.2.2, p₃.gpr r hr, g₂],
      by simp [s₅, s₄, gpr_setReg], by simp [s₅, s₄, gpr_setReg], by simp [s₅, s₄, gpr_setReg],
      by simp [s₅, s₄, rd_setReg, p₃.rd, rd₂], by simp [s₅, s₄, wr_setReg, p₃.wr, wr₂],
      fun b hb => ?_, ?_⟩
    · have e := p₃.done b hb
      rw [hm]
      simp only [g₂] at e
      rw [e]
      obtain hK : scheduleAt s₂.mem (s.gpr .rdi) = scheduleAt s.mem (s.gpr .rdi) :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame _ f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact E.keyBuf.sub_right (save_sub s)
      obtain hB : blockAt s₂.mem (wAt (s.gpr .rsi) b) = blockAt s.mem (wAt (s.gpr .rsi) b) :=
        blockAt_frame f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (E.dataBuf.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (save_sub s)
      rw [hK, hB]
    · rw [hm]
      obtain a : Frame [scratchR s, ⟨s.gpr .rsi, 8 * (n - n % 512)⟩] s.mem s₂.mem :=
        f₂.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨scratchR s, List.mem_cons_self, save_sub s⟩
      obtain b : Frame [scratchR s, ⟨s.gpr .rsi, 8 * (n - n % 512)⟩] s₂.mem s₃.mem :=
        p₃.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨scratchR s, List.mem_cons_self, by
              simp only [spillR, g₂]; exact spill_sub s⟩
          · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [g₂]; exact fun _ h => h⟩
      exact a.trans b

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

end

end


/-!
# The AVX-512 function

The batches of 512 blocks (`wide_ok`), then the AVX2 code on the blocks
left (`BitslicedAvx2.ecb_post`): every block becomes its encryption or
decryption (`ecb_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx512 VG.Spec.TripleDes
open VG.Proof.TripleDes.X86_64.Bitsliced (blockOut wAt wAt_wAt blockAt_frame EcbPre EcbPost ecb_blocks)

/-- The function on blocks in a writable region apart from the scratch
buffer and the schedule: every block becomes its encryption or decryption
(`EcbPost`). -/
theorem ecb_post (d : Direction) {s : State} (E : WideEnv s)
    (retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩) :
    WP isa (ecb d) s (EcbPost d s) := by
  let n := (s.gpr .rdx).toNat
  let D := s.gpr .rsi
  let S := s.gpr .rdi
  let k := n - n % 512
  have hl := E.len
  have fit := E.fit
  have dataBuf := E.dataBuf
  have keyBuf := E.keyBuf
  have keyData := E.keyData
  obtain ⟨⟨rb, rl⟩, hr, o, hb, hor, hrl⟩ := E.data
  rw [Impl.TripleDes.X86_64.BitsliceAvx512.ecb]
  apply WP.seq
  apply WP.mono (wide_ok d E)
  intro s₁ w
  have g : ∀ r, WideRegs r → s₁.gpr r = s.gpr r := w.gpr
  obtain hc := g .rcx (by simp [WideRegs, PassRegs])
  obtain hdi := g .rdi (by simp [WideRegs, PassRegs])
  obtain hsp := g .rsp (by simp [WideRegs, PassRegs])
  obtain hm : (s₁.gpr .rdx).toNat = n % 512 := by
    rw [w.rdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
  have hD₁ : s₁.gpr .rsi = wAt D k := w.rsi
  obtain sub₁ : Region.Sub ⟨s₁.gpr .rsi, 8 * (s₁.gpr .rdx).toNat⟩ ⟨D, 8 * n⟩ := by
    rw [hD₁, hm]; exact Offset.sub_base _ (by omega_using [])
  obtain E₁ : BitslicedAvx2.WideEnv s₁ := by
    obtain sc : BitslicedAvx2.scratchR s₁ = scratchR s := by
      simp only [BitslicedAvx2.scratchR, scratchR, hc]
    refine ⟨by rw [sc, w.wr]; exact E.scratch, ⟨⟨rb, rl⟩, by rw [w.wr]; exact hr, o + 8 * k, ?_, ?_, hrl⟩,
      fun i hi => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hD₁]; simp only [wAt, D, hb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · rw [hm]; simp only at hor ⊢; omega_using [hor]
    · rw [hdi, w.rd, w.wr]; exact E.keyIn i hi
    · rw [sc]; exact dataBuf.sub_left sub₁
    · rw [hdi, sc]; exact keyBuf
    · rw [hdi]; exact keyData.sub_right sub₁
    · rw [hD₁, hm]
      have hfit : D.toNat + 8 * n ≤ 2 ^ 64 := fit
      obtain hk : k + n % 512 = n := by omega_using []
      simp only [wAt, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega)]
      by_cases hw : D.toNat + 8 * k < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hw]; omega_using [hfit]
      · rw [show D.toNat + 8 * k = 2 ^ 64 by omega_using [hfit, hw], Nat.mod_self]; omega_using []
  apply WP.mono (BitslicedAvx2.ecb_post d E₁ (by rw [hsp]; exact retData.sub_right sub₁)
    (by rw [hsp, hc]; exact retBuf))
  intro s' t
  obtain scr₁ : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = scratchR s := by
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, scratchR, hc]
  have tf := t.frame
  rw [scr₁] at tf
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint (scratchR s) := dataBuf
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun b hb => ?_, ?_⟩
  · rw [t.gpr.1 r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w.rbx
    all_goals first | exact w.r12 | exact w.r13 | exact g _ (by simp [WideRegs, PassRegs])
  · rw [← hsp, t.gpr.2, hsp]
    refine w.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact retBuf
    · exact retData.sub_right (Region.sub_prefix (by omega_using []))
  · by_cases hbk : b < k
    · rw [← w.done b hbk]
      refine blockAt_frame tf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dataB.sub_left (Offset.sub_base _ (by omega_using [hb]))
      · rw [hD₁, hm]
        exact Offset.disjoint D (Or.inl (by omega_using [hbk])) (by omega_using [hl, hb]) (by omega_using [hl])
    · obtain ⟨j, rfl⟩ : ∃ j, b = k + j := ⟨b - k, by omega_using [hbk]⟩
      obtain e := t.done j (by rw [hm]; omega_using [hb])
      rw [hD₁, wAt_wAt, hdi] at e
      rw [e]
      obtain hK : scheduleAt s₁.mem S = scheduleAt s.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S w.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact keyBuf
          · exact keyData.sub_right (Region.sub_prefix (by omega_using []))
      obtain hB : blockAt s₁.mem (wAt D (k + j)) = blockAt s.mem (wAt D (k + j)) :=
        blockAt_frame w.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dataB.sub_left (Offset.sub_base _ (by omega_using [hb]))
          · exact Offset.disjoint_base D (by omega_using []) (by omega_using [hl, hb])
      rw [hK, hB]
  · have a : Frame [scratchR s, ⟨D, 8 * n⟩] s.mem s₁.mem := w.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scratchR s, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 8 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_using [])⟩
    obtain b : Frame [scratchR s, ⟨D, 8 * n⟩] s₁.mem s'.mem := tf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scratchR s, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 8 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, sub₁⟩
    exact a.trans b

/-- `WideEnv` from the regions of the contract. -/
theorem WideEnv.of_regions {s : State} (hrd : s.rd = [⟨s.gpr .rdi, 384⟩])
    (hwr : s.wr = [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 1024⟩])
    (keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64) : WideEnv s := by
  obtain hl := len_lt_of_disjoint dataBuf (by simp)
  refine ⟨by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
    ⟨_, by rw [hwr]; exact List.mem_cons_self, 0, by simp, by simp, hl⟩, fun i hi => ?_,
    dataBuf, keyBuf, keyData, fit⟩
  rw [hrd]
  exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem ecb_ok (d : Direction) {s : State} (hrd : s.rd = [⟨s.gpr .rdi, 384⟩])
    (hwr : s.wr = [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 1024⟩])
    (keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64) :
    WP isa (ecb d) s (fun s' => gprPreserved s s' ∧
      blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
        Spec.TripleDes.ecb (scheduleAt s.mem (s.gpr .rdi)) d
          (blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)) :=
  WP.mono (ecb_post d (WideEnv.of_regions hrd hwr keyData keyBuf dataBuf fit) retData retBuf)
    fun _ p => ⟨p.gpr, ecb_blocks _ _ _ _ _ _ p.done⟩

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

end

end


/-! # The AVX-512 bitsliced ECB functions are correct

The ECB functions run this code with the core's inlined; they are verified
in `EcbCall/Verified.lean`. -/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64
open VG.Proof.TripleDes.X86_64.Bitsliced (contract)

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceAvx512.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := ecb_ok .encrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.BitsliceAvx512.encrypt) (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceAvx512.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := ecb_ok .decrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.BitsliceAvx512.decrypt) (by lit_decide) he ha, hp⟩

end VG.Proof.TripleDes.X86_64.BitslicedAvx512
