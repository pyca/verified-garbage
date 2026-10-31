module

public import VerifiedGarbage.Proof.Aes.RISCV64.Common
public import VerifiedGarbage.Proof.Aes.RISCV64.Decrypt
public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Aes.RISCV64.Keys
import VerifiedGarbage.Proof.Framework.RISCV64.Align

/-!
# AES on whole blocks on RISC-V: the groups

As on x86-64 (`Proof/Aes/X86_64/Ecb.lean`): a group of `blocks` loads (up
to) four blocks of the data into the state registers, a byte at a time
(`Bytes.loadLE64_ok`), runs a transformation of four blocks (`encrypt4` or
`decrypt4`, whose proofs give `CryptOk`), and stores the results back in
place (`Bytes.storeLE64_ok`). The loaded blocks are named by the bytes of
the registers (`regBlock`), so that the last group needs no padding: its
unused blocks are whatever the registers held. The data's invariant
(`EcbInv`) says that the first `k` blocks hold the transformation of the
original ones, and the others are still the original ones.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Steps VG.Bitslice VG.Impl.Aes.RISCV64
  VG.Proof.Aes

/-- The state made of the bytes of the words: byte `i` of block `c` is byte
`i mod 8` of word `c + 4 ⌊i / 8⌋`, as `InRel` places them. -/
def regBlock (Q : Nat → BitVec 64) (c : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (c + 4 * (i.1 / 8))).extractLsb' (8 * (i.1 % 8)) 8

theorem inRel_regBlock (Q : Nat → BitVec 64) : InRel Q (regBlock Q) := by
  intro b _ i hi j hj
  rw [getD_eq _ hi]
  simp [regBlock, hj]

/-- What a transformation of four blocks does: `f R w` to each, with the
round keys as `EncPre` has them. -/
def CryptOk (crypt4 : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {s₀ : State} {X : Addr} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}, EncPre s₀ X R w →
    InRel (Q s₀) S → WP isa crypt4 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => f R w (S b))

theorem encrypt4_cryptOk : CryptOk encrypt4 Spec.Aes.cipher := fun hp hin => encrypt4_ok hp hin
theorem decrypt4_cryptOk : CryptOk decrypt4 Spec.Aes.invCipher := fun hp hin => decrypt4_ok hp hin

/-! ## Loading -/

theorem regBlock_load {Q : Nat → BitVec 64} {m : Mem} {a : Addr} {c : Nat}
    (h₁ : Q c = m.readW a 64) (h₂ : Q (c + 4) = m.readW (a + 8) 64) :
    regBlock Q c = Spec.Aes.stateAt m a := by
  apply Vector.ext
  intro i hi
  refine byte_ext fun j hj => ?_
  simp only [regBlock, Spec.Aes.stateAt, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb', hj,
    decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · rw [show i / 8 = 0 by omega_arith, Nat.mul_zero, Nat.add_zero, h₁, show i % 8 = i by omega_arith,
      readW_bit m a h8 hj]
  · rw [show i / 8 = 1 by omega_arith, Nat.mul_one, h₂, readW_bit m _ (by omega_arith) hj,
      show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add, show 8 + i % 8 = i by omega_arith]

/-- The data after `k` blocks: the first `k` of the `n` blocks at `D` are
`F`'s, the others are still `m₀`'s. -/
def EcbInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem writeW2_apply (m : Mem) (a x : Addr) (v₁ v₂ : BitVec 64) :
    (m.writeW a v₁).writeW (a + 8) v₂ x =
      if (x - a).toNat < 16 then
        (if (x - a).toNat < 8 then v₁.extractLsb' (8 * (x - a).toNat) 8
          else v₂.extractLsb' (8 * ((x - a).toNat - 8)) 8)
      else m x := by
  rw [writeW_apply, writeW_apply, BitVec.setWidth_eq, BitVec.setWidth_eq,
    show x - (a + 8) = x - a - 8 by grind]
  by_cases h8 : (x - a).toNat < 8
  · have : ¬ (x - a - 8).toNat < 64 / 8 := by grind
    simp only [this, h8, ite_false, ite_true, show (x - a).toNat < 16 by omega_arith]
  · by_cases h16 : (x - a).toNat < 16
    · have e : (x - a - 8).toNat = (x - a).toNat - 8 := by grind
      simp only [h8, h16, e, show (x - a).toNat - 8 < 64 / 8 by omega_arith, ite_true, ite_false]
    · have : ¬ (x - a - 8).toNat < 64 / 8 := by grind
      simp only [this, h8, h16, ite_false]

/-- One more block stored. -/
theorem ecbInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {v₁ v₂ : BitVec 64}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : EcbInv m₀ m D n k F)
    (hv : ∀ t < 16, (if t < 8 then v₁.extractLsb' (8 * t) 8 else v₂.extractLsb' (8 * (t - 8)) 8) =
      (F k).getD t 0) :
    EcbInv m₀ ((m.writeW (D + BitVec.ofNat 64 (16 * k)) v₁).writeW (D + BitVec.ofNat 64 (16 * k) + 8) v₂)
        D n (k + 1) F ∧
      Frame [⟨D, 16 * n⟩] m
        ((m.writeW (D + BitVec.ofNat 64 (16 * k)) v₁).writeW (D + BitVec.ofNat 64 (16 * k) + 8) v₂) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [writeW2_apply, off_toNat D (by omega_arith) (by omega_arith)]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, hv _ h2, ite_eq_left (show i < 16 * (k + 1) by omega_arith),
          show i / 16 = k by omega_arith, show i % 16 = i - 16 * k by omega_arith]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega_arith),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega_arith)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega_arith), h i hi,
        ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * (k + 1) by omega_arith)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    rw [writeW2_apply, ite_eq_right]
    have : 16 * k < 2 ^ 64 := by omega_arith
    have : (BitVec.ofNat 64 (16 * k)).toNat = 16 * k := by simp; omega_arith
    bv_omega

theorem ecbInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) (hk : n ≤ k) (hk' : n ≤ k') : EcbInv m₀ m D n k' F := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * k' by omega_arith)]

theorem ecbInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : EcbInv m₀ m D n k F) : EcbInv m₀ m' D n k F := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_arith) hi

/-- Before `k` blocks are stored, a block not yet stored is still `m₀`'s. -/
theorem ecbInv_orig {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) {j : Nat} (hj : k ≤ j) (hjn : j < n) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_right (show ¬ 16 * j + i < 16 * k by omega_arith)]

/-- The bytes of block `c` of the words, when they hold `T`. -/
theorem byte_of_inRel {Q : Nat → BitVec 64} {T : Nat → Spec.Aes.State} (h : InRel Q T) {c t : Nat}
    (hc : c < 4) (ht : t < 16) :
    (Q (c + 4 * (t / 8))).extractLsb' (8 * (t % 8)) 8 = (T c).getD t 0 :=
  byte_ext fun j hj => by
    rw [BitVec.getLsbD_extractLsb', h c hc t ht j hj]
    simp [hj]

theorem q_c4 : ∀ c < 4, q c ≠ .a3 ∧ q (c + 4) ≠ .a3 ∧ q c ≠ q (c + 4) ∧ q c ≠ .a4 ∧
    q (c + 4) ≠ .a4 ∧ q c ≠ sb ∧ q (c + 4) ≠ sb ∧ q c ≠ t0 ∧ q c ≠ t1 ∧ q (c + 4) ≠ t0 ∧
    q (c + 4) ≠ t1 := by decide

theorem q_mem : ∀ c < 8, q c ∈ sboxWrites := by decide

/-! ## The load phase -/

section Load

variable {m₀ : Mem} {D : Addr} {n g : Nat} {F : Nat → Spec.Aes.State} {s₀ : State}

/-- Before the load phase of group `g`. -/
structure LPre (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₀ : State) : Prop where
  hg : 4 * g < n
  hn : 16 * n < 2 ^ 64
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  a3 : s₀.gpr .a3 = D + BitVec.ofNat 64 (64 * g)
  a4 : s₀.gpr .a4 = BitVec.ofNat 64 (n - 4 * g)
  data : EcbInv m₀ s₀.mem D n (4 * g) F

/-- After `k` blocks of the group have been loaded, from `s₀`. -/
structure LS (m₀ : Mem) (D : Addr) (g : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ sboxWrites → s.gpr r = s₀.gpr r
  blk : ∀ c < k, regBlock (Q s) c = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * (4 * g + c)))

theorem ls_t0 {k : Nat} {s s' : State} {v : BitVec 64} (hs : LS m₀ D g s₀ k s) (u : Upd s s' t0 v) :
    LS m₀ D g s₀ k s' := by
  have hQ : Q s' = Q s := funext fun i => u.other _ (q_ne_t0 i)
  exact ⟨u.mem.trans hs.mem, u.rd.trans hs.rd, u.wr.trans hs.wr, u.sp.trans hs.sp,
    fun r h => (u.other r (fun e => h (e ▸ by decide))).trans (hs.keep r h),
    fun c hc => by rw [hQ]; exact hs.blk c hc⟩

theorem ls_step (hp : LPre m₀ D n g F s₀) {k : Nat} (hk : k < 4) (hkn : 4 * g + k < n) {s : State}
    (hs : LS m₀ D g s₀ k s) {P : State → Prop} (h : ∀ s', LS m₀ D g s₀ (k + 1) s' → P s') :
    WP isa (.block (loadBlock k)) s P := by
  have hn := hp.hn
  have hA : ∀ d, s.gpr .a3 + BitVec.ofNat 64 (16 * k + d) =
      D + BitVec.ofNat 64 (16 * (4 * g + k) + d) := fun d => by
    rw [hs.keep _ (by decide), hp.a3, Offset.add_add]; congr 2; omega_arith
  have hD : (⟨D, 16 * n⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ (hs.wr ▸ hp.dat)
  have hin : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .a3 + BitVec.ofNat 64 (16 * k + d)) 4 :=
    fun d hd => by rw [hA]; exact in_off hD (by omega_arith) hn
  obtain ⟨n1, n2, n3, -, -, -, -, n8, n9, n10, n11⟩ := q_c4 k hk
  unfold loadBlock
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.loadLE64_ok (d := q k) (tmp := t0) (hi := t1) (n := .a3) (off := 16 * k)
    n1 (by decide) (by decide) n8 n9 (by decide) (by omega_arith) (by simpa using hin 0 (by omega))
    (hin 4 (by omega))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have a₁ : s₁.gpr .a3 = s.gpr .a3 := g₁ _ (Ne.symm n1) (by decide) (by decide)
  refine WP.mono (Bytes.loadLE64_ok (d := q (k + 4)) (tmp := t0) (hi := t1) (n := .a3)
    (off := 16 * k + 8) n2 (by decide) (by decide) n10 n11 (by decide) (by omega_arith)
    (by rw [a₁, rd₁, wr₁]; exact hin 8 (by omega))
    (by rw [a₁, rd₁, wr₁, show 16 * k + 8 + 4 = 16 * k + 12 by omega]; exact hin 12 (by omega)))
    fun s₂ ⟨e₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have g1 : s₂.gpr (q k) = s.mem.readW (D + BitVec.ofNat 64 (16 * (4 * g + k))) 64 := by
    rw [g₂ _ n3 n8 n9, e₁]
    have := hA 0; simp only [Nat.add_zero] at this; rw [this]
  have g2 : s₂.gpr (q (k + 4)) = s.mem.readW (D + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) 64 := by
    rw [e₂, m₁, a₁, hA, add_off8]
  have o : ∀ r, r ≠ q k → r ≠ q (k + 4) → r ≠ t0 → r ≠ t1 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [g₂ r h2 h3 h4, g₁ r h1 h3 h4]
  refine h s₂ ⟨by rw [m₂, m₁, hs.mem], by rw [rd₂, rd₁, hs.rd], by rw [wr₂, wr₁, hs.wr],
    by rw [sp₂, sp₁, hs.sp],
    fun r hr => (o r (fun e => hr (e ▸ q_mem k (by omega_arith)))
      (fun e => hr (e ▸ q_mem (k + 4) (by omega_arith))) (fun e => hr (e ▸ by decide))
      (fun e => hr (e ▸ by decide))).trans (hs.keep r hr), fun c hc => ?_⟩
  by_cases hck : c = k
  · subst hck
    rw [regBlock_load g1 g2, hs.mem, ecbInv_orig hp.data (by omega_arith) hkn]
  · have hd : ∀ c < 4, ∀ k < 4, c ≠ k → q c ≠ q k ∧ q c ≠ q (k + 4) ∧ q (c + 4) ≠ q k ∧
        q (c + 4) ≠ q (k + 4) := by decide
    obtain ⟨d1, d2, d3, d4⟩ := hd c (by omega_arith) k hk hck
    obtain ⟨-, -, -, -, -, -, -, d5, d6, d7, d8⟩ := q_c4 c (by omega_arith)
    have e : regBlock (Q s₂) c = regBlock (Q s) c := by
      apply Vector.ext; intro i hi
      simp only [regBlock, Vector.getElem_ofFn, Q]
      by_cases h8 : i < 8
      · rw [show i / 8 = 0 by omega_arith, Nat.mul_zero, Nat.add_zero, o _ d1 d2 d5 d6]
      · rw [show i / 8 = 1 by omega_arith, Nat.mul_one, o _ d3 d4 d7 d8]
    rw [e, hs.blk c (by omega_arith)]

theorem ls_zero {s : State} (hg : ∀ r, r ≠ t0 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) : LS m₀ D g s₀ 0 s :=
  ⟨hm, hrd, hwr, hsp, fun r hr => hg r (fun e => hr (e ▸ by decide)),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem loadFull_eq : loadFull = loadBlock 0 ++ loadBlock 1 ++ loadBlock 2 ++ loadBlock 3 := by
  simp only [loadFull, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- The loads of a group, after `srli t0, a4, 2`. -/
theorem loadIte_wp (hp : LPre m₀ D n g F s₀) {s : State}
    (hev : isa.eval (.nonzero t0) s = some (decide (4 ≤ n - 4 * g)))
    (hls : LS m₀ D g s₀ 0 s) :
    WP isa (.ite (.nonzero t0) (.block loadFull) loadTail) s fun s' =>
      LS m₀ D g s₀ (min 4 (n - 4 * g)) s' := by
  have hg := hp.hg
  have hn := hp.hn
  refine WP.ite (decide (4 ≤ n - 4 * g)) hev (fun hb => ?_) (fun hb => ?_)
  · have h4 : 4 ≤ n - 4 * g := by simpa using hb
    rw [loadFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine ls_step hp (k := 0) (by omega_arith) (by omega_arith) hls fun s₁ x₁ => ?_
    refine ls_step hp (k := 1) (by omega_arith) (by omega_arith) x₁ fun s₂ x₂ => ?_
    refine ls_step hp (k := 2) (by omega_arith) (by omega_arith) x₂ fun s₃ x₃ => ?_
    refine ls_step hp (k := 3) (by omega_arith) (by omega_arith) x₃ fun s₄ x₄ => ?_
    rw [show min 4 (n - 4 * g) = 3 + 1 by omega_arith]; exact x₄
  · have h4 : n - 4 * g < 4 := by simpa using hb
    unfold loadTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine ls_step hp (k := 0) (by omega_arith) (by omega_arith) hls fun s₁ x₁ => ?_
    refine wp_subi (imm := 1) (by decide) fun s₂ u₂ => WP.block_nil ?_
    have x₂ := ls_t0 x₁ u₂
    have t₂ : s₂.gpr t0 = BitVec.ofNat 64 (n - 4 * g - 1) := by
      rw [u₂.gpr, x₁.keep _ (by decide), hp.a4, ofNat_sub_ofNat' (by omega_arith)]
    refine WP.ite (decide (n - 4 * g - 1 ≠ 0)) (Steps.eval_nonzero_ofNat s₂ t0 (by omega_arith) t₂)
      (fun hb => ?_) (fun hb => ?_)
    · have h2 : 2 ≤ n - 4 * g := by simp at hb; omega_arith
      refine WP.seq ?_
      rw [WP.block_append_iff (M := isa)]
      refine ls_step hp (k := 1) (by omega_arith) (by omega_arith) x₂ fun s₃ x₃ => ?_
      refine wp_subi (imm := 3) (by decide) fun s₄ u₄ => WP.block_nil ?_
      have x₄ := ls_t0 x₃ u₄
      have z₄ : isa.eval (.zero t0) s₄ = some (decide (n - 4 * g = 3)) := by
        rw [eval_zero, u₄.gpr, x₃.keep _ (by decide), hp.a4]
        congr 1
        have : n - 4 * g = 2 ∨ n - 4 * g = 3 := by omega_arith
        rcases this with h | h <;> rw [h] <;> decide
      refine WP.ite (decide (n - 4 * g = 3)) z₄ (fun hb => ?_) (fun hb => ?_)
      · have h3 : min 4 (n - 4 * g) = 2 + 1 := by simp at hb; omega_arith
        refine ls_step hp (k := 2) (by omega_arith) (by omega_arith) x₄ fun s₅ x₅ => ?_
        rw [h3]; exact x₅
      · have h3 : min 4 (n - 4 * g) = 2 := by simp at hb; omega_arith
        refine WP.block_nil ?_
        rw [h3]; exact x₄
    · have h1 : min 4 (n - 4 * g) = 1 := by simp at hb; omega_arith
      refine WP.block_nil ?_
      rw [h1]; exact x₂

end Load

/-! ## The store phase -/

section Store

variable {m₀ : Mem} {D : Addr} {n g : Nat} {F : Nat → Spec.Aes.State} {s₃ : State}

/-- Before the store phase of group `g`: the results are in the words. -/
structure SPre (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) : Prop where
  hg : 4 * g < n
  hn : 16 * n < 2 ^ 64
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₃.wr
  a3 : s₃.gpr .a3 = D + BitVec.ofNat 64 (64 * g)
  a4 : s₃.gpr .a4 = BitVec.ofNat 64 (n - 4 * g)
  data : EcbInv m₀ s₃.mem D n (4 * g) F
  out : ∀ c < 4, 4 * g + c < n → ∀ t < 16,
    (s₃.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 = (F (4 * g + c)).getD t 0

/-- After `k` blocks of the group have been stored, from `s₃`. -/
structure SS (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) (k : Nat)
    (s : State) : Prop where
  data : EcbInv m₀ s.mem D n (4 * g + k) F
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ t0 → r ≠ t1 → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  sp : s.sp = s₃.sp

/-- After the store phase: no blocks are left, or group `g + 1` is next. -/
def SDone (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ s : State) : Prop :=
  Frame [⟨D, 16 * n⟩] s₃.mem s.mem ∧
    (∀ r, r ≠ t0 → r ≠ t1 → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    ((s.gpr .a4 = 0 ∧ EcbInv m₀ s.mem D n n F) ∨
     (4 * g + 4 < n ∧ EcbInv m₀ s.mem D n (4 * (g + 1)) F ∧
      s.gpr .a3 = D + BitVec.ofNat 64 (64 * (g + 1)) ∧ s.gpr .a4 = BitVec.ofNat 64 (n - 4 * (g + 1))))

theorem ss_step (hp : SPre m₀ D n g F s₃) {k : Nat} (hk : k < 4) (hkn : 4 * g + k < n) {s : State}
    (hs : SS m₀ D n g F s₃ k s) {P : State → Prop} (h : ∀ s', SS m₀ D n g F s₃ (k + 1) s' → P s') :
    WP isa (.block (storeBlock k)) s P := by
  have hn := hp.hn
  have hA : ∀ d, s.gpr .a3 + BitVec.ofNat 64 (16 * k + d) =
      D + BitVec.ofNat 64 (16 * (4 * g + k) + d) := fun d => by
    rw [hs.keep _ (by decide) (by decide), hp.a3, Offset.add_add]; congr 2; omega_arith
  have hD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := hs.wr ▸ hp.dat
  have hin : ∀ d, d + 4 ≤ 16 → InRegions s.wr (s.gpr .a3 + BitVec.ofNat 64 (16 * k + d)) 4 :=
    fun d hd => by rw [hA]; exact in_off hD (by omega_arith) hn
  obtain ⟨-, -, -, -, -, -, -, n8, n9, n10, n11⟩ := q_c4 k hk
  have A0 : s.gpr .a3 + BitVec.ofNat 64 (16 * k) = D + BitVec.ofNat 64 (16 * (4 * g + k)) := by
    simpa using hA 0
  unfold storeBlock
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.storeLE64_ok (v := q k) (tmp := t0) (hi := t1) (n := .a3) (off := 16 * k)
    (Ne.symm n8) (by decide) (by decide) (by decide) (by omega_arith) (by simpa using hin 0 (by omega))
    (hin 4 (by omega))) fun s₁ ⟨m₁, g₁, rd₁, wr₁, sp₁⟩ => ?_
  have a₁ : s₁.gpr .a3 = s.gpr .a3 := g₁ _ (by decide) (by decide)
  have v₁ : s₁.gpr (q (k + 4)) = s.gpr (q (k + 4)) := g₁ _ n10 n11
  refine WP.mono (Bytes.storeLE64_ok (v := q (k + 4)) (tmp := t0) (hi := t1) (n := .a3)
    (off := 16 * k + 8) (Ne.symm n10) (by decide) (by decide) (by decide) (by omega_arith)
    (by rw [a₁, wr₁]; exact hin 8 (by omega))
    (by rw [a₁, wr₁, show 16 * k + 8 + 4 = 16 * k + 12 by omega]; exact hin 12 (by omega)))
    fun s₂ ⟨m₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  have e1 : s.gpr .a3 + BitVec.ofNat 64 (16 * k + 4) =
      s.gpr .a3 + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 4 := (Offset.add_add _ _ _).symm
  have e2 : s.gpr .a3 + BitVec.ofNat 64 (16 * k + 8 + 4) =
      s.gpr .a3 + BitVec.ofNat 64 (16 * k + 8) + BitVec.ofNat 64 4 := (Offset.add_add _ _ _).symm
  have hm : s₂.mem = (s.mem.writeW (D + BitVec.ofNat 64 (16 * (4 * g + k))) (s.gpr (q k))).writeW
      (D + BitVec.ofNat 64 (16 * (4 * g + k)) + 8) (s.gpr (q (k + 4))) := by
    rw [m₂, a₁, v₁, m₁, e1, e2, Words64.writeW64_split, Words64.writeW64_split, A0, hA 8, add_off8]
  have hst := ecbInv_step (v₁ := s.gpr (q k)) (v₂ := s.gpr (q (k + 4))) (by omega_arith) hkn hs.data
    (fun t ht => by
      rw [hs.keep _ n8 n9, hs.keep _ n10 n11, ← hp.out k hk hkn t ht]
      by_cases h8 : t < 8
      · rw [ite_eq_left h8, show t / 8 = 0 by omega_arith, show t % 8 = t by omega_arith, Nat.mul_zero, Nat.add_zero]
      · rw [ite_eq_right h8, show t / 8 = 1 by omega_arith, show t % 8 = t - 8 by omega_arith, Nat.mul_one])
  rw [← hm] at hst
  exact h s₂ ⟨hst.1, hs.frame.trans hst.2, fun r hr hr' => by
      rw [g₂ r hr hr', g₁ r hr hr']; exact hs.keep r hr hr',
    by rw [rd₂, rd₁, hs.rd], by rw [wr₂, wr₁, hs.wr], by rw [sp₂, sp₁, hs.sp]⟩

theorem ss_t0 {k : Nat} {s s' : State} {v : BitVec 64} (hs : SS m₀ D n g F s₃ k s) (u : Upd s s' t0 v) :
    SS m₀ D n g F s₃ k s' :=
  ⟨u.mem ▸ hs.data, u.mem ▸ hs.frame, fun r h h' => (u.other r h).trans (hs.keep r h h'),
    u.rd.trans hs.rd, u.wr.trans hs.wr, u.sp.trans hs.sp⟩

theorem ss_zero (hp : SPre m₀ D n g F s₃) {s : State} (hg : ∀ r, r ≠ t0 → s.gpr r = s₃.gpr r)
    (hm : s.mem = s₃.mem) (hrd : s.rd = s₃.rd) (hwr : s.wr = s₃.wr) (hsp : s.sp = s₃.sp) :
    SS m₀ D n g F s₃ 0 s :=
  ⟨by rw [hm, Nat.add_zero]; exact hp.data, by rw [hm]; exact Frame.refl _ _,
    fun r h _ => hg r h, hrd, hwr, hsp⟩

theorem storeFull_eq : storeFull = storeBlock 0 ++ storeBlock 1 ++ storeBlock 2 ++ storeBlock 3 ++
    ([.addi .a3 .a3 64, .addi .a4 .a4 (-4)] : List Instr) := by
  simp only [storeFull, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem storePhase_wp (hp : SPre m₀ D n g F s₃) :
    WP isa (.seq (.block [shrI t0 .a4 2]) (.ite (.nonzero t0) (.block storeFull) storeTail)) s₃
      (SDone m₀ D n g F s₃) := by
  have hg := hp.hg
  have hn := hp.hn
  refine shr2_wp (k := n - 4 * g) (by omega_arith) hp.a4 fun s₄ u₄ ev₄ => ?_
  have x₀ := ss_zero hp (fun r h => u₄.other r h) u₄.mem u₄.rd u₄.wr u₄.sp
  refine WP.ite (decide (4 ≤ n - 4 * g)) ev₄ (fun hb => ?_) (fun hb => ?_)
  · -- Four blocks.
    have h4 : 4 ≤ n - 4 * g := by simpa using hb
    rw [storeFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine ss_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine ss_step hp (k := 1) (by omega_arith) (by omega_arith) x₅ fun s₆ x₆ => ?_
    refine ss_step hp (k := 2) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
    refine ss_step hp (k := 3) (by omega_arith) (by omega_arith) x₇ fun s₈ x₈ => ?_
    refine wp_addi (imm := 64) (by decide) fun s₉ u₉ => wp_subi (imm := 4) (by decide)
      fun s₁₀ u₁₀ => WP.block_nil ?_
    have e₁ : s₈.gpr .a3 = D + BitVec.ofNat 64 (64 * g) := (x₈.keep _ (by decide) (by decide)).trans hp.a3
    have e₂ : s₈.gpr .a4 = BitVec.ofNat 64 (n - 4 * g) := (x₈.keep _ (by decide) (by decide)).trans hp.a4
    have r7' : s₁₀.gpr .a4 = BitVec.ofNat 64 (n - 4 * (g + 1)) := by
      rw [u₁₀.gpr, u₉.other _ (by decide), e₂, ofNat_sub_ofNat' h4,
        show n - 4 * g - 4 = n - 4 * (g + 1) by omega_arith]
    refine ⟨by rw [u₁₀.mem, u₉.mem]; exact x₈.frame, fun r h1 h1' h2 h3 => ?_,
      by rw [u₁₀.rd, u₉.rd]; exact x₈.rd, by rw [u₁₀.wr, u₉.wr]; exact x₈.wr,
      by rw [u₁₀.sp, u₉.sp]; exact x₈.sp, ?_⟩
    · rw [u₁₀.other _ h3, u₉.other _ h2]; exact x₈.keep r h1 h1'
    have hd : EcbInv m₀ s₁₀.mem D n (4 * (g + 1)) F := by
      rw [u₁₀.mem, u₉.mem]; simpa [Nat.mul_add] using x₈.data
    by_cases hl : n - 4 * g = 4
    · refine .inl ⟨by rw [r7', show n - 4 * (g + 1) = 0 by omega_arith]; rfl,
        ecbInv_mono hd (by omega_arith) (by omega_arith)⟩
    · refine .inr ⟨by omega_arith, hd, ?_, r7'⟩
      rw [u₁₀.other _ (by decide), u₉.gpr, e₁]; exact off_add64 D g
  · -- The last one to three blocks.
    have h4 : n - 4 * g < 4 := by simpa using hb
    unfold storeTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine ss_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine wp_subi (imm := 1) (by decide) fun s₆ u₆ => WP.block_nil ?_
    have x₆ := ss_t0 x₅ u₆
    have t₆ : s₆.gpr t0 = BitVec.ofNat 64 (n - 4 * g - 1) := by
      rw [u₆.gpr, x₅.keep _ (by decide) (by decide), hp.a4, ofNat_sub_ofNat' (by omega_arith)]
    refine WP.seq (WP.mono (Q := SS m₀ D n g F s₃ (n - 4 * g)) ?_ fun s hs => ?_)
    · refine WP.ite (decide (n - 4 * g - 1 ≠ 0)) (Steps.eval_nonzero_ofNat s₆ t0 (by omega_arith) t₆)
        (fun hb => ?_) (fun hb => ?_)
      · have h2 : 2 ≤ n - 4 * g := by simp at hb; omega_arith
        refine WP.seq ?_
        rw [WP.block_append_iff (M := isa)]
        refine ss_step hp (k := 1) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
        refine wp_subi (imm := 3) (by decide) fun s₈ u₈ => WP.block_nil ?_
        have x₈ := ss_t0 x₇ u₈
        have z₈ : isa.eval (.zero t0) s₈ = some (decide (n - 4 * g = 3)) := by
          rw [eval_zero, u₈.gpr, x₇.keep _ (by decide) (by decide), hp.a4]
          congr 1
          have : n - 4 * g = 2 ∨ n - 4 * g = 3 := by omega_arith
          rcases this with h | h <;> rw [h] <;> decide
        refine WP.ite (decide (n - 4 * g = 3)) z₈ (fun hb => ?_) (fun hb => ?_)
        · have h3 : n - 4 * g = 2 + 1 := by simp at hb; omega_arith
          refine ss_step hp (k := 2) (by omega_arith) (by omega_arith) x₈ fun s₉ x₉ => ?_
          rw [h3]; exact x₉
        · have h3 : n - 4 * g = 2 := by simp at hb; omega_arith
          exact WP.block_nil (by rw [h3]; exact x₈)
      · have h1 : n - 4 * g = 1 := by simp at hb; omega_arith
        exact WP.block_nil (by rw [h1]; exact x₆)
    · refine wp_li (imm := 0) (by decide) fun s' u' => WP.block_nil ?_
      refine ⟨by rw [u'.mem]; exact hs.frame, fun r h1 h1' _ h3 => (u'.other r h3).trans (hs.keep r h1 h1'),
        by rw [u'.rd]; exact hs.rd, by rw [u'.wr]; exact hs.wr, by rw [u'.sp]; exact hs.sp,
        .inl ⟨u'.gpr, ?_⟩⟩
      have := hs.data
      rw [show 4 * g + (n - 4 * g) = n by omega_arith, ← u'.mem] at this
      exact this

end Store

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `X` the scratch buffer (rounded to `b`), `D` the data (`n`
blocks). -/
structure ESetup (s₂ : State) (X b D : Addr) (n R : Nat) (w : List Byte) : Prop where
  scr : Scr s₂ X 2048
  base : s₂.gpr sb = b
  masks : MasksAt s₂.mem b allKs
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₂.wr
  hn : 16 * n < 2 ^ 64
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨X, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w

/-- The memory a group writes: slots 0–39 and the data. -/
abbrev eRegions (b D : Addr) (n : Nat) : List Region := [⟨b, 320⟩, ⟨D, 16 * n⟩]

/-- The results: `f R w` of each block of `m₀`'s data. -/
def ecbOut (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr) (R : Nat)
    (w : List Byte) (j : Nat) : Spec.Aes.State :=
  f R w (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)))

/-- Before group `g`. -/
structure EInv (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b D : Addr) (n R : Nat) (w : List Byte) (g : Nat) (s : State) : Prop where
  hg : 4 * g < n
  a3 : s.gpr .a3 = D + BitVec.ofNat 64 (64 * g)
  a4 : s.gpr .a4 = BitVec.ofNat 64 (n - 4 * g)
  base : s.gpr sb = b
  a0 : s.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R)
  ra : s.gpr .ra = s₂.gpr .ra
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (eRegions b D n) s₂.mem s.mem
  data : EcbInv m₀ s.mem D n (4 * g) (ecbOut f m₀ D R w)

/-- After the last group. -/
structure EDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b D : Addr) (n R : Nat) (w : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  ra : s.gpr .ra = s₂.gpr .ra
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (eRegions b D n) s₂.mem s.mem
  data : EcbInv m₀ s.mem D n n (ecbOut f m₀ D R w)

theorem ESetup.d320 {s₂ : State} {X b D : Addr} {n R : Nat} {w : List Byte}
    (hs : ESetup s₂ X b D n R w) : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 320⟩ := by
  refine hs.sep.sub_right ?_
  rw [← hs.base, hs.scr.base]
  exact Offset.sub_base X (by have := Align.pad_lt X; omega)

theorem ESetup.keys_disj {s₂ : State} {X b D : Addr} {n R : Nat} {w : List Byte}
    (hs : ESetup s₂ X b D n R w) : ∀ r ∈ eRegions b D n, Region.Disjoint ⟨b + 1024, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact keys_disjoint b
  · refine (hs.sep.sub_right ?_).symm
    rw [← hs.base]
    exact hs.scr.sub (d := 1024) (n := 960) (by omega)

theorem ESetup.masks_disj {s₂ : State} {X b D : Addr} {n R : Nat} {w : List Byte}
    (hs : ESetup s₂ X b D n R w) : ∀ r ∈ eRegions b D n,
      Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧
      Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨Offset.disjoint_base b (by omega) (by omega), Offset.disjoint_base b (by omega) (by omega)⟩
  · rw [← hs.base]
    exact ⟨(hs.sep.sub_right (hs.scr.sub (by omega))).symm,
      (hs.sep.sub_right (hs.scr.sub (by omega))).symm⟩

section Group

variable {crypt4 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
  {m₀ : Mem} {s₂ : State} {X b D : Addr} {n R : Nat} {w : List Byte}

/-- One group: from before group `g`, to after the last group (`a4 = 0`) or
before group `g + 1`. -/
theorem ecbGroup_ok (hcr : CryptOk crypt4 f) (hs : ESetup s₂ X b D n R w) {g : Nat} {s : State}
    (hi : EInv f m₀ s₂ b D n R w g s) :
    WP isa (blockGroup crypt4) s fun s' =>
      (isa.eval (.nonzero .a4) s' = some false ∧ EDone f m₀ s₂ b D n R w s') ∨
      (isa.eval (.nonzero .a4) s' = some true ∧ EInv f m₀ s₂ b D n R w (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hn := hs.hn
  have hg := hi.hg
  unfold blockGroup
  have lp : LPre m₀ D n g (ecbOut f m₀ D R w) s :=
    ⟨hg, hn, hi.wr ▸ hs.dat, hi.a3, hi.a4, hi.data⟩
  refine shr2_wp (k := n - 4 * g) (by omega_arith) hi.a4 fun s₁ u₁ ev₁ => ?_
  refine WP.seq (WP.mono (loadIte_wp lp ev₁
    (ls_zero (fun r h => u₁.other r h) u₁.mem u₁.rd u₁.wr u₁.sp)) fun s₃ l => ?_)
  have hb₃ : s₃.gpr sb = b := (l.keep sb (by decide)).trans hi.base
  have hp : EncPre s₃ X R w :=
    ⟨hs.scr.congr (by rw [l.wr, hi.wr]) (by rw [hb₃, hs.base]),
      by rw [hb₃, l.mem]; exact masks_frame hi.frame hs.masks_disj hs.masks, hs.rounds,
      by rw [l.keep .a0 (by decide), hi.a0, hb₃],
      by rw [l.keep .a0 (by decide), hi.a0, l.mem]; exact keysAt_frame hR hi.frame hs.keys_disj hs.keys⟩
  refine WP.seq (WP.mono (hcr hp (inRel_regBlock (Q s₃))) fun s₄ ⟨hc₄, hin₄⟩ => ?_)
  have fr₄ := hc₄.frame
  rw [hb₃] at fr₄
  have sp : SPre m₀ D n g (ecbOut f m₀ D R w) s₄ :=
    { hg := hg, hn := hn, dat := by rw [hc₄.wr, l.wr, hi.wr]; exact hs.dat
      a3 := by rw [hc₄.keep .a3 (by decide) (by decide), l.keep .a3 (by decide), hi.a3]
      a4 := by rw [hc₄.keep .a4 (by decide) (by decide), l.keep .a4 (by decide), hi.a4]
      data := ecbInv_frame fr₄ (by simpa using hs.d320) hn (by rw [l.mem]; exact hi.data)
      out := fun c hc hcn t ht => by
        rw [byte_of_inRel hin₄ hc ht]
        simp only [ecbOut]
        rw [l.blk c (by omega_arith)] }
  refine WP.mono (storePhase_wp sp) fun s' ⟨f', o', rd', wr', sp', hz⟩ => ?_
  have keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s'.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => (o' r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) h3 h4).trans
      ((hc₄.keep r h1 h2).trans (l.keep r h1))
  have base' : s'.gpr sb = b := (keep sb (by decide) (by decide) (by decide) (by decide)).trans hi.base
  have ra' : s'.gpr .ra = s₂.gpr .ra :=
    (keep .ra (by decide) (by decide) (by decide) (by decide)).trans hi.ra
  have rd'' : s'.rd = s₂.rd := by rw [rd', hc₄.rd, l.rd, hi.rd]
  have wr'' : s'.wr = s₂.wr := by rw [wr', hc₄.wr, l.wr, hi.wr]
  have sp'' : s'.sp = s₂.sp := by rw [sp', hc₄.sp, l.sp, hi.sp]
  have frame' : Frame (eRegions b D n) s₂.mem s'.mem :=
    hi.frame.trans (by
      rw [← l.mem]
      exact (fr₄.mono fun r hr => by simp at hr; simp [hr]).trans
        (f'.mono fun r hr => by simp at hr; simp [hr]))
  rcases hz with ⟨z, d⟩ | ⟨h4, d, r6', r7'⟩
  · exact .inl ⟨by rw [eval_nonzero, z]; rfl, base', ra', rd'', wr'', sp'', frame', d⟩
  · refine .inr ⟨by rw [Steps.eval_nonzero_ofNat s' .a4 (by omega_arith) r7']; simp; omega_arith,
      ⟨by omega_arith, r6', r7', base', ?_, ra', rd'', wr'', sp'', frame', d⟩⟩
    rw [keep .a0 (by decide) (by decide) (by decide) (by decide), hi.a0]

/-- The loop over the groups. -/
theorem ecbGroups_ok (hcr : CryptOk crypt4 f) (hs : ESetup s₂ X b D n R w) {s : State}
    (hi : EInv f m₀ s₂ b D n R w 0 s) :
    WP isa (.loop (blockGroup crypt4) (.nonzero .a4)) s (EDone f m₀ s₂ b D n R w) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 4 * g ∧ EInv f m₀ s₂ b D n R w g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (ecbGroup_ok hcr hs hg) fun s' h => ?_) n s ⟨0, by omega_arith, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 4 * (g + 1), by have := hg.hg; omega_arith, g + 1, rfl, d⟩

end Group

end VG.Proof.Aes.RISCV64
