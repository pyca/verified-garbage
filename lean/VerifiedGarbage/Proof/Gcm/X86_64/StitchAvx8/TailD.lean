module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Tail
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOneD
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# The blocks after the last batch of decryption

`finalDec_ok`: after the loop, the last batch decrypts and hashes the eight
blocks from `g`, leaving `t = nb - g - 8 < 8` blocks (`TailReadyD`);
`tailD_ok`: `StitchAvx8.tailD` and `finish` then meet `DPost` (`tailNone_ok`:
`finish` alone, when there are none). The tail is
`tail_ok`'s (`Tail.lean`), once `r9` and `rdx` are moved to where encryption
leaves them: `ksTail` encrypts the eight counters the last batch prepared,
`tailSetup` advances the counter by `t` and points `rax` at the powers
`H'ᵗ` … `H'`, and the loop (`StitchZH.remLoopD1_ok`) decrypts the `t` blocks in place
and adds the products of the blocks as they were with their powers, which
`tailEnd` reduces into `Y` (`TailLaw`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (batch q8 ksTail tailSetup tailEnd tailD finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Spec.Gcm (Block inc32 blockAt ghashFrom)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (prod reduceB)
open VG.Proof.Gcm.X86_64.StitchZH (REnv RInvD accR accR_congr remLoopD1_ok)

/-- After the last batch of decryption: the blocks before `g + 8` decrypted
and hashed, the counters of the next eight prepared, and `nb - g - 8 < 8`
blocks left. -/
structure TailReadyD (s₀ : State) (P : Nat → Block) (g : Nat) (s : State) : Prop where
  env : Env s₀ P s
  data : DataInv s₀ false (g + 8) s.mem
  templates : Templates s₀ (g + 8) 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (g + 8 + 8)
  cursor : s.gpr .rdx = bAddr s₀ g
  remaining : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g)
  hash : s.lane .xmm2 0 = hashPrefix s₀ true (g + 8)
  le : g + 8 ≤ nb s₀
  lt : nb s₀ - g < 16

theorem finalDec_ok {s₀ s : State} {P : Nat → Block} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ false P true g s) (hn : nb s₀ - g < 16) :
    WP isa (batch (nr s₀) 8 0 (q8 (nr s₀))) s (TailReadyD s₀ P g) := by
  have hc : CoreInv s₀ false P true g g s := h.core
  have hle : g + 8 ≤ nb s₀ := h.tail_le
  refine WP.mono (hc.hashBatch hp (SrcOk.inplace hp) (by simp [lead]) hle (fun _ => rfl)) fun t ht => ?_
  have hd := hc.data.batch hp (SrcOk.inplace hp) hle (by simpa only [lead, Bool.true_eq, ite_true,
    Nat.mul_zero, BitVec.add_zero] using hc.cursor) hc.rbx ht
  refine ⟨ht.env, hd, ht.templates, ?_, ?_, ?_, ?_, hle, hn⟩
  · rw [ht.counter]
  · rw [ht.regs _ (by decide) (by decide)]; exact hc.cursor
  · rw [ht.regs _ (by decide) (by decide)]; exact hc.remaining
  · rw [ht.hash, hlaw]
    change ghashFrom (hk s₀) (hashPrefix s₀ true g) ((List.range 8).map (window s₀ true g)) = _
    exact (ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ true) g).symm

/-- With no blocks left, `finish` meets `DPost`. -/
theorem tailNone_ok {s₀ s : State} {P : Nat → Block} {g : Nat} (hp : SPre s₀) (h : TailReadyD s₀ P g s)
    (hn : nb s₀ = g + 8) : WP isa (.block finish) s (DPost s₀) :=
  WP.mono (finish_complete (ix := false) hp true h.env (by rw [hn]; exact h.data) (by rw [h.counter, hn])
    (by rw [h.hash, hn])) fun _ hu => hu.1

/-- `add r9, 8`, `sub rdx, 128`, `cmp r9, 16`: the tail's registers where
encryption's has them, and whether there are blocks left. -/
theorem tailHead_ok (s : State) {t : Nat} (ht : t < 8) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 + t)) :
    WP isa (.block [.alu .add .r9 (.imm 8), .alu .sub .rdx (.imm 128), .alu .cmp .r9 (.imm 16)]) s fun u =>
      u.gpr .r9 = BitVec.ofNat 64 (16 + t) ∧ u.gpr .rdx = s.gpr .rdx - 128 ∧
      u.zf = some (decide (t = 0)) ∧ (∀ q, q ≠ .r9 → q ≠ .rdx → u.gpr q = s.gpr q) ∧
      (∀ r l, u.lane r l = s.lane r l) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have a9 : BitVec.ofNat 64 (8 + t) + 8 = BitVec.ofNat 64 (16 + t) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]; congr 1; omega
  have hz : (BitVec.ofNat 64 (16 + t) - 16 == 0) = decide (t = 0) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    simp only [decide_eq_decide]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    isa, State.setReg, e8, e16, e128, h9, a9, hz, reduceCtorEq, ↓reduceIte,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun q h1 h2 => by simp only [h1, h2, ite_false], fun _ _ => rfl,
    trivial, trivial, trivial⟩

theorem tailD_ok {s₀ s : State} {P : Nat → Block} {g : Nat} (hp : SPre s₀)
    (hlaw : TailLaw s₀ P) (h : TailReadyD s₀ P g s) :
    WP isa (.seq (tailD (nr s₀)) (.block finish)) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have hn64 : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hle := h.le
  have hlt := h.lt
  obtain ⟨t, ht⟩ : ∃ t, t = nb s₀ - (g + 8) := ⟨_, rfl⟩
  have ht8 : t < 8 := by omega
  have hnb : nb s₀ = g + 8 + t := by omega
  have h9 : s.gpr .r9 = BitVec.ofNat 64 (8 + t) := by rw [h.remaining]; congr 1; omega
  rw [tailD]
  refine WP.seq (WP.seq (WP.mono (tailHead_ok s ht8 h9) fun s₁ ⟨r9₁, dx₁, z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_))
  have hR : Region.Sub ⟨bAddr s₀ (g + 8), 16 * t⟩ (dR s₀) := Offset.sub_base _ (by omega)
  have hE₁ : Env s₀ P s₁ := h.env.dataWrite hp hR (by rw [m₁]; exact Frame.refl _ _)
    (fun r _ h2 _ h4 => g₁ r h4 h2) rd₁ wr₁
  refine WP.ite (decide (t = 0)) z₁ (fun he => ?_) (fun he => ?_)
  · -- No blocks left.
    have t0 : t = 0 := by simpa using he
    subst t0
    refine WP.block_nil (WP.mono (finish_complete (ix := false) hp true hE₁ ?_ ?_ ?_) fun u hu => hu.1)
    · rw [m₁, hnb]; exact h.data
    · rw [g₁ _ (by decide) (by decide), hnb]; exact h.counter
    · rw [l₁, h.hash, hnb]
  -- `t` blocks left.
  have t1 : 1 ≤ t := by
    have : t ≠ 0 := by simpa using he
    omega
  refine WP.seq (WP.mono (ksTail_ok hp hE₁ (m₁ ▸ h.templates))
    fun s₂ ⟨hE₂, hks, hF₂, hg₂, hy₂, hrd₂, hwr₂⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tailSetup_ok s₂ ht8 (by rw [hg₂]; exact r9₁)
    (by rw [hE₂.rd, hE₂.wr, hE₂.r11]; exact in_rdwr (in_sub hp.p_in (by decide)))
    (by rw [hE₂.rd, hE₂.wr, hE₂.r11]; exact in_rdwr (in_sub hp.p_in (by decide))))
    fun s₃ ⟨a10, aax, adx, a11, a8, ag, a0, a1, al, am, ard, awr⟩ => ?_
  have hA : bAddr s₀ g - 128 + 256 = bAddr s₀ (g + 8) := by
    rw [← bAddr_add s₀ g 8, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have rdx₃ : s₃.gpr .rdx = bAddr s₀ (g + 8) := by rw [adx, hg₂, dx₁, h.cursor, hA]
  refine WP.mono (StitchAvx.zero_ok s₃) fun s₄ ⟨p₄, f₄⟩ => ?_
  let E : REnv := ⟨t, .rdx, bAddr s₀ (g + 8), bAddr s₀ (g + 8), pp s₀ + BitVec.ofNat 64 64,
    pp s₀ + BitVec.ofNat 64 (256 - 16 * t), s₄.mem, s₄.gpr, s₄.rd, s₄.wr, s₄.lane .xmm2 0⟩
  have rd₄ : s₄.rd = s₀.rd := by rw [f₄.rd, ard, hE₂.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, awr, hE₂.wr]
  have m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, am]
  have rdx₄ : s₄.gpr .rdx = bAddr s₀ (g + 8) := by rw [f₄.gpr, rdx₃]
  have hEok : E.Ok :=
    { r1 := t1, r15 := show t ≤ 15 by omega, gS := rdx₄, gA := rdx₄
      gP := by show s₄.gpr .r11 = _; rw [f₄.gpr, a11, hE₂.r11]; rfl
      gW := by show s₄.gpr .rax = _; rw [f₄.gpr, aax, hE₂.r11]
      src9 := show Reg.rdx ≠ .r9 by decide
      src10 := show Reg.rdx ≠ .r10 by decide
      inS := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (bAddr s₀ (g + 8) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, bAddr_add]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inK := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega))
      inD := fun j (hj : j < t) => by
        show InRegions s₄.wr (bAddr s₀ (g + 8) + BitVec.ofNat 64 (16 * j)) 16
        rw [wr₄, bAddr_add]
        exact in_sub hp.d_in (by omega)
      inW := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega))
      dS := fun j (hj : j < t) i hi => by
        show Region.Disjoint ⟨bAddr s₀ (g + 8) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (g + 8), 16 * i⟩
        rw [bAddr_add]
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      dK := fun j (hj : j < t) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ (g + 8), 16 * t⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
      dW := fun j (hj : j < t) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ (g + 8), 16 * t⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)) }
  have hI₄ : RInvD E 0 s₄ :=
    { le := Nat.zero_le _
      r10 := by rw [f₄.gpr]; exact a10
      r9 := by
        show s₄.gpr .r9 = _
        rw [f₄.gpr, ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hg₂, r9₁, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := p₄
      y := by simp only [↓reduceIte]; rfl
      m0 := by
        rw [f₄.lane _ (by decide) 0 (by decide), a0, hE₂.r11]
        exact hE₂.mask
      m1 := by
        rw [f₄.lane _ (by decide) 0 (by decide), a1, hE₂.r11]
        exact hE₂.poly }
  refine WP.seq (WP.mono (remLoopD1_ok hEok hI₄) fun s₅ hI₅ => ?_)
  refine WP.mono (tailEnd_ok s₅ hp.rounds hI₅.m1) fun s₆ ⟨y₆, r11₆, r10₆, g₆, m₆, rd₆, wr₆⟩ => ?_
  -- What the tail leaves.
  have g₆₄ : ∀ q, q ≠ .r11 → q ≠ .r10 → q ≠ .r9 → s₆.gpr q = s₄.gpr q := fun q h11 h10 h9' => by
    rw [g₆ q h11 h10, hI₅.gpr q h9' h10]
  have hF : Frame [⟨bAddr s₀ (g + 8), 16 * t⟩] s₂.mem s₆.mem := by
    rw [m₆, ← m₄]; exact hI₅.frame
  have hE₆ : Env s₀ P s₆ := hE₂.dataWrite hp hR hF (fun q h1 h2 h3 h4 => by
      by_cases h11 : q = .r11
      · subst h11
        rw [r11₆, hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .r11 - 64 = _
        rw [f₄.gpr, a11, BitVec.add_sub_cancel]
      by_cases h10 : q = .r10
      · subst h10
        rw [r10₆, hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .rdi + _ = _
        rw [f₄.gpr, ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hE₂.rdi, hE₂.r10]
      · rw [g₆₄ q h11 h10 h4, f₄.gpr, ag q h10 h1 h2 h11 h3])
    (by rw [rd₆, hI₅.rd]; exact f₄.rd.trans ard)
    (by rw [wr₆, hI₅.wr]; exact f₄.wr.trans awr)
  have hD₂ : DataInv s₀ false (g + 8) s₂.mem := (m₁ ▸ h.data).frameP hp (SrcOk.inplace hp) hF₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.sub_base (pp s₀) (d := 832) (n := 128) (k := 1024) (by decide))
  have hB : ∀ j < t, E.H j = blk s₀ (g + 8 + j) := fun j hj => by
    show blockAt s₄.mem (bAddr s₀ (g + 8) + BitVec.ofNat 64 (16 * j)) = _
    rw [m₄, bAddr_add, ← srcBlk_false, (hD₂ _ (by omega)).2 (by omega)]
  have hX : ∀ j < t, E.X j = ctb s₀ (g + 8 + j) := fun j hj => by
    show blockAt s₄.mem (bAddr s₀ (g + 8) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₄.mem (pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [show blockAt s₄.mem (bAddr s₀ (g + 8) + BitVec.ofNat 64 (16 * j)) = E.H j from rfl, hB j hj, m₄,
      Offset.add_add, show 64 + (768 + 16 * j) = 832 + 16 * j by omega, hks j (by omega)]
  have hT : ∀ j < t, E.T j = P (8 - t + j) := fun j hj => by
    show s₄.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j)) 128 = _
    rw [m₄, Offset.add_add, show 256 - 16 * t + 16 * j = 128 + 16 * (8 - t + j) by omega]
    exact hE₂.powers _ (by omega)
  refine WP.mono (finish_complete (ix := false) hp true hE₆
    (fun k hk => ⟨fun hk' => ?_, fun hk' => absurd hk (by omega)⟩) ?_ ?_) fun u hu => hu.1
  · by_cases hkg : k < g + 8
    · rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hF (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint (dp s₀) (.inl (by omega)) (by omega) (by omega)),
        (hD₂ k (by omega)).1 hkg]
    · obtain ⟨j, rfl⟩ : ∃ j, k = g + 8 + j := ⟨k - (g + 8), by omega⟩
      have ct := hI₅.ct j (show j < t by omega)
      rw [show E.aD j = bAddr s₀ (g + 8 + j) from bAddr_add s₀ (g + 8) j, ← m₆] at ct
      rw [ct, hX j (by omega)]
  · rw [g₆₄ _ (by decide) (by decide) (by decide), f₄.gpr, a8, hg₂, g₁ _ (by decide) (by decide), h.counter,
      hnb, BitVec.add_assoc, BitVec.ofNat_add_ofNat, show g + 8 + 8 + t = g + 8 + t + 8 by omega]
  · rw [y₆, hI₅.prod, accR_congr _ t hB hT, hlaw t t1 (by omega)]
    have hy : E.y = hashPrefix s₀ true (g + 8) := by
      show s₄.lane .xmm2 0 = _
      rw [f₄.lane _ (by decide) 0 (by decide), al _ (by decide) (by decide), hy₂, l₁, h.hash]
    rw [hy, hnb]
    simp only [hashPrefix, List.range_add, List.map_append, List.map_map, ghashFrom, List.foldl_append]
    rfl

end VG.Proof.Gcm.X86_64.StitchAvx8
