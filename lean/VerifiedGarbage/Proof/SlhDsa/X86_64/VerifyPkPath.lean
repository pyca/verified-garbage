module

-- separate module: one height of the path and the frames, which `forsPk`'s proofs use too

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkCall
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Contracts
public import VerifiedGarbage.Proof.SlhDsa.VerifySpec
public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
public import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Verify
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA on x86-64, `xmssPk`: one height of the path

`pathBody` (`Impl/SlhDsa/X86_64/Verify.lean`) at height `z` (variable 3 of
frame 1): the bit `z` of `idx` (`r12`) and the authentication path's node
`z` (at `sig + len·n + z·n`, `r13` = `sig`), the node of lane 0 of `A`
first or second as the bit says (`order_ok`), the lane's address for height
`z + 1` (`adrs_ok`), one `H` (`thash4`), and `z + 1`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_store)
open VG.Impl.SlhDsa.X86_64 (Layout copyWords setField setFieldR)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.SlhDsa
open VG.Proof.SlhDsa.X86_64.Levels (wp_shrcl wp_add mulN_ok sx_ofNat in_scr in_scr')

/-- `and d, imm32`, with ZF. -/
theorem wp_andi_zf {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → s'.zf = some ((s.gpr d &&& v.signExtend 64) == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem sx1' : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

/-- A shift right of a value below `2⁶⁴`, by a count below 64. -/
theorem shr_nat (x z : Nat) (hx : x < 2 ^ 64) (hz : z < 64) :
    (BitVec.ofNat 64 x >>> ((BitVec.ofNat 64 z).toNat % 64) : BitVec 64) = BitVec.ofNat 64 (x / 2 ^ z) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show z < 2 ^ 64 by omega), Nat.mod_eq_of_lt hz,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

/-- The low bit of a value. -/
theorem and1_nat (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x &&& 1 : BitVec 64) = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt x (by decide)) (by decide))]

theorem beq_bit (x : Nat) : (BitVec.ofNat 64 (x % 2) == 0) = decide (x % 2 = 0) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> decide

/-- Two strings of `n` bytes, at `S + L` and `S + L + n`. -/
theorem bytesAt_two {m : Mem} {S : Addr} {L n : Nat} {A B : List Byte} (hA : A.length = n) (hB : B.length = n)
    (h₁ : ∀ i < n, m (S + BitVec.ofNat 64 (L + i)) = A.getD i 0)
    (h₂ : ∀ i < n, m (S + BitVec.ofNat 64 (L + n + i)) = B.getD i 0) :
    bytesAt m (at' S L) (2 * n) = A ++ B := by
  refine bytesAt_eq_of (by simp [hA, hB]; omega) fun i hi => ?_
  rw [ofNat_add']
  simp only [List.getD_eq_getElem?_getD]
  by_cases c : i < n
  · rw [List.getElem?_append_left (by rw [hA]; exact c), ← List.getD_eq_getElem?_getD, h₁ i c]
  · rw [List.getElem?_append_right (by rw [hA]; omega), hA, ← List.getD_eq_getElem?_getD,
      show L + i = L + n + (i - n) by omega, h₂ _ (by omega)]

/-- A byte of `scratch` outside a frame of one region of it. -/
theorem frame_byte {m m' : Mem} {S : Addr} {o l q : Nat} (f : Frame [⟨S + BitVec.ofNat 64 o, l⟩] m m')
    (h : q + 1 ≤ o ∨ o + l ≤ q) (hq : q + 1 ≤ 2 ^ 64) (ho : o + l ≤ 2 ^ 64) :
    m' (S + BitVec.ofNat 64 q) = m (S + BitVec.ofNat 64 q) := by
  have e := f.bytes (R := ⟨S + BitVec.ofNat 64 q, 1⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint S h hq ho) (show 1 ≤ 2 ^ 64 by decide) (i := 0) (show 0 < 1 by decide)
  simpa using e

/-- A byte outside a frame of a region it is apart from. -/
theorem frame_byte' {m m' : Mem} {a x : Addr} {l : Nat} (f : Frame [⟨a, l⟩] m m')
    (hd : Region.Disjoint ⟨x, 1⟩ ⟨a, l⟩) : m' x = m x := by
  have e := f.bytes (R := ⟨x, 1⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)
    (show 1 ≤ 2 ^ 64 by decide) (i := 0) (show 0 < 1 by decide)
  simpa using e

/-- The offsets in `scratch`: lane 0 of `A`, its address and its message,
and variable 3 of frame 1. -/
theorem laneA0 : Layout.laneA 0 = 3296 := rfl
theorem oVar13 : Layout.oVar 1 3 = 2600 := rfl

/-- The first block of `pathBody` and its choice: with `rbx = S`,
`r12 = idx`, `r13 = sig` and height `z` in variable 3, the `2n` bytes of
lane 0 of `A`'s message become the node (its first `n`) and the
authentication path's node `z`, in the order bit `z` of `idx` says. -/
theorem order_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hlen : p.len * p.n < 2 ^ 31)
    {s : State} {S sig : Addr} {idx z : Nat} (hidx : idx < 2 ^ 32) (hz : z < 64)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx) (h13 : s.gpr .r13 = sig)
    (hv3 : s.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr)
    (hsig : ∀ j < p.n / 8, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 (p.len * p.n + z * p.n) + BitVec.ofNat 64 (8 * j)) 8)
    (hdis : Region.Disjoint ⟨sig + BitVec.ofNat 64 (p.len * p.n + z * p.n), p.n⟩ ⟨S, 2 ^ 16⟩)
    {Q : State → Prop}
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneA 0 + p.n + 32)) (2 * p.n) =
        (if idx / 2 ^ z % 2 = 0 then
          bytesAt s.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n ++
            bytesAt s.mem (sig + BitVec.ofNat 64 (p.len * p.n + z * p.n)) p.n
        else bytesAt s.mem (sig + BitVec.ofNat 64 (p.len * p.n + z * p.n)) p.n ++
            bytesAt s.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n) →
      Frame [⟨at' S (Layout.laneA 0 + p.n + 32), 2 * p.n⟩] s.mem s'.mem → Q s') :
    WP isa (.seq (.block (([.mov .rcx (.mem (Impl.SlhDsa.X86_64.Verify.xv 3)), .mov .rax (.reg .r12), .shiftCl .shr .rax,
        .mov .rsi (.reg .rcx)] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN p.n .rsi .rdx ++
        ([.alu .add .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (p.len * p.n))), .alu .and .rax (.imm 1)] : List Instr)))
      (.ite .e
        (.block (copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n) .rsi 0 (p.n / 8)))
        (.block (copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n) .rbx
            (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8) ++
          copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8))))) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  rw [hmsg]
  have ha0 := laneA0
  have hv := oVar13
  -- the authentication path's node and its address
  obtain ⟨au, hau⟩ : ∃ au, au = sig + BitVec.ofNat 64 (p.len * p.n + z * p.n) := ⟨_, rfl⟩
  rw [← hau] at hsig hdis k
  refine WP.seq ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_movm (a := at' S (Layout.oVar 1 3)) (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hbx])
    (by rw [hv]; exact in_scr' hw (by omega)) fun s₁ u₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_shrcl fun s₃ u₃ => wp_mov fun s₄ u₄ => ?_
  refine Levels.mulN_ok hn (by decide) fun s₅ g₅ o₅ m₅ r₅ w₅ => ?_
  refine wp_add fun s₆ u₆ => wp_addi fun s₇ u₇ => wp_andi_zf fun s₈ u₈ z₈ => WP.block_nil ?_
  have hrsi : s₈.gpr .rsi = au := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, g₅, u₄.gpr, o₅ _ (by decide) (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hv3, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h13, sx_ofNat hlen, hau, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_mul,
      BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 z * _), BitVec.add_assoc]
  have hrax : s₈.gpr .rax = BitVec.ofNat 64 (idx / 2 ^ z % 2) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), o₅ _ (by decide) (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, hv3, u₁.other _ (by decide), h12, shr_nat _ _ (by omega) hz, sx1',
      and1_nat _ (by have := Nat.div_le_self idx (2 ^ z); omega)]
  have hzf : s₈.zf = some (decide (idx / 2 ^ z % 2 = 0)) := by
    rw [z₈, ← u₈.gpr, hrax, beq_bit]
  have hbx₈ : s₈.gpr .rbx = S := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), o₅ _ (by decide) (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx]
  have hm₈ : s₈.mem = s.mem := by rw [u₈.mem, u₇.mem, u₆.mem, m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, r₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, w₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hg₈ : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → s₈.gpr g = s.gpr g := fun g h₁ h₂ h₃ h₄ => by
    rw [u₈.other _ h₁, u₇.other _ h₄, u₆.other _ h₄, o₅ _ h₄ h₃, u₄.other _ h₄, u₃.other _ h₁, u₂.other _ h₁,
      u₁.other _ h₂]
  -- the lane's message, and the regions
  have hdst : ∀ (o : Nat), o + p.n ≤ 2 ^ 16 → ∀ j < p.n / 8, InRegions s₈.wr (s₈.gpr .rbx + BitVec.ofNat 64 (o + 8 * j)) 8 :=
    fun o ho j hj => by rw [hwr₈, hbx₈]; exact in_scr hw (by omega)
  have hlm : Layout.laneA 0 + p.n + 32 + 2 * p.n ≤ 2 ^ 16 := by rw [ha0]; omega
  have hAm : ∀ i < p.n, InRegions (s.rd ++ s.wr) (at' S (Layout.laneA 0 + p.n + 32) + BitVec.ofNat 64 i) 1 :=
    fun i hi => by rw [ofNat_add']; exact in_scr' hw (by omega)
  have hsep' : ∀ q, q + p.n ≤ 2 ^ 16 → Region.Disjoint ⟨S + BitVec.ofNat 64 q, p.n⟩ ⟨au, p.n⟩ := fun q hq =>
    (hdis.sub_right (Offset.sub_base S hq)).symm
  -- `L` is the message's offset in the lane
  obtain ⟨L, hL⟩ : ∃ L, L = Layout.laneA 0 + p.n + 32 := ⟨_, rfl⟩
  have eL1 : Layout.laneA 0 + (p.n + 32) = L := by omega
  have eL2 : Layout.laneA 0 + (p.n + 32) + p.n = L + p.n := by omega
  rw [eL1]
  rw [← hL] at hlm hAm k
  have hLn : L + 2 * p.n ≤ 2 ^ 16 := by omega
  have hsep'' : ∀ i < p.n, Region.Disjoint ⟨au + BitVec.ofNat 64 i, 1⟩ ⟨S + BitVec.ofNat 64 (L + p.n), p.n⟩ :=
    fun i hi => (hdis.sub_left (Offset.sub_base au (by omega))).sub_right (Offset.sub_base S (by omega))
  have hdst' : ∀ o, o + p.n ≤ 2 ^ 16 → ∀ j < p.n / 8, InRegions s₈.wr (s₈.gpr .rbx + BitVec.ofNat 64 (o + 8 * j)) 8 := hdst
  have hfr : ∀ (o : Nat), o + p.n ≤ L + 2 * p.n → L ≤ o →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 o, p.n⟩ : Region)], ∃ r' ∈ [(⟨at' S L, 2 * p.n⟩ : Region)], Region.Sub r r' :=
    fun o h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S h₂ (by omega)⟩
  refine WP.ite (decide (idx / 2 ^ z % 2 = 0)) (by show s₈.zf = _; exact hzf) (fun hb => ?_) (fun hb => ?_)
  · -- bit 0: the node stays, the path's node after it
    have hb' : idx / 2 ^ z % 2 = 0 := of_decide_eq_true hb
    refine WP.mono (copyWords_ok (d₁ := 0) (by decide) (by decide) (hdst' _ (by omega))
      (fun j hj => by rw [hrsi, hrd₈, hwr₈, Nat.zero_add]; exact hsig j hj)
      (by rw [hbx₈, hrsi, BitVec.add_zero, e8]; exact hsep' (L + p.n) (by omega))
      (by omega) (by omega)) fun s' c => ?_
    rw [hbx₈, hrsi, BitVec.add_zero, e8] at c
    refine k s' (fun g h₁ h₂ h₃ h₄ => by rw [c.gpr _ h₁, hg₈ g h₁ h₂ h₃ h₄]) (by rw [c.rd, hrd₈]) (by rw [c.wr, hwr₈])
      ?_ (by rw [← hm₈]; exact c.frame.sub (hfr _ (by omega) (by omega)))
    simp only [hb', ↓reduceIte]
    refine bytesAt_two (by simp [bytesAt_length']) (by simp [bytesAt_length']) (fun i hi => ?_) (fun i hi => ?_)
    · rw [frame_byte c.frame (by omega) (by omega) (by omega), hm₈, bytesAt_getD _ _ hi, ofNat_add']
    · rw [← ofNat_add', c.bytes i hi, hm₈, bytesAt_getD _ _ hi]
  · -- bit 1: the node moves after, the path's node first
    have hb' : ¬ (idx / 2 ^ z % 2 = 0) := fun h => by simp [h] at hb
    refine WP.block_append (WP.mono (copyWords_ok (by decide) (by decide) (hdst' _ (by omega))
      (fun j hj => by rw [hrd₈, hwr₈, hbx₈]; exact in_scr' hw (by omega))
      (by rw [hbx₈, e8]; exact Offset.disjoint S (by omega) (by omega) (by omega))
      (by omega) (by omega)) fun s₉ c₉ => ?_)
    rw [hbx₈, e8] at c₉
    have hbx₉ : s₉.gpr .rbx = S := by rw [c₉.gpr _ (by decide), hbx₈]
    have hsi₉ : s₉.gpr .rsi = au := by rw [c₉.gpr _ (by decide), hrsi]
    refine WP.mono (copyWords_ok (d₁ := 0) (by decide) (by decide)
      (fun j hj => by rw [c₉.wr, hwr₈, hbx₉]; exact in_scr hw (by omega))
      (fun j hj => by rw [hsi₉, c₉.rd, c₉.wr, hrd₈, hwr₈, Nat.zero_add]; exact hsig j hj)
      (by rw [hbx₉, hsi₉, BitVec.add_zero, e8]; exact hsep' L (by omega))
      (by omega) (by omega)) fun s' c => ?_
    rw [hbx₉, hsi₉, BitVec.add_zero, e8] at c
    refine k s' (fun g h₁ h₂ h₃ h₄ => by rw [c.gpr _ h₁, c₉.gpr _ h₁, hg₈ g h₁ h₂ h₃ h₄])
      (by rw [c.rd, c₉.rd, hrd₈]) (by rw [c.wr, c₉.wr, hwr₈]) ?_ ?_
    · simp only [hb', ↓reduceIte]
      refine bytesAt_two (by simp [bytesAt_length']) (by simp [bytesAt_length']) (fun i hi => ?_) (fun i hi => ?_)
      · -- the path's node, which the first copy left as it was
        rw [← ofNat_add', c.bytes i hi, frame_byte' c₉.frame (hsep'' i hi), hm₈, bytesAt_getD _ _ hi]
      · rw [frame_byte c.frame (by omega) (by omega) (by omega), ← ofNat_add', c₉.bytes i hi, hm₈,
          bytesAt_getD _ _ hi, ofNat_add']
    · rw [← hm₈]
      exact (c₉.frame.sub (hfr _ (by omega) (by omega))).trans (c.frame.sub (hfr _ (by omega) (by omega)))


theorem bytesAt_split2 (m : Mem) (S : Addr) (a x y : Nat) :
    bytesAt m (S + BitVec.ofNat 64 a) (x + y) =
      bytesAt m (S + BitVec.ofNat 64 a) x ++ bytesAt m (S + BitVec.ofNat 64 (a + x)) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, ofNat_add', Nat.add_assoc]

theorem bytesAt_split4 (m : Mem) (S : Addr) (a : Nat) :
    bytesAt m (S + BitVec.ofNat 64 a) 16 = bytesAt m (S + BitVec.ofNat 64 a) 4 ++
      (bytesAt m (S + BitVec.ofNat 64 (a + 4)) 4 ++ (bytesAt m (S + BitVec.ofNat 64 (a + 8)) 4 ++
        bytesAt m (S + BitVec.ofNat 64 (a + 12)) 4)) := by
  rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, bytesAt_split2, bytesAt_split2, bytesAt_split2,
    Nat.add_assoc, Nat.add_assoc]

/-- A part of `scratch` that `changes` leaves: the table of `work`, and each
lane's `PK.seed` and `a16`. -/
theorem keep_disj {p : Params} (hn : p.n ≤ 32) (S : Addr) {o l : Nat}
    (hk : (1600 ≤ o ∧ o + l ≤ 2368) ∨ (∃ k < 4, (Layout.laneA k ≤ o ∧ o + l ≤ Layout.laneA k + p.n + 16) ∨
      (Layout.laneB k ≤ o ∧ o + l ≤ Layout.laneB k + p.n + 16))) :
    ∀ r ∈ changes p S, Region.Disjoint ⟨at' S o, l⟩ r := by
  -- the offsets, as numbers
  have e : ∀ c, (Layout.laneA c = 3296 + 128 * c) ∧ Layout.laneB c = 3808 + 2208 * c := fun c => ⟨rfl, rfl⟩
  obtain ⟨lo, hi, hlo, hhi, hgap⟩ : ∃ lo hi : Nat, lo ≤ o ∧ o + l ≤ hi ∧
      ((1600 ≤ lo ∧ hi ≤ 2368) ∨ (∃ k < 4, (lo = 3296 + 128 * k ∨ lo = 3808 + 2208 * k) ∧ hi = lo + p.n + 16)) := by
    rcases hk with ⟨h₁, h₂⟩ | ⟨k, hk4, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
    · exact ⟨1600, 2368, h₁, h₂, Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
    · rw [(e k).1] at h₁ h₂; exact ⟨_, _, h₁, h₂, Or.inr ⟨k, hk4, Or.inl rfl, rfl⟩⟩
    · rw [(e k).2] at h₁ h₂; exact ⟨_, _, h₁, h₂, Or.inr ⟨k, hk4, Or.inr rfl, rfl⟩⟩
  clear hk
  have hb : hi ≤ 12000 := by omega
  intro r hr
  simp only [changes, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hr
  have dj : ∀ c l', (hi ≤ c ∨ c + l' ≤ lo) → c + l' ≤ 2 ^ 16 → Region.Disjoint ⟨at' S o, l⟩ ⟨at' S c, l'⟩ :=
    fun c l' h h' => Offset.disjoint S (by omega) (by omega) (by omega)
  rcases hr with ((rfl | rfl | rfl) | ⟨k', hk', rfl | rfl⟩) | (rfl | rfl | rfl | rfl | rfl)
  · exact Offset.disjoint_base S (by omega) (by omega)
  · exact dj _ _ (by omega) (by omega)
  · exact dj _ _ (by simp only [Layout.oVars]; omega) (by simp only [Layout.oVars]; omega)
  · rw [(e k').1]; exact dj _ _ (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega)
  · rw [(e k').2]; exact dj _ _ (by simp only [Layout.strideB]; omega) (by simp only [Layout.strideB]; omega)
  all_goals
    have e₁ : Layout.oN = 12640 := rfl
    have e₂ : Layout.oRoots = 29280 := rfl
    have e₃ : Layout.oDigits = 30368 := rfl
    have e₄ : Layout.oMsg = 30496 := rfl
    have e₅ : Layout.oFidx = 31328 := rfl
    have e₆ : Layout.nodeSlots = 520 := rfl
    exact dj _ _ (Or.inl (by omega)) (by omega)

/-- `Env` across a frame of `changes` and a stack outside `scratch`. -/
theorem Env.of_frame {p : Params} (hn : p.n ≤ 32) {m m' : Mem} {S sp : Addr} {stack : Nat} {pkSeed a16 : List Byte}
    (he : Env p m S pkSeed a16) (hf : Frame (changes p S ++ [below sp stack]) m m')
    (hst : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) : Env p m' S pkSeed a16 := by
  have hd : ∀ {o l : Nat}, ((1600 ≤ o ∧ o + l ≤ 2368) ∨ (∃ k < 4, (Layout.laneA k ≤ o ∧ o + l ≤ Layout.laneA k + p.n + 16) ∨
      (Layout.laneB k ≤ o ∧ o + l ≤ Layout.laneB k + p.n + 16))) →
      ∀ r ∈ changes p S ++ [below sp stack], Region.Disjoint ⟨at' S o, l⟩ r := fun {o l} hk r hr => by
    have hb : o + l ≤ 2 ^ 16 := by
      simp only [Layout.laneA, Layout.laneB, Layout.oA, Layout.oB, Layout.strideA, Layout.strideB] at hk
      omega_using [hk, hn]
    rcases List.mem_append.mp hr with hr | hr
    · exact keep_disj hn S hk r hr
    · rw [List.mem_singleton] at hr; subst hr
      exact (hst.sub_right (Offset.sub_base S hb)).symm
  have hA : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 → bytesAt m' (at' S (Layout.laneA k + o)) l = bytesAt m (at' S (Layout.laneA k + o)) l :=
    fun k hk o l h => bytesAt_frame hf (hd (Or.inr ⟨k, hk, Or.inl ⟨by omega, by omega⟩⟩)) (by omega)
  have hB : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 → bytesAt m' (at' S (Layout.laneB k + o)) l = bytesAt m (at' S (Layout.laneB k + o)) l :=
    fun k hk o l h => bytesAt_frame hf (hd (Or.inr ⟨k, hk, Or.inr ⟨by omega, by omega⟩⟩)) (by omega)
  refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [← he.rc r hr k hk]
    exact hf.readW (r := ⟨at' S (1600 + 32 * r + 8 * k), 8⟩) (Region.contains_self _ _)
      (hd (Or.inl ⟨by omega, by omega⟩)) (by decide)
  · rw [← he.seedA k hk, ← Nat.add_zero (Layout.laneA k), hA k hk 0 p.n (by omega)]
  · rw [← he.seedB k hk, ← Nat.add_zero (Layout.laneB k), hB k hk 0 p.n (by omega)]
  · rw [← he.adrsA k hk, hA k hk p.n 16 (by omega)]
  · rw [← he.adrsB k hk, hB k hk p.n 16 (by omega)]

/-- The address block of `pathBody`: lane 0 of `A`'s fields become the type
`TREE`, the key pair 0, the height `z + 1` and the index `⌊idx / 2^(z+1)⌋`. -/
theorem adrs_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    {s : State} {S : Addr} {idx z : Nat} (hidx : idx < 2 ^ 32) (hz : z + 1 < 64)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx)
    (hv3 : s.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneA 0 + p.n + 16)) 16 =
        toByte 2 4 ++ toByte 0 4 ++ toByte (z + 1) 4 ++ toByte (idx / 2 ^ (z + 1)) 4 →
      Frame [⟨at' S (Layout.laneA 0 + p.n + 16), 16⟩] s.mem s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block ((setField .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 2 ++
        setField .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) 0 ++
        ([.mov .r10 (.mem (Impl.SlhDsa.X86_64.Verify.xv 3)), .alu .add .r10 (.imm 1)] : List Instr) ++
        setFieldR .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        ([.mov .rcx (.reg .r10), .mov .r11 (.reg .r12), .shiftCl .shr .r11] : List Instr) ++
        setFieldR .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11) ++ is)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hadr : (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff = p.n := rfl
  rw [hadr]
  have ha0 := laneA0
  have hv := oVar13
  rw [hv] at hv3
  obtain ⟨A, hA⟩ : ∃ A, A = Layout.laneA 0 + p.n := ⟨_, rfl⟩
  rw [← hA]
  rw [← hA] at k
  have hAb : A + 32 ≤ 2 ^ 16 := by omega
  have hin : ∀ (t : State) (o : Nat), t.gpr .rbx = S → t.wr = s.wr → o + 4 ≤ 2 ^ 16 →
      InRegions t.wr (t.gpr .rbx + BitVec.ofNat 64 o) 4 := fun t o h₁ h₂ ho => by
    rw [h₁, h₂]; exact in_scr hw ho
  have hdj : ∀ a c : Nat, a + 4 ≤ c ∨ c + 4 ≤ a → a + 4 ≤ 2 ^ 16 → c + 4 ≤ 2 ^ 16 →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 c, 4⟩ : Region)], Region.Disjoint ⟨S + BitVec.ofNat 64 a, 4⟩ r :=
    fun a c h h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S h (by omega) (by omega)
  have hv8 : ∀ c : Nat, A + 16 ≤ c → c + 4 ≤ A + 32 →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 c, 4⟩ : Region)], Region.Disjoint ⟨S + BitVec.ofNat 64 2600, 8⟩ r :=
    fun c h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have hsub : ∀ c : Nat, A + 16 ≤ c → c + 4 ≤ A + 32 →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 c, 4⟩ : Region)], ∃ r' ∈ [(⟨at' S (A + 16), 16⟩ : Region)], Region.Sub r r' :=
    fun c h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S h₁ (by omega)⟩
  have hc8 : (⟨S + BitVec.ofNat 64 2600, 8⟩ : Region).Contains (S + BitVec.ofNat 64 2600) (64 / 8) :=
    Offset.contains S (Nat.le_refl _) (Nat.le_refl _) (by decide)
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine setField_ok (by decide) (by decide) (hin s _ hbx rfl (by omega)) fun s₁ f₁ => ?_
  rw [hbx] at f₁
  have hb₁ : s₁.gpr .rbx = S := by rw [f₁.gpr _ (by decide), hbx]
  refine setField_ok (by decide) (by decide) (hin s₁ _ hb₁ f₁.wr (by omega)) fun s₂ f₂ => ?_
  rw [hb₁] at f₂
  have hm₂ : s₂.mem.readW (S + BitVec.ofNat 64 2600) 64 = BitVec.ofNat 64 z := by
    rw [f₂.frame.readW hc8 (hv8 _ (by omega) (by omega)) (by decide),
      f₁.frame.readW hc8 (hv8 _ (by omega) (by omega)) (by decide)]
    exact hv3
  refine wp_movm (a := S + BitVec.ofNat 64 2600)
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, f₂.gpr _ (by decide), hb₁, hv])
    (by rw [f₂.rd, f₂.wr, f₁.rd, f₁.wr]; exact in_scr' hw (by omega)) fun s₃ u₃ => ?_
  refine wp_addi fun s₄ u₄ => ?_
  have hr10 : s₄.gpr .r10 = BitVec.ofNat 64 (z + 1) := by
    rw [u₄.gpr, u₃.gpr, hm₂, sx1']; exact (BitVec.ofNat_add z 1).symm
  have hb₄ : s₄.gpr .rbx = S := by rw [u₄.other _ (by decide), u₃.other _ (by decide), f₂.gpr _ (by decide), hb₁]
  have hz1 : (BitVec.ofNat 64 (z + 1)).toNat = z + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine setFieldR_ok (by decide) (by rw [hr10, hz1]; omega)
    (hin s₄ _ hb₄ (by rw [u₄.wr, u₃.wr, f₂.wr, f₁.wr]) (by omega)) fun s₅ f₅ => ?_
  rw [hb₄, hr10, hz1] at f₅
  refine wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_shrcl fun s₈ u₈ => ?_
  have hq : idx / 2 ^ (z + 1) < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have hr11 : s₈.gpr .r11 = BitVec.ofNat 64 (idx / 2 ^ (z + 1)) := by
    rw [u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), f₅.gpr _ (by decide),
      f₅.gpr _ (by decide), hr10, u₄.other _ (by decide), u₃.other _ (by decide), f₂.gpr _ (by decide),
      f₁.gpr _ (by decide), h12, shr_nat _ _ (by omega) hz]
  have hb₈ : s₈.gpr .rbx = S := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), f₅.gpr _ (by decide), hb₄]
  have hq' : (BitVec.ofNat 64 (idx / 2 ^ (z + 1))).toNat = idx / 2 ^ (z + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hw₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, f₅.wr, u₄.wr, u₃.wr, f₂.wr, f₁.wr]
  refine setFieldR_ok (by decide) (by rw [hr11, hq']; omega) (hin s₈ _ hb₈ hw₈ (by omega)) fun s₉ f₉ => ?_
  rw [hb₈, hr11, hq'] at f₉
  have hm₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have hm₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
  refine k s₉ (fun g h₁ h₂ h₃ h₄ => ?_) (by rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, f₅.rd, u₄.rd, u₃.rd, f₂.rd, f₁.rd])
    (by rw [f₉.wr, hw₈]) ?_ ?_
  · rw [f₉.gpr _ h₁, u₈.other _ h₄, u₇.other _ h₄, u₆.other _ h₂, f₅.gpr _ h₁, u₄.other _ h₃, u₃.other _ h₃,
      f₂.gpr _ h₁, f₁.gpr _ h₁]
  · have e₃ : bytesAt s₉.mem (S + BitVec.ofNat 64 (A + 24)) 4 = toByte (z + 1) 4 := by
      rw [bytesAt_frame f₉.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), hm₈, f₅.bytes]
    have e₂ : bytesAt s₉.mem (S + BitVec.ofNat 64 (A + 20)) 4 = toByte 0 4 := by
      rw [bytesAt_frame f₉.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), hm₈,
        bytesAt_frame f₅.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), hm₄, f₂.bytes]
    have e₁ : bytesAt s₉.mem (S + BitVec.ofNat 64 (A + 16)) 4 = toByte 2 4 := by
      rw [bytesAt_frame f₉.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), hm₈,
        bytesAt_frame f₅.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), hm₄,
        bytesAt_frame f₂.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), f₁.bytes]
    simp only [List.append_assoc]
    rw [bytesAt_split4, show A + 16 + 4 = A + 20 by omega, show A + 16 + 8 = A + 24 by omega,
      show A + 16 + 12 = A + 28 by omega, f₉.bytes, e₁, e₂, e₃]
  · have F₅ : Frame [⟨S + BitVec.ofNat 64 (A + 24), 4⟩] s₂.mem s₅.mem := by rw [← hm₄]; exact f₅.frame
    have F₉ : Frame [⟨S + BitVec.ofNat 64 (A + 28), 4⟩] s₅.mem s₉.mem := by rw [← hm₈]; exact f₉.frame
    exact (f₁.frame.sub (hsub _ (by omega) (by omega))).trans ((f₂.frame.sub (hsub _ (by omega) (by omega))).trans
      ((F₅.sub (hsub _ (by omega) (by omega))).trans (F₉.sub (hsub _ (by omega) (by omega)))))

/-- `adrs_ok`, the block alone. -/
theorem adrs_ok' {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    {s : State} {S : Addr} {idx z : Nat} (hidx : idx < 2 ^ 32) (hz : z + 1 < 64)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx)
    (hv3 : s.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) {Q : State → Prop}
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneA 0 + p.n + 16)) 16 =
        toByte 2 4 ++ toByte 0 4 ++ toByte (z + 1) 4 ++ toByte (idx / 2 ^ (z + 1)) 4 →
      Frame [⟨at' S (Layout.laneA 0 + p.n + 16), 16⟩] s.mem s'.mem → Q s') :
    WP isa (.block (setField .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 2 ++
        setField .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) 0 ++
        ([.mov .r10 (.mem (Impl.SlhDsa.X86_64.Verify.xv 3)), .alu .add .r10 (.imm 1)] : List Instr) ++
        setFieldR .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        ([.mov .rcx (.reg .r10), .mov .r11 (.reg .r12), .shiftCl .shr .r11] : List Instr) ++
        setFieldR .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11)) s Q := by
  have h := adrs_ok (is := []) hn hidx hz hbx h12 hv3 hw fun s' a b c d e => WP.block_nil (k s' a b c d e)
  rwa [List.append_nil] at h

theorem cmp_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := fun e => h (by
      have e' : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
        rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 a) (BitVec.ofNat 64 b), e]; simp
      have := congrArg BitVec.toNat e'
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    rw [beq_false_of_ne hne]; simp [h]

/-- A sequence, reassociated. -/
theorem seq_assoc' {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a b) s (fun s' => WP isa c s' Q)) : WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨_, _, hx, _, _, hc, hq⟩ := h
  cases hx with
  | seq h1 h2 => exact ⟨_, _, .seq h1 (.seq h2 hc), hq⟩

/-- A part of `scratch` in `changes`: lane `k` of `A` after its `PK.seed`
and `a16`, `work` below its table, the slots after it, and the frames. -/
theorem sub_changes {p : Params} (hn : p.n ≤ 32) (S : Addr) (X : List Region) {o l : Nat}
    (h : (∃ k < 4, Layout.laneA k + p.n + 16 ≤ o ∧ o + l ≤ Layout.laneA k + 128) ∨ o + l ≤ 1600 ∨
      (2368 ≤ o ∧ o + l ≤ 2400) ∨ (2400 ≤ o ∧ o + l ≤ 3168)) :
    ∃ r' ∈ changes p S ++ X, Region.Sub ⟨at' S o, l⟩ r' := by
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  rcases h with ⟨k, hk, h₁, h₂⟩ | h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_cons_self ..⟩))), Offset.sub S h₁ ?_⟩
    simp only [Layout.strideA]; rw [eA] at h₂ ⊢; omega
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))),
      Offset.sub_base S h⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), Offset.sub S h₁ (by omega)⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
      Offset.sub S (by simp only [Layout.oVars]; omega) (by simp only [Layout.oVars]; omega)⟩

theorem below_changes {p : Params} (S sp : Addr) (stack : Nat) :
    ∃ r' ∈ changes p S ++ [below sp stack], Region.Sub (below sp stack) r' :=
  ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩

theorem oVar10' : Layout.oVar 1 0 = 2576 := rfl

/-- What the chains of a group change: `work` but its table, the frames, the
lanes `A` but their `PK.seed` and `a16`, and the stack below `sp`. -/
def chFrame (p : Params) (S sp : Addr) (stack : Nat) : List Region :=
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (Layout.oVar 1 0), 32⟩] ++
    (List.range 4).map (fun k => ⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩) ++ [below sp stack]

theorem chFrame_sub (p : Params) (S sp : Addr) (stack : Nat) :
    ∀ r ∈ chFrame p S sp stack, ∃ r' ∈ changes p S ++ [below sp stack], Region.Sub r r' := by
  intro r hr
  simp only [chFrame, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))),
      fun _ h => h⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), fun _ h => h⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
      Offset.sub S (by rw [oVar10']; simp only [Layout.oVars]; omega) (by rw [oVar10']; simp only [Layout.oVars]; omega)⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, List.mem_cons_self ..⟩))), fun _ h => h⟩
  · exact below_changes S _ _

/-- A part of `scratch` after the lanes `A` is outside `chFrame`. -/
theorem chFrame_disj {p : Params} (hn : p.n ≤ 32) {S sp : Addr} {stack : Nat}
    (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) {o l : Nat} (h₁ : 3808 ≤ o) (h₂ : o + l ≤ 2 ^ 16) :
    ∀ r ∈ chFrame p S sp stack, Region.Disjoint ⟨at' S o, l⟩ r := by
  intro r hr
  simp only [chFrame, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl
  · exact Offset.disjoint_base S (by omega) (by omega)
  · exact Offset.disjoint S (by omega) (by omega) (by omega)
  · exact Offset.disjoint S (by rw [oVar10']; omega) (by omega) (by rw [oVar10']; omega)
  · exact Offset.disjoint S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega) (by omega)
      (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · exact (hstk.sub_right (Offset.sub_base S h₂)).symm

/-- A region outside `scratch` and the stack is outside `chFrame`. -/
theorem chFrame_disj' {p : Params} (hn : p.n ≤ 32) {S sp : Addr} {stack : Nat} {R : Region}
    (h₁ : R.Disjoint ⟨S, 2 ^ 16⟩) (h₂ : R.Disjoint (below sp stack)) :
    ∀ r ∈ chFrame p S sp stack, R.Disjoint r := by
  intro r hr
  simp only [chFrame, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl
  · exact h₁.sub_right (Region.sub_prefix (by decide))
  · exact h₁.sub_right (Offset.sub_base S (by decide))
  · exact h₁.sub_right (Offset.sub_base S (by rw [oVar10']; omega))
  · exact h₁.sub_right (Offset.sub_base S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega))
  · exact h₂

/-- A part of `scratch` in `chFrame`: lane `k` of `A` after its `PK.seed`
and `a16`, `work` below its table, the slots after it, the frame's variables. -/
theorem sub_ch {p : Params} (hn : p.n ≤ 32) (S sp : Addr) (stack : Nat) {o l : Nat}
    (h : (∃ k < 4, Layout.laneA k + p.n + 16 ≤ o ∧ o + l ≤ Layout.laneA k + 128) ∨ o + l ≤ 1600 ∨
      (2368 ≤ o ∧ o + l ≤ 2400) ∨ (2576 ≤ o ∧ o + l ≤ 2608)) :
    ∃ r' ∈ chFrame p S sp stack, Region.Sub ⟨at' S o, l⟩ r' := by
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  rcases h with ⟨k, hk, h₁, h₂⟩ | h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)),
      Offset.sub S h₁ ?_⟩
    simp only [Layout.strideA]; rw [eA] at h₂ ⊢; omega
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)), Offset.sub_base S h⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      Offset.sub S h₁ (by omega)⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))),
      Offset.sub S (by rw [oVar10']; omega) (by rw [oVar10']; omega)⟩

/-- One height of the authentication path (`pathBody`): from height `z`
(variable 3), with the node of height `z` first in lane 0 of `A`'s message,
the node of height `z + 1` there, `H` of the address of height `z + 1` and
the node and the path's node `z` in the order bit `z` of `idx` says, and
height `z + 1`, with ZF set when it is `h′`. -/
theorem pathBody_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hlen : p.len * p.n < 2 ^ 31)
    (hhp : p.hp < 63) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {idx z : Nat} {pkSeed a16 : List Byte} (hidx : idx < 2 ^ 32) (hz : z < p.hp)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx) (h13 : s.gpr .r13 = sig)
    (hv3 : s.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    (hsig : ∀ j < p.n / 8, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 (p.len * p.n + z * p.n) + BitVec.ofNat 64 (8 * j)) 8)
    (hdis : Region.Disjoint ⟨sig + BitVec.ofNat 64 (p.len * p.n + z * p.n), p.n⟩ ⟨S, 2 ^ 16⟩)
    {Q : State → Prop}
    (k : ∀ s', (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 (z + 1) →
      s'.zf = some (decide (z + 1 = p.hp)) →
      bytesAt s'.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n =
        H p pkSeed (adrsOf a16 2 0 (z + 1) (idx / 2 ^ (z + 1)))
          (if idx / 2 ^ z % 2 = 0 then
            bytesAt s.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n ++
              bytesAt s.mem (sig + BitVec.ofNat 64 (p.len * p.n + z * p.n)) p.n
          else bytesAt s.mem (sig + BitVec.ofNat 64 (p.len * p.n + z * p.n)) p.n ++
              bytesAt s.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n) →
      Frame (chFrame p S (s.gpr .rsp) stack) s.mem s'.mem → Q s') :
    WP isa (Impl.SlhDsa.X86_64.Verify.pathBody p f) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have ha0 := laneA0
  have hv := oVar13
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have hne : ∀ r ∈ calleeSaved, r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .r10 ∧ r ≠ .r11 := by decide
  have hv8 : (⟨at' S (Layout.oVar 1 3), 8⟩ : Region).Contains (at' S (Layout.oVar 1 3)) (64 / 8) :=
    Region.contains_self _ _
  unfold Impl.SlhDsa.X86_64.Verify.pathBody
  refine seq_assoc' (order_ok hn hlen hidx (by omega) hbx h12 h13 hv3 hw hsig hdis fun s₂ g₂ r₂ w₂ hm₂ fr₂ => ?_)
  have hb₂ : s₂.gpr .rbx = S := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), hbx]
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 idx := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h12]
  have hv3₂ : s₂.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z := by
    rw [fr₂.readW hv8 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hv]; exact Offset.disjoint S (by omega) (by omega) (by omega))
      (by decide), hv3]
  refine WP.seq (adrs_ok' hn hidx (by omega) hb₂ h12₂ hv3₂ (by rw [w₂]; exact hw) fun s₃ g₃ r₃ w₃ hf₃ fr₃ => ?_)
  have hb₃ : s₃.gpr .rbx = S := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hb₂]
  have hsp₃ : s₃.gpr .rsp = s.gpr .rsp := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide)]
  have F₃ : Frame (chFrame p S (s.gpr .rsp) stack) s.mem s₃.mem :=
    (fr₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_ch hn32 S _ stack (Or.inl ⟨0, by decide, by omega, by omega⟩)).trans
      (fr₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_ch hn32 S _ stack (Or.inl ⟨0, by decide, by omega, by omega⟩))
  have henv₃ := Env.of_frame hn32 henv (F₃.sub (chFrame_sub p S _ stack)) hstk
  have hw₃ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₃.wr := by rw [w₃, w₂]; exact hw
  rw [ht]
  refine WP.seq (WP.mono (Levels.t4_ok (p := p) T f.t4name hn hst hs63 hb₃ hw₃ hS (by rw [hsp₃]; exact hstk)
    henv₃.rc) fun s₄ ⟨r₄, w₄, g₄, _, o₄, fr₄⟩ => ?_)
  have hb₄ : s₄.gpr .rbx = S := by rw [g₄ _ (by decide), hb₃]
  have hsp₄ : s₄.gpr .rsp = s.gpr .rsp := by rw [g₄ _ (by decide), hsp₃]
  -- the variable, which the call leaves
  have hv3₄ : s₄.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z := by
    rw [fr₄.readW hv8 (fun r hr => ?_) (by decide), fr₃.readW hv8 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hv]; exact Offset.disjoint S (by omega) (by omega) (by omega))
      (by decide), hv3₂]
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hv]
    rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
    · rw [eA]; exact Offset.disjoint S (by omega) (by omega) (by rw [eA] at *; omega)
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · rw [hsp₃]; exact (hstk.sub_right (Offset.sub_base S (by omega))).symm
  have hw₄ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₄.wr := by rw [w₄]; exact hw₃
  refine wp_movm (a := at' S (Layout.oVar 1 3)) (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hb₄])
    (by rw [hv]; exact in_scr' hw₄ (by omega)) fun s₅ u₅ => ?_
  refine wp_addi fun s₆ u₆ => ?_
  have hb₆ : s₆.gpr .rbx = S := by rw [u₆.other _ (by decide), u₅.other _ (by decide), hb₄]
  refine wp_store (a := at' S (Layout.oVar 1 3)) (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hb₆])
    (by rw [u₆.wr, u₅.wr, hv]; exact in_scr hw₄ (by omega)) fun s₇ g₇ m₇ r₇ w₇ => ?_
  refine Levels.wp_cmpi fun s₈ g₈ m₈ r₈ w₈ z₈ => WP.block_nil ?_
  have hrax : s₆.gpr .rax = BitVec.ofNat 64 (z + 1) := by
    rw [u₆.gpr, u₅.gpr, hv3₄, sx1']; exact (BitVec.ofNat_add z 1).symm
  have hm₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have hm₈ : s₈.mem = s₄.mem.writeW (at' S (Layout.oVar 1 3)) (BitVec.ofNat 64 (z + 1)) := by
    rw [m₈, m₇, hrax, hm₆]
  have hl0 : bytesAt s₈.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n = bytesAt s₄.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n := by
    rw [hm₈]
    exact bytesAt_frame (frame_writeW _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hv]
      exact Offset.disjoint S (by omega) (by omega) (by omega)) (by omega)
  refine k s₈ (fun r hr => ?_) (by rw [r₈, r₇, u₆.rd, u₅.rd, r₄, r₃, r₂]) (by rw [w₈, w₇, u₆.wr, u₅.wr, w₄, w₃, w₂])
    (by rw [hm₈]; exact Mem.readW_writeW_self64 _ _ _) ?_ ?_ ?_
  · obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hne r hr
    rw [g₈, g₇, u₆.other _ h₁, u₅.other _ h₁, g₄ r hr, g₃ _ h₁ h₂ h₅ h₆, g₂ _ h₁ h₂ h₃ h₄]
  · rw [z₈, g₇, hrax, sx_ofNat (by omega), cmp_eq (by omega) (by omega)]
  · rw [hl0, o₄ 0 (by decide), Levels.H_shake hfam]
    -- lane 0's message: `PK.seed`, the address, the two nodes
    have hm : bytesAt s₃.mem (at' S (Layout.laneA 0 + p.n + 32)) (2 * p.n) =
        bytesAt s₂.mem (at' S (Layout.laneA 0 + p.n + 32)) (2 * p.n) :=
      bytesAt_frame fr₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
        (by omega)
    rw [show 3 * p.n + 32 = p.n + (16 + (16 + 2 * p.n)) by omega, bytesAt_split2, bytesAt_split2, bytesAt_split2,
      show Layout.laneA 0 + p.n + 16 + 16 = Layout.laneA 0 + p.n + 32 by omega]
    rw [show S + BitVec.ofNat 64 (Layout.laneA 0) = at' S (Layout.laneA 0) from rfl, henv₃.seedA 0 (by decide),
      show S + BitVec.ofNat 64 (Layout.laneA 0 + p.n) = at' S (Layout.laneA 0 + p.n) from rfl,
      henv₃.adrsA 0 (by decide),
      show S + BitVec.ofNat 64 (Layout.laneA 0 + p.n + 16) = at' S (Layout.laneA 0 + p.n + 16) from rfl, hf₃,
      show S + BitVec.ofNat 64 (Layout.laneA 0 + p.n + 32) = at' S (Layout.laneA 0 + p.n + 32) from rfl, hm, hm₂]
    simp only [adrsOf, List.append_assoc]
  · refine F₃.trans ((fr₄.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
      · exact sub_ch hn32 S _ stack (Or.inl ⟨c, hc, by omega, by omega⟩)
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact sub_ch hn32 S _ stack (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
      · rw [hsp₃]; exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩
    · rw [hm₈]
      exact (frame_writeW _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hv]
        exact sub_ch hn32 S _ stack (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))

end VG.Proof.SlhDsa.X86_64
