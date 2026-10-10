import VerifiedGarbage.Proof.Sm4.X86_64.CtrBlocks
import VerifiedGarbage.Proof.Sm4.X86_64.CtrXor

/-!
# One group of blocks of SM4-CTR on x86-64

`ctrGroup_wp`: one iteration of the data loop writes the group's sixteen
counter blocks to the tail buffer (`ctrBlocks_ok`), transforms them there
into the keystream (`crypt16_wp`), XORs the keystream into the group's
blocks (`xorBlocks_wp`) and steps to the next group. Block `j` of the data
becomes its XOR with the encryption of the counter block `V + j`
(`ctrF`).
-/

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_)
open VG.Proof.Sm4 (DInv ofInt_nat quads ofBlock outBlock not_contains_off toNat_off blockAt_getD)
open VG.Spec.Aes (bytesAt)

/-- The counter block `V` (its 16 big-endian bytes), as an SM4 block. -/
def ctrBlk (V : Nat) : Spec.Sm4.Block := Vector.ofFn fun i => (Spec.Ctr.ofNat V 16).getD i.val 0

/-- Keystream block `j` from the counter block `V`, with the round keys `E`. -/
def ksF (E : Nat → Spec.Sm4.Word) (V j : Nat) : Spec.Sm4.Block := outBlock (quads .enc E 8 (ofBlock (ctrBlk (V + j))))

/-- Data block `j` after CTR from the counter block `V`. -/
def ctrF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (V j : Nat) : Spec.Sm4.Block :=
  Vector.ofFn fun i => (ksF E V j).getD i.val 0 ^^^ (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j))).getD i.val 0

theorem blockAt_of_bytes {m : Mem} {P : Addr} {l : List Byte} (h : bytesAt m P 16 = l) :
    Spec.Sm4.blockAt m P = Vector.ofFn fun i => l.getD i.val 0 := by
  apply Vector.ext; intro i hi
  simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn, ← h, bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

/-- The data loop, before group `k`. -/
structure CInv (s₀ : State) (b D : Addr) (n : Nat) (R : Region) (E : Nat → Spec.Sm4.Word) (V k : Nat) (s : State) :
    Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rdx : s.gpr .rdx = D + BitVec.ofNat 64 (256 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (n - 16 * k)
  lt : 16 * k < n
  rdi : s.gpr .rdi = b + BitVec.ofNat 64 (8 * tableEnd)
  scr : ScrOk s₀ b E s.mem
  hi : s.mem.readW (wordAddr b ctrHi) 64 = hiOf (V + 16 * k)
  lo : s.mem.readW (wordAddr b ctrLo) 64 = loOf (V + 16 * k)
  data : DInv s₀.mem s.mem D n (16 * k) (ctrF s₀.mem D E V)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩, R] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure CDone (s₀ : State) (b D : Addr) (n : Nat) (R : Region) (E : Nat → Spec.Sm4.Word) (V : Nat) (s : State) :
    Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n n (ctrF s₀.mem D E V)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩, R] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ctrF_getD (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (V j : Nat) {u : Nat} (hu : u < 16) :
    (ctrF m₀ D E V j).getD u 0 = (ksF E V j).getD u 0 ^^^ m₀ (D + BitVec.ofNat 64 (16 * j + u)) := by
  rw [← addr_add, ← blockAt_getD m₀ _ hu]
  simp [ctrF, Vector.getD, hu]

theorem ctrGroup_wp {s₀ : State} {b D : Addr} {n : Nat} {R : Region} {E : Nat → Spec.Sm4.Word} {V : Nat}
    (hp : GPre s₀ b D n) {k : Nat} {s : State} (hi : CInv s₀ b D n R E V k s) :
    WP isa ctrGroup s fun s' => (s'.zf = some true ∧ CDone s₀ b D n R E V s') ∨
      (s'.zf = some false ∧ CInv s₀ b D n R E V (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  rw [slots_eq] at hfit
  let v := n - 16 * k
  let c := min v 16
  have hv : v < 2 ^ 64 := by omega
  have hc0 : 0 < c := by omega
  have hc16 : c ≤ 16 := by omega
  have hkc : 256 * k + 16 * c ≤ 16 * n := by omega
  let A := D + BitVec.ofNat 64 (256 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t, t < 32 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)
  have inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega) (by omega)
  have sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega))
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have subTC : ∀ r ∈ [tailRegion b 16, ctrRegion b], Region.Sub r ⟨b, 8 * slots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine subS ?_ <;> simp only [tailSlot_eq, ctrHi_eq, slots_eq] <;> omega
  -- The counter blocks.
  obtain ⟨s₁, e₁, tb₁, h₁, l₁, f₁, o₁, rd₁, wr₁⟩ := ctrBlocks_ok s hi.base hwS hi.hi hi.lo
  unfold ctrGroup
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have base₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide) (by decide) (by decide), hi.base]
  have sc₁ : ScrOk s₀ b E s₁.mem := by
    refine hi.scr.frame f₁ fun t ht r hr => ?_
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    rcases ht with rfl | rfl | rfl <;> rcases hr with rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [tailSlot_eq, tableSlot_eq, savedSlot_eq, ctrHi_eq]) <;> omega
  -- The sixteen blocks.
  have hkey : KeyCtx s₁ E :=
    { scr := by rw [base₁, wr₁]; exact hwS
      fit := by rw [base₁, slots_eq]; exact hfit
      keys := fun e he => by rw [base₁]; exact sc₁.keys e he }
  have hrdi₁ : s₁.gpr .rdi = s₁.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [o₁ _ (by decide) (by decide) (by decide), hi.rdi, base₁]
  have hT₁ : ∀ j < 16, tailBlock s₁ j = ctrBlk (V + 16 * k + j) := fun j hj => by
    simp only [tailBlock, base₁]
    exact blockAt_of_bytes (tb₁ j hj)
  refine WP.seq (WP.mono (crypt16_wp hkey (sc₁.masks.ok base₁) hrdi₁) fun s₂ ⟨c₂, b₂⟩ => ?_)
  have base₂ : s₂.gpr sb = b := by rw [c₂.base, base₁]
  have f₂ : Frame [⟨b, 8 * tableSlot⟩] s₁.mem s₂.mem := by have := c₂.frame; rw [base₁] at this; exact this
  have g₂ : ∀ r, r ∉ sboxWrites → r ≠ kp → s₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [c₂.keep r h1 h2, o₁ r (fun h => h1 (by subst h; decide)) (fun h => h1 (by subst h; decide))
      (fun h => h1 (by subst h; decide))]
  have sc₂ : ScrOk s₀ b E s₂.mem := by
    refine sc₁.frame2 f₂ (c₂.masks.at base₂) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    subst hr
    rcases ht with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]) (by rw [tableSlot_eq]; omega)
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq, savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega)
  have keepC : ∀ x, x = ctrHi ∨ x = ctrLo → s₂.mem.readW (wordAddr b x) 64 = s₁.mem.readW (wordAddr b x) 64 :=
    fun x hx => f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hx with rfl | rfl <;> exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]; decide) (by decide))
      (by decide)
  -- The keystream XORed into the group's blocks.
  have r8₂ : s₂.gpr .r8 = BitVec.ofNat 64 v := by rw [g₂ _ (by decide) (by decide), hi.r8]
  have rdx₂ : s₂.gpr .rdx = A := by rw [g₂ _ (by decide) (by decide), hi.rdx]
  unfold xorOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r8₂ hv) fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ => ?_))
  obtain ⟨s₄a, e₄a, r₄a, o₄a, m₄a, rd₄a, wr₄a⟩ := slotAddr_ok s₃ .rax tailSlot (by decide)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₄a .rbx .rdx
  refine WP.seq (WP.of_runBlock ⟨s₄, by rw [runBlock_app, e₄a, Option.bind_some, e₄], ?_⟩)
  have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₄a, m₃]
  have wr₂' : s₂.wr = s.wr := by rw [c₂.wr, wr₁]
  have rd₂' : s₂.rd = s.rd := by rw [c₂.rd, rd₁]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄a, wr₃, wr₂']
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₄a, rd₃, rd₂']
  have g₄ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₄.gpr r = s₂.gpr r := fun r h1 h2 h3 => by
    rw [o₄ r h2, o₄a r h1, o₃ r h3]
  refine WP.mono (xorBlocks_wp (A := T) (B := A) hc0 hc16
    (fun t ht => by rw [rd₄', wr₄']; exact inRd (inT t (by omega)))
    (fun t ht => by rw [wr₄']; exact inA t ht) sepAT.symm
    ⟨by rw [o₄ _ (by decide), r₄a, o₃ _ (by decide), base₂]; simp [T],
      by rw [r₄, o₄a _ (by decide), o₃ _ (by decide), rdx₂]; simp [A],
      by rw [o₄ _ (by decide), o₄a _ (by decide), c₃, Nat.sub_zero], fun t ht => by omega, fun t _ _ => rfl,
      Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₅ h₅ => ?_
  have f₅ : Frame [⟨A, 16 * c⟩] s₂.mem s₅.mem := by rw [← mem₄]; exact h₅.frame
  have g₅ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₅.gpr r = s₂.gpr r :=
    fun r h1 h2 h3 h4 => by rw [h₅.regs r h1 h2 h3 h4, g₄ r h1 h2 h3]
  have base₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), base₂]
  have rdx₅ : s₅.gpr .rdx = A := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), rdx₂]
  have r8₅ : s₅.gpr .r8 = BitVec.ofNat 64 v := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide), r8₂]
  have rdi₅ : s₅.gpr .rdi = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide), hi.rdi]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide), hi.rsp]
  have wr₅' : s₅.wr = s₀.wr := by rw [h₅.wr, wr₄', hi.wr]
  have rd₅' : s₅.rd = s₀.rd := by rw [h₅.rd, rd₄', hi.rd]
  have sc₅ : ScrOk s₀ b E s₅.mem := by
    refine sc₂.frame f₅ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [tableSlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right hsub).symm
  have keepC₅ : ∀ x, x = ctrHi ∨ x = ctrLo → s₅.mem.readW (wordAddr b x) 64 = s₂.mem.readW (wordAddr b x) 64 :=
    fun x hx => f₅.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right
        (subS (by rcases hx with rfl | rfl <;> simp only [ctrHi_eq, ctrLo_eq, slots_eq] <;> omega))).symm) (by decide)
  have hi₅ : s₅.mem.readW (wordAddr b ctrHi) 64 = hiOf (V + 16 * (k + 1)) := by
    rw [keepC₅ _ (.inl rfl), keepC _ (.inl rfl), h₁, show V + 16 * k + 16 = V + 16 * (k + 1) by omega]
  have lo₅ : s₅.mem.readW (wordAddr b ctrLo) 64 = loOf (V + 16 * (k + 1)) := by
    rw [keepC₅ _ (.inr rfl), keepC _ (.inr rfl), l₁, show V + 16 * k + 16 = V + 16 * (k + 1) by omega]
  have fr₅ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩, R] s.mem s₅.mem := by
    refine ((f₁.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, subTC r hr⟩).trans
      ((f₂.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₅.sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega)
  -- The data.
  have hdata : DInv s₀.mem s₅.mem D n (16 * k + c) (ctrF s₀.mem D E V) := by
    intro i hin
    by_cases hin1 : 256 * k ≤ i ∧ i < 256 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 256 * k) := by
        rw [addr_add, show 256 * k + (i - 256 * k) = i by omega]
      have hj : (i - 256 * k) / 16 < c := by omega
      have eT : T + BitVec.ofNat 64 (i - 256 * k) = s₂.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 256 * k) / 16)) +
          BitVec.ofNat 64 ((i - 256 * k) % 16) := by
        rw [base₂, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 256 * k) / 16) + (i - 256 * k) % 16 =
          8 * tailSlot + (i - 256 * k) by omega]
      have hks : s₂.mem (T + BitVec.ofNat 64 (i - 256 * k)) = (ksF E V (i / 16)).getD (i % 16) 0 := by
        rw [eT, ← blockAt_getD s₂.mem _ (Nat.mod_lt _ (by decide))]
        show (tailBlock s₂ _).getD _ 0 = _
        rw [b₂ _ (by omega), hT₁ _ (by omega), ksF, show V + 16 * k + (i - 256 * k) / 16 = V + i / 16 by omega,
          show (i - 256 * k) % 16 = i % 16 by omega]
      have hd₂ : s₂.mem (A + BitVec.ofNat 64 (i - 256 * k)) = s₀.mem (D + BitVec.ofNat 64 i) := by
        rw [← e1, f₂.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)) (by simp only; omega) hin,
          f₁.bytes (R := ⟨D, 16 * n⟩) (hdS subTC) (by simp only; omega) hin, hi.data i hin,
          ite_eq_right (by omega)]
      rw [e1, h₅.xored _ (by omega), mem₄, hks, hd₂, ite_eq_left (show i < 16 * (16 * k + c) by omega),
        ctrF_getD _ _ _ _ _ (Nat.mod_lt _ (by decide)), show 16 * (i / 16) + i % 16 = i by omega]
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega) (by omega) (by omega) (by omega)
      rw [f₅ _ hout,
        f₂.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)) (by simp only; omega) hin,
        f₁.bytes (R := ⟨D, 16 * n⟩) (hdS subTC) (by simp only; omega) hin, hi.data i hin]
      by_cases h2 : i < 256 * k
      · rw [ite_eq_left (show i < 16 * (16 * k) by omega), ite_eq_left (show i < 16 * (16 * k + c) by omega)]
      · rw [ite_eq_right (show ¬ i < 16 * (16 * k) by omega), ite_eq_right (show ¬ i < 16 * (16 * k + c) by omega)]
  have fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩, R] s₀.mem s₅.mem := hi.frame.trans fr₅
  -- On to the next group.
  unfold advance
  obtain ⟨s₈, e₈, cf₈, g₈, m₈, rd₈, wr₈⟩ := cmpImm_ok s₅ .r8 16 r8₅ hv rfl
  refine WP.seq (WP.of_runBlock ⟨s₈, e₈, ?_⟩)
  refine WP.ite (decide (v < 16)) (by simp [X86_64.eval, cf₈]) (fun hlt => ?_) (fun hge => ?_)
  · have hlt' : v < 16 := by simpa using hlt
    obtain ⟨s₉, e₉, z₉, o₉, m₉, rd₉, wr₉⟩ := subSelf_ok s₈ .r8
    refine WP.of_runBlock ⟨s₉, e₉, .inl ⟨z₉, ?_⟩⟩
    have hn : 16 * k + c = n := by omega
    refine ⟨by rw [o₉ _ (by decide), g₈, base₅], by rw [o₉ _ (by decide), g₈, rsp₅],
      by rw [m₉, m₈]; exact sc₅, fun i hi' => by rw [m₉, m₈, hdata i hi', hn], by rw [m₉, m₈]; exact fr,
      by rw [rd₉, rd₈, rd₅'], by rw [wr₉, wr₈, wr₅']⟩
  · have hge' : 16 ≤ v := by simpa using hge
    have hc : c = 16 := by omega
    obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := addImm_ok s₈ .rdx 256
    obtain ⟨s₁₀, e₁₀, r₁₀, z₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subImm_ok s₉ .r8 16
    have r8₉ : s₉.gpr .r8 = BitVec.ofNat 64 v := by rw [o₉ _ (by decide), g₈, r8₅]
    have hz : s₁₀.zf = some (decide (v = 16)) := by
      rw [z₁₀, r8₉, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq hv (by decide)]
    refine WP.of_runBlock ⟨s₁₀, by
      rw [show ([Instr.alu .add .rdx (.imm 256), .alu .sub .r8 (.imm 16)] : List Instr) =
        [.alu .add .rdx (.imm 256)] ++ [.alu .sub .r8 (.imm 16)] from rfl, runBlock_app, e₉,
        Option.bind_some, e₁₀], ?_⟩
    have hm : s₁₀.mem = s₅.mem := by rw [m₁₀, m₉, m₈]
    have base₁₀ : s₁₀.gpr sb = b := by rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, base₅]
    have rsp₁₀ : s₁₀.gpr .rsp = s₀.gpr .rsp := by rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, rsp₅]
    have rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈, rd₅']
    have wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈, wr₅']
    by_cases h16 : v = 16
    · refine .inl ⟨by rw [hz, h16]; rfl, base₁₀, rsp₁₀, hm ▸ sc₅, ?_, hm ▸ fr, rd₁₀', wr₁₀'⟩
      intro i hi'
      rw [hm, hdata i hi', show 16 * k + c = n by omega]
    · refine .inr ⟨by rw [hz]; simp [h16], base₁₀, rsp₁₀, ?_, ?_, by omega, ?_, hm ▸ sc₅, by rw [hm]; exact hi₅,
        by rw [hm]; exact lo₅, ?_, hm ▸ fr, rd₁₀', wr₁₀'⟩
      · rw [o₁₀ _ (by decide), r₉, g₈, rdx₅, show (256 : BitVec 32).signExtend 64 = BitVec.ofNat 64 256 from rfl,
          addr_add, show 256 * k + 256 = 256 * (k + 1) by omega]
      · rw [r₁₀, r8₉, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
          VG.Offset.ofNat_sub_ofNat (by omega), show v - 16 = n - 16 * (k + 1) by omega]
      · rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, rdi₅]
      · intro i hi'
        rw [hm, hdata i hi', show 16 * k + c = 16 * (k + 1) by omega]

end VG.Proof.Sm4.X86_64
