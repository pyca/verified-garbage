import VerifiedGarbage.Proof.Camellia.X86_64.Group

/-!
# Camellia ECB on x86-64: the whole function

`ecb_wp`: with the working space as an argument (`ecbX86_64`), `ecb dir`
saves the callee-saved registers, sets the masks, builds the table of
subkeys for 18 or 24 rounds in the order `dir` uses them, transforms the
blocks a group at a time (`dataGroup_wp`) and restores the registers.
-/

namespace VG.Proof.Camellia

open VG VG.X86_64 VG.Impl.Camellia.X86_64

/-- The specification's direction. -/
def specDir : Dir → Spec.Camellia.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on x86-64 with its working space at `r8`. -/
def ecbX86_64 (dir : Dir) : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 272⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * slots⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 8 * slots ≤ 2 ^ 64 ∧ ((s.gpr .rsi).toNat = 18 ∨ (s.gpr .rsi).toNat = 24)
  post s s' :=
    Spec.Camellia.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Camellia.ecb (Spec.Camellia.subkeysAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (specDir dir)
        (Spec.Camellia.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Camellia

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st setMasks)

theorem testSelf_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (s.gpr r == 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨arithFlags s (s.gpr r &&& s.gpr r) false false, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp only [RegUpd.zf_arithFlags, BitVec.and_self]

/-- The order of the subkeys in the table, for each direction. -/
def permOf : Dir → Nat → Nat → Nat
  | .encrypt => fun _ i => i
  | .decrypt => Camellia.decPerm

theorem endAddr_post {s₀ s : State} {b sched : Addr} {g : Nat} {perm : Nat → Nat} (hg : g = 3 ∨ g = 4)
    (h : KeysPost s₀ b sched g perm s) :
    ∃ s', runBlock isa (endAddr g) s = some s' ∧ KeysPost s₀ b sched g perm s' ∧
      s'.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rdi sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rdi (BitVec.ofNat 32 (8 * keySlot + 512 * g))
  have hb : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide), o₁ _ (by decide)]
  refine ⟨s₂, by rw [endAddr, show ([movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * keySlot + 512 * g)))] :
      List Instr) = [movR .rdi sb] ++ [.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * keySlot + 512 * g)))] from rfl,
      runBlock_append', e₁, Option.bind_some, e₂],
    ⟨h.pre.congr hb (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]), fun i hi => by rw [m₂, m₁]; exact h.ent i hi,
      fun kv hkv => by
        show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
        rw [m₂, m₁, hb]; exact h.masks kv hkv,
      by rw [m₂, m₁]; exact h.frame, fun r h1 h2 h3 => by rw [o₂ r h3, o₁ r h3, h.regs r h1 h2 h3],
      by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr]⟩, ?_⟩
  rw [r₂, r₁, h.pre.base]
  rcases hg with rfl | rfl <;> rfl

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : Addr} {g : Nat} (hg : g = 3 ∨ g = 4)
    (hk : KeyPre s₀ b sched) (hrdi : s₀.gpr .rdi = sched) (hm : MasksOk s₀) :
    WP isa (keys dir g) s₀ fun s => KeysPost s₀ b sched g (permOf dir g) s ∧
      s.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
  unfold keys
  cases dir
  · refine WP.seq (WP.mono (encKeys_wp hg hk hrdi hm) fun s h => ?_)
    obtain ⟨s', e', h', r'⟩ := endAddr_post hg h
    exact WP.of_runBlock ⟨s', e', h', r'⟩
  · refine WP.seq (WP.mono (decKeys_wp hg hk hrdi hm) fun s h => ?_)
    obtain ⟨s', e', h', r'⟩ := endAddr_post hg h
    exact WP.of_runBlock ⟨s', e', h', r'⟩

theorem dataLoop_wp {s₀ : State} {b D : Addr} {n g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n g)
    {s : State} (hi : GInv s₀ b D n g E 0 s) :
    WP isa (.loop Impl.Camellia.X86_64.group .ne) s (GDone s₀ b D n g E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n g E k s) (fun m s hs => ?_) n s
    ⟨0, by omega, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - 8 * (k + 1), by have := d.lt; have := hk.lt; omega,
      k + 1, rfl, d⟩

theorem sreg_ne (i : Nat) : sreg i ≠ .r9 ∧ sreg i ≠ .r8 := by
  unfold sreg; split <;> decide

theorem prologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .r8 = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) :
    ∃ s, runBlock isa (([movR .r9 .r8, movR .r8 .rcx] : List Instr) ++ saveRegs ++ setMasks layerMasks ++
        ([.alu .cmp .rsi (.imm 18)] : List Instr)) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r8 = s₀.gpr .rcx ∧ (∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ t0 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ s.zf = some (s₀.gpr .rsi - (18 : BitVec 32).signExtend 64 == 0) ∧
      Frame [⟨b, 8 * tailSlot⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ .r9 .r8
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁a .r8 .rcx
  have hb₁ : s₁.gpr sb = b := by rw [show sb = .r9 from rfl, o₁ _ (by decide), r₁a, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (by rw [wr₁, wr₁a]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setMasks_ok (b := b) layerMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁, wr₁a]; exact hw) (fun kv hkv => mask_lt hkv) (by decide)
  obtain ⟨s₄, e₄, z₄, g₄, m₄, rd₄, wr₄⟩ := cmpImmZ_ok s₃ .rsi 18
  have g₁ : ∀ r, r ≠ .r9 → r ≠ .r8 → s₁.gpr r = s₀.gpr r := fun r h1 h2 => by rw [o₁ r h2, o₁a r h1]
  refine ⟨s₄, by
    rw [runBlock_append', runBlock_append', runBlock_append', show ([movR .r9 .r8, movR .r8 .rcx] : List Instr) =
      [movR .r9 .r8] ++ [movR .r8 .rcx] from rfl, runBlock_append', e₁a, Option.bind_some, e₁,
      Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some, e₄],
    by rw [g₄, g₃ _ (by decide), g₂, hb₁], by rw [g₄, g₃ _ (by decide), g₂, r₁, o₁a _ (by decide)],
    fun r h1 h2 h3 => by rw [g₄, g₃ r h3, g₂, g₁ r h1 h2], fun i hi => ?_, fun kv hkv => ?_,
    by rw [z₄, g₃ _ (by decide), g₂, g₁ _ (by decide) (by decide)], ?_,
    by rw [rd₄, rd₃, rd₂, rd₁, rd₁a], by rw [wr₄, wr₃, wr₂, wr₁, wr₁a]⟩
  · obtain ⟨n1, n2⟩ := sreg_ne i
    rw [m₄, ← g₁ _ n1 n2, ← sv₂ i hi]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    have : savedSlot = 371 := rfl
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [keySlot_eq]; omega) (by omega)
  · show s₄.mem.readW (wordAddr (s₄.gpr sb) kv.1) 64 = kv.2
    rw [m₄, g₄]; exact v₃ kv hkv
  · have hm1 : s₁.mem = s₀.mem := by rw [m₁, m₁a]
    rw [m₄, ← hm1]
    refine f₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by rw [keySlot_eq, tailSlot_eq]; omega)

/-! ## The specification -/

theorem blocksAt_of_dinv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Camellia.Block}
    (h : DInv m₀ m D n n F) : Spec.Camellia.blocksAt m D n = (List.range n).map F := by
  simp only [Spec.Camellia.blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext; intro t ht
  simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn]
  rw [addr_add, h _ (by omega), ite_eq_left (by omega), show (16 * j + t) / 16 = j by omega,
    show (16 * j + t) % 16 = t by omega]
  simp [Vector.getD, ht]

/-- The schedule's words, as `subkeysAt` reads them. -/
abbrev schedWords (m : Mem) (sched : Addr) (R : Nat) : List (BitVec 64) :=
  (List.range (Spec.Camellia.scheduleLength R)).map fun i => Spec.Camellia.wordAt m (sched + BitVec.ofNat 64 (8 * i))

/-- The block function of each direction. -/
def blockFn (sk : Spec.Camellia.Subkeys) : Spec.Camellia.Direction → Spec.Camellia.Block → Spec.Camellia.Block
  | .encrypt => Spec.Camellia.encryptBlock sk
  | .decrypt => Spec.Camellia.decryptBlock sk

theorem ecb_eq (sk : Spec.Camellia.Subkeys) (d : Spec.Camellia.Direction) (l : List Spec.Camellia.Block) :
    Spec.Camellia.ecb sk d l = l.map (blockFn sk d) := by
  cases d <;> rfl

theorem outF_spec (dir : Dir) (m : Mem) (sched D : Addr) {R : Nat} (hR : R = 18 ∨ R = 24) (j : Nat) :
    outF m D (R / 6) (fun i => (schedWords m sched R).getD (permOf dir (R / 6) i) 0) j =
      blockFn (Spec.Camellia.subkeysAt m sched R) (specDir dir)
        (Spec.Camellia.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, specDir, blockFn, Spec.Camellia.encryptBlock, Spec.Camellia.subkeysAt,
      Camellia.encryptWith_eq hR, permOf]
  · simp only [outF, specDir, blockFn, Spec.Camellia.decryptBlock, Spec.Camellia.subkeysAt,
      Camellia.decryptWith_eq hR, permOf]

theorem schedWords_getD (m : Mem) (sched : Addr) {R i : Nat} (hi : i < Spec.Camellia.scheduleLength R) :
    (schedWords m sched R).getD i 0 = Spec.Camellia.wordAt m (sched + BitVec.ofNat 64 (8 * i)) := by
  simp [schedWords, List.getD_eq_getElem?_getD, hi]

theorem permOf_lt (dir : Dir) {g i : Nat} (hi : i < 8 * g + 2) : permOf dir g i < 8 * g + 2 := by
  cases dir <;> simp only [permOf, Camellia.decPerm] <;> (try split) <;> (try split) <;> omega

/-! ## The whole function -/

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbX86_64 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => gprPreserved s₀ s' ∧ (ecbX86_64 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, dRD, dRS, fitK, fitD, fitB, hR⟩ := hp
  let b := s₀.gpr .r8
  let D := s₀.gpr .rdx
  let n := (s₀.gpr .rcx).toNat
  let sched := s₀.gpr .rdi
  let R := (s₀.gpr .rsi).toNat
  have hg : R / 6 = 3 ∨ R / 6 = 4 := by omega
  have hg4 : R / 6 ≤ 4 := by omega
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r8₁, g₁, sv₁, m₁, z₁, f₁, rd₁, wr₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : KeyPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have rdi₁ : s₁.gpr .rdi = sched := g₁ _ (by decide) (by decide) (by decide)
  have hz₁ : s₁.zf = some (decide (R = 18)) := by
    rw [z₁, show (18 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18 from rfl,
      show s₀.gpr .rsi = BitVec.ofNat 64 R by simp only [R, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  -- The table.
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  rw [hgR] at hg hg4
  refine WP.seq (WP.mono (M := isa) (Q := fun s => KeysPost s₁ b sched g (permOf dir g) s ∧
      s.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g))
    (WP.ite (decide (R = 18)) (by simp [X86_64.eval, hz₁]) (fun h => ?_) (fun h => ?_)) fun s₂ ⟨k₂, rdi₂⟩ => ?_)
  · obtain rfl : g = 3 := by simp at h; omega
    exact keys_wp dir (Or.inl rfl) hk₁ rdi₁ m₁
  · obtain rfl : g = 4 := by simp at h; omega
    exact keys_wp dir (Or.inr rfl) hk₁ rdi₁ m₁
  -- The scratch buffer and the data before the groups.
  let E : Nat → BitVec 64 := fun i => (schedWords s₀.mem sched R).getD (permOf dir g i) 0
  have hfitB := fitB
  rw [slots_eq] at hfitB
  have f₀₂ : Frame [⟨b, 8 * slots⟩] s₀.mem s₂.mem := by
    refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
      (simp only [List.mem_singleton] at hr; subst hr) <;>
      exact Region.sub_prefix (by simp only [slots_eq, tailSlot_eq, endSlot_eq]; omega)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have hE : ∀ i < 8 * g + 2,
      Spec.Camellia.wordAt s₁.mem (sched + BitVec.ofNat 64 (8 * permOf dir g i)) = E i := fun i hi => by
    have hp := permOf_lt dir hi
    rw [show E i = _ from schedWords_getD s₀.mem sched (R := R) (by simp only [Spec.Camellia.scheduleLength]; omega)]
    refine wordAt_frame f₁ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (dSS.sub_left (VG.Offset.sub_base sched (by omega))).sub_right (Region.sub_prefix (by
      rw [slots_eq, tailSlot_eq]; omega))
  have sc₂ : ScrOk s₀ b g E s₂.mem := by
    refine ⟨k₂.masks.at base₂, fun i hi => hE i hi ▸ k₂.ent i hi, fun i hi => ?_⟩
    rw [← sv₁ i hi]
    refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    have : savedSlot = 371 := rfl
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [endSlot_eq]; omega) (by omega)
  have data₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₀₂.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
      (by simp only; omega) hi
  have fr₂ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have rsp₂ : s₂.gpr .rsp = s₀.gpr .rsp := by
    rw [k₂.regs _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)]
  have r8₂ : s₂.gpr .r8 = s₀.gpr .rcx := by rw [k₂.regs _ (by decide) (by decide) (by decide), r8₁]
  have rdx₂ : s₂.gpr .rdx = D := by
    rw [k₂.regs _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- Any blocks?
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₂ .r8
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [z₃, r8₂]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp [n, h], fun h => BitVec.eq_of_toNat_eq (by simpa [n] using h)⟩
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n g E)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₃]) (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨by rw [g₃, base₂], by rw [g₃, rsp₂], by rw [m₃]; exact sc₂, fun i hi => by omega,
      by rw [m₃]; exact fr₂, by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitB, fitD, hg⟩ ⟨by rw [g₃, base₂], by rw [g₃, rsp₂],
      by rw [g₃, rdx₂]; simp, by rw [g₃, r8₂, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega,
      by rw [g₃, rdi₂], by rw [m₃]; exact sc₂, fun i hi => ?_, by rw [m₃]; exact fr₂, by rw [rd₃, rd₂],
      by rw [wr₃, wr₂]⟩
    rw [m₃, data₂ i hi, ite_eq_right (by omega)]
  -- The epilogue.
  obtain ⟨s₅, e₅, rg₅, o₅, f₅, rd₅, wr₅⟩ := restore_ok (by rw [d₄.wr]; exact hwS) d₄.base d₄.scr.saved
  refine WP.of_runBlock ⟨s₅, e₅, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₅ 0 (by omega)
    · exact rg₅ 1 (by omega)
    · rw [o₅ _ (fun i hi => by unfold sreg; split <;> decide), d₄.rsp]
    · exact rg₅ 2 (by omega)
    · exact rg₅ 3 (by omega)
    · exact rg₅ 4 (by omega)
    · exact rg₅ 5 (by omega)
  · -- The return address is untouched.
    have fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₅.mem :=
      d₄.frame.trans (f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by rw [slots_eq, tailSlot_eq]; omega)⟩)
    refine fr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · have hd₅ : DInv s₀.mem s₅.mem D n n (outF s₀.mem D g E) := fun i hi => by
      rw [f₅.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dDS.sub_right (Region.sub_prefix (by rw [slots_eq, tailSlot_eq]; omega)))
        (by simp only; omega) hi]
      exact d₄.data i hi
    show Spec.Camellia.blocksAt s₅.mem D n = _
    rw [blocksAt_of_dinv hd₅, ecb_eq]
    simp only [Spec.Camellia.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    subst hgR
    exact outF_spec dir s₀.mem sched D hR j

end VG.Proof.Camellia.X86_64
