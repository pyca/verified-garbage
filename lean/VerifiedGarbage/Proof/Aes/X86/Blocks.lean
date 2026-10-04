import VerifiedGarbage.Proof.Aes.X86.Ecb
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES on whole blocks on x86 (32-bit): the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt2` and `decrypt2`, and are proven at once, for any transformation
of two blocks with `CryptOk`: the prologue saves the callee-saved registers
in the scratch buffer and bitslices the round keys as `vg_aes_ctr32`'s does
(`Ctr32.lean`, `Keys.lean`); the groups (`Ecb.lean`) do the rest; the
epilogue restores the registers.
-/

namespace VG.Proof.Aes

open _root_.VG.X86 in
/-- X86 (32-bit) contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher), whose arguments are on
the stack: replaces each of the `n` blocks at `data` with `f rounds w` of it,
for the key schedule `w`.

The code may read `schedule` (240 bytes) and the arguments (20 bytes above
the return address), and read and write `data` (`16 n` bytes) and `scratch`
(2048 bytes, whose contents on exit are unspecified). The writable buffers
may not overlap each other, `schedule`, the arguments or the return address;
nothing may wrap around the end of the (32-bit) address space. `rounds` is
10, 12 or 14. `esp` and the arguments are public; the key schedule and the
data are secret. -/
def blocksX86 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 2048⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 2048 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      (Spec.Aes.statesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat).map
        (f (arg s 1).toNat (Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1))))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Aes

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.X86.Wp (wp_mov wp_ldm wp_stm wp_test)

section
variable (s : State)

abbrev bSchP : BitVec 32 := arg s 0
abbrev bRounds : Nat := (arg s 1).toNat
abbrev bDatP : BitVec 32 := arg s 2
abbrev bN : Nat := (arg s 3).toNat
abbrev bScrP : BitVec 32 := arg s 4
abbrev bSchR : Region := reg32 (bSchP s) 240
abbrev bDatR : Region := reg32 (bDatP s) (16 * bN s)
abbrev bScrR : Region := reg32 (bScrP s) 2048
abbrev bArgR : Region := ⟨argAddr s 0, 20⟩
abbrev bRetR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

end

/-- `blocksX86.pre`, by name. -/
structure BPre (s : State) : Prop where
  rd : s.rd = [bSchR s, bArgR s]
  wr : s.wr = [bDatR s, bScrR s]
  dSD : (bSchR s).Disjoint (bDatR s)
  dSB : (bSchR s).Disjoint (bScrR s)
  dDB : (bDatR s).Disjoint (bScrR s)
  aD : (bArgR s).Disjoint (bDatR s)
  aB : (bArgR s).Disjoint (bScrR s)
  rD : (bRetR s).Disjoint (bDatR s)
  rB : (bRetR s).Disjoint (bScrR s)
  fS : (bSchP s).toNat + 240 ≤ 2 ^ 32
  fD : (bDatP s).toNat + 16 * bN s ≤ 2 ^ 32
  fB : (bScrP s).toNat + 2048 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  rounds : bRounds s = 10 ∨ bRounds s = 12 ∨ bRounds s = 14

theorem BPre.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State}
    (h : (Proof.Aes.blocksX86 f).pre s) : BPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-! ## The prologue -/

/-- After the prologue. -/
structure BP1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  edi : s.gpr .edi = bScrP s₀
  esi : s.gpr .esi = arg s₀ 1
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr (bScrP s₀) 256, 16⟩] s₀.mem s.mem
  saved : ∀ p ∈ savedRegs, s.mem.readW (addr (bScrP s₀) p.2) 32 = s₀.gpr p.1

theorem bPrologue_eq : saveRegs 4 ++ keySetup = ([
    .mov .eax (.mem (at_ .esp 20)), .store (at_ .eax 256) .ebx, .store (at_ .eax 260) .esi,
    .store (at_ .eax 264) .edi, .store (at_ .eax 268) .ebp, .mov .edi (.reg .eax),
    .mov .esi (.mem (at_ .esp 8))] : List Instr) := rfl

theorem bPrologue_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block (saveRegs 4 ++ keySetup)) s₀ (BP1 s₀) := by
  have fB := hp.fB; have fSp := hp.fSp
  let B := bScrP s₀
  let E := s₀.gpr .esp
  have hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hrA : bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have argC : ∀ i < 5, (bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨bArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  have bIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  have cB : ∀ o, 256 ≤ o → o + 4 ≤ 272 → (⟨addr B 256, 16⟩ : Region).Contains (addr B o) (32 / 8) :=
    fun o h1 h2 => part_contains fB (by omega) h1 (by omega) (by decide)
  have hmB : (⟨addr B 256, 16⟩ : Region) ∈ [⟨addr B 256, 16⟩] := List.mem_singleton_self _
  rw [bPrologue_eq]
  refine wp_ldm (B := E) (o := 20) rfl (argIn _ rfl 4 (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = B := by rw [u₁.gpr]; rfl
  refine wp_stm e₁ (bIn _ u₁.wr 256 (by omega)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (bIn _ (by rw [u₂.wr, u₁.wr]) 260 (by omega)) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁) (bIn _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 264 (by omega))
    fun s₄ u₄ => ?_
  refine wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁)
    (bIn _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 268 (by omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  have g₆ : ∀ r, r ≠ .eax → r ≠ .edi → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₆.other r h2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h1]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  let M₄ := (((s₀.mem.writeW (addr B 256) (s₀.gpr .ebx)).writeW (addr B 260) (s₀.gpr .esi)).writeW
    (addr B 264) (s₀.gpr .edi)).writeW (addr B 268) (s₀.gpr .ebp)
  have m₆ : s₆.mem = M₄ := by
    simp only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr]
    rw [u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.mem]
  have f₆ : Frame [⟨addr B 256, 16⟩] s₀.mem s₆.mem := by
    rw [m₆]
    exact ((((Frame.refl _ _).writeW hmB _ (cB 256 (by omega) (by omega))).writeW hmB _
      (cB 260 (by omega) (by omega))).writeW hmB _ (cB 264 (by omega) (by omega))).writeW hmB _
      (cB 268 (by omega) (by omega))
  have esp₆ : s₆.gpr .esp = E := g₆ _ (by decide) (by decide)
  refine wp_ldm (B := E) (o := 8) esp₆ (argIn _ rd₆ 1 (by omega)) fun s₇ u₇ => WP.block_nil ?_
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  refine ⟨by rw [u₇.other _ (by decide)]; exact esp₆, ?_, ?_, by rw [u₇.rd, rd₆],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₇.mem]; exact f₆, fun p hp' => ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁
  · rw [u₇.gpr, arg_eq]
    exact f₆.readW (argC 1 (by omega)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.aB.sub_right (part_sub_reg fB (by omega))) (by decide)
  · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> rw [u₇.mem, m₆] <;>
      simp (disch := decide) only [M₄, B, rd_wr_ne fB', Mem.readW_writeW_self32]

/-! ## Between the loops -/

theorem blocksSetup_ok {s : State} {B E : BitVec 32} (hb : s.gpr .edi = B) (he : s.gpr .esp = E)
    (hfit : B.toNat + 2048 ≤ 2 ^ 32) (hw : reg32 B 2048 ∈ s.wr)
    (hin : ∀ i, i = 2 ∨ i = 3 → InRegions (s.rd ++ s.wr) (addr E (4 + 4 * i)) 4)
    (hsep : ∀ i, i = 2 ∨ i = 3 → Region.Disjoint ⟨addr E (4 + 4 * i), 4⟩ (reg32 B 2048))
    {P : State → Prop}
    (h : ∀ s', s'.gpr .edi = B → s'.gpr .esp = E → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.mem.readW (addr B dOff) 32 = s.mem.readW (addr E 12) 32 →
      s'.mem.readW (addr B nOff) 32 = s.mem.readW (addr E 16) 32 →
      s'.zf = some (s.mem.readW (addr E 16) 32 == 0) → Frame [⟨addr B dOff, 8⟩] s.mem s'.mem →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block blocksSetup) s P := by
  have hin' : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hw hfit ho (by decide)
  have hm : (⟨addr B dOff, 8⟩ : Region) ∈ [⟨addr B dOff, 8⟩] := List.mem_singleton_self _
  refine wp_ldm (B := E) (o := 12) he (hin 2 (.inl rfl)) fun s₁ u₁ => ?_
  refine wp_stm (B := B) (o := dOff) (by rw [u₁.other _ (by decide)]; exact hb) (hin' _ u₁.wr _ (by decide))
    fun s₂ u₂ => ?_
  have f₂ : Frame [⟨addr B dOff, 8⟩] s.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW hm _ (part_contains hfit (by decide) (by decide) (by decide) (by decide))
  refine wp_ldm (B := E) (o := 16) (by rw [u₂.gpr, u₁.other _ (by decide)]; exact he)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 3 (.inr rfl)) fun s₃ u₃ => ?_
  refine wp_stm (B := B) (o := nOff) (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hb)
    (hin' _ (by rw [u₃.wr, u₂.wr, u₁.wr]) _ (by decide)) fun s₄ u₄ => wp_test fun s₅ u₅ hz => WP.block_nil ?_
  have v₃ : s₃.gpr .eax = s.mem.readW (addr E 16) 32 := by
    rw [u₃.gpr]
    exact f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hsep 3 (.inr rfl)).sub_right (part_sub_reg hfit (by decide))) (by decide)
  refine h s₅ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hb
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact he
  · rw [u₅.gpr, u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem,
      rd_wr_ne hfit _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [u₅.mem, u₄.mem, Mem.readW_writeW_self32, v₃]
  · rw [hz, u₄.gpr, v₃, BitVec.and_self]
  · rw [u₅.mem, u₄.mem, u₃.mem]
    exact f₂.writeW hm _ (part_contains hfit (by decide) (by decide) (by decide) (by decide))

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_left (show 16 * j + t < 16 * n by omega),
    show (16 * j + t) / 16 = j by omega, show (16 * j + t) % 16 = t by omega, getD_eq _ ht]

/-! ## The whole function -/

theorem correct_blocks {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {s₀ : State} (hp : BPre s₀) :
    WP isa (blocks crypt2) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 f).post s₀ s' := by
  have fB := hp.fB; have fD := hp.fD; have fS := hp.fS; have fSp := hp.fSp
  have hR : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  let B := bScrP s₀
  let D := bDatP s₀
  let S := bSchP s₀
  let E := s₀.gpr .esp
  let R := bRounds s₀
  let n := bN s₀
  let w := Spec.Aes.bytesAt s₀.mem (S.setWidth 64) (16 * (R + 1))
  have fS' : S.toNat + 240 ≤ 2 ^ 32 := fS
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  have fD' : D.toNat + 16 * n ≤ 2 ^ 32 := fD
  have fE' : E.toNat + 24 ≤ 2 ^ 32 := fSp
  have hR' : R ≤ 14 := hR
  have hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hwD : reg32 D (16 * n) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self ..
  have hrS : reg32 S 240 ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_self ..
  have hrA : bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have argC : ∀ i < 5, (bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨bArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  have argSub : ∀ i < 5, Region.Sub ⟨addr E (4 + 4 * i), 4⟩ (bArgR s₀) := fun i hi =>
    part_sub (N := 24) (b := E) fSp (by omega) (by omega) (by omega)
  -- The prologue.
  unfold blocks
  refine WP.seq (WP.mono (bPrologue_ok hp) fun s₁ h₁ => ?_)
  have F₁ := h₁.frame
  have d₁ : ∀ {r : Region}, r.Disjoint (bScrR s₀) → ∀ r' ∈ [(⟨addr B 256, 16⟩ : Region)], r.Disjoint r' := by
    intro r h1 r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    exact h1.sub_right (part_sub_reg fB (by omega))
  have arg₁ : ∀ i < 5, s₁.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    F₁.readW (argC i hi) (d₁ hp.aB) (by decide)
  have sched₁ : ∀ i < 240, s₁.mem (addr S i) = s₀.mem (addr S i) := fun i hi =>
    frame_one F₁ (reg_contains fS (by omega) (by decide)) (d₁ hp.dSB)
  have hk : KSetup s₁ B S R w :=
    { scr := by rw [h₁.wr]; exact hwB
      fitB := fB
      sch := by rw [h₁.rd]; exact List.mem_append_left _ hrS
      fitS := fS
      sep := hp.dSB
      rounds := hp.rounds
      base := h₁.edi
      argIn := fun i hi => by rw [h₁.esp]; exact argIn _ h₁.rd i (by omega)
      arg0 := by rw [h₁.esp]; exact arg₁ 0 (by omega)
      arg1 := by rw [h₁.esp, arg₁ 1 (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := fun i hi => by rw [h₁.esp]; exact hp.aB.sub_left (argSub i (by omega))
      w := fun i hi => by
        rw [sched₁ i (by omega)]
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        rw [addr_eq (by have := fS'; omega)] }
  have hi₁ : KInv s₁ B R w R s₁ :=
    { hj := Nat.le_refl _
      esi := by rw [h₁.esi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rd := rfl
      wr := rfl
      keep := fun _ _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₁) fun s₂ d₂ => ?_)
  have edi₂ : s₂.gpr .edi = B := (d₂.keep _ (by decide) (by decide)).trans h₁.edi
  have esp₂ : s₂.gpr .esp = E := (d₂.keep _ (by decide) (by decide)).trans h₁.esp
  have kfSub := hk.frame_sub
  have d₂' : ∀ {r : Region}, r.Disjoint (bScrR s₀) → ∀ r' ∈ keyFrame B, r.Disjoint r' :=
    fun h r' hr' => h.sub_right (kfSub r' hr')
  have arg₂ : ∀ i < 5, s₂.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [← arg₁ i hi]; exact d₂.frame.readW (argC i hi) (d₂' hp.aB) (by decide)
  -- Between the loops.
  refine WP.seq (blocksSetup_ok edi₂ esp₂ fB' (by rw [d₂.wr, h₁.wr]; exact hwB)
    (fun i hi => argIn _ (by rw [d₂.rd, h₁.rd]) i (by omega))
    (fun i hi => hp.aB.sub_left (argSub i (by omega)))
    fun s₃ edi₃ esp₃ g₃ ds₃ ns₃ z₃ F₃ rd₃ wr₃ => ?_)
  have d₃ : ∀ {r : Region}, r.Disjoint (bScrR s₀) → ∀ r' ∈ [(⟨addr B dOff, 8⟩ : Region)], r.Disjoint r' :=
    fun h r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact h.sub_right (part_sub_reg fB (by decide))
  have arg₃ : ∀ i < 5, s₃.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [← arg₂ i hi]; exact F₃.readW (argC i hi) (d₃ hp.aB) (by decide)
  have e16 : s₂.mem.readW (addr E 16) 32 = arg s₀ 3 := arg₂ 3 (by omega)
  have hs : ESetup s₃ B D n R w :=
    { scr := by rw [wr₃, d₂.wr, h₁.wr]; exact hwB
      fitB := fB
      dat := by rw [wr₃, d₂.wr, h₁.wr]; exact hwD
      fitD := fD
      sep := hp.dDB
      rounds := hp.rounds
      argIn := by rw [esp₃]; exact argIn _ (by rw [rd₃, d₂.rd, h₁.rd]) 1 (by omega)
      argR := by rw [esp₃, arg₃ 1 (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := by rw [esp₃]; exact hp.aB.sub_left (argSub 1 (by omega))
      argSepD := by rw [esp₃]; exact hp.aD.sub_left (argSub 1 (by omega))
      keys := fun j hj => by
        refine keyRel_congr (d₂.keys j hj) fun k hk => ?_
        have := keyOff_le (j := j) hR'
        exact F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact part_disj fB (by simp only [lastKey] at this; omega) (by decide)
            (.inr (by simp only [dOff, lastKey] at this ⊢; omega))) (by decide) }
  -- The memory the prologue, the key loop and the setup of the groups wrote.
  have G₃ : Frame [bScrR s₀] s₀.mem s₃.mem := by
    refine (F₁.sub fun r hr => ?_).trans ((d₂.frame.sub fun r hr => ?_).trans (F₃.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨bScrR s₀, by simp, part_sub_reg fB (by omega)⟩
    · exact ⟨bScrR s₀, by simp, kfSub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨bScrR s₀, by simp, part_sub_reg fB (by decide)⟩
  have dD : ∀ r ∈ [bScrR s₀], (bDatR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.dDB
  have hn64 : 16 * n < 2 ^ 64 := by omega
  have data₃ : EcbInv s₀.mem s₃.mem (D.setWidth 64) n 0
      (ecbOut f s₀.mem (D.setWidth 64) R w) := fun i hi => by
    rw [ite_eq_right (show ¬ i < 16 * 0 by omega)]
    exact G₃.bytes (R := bDatR s₀) dD (by show 16 * n ≤ 2 ^ 64; omega) hi
  -- The groups.
  refine WP.seq (WP.mono (Q := EDone f s₀.mem s₃ B D n R w) ?_ fun s₄ h₄ => ?_)
  · refine WP.ite (arg s₀ 3 == 0) (by simp only [X86.eval, z₃, e16]) (fun hb => ?_) (fun hb => ?_)
    · have hn0 : n = 0 := by
        have : arg s₀ 3 = 0 := by simpa using hb
        show (arg s₀ 3).toNat = 0; rw [this]; rfl
      exact WP.block_nil ⟨edi₃, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
    · have hn0 : 0 < n := by
        have : arg s₀ 3 ≠ 0 := by simpa using hb
        show 0 < (arg s₀ 3).toNat
        exact Nat.pos_of_ne_zero fun h => this (BitVec.eq_of_toNat_eq (by simpa using h))
      refine ecbGroups_ok hs hcr ⟨by omega, edi₃, rfl, rfl, rfl, Frame.refl _ _, ?_, ?_, data₃⟩
      · rw [ds₃, arg₂ 2 (by omega)]; simp; rfl
      · rw [ns₃, e16, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · -- The epilogue.
    have G₄ : Frame [bScrR s₀, bDatR s₀] s₀.mem s₄.mem := by
      refine (G₃.mono (by simp)).trans (h₄.frame.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨bScrR s₀, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨bScrR s₀, by simp, part_sub_reg fB (by decide)⟩
      · exact ⟨bDatR s₀, by simp, fun _ h => h⟩
    have retD : ∀ r ∈ [bScrR s₀, bDatR s₀], (bRetR s₀).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.rB
      · exact hp.rD
    -- The saved registers.
    have saved : Spill.Saved s₄.mem (addr B) s₀.gpr savedRegs := fun p hp' => by
      have ho : 256 ≤ p.2 ∧ p.2 + 4 ≤ 272 := by revert p hp'; decide
      rw [← h₁.saved p hp']
      have e₄ : s₄.mem.readW (addr B p.2) 32 = s₃.mem.readW (addr B p.2) 32 :=
        h₄.frame.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
            rw [← addr_zero]; exact part_disj fB (by omega) (by omega) (.inr (by omega))
          · exact part_disj fB (by omega) (by decide) (.inl (by simp only [dOff]; omega))
          · exact (hp.dDB.sub_right (part_sub_reg fB (by omega))).symm) (by decide)
      rw [e₄, F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact part_disj fB (by omega) (by decide) (.inl (by simp only [dOff]; omega))) (by decide)]
      exact d₂.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
          rw [← addr_zero]; exact part_disj fB (by omega) (by omega) (.inr (by omega))
        · exact part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
    have esp₄ : s₄.gpr .esp = E := h₄.esp.trans esp₃
    refine WP.mono (restore_ok h₄.base fB' (by rw [h₄.wr, wr₃, d₂.wr, h₁.wr]; exact hwB) saved)
      fun s₅ r₅ => ?_
    refine ⟨⟨r₅.abi (by decide) (by decide) esp₄, ?_⟩, ?_⟩
    · rw [r₅.mem]
      exact G₄.readW (Region.contains_self _ _) retD (by decide)
    · show Spec.Aes.statesAt s₅.mem (D.setWidth 64) n = _
      rw [r₅.mem, statesAt_of_ecbInv h₄.data]
      simp only [Spec.Aes.statesAt, List.map_map]
      rfl

theorem blocks_correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) (s : State) (hs : (Proof.Aes.blocksX86 f).pre s) :
    ∃ t s', Exec isa (blocks crypt2) s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s' :=
  (correct_blocks hcr (BPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.cipher).post s s' :=
  blocks_correct encrypt2_cryptOk s hs

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s s' :=
  blocks_correct decrypt2_cryptOk s hs

end VG.Proof.Aes.X86
