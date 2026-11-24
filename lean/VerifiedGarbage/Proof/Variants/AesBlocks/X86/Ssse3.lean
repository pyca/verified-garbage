module

public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Proof.Aes.X86.Vperm
import VerifiedGarbage.Proof.Aes.X86.Vperm.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
meta import VerifiedGarbage.Proof.Aes.X86.Vperm
meta import VerifiedGarbage.Proof.Aes.X86.Vperm.Lit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `AesBlocks` on x86 (32-bit): vector permutations (SSSE3)

`vg_aes_encrypt_blocks_ssse3` and `vg_aes_decrypt_blocks_ssse3`
(`Impl/Aes/X86/Vperm.lean`), a block at a time: after `c` blocks, the first
`c` data blocks hold the cipher of the original ones (`BInv`).
-/

@[expose] public section

namespace VG.Proof.Variants.AesBlocks.X86.Ssse3

open VG VG.X86
open VG.Impl.Aes.X86.Vperm
open VG.Impl.Aes.X86.AesNi (at_ argOp)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 addr_zero addr_add in_rd
  in_reg part_sub_reg reg_contains part_contains part_sub part_disj blocksτ₀ blocks_agree₀)
open VG.Proof.Aes.X86.Vperm
open VG.Proof.Aes.Vector (st)

section
variable (s₀ : State)

/-- Block `k` of the data. -/
abbrev bAddr (k : Nat) : Addr := (bDatP s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem ((bSchP s₀).setWidth 64) (16 * (bRounds s₀ + 1))

end

theorem stateAt_eq (m : Mem) (p : Addr) : Spec.Aes.stateAt m p = st (m.readW p 128) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, st, Vector.getElem_ofFn]
  exact (VG.Proof.Aes.Vector.vbyte_readW m p hi).symm

theorem args_of {s₀ : State} (hp : BPre s₀) : Args 4 2048 (bScrP s₀) s₀ where
  fit := hp.fB
  scr := by rw [hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  argIn := ⟨bArgR s₀, by rw [hp.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self),
    part_contains (N := 24) (by have := hp.fSp; omega_using [this]) (by decide) (by decide) (by decide) (by decide)⟩
  arg := rfl

theorem argC {s₀ : State} (hp : BPre s₀) {i : Nat} (hi : i < 5) :
    (bArgR s₀).Contains (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  part_contains (N := 24) (a := 4) (by have := hp.fSp; omega_using [this]) (by decide) (by omega_using [])
    (by omega_using [hi]) (by decide)

theorem argSub {s₀ : State} (hp : BPre s₀) {i : Nat} (hi : i < 5) :
    Region.Sub ⟨addr (s₀.gpr .esp) (4 + 4 * i), 4⟩ (bArgR s₀) :=
  part_sub (N := 24) (c := 4) (by have := hp.fSp; omega_using [this]) (by decide) (by omega_using [])
    (by omega_using [hi])

theorem sched_of {s₀ : State} (hp : BPre s₀) :
    Sched 2048 (bScrP s₀) (bSchP s₀) (bRounds s₀) (sch s₀) s₀ where
  fit := hp.fS
  sch := by rw [hp.rd]; exact List.mem_append_left _ List.mem_cons_self
  sep := hp.dSB
  argIn := fun i hi => ⟨bArgR s₀, by rw [hp.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self),
    argC hp (by omega_using [hi])⟩
  argSep := fun i hi => hp.aB.sub_left (argSub hp (by omega_using [hi]))
  arg0 := rfl
  arg1 := by
    show arg s₀ 1 = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rounds := hp.rounds
  key := fun j hj => by
    have hR : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_using [h]
    rw [addr_eq (by have := hp.fS; omega_using [hj, hR, this])]
    exact VG.Proof.Aes.Vector.keyIs_readW _ _ (by omega_using [hj])

section
variable {d : Dir} {all : List (BitVec 128)} {F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State}

/-- After `c` blocks. -/
structure BInv (d : Dir) (all : List (BitVec 128)) (F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State)
    (sk : Nat → BitVec 128) (s₀ : State) (c : Nat) (s : State) : Prop where
  core : CoreIn d all 2048 (bScrP s₀) (bRounds s₀) sk s
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Spill.Saved s.mem (addr (bScrP s₀)) s₀.gpr d.savedRegs
  frame : Frame [bDatR s₀, reg32 (bScrP s₀) (d.saved + 16)] s₀.mem s.mem
  esi : s.gpr .esi = bDatP s₀ + BitVec.ofNat 32 (16 * c)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (bN s₀ - c)
  le : c ≤ bN s₀
  blocks : ∀ k < bN s₀, Spec.Aes.stateAt s.mem (bAddr s₀ k) =
    if k < c then F (bRounds s₀) (sch s₀) (Spec.Aes.stateAt s₀.mem (bAddr s₀ k))
    else Spec.Aes.stateAt s₀.mem (bAddr s₀ k)

/-- The setup, the slots and the data's arguments. -/
theorem start_ok (hd : CryptOk d all F) (hp : BPre s₀) :
    WP isa (.block (d.setup 4)) s₀ fun s₁ => WP isa d.prep s₁ fun s₂ =>
      ∃ sk : Nat → BitVec 128, (∀ {s : State}, CoreIn d all 2048 (bScrP s₀) (bRounds s₀) sk s →
        WP isa d.core s fun s' => Kept s s' ∧ st (s'.xmm .xmm0) = F (bRounds s₀) (sch s₀) (st (s.xmm .xmm0))) ∧
      WP isa (.block Dir.dataArgs) s₂ fun s₃ => BInv d all F sk s₀ 0 s₃ ∧ s₃.zf = some (decide (bN s₀ = 0)) := by
  have hN : d.saved + 16 ≤ 2048 := by
    have h := hd.setup.le
    have e : d.saved = d.slots + 240 := rfl
    omega_using [h, e]
  have hscr : reg32 (bScrP s₀) 2048 ∈ s₀.wr := (args_of hp).scr
  obtain ⟨sk, hprep, hcore⟩ := hd.prep hp.fB hN hscr (sched_of hp)
  refine WP.mono (setup_ok hd.setup (args_of hp) hN) fun s₁ ⟨h₁, h6, h7⟩ => ?_
  refine WP.mono (hprep h₁ h6 h7) fun s₂ ⟨h₂, c₂⟩ => ⟨sk, hcore, ?_⟩
  have harg : ∀ {t : State} {i : Nat}, t.mem = s₂.mem → t.rd = s₂.rd → t.wr = s₂.wr → i < 5 →
      InRegions (t.rd ++ t.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
        t.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i := fun hm hr hw hi => by
    refine ⟨⟨bArgR s₀, ?_, argC hp hi⟩, ?_⟩
    · rw [hr, h₂.rd, hp.rd]
      exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [hm]
      refine (h₂.sub hN).readW (argC hp hi) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.aB
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s₂.mem ∧ s'.rd = s₂.rd ∧ s'.wr = s₂.wr ∧ s'.gpr .edi = s₂.gpr .edi ∧
    s'.gpr .esp = s₂.gpr .esp ∧ s'.gpr .esi = bDatP s₀ ∧ s'.gpr .ebp = arg s₀ 3 ∧
    s'.zf = some (arg s₀ 3 &&& arg s₀ 3 == 0)) rfl ?_) fun s' hh => ?_
  · obtain ⟨i2, a2⟩ := harg (t := s₂) (i := 2) rfl rfl rfl (by decide)
    refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 2) h₂.esp i2 fun t₁ u₁ => ?_
    obtain ⟨i3, a3⟩ := harg (t := t₁) (i := 3) u₁.mem u₁.rd u₁.wr (by decide)
    refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 3) ((u₁.other _ (by decide)).trans h₂.esp) i3 fun t₂ u₂ => ?_
    refine Wp.wp_test fun t₃ u₃ z => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]
    · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr]; exact a2
    · rw [u₃.gpr, u₂.gpr]; exact a3
    · rw [z, u₂.gpr]; exact congrArg (fun x => some (x &&& x == 0)) a3
  · obtain ⟨⟨m, rd, wr, e, p, si, bp, z⟩, x⟩ := hh
    have hl := hd.setup.len
    have hn : bN s₀ < 2 ^ 32 := (arg s₀ 3).isLt
    refine ⟨⟨c₂.of_frame (rs := []) e p rd wr (congrFun x _) (congrFun x _) (by rw [m]; exact Frame.refl _ _) hl
      (fun _ _ _ h => nomatch h) (fun _ h => nomatch h), p.trans h₂.esp, rd.trans h₂.rd, wr.trans h₂.wr,
      by rw [m]; exact h₂.saved, ?_, by rw [si]; exact (BitVec.add_zero _).symm, ?_, Nat.zero_le _, fun k hk => ?_⟩, ?_⟩
    · rw [m]
      exact h₂.frame.mono fun r hr => List.mem_cons_of_mem _ hr
    · rw [bp, Nat.sub_zero, bN, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [ite_eq_right (Nat.not_lt_zero k), m, stateAt_eq, stateAt_eq]
      refine congrArg st ((h₂.sub hN).readW (r := ⟨bAddr s₀ k, 16⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide))
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.dDB.sub_left (Offset.sub_base _ (by omega_using [hk]))
    · rw [z, BitVec.and_self]
      refine congrArg some ?_
      rw [show arg s₀ 3 = BitVec.ofNat 32 (bN s₀) by rw [bN, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        Wp.ofNat_beq_zero hn]

/-- One block. -/
theorem body_ok (hd : CryptOk d all F) (hp : BPre s₀) {sk : Nat → BitVec 128}
    (hcore : ∀ {s : State}, CoreIn d all 2048 (bScrP s₀) (bRounds s₀) sk s →
      WP isa d.core s fun s' => Kept s s' ∧ st (s'.xmm .xmm0) = F (bRounds s₀) (sch s₀) (st (s.xmm .xmm0)))
    {c : Nat} (hc : c < bN s₀) {s : State} (h : BInv d all F sk s₀ c s) :
    WP isa d.body s fun s' => BInv d all F sk s₀ (c + 1) s' ∧ s'.zf = some (decide (bN s₀ = c + 1)) := by
  have fD := hp.fD
  have fB := hp.fB
  have hsl := hd.setup.le
  have hl := hd.setup.len
  have hsv : d.saved = d.slots + 240 := rfl
  have he : addr (s.gpr .esi) 0 = bAddr s₀ c := by
    rw [h.esi, addr_add, Nat.add_zero, addr_eq (by omega_using [fD, hc])]
  have hwr : bDatR s₀ ∈ s.wr := by rw [h.wr, hp.wr]; exact List.mem_cons_self
  have hcon : (bDatR s₀).Contains (bAddr s₀ c) 16 := Offset.contains_base _ (by omega_using [hc]) (by omega_using [fD, hc])
  refine WP.seq (WP.mono (Q := fun s₁ => s₁ = setX s (put s.xmm .xmm0 (s.mem.readW (bAddr s₀ c) 128))) ?_ fun s₁ e₁ => ?_)
  · refine wp_x (is := [.movdquLoad .xmm0 (at_ .esi 0)]) (rest := []) rfl (fun m hm => ?_) (WP.block_nil ?_)
    · simp only [List.filterMap_cons, xmemOp, List.filterMap_nil, List.mem_singleton] at hm
      subst hm
      rw [at_, ea_mk, he]
      exact in_rd ⟨_, hwr, hcon⟩
    · rw [xvals, xvals, xval, at_, ea_mk, he]
  have hk₁ : Kept s s₁ := by
    rw [e₁]
    exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by rw [setX_xmm, put_ne _ _ (by decide)], by rw [setX_xmm, put_ne _ _ (by decide)]⟩
  refine WP.seq (WP.mono (hcore (h.core.of_kept hk₁)) fun s₂ ⟨k₂, x₂⟩ => ?_)
  have k := hk₁.trans k₂
  have x₂' : st (s₂.xmm .xmm0) = F (bRounds s₀) (sch s₀) (Spec.Aes.stateAt s₀.mem (bAddr s₀ c)) := by
    have hb := h.blocks c hc
    rw [ite_eq_right (Nat.lt_irrefl c), stateAt_eq] at hb
    rw [x₂, e₁, setX_xmm, put_self, hb]
  have he₂ : addr (s₂.gpr .esi) 0 = bAddr s₀ c := by rw [k.gpr _ (by decide) (by decide), he]
  refine WP.block_cons_iff.mpr ⟨{ s₂ with mem := s₂.mem.writeW (bAddr s₀ c) (s₂.xmm .xmm0) }, ?_, ?_⟩
  · show s₂.store128 (s₂.ea ⟨.esi, 0⟩) (s₂.xmm .xmm0) = _
    rw [ea_mk, he₂]
    exact ite_eq_left ⟨_, by rw [k.wr]; exact hwr, hcon⟩
  generalize hs₃ : ({ s₂ with mem := s₂.mem.writeW (bAddr s₀ c) (s₂.xmm .xmm0) } : State) = s₃
  have hm₃ : s₃.mem = s₂.mem.writeW (bAddr s₀ c) (s₂.xmm .xmm0) := by rw [← hs₃]
  have hg₃ : s₃.gpr = s₂.gpr := by rw [← hs₃]
  have hrd₃ : s₃.rd = s₂.rd := by rw [← hs₃]
  have hwr₃ : s₃.wr = s₂.wr := by rw [← hs₃]
  have hx₃ : s₃.xmm = s₂.xmm := by rw [← hs₃]
  have hfr : Frame [⟨bAddr s₀ c, 16⟩] s.mem s₃.mem := by
    rw [hm₃, k.mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have hsub : Region.Sub ⟨bAddr s₀ c, 16⟩ (bDatR s₀) := Offset.sub_base _ (by omega_using [hc])
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s₃.mem ∧ s'.rd = s₃.rd ∧ s'.wr = s₃.wr ∧ s'.gpr .edi = s₃.gpr .edi ∧
    s'.gpr .esp = s₃.gpr .esp ∧ s'.gpr .esi = s₃.gpr .esi + 16 ∧ s'.gpr .ebp = s₃.gpr .ebp - 1 ∧
    s'.zf = some (s₃.gpr .ebp - 1 == 0)) rfl ?_) fun s' hh => ?_
  · refine Wp.wp_addi fun t₁ u₁ => Wp.wp_subi fun t₂ u₂ _ z => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₂.mem, u₁.mem]
    · rw [u₂.rd, u₁.rd]
    · rw [u₂.wr, u₁.wr]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₂.other _ (by decide), u₁.gpr]
    · rw [u₂.gpr, u₁.other _ (by decide)]
    · rw [z, u₁.other _ (by decide)]
  · obtain ⟨⟨m, rd, wr, e, p, si, bp, z⟩, x⟩ := hh
    have hf' : Frame [⟨bAddr s₀ c, 16⟩] s.mem s'.mem := by rw [m]; exact hfr
    have gi : ∀ r, r ≠ .ebx → r ≠ .ecx → s₃.gpr r = s.gpr r := fun r h1 h2 => by rw [hg₃, k.gpr r h1 h2]
    have ebp' : s.gpr .ebp - 1 = BitVec.ofNat 32 (bN s₀ - (c + 1)) := by
      rw [h.ebp, Wp.ofNat_pred (by omega_using [hc])]; congr 1
    have hdB : ∀ o n, o + n ≤ 2048 → Region.Disjoint ⟨addr (bScrP s₀) o, n⟩ ⟨bAddr s₀ c, 16⟩ := fun o n hon =>
      ((hp.dDB.sub_left hsub).sub_right (part_sub_reg fB hon)).symm
    refine ⟨⟨h.core.of_frame (rs := [⟨bAddr s₀ c, 16⟩]) (by rw [e, gi _ (by decide) (by decide)])
      (by rw [p, gi _ (by decide) (by decide)]) (by rw [rd, hrd₃, k.rd]) (by rw [wr, hwr₃, k.wr])
      (by rw [x, hx₃, k.x6]) (by rw [x, hx₃, k.x7]) hf' hl (fun o ho r hr => ?_) (fun r hr => ?_),
      by rw [p, gi _ (by decide) (by decide), h.esp], by rw [rd, hrd₃, k.rd, h.rd], by rw [wr, hwr₃, k.wr, h.wr],
      ?_, ?_, ?_, ?_, hc, ?_⟩, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact hdB _ _ (by omega_using [ho, hsl])
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.esp]
      exact (hp.aD.sub_left (argSub hp (i := 1) (by decide))).sub_right hsub
    · refine h.saved.of_frame hf' (R := ⟨addr (bScrP s₀) d.saved, 16⟩) (fun q hq => ?_) (fun r hr => ?_)
      · rcases savedRegs_mem hq with rfl | rfl | rfl | rfl <;>
          exact part_contains fB (by omega_using [hsl, hsv]) (by omega_using []) (by omega_using []) (by decide)
      · simp only [List.mem_singleton] at hr; subst hr
        exact hdB _ _ (by omega_using [hsl, hsv])
    · exact h.frame.trans (hf'.sub fun r hr => ⟨bDatR s₀, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩)
    · rw [si, gi _ (by decide) (by decide), h.esi, BitVec.add_assoc]
      exact congrArg _ ((BitVec.ofNat_add _ _).symm.trans (congrArg _ (by omega_using [])))
    · rw [bp, gi _ (by decide) (by decide), ebp']
    · intro j hj
      by_cases ej : j = c
      · subst ej
        rw [ite_eq_left (Nat.lt_succ_self j), stateAt_eq, m, hm₃, Mem.readW_writeW_self _ _ 16 _ (by decide), x₂']
      · rw [stateAt_eq, hf'.readW (r := ⟨bAddr s₀ j, 16⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide),
          ← stateAt_eq, h.blocks j hj]
        · by_cases hjc : j < c
          · rw [ite_eq_left hjc, ite_eq_left (by omega_using [hjc])]
          · rw [ite_eq_right hjc, ite_eq_right (by omega_using [hjc, ej])]
        · simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_using [ej]) (by omega_using [fD, hj]) (by omega_using [fD, hc])
    · rw [z, gi _ (by decide) (by decide), ebp', Wp.ofNat_beq_zero (by omega_using [fD])]
      exact congrArg some (decide_eq_decide.mpr (by omega_using [hc]))

/-- The functions of whole blocks. -/
theorem blocks_ok (hd : CryptOk d all F) (hk : d.keep = true) (hp : BPre s₀) :
    WP isa d.blocks s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 F).post s₀ s' ∧
      Frame [bDatR s₀, reg32 (bScrP s₀) (d.saved + 16)] s₀.mem s'.mem := by
  have hsl := hd.setup.le
  have hsv : d.saved = d.slots + 240 := rfl
  have hN : d.saved + 16 ≤ 2048 := by omega_using [hsl, hsv]
  refine WP.seq (WP.mono (start_ok hd hp) fun s₁ w₁ => WP.seq (WP.mono w₁ fun s₂ ⟨sk, hcore, w₂⟩ =>
    WP.seq (WP.mono w₂ fun s₃ ⟨h₃, z₃⟩ => ?_)))
  refine WP.seq (WP.mono (Q := BInv d all F sk s₀ (bN s₀)) ?_ fun s₄ h₄ => ?_)
  · refine WP.ite (decide (bN s₀ = 0)) (by simp [eval, z₃]) (fun e => ?_) (fun e => ?_)
    · rw [of_decide_eq_true e]; exact WP.block_nil h₃
    · have e0 : bN s₀ ≠ 0 := of_decide_eq_false e
      refine WP.loop (M := isa) (fun n s' => ∃ c, n = bN s₀ - c ∧ c < bN s₀ ∧ BInv d all F sk s₀ c s')
        (fun n s' ⟨c, hn, hc, i⟩ => ?_) (bN s₀) s₃ ⟨0, rfl, by omega_using [e0], h₃⟩
      refine WP.mono (body_ok hd hp hcore hc i) fun s'' ⟨i', z⟩ => ?_
      by_cases e : bN s₀ = c + 1
      · exact .inl ⟨by simp [eval, z, e], by rw [e]; exact i'⟩
      · exact .inr ⟨by simp [eval, z, e], bN s₀ - (c + 1), by omega_using [hn, hc], c + 1, rfl,
          by omega_using [hc, e], i'⟩
  · refine WP.mono (restore_ok h₄.core.edi h₄.esp hp.fB hN (by rw [h₄.wr]; exact (args_of hp).scr) hk h₄.saved)
      fun s' ⟨m, g⟩ => ⟨⟨g, ?_⟩, ?_, by rw [m]; exact h₄.frame⟩
    · rw [m]
      refine h₄.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.rD
      · exact hp.rB.sub_right (Region.sub_prefix hN)
    · show Spec.Aes.statesAt s'.mem ((bDatP s₀).setWidth 64) (bN s₀) = _
      rw [m]
      simp only [Spec.Aes.statesAt, List.map_map]
      refine List.map_congr_left fun k hk => ?_
      obtain hk := List.mem_range.mp hk
      obtain hb := h₄.blocks k hk
      rw [ite_eq_left hk] at hb
      exact hb

/-- Beyond `W` bytes it leaves the scratch buffer as it was. -/
theorem unwritten (hd : CryptOk d all F) (hk : d.keep = true) (s : State) (hs : (Proof.Aes.blocksX86 F).pre s) (t : List Leak) (s' : State)
    (he : Exec isa d.blocks s t s') : ∀ i, d.saved + 16 ≤ i → i < 2048 →
      s'.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) := by
  obtain hp := BPre.of hs
  have fB := hp.fB
  obtain ⟨t', s'', he', -, -, hf⟩ := blocks_ok hd hk hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  intro i h1 hi
  refine hf _ fun r hr hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.dDB _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  · simp only [Region.Contains, BitVec.add_comm ((arg s 4).setWidth 64), BitVec.add_sub_cancel,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [hi])] at hc
    omega_using [h1, hc]

theorem correct (hd : CryptOk d all F) (hk : d.keep = true) (s : State) (hs : (Proof.Aes.blocksX86 F).pre s) :
    ∃ t s', Exec isa d.blocks s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 F).post s s' := by
  obtain ⟨t, s', he, ha, hq, -⟩ := blocks_ok hd hk (BPre.of hs)
  exact ⟨t, s', he, ha, hq⟩

end

theorem encrypt_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.cipher).pub encryptBlocks :=
  VG.Taint.constantTime (A := sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp) (by taint_decide)

theorem decrypt_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub decryptBlocks :=
  VG.Taint.constantTime (A := sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp) (by taint_decide)

/-- The implementation. -/
def variant : Proof.Aes.X86.BlocksImpl where
  enc := ⟨"vg_aes_encrypt_blocks_ssse3", encryptBlocks⟩
  encStack := by lit_decide
  encOk := correct Enc.cryptOk rfl
  encCt := encrypt_ct
  encNosp := NoSp.of_all (by lit_decide)
  encSpSafe := Code.all_of_spTest (by lit_decide)
  encScrub := by lit_decide
  dec := ⟨"vg_aes_decrypt_blocks_ssse3", decryptBlocks⟩
  decStack := by lit_decide
  decOk := correct Dec.cryptOk rfl
  decCt := decrypt_ct
  decNosp := NoSp.of_all (by lit_decide)
  decSpSafe := Code.all_of_spTest (by lit_decide)
  decScrub := by lit_decide
  encWritten := 480
  encWrittenLe := by decide
  encWrittenOk := unwritten Enc.cryptOk rfl
  decWritten := 720
  decWrittenLe := by decide
  decWrittenOk := unwritten Dec.cryptOk rfl
  suffix := "_ssse3"
  features := ["ssse3"]
  expand := Proof.Aes.X86.Ctr32Impl.scalar.expand
  expandStack := Proof.Aes.X86.Ctr32Impl.scalar.expandStack
  expandOk := Proof.Aes.X86.Ctr32Impl.scalar.expandOk
  expandCt := Proof.Aes.X86.Ctr32Impl.scalar.expandCt
  expandNosp := Proof.Aes.X86.Ctr32Impl.scalar.expandNosp
  expandSpSafe := Proof.Aes.X86.Ctr32Impl.scalar.expandSpSafe
  expandScrub := Proof.Aes.X86.Ctr32Impl.scalar.expandScrub

end VG.Proof.Variants.AesBlocks.X86.Ssse3
