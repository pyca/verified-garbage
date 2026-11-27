module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Cached
public import VerifiedGarbage.Impl.Ffdh.RISCV64.VettedValidation
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Ffdh.RISCV64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcMain
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Ffdh.CachedSat
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.RISCV64.ZMask
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# `vg_ffdh_generate_key_precompute` on RISC-V: correctness

The exchange's data of the precompute (`pcx`): `out` the context, x the
domain's `p_len` octets and the peer g's. `pcFront_ok`: the registers saved
and the header's words 0–3; `recog_ok`: the recognized width; `post_ok`:
`Base`; then `loadP_X`, `bound_step` and `rest_ok` (`pc_correct`).
-/

@[expose] public section

/-! # `vg_ffdh_generate_key_precompute` on RISCV64: the function

`vg_ffdh_generate_key_precompute(ctx = a0, ctx_len = a1, domain = a2,
domain_len = a3, p_len = a4, scratch = a5, scratch_len = a6)`, with the
vetted groups' table (`pcContract`), and the shared contract
(`pc_implies`). -/

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64
open VG.Impl.Ffdh.RISCV64.VettedValidation (tableSym tableConsts)

/-- The context's region. -/
abbrev pcCtx (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩

/-- The domain's region. -/
abbrev pcDomR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩

/-- The working space's region. -/
abbrev pcScr (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat * 8⟩

/-- The domain's bytes. -/
abbrev pcDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat

def pcPre (s : State) : Prop :=
  s.rd = [pcDomR s] ∧ s.wr = [pcCtx s, pcScr s] ∧ (pcCtx s).Disjoint (pcDomR s) ∧
    (pcCtx s).Disjoint (pcScr s) ∧ (pcDomR s).Disjoint (pcScr s) ∧
    (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + (s.gpr .a6).toNat * 8 ≤ 2 ^ 64 ∧
    Spec.Ffdh.pLenValid (s.gpr .a4).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .a4).toNat (s.gpr .a3).toNat ∧
    (s.gpr .a1).toNat = Spec.Ffdh.generationPrecomputedWords (s.gpr .a4).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .a4).toNat ≤ (s.gpr .a6).toNat ∧
    Spec.Ffdh.domainValid (s.gpr .a4).toNat (pcDom s) ∧ (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a5).toNat % 8 = 0

def pcPost (s t : State) : Prop :=
  (t.gpr .a0).setWidth 32 = 1 ∧
    Spec.Ffdh.generationPrecompute (s.gpr .a4).toNat (pcDom s) = some (Spec.Rsa.wordsAt t.mem (s.gpr .a0) (s.gpr .a1).toNat)

def pcPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ (pcDom s₁).map (·.toNat) = (pcDom s₂).map (·.toNat) ∧
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
    s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6

/-- `vg_ffdh_generate_key_precompute`, with the vetted groups' table. -/
def pcContract : Contract isa where
  pre s := pcPre (stripConsts tableConsts s) ∧ ConstsOk tableConsts 0 s
  post := pcPost
  pub s₁ s₂ := pcPub s₁ s₂ ∧ s₁.syms tableSym = s₂.syms tableSym

theorem pc_pre0 {s : State} (h : (Spec.Ffdh.generationPrecomputeContract RISCV64.abi).pre s) : pcPre s := by
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, RISCV64.abi, RISCV64.argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at h
  sig_split h
  sig_reduce [pcPre, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
  sig_and_intros
  sig_close
  all_goals first | with_reducible assumption | sig_disjoint_symm | omega

theorem pc_post0 {s t : State} (h : pcPost s t) : (Spec.Ffdh.generationPrecomputeContract RISCV64.abi).post s t := by
  sig_post [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, RISCV64.abi, RISCV64.argRegs,
    List.append_eq]
  sig_reduce [pcPost, pcDom] at h
  exact h

theorem pc_pub0 {s₁ s₂ : State} (h : (Spec.Ffdh.generationPrecomputeContract RISCV64.abi).pub s₁ s₂) : pcPub s₁ s₂ := by
  sig_pub [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, RISCV64.abi, RISCV64.argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at h
  exact h

/-! ## A caller meeting the contract -/

/-- The domain at `0x3000` and a table of `words` at `0x100000`. -/
private def pcSatMem (words : List (BitVec 64)) (a : Addr) : Byte :=
  if (a - 0x100000).toNat < 17744 then constMem 0x100000 words a else CachedSat.domainMem a

/-- The context at `0x200000`, the working space at `0x4000`. -/
private def pcSatState (words : List (BitVec 64)) : State where
  gpr r := match r with
    | .a0 => 0x200000 | .a1 => 275 | .a2 => 0x3000 | .a3 => 128 | .a4 => 64 | .a5 => 0x4000 | .a6 => 1056
    | _ => 0
  sp := 0x8000
  mem := pcSatMem words
  rd := [⟨0x3000, 128⟩, ⟨0x100000, 17744⟩]
  wr := [⟨0x200000, 2200⟩, ⟨0x4000, 8448⟩]
  syms _ := 0x100000

private theorem pcSat_domain (words : List (BitVec 64)) :
    Spec.Rsa.bytesAt (pcSatState words).mem 0x3000 128 = CachedSat.domain := by
  apply CachedSat.bytesAt_eq
  intro i hi
  show pcSatMem words _ = _
  unfold pcSatMem
  apply ite_eq_right
  have : ∀ i < 128, ¬ ((0x3000 : BitVec 64) + BitVec.ofNat 64 i - 0x100000).toNat < 17744 := by decide
  exact this i hi

private theorem pcSat_pre (words : List (BitVec 64)) :
    (Spec.Ffdh.generationPrecomputeContract RISCV64.abi).pre (stripConsts [(tableSym, words)] (pcSatState words)) := by
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, RISCV64.abi, RISCV64.argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Rsa.scratchWords]
  have hdv : Spec.Ffdh.domainValid (BitVec.toNat (64 : BitVec 64))
      (Spec.Rsa.bytesAt (pcSatMem words) 12288 (BitVec.toNat (128 : BitVec 64))) = true := by
    have := pcSat_domain words
    change Spec.Rsa.bytesAt (pcSatMem words) 12288 128 = _ at this
    rw [show BitVec.toNat (64 : BitVec 64) = 64 from rfl, show BitVec.toNat (128 : BitVec 64) = 128 from rfl, this]
    exact CachedSat.domain_valid
  repeat' apply And.intro
  all_goals first
    | with_reducible exact hdv
    | (apply Region.disjoint_of_sep; decide)
    | decide
    | rfl

private theorem pcGeometry :
    (0x100000 : Addr).toNat + 8 * 2218 ≤ 2 ^ 64 ∧
    (⟨0x100000, 8 * 2218⟩ : Region).Disjoint ⟨0x200000, 2200⟩ ∧
    (⟨0x100000, 8 * 2218⟩ : Region).Disjoint ⟨0x4000, 8448⟩ :=
  ⟨by decide, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

private theorem pcSat_consts (words : List (BitVec 64)) (size : words.length = 2218) :
    ConstsOk [(tableSym, words)] 0 (pcSatState words) := by
  refine ⟨?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [constRegs, Abi.constRegions, pcSatState, List.map_cons, List.map_nil, size]
    rfl
  · intro c hc i hi
    obtain rfl := List.mem_singleton.mp hc
    rw [← constMem_held 0x100000 words (by rw [size]; decide) i hi]
    apply Mem.readW_congr
    intro j hj
    show pcSatMem words _ = _
    unfold pcSatMem
    apply ite_eq_left
    have hi' : i < 2218 := by rw [← size]; exact hi
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    change ((0x100000 : BitVec 64) + BitVec.ofNat 64 (8 * i + j) - 0x100000).toNat < 17744
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    rw [size]
    refine ⟨pcGeometry.1, fun q hq => ?_, fun q hq => ?_⟩
    · change q ∈ ([⟨0x200000, 2200⟩, ⟨0x4000, 8448⟩] : List Region) at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact pcGeometry.2.1
      · exact pcGeometry.2.2
    · change q ∈ ([] : List Region) at hq
      contradiction
  · simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    exact (by decide : (0x100000 : BitVec 64).toNat % 64 = 0)

private theorem pcSatAux (words : List (BitVec 64)) (size : words.length = 2218) :
    ∃ s, (Spec.Ffdh.generationPrecomputeContract (RISCV64.abi.withConsts [(tableSym, words)])).pre s :=
  ⟨pcSatState words, pre_consts.mpr ⟨pcSat_pre words, pcSat_consts words size⟩⟩

theorem precompute_sat : ∃ s, (Spec.Ffdh.generationPrecomputeContract (RISCV64.abi.withConsts tableConsts)).pre s :=
  pcSatAux VG.Impl.Ffdh.VettedGroups.tableWords VG.Proof.Ffdh.VettedTableFacts.tableWords_length

theorem pc_implies : pcContract.Implies (Spec.Ffdh.generationPrecomputeContract (RISCV64.abi.withConsts tableConsts)) where
  pre s h := by
    obtain ⟨hp, hc⟩ := pre_consts.mp h
    exact ⟨pc_pre0 hp, hc⟩
  post _ _ _ h := post_consts.mpr (pc_post0 h)
  pub _ _ _ _ h := ⟨pc_pub0 (pub_consts.mp h).1, (pub_consts.mp h).2 _ List.mem_cons_self⟩
  sat := precompute_sat

end VG.Proof.Ffdh.RISCV64.Cached

/-! # The vetted groups' recognition on RISC-V, with its value

`recognize_val`: `recognize` leaves in `a5` the or of the widths of the
groups the domain matches (`orBits`), which is the first match's
(`recognizeList`), as the groups of one length have one width. -/

namespace VG.Proof.Ffdh.RISCV64.VettedValidation

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64
open VG.Impl.Ffdh.RISCV64.VettedValidation VG.Impl.Ffdh.VettedGroups

/-- The or of the widths of the groups of `gs` the domain matches. -/
def orBits (k : Nat) (dom : List Byte) : List Group → BitVec 64
  | [] => 0
  | g :: gs => BitVec.ofNat 64 (if Hit g k dom then g.bits else 0) ||| orBits k dom gs

theorem mask_bits (b : Bool) (n : Nat) :
    bmask b &&& BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 (if b then n else 0) := by
  cases b
  · simp [bmask]
  · rw [show bmask true = BitVec.allOnes 64 from rfl, BitVec.allOnes_and, BitVec.ofInt_natCast]
    rfl

/-- `accumulate g` and `advance n`: `a5 |= g.bits` if `t4 = 0`. -/
theorem acc_val (g : Group) {n : Nat} (hb : g.bits < 2048) (hn : n ≤ 4000) (s : State) :
    WP isa (.block (accumulate g ++ advance n)) s fun t =>
      t.gpr .a5 = s.gpr .a5 ||| BitVec.ofNat 64 (if s.gpr .t4 = 0 then g.bits else 0) ∧
        t.gpr .t5 = s.gpr .t5 + BitVec.ofNat 64 n ∧ t.mem = s.mem ∧ Keep [.t6, .a5, .t5] s t := by
  refine WP.mono (WP.keep [.t6, .a5, .t5] (Q := fun t => t.gpr .a5 = s.gpr .a5 |||
      ((if BitVec.ofNat 64 0 < s.gpr .t4 then (1 : BitVec 64) else 0) - BitVec.ofNat 64 1 &&&
        BitVec.ofInt 64 (g.bits : Int)) ∧
      t.gpr .t5 = VG.Proof.Mont.off (s.gpr .t5) (n / 2 + (n - n / 2)) ∧ t.mem = s.mem)
    (by unfold accumulate advance; brun [exec_li, exec_logicImm (show imm12 (g.bits : Int) by unfold imm12; omega),
      show n / 2 < 2048 by omega, show n - n / 2 < 2048 by omega]) (by rfl) (by rfl))
    fun t ⟨⟨t5', t5, tm⟩, tk⟩ => ⟨?_, ?_, tm, tk⟩
  · rw [t5', VG.Proof.Ffdh.RISCV64.sltu_mask, mask_bits _ _]
    simp only [decide_eq_true_eq]
  · rw [t5]
    show s.gpr .t5 + BitVec.ofNat 64 (n / 2 + (n - n / 2)) = _
    congr 2
    omega

/-- The scan: `a5 |=` the widths of the groups of `gs` the domain matches. -/
theorem scan_val {src : Addr} {k : Nat} {dom : List Byte} :
    ∀ (gs : List Group) (s : State), Ctx src k dom s → TableAt (s.gpr .t5) gs s →
      WP isa (scan gs) s fun t => t.gpr .a5 = s.gpr .a5 ||| orBits k dom gs ∧ t.mem = s.mem ∧
        Keep clobbers s t
  | [], s, _, _ => WP.block_nil ⟨by simp [orBits], rfl, Keep.refl _ _⟩
  | g :: gs, s, h, data => by
    have hr := data.1
    unfold scan
    refine WP.seq (WP.mono (record_ok h g hr) fun s₁ ⟨r4, m1, k1⟩ => ?_)
    refine WP.seq (WP.mono (acc_val g (n := 8 + 3 * g.len) hr.bitsFit (by have := hr.lenFit; omega) s₁)
      fun s₂ ⟨a5, t5, m2, k2⟩ => ?_)
    have hm : s₂.mem = s.mem := m2.trans m1
    have k12 := k1.trans k2
    have tail : TableAt (s₂.gpr .t5) gs s₂ := by
      rw [t5, k1.gpr (by decide)]; exact data.2.after hm k12
    refine WP.mono (scan_val gs s₂ (h.after hm k12) tail) fun t ⟨ta, tm, tk⟩ =>
      ⟨?_, tm.trans hm, (k12.trans tk).mono (by decide)⟩
    rw [ta, a5, k1.gpr (by decide), orBits, BitVec.or_assoc]
    congr 3
    by_cases hh : Hit g k dom
    · rw [ite_eq_left_iff.mpr (fun h' => absurd (r4.mpr hh) h'), ite_eq_left_iff.mpr (fun h' => absurd hh h')]
    · rw [ite_eq_right_iff.mpr (fun h' => absurd (r4.mp h') hh), ite_eq_right_iff.mpr (fun h' => absurd h' hh)]

/-- The widths of the groups of one length are one. -/
theorem groups_bits : ∀ g₁ ∈ groups, ∀ g₂ ∈ groups, g₁.len = g₂.len → g₁.bits = g₂.bits := by
  intro g₁ h₁ g₂ h₂
  simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases h₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The first match's width, or 0. -/
theorem recognizeList_cases {k : Nat} {dom : List Byte} :
    ∀ gs : List Group, recognizeList gs k dom = 0 ∨ ∃ g ∈ gs, Hit g k dom ∧ recognizeList gs k dom = g.bits
  | [] => Or.inl rfl
  | g :: gs => by
    by_cases hh : Hit g k dom
    · have e : recognizeList (g :: gs) k dom = g.bits := by
        simp only [recognizeList]; exact ite_eq_left_iff.mpr (fun h' => absurd hh h')
      exact Or.inr ⟨g, List.mem_cons_self, hh, e⟩
    · have e : recognizeList (g :: gs) k dom = recognizeList gs k dom := by
        simp only [recognizeList]; exact ite_eq_right_iff.mpr (fun h' => absurd h' hh)
      rcases recognizeList_cases gs with h | ⟨g', hg', hh', e'⟩
      · exact Or.inl (e.trans h)
      · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', hh', e.trans e'⟩

theorem orBits_eq {k : Nat} {dom : List Byte} :
    ∀ gs : List Group, (∀ g₁ ∈ gs, ∀ g₂ ∈ gs, g₁.len = g₂.len → g₁.bits = g₂.bits) →
      orBits k dom gs = BitVec.ofNat 64 (recognizeList gs k dom)
  | [], _ => rfl
  | g :: gs, hs => by
    have ih := orBits_eq (k := k) (dom := dom) gs fun a ha b hb => hs a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    rw [orBits, ih]
    by_cases hh : Hit g k dom
    · have e : recognizeList (g :: gs) k dom = g.bits := by
        simp only [recognizeList]; exact ite_eq_left_iff.mpr (fun h' => absurd hh h')
      rw [e, ite_eq_left_iff.mpr (fun h' => absurd hh h')]
      rcases recognizeList_cases (k := k) (dom := dom) gs with h | ⟨g', hg', hh', e'⟩
      · rw [h, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.or_zero]
      · rw [e', ← hs g List.mem_cons_self g' (List.mem_cons_of_mem _ hg') (hh.1.trans hh'.1.symm),
          BitVec.or_self]
    · have e : recognizeList (g :: gs) k dom = recognizeList gs k dom := by
        simp only [recognizeList]; exact ite_eq_right_iff.mpr (fun h' => absurd h' hh)
      rw [e, ite_eq_right_iff.mpr (fun h' => absurd h' hh), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.zero_or]

/-- `recognize`: `a5 :=` the domain's recognized width. -/
theorem recognize_val {s : State} {src : Addr} {k : Nat} {dom : List Byte} (input : Ctx src k dom s)
    (table : TableAt (s.syms tableSym) groups s) :
    WP isa recognize s fun t =>
      t.gpr .a5 = BitVec.ofNat 64 (recognizeList groups k dom) ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  unfold recognize
  refine WP.seq (WP.mono (WP.keep [.t5, .a5] (Q := fun t => t.gpr .t5 = s.syms tableSym ∧ t.gpr .a5 = 0 ∧
    t.mem = s.mem) (by brun [exec_lla, exec_li]; rfl) (by rfl) (by rfl)) fun u ⟨⟨u5, ua, m⟩, k⟩ => ?_)
  refine WP.mono (scan_val groups u (input.after m k) (by rw [u5]; exact table.after m k)) fun t ⟨ta, tm, tk⟩ =>
    ⟨by rw [ta, ua, show (0 : BitVec 64) = 0#64 from rfl, BitVec.zero_or, orBits_eq groups groups_bits], tm.trans m, (k.trans tk).mono (by decide)⟩

/-- The table's records at `s`, from its bytes there. -/
theorem table_at {s : State} (read : InRegions (s.rd ++ s.wr) (s.syms tableSym) tableBytes.length)
    (bytes : Spec.Rsa.bytesAt s.mem (s.syms tableSym) tableBytes.length = tableBytes) :
    TableAt (s.syms tableSym) groups s := by
  apply tableOfBytes groups _ s read bytes
    (by change tableBytes.length ≤ 17744; rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length])
  intro g hg
  simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The table's bytes, from the contract's table. -/
theorem consts_bytes {s : State} {st : Nat} (hc : ConstsOk tableConsts st s) :
    InRegions (s.rd ++ s.wr) (s.syms tableSym) tableBytes.length ∧
      Spec.Rsa.bytesAt s.mem (s.syms tableSym) tableBytes.length = tableBytes := by
  have held := ConstsOk.held1 (name := tableSym) (ws := tableWords) hc
  refine ⟨?_, ?_⟩
  · have := ConstsOk.rd1 (name := tableSym) (ws := tableWords) hc
    rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] at this
    rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length]
    exact ⟨_, List.mem_append_left _ this, Region.contains_self _ _⟩
  · apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      rw [VG.Proof.Ffdh.VettedTableFacts.table_held_byte held hj]
      exact (List.getElem_eq_getD (h := hj) 0).symm

end VG.Proof.Ffdh.RISCV64.VettedValidation

/-! # FFDH's context on RISC-V: with p valid

`bound_step` and `rest_ok`: from p checked and the recognized width in
`a5` (`MP`), the bound's bit length, the width and the metadata,
`R² mod p`, the prefix rows and the table: the context's words are
`generationValues`. -/

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Precompute
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Spec.RsaKeyGen (bitLength)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (A WCtx slot24 slot_lt)

/-- At `main`: the exchange's state with p valid in array 0, the domain's
registers, the recognized width in `a5`, the domain valid, and the context
writable and apart. -/
structure MP (x : XD) (s : State) : Prop where
  base : Base x s
  hp : wordsVal s.mem x.S (slot x.w 0) x.w = x.p
  a2 : s.gpr .a2 = x.D
  a3 : s.gpr .a3 = BitVec.ofNat 64 x.L
  a4 : s.gpr .a4 = BitVec.ofNat 64 x.k
  a5 : s.gpr .a5 = BitVec.ofNat 64 (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups x.k x.db)
  dv : Spec.Ffdh.domainValid x.k x.db = true
  hL : x.L = 2 * x.k ∨ x.L = 3 * x.k
  hY : x.Y = off x.D x.k
  hc : Scr s x.O (8 * ctxWords x.w)
  sepCB : ∀ y, ofs x.O y < 8 * ctxWords x.w → x.Z ≤ ofs x.S y
  sepBC : ∀ y, ofs x.S y < x.Z → 8 * ctxWords x.w ≤ ofs x.O y
  sepDC : ∀ i < x.L, ∀ y, ofs x.O y < 8 * ctxWords x.w → off x.D i ≠ y

/-- The bound's bit length. -/
abbrev blOf (x : XD) : Nat := bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf x.k x.db))

theorem scr_shrink {s : State} {b : Addr} {n m : Nat} (hs : Scr s b n) (h : m ≤ n) : Scr s b m :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, hm, hb, by omega_arith, hL'⟩,
    by have := hs.nowrap; omega_arith, hs.al⟩

theorem MP.keep {x : XD} {s t : State} {rs : List Reg} (h : MP x s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ baseRegs ++ ([.a2, .a3, .a4, .a5] : List Reg), r ∉ rs) : MP x t :=
  ⟨h.base.same k hm (fun r hr' => hr r (List.mem_append_left _ hr')), by rw [hm]; exact h.hp,
    (k.gpr (hr _ (by decide))).trans h.a2, (k.gpr (hr _ (by decide))).trans h.a3,
    (k.gpr (hr _ (by decide))).trans h.a4, (k.gpr (hr _ (by decide))).trans h.a5, h.dv, h.hL, h.hY,
    h.hc.congr k.2.2, h.sepCB, h.sepBC, h.sepDC⟩

/-- The bound's bit length is at most p's. -/
theorem bl_le {k : Nat} {dom : List Byte} (hv : Spec.Ffdh.domainValid k dom = true) :
    bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) ≤ 8 * k := by
  have hv' := (VG.Proof.Ffdh.domainValid_iff k dom).mp hv
  have hle : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≤ (Spec.Ffdh.domainOf k dom).p := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega_arith
    | some q => have := (hv'.2.2 q hq).1.2.2; simp only [Option.getD_some]; omega_arith
  have hp : (Spec.Ffdh.domainOf k dom).p < 2 ^ (8 * k) := by
    have h1 := VG.Proof.Bignum.os2ip_lt (dom.take k)
    have h2 : 256 ^ (dom.take k).length ≤ 2 ^ (8 * k) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega_arith)
    change Spec.Rsa.os2ip (dom.take k) < _
    omega_arith
  exact VG.Proof.Ffdh.ContextRows.bitLength_le_of_lt (Nat.lt_of_le_of_lt hle hp)

/-- `bound`: the bound's bit length into `s3`. -/
theorem bound_step {x : XD} {s : State} (h : MP x s) :
    WP isa bound s fun t => (MP x t ∧ t.gpr .s3 = BitVec.ofNat 64 (blOf x)) ∧ t.mem = s.mem := by
  have hb := h.base
  have hc := hb.ctx
  have hk := hc.k64; have hk' := hc.k1024
  have hf := VG.Proof.Bignum.valid_facts ((VG.Proof.Ffdh.domainValid_iff _ _).mp h.dv).1 hk
  have hlen : (Spec.Rsa.bytesAt s.mem x.D x.L).length = x.L := by simp [Spec.Rsa.bytesAt]
  have hp : ∀ m : Mem, Spec.Rsa.bytesAt m x.D x.L = x.db →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.D x.k) = (Spec.Ffdh.domainOf x.k x.db).p := fun m e => by
    rw [← e, Proof.Ffdh.domainOf_p _ _ (by rcases h.hL with e' | e' <;> omega_arith)]
  refine WP.mono (bound_ok h.a2 h.a3 h.a4 h.hL (by omega_arith) hk' hc.rdD (fun _ => by
      rw [hp _ hc.bD]; exact ⟨hf.1, hf.2.1⟩)
    (by rw [hc.bD]; exact lead_ne (by omega_arith) (by rw [← hc.bD, hlen]; exact h.hL) h.dv))
    fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨h.keep kt tm (by decide), by rw [t3, hc.bD]⟩, tm⟩

/-- `TS` with the memory it keeps below array 1 from now on. -/
theorem TS.remem {s : State} {B C : Addr} {Z w P : Nat} {M : Mem} (h : TS s B C Z w P M) : TS s B C Z w P s.mem :=
  ⟨h.win, h.h10, h.hc, h.sepCB, h.sepBC, h.odd, h.one, fun _ _ => rfl⟩

theorem CtxKeep.out {C : Addr} {w : Nat} {m m' : Mem} (h : CtxKeep C w m m') : Outside C (rowOff w 2) (2 ^ 64) m m' :=
  fun y hy => hy.elim (h y) fun h' => absurd h' (by have := (y - C).isLt; simp only [ofs]; omega_arith)

/-- After `bound`: the width, the metadata, `R² mod p`, the prefix and the
table. -/
theorem rest_ok {x : XD} {s : State} (h : MP x s) (h3 : s.gpr .s3 = BitVec.ofNat 64 (blOf x)) :
    WP isa (.seq width (.seq (.block metadata) (.seq VG.Impl.Ffdh.RISCV64.r2 (.seq storePrefix (.seq table (.block [.li .a0 1]))))))
      s fun t =>
      Spec.Rsa.wordsAt t.mem x.O (3 + 34 * x.w) = VG.Proof.Ffdh.generationValues x.k x.db ∧ t.gpr .a0 = 1 ∧
        t.gpr .s6 = x.S ∧ (∀ y, ofs x.S y < 256 → t.mem y = s.mem y) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hb := h.base
  have hc := hb.ctx
  have hk := hc.k64; have hk' := hc.k1024
  have hZ := hc.hZ; have hn := hc.scr.nowrap
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have hw8 : 8 ≤ x.w := by omega_arith
  have hw' : x.w < 2 ^ 31 := by omega_arith
  have hv' := (VG.Proof.Ffdh.domainValid_iff _ _).mp h.dv
  have hf := VG.Proof.Bignum.valid_facts hv'.1 hk
  have hpx : x.p = (Spec.Ffdh.domainOf x.k x.db).p := rfl
  have hlen : x.db.length = x.L := by rw [← hc.bD]; simp [Spec.Rsa.bytesAt]
  have hd : x.db.length = 2 * x.k ∨ x.db.length = 3 * x.k := by rw [hlen]; exact h.hL
  have e24 : slot x.w 24 = 256 + 24 * (8 * (x.w + 2)) := by simp [slot, hdrBytes]
  have e0 : slot x.w 0 = 256 := by simp [slot, hdrBytes]
  have e1 : slot x.w 1 = 256 + 8 * (x.w + 2) := by simp [slot, hdrBytes]
  have e8 : slot x.w 8 = 256 + 8 * (8 * (x.w + 2)) := by simp [slot, hdrBytes]
  have hCn := h.hc.nowrap
  -- The width.
  have hcap := recognize_lt (by omega_arith) hd hf.2.2
  have hbl : blOf x ≤ 8 * x.k := bl_le h.dv
  refine WP.seq (WP.mono (width_ok h.a5 h3 (by omega_arith) (by omega_arith)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ => ?_)
  rw [width_eq (by omega_arith) hd hf.2.2] at a9
  have hgb := VG.Proof.Ffdh.ContextRows.genBits_facts h.dv
  generalize hbits : Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db) = bits at a9 hgb
  -- The metadata.
  have h10 : s₁.gpr .s10 = x.O := (k1.gpr (by decide)).trans (hb.s10.trans (add_ofNat_zero _))
  refine WP.seq (WP.mono (metadata_ok (scr_shrink (h.hc.congr k1.2.2) (by unfold ctxWords; omega_arith)) h10 a9
    (by omega_arith)) fun s₂ ⟨⟨c0, c8, c16, a9', o2⟩, k2⟩ => ?_)
  rw [m1] at o2
  have k12 := k1.trans k2
  have o2S : Outside x.S x.Z (2 ^ 64) s.mem s₂.mem := ctx_of_scr o2 (by unfold ctxWords; omega_arith) h.sepBC
  -- `R² mod p`.
  unfold VG.Impl.Ffdh.RISCV64.r2
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k12.gpr (by decide)).trans hb.a7)
    ((k12.gpr (by decide)).trans hb.s5) 1) fun s₃ ⟨⟨b2, m3⟩, k3⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k12.trans k3).gpr (by decide) |>.trans hb.a7)
    ((k12.trans k3).gpr (by decide) |>.trans hb.s5) 2) fun s₄ ⟨⟨b5, m4⟩, k4⟩ => ?_
  have k14 := (k12.trans k3).trans k4
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) (k14.gpr (by decide) |>.trans hb.a7)
    (k14.gpr (by decide) |>.trans hb.s5) 3) fun s₅ ⟨⟨b6, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have hm5 : s₅.mem = s₂.mem := by rw [m5, m4, m3]
  have p5 : wordsVal s₅.mem x.S (slot x.w 0) x.w = x.p := by
    rw [hm5, Outside.wordsVal o2S (Or.inl (by omega_arith)) (by omega_arith)]; exact h.hp
  refine WP.mono (r2t_ok (hc.scr.congr k15.2.2) ((k4.trans k5).gpr (by decide) |>.trans b2)
    ((k5.gpr (by decide)).trans b5) b6 (k15.gpr (by decide) |>.trans hb.a7) (k15.gpr (by decide) |>.trans hb.t0)
    (by omega_arith) hw' (by omega_arith) (by rw [p5]; exact hf.2.2) (by rw [p5]; exact hf.1))
    fun s₆ ⟨⟨rr6, inv6, o6⟩, k6⟩ => ?_
  rw [p5] at rr6
  have k16 := k15.trans k6
  have o6C : Outside x.O (8 * ctxWords x.w) (2 ^ 64) s₅.mem s₆.mem :=
    ctx_of_scr o6 (by omega_arith) h.sepCB
  have hlow6 : ∀ y, ofs x.S y < slot x.w 1 → s₆.mem y = s₅.mem y := fun y hy => o6 y (Or.inl hy)
  have hw06 : Mont.word s₆.mem x.S (slot x.w 0) = Mont.word s₅.mem x.S (slot x.w 0) :=
    Outside.word o6 (Or.inl (by omega_arith)) (by omega_arith)
  have p6 : wordsVal s₆.mem x.S (slot x.w 0) x.w = x.p := by
    rw [Outside.wordsVal o6 (Or.inl (by omega_arith)) (by omega_arith)]; exact p5
  have ts6 : TS s₆ x.S x.O x.Z x.w x.p s₆.mem :=
    ⟨⟨hc.scr.congr (k16.2.2), by omega_arith, hw', hZ, k6.gpr (by decide) |>.trans (k15.gpr (by decide) |>.trans hb.a7),
      k16.gpr (by decide) |>.trans hb.s5, k16.gpr (by decide) |>.trans hb.t0, by rw [hw06]; exact inv6, p6⟩,
      (k16.gpr (by decide)).trans (hb.s10.trans (add_ofNat_zero _)), h.hc.congr k16.2.2, h.sepCB, h.sepBC, hf.1, hf.2.1,
      fun _ _ => rfl⟩
  -- The prefix.
  refine WP.seq (WP.mono (storePrefix_ok ts6) fun s₇ ⟨⟨r0, r1, o7, b7, ts7⟩, k7⟩ => ?_)
  have k17 := k16.trans k7
  -- The table.
  have hg : ∀ m : Mem, Spec.Rsa.bytesAt m x.D x.L = x.db →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off x.D x.k) x.k) = (Spec.Ffdh.domainOf x.k x.db).g := fun m e => by
    rw [← e, Proof.Ffdh.domainOf_g _ _ (by rcases h.hL with e' | e' <;> omega_arith)]
  have hsepC : ∀ i < x.k, ∀ y, ofs x.O y < 8 * ctxWords x.w → off (off x.D x.k) i ≠ y := fun i hi y hy => by
    rw [Derive.off_off]; exact h.sepDC (x.k + i) (by rcases h.hL with e' | e' <;> omega_arith) y hy
  have hsepS : ∀ i < x.k, ∀ y, ofs x.S y < x.Z → off (off x.D x.k) i ≠ y := fun i hi y hy => by
    rw [← h.hY]; exact hc.sepY i hi y hy
  have hb7 : Spec.Rsa.bytesAt s₇.mem (off x.D x.k) x.k = Spec.Rsa.bytesAt s.mem (off x.D x.k) x.k := by
    rw [Pub.bytes_apart (Z := 8 * ctxWords x.w) o7 (by unfold rowOff ctxWords; omega_arith) hsepC,
      Pub.bytes_apart (Z := x.Z) o6 (by omega_arith) hsepS, hm5,
      Pub.bytes_apart (Z := 8 * ctxWords x.w) o2 (by unfold ctxWords; omega_arith) hsepC]
  have h9 : s₇.gpr .s9 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) :=
    ((k3.trans k4).trans k5 |>.trans k6 |>.trans k7).gpr (by decide) |>.trans a9'
  have hrows := VG.Proof.Rsa.FixedBaseComb.rows_small (show bits ≤ 8192 by omega_arith)
  have hrpos := VG.Proof.Rsa.FixedBaseComb.rows_pos (show 0 < bits by omega_arith)
  have hgp : (Spec.Ffdh.domainOf x.k x.db).g < x.p := by have := hv'.2.1; omega_arith
  have a17 : A s₇.mem x.S x.w 1 = 2 ^ (64 * x.w) * 2 ^ (64 * x.w) % x.p := by
    show wordsVal s₇.mem x.S (slot x.w 1) x.w = _
    rw [Outside.wordsVal b7 (Or.inl (by omega_arith)) (by omega_arith), rr6, ← Nat.pow_add]
    congr 2; omega_arith
  refine WP.seq (WP.mono (table_ok (D := x.D) (k := x.k) (G := (Spec.Ffdh.domainOf x.k x.db).g) (bits := bits)
    ⟨ts7.remem, h9, CtxKeep.of_eq rfl, Keep.refl _ _⟩ hrpos (by omega_arith) a17
    (k17.gpr (by decide) |>.trans hb.s6) (k17.gpr (by decide) |>.trans hb.s7) (k17.gpr (by decide) |>.trans hb.s11)
    (by omega_arith) (by omega_arith) (fun i hi => by rw [k17.2.1, k17.2.2, ← h.hY]; exact hc.rdY i hi) hsepS hsepC
    (by rw [hb7]; exact hg _ hc.bD) hgp) fun s₈ ⟨tt8, e8'⟩ => ?_)
  -- `a0 := 1`.
  refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = 1 ∧ t.mem = s₈.mem) (by brun [Pub.pub_li1]; rfl)
    (by rfl) (by rfl)) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have k8 := tt8.kr
  have ck := tt8.keep.out
  have hrow2 : rowOff x.w 1 + 8 * x.w ≤ rowOff x.w 2 := by unfold rowOff; omega_arith
  have hrow02 : rowOff x.w 0 + 8 * x.w ≤ rowOff x.w 2 := by unfold rowOff; rw [Nat.mul_zero]; omega_arith
  have hcw : 8 * ctxWords x.w = 24 + 272 * x.w := by unfold ctxWords; omega_arith
  have hr2 : rowOff x.w 2 = 24 + 16 * x.w := by unfold rowOff; omega_arith
  have wd : ∀ d, d + 8 ≤ 24 → word t.mem x.O d = word s₂.mem x.O d := fun d hd => by
    rw [mt, Outside.word ck (Or.inl (by unfold rowOff; omega_arith)) (by omega_arith),
      Outside.word o7 (Or.inl (by unfold rowOff; omega_arith)) (by omega_arith),
      Outside.word o6C (Or.inl (by unfold ctxWords; omega_arith)) (by omega_arith), hm5]
  refine ⟨?_, t0, (kt.gpr (by decide)).trans (k8.gpr (by decide) |>.trans (k17.gpr (by decide) |>.trans hb.s6)),
    fun y hy => ?_, by rw [kt.2.1, k8.2.1, k17.2.1], by rw [kt.2.2, k8.2.2, k17.2.2]⟩
  · have c0' : word t.mem x.O 0 = BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db)) := by
      rw [wd 0 (by decide), c0, hbits]
    have c8' : word t.mem x.O 8 =
        BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db) + 7) / 8) := by
      rw [wd 8 (by decide), c8, hbits]
    have c16' : word t.mem x.O 16 = BitVec.ofNat 64
        (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db))) := by
      rw [wd 16 (by decide), c16, hbits]
    have hp' : wordsVal t.mem x.O (rowOff x.w 0) x.w = (Spec.Ffdh.domainOf x.k x.db).p := by
      rw [mt, Outside.wordsVal ck (Or.inl hrow02) (by unfold rowOff; rw [Nat.mul_zero]; omega_arith), r0]
      exact ts6.win.n
    have hr' : wordsVal t.mem x.O (rowOff x.w 1) x.w =
        2 ^ (64 * x.w) * 2 ^ (64 * x.w) % (Spec.Ffdh.domainOf x.k x.db).p := by
      rw [mt, Outside.wordsVal ck (Or.inl hrow2) (by unfold rowOff; omega_arith), r1]
      show wordsVal s₆.mem x.S (slot x.w 1) x.w = _
      rw [rr6, ← Nat.pow_add]
      congr 2; omega_arith
    have he' : Ents t.mem x.O (Spec.Ffdh.domainOf x.k x.db).g (Spec.Ffdh.domainOf x.k x.db).p x.w
        (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db)) 32 := by
      rw [hbits]; intro a ha; rw [ent, mt]; exact e8' a ha
    exact ctx_words (k := x.k) (dom := x.db) c0' c8' c16' hp' hr' he'
  · have hy' : ofs x.S y < x.Z := by omega_arith
    rw [mt, tt8.ts.low y (by omega_arith), b7 y (Or.inl hy'), o6 y (Or.inl (by omega_arith)), hm5,
      o2 y (Or.inr (by have := h.sepBC y hy'; omega_arith))]

end VG.Proof.Ffdh.RISCV64.Cached

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Precompute
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Bignum (slot ofNat_toNat64)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)
open VG.Impl.Ffdh.RISCV64.VettedValidation (tableSym tableConsts)

/-- The exchange's data of a precompute: the context as `out`, the domain's
`p_len` octets as x, g's as the peer. -/
def pcx (s : State) : XD :=
  ⟨s.gpr .a0, s.gpr .a2, (s.gpr .a3).toNat, (s.gpr .a4).toNat, s.gpr .a2, (s.gpr .a4).toNat,
    off (s.gpr .a2) (s.gpr .a4).toNat, s.gpr .a5, (s.gpr .a6).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat⟩

/-- The header's words 0–3: the context, the domain, `p_len` and g's
address; the domain's arguments where `recognize` reads them. -/
theorem pcHdr_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 32 ≤ Z) (h6 : s.gpr .s6 = S) :
    WP isa (.block ([.store .d .a0 .s6 0, .store .d .a2 .s6 8, .store .d .a4 .s6 16, .add .t2 .a2 .a4,
      .store .d .t2 .s6 24, .addi .a0 .a2 0, .addi .a1 .a3 0, .addi .a2 .a4 0] : List Instr)) s fun t =>
      (word t.mem S 0 = s.gpr .a0 ∧ word t.mem S 8 = s.gpr .a2 ∧ word t.mem S 16 = s.gpr .a4 ∧
        word t.mem S 24 = s.gpr .a2 + s.gpr .a4 ∧ t.gpr .a0 = s.gpr .a2 ∧ t.gpr .a1 = s.gpr .a3 ∧
        t.gpr .a2 = s.gpr .a4 ∧ Outside S 0 32 s.mem t.mem) ∧ Keep [.t2, .a0, .a1, .a2] s t := by
  have hn := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  have i0 := hs.st (d := 0) (n := 8) (by omega_arith)
  have i8 := hs.st (d := 8) (n := 8) (by omega_arith)
  have i16 := hs.st (d := 16) (n := 8) (by omega_arith)
  have i24 := hs.st (d := 24) (n := 8) (by omega_arith)
  have l0 := hs.al8 (d := 0) (by omega_arith) (by decide)
  have l8 := hs.al8 (d := 8) (by omega_arith) (by decide)
  have l16 := hs.al8 (d := 16) (by omega_arith) (by decide)
  have l24 := hs.al8 (d := 24) (by omega_arith) (by decide)
  have o0 := writeW_outside s.mem S (d := 0) (s.gpr .a0) (by omega_arith)
  have o1 := writeW_outside (s.mem.writeW (off S 0) (s.gpr .a0)) S (d := 8) (s.gpr .a2) (by omega_arith)
  have o2 := writeW_outside ((s.mem.writeW (off S 0) (s.gpr .a0)).writeW (off S 8) (s.gpr .a2)) S (d := 16)
    (s.gpr .a4) (by omega_arith)
  have o3 := writeW_outside (((s.mem.writeW (off S 0) (s.gpr .a0)).writeW (off S 8) (s.gpr .a2)).writeW
    (off S 16) (s.gpr .a4)) S (d := 24) (s.gpr .a2 + s.gpr .a4) (by omega_arith)
  refine WP.mono (WP.keep [.t2, .a0, .a1, .a2] (Q := fun t => t.mem = (((s.mem.writeW (off S 0) (s.gpr .a0)).writeW
      (off S 8) (s.gpr .a2)).writeW (off S 16) (s.gpr .a4)).writeW (off S 24) (s.gpr .a2 + s.gpr .a4) ∧
      t.gpr .a0 = s.gpr .a2 ∧ t.gpr .a1 = s.gpr .a3 ∧ t.gpr .a2 = s.gpr .a4) ?_ (by rfl) (by rfl))
    fun t ⟨⟨tm, t0, t1, t2⟩, kt⟩ => ⟨⟨?_, ?_, ?_, ?_, t0, t1, t2, ?_⟩, kt⟩
  · brun [h6', i0, i8, i16, i24, l0, l8, l16, l24]
    exact ⟨BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _⟩
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith),
      o1.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (((o0.mono (by omega_arith) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))).trans
      (o2.mono (by omega_arith) (by omega_arith))).trans (o3.mono (by omega_arith) (by omega_arith))

/-- What the front leaves. -/
structure PF (s t : State) : Prop where
  s6 : t.gpr .s6 = s.gpr .a5
  sav : ∀ i < 12, t.mem.readW (off (savW (s.gpr .a5)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)
  w0 : word t.mem (s.gpr .a5) 0 = s.gpr .a0
  w8 : word t.mem (s.gpr .a5) 8 = s.gpr .a2
  w16 : word t.mem (s.gpr .a5) 16 = s.gpr .a4
  w24 : word t.mem (s.gpr .a5) 24 = s.gpr .a2 + s.gpr .a4
  a0 : t.gpr .a0 = s.gpr .a2
  a1 : t.gpr .a1 = s.gpr .a3
  a2 : t.gpr .a2 = s.gpr .a4
  a3 : t.gpr .a3 = s.gpr .a3
  a4 : t.gpr .a4 = s.gpr .a4
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : Outside (s.gpr .a5) 0 256 s.mem t.mem
  syms : t.syms = s.syms

theorem pcWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = ctxWords ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords,
    ctxWords]
  omega_arith

/-- The precondition's facts, by name. -/
structure PP (s : State) : Prop where
  rd : (pcDomR s) ∈ s.rd
  wr : s.wr = [pcCtx s, pcScr s]
  dCD : (pcCtx s).Disjoint (pcDomR s)
  dCS : (pcCtx s).Disjoint (pcScr s)
  dDS : (pcDomR s).Disjoint (pcScr s)
  nwC : (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64
  nwD : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  nwS : (s.gpr .a5).toNat + (s.gpr .a6).toNat * 8 ≤ 2 ^ 64
  k64 : 64 ≤ (s.gpr .a4).toNat
  k1024 : (s.gpr .a4).toNat ≤ 1024
  hL : (s.gpr .a3).toNat = 2 * (s.gpr .a4).toNat ∨ (s.gpr .a3).toNat = 3 * (s.gpr .a4).toNat
  hcl : (s.gpr .a1).toNat = ctxWords (((s.gpr .a4).toNat + 7) / 8)
  hsl : 16 * (s.gpr .a4).toNat + 32 ≤ (s.gpr .a6).toNat
  dv : Spec.Ffdh.domainValid (s.gpr .a4).toNat (pcDom s) = true
  alC : (s.gpr .a0).toNat % 8 = 0
  alS : (s.gpr .a5).toNat % 8 = 0
  cs : ConstsOk tableConsts 0 s

theorem pp_of {s : State} (h : pcContract.pre s) : PP s := by
  obtain ⟨⟨hrd, hwr, dCD, dCS, dDS, nwC, nwD, nwS, ⟨hk, hk'⟩, hL, hcl, hsl, hdv, alC, alS⟩, hc⟩ := h
  simp only [Spec.Rsa.scratchWords, stripConsts_gpr] at hsl hL hcl
  refine ⟨stripConsts_rd_mem (K := tableConsts) (by rw [hrd]; exact List.mem_cons_self), hwr, dCD, dCS, dDS, nwC,
    nwD, nwS, hk, hk', by simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith, by rw [hcl, pcWords_eq], hsl,
    hdv, alC, alS, hc⟩

/-- `front`. -/
theorem pcFront_ok {s : State} (h : PP s) : WP isa (.block front) s (PF s) := by
  suffices hw : WP isa (.block front) s fun t => t.syms = s.syms → PF s t from WP.mono_syms hw fun _ h₁ h₂ => h₁ h₂
  have hS : Scr s (s.gpr .a5) ((s.gpr .a6).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.nwS h.alS
  have hn := h.nwS
  unfold front
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = s.gpr .a5 ∧ t.mem = s.mem)
    (by brun [add_ofNat_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a0', m1⟩, k1⟩ => ?_)
  have hin : ∀ i < 12, InRegions s₁.wr (off (savW (s₁.gpr .t0)) (8 * i)) 8 := fun i hi => by
    rw [a0', k1.2.2, h.wr]
    show InRegions _ (s.gpr .a5 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    have := h.hsl
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.block_append (WP.mono (Pub.save_ok s₁ hin (fun i hi => by
    rw [a0']; exact Pub.sav_al h.alS (by have := h.hsl; omega_arith) hi)) fun s₂ hSv => ?_)
  have k12 := k1.trans hSv.keep
  have h6₂ : s₂.gpr .s6 = s.gpr .a5 := hSv.s6.trans a0'
  refine WP.mono (pcHdr_ok (hS.congr k12.2.2) (by have := h.hsl; omega_arith) h6₂)
    fun t ⟨⟨w0, w8, w16, w24, t0, t1, t2, o3⟩, k3⟩ hsy => ?_
  have k := k12.trans k3
  have g : ∀ r ∈ ([.a0, .a2, .a3, .a4] : List Reg), s₂.gpr r = s.gpr r := fun r hr => k12.gpr (by revert r hr; decide)
  have hm2 : Outside (s.gpr .a5) 0 256 s.mem s₂.mem := fun y hy => by
    rw [← m1]
    refine hSv.frame y fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [a0'] at hc
    have hc' := (Offset.sub_base (n := 96) (k := 256) (s.gpr .a5) (d := 128) (by have := h.hsl; omega_arith)) _ hc
    simp only [Region.Contains] at hc'
    simp only [ofs] at hy
    omega_arith
  refine ⟨(k3.gpr (by decide)).trans h6₂, fun i hi => ?_, by rw [w0, g .a0 (by decide)],
    by rw [w8, g .a2 (by decide)], by rw [w16, g .a4 (by decide)], by rw [w24, g .a2 (by decide), g .a4 (by decide)],
    by rw [t0, g .a2 (by decide)], by rw [t1, g .a3 (by decide)], by rw [t2, g .a4 (by decide)],
    by rw [k3.gpr (by decide), g .a3 (by decide)], by rw [k3.gpr (by decide), g .a4 (by decide)], k.2.1, k.2.2,
    hm2.trans (o3.mono (Nat.le_refl _) (by omega_arith)), hsy⟩
  have e : off (savW (s.gpr .a5)) (8 * i) = off (s.gpr .a5) (128 + 8 * i) := by rw [off, off, Offset.add_add]
  rw [e]
  show word t.mem (s.gpr .a5) (128 + 8 * i) = _
  rw [o3.word (Or.inr (by omega_arith)) (by have := h.hsl; omega_arith)]
  show s₂.mem.readW (off (s.gpr .a5) (128 + 8 * i)) 64 = _
  rw [← e, ← a0', hSv.saved i hi, k1.gpr fun h' => Pub.saved_ne_t0 i hi (List.mem_singleton.mp h')]

/-- The domain's octets after the front, apart from the working space. -/
theorem pf_bytes {s t : State} (h : PP s) (hf : PF s t) {Q : Addr} {n : Nat}
    (hsep : ∀ i < n, ∀ x, ofs (s.gpr .a5) x < (s.gpr .a6).toNat * 8 → off Q i ≠ x) :
    Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n :=
  Pub.bytes_apart (o := 0) (n := 256) hf.out (by have := h.hsl; omega_arith) hsep

/-- The recognized width of the domain. -/
abbrev pcCap (s : State) : Nat :=
  VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups (s.gpr .a4).toNat (pcDom s)

theorem sepDS {s : State} (h : PP s) :
    ∀ i < (s.gpr .a3).toNat, ∀ x, ofs (s.gpr .a5) x < (s.gpr .a6).toNat * 8 → off (s.gpr .a2) i ≠ x :=
  Pub.ne_of_disjoint h.dDS (Nat.le_of_lt (s.gpr .a3).isLt)

/-- `recognize`, after the front. -/
theorem recog_ok {s t : State} (h : PP s) (hf : PF s t) :
    WP isa VG.Impl.Ffdh.RISCV64.VettedValidation.recognize t fun u =>
      PF s u ∧ u.gpr .a5 = BitVec.ofNat 64 (pcCap s) := by
  have hlen : (pcDom s).length = (s.gpr .a3).toNat := by simp [pcDom, Spec.Rsa.bytesAt]
  have input : VettedValidation.Ctx (s.gpr .a2) (s.gpr .a4).toNat (pcDom s) t :=
    ⟨hf.a0, by rw [hf.a1, hlen, ofNat_toNat64], by rw [hf.a2, ofNat_toNat64],
      ⟨_, List.mem_append_left _ (by rw [hf.rd]; exact h.rd), by rw [hlen]; exact Region.contains_self _ _⟩,
      by rw [hlen, pf_bytes h hf (sepDS h)], by rw [hlen]; exact h.hL, h.k64, h.k1024⟩
  have cb := VettedValidation.consts_bytes h.cs
  have hT : (⟨s.syms tableSym, 8 * VG.Impl.Ffdh.VettedGroups.tableWords.length⟩ : Region).Disjoint (pcScr s) :=
    ConstsOk.wr1 h.cs _ (by rw [h.wr]; simp)
  rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] at hT
  have table : VettedValidation.TableAt (t.syms tableSym) VG.Impl.Ffdh.VettedGroups.groups t := by
    refine VettedValidation.table_at (s := t) (by rw [hf.rd, hf.wr, hf.syms]; exact cb.1) ?_
    · have sepT : ∀ i < VG.Impl.Ffdh.VettedGroups.tableBytes.length, ∀ x,
          ofs (s.gpr .a5) x < (s.gpr .a6).toNat * 8 → off (s.syms tableSym) i ≠ x := fun i hi =>
        Pub.ne_of_disjoint hT (by decide) i (by rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length] at hi; omega_arith)
      rw [hf.syms, pf_bytes h hf sepT]
      exact cb.2
  refine WP.mono_syms (VettedValidation.recognize_val input table) fun u ⟨ua, um, uk⟩ usy => ⟨?_, ua⟩
  have g : ∀ r ∈ ([.s6, .a0, .a1, .a2, .a3, .a4] : List Reg), u.gpr r = t.gpr r :=
    fun r hr => uk.gpr (by revert r hr; decide)
  exact ⟨(g .s6 (by decide)).trans hf.s6, fun i hi => by rw [um]; exact hf.sav i hi, by rw [um]; exact hf.w0,
    by rw [um]; exact hf.w8, by rw [um]; exact hf.w16, by rw [um]; exact hf.w24, (g .a0 (by decide)).trans hf.a0,
    (g .a1 (by decide)).trans hf.a1, (g .a2 (by decide)).trans hf.a2, (g .a3 (by decide)).trans hf.a3,
    (g .a4 (by decide)).trans hf.a4, uk.2.1.trans hf.rd, uk.2.2.trans hf.wr, by rw [um]; exact hf.out,
    usy.trans hf.syms⟩

/-- `post`: `Base` of the precompute's data. -/
theorem post_ok {s u : State} (h : PP s) (hf : PF s u) :
    WP isa (.block post) u fun v => Base (pcx s) v ∧ v.gpr .a2 = s.gpr .a2 ∧ v.gpr .a3 = s.gpr .a3 ∧
      v.gpr .a4 = s.gpr .a4 ∧ v.gpr .a5 = u.gpr .a5 ∧ v.mem = u.mem ∧ v.rd = s.rd ∧ v.wr = s.wr := by
  have hS : Scr u (s.gpr .a5) ((s.gpr .a6).toNat * 8) := Scr.of_mem (by rw [hf.wr, h.wr]; simp) h.nwS h.alS
  have hsl := h.hsl
  have hk := h.k64; have hk' := h.k1024
  have h6' : u.gpr .s6 = off (s.gpr .a5) 0 := by rw [hf.s6]; simp [off]
  have l0 := hS.ld (d := 0) (n := 8) (by omega_arith)
  have a0' := hS.al8 (d := 0) (by omega_arith) (by decide)
  unfold post
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.a2, .s7, .s8, .a1, .a0] (Q := fun t => t.gpr .a2 = s.gpr .a2 ∧ t.gpr .s7 = s.gpr .a2 ∧
      t.gpr .s8 = s.gpr .a4 ∧ t.gpr .a1 = s.gpr .a4 ∧ t.gpr .a0 = s.gpr .a0 ∧ t.mem = u.mem)
    (by
      brun [hf.a0, hf.a2, hf.a4, h6', l0, a0']
      exact ⟨BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _, hf.w0⟩) (by rfl) (by rfl)) fun t₁ ⟨⟨b2, b7, b8, b1, b0, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.setup_ok (O := s.gpr .a0) (k := (s.gpr .a4).toNat) b0 (by rw [b1, ofNat_toNat64])
    ((k1.gpr (by decide)).trans hf.s6) hk') fun v ⟨⟨j10, j11, j0, j5, j7, jm⟩, k2⟩ => ?_
  have k := k1.trans k2
  have hrdv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [k.2.1, k.2.2, hf.rd, hf.wr]
  have hvm : v.mem = u.mem := by rw [jm, m1]
  have hLk : 2 * (s.gpr .a4).toNat ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat ≤ 3 * (s.gpr .a4).toNat := by
    have := h.hL; omega_arith
  have hcl := h.hcl
  have nwC := h.nwC
  have hCk : (s.gpr .a4).toNat ≤ (s.gpr .a1).toNat * 8 := by rw [hcl]; unfold ctxWords; omega_arith
  have sepD := sepDS h
  have rdD : ∀ i < (s.gpr .a3).toNat, InRegions (v.rd ++ v.wr) (off (s.gpr .a2) i) 1 := by
    rw [hrdv]; exact rd_of_mem h.rd (Nat.le_refl _) (BitVec.isLt _)
  have hb := pf_bytes h hf sepD
  refine ⟨⟨⟨Scr.of_mem (by rw [k.2.2, hf.wr, h.wr]; simp [pcx]) h.nwS h.alS, hk, hk', hLk, ?_, by
      change (s.gpr .a0).toNat + (s.gpr .a4).toNat ≤ _; omega_arith,
      fun i hi => ⟨pcCtx s, by rw [k.2.2, hf.wr, h.wr]; simp,
        Offset.contains_base _ (by change i < (s.gpr .a4).toNat at hi; omega_arith)
          (by change i < (s.gpr .a4).toNat at hi; omega_arith)⟩,
      fun y hy => Pub.sep_of_disjoint h.dCS y (by
        have : (y - s.gpr .a0).toNat < (s.gpr .a4).toNat := hy
        show (y - s.gpr .a0).toNat < _; omega_arith),
      rdD, sepD,
      fun i hi => by
        change i < (s.gpr .a4).toNat at hi
        show InRegions _ (off (off (s.gpr .a2) (s.gpr .a4).toNat) i) 1
        rw [Derive.off_off]; exact rdD _ (by omega_arith),
      fun i hi => by
        change i < (s.gpr .a4).toNat at hi
        show ∀ y, _ → off (off (s.gpr .a2) (s.gpr .a4).toNat) i ≠ y
        rw [Derive.off_off]; exact sepD _ (by omega_arith),
      fun i hi => rdD i (by change i < (s.gpr .a4).toNat at hi; omega_arith),
      fun i hi => sepD i (by change i < (s.gpr .a4).toNat at hi; omega_arith),
      by change 1 ≤ (s.gpr .a4).toNat; omega_arith, Nat.le_refl _, by rw [hvm]; exact hb,
      by rw [hvm]; exact hf.w0.trans (add_ofNat_zero _).symm, by rw [hvm]; exact hf.w8.trans (add_ofNat_zero _).symm,
      by rw [hvm]; exact hf.w16.trans (ofNat_toNat64 _).symm,
      by
        rw [hvm]; refine hf.w24.trans ?_
        show s.gpr .a2 + s.gpr .a4 = s.gpr .a2 + BitVec.ofNat 64 (s.gpr .a4).toNat
        rw [ofNat_toNat64]⟩,
    by rw [k2.gpr (by decide), k1.gpr (by decide), hf.s6]; rfl, j7, by rw [j5]; rfl, j0,
    by rw [k2.gpr (by decide), b7]; exact (add_ofNat_zero _).symm,
    by rw [k2.gpr (by decide), b8]; exact (ofNat_toNat64 _).symm,
    by rw [j10]; exact (add_ofNat_zero _).symm, j11⟩,
    by rw [k2.gpr (by decide), b2], by rw [k.gpr (by decide), hf.a3], by rw [k.gpr (by decide), hf.a4],
    k.gpr (by decide), hvm, by rw [k.2.1, hf.rd], by rw [k.2.2, hf.wr]⟩
  show slot (((s.gpr .a4).toNat + 7) / 8) 24 ≤ (s.gpr .a6).toNat * 8
  unfold slot hdrBytes; omega_arith

/-- `MP` after p's load, from the precondition. -/
theorem mp_of {s t₄ : State} (h : PP s) (h4 : X4 (pcx s) t₄) (r4 : t₄.wr = s.wr) (a2 : t₄.gpr .a2 = s.gpr .a2)
    (a3 : t₄.gpr .a3 = s.gpr .a3) (a4 : t₄.gpr .a4 = s.gpr .a4) (a5 : t₄.gpr .a5 = BitVec.ofNat 64 (pcCap s)) :
    MP (pcx s) t₄ := by
  have hcl := h.hcl
  have e8 : (s.gpr .a1).toNat * 8 = 8 * ctxWords (pcx s).w := by
    show _ = 8 * ctxWords (((s.gpr .a4).toNat + 7) / 8); rw [hcl]; omega_arith
  have dCD := h.dCD
  have dCS := h.dCS
  rw [show pcCtx s = ⟨s.gpr .a0, 8 * ctxWords (pcx s).w⟩ by simp only [pcCtx, e8]] at dCD dCS
  refine ⟨h4.1, h4.2.1, a2, by rw [a3]; exact (ofNat_toNat64 _).symm,
    by rw [a4]; exact (ofNat_toNat64 _).symm, a5, h.dv, h.hL, rfl,
    Scr.of_mem (by rw [r4, h.wr]; simp [pcCtx, pcx, e8]) (by rw [← e8]; exact h.nwC) h.alC,
    fun y hy => Pub.sep_of_disjoint dCS y hy, fun y hy => Pub.sep_of_disjoint dCS.symm y hy,
    fun i hi y hy => Pub.ne_of_disjoint dCD.symm (Nat.le_of_lt (s.gpr .a3).isLt) i hi y hy⟩

/-- Every register but `ra`. -/
def pcNotRa : List Reg :=
  [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10,
    .s11, .t3, .t4, .t5, .t6]

theorem pc_pres_saved : ∀ r ∈ preserved, ∃ i < 12, r = PublicChecked.saved i := by decide

theorem pc_correct (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa Precompute.code s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa Precompute.code s fun t => abiPreserved s t ∧ pcContract.post s t
  suffices main : WP isa Precompute.code s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ pcPost s t from
    WP.mono (WP.rdwr (WP.keep pcNotRa main (by rfl))) fun t ⟨⟨⟨hp, hpost⟩, kra⟩, _, _, hsp⟩ =>
      ⟨⟨hp, hsp, kra.gpr (by decide)⟩, hpost⟩
  have hp := pp_of h
  have hsl := hp.hsl
  have hk := hp.k64
  have hn := hp.nwS
  unfold Precompute.code
  refine WP.seq (WP.mono (pcFront_ok hp) fun t₁ f1 => ?_)
  refine WP.seq (WP.mono (recog_ok hp f1) fun t₂ ⟨f2, c2⟩ => ?_)
  refine WP.seq (WP.mono (post_ok hp f2) fun t₃ ⟨b3, a2, a3, a4, a5, m3, r3, w3⟩ => ?_)
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadP_X b3) (by rfl)))
    fun t₄ ⟨⟨⟨h4, ar4⟩, k4⟩, r4, w4, _⟩ => ?_)
  have hv : Spec.Rsa.modulusValid (pcx s).p (pcx s).k = true := Proof.Ffdh.domainValid_mod hp.dv
  have hz4 : t₄.gpr .s0 = 0 := h4.2.2.mpr hv
  have mp := mp_of hp h4 (by rw [w4, w3]) ((k4.gpr (by decide)).trans a2) ((k4.gpr (by decide)).trans a3)
    ((k4.gpr (by decide)).trans a4) ((k4.gpr (by decide)).trans (a5.trans c2))
  refine WP.seq (WP.mono (WP.rdwr (show WP isa (.ite (.zero .s0) main (.block [.li .a0 0])) t₄ (fun t =>
      Spec.Rsa.wordsAt t.mem (pcx s).O (3 + 34 * (pcx s).w) = VG.Proof.Ffdh.generationValues (pcx s).k (pcx s).db ∧
        t.gpr .a0 = 1 ∧ t.gpr .s6 = (pcx s).S ∧ ∀ y, ofs (pcx s).S y < 256 → t.mem y = t₄.mem y) from
    WP.ite (t₄.gpr .s0 == 0) (Steps.eval_zero _ _) (fun _ => by
        unfold main
        simp only [seqs]
        exact WP.seq (WP.mono (bound_step mp) fun u ⟨⟨mpu, u3⟩, um⟩ => WP.mono (rest_ok mpu u3)
          fun t ⟨tw, t0, t6, tf, _, _⟩ => ⟨tw, t0, t6, fun y hy => (tf y hy).trans (by rw [um])⟩))
      (fun hb => absurd hz4 (by simpa using hb)))) fun t₅ ⟨⟨tw5, t05, t65, tf5⟩, r5, w5, _⟩ => ?_)
  -- The saved registers' words.
  have hin : ∀ i < 12, InRegions t₅.wr (off (savW (s.gpr .a5)) (8 * i)) 8 := fun i hi => by
    rw [w5, w4, w3, hp.wr]
    show InRegions _ (s.gpr .a5 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 12, t₅.mem.readW (off (savW (s.gpr .a5)) (8 * i)) 64 = s.gpr (PublicChecked.saved i) :=
      fun i hi => by
    have e : off (savW (s.gpr .a5)) (8 * i) = off (s.gpr .a5) (128 + 8 * i) := by
      rw [off, off, Offset.add_add]
    rw [← f2.sav i hi, e]
    show word t₅.mem (s.gpr .a5) (128 + 8 * i) = word t₂.mem (s.gpr .a5) (128 + 8 * i)
    have o5 : Outside (s.gpr .a5) 256 (2 ^ 64) t₄.mem t₅.mem := fun y hy => tf5 y (hy.elim id fun h' => by
      have := (y - s.gpr .a5).isLt; simp only [ofs] at h'; omega_arith)
    have ar4' : Outside (s.gpr .a5) 256 ((s.gpr .a6).toNat * 8 - 256) t₃.mem t₄.mem := ar4
    rw [Outside.word o5 (Or.inl (by omega_arith)) (by omega_arith),
      Outside.word ar4' (Or.inl (by omega_arith)) (by omega_arith), m3]
  refine WP.mono (Pub.restore_ok t₅ (S := s.gpr .a5) (v := fun i => s.gpr (PublicChecked.saved i)) t65 hin
    (fun i hi => Pub.sav_al hp.alS (by omega_arith) hi) hsav) fun u ⟨urs, uot, um, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pc_pres_saved r hr
    exact urs i hi
  refine ⟨by rw [uot .a0 (by decide), t05]; decide, ?_⟩
  rw [um, show (s.gpr .a1).toNat = 3 + 34 * (pcx s).w by rw [hp.hcl]; rfl]
  have hlk : (s.gpr .a4).toNat ≤ (pcDom s).length := by
    simp only [pcDom, VG.Proof.Bignum.bytesAt_length]; have := hp.hL; omega_arith
  have tw5' : Spec.Rsa.wordsAt t₅.mem (s.gpr .a0) (3 + 34 * (pcx s).w) =
      VG.Proof.Ffdh.generationValues (s.gpr .a4).toNat (pcDom s) := tw5
  rw [tw5', Proof.Ffdh.generationPrecompute_eq hlk hv]

end VG.Proof.Ffdh.RISCV64.Cached
